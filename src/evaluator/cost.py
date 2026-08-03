"""Equivalent public API cost calculation from structured model usage."""

from __future__ import annotations

import math
from collections.abc import Iterable
from dataclasses import dataclass

from genai_prices import Usage, calc_price
from genai_prices.types import PriceCalculation, TieredPrices

from evaluator.usage import RequestUsage, UsageCost, UsageSummary

_CLAUDE_AGGREGATE_SOURCES = {
    "claude_code.total_cost_usd",
    "claude_code.modelUsage.costUSD",
}
_CLAUDE_PUBLIC_PRICE_SOURCE = "claude_code.modelUsage.public_price"
_PI_AGGREGATE_SOURCE = "pi.session.usage.cost.total"
_PI_COMPACTION_USAGE_SOURCE = "pi_cli_compaction_end"
_PI_COMPACTION_BOUNDARY_WARNING = "pi compaction usage may aggregate one or more summarizer calls"
_COST_DIFFERENCE_LIMIT = 0.10
_MODEL_ALIASES = {"sonnet-4.5": "claude-sonnet-4-5"}
_REQUEST_USD_SOURCES = {
    "litellm.completion_cost",
    "litellm.response_cost",
    "pi.usage.cost.total",
}
_COST_ONLY_WARNING_PARTS = (
    "cost is unavailable",
    "cost is a lower bound",
    "did not report cost or aiu",
    "did not report total_cost_usd or modelusage costusd",
    "missing or invalid cost.total",
    "usage cost unavailable",
    "zero usd estimate",
    "differs from modelusage costusd",
)


@dataclass(frozen=True)
class _PricedUsage:
    amount: float
    calculation: PriceCalculation


def _cost_only_warning(warning: str) -> bool:
    normalized = warning.lower()
    return normalized.startswith("cost:") or any(part in normalized for part in _COST_ONLY_WARNING_PARTS)


def _complete_usd_cost(usage: UsageSummary, sources: Iterable[str]) -> UsageCost | None:
    matching = [cost for cost in usage.costs if cost.unit == "usd" and cost.source in sources]
    if len(matching) != 1:
        return None
    cost = matching[0]
    partial_warning = f"cost:{cost.source} is unavailable in part of the aggregate"
    return None if any(partial_warning in warning for warning in usage.warnings) else cost


def _normalize_fallback_model(model: str | None, provider: str | None) -> str | None:
    """Strip Pi's ``provider/model`` CLI prefix for provider-scoped lookup."""

    prefix = f"{provider}/" if provider else None
    normalized = model[len(prefix) :] if model and prefix and model.startswith(prefix) else model
    return _MODEL_ALIASES.get(normalized, normalized)


def _model_candidates(request: RequestUsage | None, fallback_model: str | None) -> tuple[str, ...]:
    if (
        request is not None
        and request.provider == "litellm"
        and request.resolved_model
        and request.requested_model
        and request.requested_model.partition("/")[2] == request.resolved_model
    ):
        # LiteLLM may remove exactly its routing prefix from response.model.
        # Restore only that proven identity; unrelated resolved models remain
        # fail-closed instead of falling back to the requested model.
        return (request.requested_model,)
    values = (
        request.resolved_model if request is not None else None,
        request.requested_model if request is not None else None,
        fallback_model,
    )
    return next(((value,) for value in values if isinstance(value, str) and value), ())


def _provider_candidates(
    request: RequestUsage | None,
    fallback_provider: str | None,
) -> tuple[str | None, ...]:
    provider = request.provider if request is not None and request.provider else fallback_provider
    if provider in {"copilot", "github-copilot"}:
        provider = None
    return (provider,)


def _try_price(
    *,
    input_tokens: int,
    output_tokens: int,
    cache_read_tokens: int | None,
    cache_write_tokens: int | None,
    models: Iterable[str],
    providers: Iterable[str | None],
) -> tuple[_PricedUsage | None, str | None]:
    known_cache_tokens = sum(value for value in (cache_read_tokens, cache_write_tokens) if value is not None)
    if known_cache_tokens > input_tokens:
        return None, "cache read/write tokens exceed total input tokens"

    matched_with_missing_cache: set[str] = set()
    for model in models:
        for provider in providers:
            try:
                calculation = calc_price(
                    Usage(
                        input_tokens=input_tokens,
                        output_tokens=output_tokens,
                        cache_read_tokens=cache_read_tokens or 0,
                        cache_write_tokens=cache_write_tokens or 0,
                    ),
                    model,
                    provider_id=provider,
                )
            except Exception:
                continue

            model_price = calculation.model_price
            if input_tokens > 0 and cache_read_tokens is None and model_price.cache_read_mtok is not None:
                matched_with_missing_cache.add("cache-read")
                continue
            if input_tokens > 0 and cache_write_tokens is None and model_price.cache_write_mtok is not None:
                matched_with_missing_cache.add("cache-write")
                continue
            amount = float(calculation.total_price)
            if amount < 0 or not math.isfinite(amount):
                continue
            return _PricedUsage(amount, calculation), None

    if matched_with_missing_cache:
        fields = " and ".join(sorted(matched_with_missing_cache))
        return None, f"{fields} token usage is unavailable for a model with separate cache pricing"
    return None, "model price is unavailable"


def _native_claude_cost(usage: UsageSummary) -> float | None:
    cost = _complete_usd_cost(usage, _CLAUDE_AGGREGATE_SOURCES)
    if cost is None:
        return None
    if cost.source == "claude_code.modelUsage.costUSD" and any(
        "modelUsage costUSD is missing for some models" in warning
        or "modelUsage contains malformed model entries" in warning
        for warning in usage.warnings
    ):
        return None
    amount = cost.amount
    if amount < 0 or not math.isfinite(amount):
        return None
    if amount == 0 and ((usage.input_tokens or 0) > 0 or (usage.output_tokens or 0) > 0):
        return None
    return amount


def _stored_claude_public_price(usage: UsageSummary) -> float | None:
    cost = _complete_usd_cost(usage, (_CLAUDE_PUBLIC_PRICE_SOURCE,))
    if cost is None:
        return None
    amount = cost.amount
    return amount if amount >= 0 and math.isfinite(amount) else None


def _native_pi_cost(usage: UsageSummary) -> float | None:
    partial_warning = f"cost:{_PI_AGGREGATE_SOURCE} is unavailable in part of the aggregate"
    if any(partial_warning in warning for warning in usage.warnings):
        return None
    matching = [cost for cost in usage.costs if cost.unit == "usd" and cost.source == _PI_AGGREGATE_SOURCE]
    if len(matching) != 1:
        return None
    amount = matching[0].amount
    if amount < 0 or not math.isfinite(amount):
        return None
    if amount == 0 and ((usage.input_tokens or 0) > 0 or (usage.output_tokens or 0) > 0):
        return None
    return amount


def _native_request_cost(usage: UsageSummary) -> float | None:
    if not usage.complete or usage.model_requests != len(usage.requests) or not usage.requests:
        return None
    amounts: list[float] = []
    for request in usage.requests:
        matching = [cost for cost in request.costs if cost.unit == "usd" and cost.source in _REQUEST_USD_SOURCES]
        if len(matching) != 1:
            return None
        amount = matching[0].amount
        if amount < 0 or not math.isfinite(amount):
            return None
        if amount == 0 and ((request.input_tokens or 0) > 0 or (request.output_tokens or 0) > 0):
            return None
        amounts.append(amount)
    total = sum(amounts)
    return total if math.isfinite(total) else None


def _request_usage_is_priceable(usage: UsageSummary) -> bool:
    if not usage.available or usage.model_requests != len(usage.requests) or not usage.requests:
        return False
    if usage.complete:
        return True
    return bool(usage.warnings) and all(_cost_only_warning(warning) for warning in usage.warnings)


def _aggregate_usage_is_priceable(usage: UsageSummary) -> bool:
    return usage.complete or (
        usage.available and bool(usage.warnings) and all(_cost_only_warning(warning) for warning in usage.warnings)
    )


def _tier_thresholds(calculation: PriceCalculation) -> list[int]:
    return [
        tier.start
        for value in vars(calculation.model_price).values()
        if isinstance(value, TieredPrices)
        for tier in value.tiers
    ]


def _requests_share_pricing_identity(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None,
) -> bool:
    if usage.model_requests != len(usage.requests) or not usage.requests:
        return False
    identities = {
        (_model_candidates(request, fallback_model), _provider_candidates(request, fallback_provider))
        for request in usage.requests
    }
    return len(identities) == 1 and bool(next(iter(identities))[0])


def _price_requests(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None,
) -> tuple[float | None, str | None]:
    if not _request_usage_is_priceable(usage):
        return None, "per-request token usage is incomplete"

    total = 0.0
    for request in usage.requests:
        if request.input_tokens is None or request.output_tokens is None:
            return None, "input or output tokens are unavailable for a model request"
        priced, warning = _try_price(
            input_tokens=request.input_tokens,
            output_tokens=request.output_tokens,
            cache_read_tokens=request.cache_read_input_tokens,
            cache_write_tokens=request.cache_write_input_tokens,
            models=_model_candidates(request, fallback_model),
            providers=_provider_candidates(request, fallback_provider),
        )
        if priced is None:
            return None, warning
        total += priced.amount
    return total, None


def calculate_model_aggregate_cost_usd(
    model_aggregates: Iterable[RequestUsage],
    fallback_provider: str | None,
) -> tuple[float | None, str | None]:
    """Price Claude's exact per-model totals when native USD is absent."""

    aggregates = tuple(model_aggregates)
    if not aggregates:
        return None, "per-model token usage is unavailable"

    total = 0.0
    for aggregate in aggregates:
        if aggregate.input_tokens is None or aggregate.output_tokens is None:
            return None, "input or output tokens are unavailable for a model aggregate"
        priced, warning = _try_price(
            input_tokens=aggregate.input_tokens,
            output_tokens=aggregate.output_tokens,
            cache_read_tokens=aggregate.cache_read_input_tokens,
            cache_write_tokens=aggregate.cache_write_input_tokens,
            models=_model_candidates(aggregate, None),
            providers=_provider_candidates(aggregate, fallback_provider),
        )
        if priced is None:
            return None, warning
        if _tier_thresholds(priced.calculation) and aggregate.input_tokens > min(_tier_thresholds(priced.calculation)):
            return None, "tiered pricing requires per-request usage above the model threshold"
        if priced.calculation.model_price.requests_kcount is not None:
            return None, "request-count pricing requires per-request usage"
        total += priced.amount
    return (total, None) if math.isfinite(total) else (None, "calculated model-aggregate cost is invalid")


def _price_aggregate(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None,
    request: RequestUsage | None = None,
) -> tuple[float | None, str | None]:
    if not _aggregate_usage_is_priceable(usage) or usage.input_tokens is None or usage.output_tokens is None:
        return None, "aggregate token usage is incomplete"
    priced, warning = _try_price(
        input_tokens=usage.input_tokens,
        output_tokens=usage.output_tokens,
        cache_read_tokens=usage.cache_read_input_tokens,
        cache_write_tokens=usage.cache_write_input_tokens,
        models=_model_candidates(request, fallback_model),
        providers=_provider_candidates(request, fallback_provider),
    )
    if priced is None:
        return None, warning

    model_price = priced.calculation.model_price
    thresholds = _tier_thresholds(priced.calculation)
    if thresholds and usage.input_tokens > min(thresholds) and usage.model_requests != 1:
        return None, "tiered pricing requires per-request token usage above the model threshold"
    if model_price.requests_kcount is not None and usage.model_requests != 1:
        return None, "request-count pricing requires exactly one model request for aggregate usage"
    return priced.amount, None


def _price_pi_compaction_usage(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None,
) -> tuple[float | None, str | None]:
    """Price valid Pi compaction aggregates without inventing request boundaries."""

    if not usage.available or any(
        not (_cost_only_warning(warning) or _PI_COMPACTION_BOUNDARY_WARNING in warning.lower())
        for warning in usage.warnings
    ):
        return None, "Pi compaction token usage is incomplete"
    if usage.model_requests is None or usage.model_requests < len(usage.requests) + 1:
        return None, "Pi compaction request coverage is incomplete"

    fields = (
        "input_tokens",
        "output_tokens",
        "cache_read_input_tokens",
        "cache_write_input_tokens",
    )
    aggregate = {field: getattr(usage, field) for field in fields}
    if any(value is None for value in aggregate.values()):
        return None, "Pi compaction token usage is incomplete"

    assistant_cost = 0.0
    assistant_totals = dict.fromkeys(fields, 0)
    for request in usage.requests:
        request_values = {field: getattr(request, field) for field in fields}
        if any(value is None for value in request_values.values()):
            return None, "Pi assistant request token usage is incomplete"
        priced, warning = _try_price(
            input_tokens=request.input_tokens,
            output_tokens=request.output_tokens,
            cache_read_tokens=request.cache_read_input_tokens,
            cache_write_tokens=request.cache_write_input_tokens,
            models=_model_candidates(request, fallback_model),
            providers=_provider_candidates(request, fallback_provider),
        )
        if priced is None:
            return None, warning
        assistant_cost += priced.amount
        for field, value in request_values.items():
            assert value is not None
            assistant_totals[field] += value

    compaction = {field: value - assistant_totals[field] for field, value in aggregate.items() if value is not None}
    if len(compaction) != len(fields) or any(value < 0 for value in compaction.values()):
        return None, "Pi compaction aggregate is inconsistent with assistant request usage"
    if not any(compaction.values()):
        return None, "Pi compaction aggregate contains no model usage"

    priced, warning = _try_price(
        input_tokens=compaction["input_tokens"],
        output_tokens=compaction["output_tokens"],
        cache_read_tokens=compaction["cache_read_input_tokens"],
        cache_write_tokens=compaction["cache_write_input_tokens"],
        models=_model_candidates(None, fallback_model),
        providers=_provider_candidates(None, fallback_provider),
    )
    if priced is None:
        return None, warning
    thresholds = _tier_thresholds(priced.calculation)
    if thresholds and compaction["input_tokens"] > min(thresholds):
        return None, "tiered pricing requires per-request Pi compaction usage above the model threshold"
    if priced.calculation.model_price.requests_kcount is not None:
        return None, "request-count pricing requires exact Pi compaction request boundaries"
    total = assistant_cost + priced.amount
    return (total, None) if math.isfinite(total) else (None, "calculated Pi cost is invalid")


def public_price_error(model: str | None, provider: str | None = None) -> str | None:
    """Return why a configured model cannot be priced before a run."""

    model = _normalize_fallback_model(model, provider)
    if not model:
        return "model name is unavailable"
    priced, warning = _try_price(
        input_tokens=1,
        output_tokens=1,
        cache_read_tokens=0,
        cache_write_tokens=0,
        models=(model,),
        providers=_provider_candidates(None, provider),
    )
    return None if priced is not None else warning


def _calculated_cost(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None,
) -> tuple[float | None, str | None]:
    if _PI_COMPACTION_USAGE_SOURCE in usage.sources:
        return _price_pi_compaction_usage(usage, fallback_model, fallback_provider)

    if usage.requests:
        request_cost, warning = _price_requests(usage, fallback_model, fallback_provider)
        if request_cost is not None or not _aggregate_usage_is_priceable(usage):
            return request_cost, warning
        if not _requests_share_pricing_identity(usage, fallback_model, fallback_provider):
            return request_cost, warning
        aggregate_cost, aggregate_warning = _price_aggregate(
            usage,
            fallback_model,
            fallback_provider,
            usage.requests[0],
        )
        return aggregate_cost, aggregate_warning
    return _price_aggregate(usage, fallback_model, fallback_provider)


def calculate_equivalent_cost_usd(
    usage: UsageSummary,
    fallback_model: str | None,
    fallback_provider: str | None = None,
) -> tuple[float | None, str | None]:
    """Prefer agent-reported USD, with complete public-price fallback."""

    fallback_model = _normalize_fallback_model(fallback_model, fallback_provider)

    native_cost = _native_claude_cost(usage)
    if native_cost is None:
        native_cost = _native_pi_cost(usage)
    if native_cost is None:
        native_cost = _native_request_cost(usage)
    if (
        native_cost is None
        and usage.complete
        and usage.model_requests == 0
        and usage.input_tokens == 0
        and usage.output_tokens == 0
    ):
        return 0.0, None

    calculated_cost = _stored_claude_public_price(usage)
    calculated_warning = None
    if calculated_cost is None:
        calculated_cost, calculated_warning = _calculated_cost(usage, fallback_model, fallback_provider)
    if native_cost is None:
        return calculated_cost, calculated_warning
    if calculated_cost is not None:
        if native_cost == 0:
            if calculated_cost != 0:
                return (
                    native_cost,
                    f"agent-reported USD cost $0.000000 differs from token-priced cost ${calculated_cost:.6f}",
                )
            return native_cost, None
        difference = abs(native_cost - calculated_cost) / native_cost
        if difference > _COST_DIFFERENCE_LIMIT:
            return (
                native_cost,
                f"agent-reported USD cost ${native_cost:.6f} differs from token-priced cost "
                f"${calculated_cost:.6f} by {difference:.1%}",
            )
    return native_cost, None
