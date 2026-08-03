"""Equivalent public API cost calculation."""

from __future__ import annotations

import pytest

from evaluator.backends import get_backend
from evaluator.cost import calculate_equivalent_cost_usd, calculate_model_aggregate_cost_usd, public_price_error
from evaluator.usage import RequestUsage, UsageCost, UsageSummary


def _request(
    *,
    input_tokens: int | None = 100,
    output_tokens: int | None = 10,
    cache_read: int | None = 0,
    cache_write: int | None = 0,
    model: str | None = "gpt-5.6-sol",
    requested_model: str | None = None,
    provider: str | None = "openai",
    costs: tuple[UsageCost, ...] = (),
) -> RequestUsage:
    return RequestUsage(
        input_tokens=input_tokens,
        output_tokens=output_tokens,
        cache_read_input_tokens=cache_read,
        cache_write_input_tokens=cache_write,
        requested_model=requested_model,
        resolved_model=model,
        provider=provider,
        costs=costs,
    )


def _summary(
    requests: tuple[RequestUsage, ...],
    *,
    complete: bool = True,
    is_lower_bound: bool = False,
    warnings: tuple[str, ...] = (),
) -> UsageSummary:
    return UsageSummary.from_requests(
        requests,
        source="test",
        complete=complete,
        is_lower_bound=is_lower_bound,
        warnings=warnings,
        totals={"model_requests": len(requests)},
    )


def test_exact_zero_request_usage_costs_zero():
    usage = UsageSummary(
        input_tokens=0,
        output_tokens=0,
        model_requests=0,
        complete=True,
    )

    assert calculate_equivalent_cost_usd(usage, "unknown") == (0.0, None)


def test_native_cost_takes_precedence_over_exact_zero_token_summary():
    usage = UsageSummary(
        input_tokens=0,
        output_tokens=0,
        model_requests=0,
        costs=(UsageCost(0.1, "usd", "claude_code.total_cost_usd"),),
        complete=True,
    )

    assert calculate_equivalent_cost_usd(usage, "unknown") == (0.1, None)


def test_claude_code_authoritative_aggregate_cost_is_preferred():
    usage = UsageSummary(
        input_tokens=1_000,
        output_tokens=100,
        model_requests=2,
        costs=(UsageCost(0.125, "usd", "claude_code.total_cost_usd"),),
        complete=False,
        is_lower_bound=True,
        warnings=("Claude Code model_requests is a lower bound",),
    )

    assert calculate_equivalent_cost_usd(usage, "claude-opus-4-8") == (0.125, None)


def test_conflicting_claude_code_cost_uses_primary_native_total():
    usage = UsageSummary(
        input_tokens=1_000,
        output_tokens=100,
        costs=(UsageCost(0.125, "usd", "claude_code.total_cost_usd"),),
        complete=False,
        is_lower_bound=True,
        warnings=("Claude Code total_cost_usd 0.125 differs from modelUsage costUSD 0.2",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "claude-opus-4-8")

    assert cost == 0.125
    assert warning is None


@pytest.mark.parametrize(
    "warning",
    [
        "Claude Code modelUsage costUSD is missing for some models",
        "Claude Code modelUsage contains malformed model entries",
    ],
)
def test_partial_claude_code_model_usage_cost_is_unavailable(warning):
    usage = UsageSummary(
        input_tokens=1_000,
        output_tokens=100,
        model_requests=2,
        costs=(UsageCost(0.125, "usd", "claude_code.modelUsage.costUSD"),),
        complete=False,
        is_lower_bound=True,
        warnings=(warning,),
    )

    cost, reason = calculate_equivalent_cost_usd(usage, "claude-opus-4-8")

    assert cost is None
    assert reason is not None


@pytest.mark.parametrize(
    "source",
    [
        "claude_code.total_cost_usd",
        "claude_code.modelUsage.costUSD",
        "claude_code.modelUsage.public_price",
    ],
)
def test_partial_claude_code_aggregate_cost_source_is_unavailable(source):
    usage = UsageSummary(
        input_tokens=500,
        output_tokens=50,
        model_requests=1,
        costs=(UsageCost(0.125, "usd", source),),
        complete=True,
    ).merge(
        UsageSummary(
            input_tokens=500,
            output_tokens=50,
            model_requests=1,
            complete=True,
        )
    )
    partial_warning = f"cost:{source} is unavailable in part of the aggregate; total is a lower bound"

    cost, warning = calculate_equivalent_cost_usd(usage, "does-not-exist")

    assert partial_warning in usage.warnings
    assert cost is None
    assert warning is not None


def test_complete_pi_native_request_cost_is_used():
    request = _request(
        costs=(UsageCost(0.0042, "usd", "pi.usage.cost.total"),),
    )

    cost, warning = calculate_equivalent_cost_usd(_summary((request,)), "gpt-5.6-sol")

    assert cost == 0.0042
    assert warning is not None
    assert "differs from token-priced cost" in warning


def test_native_cost_within_ten_percent_does_not_warn():
    request = _request(
        input_tokens=1_000,
        output_tokens=100,
        costs=(UsageCost(0.0087, "usd", "pi.usage.cost.total"),),
    )

    cost, warning = calculate_equivalent_cost_usd(_summary((request,)), "gpt-5.6-sol")

    assert cost == 0.0087
    assert warning is None


def test_pi_authoritative_session_cost_survives_unknown_compaction_request_boundaries():
    usage = UsageSummary(
        input_tokens=2_000,
        output_tokens=200,
        model_requests=2,
        costs=(UsageCost(0.125, "usd", "pi.session.usage.cost.total"),),
        complete=False,
        is_lower_bound=True,
        warnings=("Pi compaction usage may aggregate one or more summarizer calls",),
    )

    assert calculate_equivalent_cost_usd(usage, "gpt-5.6-sol") == (0.125, None)


def test_pi_session_cost_missing_from_part_of_aggregate_is_unavailable():
    usage = UsageSummary(
        input_tokens=2_000,
        output_tokens=200,
        model_requests=2,
        costs=(UsageCost(0.125, "usd", "pi.session.usage.cost.total"),),
        complete=False,
        is_lower_bound=True,
        warnings=("cost:pi.session.usage.cost.total is unavailable in part of the aggregate; total is a lower bound",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "does-not-exist")

    assert cost is None
    assert warning is not None


def test_nonzero_pi_session_usage_with_zero_native_cost_falls_back_to_public_price():
    usage = UsageSummary(
        input_tokens=1_000,
        output_tokens=100,
        cache_read_input_tokens=0,
        cache_write_input_tokens=0,
        model_requests=1,
        costs=(UsageCost(0.0, "usd", "pi.session.usage.cost.total"),),
        complete=True,
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost == pytest.approx(0.008)
    assert warning is None


def test_nonzero_tokens_with_native_zero_fall_back_to_public_price():
    request = _request(
        input_tokens=1_000,
        output_tokens=100,
        costs=(UsageCost(0.0, "usd", "pi.usage.cost.total"),),
    )
    usage = _summary(
        (request,),
        warnings=("Pi reported nonzero tokens with a zero USD estimate",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost == pytest.approx(0.008)
    assert warning is None


def test_missing_litellm_native_cost_can_be_calculated_from_complete_tokens():
    request = _request(model="claude-sonnet-4-6", provider="litellm")
    usage = _summary(
        (request,),
        complete=False,
        is_lower_bound=True,
        warnings=("LiteLLM cost is unavailable for 1 model request(s); total is a lower bound",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "claude-sonnet-4-6", "litellm")

    assert cost == pytest.approx(0.00045)
    assert warning is None


def test_litellm_exactly_stripped_provider_prefix_keeps_pricing_identity():
    request = _request(
        model="anthropic.claude-opus-4-8-v1:0",
        requested_model="bedrock/anthropic.claude-opus-4-8-v1:0",
        provider="litellm",
    )

    cost, warning = calculate_equivalent_cost_usd(
        _summary((request,)),
        "bedrock/anthropic.claude-opus-4-8-v1:0",
        "litellm",
    )

    assert cost == pytest.approx(0.000825)
    assert warning is None


def test_litellm_unrelated_resolved_model_does_not_reuse_requested_provider_prefix():
    request = _request(
        model="definitely-unknown-model",
        requested_model="bedrock/anthropic.claude-opus-4-8-v1:0",
        provider="litellm",
    )

    cost, warning = calculate_equivalent_cost_usd(
        _summary((request,)),
        "bedrock/anthropic.claude-opus-4-8-v1:0",
        "litellm",
    )

    assert cost is None
    assert warning == "model price is unavailable"


def test_missing_pi_native_cost_uses_complete_public_price_data():
    usage = _summary(
        (_request(costs=()),),
        complete=False,
        is_lower_bound=True,
        warnings=("Pi assistant usage has missing or invalid cost.total",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost == pytest.approx(0.0008)
    assert warning is None


def test_single_claude_request_can_use_settled_aggregate_tokens_when_native_cost_is_missing():
    request = _request(
        input_tokens=1_000,
        output_tokens=None,
        model="claude-opus-4-8",
        requested_model="claude-opus-4-8",
        provider="anthropic",
    )
    usage = UsageSummary.from_requests(
        (request,),
        source="claude_code_stream_json",
        complete=False,
        is_lower_bound=True,
        warnings=("Claude Code result event did not report total_cost_usd or modelUsage costUSD",),
        totals={
            "input_tokens": 1_000,
            "output_tokens": 100,
            "cache_read_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "model_requests": 1,
        },
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "claude-opus-4-8")

    assert cost == pytest.approx(0.0075)
    assert warning is None


def test_same_model_claude_requests_can_use_settled_aggregate_tokens_when_native_cost_is_missing():
    requests = tuple(
        _request(
            input_tokens=1_000,
            output_tokens=None,
            model="claude-opus-4-8",
            requested_model="claude-opus-4-8",
            provider="anthropic",
        )
        for _ in range(2)
    )
    usage = UsageSummary.from_requests(
        requests,
        source="claude_code_stream_json",
        complete=False,
        is_lower_bound=True,
        warnings=("Claude Code result event did not report total_cost_usd or modelUsage costUSD",),
        totals={
            "input_tokens": 2_000,
            "output_tokens": 200,
            "cache_read_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "model_requests": 2,
        },
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "claude-opus-4-8", "anthropic")

    assert cost == pytest.approx(0.015)
    assert warning is None


@pytest.mark.parametrize(
    ("input_tokens", "expected_cost", "expected_warning"),
    [
        (200_000, 1.0, None),
        (272_001, None, "tiered pricing requires per-request token usage above the model threshold"),
    ],
)
def test_same_model_aggregate_fallback_respects_tier_boundaries(input_tokens, expected_cost, expected_warning):
    requests = tuple(_request(input_tokens=input_tokens // 2, output_tokens=None) for _ in range(2))
    usage = UsageSummary.from_requests(
        requests,
        source="test",
        complete=False,
        is_lower_bound=True,
        warnings=("cost is unavailable",),
        totals={
            "input_tokens": input_tokens,
            "output_tokens": 0,
            "cache_read_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "model_requests": 2,
        },
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol", "openai")

    if expected_cost is None:
        assert cost is None
    else:
        assert cost == pytest.approx(expected_cost)
    assert warning == expected_warning


def test_cross_model_requests_do_not_use_one_aggregate_price():
    requests = (
        _request(output_tokens=None, model="claude-opus-4-8", provider="anthropic"),
        _request(output_tokens=None, model="claude-sonnet-4-6", provider="anthropic"),
    )
    usage = UsageSummary.from_requests(
        requests,
        source="test",
        complete=False,
        is_lower_bound=True,
        warnings=("cost is unavailable",),
        totals={
            "input_tokens": 200,
            "output_tokens": 20,
            "cache_read_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "model_requests": 2,
        },
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "claude-opus-4-8", "anthropic")

    assert cost is None
    assert warning == "input or output tokens are unavailable for a model request"


def test_fatal_usage_warning_does_not_become_a_price():
    usage = _summary(
        (_request(),),
        complete=False,
        is_lower_bound=True,
        warnings=("JSONL contains a malformed nonempty line",),
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost is None
    assert warning == "per-request token usage is incomplete"


def test_copilot_claude_dotted_alias_is_matched_without_provider_hint():
    request = _request(
        input_tokens=100,
        output_tokens=10,
        model="claude-opus-4.8",
        provider="github-copilot",
        costs=(UsageCost(1.0, "model_multiplier", "assistant.usage.cost"),),
    )

    cost, warning = calculate_equivalent_cost_usd(_summary((request,)), "claude-opus-4.8", "copilot")

    assert cost == pytest.approx(0.00075)
    assert warning is None


def test_gpt_5_6_cache_read_write_and_tier_prices_are_applied():
    request = _request(
        input_tokens=1_000_000,
        output_tokens=100_000,
        cache_read=100_000,
        cache_write=50_000,
    )

    cost, warning = calculate_equivalent_cost_usd(_summary((request,)), "gpt-5.6-sol")

    assert cost == pytest.approx(13.725)
    assert warning is None


def test_multiple_requests_are_priced_individually_before_tier_threshold():
    usage = _summary(
        (
            _request(input_tokens=200_000, output_tokens=0),
            _request(input_tokens=200_000, output_tokens=0),
        )
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost == pytest.approx(2.0)
    assert warning is None


def test_aggregate_above_tier_threshold_without_request_count_is_unavailable():
    usage = UsageSummary(
        input_tokens=400_000,
        output_tokens=0,
        cache_read_input_tokens=0,
        cache_write_input_tokens=0,
        model_requests=None,
        complete=True,
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost is None
    assert warning == "tiered pricing requires per-request token usage above the model threshold"


@pytest.mark.parametrize(
    ("model_requests", "expected_cost"),
    [
        (1, 0.01211),
        (2, None),
        (None, None),
    ],
)
def test_aggregate_request_fee_requires_exactly_one_request(model_requests, expected_cost):
    usage = UsageSummary(
        input_tokens=100,
        output_tokens=10,
        cache_read_input_tokens=0,
        cache_write_input_tokens=0,
        model_requests=model_requests,
        complete=True,
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "sonar", "perplexity")

    if expected_cost is None:
        assert cost is None
        assert warning == "request-count pricing requires exactly one model request for aggregate usage"
    else:
        assert cost == pytest.approx(expected_cost)
        assert warning is None


def test_model_aggregate_above_tier_threshold_is_unavailable():
    cost, warning = calculate_model_aggregate_cost_usd(
        (
            _request(
                input_tokens=272_001,
                output_tokens=0,
                cache_read=0,
                cache_write=0,
            ),
        ),
        "openai",
    )

    assert cost is None
    assert warning == "tiered pricing requires per-request usage above the model threshold"


@pytest.mark.parametrize(
    ("input_tokens", "model_requests", "expected"),
    [
        (272_000, None, 1.36),
        (272_001, 1, 2.72001),
    ],
)
def test_aggregate_tier_boundary_is_exact(input_tokens, model_requests, expected):
    usage = UsageSummary(
        input_tokens=input_tokens,
        output_tokens=0,
        cache_read_input_tokens=0,
        cache_write_input_tokens=0,
        model_requests=model_requests,
        complete=True,
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost == pytest.approx(expected)
    assert warning is None


def test_missing_priced_cache_bucket_is_unavailable():
    usage = _summary((_request(cache_write=None),))

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost is None
    assert warning == "cache-write token usage is unavailable for a model with separate cache pricing"


def test_invalid_cache_classification_is_unavailable():
    usage = _summary((_request(input_tokens=100, cache_read=90, cache_write=20),))

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.6-sol")

    assert cost is None
    assert warning == "per-request token usage is incomplete"


def test_unknown_model_is_not_reported_as_zero():
    usage = _summary((_request(model="does-not-exist"),))

    cost, warning = calculate_equivalent_cost_usd(usage, "does-not-exist")

    assert cost is None
    assert warning == "model price is unavailable"


def test_public_price_preflight_distinguishes_known_and_unknown_models():
    assert public_price_error("gpt-5.6-sol", "openai") is None
    assert public_price_error("definitely-not-a-real-model", "openai") == "model price is unavailable"


def test_public_price_preflight_normalizes_pi_github_copilot_provider():
    assert public_price_error("github-copilot/claude-opus-4.8", "github-copilot") is None


def test_public_price_preflight_normalizes_cursor_default_model():
    assert public_price_error("sonnet-4.5") is None


@pytest.mark.parametrize(
    "backend_name",
    ["codex", "claude_code", "copilot", "copilot_oneshot", "cursor", "litellm", "litellm_oneshot", "pi"],
)
def test_supported_backends_require_public_price_preflight(backend_name):
    assert get_backend(backend_name).requires_public_pricing


def test_unknown_resolved_model_does_not_fall_back_to_requested_model_price():
    usage = _summary(
        (
            _request(
                model="definitely-unknown-model",
                requested_model="gpt-5.5",
            ),
        )
    )

    cost, warning = calculate_equivalent_cost_usd(usage, "gpt-5.5")

    assert cost is None
    assert warning == "model price is unavailable"


@pytest.mark.parametrize(
    ("model", "provider"),
    [
        ("claude-opus-4-6", "openai"),
        ("gpt-5.6-sol", "definitely-not-provider"),
    ],
)
def test_mismatched_or_unknown_provider_does_not_fall_back_to_default_provider(model, provider):
    usage = _summary((_request(model=model, provider=provider),))

    cost, warning = calculate_equivalent_cost_usd(usage, model)

    assert cost is None
    assert warning == "model price is unavailable"
