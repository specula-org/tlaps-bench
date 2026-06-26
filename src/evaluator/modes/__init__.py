"""Mode registry."""

from .auto_complete import AutoComplete
from .base import Mode
from .synthesis_from_scratch import SynthesisFromScratch

_REGISTRY: dict[str, type[Mode]] = {
    AutoComplete.name: AutoComplete,
    SynthesisFromScratch.name: SynthesisFromScratch,
}


def get_mode(name: str, benchmark_root: str, checker_binary: str) -> Mode:
    if name not in _REGISTRY:
        raise ValueError(f"unknown mode {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name](benchmark_root, checker_binary)


def list_modes() -> list[str]:
    return sorted(_REGISTRY)
