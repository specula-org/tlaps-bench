"""Mode registry."""

from .base import Mode
from .proof_completion import ProofCompletion
from .proof_from_scratch import ProofFromScratch

_REGISTRY: dict[str, type[Mode]] = {
    ProofCompletion.name: ProofCompletion,
    ProofFromScratch.name: ProofFromScratch,
}


def get_mode(name: str, benchmark_root: str, checker_binary: str) -> Mode:
    if name not in _REGISTRY:
        raise ValueError(f"unknown mode {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name](benchmark_root, checker_binary)


def list_modes() -> list[str]:
    return sorted(_REGISTRY)
