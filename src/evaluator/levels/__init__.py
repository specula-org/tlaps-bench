"""Level registry."""

from .base import Level
from .level1 import Level1
from .level2 import Level2

_REGISTRY: dict[str, type[Level]] = {
    Level1.name: Level1,
    Level2.name: Level2,
}


def get_level(name: str, benchmark_root: str, checker_binary: str) -> Level:
    if name not in _REGISTRY:
        raise ValueError(f"unknown level {name!r}; available: {sorted(_REGISTRY)}")
    return _REGISTRY[name](benchmark_root, checker_binary)


def list_levels() -> list[str]:
    return sorted(_REGISTRY)
