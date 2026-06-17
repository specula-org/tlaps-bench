"""Typed view of a TLA+ module's SANY semantic dump.

These dataclasses mirror the JSON emitted by ``tlacore/sany/DumpSemantics.java``
(see ``sany/dump.py`` for the loader). Working on this typed model — rather than
the raw source text — is what makes the checker robust to line breaks, inline
comments, multi-line ASSUME/PROVE, and keywords appearing inside strings: SANY
has already parsed all of that away.

Key signals the checker relies on:
  * ``Theorem.is_admitted`` — the theorem carries NO real proof obligation. This
    is true when the theorem has no proof clause at all (``proof_loc is None``,
    a bare ``THEOREM Foo == P``) or an explicit ``PROOF OMITTED``. Both are
    treated by tlapm as axioms — admitted without checking. This is the core of
    the bare-theorem / OMITTED cheat.
  * ``Theorem.references`` — the theorem/lemma names cited by this proof's
    BY/USE/DEFS. Used to tell whether a proof *depends on* an admitted statement.
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass(frozen=True)
class Loc:
    line_start: int
    column_start: int
    line_end: int
    column_end: int

    @classmethod
    def parse(cls, d: dict | None) -> Loc | None:
        if not d:
            return None
        return cls(
            d.get("line_start", 0),
            d.get("column_start", 0),
            d.get("line_end", 0),
            d.get("column_end", 0),
        )


@dataclass
class Theorem:
    name: str | None  # None for unnamed THEOREM ... (e.g. the target)
    loc: Loc | None
    statement_loc: Loc | None
    proof_loc: Loc | None  # None => no proof clause at all (bare theorem)
    proof_is_omitted: bool  # True => PROOF OMITTED
    references: list[str]  # theorem/lemma names cited by BY/USE/DEFS
    statement_references: list[str]
    shape: dict
    raw: dict = field(default_factory=dict, repr=False)

    @property
    def is_admitted(self) -> bool:
        """No real proof obligation: bare (no proof) or PROOF OMITTED.

        tlapm admits both without checking — they act as free axioms. A theorem
        with a genuine proof has ``proof_loc`` set and ``proof_is_omitted`` False.
        """
        return self.proof_loc is None or self.proof_is_omitted

    @property
    def display_name(self) -> str:
        if self.name:
            return self.name
        line = self.loc.line_start if self.loc else "?"
        return f"<unnamed L{line}>"

    @classmethod
    def parse(cls, d: dict) -> Theorem:
        return cls(
            name=d.get("name"),
            loc=Loc.parse(d.get("loc")),
            statement_loc=Loc.parse(d.get("statement_loc")),
            proof_loc=Loc.parse(d.get("proof_loc")),
            proof_is_omitted=bool(d.get("proof_is_omitted", False)),
            references=list(d.get("references") or []),
            statement_references=list(d.get("statement_references") or []),
            shape=d.get("shape") or {},
            raw=d,
        )


@dataclass
class Assumption:
    name: str | None
    is_axiom: bool  # True => AXIOM, False => ASSUME/ASSUMPTION
    loc: Loc | None
    references: list[str]

    @classmethod
    def parse(cls, d: dict) -> Assumption:
        return cls(
            name=d.get("name"),
            is_axiom=bool(d.get("is_axiom", False)),
            loc=Loc.parse(d.get("loc")),
            references=list(d.get("references") or []),
        )


@dataclass
class Instance:
    name: str | None  # e.g. "C" in `C == INSTANCE Consensus`
    module: str | None  # the instantiated module name
    loc: Loc | None
    references: list[str]

    @classmethod
    def parse(cls, d: dict) -> Instance:
        return cls(
            name=d.get("name"),
            module=d.get("module"),
            loc=Loc.parse(d.get("loc")),
            references=list(d.get("references") or []),
        )


@dataclass
class Operator:
    name: str
    loc: Loc | None
    is_spec_formula: bool
    body_kind: str | None
    references: list[str]

    @classmethod
    def parse(cls, d: dict) -> Operator:
        return cls(
            name=d.get("name"),
            loc=Loc.parse(d.get("loc")),
            is_spec_formula=bool(d.get("is_spec_formula", False)),
            body_kind=d.get("body_kind"),
            references=list(d.get("references") or []),
        )


@dataclass
class Symbol:
    """A CONSTANT or VARIABLE declaration."""

    name: str
    loc: Loc | None

    @classmethod
    def parse(cls, d: dict) -> Symbol:
        return cls(name=d.get("name"), loc=Loc.parse(d.get("loc")))


@dataclass
class Module:
    name: str
    source_file: str | None
    filename: str | None
    line_start: int
    line_end: int
    extends: list[str]
    constants: list[Symbol]
    variables: list[Symbol]
    assumes: list[Assumption]
    instances: list[Instance]
    operators: list[Operator]
    spec_formulas: list[str]
    theorems: list[Theorem]
    raw: dict = field(default_factory=dict, repr=False)

    @classmethod
    def parse(cls, d: dict) -> Module:
        return cls(
            name=d.get("module"),
            source_file=d.get("source_file"),
            filename=d.get("filename"),
            line_start=d.get("module_line_start", 0),
            line_end=d.get("module_line_end", 0),
            extends=list(d.get("extends") or []),
            constants=[Symbol.parse(x) for x in d.get("constants", [])],
            variables=[Symbol.parse(x) for x in d.get("variables", [])],
            assumes=[Assumption.parse(x) for x in d.get("assumes", [])],
            instances=[Instance.parse(x) for x in d.get("instances", [])],
            operators=[Operator.parse(x) for x in d.get("operators", [])],
            spec_formulas=list(d.get("spec_formulas") or []),
            theorems=[Theorem.parse(x) for x in d.get("theorems", [])],
            raw=d,
        )

    # -- convenience queries -------------------------------------------------

    @property
    def admitted_theorems(self) -> list[Theorem]:
        """Theorems with no real proof (bare or OMITTED) = treated as axioms."""
        return [t for t in self.theorems if t.is_admitted]

    @property
    def referenced_modules(self) -> set[str]:
        """Modules this one pulls in via EXTENDS or INSTANCE."""
        mods = set(self.extends)
        mods |= {i.module for i in self.instances if i.module}
        return mods
