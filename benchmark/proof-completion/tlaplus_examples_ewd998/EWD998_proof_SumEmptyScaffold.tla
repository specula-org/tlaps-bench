---------------------------- MODULE EWD998_proof_SumEmptyScaffold ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998 specification.                 *)
(***************************************************************************)
EXTENDS EWD998_proofModel

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Init /\ [][Next]_vars => []TypeOK
PROOF OMITTED

(***************************************************************************)
(* Lemmas about FoldFunction that should go to a library.                  *)
(***************************************************************************)
IsAssociativeOn(op(_,_), S) ==
  \A x,y,z \in S : op(x, op(y,z)) = op(op(x,y), z)
  
IsCommutativeOn(op(_,_), S) ==
  \A x,y \in S : op(x,y) = op(y,x)
  
IsIdentityOn(op(_,_), e, S) ==
  \A x \in S : op(e,x) = x

LEMMA FoldFunctionIsFoldFunctionOnSet ==
  ASSUME NEW op(_,_), NEW base, NEW fun
  PROVE  FoldFunction(op, base, fun) = FoldFunctionOnSet(op, base, fun, DOMAIN fun)

LEMMA FoldFunctionOnSetEmpty ==
  ASSUME NEW op(_,_), NEW base, NEW fun
  PROVE  FoldFunctionOnSet(op, base, fun, {}) = base 

LEMMA FoldFunctionOnSetIterate ==
  ASSUME NEW op(_,_), 
         NEW S, IsFiniteSet(S), NEW T, 
         NEW base \in T, NEW fun \in [S -> T], 
         NEW inds \in SUBSET S, NEW e \in inds,
         IsAssociativeOn(op, T), IsCommutativeOn(op, T), IsIdentityOn(op, base, T)
  PROVE  FoldFunctionOnSet(op, base, fun, inds)
       = op(fun[e], FoldFunctionOnSet(op, base, fun, inds \ {e}))

LEMMA FoldFunctionOnSetUnion ==
  ASSUME NEW op(_,_),
         NEW S, IsFiniteSet(S), NEW T,
         NEW base \in T, NEW fun \in [S -> T],
         NEW inds1 \in SUBSET S, NEW inds2 \in SUBSET S, inds1 \cap inds2 = {},
         IsAssociativeOn(op, T), IsCommutativeOn(op, T), IsIdentityOn(op, base, T)
  PROVE  FoldFunctionOnSet(op, base, fun, inds1 \cup inds2)
         = op(FoldFunctionOnSet(op, base, fun, inds1), FoldFunctionOnSet(op, base, fun, inds2))

LEMMA FoldFunctionOnSetEqual ==
  ASSUME NEW op(_,_),
         NEW S, IsFiniteSet(S), NEW T, NEW base \in T,
         NEW f \in [S -> T], NEW g \in [S -> T],
         NEW inds \in SUBSET S,
         \A x \in inds : f[x] = g[x]
  PROVE  FoldFunctionOnSet(op, base, f, inds) = FoldFunctionOnSet(op, base, g, inds)

LEMMA FoldFunctionOnSetType == 
  ASSUME NEW op(_,_),
         NEW S, NEW T, IsFiniteSet(S), 
         NEW base \in T, NEW fun \in [S -> T],
         NEW inds \in SUBSET S,
         \A x,y \in T : op(x,y) \in T
  PROVE  FoldFunctionOnSet(op, base, fun, inds) \in T

(***************************************************************************)
(* The provers have trouble applying these generic lemmas to the specific  *)
(* instances required for the spec so we restate them for the operators    *)
(* that appear in the definition of the inductive invariant.               *)
(***************************************************************************)
LEMMA NodeIsFinite == IsFiniteSet(Node)
PROOF OMITTED

LEMMA PlusACI ==
  /\ IsAssociativeOn(+, Nat)
  /\ IsCommutativeOn(+, Nat)
  /\ IsIdentityOn(+, 0, Nat)
  /\ IsAssociativeOn(+, Int)
  /\ IsCommutativeOn(+, Int)
  /\ IsIdentityOn(+, 0, Int)
PROOF OMITTED

=============================================================================
