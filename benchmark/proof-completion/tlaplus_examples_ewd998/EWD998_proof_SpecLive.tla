---------------------------- MODULE EWD998_proof_SpecLive ----------------------------
(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998 specification.                 *)
(***************************************************************************)
EXTENDS EWD998_proof

USE NAssumption

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

LEMMA SumEmpty ==
  ASSUME NEW fun
  PROVE  Sum(fun, {}) = 0 
PROOF OMITTED

LEMMA SumIterate ==
  ASSUME NEW fun \in [Node -> Int], 
         NEW inds \in SUBSET Node, NEW e \in inds
  PROVE  Sum(fun, inds) = fun[e] + Sum(fun, inds \ {e})
\* BY FoldFunctionOnSetIterate, NodeIsFinite, PlusACI DEF Sum (* fails *)

LEMMA SumSingleton ==
  ASSUME NEW fun \in [Node -> Int], NEW x \in Node
  PROVE  Sum(fun, {x}) = fun[x]
PROOF OMITTED

LEMMA SumUnion ==
  ASSUME NEW fun \in [Node -> Int],
         NEW inds1 \in SUBSET Node, NEW inds2 \in SUBSET Node, inds1 \cap inds2 = {}
  PROVE  Sum(fun, inds1 \cup inds2) = Sum(fun, inds1) + Sum(fun, inds2)

LEMMA SumEqual ==
  ASSUME NEW f \in [Node -> Int], NEW g \in [Node -> Int],
         NEW inds \in SUBSET Node,
         \A x \in inds : f[x] = g[x]
  PROVE  Sum(f, inds) = Sum(g, inds)
\* BY FoldFunctionOnSetEqual, NodeIsFinite DEF Sum (* fails *)

LEMMA SumIsInt == 
  ASSUME NEW fun \in [Node -> Int],
         NEW inds \in SUBSET Node
  PROVE  Sum(fun, inds) \in Int
PROOF OMITTED

LEMMA SumIsNat == 
  ASSUME NEW fun \in [Node -> Nat],
         NEW inds \in SUBSET Node
  PROVE  Sum(fun, inds) \in Nat
PROOF OMITTED

LEMMA SumZero ==
  ASSUME NEW fun \in [Node -> Int], NEW inds \in SUBSET Node,
         \A i \in inds : fun[i] = 0
  PROVE  Sum(fun, inds) = 0
PROOF OMITTED

(***************************************************************************)
(* Proof of the inductive invariant.                                       *)
(***************************************************************************)
THEOREM Invariance == Init /\ [][Next]_vars => []Inv
PROOF OMITTED

(***************************************************************************)
(* In particular, the invariant explains why the algorithm is safe.        *)
(***************************************************************************)
THEOREM Safety ==
  /\ TypeOK /\ Inv /\ terminationDetected => Termination
  /\ TypeOK' /\ Inv' /\ terminationDetected' => Termination'
PROOF OMITTED

(***************************************************************************)
(* A useful lemma for the liveness and refinement proofs.                  *)
(***************************************************************************)
LEMMA B0NoMessagePending == 
  /\ TypeOK /\ B=0 => \A i \in Node : pending[i] = 0
  /\ TypeOK' /\ B'=0 => \A i \in Node : pending'[i] = 0
PROOF OMITTED

(***************************************************************************)
(* Proofs of liveness.                                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first establish the enabledness condition for the System action.     *)
(* We exclude a special case that we are not interested in. In fact, it    *)
(* would be reasonable to assume N>1.                                      *)
(***************************************************************************)
LEMMA EnabledSystem ==
  ASSUME TypeOK, N > 1 \/ counter[0]=0
  PROVE  ENABLED <<System>>_vars
         <=> \/ /\ token.pos = 0 
                /\ token.color = "black" \/ color[0] = "black" \/ counter[0]+token.q > 0
             \/ \E i \in Node \ {0} : ~ active[i] /\ token.pos = i
PROOF OMITTED

(***************************************************************************)
(* In particular, a system transition is enabled when the token is at the  *)
(* master node and termination has not been detected.                      *)
(***************************************************************************)
COROLLARY EnabledAtMaster ==
  ASSUME TypeOK, Inv, Termination, token.pos = 0, ~ terminationDetected
  PROVE  ENABLED <<System>>_vars
PROOF OMITTED

(***************************************************************************)
(* Assuming the system has terminated, termination detection may require   *)
(* up to three rounds of the token:                                        *)
(* 1. The first round simply brings the token back to the master node.     *)
(* 2. The second round brings the token back to the master, with all nodes *)
(*    being colored white.                                                 *)
(* 3. The third round verifies that all nodes are white and brings back a  *)
(*    white token to the master node. Moreover, the counter held by the    *)
(*    token corresponds to the sum of the non-master nodes.                *)
(* At the end of the third round, the invariant ensures that the master    *)
(* node detects termination.                                               *)
(* The proof becomes a little simpler if we assume, aiming for a           *)
(* contradiction, that termination is never detected. This motivates the   *)
(* definition of the following operator BSpec.                             *)
(***************************************************************************)

atMaster == token.pos = 0
tknWhite == token.color = "white"
tknCount == token.q = Sum(counter, Rng(1,N-1))
allWhite == \A i \in Node : color[i] = "white"

LEMMA Round1 == BSpec => (Termination
                            ~> Termination /\ atMaster)
PROOF OMITTED

LEMMA Round2 == BSpec => (Termination /\ atMaster
                            ~> Termination /\ atMaster /\ allWhite)
PROOF OMITTED

LEMMA Round3 == BSpec => (Termination /\ atMaster /\ allWhite
                            ~> Termination /\ atMaster /\ allWhite /\ tknWhite /\ tknCount)
PROOF OMITTED

LEMMA Detection == 
  TypeOK /\ Inv /\ Termination /\ atMaster /\ allWhite /\ tknWhite /\ tknCount
    => terminationDetected
PROOF OMITTED

THEOREM Live == []TypeOK /\ []Inv /\ [][Next]_vars /\ WF_vars(System) => Liveness
PROOF OMITTED

COROLLARY SpecLive == Spec => Liveness
PROOF OBVIOUS

(***************************************************************************)
(* Refinement proof.                                                       *)
(* In order to reuse lemmas about the high-level specification, we         *)
(* instantiate the corresponding proof module.                             *)
(***************************************************************************)

(***************************************************************************)
(* The (state-level) safety invariant `TerminationDetection`:              *)
(* `terminationDetected => Termination`.  Direct corollary of Safety       *)
(* together with the type and Inv invariance theorems.                     *)
(***************************************************************************)

=============================================================================
\* Modification History
\* Last modified Fri Jul 01 09:08:35 CEST 2022 by merz
\* Created Wed Apr 13 08:20:53 CEST 2022 by merz
