---- MODULE EWD998_proof_Detection ----
EXTENDS FiniteSetTheorems, FiniteSets, Functions, Integers, TLAPS
(* ---- Content from module EWD998 ---- *)
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Shmuel Safra, published as EWD 998:         *)
(* Shmuel Safra's version of termination detection.                        *)
(* https://www.cs.utexas.edu/users/EWD/ewd09xx/EWD998.PDF                  *)
(***************************************************************************)

CONSTANT
    \* @type: Int;
    N
ASSUME NAssumption == N \in Nat \ {0} \* At least one node.

Node == 0 .. N-1
Color == {"white", "black"}
Token == [pos : Node, q : Int, color : Color]

VARIABLES 
 \* @type: Int -> Bool;
 active,     \* activation status of nodes
 \* @type: Int -> Str;
 color,      \* color of nodes
 \* @type: Int -> Int;
 counter,    \* nb of sent messages - nb of rcvd messages per node
 \* @type: Int -> Int;
 pending,    \* nb of messages in transit to node
 \* @type: [ pos: Int, q: Int, color: Str ];
 token       \* token structure
  
vars == <<active, color, counter, pending, token>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ counter \in [Node -> Int]
  /\ pending \in [Node -> Nat]
  /\ token \in Token
------------------------------------------------------------------------------
 
Init ==
  (* EWD840 but nodes *) 
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  (* Rule 0 *)
  /\ counter = [i \in Node |-> 0] \* c properly initialized
  /\ pending = [i \in Node |-> 0]
  /\ token \in [ pos: Node, q: {0}, color: {"black"} ]

InitiateProbe ==
  (* Rules 1 + 5 + 6 *)
  /\ token.pos = 0
  /\ \* previous round not conclusive if:
     \/ token.color = "black"
     \/ color[0] = "black"
     \/ counter[0] + token.q > 0
  /\ token' = [pos |-> N-1, q |-> 0, color |-> "white"]
  /\ color' = [ color EXCEPT ![0] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>                            
  
PassToken(i) ==
  (* Rules 2 + 4 + 7 *)
  /\ ~ active[i] \* If machine i is active, keep the token.
  /\ token.pos = i
  /\ token' = [pos |-> token.pos - 1,
               q |-> token.q + counter[i],
               color |-> IF color[i] = "black" THEN "black" ELSE token.color]
            \*    color |-> color[i] ]
  /\ color' = [ color EXCEPT ![i] = "white" ]
  \* The state of the nodes remains unchanged by token-related actions.
  /\ UNCHANGED <<active, counter, pending>>

System == \/ InitiateProbe
          \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------

SendMsg(i) ==
  \* Only allowed to send msgs if node i is active.
  /\ active[i]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ + 1]
  \* Non-deterministically choose a receiver node.
  /\ \E j \in Node \ {i} : pending' = [pending EXCEPT ![j] = @ + 1]
          \* Note that we don't blacken node i as in EWD840 if node i
          \* sends a message to node j with j > i
  /\ UNCHANGED <<active, color, token>>

RecvMsg(i) ==
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = @ - 1]
  (* Rule 0 *)
  /\ counter' = [counter EXCEPT ![i] = @ - 1]
  (* Rule 3 *)
  /\ color' = [ color EXCEPT ![i] = "black" ]
  \* Receipt of a message activates i.
  /\ active' = [ active EXCEPT ![i] = TRUE ]
  /\ UNCHANGED <<token>>                           

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, counter, pending, token>>

Environment == \E i \in Node : SendMsg(i) \/ RecvMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next ==
  System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Bound the otherwise infinite state space that TLC has to check.         *)
(***************************************************************************)
StateConstraint ==
  /\ \A i \in Node : counter[i] <= 3 /\ pending[i] <= 3
  /\ token.q <= 9

-----------------------------------------------------------------------------

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 and there are *)
(* no in-flight messages then every node is inactive.                      *)
(***************************************************************************)
terminationDetected ==
  /\ token.pos = 0
  /\ token.color = "white"
  /\ token.q + counter[0] = 0
  /\ color[0] = "white"
  /\ ~ active[0]

(***************************************************************************)
(* Sum of the values f[x], for x \in S \subseteq DOMAIN f.                 *)
(***************************************************************************)
Sum(f, S) == FoldFunctionOnSet(+, 0, f, S)

(***************************************************************************)
(* The number of messages on their way. "in-flight"                        *)
(***************************************************************************)
B == Sum(pending, Node)

(***************************************************************************)
(* The system has terminated if no node is active and there are no         *)
(* in-flight messages.                                                     *)
(***************************************************************************)
Termination == 
  /\ \A i \in Node : ~ active[i]
  /\ B = 0

TerminationDetection ==
  terminationDetected => Termination

(***************************************************************************)
(* Interval of nodes between a and b: this is just a..b, but the following *)
(* definition helps Apalache to construct a bounded set.                   *)
(***************************************************************************)
Rng(a,b) == { i \in Node: a <= i /\ i <= b }


(***************************************************************************)
(* Safra's inductive invariant                                             *)
(***************************************************************************)
Inv == 
  \* The number of counted messages at each node and the number of messages in transit is consistent.
  /\ P0:: B = Sum(counter, Node)
     (* (Ai: t < i < N: machine nr.i is passive) /\ *)
     (* (Si: t < i < N: ci.i) = q *)
  /\ \/ P1:: /\ \A i \in Rng(token.pos+1, N-1): active[i] = FALSE \* machine nr.i is passive
             /\ IF token.pos = N-1 
                THEN token.q = 0 
                ELSE token.q = Sum(counter, Rng(token.pos+1,N-1))
     (* (Si: 0 <= i <= t: c.i) + q > 0. *)
     \/ P2:: Sum(counter, Rng(0, token.pos)) + token.q > 0
     (* Ei: 0 <= i <= t : machine nr.i is black. *)
     \/ P3:: \E i \in Rng(0, token.pos) : color[i] = "black"
     (* The token is black. *)
     \/ P4:: token.color = "black"

(***************************************************************************)
(* The inductive invariant combined with the type invariant                *)
(***************************************************************************)
TypedInv ==
    /\ TypeOK
    /\ Inv

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  Termination ~> terminationDetected

(***************************************************************************)
(* The algorithm implements the specification of termination detection     *)
(* in a ring with asynchronous communication.                              *)
(* The parameters of module AsyncTerminationDetection are instantiated     *)
(* by the symbols of the same name of the present module.                  *)
(***************************************************************************)
TD == INSTANCE AsyncTerminationDetection

TDSpec == TD!Spec

THEOREM Spec => TDSpec

(***************************************************************************)
(* Proofs checked by TLAPS about the EWD998 specification.                 *)
(***************************************************************************)

USE NAssumption

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Init /\ [][Next]_vars => []TypeOK
  PROOF OMITTED

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

THEOREM Invariance == Init /\ [][Next]_vars => []Inv
  PROOF OMITTED

THEOREM Safety ==
  /\ TypeOK /\ Inv /\ terminationDetected => Termination
  /\ TypeOK' /\ Inv' /\ terminationDetected' => Termination'
  PROOF OMITTED

LEMMA B0NoMessagePending == 
  /\ TypeOK /\ B=0 => \A i \in Node : pending[i] = 0
  /\ TypeOK' /\ B'=0 => \A i \in Node : pending'[i] = 0
  PROOF OMITTED

-----------------------------------------------------------------------------
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

COROLLARY EnabledAtMaster ==
  ASSUME TypeOK, Inv, Termination, token.pos = 0, ~ terminationDetected
  PROVE  ENABLED <<System>>_vars
  PROOF OMITTED

BSpec ==
  /\ []TypeOK
  /\ []Inv
  /\ [][Next]_vars
  /\ []~terminationDetected
  /\ WF_vars(System)

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
PROOF OBVIOUS

========================================