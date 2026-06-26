----------------------------- MODULE Stuttering ----------------------------

EXTENDS Naturals, TLC
top == [top |-> "top"] 

VARIABLES s, vars

NoStutter(A) == (s = top) /\ A /\ (s' = s)

PostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ s.ctxt = context 
                  /\ UNCHANGED vars 
                  /\ s'= IF s.val = bot THEN top 
                                        ELSE [s EXCEPT !.val = decr(s.val)]

PreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ UNCHANGED vars 
         /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal] 
    ELSE /\ s.id = actionId
         /\ s.ctxt = context 
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)]

MayPostStutter(A, actionId, context, bot, initVal, decr(_)) ==
  IF s = top THEN /\ A 
                  /\ s' = IF initVal = bot
                            THEN s
                            ELSE [id |-> actionId, ctxt |-> context, 
                                  val |-> initVal]
             ELSE /\ s.id = actionId
                  /\ s.ctxt = context 
                  /\ UNCHANGED vars 
                  /\ s'= IF decr(s.val) = bot 
                           THEN top 
                           ELSE [s EXCEPT !.val = decr(s.val)]

MayPreStutter(A, enabled, actionId, context, bot, initVal, decr(_)) == 
  IF s = top 
    THEN /\ enabled
         /\ IF initVal = bot
              THEN A /\ (s' = s)
              ELSE /\ s' = [id |-> actionId, ctxt |-> context, val |-> initVal]
                   /\ UNCHANGED vars         
    ELSE /\ s.id = actionId
         /\ s.ctxt = context 
         /\ IF s.val = bot THEN /\ s.ctxt = context
                                /\ A 
                                /\ s' = top
                           ELSE /\ UNCHANGED vars  
                                /\ s' = [s EXCEPT !.val = decr(s.val)] 
-----------------------------------------------------------------------------

StutterConstantCondition(Sigma, bot, decr(_)) ==
  LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
      R[n \in Nat] == IF n = 0 THEN {bot}
                               ELSE LET T == R[n-1] 
                                    IN  T \cup InverseDecr(T)
                        
  IN Sigma = UNION {R[n] : n \in Nat}

AltStutterConstantCondition(Sigma, bot, decr(_)) ==
   LET InverseDecr(S) == {sig \in Sigma \ S : decr(sig) \in S}
       ReachBot[S \in SUBSET Sigma] ==
          IF InverseDecr(S) = {} THEN S 
                                 ELSE ReachBot[S \cup InverseDecr(S)]
   IN  ReachBot[{bot}] = Sigma
=============================================================================

