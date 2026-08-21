
---- MODULE btree_TypeOkCorrectDefs ----
EXTENDS btreeModel

TypeOk == /\ root \in Nodes
          /\ isLeaf \in [Nodes -> BOOLEAN]
          /\ keysOf \in [Nodes -> SUBSET Keys]
          /\ childOf \in [Nodes \X Keys -> Nodes \union {NIL}]
          /\ lastOf \in [Nodes -> Nodes \union {NIL}]
          /\ valOf \in [Nodes \X Keys -> Vals \union {NIL}]
          /\ focus \in Nodes \union {NIL}
          /\ toSplit \in Seq(Nodes)
          /\ op \in {"get", "insert", "update", NIL}
          /\ ret \in Vals \union {"ok", "error", MISSING, NIL}
          /\ state \in {READY, GET_VALUE, FIND_LEAF_TO_ADD, WHICH_TO_SPLIT, ADD_TO_LEAF, SPLIT_LEAF, SPLIT_INNER, SPLIT_ROOT_LEAF, SPLIT_ROOT_INNER, UPDATE_LEAF}

====
