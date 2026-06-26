------------------ MODULE ivy_examples_alternating_bit_protocol_Liveness ------------------
EXTENDS IvyAlternatingBitProtocol

DataDelivery ==
  \A i \in Nat :
    (sender_array[i] # Bot) ~> (receiver_array[i] # Bot)

THEOREM Liveness == Spec => DataDelivery
PROOF OBVIOUS

=============================================================================
