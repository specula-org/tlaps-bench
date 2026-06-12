------------------ MODULE ivy_examples_alternating_bit_protocol_Safety ------------------
EXTENDS IvyAlternatingBitProtocol

ReceiverValuesFromSender ==
  \A i \in Nat :
    receiver_array[i] # Bot => receiver_array[i] = sender_array[i]

THEOREM Safety == SafetySpec => []ReceiverValuesFromSender
PROOF OBVIOUS

=============================================================================
