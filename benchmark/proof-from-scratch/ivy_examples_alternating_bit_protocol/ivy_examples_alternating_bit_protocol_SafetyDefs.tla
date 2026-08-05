------------------ MODULE ivy_examples_alternating_bit_protocol_SafetyDefs ------------------
EXTENDS ivy_examples_alternating_bit_protocolModel

ReceiverValuesFromSender ==
  \A i \in Nat :
    receiver_array[i] # Bot => receiver_array[i] = sender_array[i]

=============================================================================
