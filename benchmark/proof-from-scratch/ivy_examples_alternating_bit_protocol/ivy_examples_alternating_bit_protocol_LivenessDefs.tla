------------------ MODULE ivy_examples_alternating_bit_protocol_LivenessDefs ------------------
EXTENDS ivy_examples_alternating_bit_protocolModel

Spec ==
  /\ SafetySpec
  /\ WF_vars(SenderSendData)
  /\ WF_vars(ReceiverSendAck)
  /\ SF_vars(ReceiverReceiveData)
  /\ SF_vars(SenderReceiveAck)

DataDelivery ==
  \A i \in Nat :
    (sender_array[i] # Bot) ~> (receiver_array[i] # Bot)

=============================================================================
