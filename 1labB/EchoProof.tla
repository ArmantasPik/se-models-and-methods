--------------------------- MODULE EchoProof ---------------------------
EXTENDS Echo, TLAPS

ASSUME ParentOK ==
   \A n \in Nodes \ {Initiator} : parent[n] \in Nodes

THEOREM TypeOKInvariant == Spec => []TypeOK
    <1> USE DEF vars, TypeOK, Init, Next, Spec
    <1> USE InitiatorInNodes, NoSelfLoops, ParentOK
    <1>1. Init => TypeOK
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
            BY DEF Next, TypeOK
            <2>1. CASE InitiatorSend
                BY <2>1, TypeOK, InitiatorInNodes, NoSelfLoops
                DEF InitiatorSend, TypeOK
            <2>2. CASE \E n \in Nodes \ {Initiator} : FirstReceive(n)
                BY <2>2, TypeOK, NoSelfLoops DEF FirstReceive, TypeOK
            <2>3. CASE \E n \in Nodes : SendAck(n)
                BY <2>3, TypeOK, ParentOK DEF SendAck, TypeOK
            <2>4. CASE \E n \in Nodes : ReceiveAck(n)
                BY <2>4, TypeOK DEF ReceiveAck, TypeOK
            <2>5. CASE Decide
                BY <2>5, TypeOK DEF Decide, TypeOK
            <2>6. CASE Terminating
                BY <2>6, TypeOK DEF Terminating, vars
            <2> QED
    <1> QED BY <1>1, <1>2 DEF Spec

=============================================================================


