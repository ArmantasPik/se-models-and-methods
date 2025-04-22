--------------------------- MODULE Echo_Proof ---------------------------
EXTENDS Echo, TLAPS

THEOREM ParentOK == 
    \A n \in Nodes \ {Initiator} : parent[n] \in Nodes
PROOF OMITTED 

\* To prove theorems like Spec => []Invariant, you have to:
\*  1. Prove Invariant holds in the initial state (usually trivial)
\*  2. Prove Invariant holds when variables are unchanged (usually trivial)
\*  3. Prove that assuming Invariant is true, a Next step implies Invariant'
THEOREM TypeOKInvariant == Spec => []TypeOK
PROOF
    <1> USE DEF vars, TypeOK, Init, Next, Spec
    <1> USE InitiatorInNodes, NoSelfLoops, ParentOK
    <1>1. Init => TypeOK
        BY DEFS Init, TypeOK
    <1>2. TypeOK /\ UNCHANGED vars => TypeOK'
        BY DEFS TypeOK, vars
    <1>3. TypeOK /\ [Next]_vars => TypeOK'
        <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
            BY DEFS Next, TypeOK
            <2>1. CASE InitiatorSend
                BY <2>1, TypeOK, InitiatorInNodes, NoSelfLoops DEF InitiatorSend, TypeOK
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
            <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
    <1> QED BY PTL, <1>1, <1>2, <1>3 DEF Spec

=============================================================================


