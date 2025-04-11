----------------------------- MODULE Echo -----------------------------
\*  Echo algorithm model. Constructs a spanning tree in an unidrected graph.  */
\*  Starts from a single initiator that send messages to all neighbors.       */
EXTENDS Naturals, FiniteSets, TLC, TLAPS

CONSTANTS 
    Nodes,
    Initiator,
    Topology,
    NULL

ASSUME 
    /\ Initiator \in Nodes
    /\ \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})        \* No self-loops
    /\ \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m] \* Undirected/symmetric 

VARIABLES 
    msgSent,   \* Regular message (sender, receiver)
    ackSent,   \* Acknowledgment message (sender, receiver)
    visited,
    parent,
    children,
    done

vars == <<msgSent, ackSent, visited, parent, children, done>>

--------------------------------------------------------------------------------
InitiatorSend ==
    /\ Initiator \notin done
    /\ msgSent' = msgSent \cup {<<Initiator, n>> : n \in Topology[Initiator]}
    /\ UNCHANGED <<ackSent, visited, parent, children, done>>

FirstReceive(n) ==
    /\ n \notin visited
    /\ n \notin done
    /\ \E sender \in Nodes : 
        /\ <<sender, n>> \in msgSent
        /\ parent' = [parent EXCEPT ![n] = sender]
        /\ visited' = visited \cup {n}
        /\ msgSent' = msgSent \cup {<<n, m>> : m \in Topology[n] \ {sender}}
    /\ UNCHANGED <<ackSent, children, done>>

SendAck(n) ==
    /\ n \in visited
    /\ n \notin done
    /\ n # Initiator
    /\ \A nbr \in Topology[n] : (nbr = parent[n]) \/ <<nbr, n>> \in msgSent \/ <<nbr, n>> \in ackSent
    /\ ackSent' = ackSent \cup {<<n, parent[n]>>}
    /\ done' = done \cup {n}
    /\ UNCHANGED <<msgSent, visited, parent, children>>

ReceiveAck(n) ==
    /\ n \in visited
    /\ \E child \in Nodes :
        /\ <<child, n>> \in ackSent
        /\ child \notin children[n]
        /\ children' = [children EXCEPT ![n] = @ \cup {child}]
    /\ UNCHANGED <<msgSent, ackSent, visited, parent, done>>

Decide ==
    /\ Initiator \in visited
    /\ Initiator \notin done
    /\ \A nbr \in Topology[Initiator] : 
        \/ <<nbr, Initiator>> \in msgSent 
        \/ <<nbr, Initiator>> \in ackSent /\ nbr \in children[Initiator]
    /\ done' = done \cup {Initiator}
    /\ UNCHANGED <<msgSent, ackSent, visited, parent, children>>

Terminating ==
    /\ done = Nodes
    /\ UNCHANGED vars

--------------------------------------------------------------------------------
Init ==
    /\ msgSent = {}
    /\ ackSent = {}
    /\ visited = {Initiator}
    /\ parent = [n \in Nodes |-> NULL]
    /\ children = [n \in Nodes |-> {}]
    /\ done = {}

Next ==
    \/ InitiatorSend
    \/ \E n \in Nodes \ {Initiator} : FirstReceive(n)
    \/ \E n \in Nodes : SendAck(n)
    \/ \E n \in Nodes : ReceiveAck(n)
    \/ Decide
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------
TypeOK ==
    /\ msgSent \subseteq (Nodes \X Nodes)
    /\ ackSent \subseteq (Nodes \X Nodes)
    /\ visited \subseteq Nodes
    /\ done \subseteq Nodes
    /\ done \subseteq visited
    /\ \A n \in done : \A m \in Topology[n] : m \in visited
    /\ parent \in [Nodes -> (Nodes \cup {NULL})]
    /\ children \in [Nodes -> SUBSET Nodes]
    /\ \A pair \in msgSent : pair[2] \in Topology[pair[1]]
    /\ \A pair \in ackSent : pair[2] \in Topology[pair[1]]

Termination == <>[](done = Nodes)

NoParentInv == parent[Initiator] = NULL

--------------------------------------------------------------------------------
THEOREM TypeOKInvariant == Spec => []TypeOK
    <1> USE DEF vars
    <1>1. Init => TypeOK
        <2>1. msgSent = {} => msgSent \subseteq (Nodes \X Nodes)
            BY DEF Init
        <2>2. ackSent = {} => ackSent \subseteq (Nodes \X Nodes)
            BY DEF Init
        <2>3. visited = {Initiator} => visited \subseteq Nodes
            BY Initiator \in Nodes
        <2>4. done = {} => done \subseteq Nodes
            BY DEF Init
        <2>5. done = {} => done \subseteq {Initiator}
            BY DEF Init
        <2>6. \A n \in done : \A m \in Topology[n] : m \in visited
            BY DEF Init
        <2>7. parent = [n \in Nodes |-> NULL] => parent \in [Nodes -> (Nodes \cup {NULL})]
            BY DEF Init
        <2>8. children = [n \in Nodes |-> {}] => children \in [Nodes -> SUBSET Nodes]
            BY DEF Init
        <2>9. \A pair \in msgSent : pair[2] \in Topology[pair[1]]
            BY DEF Init
        <2>10. \A pair \in ackSent : pair[2] \in Topology[pair[1]]
            BY DEF Init
        <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9, <2>10 DEF TypeOK, Init

    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        <2> SUFFICES ASSUME TypeOK, Next PROVE TypeOK'
            BY DEF TypeOK
        <2>1. CASE InitiatorSend
            <3>1. msgSent' = msgSent \cup {<<Initiator, n>> : n \in Topology[Initiator]}
                BY <2>1 DEF InitiatorSend
            <3>2. ackSent' = ackSent
                BY <2>1 DEF InitiatorSend
            <3>3. visited' = visited
                BY <2>1 DEF InitiatorSend
            <3>4. done' = done
                BY <2>1 DEF InitiatorSend
            <3>5. parent' = parent
                BY <2>1 DEF InitiatorSend
            <3>6. children' = children
                BY <2>1 DEF InitiatorSend
            <3>7. msgSent' \subseteq (Nodes \X Nodes)
                BY <3>1, TypeOK
            <3>8. \A pair \in msgSent' : pair[2] \in Topology[pair[1]]
                BY <3>1, TypeOK
            <3> QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, TypeOK DEF TypeOK
        
        <2>2. CASE \E n \in Nodes \ {Initiator} : FirstReceive(n)
            <3> USE DEF FirstReceive
            <3>1. \E n \in Nodes \ {Initiator} : 
                  /\ n \notin visited
                  /\ n \notin done
                  /\ \E sender \in Nodes : 
                    /\ <<sender, n>> \in msgSent
                    /\ parent' = [parent EXCEPT ![n] = sender]
                    /\ visited' = visited \cup {n}
                    /\ msgSent' = msgSent \cup {<<n, m>> : m \in Topology[n] \ {sender}}
                  /\ UNCHANGED <<ackSent, children, done>>
                BY <2>2
            <3>2. msgSent' \subseteq (Nodes \X Nodes)
                BY <3>1, TypeOK
            <3>3. \A pair \in msgSent' : pair[2] \in Topology[pair[1]]
                BY <3>1, TypeOK
            <3>4. parent' \in [Nodes -> (Nodes \cup {NULL})]
                BY <3>1, TypeOK
            <3>5. visited' \subseteq Nodes
                BY <3>1, TypeOK
            <3> QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, TypeOK DEF TypeOK

        <2>3. CASE \E n \in Nodes : SendAck(n)
            <3> USE DEF SendAck
            <3>1. \E n \in Nodes : 
                  /\ n \in visited
                  /\ n \notin done
                  /\ n # Initiator
                  /\ \A nbr \in Topology[n] : (nbr = parent[n]) \/ <<nbr, n>> \in msgSent \/ <<nbr, n>> \in ackSent
                  /\ ackSent' = ackSent \cup {<<n, parent[n]>>}
                  /\ done' = done \cup {n}
                  /\ UNCHANGED <<msgSent, visited, parent, children>>
                BY <2>3
            <3>2. ackSent' \subseteq (Nodes \X Nodes)
                BY <3>1, TypeOK
            <3>3. \A pair \in ackSent' : pair[2] \in Topology[pair[1]]
                BY <3>1, TypeOK
            <3>4. done' \subseteq visited'
                BY <3>1, TypeOK
            <3>5. \A n \in done' : \A m \in Topology[n] : m \in visited'
                BY <3>1, TypeOK
            <3> QED
                BY <3>1, <3>2, <3>3, <3>4, <3>5, TypeOK DEF TypeOK

        <2>4. CASE \E n \in Nodes : ReceiveAck(n)
            <3> USE DEF ReceiveAck
            <3>1. \E n \in Nodes : 
                  /\ n \in visited
                  /\ \E child \in Nodes :
                    /\ <<child, n>> \in ackSent
                    /\ child \notin children[n]
                    /\ children' = [children EXCEPT ![n] = @ \cup {child}]
                  /\ UNCHANGED <<msgSent, ackSent, visited, parent, done>>
                BY <2>4
            <3>2. children' \in [Nodes -> SUBSET Nodes]
                BY <3>1, TypeOK
            <3> QED
                BY <3>1, <3>2, TypeOK DEF TypeOK

        <2>5. CASE Decide
            <3> USE DEF Decide
            <3>1. /\ Initiator \in visited
                  /\ Initiator \notin done
                  /\ \A nbr \in Topology[Initiator] : 
                    \/ <<nbr, Initiator>> \in msgSent 
                    \/ <<nbr, Initiator>> \in ackSent /\ nbr \in children[Initiator]
                  /\ done' = done \cup {Initiator}
                  /\ UNCHANGED <<msgSent, ackSent, visited, parent, children>>
                BY <2>5
            <3>2. done' \subseteq visited'
                BY <3>1, TypeOK
            <3>3. \A n \in done' : \A m \in Topology[n] : m \in visited'
                BY <3>1, TypeOK
            <3> QED
                BY <3>1, <3>2, <3>3, TypeOK DEF TypeOK

        <2>6. CASE Terminating
            <3> USE DEF Terminating
            <3>1. /\ done = Nodes
                  /\ UNCHANGED vars
                BY <2>6
            <3> QED
                BY <3>1, TypeOK DEF TypeOK, vars

        <2> QED
            BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next

    <1> QED
        BY <1>1, <1>2 DEF Spec

=============================================================================