----------------------------- MODULE Echo -----------------------------
\*  Echo algorithm model. Constructs a spanning tree in an unidrected graph.  */
\*  Starts from a single initiator that send messages to all neighbors.       */
EXTENDS Naturals, FiniteSets, Connectivity, TLC

CONSTANTS 
    Nodes,
    Initiator,
    Topology,
    NULL

ASSUME 
    /\ Initiator \in Nodes
    /\ \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})        \* No self-loops
    /\ \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m] \* Undirected/symmetric 
    /\ IsConnected(Nodes, Topology, Initiator)                     \* Connected 

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

=============================================================================