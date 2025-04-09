----------------------------- MODULE Echo_Abs -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Nodes,      \* Set of nodes in the network
    Initiator,  \* The initiator node
    Topology,   \* Network topology (adjacency list)
    NULL        \* Null value

ASSUME 
    /\ Initiator \in Nodes
    /\ \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})        \* No self-loops
    /\ \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m] \* Undirected/symmetric 

VARIABLES 
    visited,   \* Set of nodes that have been reached
    done       \* Set of nodes that have completed their part

vars == <<visited, done>>

--------------------------------------------------------------------------------
\* A node becomes visited if it's connected to an already visited node
VisitNode(n) ==
    /\ n \notin visited
    /\ \E v \in visited : n \in Topology[v]
    /\ visited' = visited \cup {n}
    /\ UNCHANGED <<done>>

\* A node is done when it and all its neighbors are visited
MarkDone(n) ==
    /\ n \in visited
    /\ n \notin done
    /\ \A m \in Topology[n] : m \in visited
    /\ done' = done \cup {n}
    /\ UNCHANGED <<visited>>

\* The system terminates when all nodes are done
Terminating ==
    /\ done = Nodes
    /\ UNCHANGED vars

--------------------------------------------------------------------------------
Init ==
    /\ visited = {Initiator}
    /\ done = {}

Next ==
    \/ \E n \in Nodes \ {Initiator} : VisitNode(n)
    \/ \E n \in Nodes : MarkDone(n)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ visited \subseteq Nodes
    /\ done \subseteq Nodes

\* Termination property
Termination == <>[](done = Nodes)

\* Invariant: All done nodes are visited
DoneVisitedInv == done \subseteq visited

\* Invariant: If a node is done, all its neighbors are visited
DoneNeighborsVisitedInv == \A n \in done : \A m \in Topology[n] : m \in visited

=============================================================================
