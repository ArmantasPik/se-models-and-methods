----------------------------- MODULE Echo_Abs -----------------------------
\*  Abstract specification of the Echo algorithm.      */
\*  Constructs a spanning tree in an unidrected graph. */
\*  Hides details of message passing and node state.   */
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Nodes,      
    Initiator,  
    Topology,   
    NULL        

ASSUME 
    /\ Initiator \in Nodes
    /\ \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})   \* No self-loops     
    /\ \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m]  \* Undirected/symmetric 

VARIABLES 
    visited,   
    done       

vars == <<visited, done>>

--------------------------------------------------------------------------------
VisitNode(n) ==
    /\ n \notin visited
    /\ \E v \in visited : n \in Topology[v]
    /\ visited' = visited \cup {n}
    /\ UNCHANGED <<done>>

MarkDone(n) ==
    /\ n \in visited
    /\ n \notin done
    /\ \A m \in Topology[n] : m \in visited
    /\ done' = done \cup {n}
    /\ UNCHANGED <<visited>>

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
TypeOK ==
    /\ visited \subseteq Nodes
    /\ done \subseteq Nodes
    /\ done \subseteq visited \* All done nodes are visited
    /\ \A n \in done : \A m \in Topology[n] : m \in visited \* All neighbors of done nodes are visited

Termination == <>[](done = Nodes)

DoneVisitedInv == done \subseteq visited

DoneNeighborsVisitedInv == \A n \in done : \A m \in Topology[n] : m \in visited

=============================================================================
