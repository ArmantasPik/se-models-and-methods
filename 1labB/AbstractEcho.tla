----------------------------- MODULE AbstractEcho -----------------------------
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
    avisited,  \* Set of nodes that have been reached
    adone      \* Set of nodes that have completed their part

avars == <<avisited, adone>>

--------------------------------------------------------------------------------
\* A node becomes visited if it's connected to an already visited node
AVisitNode(n) ==
    /\ n \notin avisited
    /\ \E v \in avisited : n \in Topology[v]
    /\ avisited' = avisited \cup {n}
    /\ UNCHANGED <<adone>>

\* A node is done when it and all its neighbors are visited
AMarkDone(n) ==
    /\ n \in avisited
    /\ n \notin adone
    /\ \A m \in Topology[n] : m \in avisited
    /\ adone' = adone \cup {n}
    /\ UNCHANGED <<avisited>>

\* The system terminates when all nodes are done
ATerminating ==
    /\ adone = Nodes
    /\ UNCHANGED avars

--------------------------------------------------------------------------------
AInit ==
    /\ avisited = {Initiator}
    /\ adone = {}

ANext ==
    \/ \E n \in Nodes \ {Initiator} : AVisitNode(n)
    \/ \E n \in Nodes : AMarkDone(n)
    \/ ATerminating

ASpec == AInit /\ [][ANext]_avars /\ WF_avars(ANext)

--------------------------------------------------------------------------------
\* Type invariant
ATypeOK ==
    /\ avisited \subseteq Nodes
    /\ adone \subseteq Nodes

\* Termination property
ATermination == <>[](adone = Nodes)

\* Invariant: All done nodes are visited
ADoneVisitedInv == adone \subseteq avisited

\* Invariant: If a node is done, all its neighbors are visited
ADoneNeighborsVisitedInv == \A n \in adone : \A m \in Topology[n] : m \in avisited

============================================================================= 