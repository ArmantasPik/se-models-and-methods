----------------------------- MODULE Echo -----------------------------
(***************************************************************************)
(* This is an abstract specification of the Echo algorithm for constructing *)
(* a spanning tree in an undirected graph from a single initiator.         *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, Relation, TLC

(***************** CONSTANTS AND VARIABLES *****************)

CONSTANTS 
  Nodes,      \* Set of all nodes in the network
  Initiator,  \* The node that initiates the algorithm
  Topology,    \* The network topology as a function: Nodes -> SUBSET Nodes
  NULL
\* Assumptions about the network
ASSUME 
  /\ Initiator \in Nodes
  /\ \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})     \* No self-loops
  /\ \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m] \* Symmetric (undirected)


\* Special value to represent "no parent"
\* NULL == CHOOSE x : x \notin Nodes

\* State variables
VARIABLES 
  (* Abstract message state *)
  msgSent,   \* Set of (sender, receiver) pairs where a message has been sent
  ackSent,   \* Set of (sender, receiver) pairs where an acknowledgment has been sent
  
  (* Node states *)
  visited,   \* Set of nodes that have received at least one message
  parent,    \* Parent node in the spanning tree
  children,  \* Children of each node in the spanning tree
  done       \* Set of nodes that have completed the algorithm

vars == <<msgSent, ackSent, visited, parent, children, done>>

(***************** TYPE INVARIANT *****************)

TypeOK ==
  /\ msgSent \subseteq (Nodes \X Nodes)
  /\ ackSent \subseteq (Nodes \X Nodes)
  /\ visited \subseteq Nodes
  /\ parent \in [Nodes -> (Nodes \cup {NULL})]
  /\ children \in [Nodes -> SUBSET Nodes]
  /\ done \subseteq Nodes
  /\ \A pair \in msgSent : pair[2] \in Topology[pair[1]]
  /\ \A pair \in ackSent : pair[2] \in Topology[pair[1]]

(***************** INITIAL STATE *****************)

Init ==
  /\ msgSent = {}
  /\ ackSent = {}
  /\ visited = {Initiator}
  /\ parent = [n \in Nodes |-> NULL]
  /\ children = [n \in Nodes |-> {}]
  /\ done = {}

(***************** ACTIONS *****************)

\* Initiator starts the algorithm by sending messages to all neighbors
InitiatorSend ==
  /\ Initiator \notin done
  /\ msgSent' = msgSent \cup {<<Initiator, n>> : n \in Topology[Initiator]}
  /\ done' = done \cup {Initiator}
  /\ UNCHANGED <<ackSent, visited, parent, children>>

\* A node receives its first message and forwards to other neighbors
FirstReceive(n) ==
  /\ n \notin visited
  /\ n \notin done
  /\ \E sender \in Nodes : 
      /\ <<sender, n>> \in msgSent
      /\ parent' = [parent EXCEPT ![n] = sender]
      /\ visited' = visited \cup {n}
      /\ msgSent' = msgSent \cup {<<n, m>> : m \in Topology[n] \ {sender}}
  /\ UNCHANGED <<ackSent, children, done>>

\* A node has received messages from all neighbors and sends acknowledgment to parent
SendAck(n) ==
  /\ n \in visited
  /\ n \notin done
  /\ n # Initiator
  /\ \A nbr \in Topology[n] : (nbr = parent[n]) \/ <<nbr, n>> \in msgSent
  /\ ackSent' = ackSent \cup {<<n, parent[n]>>}
  /\ done' = done \cup {n}
  /\ UNCHANGED <<msgSent, visited, parent, children>>

\* A node receives acknowledgment from a child and updates its children set
ReceiveAck(n) ==
  /\ n \in visited
  /\ \E child \in Nodes :
      /\ <<child, n>> \in ackSent
      /\ child \notin children[n]
      /\ children' = [children EXCEPT ![n] = @ \cup {child}]
  /\ UNCHANGED <<msgSent, ackSent, visited, parent, done>>

\* Combined next-state relation
Next ==
  \/ InitiatorSend
  \/ \E n \in Nodes \ {Initiator} : FirstReceive(n)
  \/ \E n \in Nodes \ {Initiator} : SendAck(n)
  \/ \E n \in Nodes : ReceiveAck(n)

\* Complete specification
Spec == Init /\ [][Next]_vars

(***************** PROPERTIES *****************)

\* Algorithm eventually terminates
Termination == <>(done = Nodes)

\* The initiator never has a parent
InitiatorNoParent == parent[Initiator] = NULL

\* If a node has a parent, it is a neighbor node
ParentIsNeighbor == \A n \in Nodes : parent[n] \in Topology[n] \cup {NULL}

\* A node n is a child of node m only if m is the parent of n
ParentChildRelation == \A m, n \in Nodes :
  /\ n \in children[m] => m = parent[n]
  /\ m = parent[n] /\ m \in done => n \in children[m]

\* Helper to compute the ancestor relation
IsParent == [m, n \in Nodes |-> n = parent[m]]
\* IsAncestor == TC(IsParent)  \* TC is the transitive closure

\* \* At the end, the initiator is an ancestor of every other node
\* \* and the ancestor relation is acyclic
\* SpanningTreeProperties ==
\*   (done = Nodes) =>
\*     LET anc == IsAncestor IN
\*       /\ \A n \in Nodes \ {Initiator} : anc[n, Initiator]
\*       /\ \A n \in Nodes : ~anc[n, n]  \* No self-loops (acyclic)

=============================================================================