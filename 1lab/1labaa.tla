----------------------------- MODULE 1labaa -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,      \* Set of all nodes in the network
          Initiator,  \* The node that initiates the algorithm
          Topology,   \* The network topology as a function: Nodes -> SUBSET Nodes
          NULL        \* Special value to represent "no parent"

ASSUME Initiator \in Nodes
ASSUME \A n \in Nodes : Topology[n] \subseteq (Nodes \ {n})
ASSUME \A n, m \in Nodes : m \in Topology[n] <=> n \in Topology[m] \* Bidirectional links

\* ConstTopology == [
\*         n1 |-> {n2, n3},
\*         n2 |-> {n1, n4},
\*         n3 |-> {n1, n4, n5},
\*         n4 |-> {n2, n3, n5},
\*         n5 |-> {n3, n4}
\*     ]

VARIABLES 
  visited,    \* Set of nodes that have received a message
  parent,     \* Function mapping each node to its parent in the spanning tree
  pendingMsg, \* Set of messages currently in transit (source, destination)
  pendingEcho,\* Function mapping each node to the set of neighbors it's waiting for echoes from
  terminated  \* Boolean indicating whether the algorithm has terminated

vars == <<visited, parent, pendingMsg, pendingEcho, terminated>>

TypeOK ==
  /\ visited \subseteq Nodes
  /\ parent \in [Nodes -> Nodes \cup {NULL}]
  /\ pendingMsg \subseteq (Nodes \X Nodes)
  /\ pendingEcho \in [Nodes -> SUBSET Nodes]
  /\ terminated \in BOOLEAN

Init ==
  /\ visited = {Initiator}
  /\ parent = [n \in Nodes |-> IF n = Initiator THEN NULL ELSE NULL]
  /\ pendingMsg = {<<Initiator, n>> : n \in Topology[Initiator]}
  /\ pendingEcho = [n \in Nodes |-> IF n = Initiator THEN Topology[Initiator] ELSE {}]
  /\ terminated = FALSE

\* A node receives a message and forwards it to all neighbors (if not visited before)
ReceiveMessage(sender, receiver) ==
  /\ <<sender, receiver>> \in pendingMsg
  /\ IF receiver \notin visited THEN
       /\ visited' = visited \cup {receiver}
       /\ parent' = [parent EXCEPT ![receiver] = sender]
       /\ pendingMsg' = (pendingMsg \ {<<sender, receiver>>}) \cup 
                        {<<receiver, n>> : n \in Topology[receiver] \ {sender}}
       /\ pendingEcho' = [pendingEcho EXCEPT ![receiver] = Topology[receiver] \ {sender}]
       /\ UNCHANGED terminated
     ELSE
       \* Already visited, just send echo back
       /\ pendingMsg' = (pendingMsg \ {<<sender, receiver>>}) \cup {<<receiver, sender>>}
       /\ UNCHANGED <<visited, parent, pendingEcho, terminated>>

\* A node receives an echo from one of its neighbors
ReceiveEcho(sender, receiver) ==
  /\ <<sender, receiver>> \in pendingMsg
  /\ sender \in pendingEcho[receiver]
  /\ pendingEcho' = [pendingEcho EXCEPT ![receiver] = @ \ {sender}]
  /\ pendingMsg' = pendingMsg \ {<<sender, receiver>>}
  /\ IF receiver = Initiator /\ pendingEcho'[receiver] = {} THEN
       /\ terminated' = TRUE
       /\ UNCHANGED <<visited, parent>>
     ELSE IF pendingEcho'[receiver] = {} THEN
       \* All echoes received, send echo to parent
       /\ pendingMsg' = pendingMsg' \cup {<<receiver, parent[receiver]>>}
       /\ UNCHANGED <<visited, parent, terminated>>
     ELSE
       /\ UNCHANGED <<visited, parent, terminated>>

\* Next state relation
Next ==
  \/ \E s, r \in Nodes :
       /\ s \in visited
       /\ <<s, r>> \in pendingMsg
       /\ IF r \in pendingEcho[s] THEN ReceiveEcho(r, s) ELSE ReceiveMessage(s, r)
  \/ UNCHANGED vars

\* Specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Properties to check

\* Eventually the algorithm terminates
Termination == <>terminated

\* All nodes are eventually visited
AllNodesVisited == <>(visited = Nodes)

\* The parent pointers form a valid spanning tree rooted at the initiator
ValidSpanningTree ==
  <>(
    /\ parent[Initiator] = NULL
    /\ \A n \in Nodes \ {Initiator} : parent[n] \in Nodes
    /\ \A n \in Nodes \ {Initiator} : n \in visited => parent[n] \in visited
  )

\* No messages remain in transit after termination
NoOrphanedMessages ==
  [](terminated => pendingMsg = {})

\* Safety: The algorithm doesn't terminate until all nodes are visited
SafeTermination ==
  [](terminated => visited = Nodes)

=============================================================================