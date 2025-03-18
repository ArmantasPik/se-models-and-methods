-------------------------------- MODULE Echo --------------------------------
(***************************************************************************)
(* The Echo algorithm constructs a spanning tree in an undirected graph    *)
(* starting from a single initiator node. This specification is a pure     *)
(* TLA+ version that is more abstract than the original PlusCal algorithm. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Relation, TLC

CONSTANTS 
    Node,      \* Set of nodes in the graph
    initiator, \* Single initiator node that will be the root of the tree
    R          \* Neighborhood relation represented as a Boolean function over nodes 

(***************************************************************************)
(* Basic assumptions about the graph structure                             *)
(***************************************************************************)
ASSUME 
    /\ initiator \in Node             \* The initiator must be a node in the graph
    /\ R \in [Node \X Node -> BOOLEAN] \* R defines edges between nodes
    /\ IsIrreflexive(R, Node)         \* No self-loops (no edge from a node to itself)
    /\ IsSymmetric(R, Node)           \* Undirected graph (if a connects to b, b connects to a)
    /\ IsConnected(R, Node)           \* The graph is connected (there's a path between any two nodes)

(***************************************************************************)
(* Helper definitions                                                      *)
(***************************************************************************)
NoNode == CHOOSE x : x \notin Node    \* A value that represents "no node"
neighbors(n) == { m \in Node : R[m,n] } \* Set of neighbors for node n

(***************************************************************************)
(* Message types:                                                          *)
(* - "m": "Mark" message used to initially explore the graph               *)
(* - "c": "Child" message sent from a node to its parent                   *)
(***************************************************************************)
MessageType == {"m", "c"}

(***************************************************************************)
(* Variables for the state of the system                                   *)
(***************************************************************************)
VARIABLES 
    inbox,    \* Messages waiting to be processed at each node
    parent,   \* Parent node in the spanning tree (NoNode if none assigned yet)
    children, \* Set of children nodes in the spanning tree
    rcvd,     \* Number of messages received by each node
    status    \* Status of each node: "init", "active", or "done"

vars == << inbox, parent, children, rcvd, status >>

(***************************************************************************)
(* Helper operators for message handling                                   *)
(***************************************************************************)
\* Add a message from node p to node q of type knd
send(net, p, q, knd) == 
    [net EXCEPT ![q] = @ \cup {[kind |-> knd, sndr |-> p]}]

\* Remove a message from node p's inbox
receive(net, p, msg) == 
    [net EXCEPT ![p] = @ \ {msg}]

\* Send a message of type knd from node p to all nodes in dest
multicast(net, p, dest, knd) ==
    [m \in Node |-> IF m \in dest 
                    THEN net[m] \cup {[kind |-> knd, sndr |-> p]}
                    ELSE net[m]]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init == 
    /\ inbox = [n \in Node |-> {}]              \* Empty inboxes
    /\ parent = [n \in Node |-> NoNode]         \* No parent assigned yet
    /\ children = [n \in Node |-> {}]           \* No children assigned yet
    /\ rcvd = [n \in Node |-> 0]                \* No messages received yet
    /\ status = [n \in Node |-> IF n = initiator THEN "active" ELSE "init"] 
       \* Initiator starts as active, others as initial

(***************************************************************************)
(* Actions (state transitions)                                             *)
(***************************************************************************)

\* Action: Initiator sending the first "mark" messages to all its neighbors
InitiatorSend ==
    /\ \E n \in Node : 
        /\ n = initiator
        /\ status[n] = "active"
        /\ inbox' = multicast(inbox, n, neighbors(n), "m")
        /\ status' = [status EXCEPT ![n] = "done"]
    /\ UNCHANGED << parent, children, rcvd >>

\* Action: Non-initiator receiving its first message
FirstReceive ==
    /\ \E n \in Node, msg \in inbox[n] :
        /\ n # initiator
        /\ status[n] = "init"  \* Only happens in initial state
        /\ rcvd[n] = 0         \* No messages received yet
        /\ msg.kind = "m"      \* First message must be a mark message
        /\ parent' = [parent EXCEPT ![n] = msg.sndr]  \* Set parent to message sender
        /\ rcvd' = [rcvd EXCEPT ![n] = 1]            \* Increment received count
        /\ inbox' = multicast(receive(inbox, n, msg), n, neighbors(n) \ {msg.sndr}, "m")
        /\ status' = [status EXCEPT ![n] = "active"]  \* Node becomes active
    /\ UNCHANGED children

\* Action: Node receiving a subsequent message
SubsequentReceive ==
    /\ \E n \in Node, msg \in inbox[n] :
        /\ status[n] = "active"
        /\ rcvd[n] > 0  \* At least one message has been received before
        /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
        /\ inbox' = receive(inbox, n, msg)
        /\ IF msg.kind = "c"  \* If it's a child notification
           THEN children' = [children EXCEPT ![n] = @ \cup {msg.sndr}]
           ELSE UNCHANGED children
        /\ IF rcvd'[n] = Cardinality(neighbors(n))  \* If all neighbors have responded
           THEN status' = [status EXCEPT ![n] = "done"]
           ELSE UNCHANGED status
    /\ UNCHANGED parent

\* Action: Node sending a child notification to its parent
SendChildNotification ==
    /\ \E n \in Node :
        /\ n # initiator
        /\ status[n] = "done"
        /\ parent[n] # NoNode
        /\ \A m \in neighbors(n) : 
           \/ m = parent[n]      \* Either it's the parent
           \/ rcvd[n] >= 1       \* Or we've received at least one message (implying we've sent to all non-parent neighbors)
        /\ inbox' = send(inbox, n, parent[n], "c")
        /\ status' = [status EXCEPT ![n] = "terminated"]
    /\ UNCHANGED << parent, children, rcvd >>

(***************************************************************************)
(* Next state relation                                                     *)
(***************************************************************************)
Next ==
    \/ InitiatorSend
    \/ FirstReceive
    \/ SubsequentReceive
    \/ SendChildNotification
    \/ UNCHANGED vars  \* Allow stuttering

(***************************************************************************)
(* Complete temporal formula                                               *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants and Properties                                               *)
(***************************************************************************)

\* Type invariant
TypeOK ==
    /\ parent \in [Node -> (Node \cup {NoNode})]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))
    /\ inbox \in [Node -> SUBSET [kind : MessageType, sndr : Node]]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
    /\ status \in [Node -> {"init", "active", "done", "terminated"}]

\* The initiator never has a parent
InitiatorNoParent == parent[initiator] = NoNode

\* If a node has a parent, it is a neighbor node
ParentIsNeighbor == \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

\* Parent-child relationship is consistent
ParentChildConsistency == \A m, n \in Node :
    /\ n \in children[m] => m = parent[n]
    /\ status[m] = "terminated" /\ m = parent[n] => n \in children[m]

\* Compute the ancestor relation for checking tree properties
IsParent == [m, n \in Node |-> n = parent[m]]
IsAncestor == TransitiveClosure(IsParent, Node)

\* Spanning tree properties
\* When the algorithm terminates, we have a proper spanning tree
SpanningTreeProperties ==
    (\A n \in Node : status[n] = "terminated") =>
    LET anc == IsAncestor
    IN  /\ \A n \in Node \ {initiator} : anc[n, initiator]  \* Initiator is ancestor of all nodes
        /\ IsIrreflexive(anc, Node)  \* No cycles in the ancestor relation

\* Termination property: eventually all nodes will be in the "terminated" state
Termination == <>(\A n \in Node : status[n] = "terminated")

=============================================================================