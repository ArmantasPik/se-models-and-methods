--------------------------- MODULE EchoAlgorithm ---------------------------
EXTENDS Naturals, TLC

(* --CONFIG
CONSTANT N = 5 (* Number of nodes in the network *)
*)

(* System state definition *)
VARIABLES nodes, messages, echoes, decided

(* Define initial conditions *)
Init == 
    /\ nodes = {0, 1, 2, 3, 4} (* Example network of 5 nodes *)
    /\ messages = {[i \in nodes |-> {}]} (* No messages sent initially *)
    /\ echoes = {[i \in nodes |-> {}]} (* No echoes sent initially *)
    /\ decided = {} (* No node has decided yet *)

(* Transition: A node receives a message and forwards it to neighbors *)
SendMessage(n) ==
    /\ n \in nodes
    /\ \E sender \in nodes : sender \in messages[n]  (* Message received *)
    /\ messages' = [messages EXCEPT ![n] = messages[n] \union {m \in nodes : m # sender}]  
    /\ UNCHANGED <<echoes, decided>>

(* Transition: A node receives messages from all neighbors and sends an echo *)
SendEcho(n) ==
    /\ n \in nodes
    /\ messages[n] = {m \in nodes : m # n} (* Received from all neighbors *)
    /\ echoes' = [echoes EXCEPT ![n] = echoes[n] \union {Parent(n)}]  (* Send echo to parent *)
    /\ UNCHANGED <<messages, decided>>

(* Transition: The initiator node decides when all echoes received *)
Decide(p) ==
    /\ p \in nodes
    /\ \A n \in nodes : n # p => p \in echoes[n] (* p has received all echoes *)
    /\ decided' = decided \union {p} 
    /\ UNCHANGED <<messages, echoes>>

(* Define the next state relation *)
Next == \E n \in nodes : SendMessage(n) \/ SendEcho(n) \/ Decide(0) (* Initiator is node 0 *)

(* Safety property: No node decides before it should *)
SafeDecide == [] (\A p \in nodes : p \in decided => \A n \in nodes : n # p => p \in echoes[n])

(* Liveness property: The algorithm always terminates *)
Termination == <> (\A p \in nodes : p \in decided)

(* Type Invariant *)
TypeOK == 
    /\ nodes \subseteq 0..N-1  (* Nodes are within the valid range *)
    /\ messages \in [nodes -> SUBSET nodes]  (* Each node's messages are sets of nodes *)
    /\ echoes \in [nodes -> SUBSET nodes]  (* Each node's echoes are sets of nodes *)
    /\ decided \subseteq nodes  (* Decided nodes are a subset of all nodes *)

(* Specification *)
Spec == Init /\ [][Next]_<<nodes, messages, echoes, decided>>

=============================================================================