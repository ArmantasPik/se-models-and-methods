---- MODULE RoundAcc ----
EXTENDS Naturals, FiniteSets
CONSTANT Nodes
CONSTANT Rounds
VARIABLE round
VARIABLE done
VARIABLE recv
VARIABLE msgs
vars == <<round, done, recv, msgs>>

N == Cardinality(Nodes)
Msgs == [n : Nodes, r: Rounds]

TypeOK ==
    /\ round \in [Nodes -> Rounds]
    /\ done \in [Nodes -> [Rounds -> BOOLEAN]]
    /\ recv \in [Nodes -> [Rounds -> SUBSET Nodes]]
    /\ msgs \in SUBSET Msgs

---------

RoundDoneSend(n) ==
    LET r == round[n]
    IN
        /\ ~done[n][r]
        /\ done' = [done EXCEPT ![n][r] = TRUE]
        /\ msgs' = msgs \cup {[n |-> n, r |-> r]}
        /\ UNCHANGED <<round, recv>>

RoundDoneRecv(n) ==
    /\ round[n] + 1 \in Rounds \* For TLC only.
    \* /\ [n : Nodes, r: {round[n]}] \subseteq msgs
    \* /\ round' = [round EXCEPT ![n] = @ + 1]
    \* /\ UNCHANGED <<done, msgs>>
    /\ \E m \in msgs:
        /\ round[n] = m.r
        /\ recv' = [recv EXCEPT ![n][round[n]] = @ \cup {m.n}]
        /\ \/ /\ Cardinality(recv[n][round[n]]) = N
              /\ round' = [round EXCEPT ![n] = @ + 1]
              /\ UNCHANGED <<done, msgs>>
           \/ /\ Cardinality(recv[n][round[n]]) < N
              /\ UNCHANGED <<done, round, msgs>>

---------

Init ==
    /\ round = [ n \in Nodes |-> 0 ]
    /\ done = [ n \in Nodes |-> [r \in Rounds |-> FALSE] ]
    /\ recv = [ n \in Nodes |-> [r \in Rounds |-> {} ] ]
    /\ msgs = {}

Next ==
    \E n \in Nodes:
        \/ RoundDoneSend(n)
        \/ RoundDoneRecv(n)

Fair ==
    WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fair

---------

RoundActive(n, r) ==
    /\ round[n] = r
    /\ ~done[n][r]

RoundsIsolated ==
    \A n1, n2 \in Nodes:
        \A r1, r2 \in Rounds:
            RoundActive(n1, r1) /\ RoundActive(n2, r2)
                => r1 = r2

EachRoundIsReached ==
    \A n \in Nodes, r \in Rounds :
        <>(round[n] = r)

====

