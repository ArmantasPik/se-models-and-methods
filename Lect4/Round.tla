---- MODULE Round ----
EXTENDS Naturals
CONSTANT Nodes
CONSTANT Rounds
VARIABLE round
VARIABLE done
VARIABLE msgs
ASSUME RoundAssm == \E R \in Nat : Rounds = 0..R

vars == <<round, done, msgs>>

Msgs == [n : Nodes, r: Rounds]

TypeOK ==
    /\ round \in [Nodes -> Rounds]
    /\ done \in [Nodes -> [Rounds -> BOOLEAN]]
    /\ msgs \in SUBSET Msgs

---------

RoundDoneSend(n) ==
    LET r == round[n]
    IN
        /\ ~done[n][r]
        /\ done' = [done EXCEPT ![n][r] = TRUE]
        /\ msgs' = msgs \cup {[n |-> n, r |-> r]}
        /\ UNCHANGED round

RoundDoneRecv(n) ==
    /\ round[n] + 1 \in Rounds \* For TLC only.
    /\ [n : Nodes, r: {round[n]}] \subseteq msgs
    /\ round' = [round EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<done, msgs>>

---------

Init ==
    /\ round = [ n \in Nodes |-> 0 ]
    /\ done = [ n \in Nodes |-> [r \in Rounds |-> FALSE] ]
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

------------------------------------------
THEOREM Spec => []TypeOK
PROOF OMITTED \* Checked by TLC.


LEMMA Init_TypeOK ==
    Init => TypeOK
PROOF
    BY RoundAssm DEF TypeOK, Init, Msgs

    \* <1>1. ASSUME Init PROVE TypeOK
    \*     <2>q. QED BY <1>1, RoundAssm DEF TypeOK, Init, Msgs
    \* <1>q. QED BY <1>1

    \* <1> HAVE Init
    \* <1>q. QED BY RoundAssm DEF TypeOK, Init, Msgs

====

