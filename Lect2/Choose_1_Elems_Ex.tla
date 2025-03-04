---- MODULE Choose_1_Elems_Ex ----
EXTENDS Naturals, Sequences
VARIABLE x
VARIABLE e

Init == x = 0 /\ e = <<>>
Next == \E d \in Nat : d > 0 /\ x' = x + d /\ e' = Append(e, d)
Spec == Init /\ [][Next]_x /\ WF_x(Next)
TypeOK == x \in Nat

\* THEOREM Init /\ [][Next]_x /\ WF_x(Next) => []TypeOK
\*     ASSUME Init, [][Next]_x, WF_x(Next) PROVE []TypeOK
\*        WF_x(Next) -- TRUE
\*        []([]ENABLED <<Next>>_x => <><<Next>>_x) -- TRUE

====
