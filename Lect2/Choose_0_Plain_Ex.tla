---- MODULE Choose_0_Plain_Ex ----
EXTENDS Naturals
VARIABLE x

Init == x \in Nat
Next == \E d \in Nat : d > 0 /\ x' = x + d
Spec == Init /\ [][Next]_x /\ WF_x(Next)
TypeOK == x \in Nat
====
