---- MODULE Choose_0_Plain_Ch ----
EXTENDS Naturals
CONSTANT NAT
VARIABLE x

Init == x = 0
Next == x' = x + CHOOSE d \in NAT : d > 0
Spec == Init /\ [][Next]_x /\ WF_x(Next)
\* [Next]_x == Next \/ UNCHANGED x
TypeOK == x \in NAT
====