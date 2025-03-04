---- MODULE Choose_1_Elems_Ch ----
EXTENDS Naturals, Sequences
VARIABLE x
VARIABLE e

Init == x = 0 /\ e = <<>>
Next ==
    LET d == CHOOSE d \in Nat : d > 0 IN
        /\ x' = x + d /\ e' = Append(e, d)
    \* /\ x' = x + (CHOOSE d \in Nat : d > 0)
    \* /\ e' = Append(e, (CHOOSE d \in Nat : d > 0))

Spec == Init /\ [][Next]_x /\ WF_x(Next)
TypeOK == x \in Nat
====
