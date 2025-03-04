---- MODULE MyGCD ----
EXTENDS Naturals
CONSTANTS A, B
ASSUME AssumeAB == A \in Nat /\ B \in Nat
VARIABLES a, b
vars == <<a, b>>

--------------------------
StepA ==
    /\ a > b \* Precondition.
    /\ a' = a - b
    /\ UNCHANGED b
StepB ==
    /\ b > a
    /\ b' = b - a
    /\ UNCHANGED a

--------------------------
Init ==
    /\ a = A
    /\ b = B
Next ==
    \/ StepA
    \/ StepB
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

--------------------------
TypeOK ==
    /\ a \in Nat
    /\ b \in Nat
LessInv ==
    /\ a \leq A
    /\ b \leq B

Divides(n, x) == \E y \in 1..n : n = x * y
CommonDivisor(c) == Divides(A, c) /\ Divides(B, c)
GreatestCD(c) ==
    /\ CommonDivisor(c)
    /\ \A d \in 1..c : CommonDivisor(d) => d \leq c

EqImpliesGCD == (a = b) => GreatestCD(a)
EventuallyEq == <>[](a = b)

-------------------------
INSTANCE TLAPS

THEOREM Spec => []TypeOK
    <1>1. Init => TypeOK
        BY AssumeAB DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        BY DEF TypeOK, Next, vars, StepA, StepB
    <1>q. QED BY <1>1, <1>2, PTL DEF Spec, vars

====
