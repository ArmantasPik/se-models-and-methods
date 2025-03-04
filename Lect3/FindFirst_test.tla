---- MODULE FindFirst_test ----
EXTENDS FindFirst
VARIABLE tc

Init ==
    tc \in {            \* 1  2  3  4  5
        [e |-> 2,  l |-> <<5, 3, 2, 7, 2>>,  r |-> 3],
        [e |-> 7,  l |-> <<5, 3, 2, 7, 2>>,  r |-> 4],
        [e |-> 1,  l |-> <<5, 3, 2, 7, 2>>,  r |-> 0]
    }

Next == UNCHANGED tc
Spec == Init /\ [][Next]_tc

TestRec == tc.r = FindFirstRec(tc.e, tc.l)
TestCh  == tc.r = FindFirstCh(tc.e, tc.l)
TextEx  == FindFirstEx(tc.e, tc.l, LAMBDA r : tc.r = r)


TestInline ==
    LET e == tc.e
        l == tc.l
        r == tc.r
    IN
    \/ \E n \in DOMAIN l:
          /\ l[n] = e
          /\ \A i \in 1..n-1 : l[i] # e
          /\ (n = r) \* Your condition here.
    \/ \A n \in DOMAIN l: l[n] # e /\ (r = 0)

TestInlinePred ==
    LET e == tc.e
        l == tc.l
        r == tc.r
    IN
    \/ \E n \in DOMAIN l:
          /\ IsFirst(e, l, n)
          /\ (n = r) \* Your condition here.
    \/ \A n \in DOMAIN l: l[n] # e /\ (r = 0)

THEOREM Spec => \* Not used by the TLC
    /\ []TestRec
    /\ []TestCh
    /\ []TextEx
    /\ []TestInline
    /\ []TestInlinePred

====
