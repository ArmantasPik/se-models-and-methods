---- MODULE FindFirst ----
EXTENDS Sequences, Naturals

RECURSIVE FindFirstRecStep(_, _, _)
FindFirstRecStep(e, l, n) ==
    IF l = <<>>
    THEN 0
    ELSE IF Head(l) = e
         THEN n
         ELSE FindFirstRecStep(e, Tail(l), n+1)

FindFirstRec(e, l) == FindFirstRecStep(e, l, 1)

----

FindFirstCh(e, l) ==
    CHOOSE n \in Nat :
        IF \E i \in DOMAIN l : l[i] = e
        THEN  \* describing the properties of a result.
            /\ n \in DOMAIN l             \* Some position in a list.
            /\ l[n] = e                   \* it has to point to our value.
            /\ \A i \in 1..n-1 : l[i] # e \* It has to be the first.
        ELSE n = 0

FindFirstEx(e, l, P(_)) ==
    \/ \E n \in DOMAIN l:
        /\ l[n] = e
        /\ \A i \in 1..n-1 : l[i] # e
        /\ P(n)
    \/ \A n \in DOMAIN l:
        /\ l[n] # e
        /\ P(0)

IsFirst(e, l, n) ==
    /\ n \in DOMAIN l
    /\ l[n] = e
    /\ \A i \in 1..n-1 : l[i] # e

IsFirstOrNA(e, l, n) ==
    \/ IsFirst(e, l, n)
    \/ n = 0 /\ \A i \in DOMAIN l: l[i] # e

====
