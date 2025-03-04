---- MODULE FindFirst_SM ----
EXTENDS Sequences, Naturals, FindFirst
CONSTANT Els

VARIABLE e
VARIABLE l

VARIABLE done
VARIABLE acc
VARIABLE res
vars == <<e, l, done, acc, res>>

TypeOK ==
    /\ e \in Els
    /\ l \in Seq(Els)
    /\ done \in BOOLEAN
    /\ acc \in Seq(Els) \* Els = {a, b}, <<>>, <<a>>, ...
    /\ res \in Nat

StepNone ==
    /\ ~done
    /\ acc = <<>>
    /\ done' = TRUE
    /\ res' = 0
    /\ UNCHANGED <<e, l, acc>>

StepFound ==
    /\ ~done
    /\ Len(acc) > 0
    /\ Head(acc) = e
    /\ done' = TRUE
    /\ UNCHANGED <<e, l, res, acc>>

StepNext ==
    /\ ~done
    /\ Len(acc) > 0
    /\ Head(acc) # e
    /\ acc' = Tail(acc)
    /\ res' = res + 1
    /\ UNCHANGED <<e, l, done>>

Init ==
    /\ e \in Els
    \* /\ l \in UNION {[1..n -> Els] : n \in Nat}
    /\ \E n \in Nat:
        /\ n + 1 \in Nat
        /\ l \in [1..n -> Els]
    /\ done = FALSE
    /\ acc = l
    /\ res = 1
Next == StepNone \/ StepFound \/ StepNext
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
----

ResOK ==
    done => IsFirstOrNA(e, l, res)

ResOKEventually ==
    <>[](done /\ IsFirstOrNA(e, l, res))

Terminates == <>[]done
\* TypeOkay == []TypeOK

THEOREM Spec =>
    /\ []TypeOK
    /\ []ResOK
    /\ ResOKEventually
    /\ Terminates


====
