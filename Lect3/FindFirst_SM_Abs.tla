---- MODULE FindFirst_SM_Abs ----
EXTENDS Sequences, Naturals, FindFirst
CONSTANT Els

VARIABLE e
VARIABLE l

VARIABLE done
VARIABLE res
vars == <<e, l, done, res>>

TypeOK ==
    /\ e \in Els
    /\ l \in Seq(Els)
    /\ done \in BOOLEAN
    /\ res \in Nat

StepMagic ==
    /\ ~done
    /\ \E n \in Nat:
        /\ IsFirstOrNA(e, l, n)
        /\ res' = n
        /\ done' = TRUE
    /\ UNCHANGED <<e, l>>

Init ==
    /\ e \in Els
    /\ \E n \in Nat:
        /\ n + 1 \in Nat
        /\ l \in [1..n -> Els]
    /\ done = FALSE
    /\ res = 0
Next == StepMagic
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
