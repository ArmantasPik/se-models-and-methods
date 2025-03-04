---- MODULE FindFirst_SM_Ref ----
EXTENDS FindFirst_SM

Abs == INSTANCE FindFirst_SM_Abs
        WITH
            e <- e,
            l <- l,
            res <- (IF done THEN res ELSE 0)

Refinement == Abs!Spec

THEOREM Spec => Refinement

====
