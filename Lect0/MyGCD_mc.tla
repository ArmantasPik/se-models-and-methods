---- MODULE MyGCD_mc ----
EXTENDS MyGCD
CONSTANT R

CorrectR ==
    /\ a = R
    /\ b = R

EventuallyR ==
    <>[]CorrectR

====