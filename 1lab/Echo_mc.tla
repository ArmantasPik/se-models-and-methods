----------------------------- MODULE Echo_mc -----------------------------
EXTENDS Echo

ConstNodes == {"n1", "n2", "n3", "n4", "n5"}

ConstInitiator == "n1"

ConstTopology == [
  n \in Nodes |->
    CASE n = "n1" -> {"n2", "n3"}
    []   n = "n2" -> {"n1", "n4"}
    []   n = "n3" -> {"n1", "n4", "n5"}
    []   n = "n4" -> {"n2", "n3", "n5"}
    []   n = "n5" -> {"n3", "n4"}
]

\* Not connected graph example
\* ConstTopology == [
\*   n \in Nodes |->
\*     CASE n = "n1" -> {"n2", "n3"}
\*     []   n = "n2" -> {"n1"}
\*     []   n = "n3" -> {"n1"}
\*     []   n = "n4" -> {"n5"}
\*     []   n = "n5" -> {"n4"}
\* ]

=============================================================================