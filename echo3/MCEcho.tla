---- MODULE MCEcho ----
EXTENDS Echo

\* Define small test network for model checking
ConstNodes == {"n1", "n2", "n3", "n4", "n5"}

ConstInitiator == "n1"

ConstTopology == [
  n \in ConstNodes |->
    CASE n = "n1" -> {"n2", "n3"}
    []   n = "n2" -> {"n1", "n4"}
    []   n = "n3" -> {"n1", "n4", "n5"}
    []   n = "n4" -> {"n2", "n3", "n5"}
    []   n = "n5" -> {"n3", "n4"}
]

====