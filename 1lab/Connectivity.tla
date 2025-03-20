----------------------------- MODULE Connectivity -----------------------------
EXTENDS FiniteSets, TLC

\* Is graph connected
IsConnected(NodeSet, Graph, Root) ==
    LET
        RECURSIVE ReachableFrom(_)
        ReachableFrom(Visited) ==
            LET 
                NewNodes == UNION {Graph[n] : n \in Visited} \ Visited
            IN 
                IF NewNodes = {} 
                THEN Visited \* Corner
                ELSE ReachableFrom(Visited \cup NewNodes)
    IN
        ReachableFrom({Root}) = NodeSet

=============================================================================