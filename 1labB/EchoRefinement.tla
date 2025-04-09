----------------------------- MODULE EchoRefinement -----------------------------
EXTENDS Echo

\* Import abstract specification with refinement mapping
AbstractSpec == INSTANCE AbstractEcho WITH 
    avisited <- visited,
    adone <- done

\* Safety property: The concrete spec implements the abstract spec's safety properties
RefinementSafety == AbstractSpec!ASpec

\* Liveness property: The concrete spec implements the abstract spec's liveness properties
RefinementLiveness == AbstractSpec!ATermination

\* Invariants from AbstractEcho
AbstractDoneVisitedInv == AbstractSpec!ADoneVisitedInv
AbstractNeighborsVisitedInv == AbstractSpec!ADoneNeighborsVisitedInv

\* Additional invariant: In the concrete model, when a node is done, it has correctly 
\* identified its children (nodes that acknowledged to it)
ChildrenInvariant == 
    \A n \in done : 
        children[n] = {m \in Nodes : <<m, n>> \in ackSent}

============================================================================= 