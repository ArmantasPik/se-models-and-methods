----------------------------- MODULE Echo_Refinement -----------------------------
EXTENDS Echo

\* Define the refinement mapping from Echo (concrete) to Echo_Abs (abstract)
Abs == INSTANCE Echo_Abs
        WITH
            visited <- visited,    \* Direct mapping of visited set
            done <- done           \* Direct mapping of done set

\* The refinement property states that the concrete spec implements the abstract spec
Refinement == Abs!Spec

\* This theorem states that every behavior of the concrete spec
\* satisfies the abstract spec under the mapping defined by WITH
THEOREM Spec => Refinement

============================================================================= 