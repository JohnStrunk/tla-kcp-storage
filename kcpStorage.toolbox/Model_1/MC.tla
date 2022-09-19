---- MODULE MC ----
EXTENDS kcpStorage, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
C1, C2, C3
----

\* MV CONSTANT definitions CLUSTERS
const_16636019792422000 == 
{C1, C2, C3}
----

\* SYMMETRY definition
symm_16636019792423000 == 
Permutations(const_16636019792422000)
----

=============================================================================
\* Modification History
\* Created Mon Sep 19 11:39:39 EDT 2022 by jstrunk
