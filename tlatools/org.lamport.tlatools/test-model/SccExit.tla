---- MODULE SccExit ----
\* The only <<B>> step leaves the SCC {0, 1}. A liveness check that counted it
\* as a step of the SCC would report a bogus violation of Prop.
EXTENDS Naturals
VARIABLE x
A == x \in {0, 1} /\ x' = 1 - x
B == x = 0 /\ x' = 2
Done == x = 2 /\ UNCHANGED x
Spec == x = 0 /\ [][A \/ B \/ Done]_x /\ WF_x(A) /\ SF_x(B)
Prop == <>[](x = 2)
====
