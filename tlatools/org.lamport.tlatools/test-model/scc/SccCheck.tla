------------------------------ MODULE SccCheck ------------------------------
(***************************************************************************)
(* What TLC's liveness checking requires of an SCC search: Every SCC of    *)
(* the behavior graph that is reachable from the initial nodes is checked  *)
(* once, and the check finds a violation iff one of the SCCs violates      *)
(* liveness. The graph, its initial nodes and the violating nodes are      *)
(* chosen nondeterministically, so that a single model covers all graphs   *)
(* over Nodes.                                                             *)
(*                                                                         *)
(* An implementation EXTENDS this module, updates the variables below with *)
(* Record and Complete only, and checks SccSpec as a property.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Nodes

VARIABLES
    E,        \* The edges of the graph.
    Roots,    \* The initial nodes.
    Bad,      \* An SCC violates liveness iff it contains a Bad node.
    reported, \* The SCCs passed to the liveness check so far.
    verdict,  \* "running", "ok" or "violated".
    cex,      \* A violating SCC once verdict = "violated".
    reports   \* The number of checks; unlike reported, counts a duplicate.

sccVars == <<E, Roots, Bad, reported, verdict, cex, reports>>

Succs(n) == {m \in Nodes : <<n, m>> \in E}

RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    LET T == S \cup UNION {Succs(n) : n \in S}
    IN  IF T = S THEN S ELSE ReachFrom(T)

Reachable == ReachFrom(Roots)

SCCs ==
    LET R == [n \in Nodes |-> ReachFrom({n})]
    IN  {{m \in R[n] : n \in R[m]} : n \in Reachable}

Violates(C) == C \cap Bad # {}

\* A single bad node suffices to tell violating SCCs from the others. Smaller
\* models override these in their .cfg.
RootSets == SUBSET Nodes \ {{}}
BadSets == {{}} \cup {{n} : n \in Nodes}

-----------------------------------------------------------------------------

SccInit ==
    /\ E \in SUBSET (Nodes \X Nodes)
    /\ Roots \in RootSets
    /\ Bad \in BadSets
    /\ reported = {}
    /\ verdict = "running"
    /\ cex = {}
    /\ reports = 0

\* The first violating SCC decides the verdict; SCCs checked concurrently
\* with or after it do not change it.
Record(C) ==
    /\ reported' = reported \cup {C}
    /\ reports' = reports + 1
    /\ IF verdict = "running" /\ Violates(C)
       THEN verdict' = "violated" /\ cex' = C
       ELSE UNCHANGED <<verdict, cex>>
    /\ UNCHANGED <<E, Roots, Bad>>

Report == \E C \in SCCs \ reported : Record(C)

Complete ==
    /\ verdict' = "ok"
    /\ UNCHANGED <<E, Roots, Bad, reported, cex, reports>>

Finish ==
    /\ verdict = "running"
    /\ reported = SCCs
    /\ Complete

SccNext == Report \/ Finish

\* Once a violation is found, the remaining SCCs need not be checked.
SccSpec ==
    /\ SccInit
    /\ [][SccNext]_sccVars
    /\ WF_sccVars(verdict = "running" /\ Report)
    /\ WF_sccVars(Finish)

\* Equivalent to SccSpec: Its fairness conditions hold trivially once the
\* verdict is no longer "running", which SccSpec guarantees eventually.
\* Unlike SccSpec, TLC checks these without a costly tableau.
SccSafety == SccInit /\ [][SccNext]_sccVars

Terminates == <>(verdict # "running")

-----------------------------------------------------------------------------

Correct ==
    /\ verdict = "ok" => \A C \in SCCs : ~Violates(C)
    /\ verdict = "violated" => cex \in SCCs /\ Violates(cex)

=============================================================================
