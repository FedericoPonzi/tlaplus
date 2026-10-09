----------------------------- MODULE UFSCCTrace -----------------------------
(***************************************************************************)
(* Trace validation of tlc2.tool.liveness.UnionFindSccSearch: checks that  *)
(* a log of a run, written by UnionFindSccSearchTraceTest, is a behavior   *)
(* of UFSCC. The first line of the log fixes the graph, the initial nodes  *)
(* and the bad nodes; every further line is one atomic step of a worker,   *)
(* which must match the corresponding UFSCC action with the logged values. *)
(*                                                                         *)
(* UFSCC's Terminate is not matched: A Java worker exits once it has taken *)
(* all roots added so far, whereas UFSCC's workers take every root. A root *)
(* added later is searched by the worker that added it. Instead, TraceEnd  *)
(* checks the outcome at the end of the log.                               *)
(***************************************************************************)
EXTENDS UFSCC, Json, TLC, FiniteSets

CONSTANT TraceFile

Log == ndJsonDeserialize(TraceFile)
Hdr == Log[1]
Steps == Len(Log) - 1
Ev(i) == Log[i + 1]

ToSet(s) == {s[i] : i \in DOMAIN s}

\* Overrides of UFSCC's and SccCheck's constants and choice sets (see .cfg).
TraceNodes == 0..(Hdr.nodes - 1)
TraceWorkers == 0..(Hdr.workers - 1)
TraceEdgeSets == {{<<e[1], e[2]>> : e \in ToSet(Hdr.edges)}}
TraceRootSets == {ToSet(Hdr.roots)}
TraceBadSets == {ToSet(Hdr.bad)}

VARIABLE l  \* The log line of the next step.

\* Without this override, TLC would enumerate all subsets of the live nodes.
TracePickSets(r) ==
    IF l <= Steps /\ Ev(l).a = "pick"
    THEN {S \in {ToSet(Ev(l).s)} : S # {} /\ S \subseteq live[r]}
    ELSE {}

-----------------------------------------------------------------------------

ClaimResult(p, n) ==
    LET r == Find(n) IN
    IF dead[r] THEN "DEAD" ELSE IF p \in owners[r] THEN "FOUND" ELSE "SUCCESS"

IsStart(p, n, res) ==
    /\ n \in Roots \ taken[p]
    /\ ClaimResult(p, n) = res
    /\ StartRoot(p)
    /\ taken'[p] = taken[p] \cup {n}

IsClaim(p, n, res) ==
    /\ frames[p] # <<>>
    /\ n \in Top(p).succ
    /\ ClaimResult(p, n) = res
    /\ Claim(p)
    /\ LET f == [Top(p) EXCEPT !.succ = @ \ {n}] IN
       frames'[p] = IF res = "SUCCESS"
                    THEN <<NewFrame(n), f>> \o Tail(frames[p])
                    ELSE <<f>> \o Tail(frames[p])

IsMerge(p, root, child) ==
    /\ parent[child] = child
    /\ Unite(p)
    /\ parent'[child] = root

IsSame(p) ==
    /\ Unite(p)
    /\ pc'[p] = "unite"
    /\ parent' = parent

IsUnited(p) ==
    /\ Unite(p)
    /\ pc'[p] = "run"

IsFetch(p, n) ==
    /\ frames[p] # <<>>
    /\ n \in Top(p).pending
    /\ Fetch(p)
    /\ Head(frames'[p]).pending = Top(p).pending \ {n}

IsRemove(p, S) ==
    /\ frames[p] # <<>>
    /\ Top(p).picked = S
    /\ Remove(p)

IsPick(p, S) ==
    /\ Pick(p)
    /\ pc'[p] = "run"
    /\ Len(frames'[p]) = Len(frames[p])
    /\ Head(frames'[p]).picked = S

IsComplete(p, r) ==
    /\ Pick(p)
    /\ pc'[p] = "report"
    /\ arg'[p] = r

IsDeadSet(p) ==
    /\ Pick(p)
    /\ pc'[p] = "run"
    /\ Len(frames'[p]) = Len(frames[p]) - 1

IsCheck(p, r, S, bad) ==
    /\ arg[p] = r
    /\ Members(r) = S
    /\ Violates(S) = bad
    /\ CheckScc(p)

TraceInit == Init /\ l = 1

TraceNext ==
    /\ l <= Steps
    /\ l' = l + 1
    /\ LET e == Ev(l)
           p == e.p
       IN  CASE e.a = "start"    -> IsStart(p, e.n, e.r)
             [] e.a = "claim"    -> IsClaim(p, e.n, e.r)
             [] e.a = "merge"    -> IsMerge(p, e.root, e.child)
             [] e.a = "same"     -> IsSame(p)
             [] e.a = "united"   -> IsUnited(p)
             [] e.a = "fetch"    -> IsFetch(p, e.n)
             [] e.a = "remove"   -> IsRemove(p, ToSet(e.s))
             [] e.a = "pick"     -> IsPick(p, ToSet(e.s))
             [] e.a = "complete" -> IsComplete(p, e.r)
             [] e.a = "deadset"  -> IsDeadSet(p)
             [] e.a = "check"    -> IsCheck(p, e.r, ToSet(e.s), e.bad)

TraceSpec == TraceInit /\ [][TraceNext]_<<vars, l>>

-----------------------------------------------------------------------------

\* Every UFSCC step of the log is a step of UFSCC's Next.
TraceRefinesUFSCC == [][Next]_vars

\* At the end of the log, the outcome is the one SccSpec requires: Every
\* checked SCC is an SCC reachable from the initial nodes and checked once,
\* and either a violation stopped the search or all of them have been
\* checked, none violates, and the workers have no work left. Checked once at
\* the end, as SCCs is expensive to evaluate on every step (unlike
\* SccSafety, which would).
TraceEnd ==
    l = Steps + 1 =>
        /\ reported \subseteq SCCs
        /\ reports = Cardinality(reported)
        /\ IF stop
           THEN verdict = "violated" /\ cex \in reported /\ Violates(cex)
           ELSE /\ verdict = "running"
                /\ reported = SCCs
                /\ \A C \in SCCs : ~Violates(C)
                /\ \A p \in Workers : frames[p] = <<>> /\ pc[p] = "run"

\* All lines of the log have been matched.
TraceAccepted ==
    LET d == TLCGet("stats").diameter IN
    IF d - 1 = Steps THEN TRUE
    ELSE Print(<<"Trace rejected: no UFSCC step matches line", d + 1, Ev(d)>>, FALSE)
=============================================================================
