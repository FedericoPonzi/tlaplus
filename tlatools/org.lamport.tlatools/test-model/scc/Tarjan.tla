------------------------------- MODULE Tarjan -------------------------------
(***************************************************************************)
(* Tarjan's sequential SCC search as in tlc2.tool.liveness.LiveWorker,     *)
(* which checks each SCC once Tarjan completes it. The successors of a     *)
(* node are explored in any order.                                         *)
(***************************************************************************)
EXTENDS SccCheck, Integers, Sequences

VARIABLES
    index,   \* 0 iff not yet visited.
    low,
    counter,
    stack,   \* Tarjan's stack of the nodes of incomplete SCCs.
    calls,   \* The DFS: <<[v, succ]>>, where succ are v's unexplored successors.
    todo     \* The initial nodes not yet searched from.

vars == <<sccVars, index, low, counter, stack, calls, todo>>

Range(s) == {s[i] : i \in DOMAIN s}

Min(a, b) == IF a < b THEN a ELSE b

Init ==
    /\ SccInit
    /\ index = [n \in Nodes |-> 0]
    /\ low = [n \in Nodes |-> 0]
    /\ counter = 1
    /\ stack = <<>>
    /\ calls = <<>>
    /\ todo = Roots

Visit(v, cs) ==
    /\ index' = [index EXCEPT ![v] = counter]
    /\ low' = [low EXCEPT ![v] = counter]
    /\ counter' = counter + 1
    /\ stack' = <<v>> \o stack
    /\ calls' = <<[v |-> v, succ |-> Succs(v)]>> \o cs

Start ==
    /\ verdict = "running"
    /\ calls = <<>>
    /\ \E r \in todo :
        /\ todo' = todo \ {r}
        /\ IF index[r] = 0
           THEN Visit(r, calls)
           ELSE UNCHANGED <<index, low, counter, stack, calls>>
    /\ UNCHANGED sccVars

Explore ==
    /\ verdict = "running"
    /\ calls # <<>>
    /\ LET f == Head(calls) IN
       \E w \in f.succ :
         LET cs == <<[f EXCEPT !.succ = @ \ {w}]>> \o Tail(calls) IN
         IF index[w] = 0
         THEN Visit(w, cs)
         ELSE /\ calls' = cs
              /\ low' = IF w \in Range(stack)
                        THEN [low EXCEPT ![f.v] = Min(@, index[w])]
                        ELSE low
              /\ UNCHANGED <<index, counter, stack>>
    /\ UNCHANGED <<sccVars, todo>>

Return ==
    /\ verdict = "running"
    /\ calls # <<>>
    /\ Head(calls).succ = {}
    /\ LET v == Head(calls).v IN
       /\ calls' = Tail(calls)
       /\ IF low[v] = index[v]
          THEN LET k == CHOOSE i \in DOMAIN stack : stack[i] = v IN
               /\ stack' = SubSeq(stack, k + 1, Len(stack))
               /\ Record(Range(SubSeq(stack, 1, k)))
               /\ UNCHANGED low
          \* A DFS root has low = index, thus v has a caller.
          ELSE /\ low' = [low EXCEPT ![Head(Tail(calls)).v] = Min(@, low[v])]
               /\ UNCHANGED <<stack, sccVars>>
    /\ UNCHANGED <<index, counter, todo>>

Done ==
    /\ verdict = "running"
    /\ calls = <<>>
    /\ todo = {}
    /\ Complete
    /\ UNCHANGED <<index, low, counter, stack, calls, todo>>

Next == Start \/ Explore \/ Return \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================
