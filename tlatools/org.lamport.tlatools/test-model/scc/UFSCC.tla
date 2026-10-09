-------------------------------- MODULE UFSCC --------------------------------
(***************************************************************************)
(* tlc2.tool.liveness.UnionFindSccSearch, the multi-worker SCC search of   *)
(* Bloemen, Laarman and van de Pol (PPoPP'16), with the liveness check of  *)
(* each SCC by the worker that completes it.                               *)
(*                                                                         *)
(* Each action is a step that the Java code does atomically, i.e. under    *)
(* the lock of a set's root. Find is atomic, which abstracts path halving. *)
(* A worker picks any non-empty subset of its set's live nodes, which     *)
(* includes the batches of the rotating live list.                         *)
(***************************************************************************)
EXTENDS SccCheck, Integers, Sequences

CONSTANT Workers

VARIABLES
    parent,  \* The union-find forest.
    owners,  \* owners[r]: The workers that claimed root r's set.
    dead,    \* dead[r]: Root r's set is a complete SCC.
    live,    \* live[r]: The nodes of root r's set not yet fully explored.
    frames,  \* frames[p]: p's DFS stack of [v, picked, pending, succ].
    rstack,  \* rstack[p]: p's stack of the (former) roots of its sets.
    pc,      \* "run", "unite", "pick", "report", "exit" or "error".
    arg,     \* The node of "unite" and the root of "report".
    taken,   \* taken[p]: The initial nodes p searched from.
    stop

vars == <<sccVars, parent, owners, dead, live, frames, rstack, pc, arg, taken,
          stop>>

NoNode == CHOOSE n \in Nodes : TRUE

RECURSIVE Find(_)
Find(n) == IF parent[n] = n THEN n ELSE Find(parent[n])

Members(r) == {n \in Nodes : Find(n) = r}

NewFrame(v) == [v |-> v, picked |-> {}, pending |-> {}, succ |-> {}]

Init ==
    /\ SccInit
    /\ parent = [n \in Nodes |-> n]
    /\ owners = [n \in Nodes |-> {}]
    /\ dead = [n \in Nodes |-> FALSE]
    /\ live = [n \in Nodes |-> {n}]
    /\ frames = [p \in Workers |-> <<>>]
    /\ rstack = [p \in Workers |-> <<>>]
    /\ pc = [p \in Workers |-> "run"]
    /\ arg = [p \in Workers |-> NoNode]
    /\ taken = [p \in Workers |-> {}]
    /\ stop = FALSE

\* The loop of Worker#search continues unless stopped.
Running(p) == pc[p] = "run" /\ ~stop

Top(p) == Head(frames[p])

SetTop(p, f) == frames' = [frames EXCEPT ![p] = <<f>> \o Tail(frames[p])]

Push(p, v, fs) ==
    /\ frames' = [frames EXCEPT ![p] = <<NewFrame(v)>> \o fs]
    /\ rstack' = [rstack EXCEPT ![p] = <<v>> \o @]

Pop(p) ==
    /\ frames' = [frames EXCEPT ![p] = Tail(@)]
    /\ rstack' = [rstack EXCEPT ![p] =
                    IF @ # <<>> /\ Head(@) = Top(p).v THEN Tail(@) ELSE @]

\* UnionFindSccSearch#work, with makeClaim of an initial node.
StartRoot(p) ==
    /\ Running(p)
    /\ frames[p] = <<>>
    /\ \E n \in Roots \ taken[p] :
        /\ taken' = [taken EXCEPT ![p] = @ \cup {n}]
        /\ LET r == Find(n) IN
           IF dead[r] \/ p \in owners[r]
           THEN UNCHANGED <<owners, frames, rstack>>
           ELSE /\ owners' = [owners EXCEPT ![r] = @ \cup {p}]
                /\ Push(p, n, <<>>)
    /\ UNCHANGED <<sccVars, parent, dead, live, pc, arg, stop>>

\* makeClaim of a successor w and what Worker#search does with the claim.
Claim(p) ==
    /\ Running(p)
    /\ frames[p] # <<>>
    /\ \E w \in Top(p).succ :
        LET fs == <<[Top(p) EXCEPT !.succ = @ \ {w}]>> \o Tail(frames[p])
            r == Find(w)
        IN  IF dead[r]
            THEN /\ frames' = [frames EXCEPT ![p] = fs]
                 /\ UNCHANGED <<owners, rstack, pc, arg>>
            ELSE IF p \in owners[r]
            THEN /\ frames' = [frames EXCEPT ![p] = fs]
                 /\ pc' = [pc EXCEPT ![p] = "unite"]
                 /\ arg' = [arg EXCEPT ![p] = w]
                 /\ UNCHANGED <<owners, rstack>>
            ELSE /\ owners' = [owners EXCEPT ![r] = @ \cup {p}]
                 /\ Push(p, w, fs)
                 /\ UNCHANGED <<pc, arg>>
    /\ UNCHANGED <<sccVars, parent, dead, live, taken, stop>>

\* One iteration of uniting the sets on p's stack down to w's set.
Unite(p) ==
    /\ pc[p] = "unite"
    /\ LET w == arg[p] IN
       IF Find(Top(p).v) = Find(w)
       THEN /\ pc' = [pc EXCEPT ![p] = "run"]
            /\ arg' = [arg EXCEPT ![p] = NoNode]
            /\ UNCHANGED <<parent, owners, live, rstack>>
       ELSE LET rs == Tail(rstack[p]) IN
            IF rs = <<>>
            THEN /\ pc' = [pc EXCEPT ![p] = "error"]
                 /\ UNCHANGED <<parent, owners, live, rstack, arg>>
            ELSE LET ra == Find(Head(rs))
                     rb == Find(Head(rstack[p]))
                 IN  /\ rstack' = [rstack EXCEPT ![p] = rs]
                     /\ IF ra = rb
                        THEN UNCHANGED <<parent, owners, live, pc, arg>>
                        ELSE IF dead[ra] \/ dead[rb]
                        THEN /\ pc' = [pc EXCEPT ![p] = "error"]
                             /\ UNCHANGED <<parent, owners, live, arg>>
                        \* Java makes the larger set's root the new root.
                        ELSE \E root \in {ra, rb} :
                             LET child == IF root = ra THEN rb ELSE ra IN
                             /\ parent' = [parent EXCEPT ![child] = root]
                             /\ owners' = [owners EXCEPT ![root] = @ \cup owners[child],
                                                         ![child] = {}]
                             /\ live' = [live EXCEPT ![root] = @ \cup live[child],
                                                     ![child] = {}]
                             /\ UNCHANGED <<pc, arg>>
    /\ UNCHANGED <<sccVars, dead, frames, taken, stop>>

\* successors.of the next picked node.
Fetch(p) ==
    /\ Running(p)
    /\ frames[p] # <<>>
    /\ Top(p).succ = {}
    /\ \E x \in Top(p).pending :
        SetTop(p, [Top(p) EXCEPT !.succ = Succs(x), !.pending = @ \ {x}])
    /\ UNCHANGED <<sccVars, parent, owners, dead, live, rstack, pc, arg, taken,
                   stop>>

\* removeFromList of the picked nodes, which are fully explored. The pick
\* follows without checking stop.
Remove(p) ==
    /\ Running(p)
    /\ frames[p] # <<>>
    /\ Top(p).succ = {}
    /\ Top(p).pending = {}
    /\ Top(p).picked # {}
    /\ LET r == Find(Top(p).v) IN
       live' = [live EXCEPT ![r] = @ \ Top(p).picked]
    /\ SetTop(p, [Top(p) EXCEPT !.picked = {}])
    /\ pc' = [pc EXCEPT ![p] = "pick"]
    /\ UNCHANGED <<sccVars, parent, owners, dead, rstack, arg, taken, stop>>

\* The sets of live nodes of root r's set that a worker may pick at once.
PickSets(r) == SUBSET live[r] \ {{}}

\* pickFromList: Pops the frame if its set is dead, completes the set if it
\* has no live nodes left, or picks some of its live nodes otherwise.
Pick(p) ==
    /\ \/ pc[p] = "pick"
       \/ /\ Running(p)
          /\ frames[p] # <<>>
          /\ Top(p).succ = {}
          /\ Top(p).pending = {}
          /\ Top(p).picked = {}
    /\ LET r == Find(Top(p).v) IN
       IF dead[r]
       THEN /\ Pop(p)
            /\ pc' = [pc EXCEPT ![p] = "run"]
            /\ UNCHANGED <<dead, arg>>
       ELSE IF live[r] = {}
       THEN /\ dead' = [dead EXCEPT ![r] = TRUE]
            /\ pc' = [pc EXCEPT ![p] = "report"]
            /\ arg' = [arg EXCEPT ![p] = r]
            /\ UNCHANGED <<frames, rstack>>
       ELSE \E S \in PickSets(r) :
            /\ SetTop(p, [Top(p) EXCEPT !.picked = S, !.pending = S])
            /\ pc' = [pc EXCEPT ![p] = "run"]
            /\ UNCHANGED <<dead, rstack, arg>>
    /\ UNCHANGED <<sccVars, parent, owners, live, taken, stop>>

\* SccListener#found, i.e. the liveness check of the completed SCC, which
\* stops the search if the SCC violates liveness.
CheckScc(p) ==
    /\ pc[p] = "report"
    /\ LET C == Members(arg[p]) IN
       /\ Record(C)
       /\ IF Violates(C)
          THEN /\ stop' = TRUE
               /\ pc' = [pc EXCEPT ![p] = "exit"]
               /\ UNCHANGED <<frames, rstack>>
          ELSE /\ Pop(p)
               /\ pc' = [pc EXCEPT ![p] = "run"]
               /\ UNCHANGED stop
    /\ arg' = [arg EXCEPT ![p] = NoNode]
    /\ UNCHANGED <<parent, owners, dead, live, taken>>

Done(p) ==
    \/ pc[p] = "exit"
    \/ pc[p] = "run" /\ (stop \/ (frames[p] = <<>> /\ taken[p] = Roots))

\* UnionFindSccSearch#run returns once all workers are done.
Terminate ==
    /\ verdict = "running"
    /\ \A p \in Workers : Done(p)
    /\ Complete
    /\ UNCHANGED <<parent, owners, dead, live, frames, rstack, pc, arg, taken,
                   stop>>

Worker(p) ==
    \/ StartRoot(p) \/ Claim(p) \/ Unite(p) \/ Fetch(p) \/ Remove(p)
    \/ Pick(p) \/ CheckScc(p)

Next == (\E p \in Workers : Worker(p)) \/ Terminate

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Workers : WF_vars(Worker(p))
    /\ WF_vars(Terminate)

NoError == \A p \in Workers : pc[p] # "error"

\* Unlike Terminates, also after a violation, which sets the verdict while
\* other workers may still run.
Returns == <>(\A p \in Workers : Done(p))

=============================================================================
