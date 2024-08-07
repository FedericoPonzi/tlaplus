---------------------------- MODULE RealQuicksort2 -------------------------- 
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT MaxLen

ASSUME MaxLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] : 
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

Min(S) == CHOOSE i \in S : \A j \in S : i \leq j
Max(S) == CHOOSE i \in S : \A j \in S : i \geq j

(*   

--algorithm RealQuicksort2
  variables A \in UNION {[1..N -> 1..N] : N \in 0..MaxLen};
            Uns = {1..Len(A)} ;
            new = {} ;
            next = {} ;
  procedure Part(parg)
    begin pt1 : with new1 \in
                      {Min(parg)..piv : piv \in parg \ {Max(parg)}}  do
                with new2 = parg \ new1      do
                new := {new1, new2} ;
                with Ap \in
                      {AA \in PermsOf(A) :
                             (\A i \in 1..Len(A) \ parg : AA[i] = A[i])
                          /\ (\A i \in new1, j \in new2 :
                                  AA[i] \leq AA[j])}  do
                A := Ap;
                return ;
                end with ;
                end with ;
                end with;
    end procedure;
  begin rqs : while Uns # {}
               do with nxt \in Uns do next := nxt ;
                  end with ;
                  Uns := Uns \ {next};
                  if Cardinality(next) > 1
                    then        call Part(next) ;
                         rqs2 : Uns := Uns \cup new ;
                  end if ;
              end while;
  end algorithm

*)
                    
\* BEGIN TRANSLATION (chksum(pcal) = "52883366" /\ chksum(tla) = "e311d19b")
CONSTANT defaultInitValue
VARIABLES pc, A, Uns, new, next, stack, parg

vars == << pc, A, Uns, new, next, stack, parg >>

Init == (* Global variables *)
        /\ A \in UNION {[1..N -> 1..N] : N \in 0..MaxLen}
        /\ Uns = {1..Len(A)}
        /\ new = {}
        /\ next = {}
        (* Procedure Part *)
        /\ parg = defaultInitValue
        /\ stack = << >>
        /\ pc = "rqs"

pt1 == /\ pc = "pt1"
       /\ \E new1 \in {Min(parg)..piv : piv \in parg \ {Max(parg)}}:
            LET new2 == parg \ new1 IN
              /\ new' = {new1, new2}
              /\ \E Ap \in {AA \in PermsOf(A) :
                                  (\A i \in 1..Len(A) \ parg : AA[i] = A[i])
                               /\ (\A i \in new1, j \in new2 :
                                       AA[i] \leq AA[j])}:
                   /\ A' = Ap
                   /\ pc' = Head(stack).pc
                   /\ parg' = Head(stack).parg
                   /\ stack' = Tail(stack)
       /\ UNCHANGED << Uns, next >>

Part == pt1

rqs == /\ pc = "rqs"
       /\ IF Uns # {}
             THEN /\ \E nxt \in Uns:
                       next' = nxt
                  /\ Uns' = Uns \ {next'}
                  /\ IF Cardinality(next') > 1
                        THEN /\ /\ parg' = next'
                                /\ stack' = << [ procedure |->  "Part",
                                                 pc        |->  "rqs2",
                                                 parg      |->  parg ] >>
                                             \o stack
                             /\ pc' = "pt1"
                        ELSE /\ pc' = "rqs"
                             /\ UNCHANGED << stack, parg >>
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << Uns, next, stack, parg >>
       /\ UNCHANGED << A, new >>

rqs2 == /\ pc = "rqs2"
        /\ Uns' = (Uns \cup new)
        /\ pc' = "rqs"
        /\ UNCHANGED << A, new, next, stack, parg >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Part \/ rqs \/ rqs2
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

Invariant == 
   (pc = "Done") => \A i, j \in 1..Len(A) :
                       (i < j) => A[i] \leq A[j]
=============================================================================
