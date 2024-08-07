------------------------------ MODULE FastMutex ----------------------------- 

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

(**********************
--algorithm FastMutex
  variables x ; y = 0 ; b = [i \in 1..N |-> FALSE] ; 
process Proc \in 1..N
variables j = 0 ; failed = FALSE ;
begin
start : while TRUE
         do l1 : b[self] := TRUE ;
            l2 : x := self ;
            l3 : if y # 0
                   then l4 : b[self] := FALSE ;
                        l5 : when y = 0 ; skip ;
                   else l6 : y := self ;
                        l7 : if x # self 
                               then l8 : b[self] := FALSE ;
                                         j := 1 ;
                                    l9 : while (j \leq N)
                                           do when ~b[j] ;
                                              j := j+1 ;
                                         end while ;
                                    l10 : if y # self
                                            then when y = 0 ;
                                                 failed := TRUE ;
                                          end if;
                             end if ;
                        cs : if ~ failed
                               then       skip ; \* the critical section
                                    l11 : y := 0 ;
                                    l12 : b[self] := FALSE ;
                               else failed := FALSE ;
                             end if ;
                  end if ;
        end while ;
end process
end algorithm

***********************)

\* BEGIN TRANSLATION (chksum(pcal) = "6934d70d" /\ chksum(tla) = "c3b2ff6d")
CONSTANT defaultInitValue
VARIABLES pc, x, y, b, j, failed

vars == << pc, x, y, b, j, failed >>

ProcSet == (1..N)

Init == (* Global variables *)
        /\ x = defaultInitValue
        /\ y = 0
        /\ b = [i \in 1..N |-> FALSE]
        (* Process Proc *)
        /\ j = [self \in 1..N |-> 0]
        /\ failed = [self \in 1..N |-> FALSE]
        /\ pc = [self \in ProcSet |-> "start"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "l1"]
               /\ UNCHANGED << x, y, b, j, failed >>

l1(self) == /\ pc[self] = "l1"
            /\ b' = [b EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ UNCHANGED << x, y, j, failed >>

l2(self) == /\ pc[self] = "l2"
            /\ x' = self
            /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED << y, b, j, failed >>

l3(self) == /\ pc[self] = "l3"
            /\ IF y # 0
                  THEN /\ pc' = [pc EXCEPT ![self] = "l4"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l6"]
            /\ UNCHANGED << x, y, b, j, failed >>

l4(self) == /\ pc[self] = "l4"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l5"]
            /\ UNCHANGED << x, y, j, failed >>

l5(self) == /\ pc[self] = "l5"
            /\ y = 0
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j, failed >>

l6(self) == /\ pc[self] = "l6"
            /\ y' = self
            /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED << x, b, j, failed >>

l7(self) == /\ pc[self] = "l7"
            /\ IF x # self
                  THEN /\ pc' = [pc EXCEPT ![self] = "l8"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << x, y, b, j, failed >>

l8(self) == /\ pc[self] = "l8"
            /\ b' = [b EXCEPT ![self] = FALSE]
            /\ j' = [j EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "l9"]
            /\ UNCHANGED << x, y, failed >>

l9(self) == /\ pc[self] = "l9"
            /\ IF (j[self] \leq N)
                  THEN /\ ~b[j[self]]
                       /\ j' = [j EXCEPT ![self] = j[self]+1]
                       /\ pc' = [pc EXCEPT ![self] = "l9"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "l10"]
                       /\ j' = j
            /\ UNCHANGED << x, y, b, failed >>

l10(self) == /\ pc[self] = "l10"
             /\ IF y # self
                   THEN /\ y = 0
                        /\ failed' = [failed EXCEPT ![self] = TRUE]
                   ELSE /\ TRUE
                        /\ UNCHANGED failed
             /\ pc' = [pc EXCEPT ![self] = "cs"]
             /\ UNCHANGED << x, y, b, j >>

cs(self) == /\ pc[self] = "cs"
            /\ IF ~ failed[self]
                  THEN /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "l11"]
                       /\ UNCHANGED failed
                  ELSE /\ failed' = [failed EXCEPT ![self] = FALSE]
                       /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED << x, y, b, j >>

l11(self) == /\ pc[self] = "l11"
             /\ y' = 0
             /\ pc' = [pc EXCEPT ![self] = "l12"]
             /\ UNCHANGED << x, b, j, failed >>

l12(self) == /\ pc[self] = "l12"
             /\ b' = [b EXCEPT ![self] = FALSE]
             /\ pc' = [pc EXCEPT ![self] = "start"]
             /\ UNCHANGED << x, y, j, failed >>

Proc(self) == start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
                 \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
                 \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self)
                 \/ l12(self)

Next == (\E self \in 1..N: Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))

\* END TRANSLATION

inCS(i) ==  (pc[i] = "cs") /\ (~failed[i])

Invariant == \A i, k \in 1..N : (i # k) => ~ (inCS(i) /\ inCS(k))


Liveness == []<> \E i \in 1..N : inCS(i)
=============================================================================
