------------------------------- MODULE Either2 ------------------------------ 
EXTENDS Naturals, Sequences, TLC

(* --algorithm Either
      variables x = 0 ; y = 0 ; z = 0 ;
      begin a: either    x := 1 ; 
                      b: x := x + 1; 
                   or y := 1 ; c: y := y + 1;
               end either ;
            d: either when x = 0 ; z := z + 1 ;
                   or when x = 2 ; z := z + 3 ;
               end either ;     
               assert x+y = 2 ;
               assert z = x + 1 ;
     end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "d9025312" /\ chksum(tla) = "1742027")
VARIABLES pc, x, y, z

vars == << pc, x, y, z >>

Init == (* Global variables *)
        /\ x = 0
        /\ y = 0
        /\ z = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ \/ /\ x' = 1
           /\ pc' = "b"
           /\ y' = y
        \/ /\ y' = 1
           /\ pc' = "c"
           /\ x' = x
     /\ z' = z

b == /\ pc = "b"
     /\ x' = x + 1
     /\ pc' = "d"
     /\ UNCHANGED << y, z >>

c == /\ pc = "c"
     /\ y' = y + 1
     /\ pc' = "d"
     /\ UNCHANGED << x, z >>

d == /\ pc = "d"
     /\ \/ /\ x = 0
           /\ z' = z + 1
        \/ /\ x = 2
           /\ z' = z + 3
     /\ Assert(x+y = 2, "Failure of assertion at line 13, column 16.")
     /\ Assert(z' = x + 1, "Failure of assertion at line 14, column 16.")
     /\ pc' = "Done"
     /\ UNCHANGED << x, y >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ c \/ d
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
