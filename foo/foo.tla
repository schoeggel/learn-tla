------------------------------ MODULE foo ------------------------------

(* --algorithm LiftSimple

variables 
etage = "unten";

process StateMachine = "SM"
begin
  Action:
    either 
      await etage = "unten";
      etage := "mitte";
    or
      await etage = "mitte";
      etage := "unten";
    or
      await etage = "mitte";
      etage := "oben";
    or
      await etage = "oben";
      etage := "unten";
    end either;
    goto Action;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "24dfb357" /\ chksum(tla) = "e6e12176")
VARIABLES pc, etage

vars == << pc, etage >>

ProcSet == {"SM"}

Init == (* Global variables *)
        /\ etage = "unten"
        /\ pc = [self \in ProcSet |-> "Action"]

Action == /\ pc["SM"] = "Action"
          /\ \/ /\ etage = "unten"
                /\ etage' = "mitte"
             \/ /\ etage = "mitte"
                /\ etage' = "unten"
             \/ /\ etage = "mitte"
                /\ etage' = "oben"
             \/ /\ etage = "oben"
                /\ etage' = "unten"
          /\ pc' = [pc EXCEPT !["SM"] = "Action"]

StateMachine == Action

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == StateMachine
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Aug 28 14:26:34 CEST 2024 by joel.koch
\* Created Tue Aug 27 11:16:04 CEST 2024 by joel.koch
