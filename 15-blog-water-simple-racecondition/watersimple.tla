------------------------------- MODULE watersimple -------------------------------

EXTENDS Integers, Sequences, FiniteSets

Machines == 1..2

(* --algorithm water 
variables 
  Fridge = "idle";
  Controller = {};


define   
  TypeInvariant == Fridge \in {"idle", "dispense"}
  OnlyOneController == Cardinality(Controller) <= 1
  ValidController == (Fridge = "dispense") = (Controller # {})
end define

process machine \in Machines 
variables 
  requestFridge = "none";
begin
    UserInput:
    while TRUE do
        either 
            requestFridge := "none";
            if self \in Controller then
                Controller := Controller \ {self};
                Fridge := "idle";
            end if
        or  
            requestFridge := "dispense";
        end either; 

        if self \notin Controller 
            /\ requestFridge = "dispense" 
            /\ Fridge = "idle" then
            TakeControl:
            Fridge := "dispense";
            Controller := Controller \union {self};
        end if;

    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c25e1687" /\ chksum(tla) = "4a558711")
VARIABLES pc, Fridge, Controller

(* define statement *)
TypeInvariant == Fridge \in {"idle", "dispense"}
OnlyOneController == Cardinality(Controller) <= 1
ValidController == (Fridge = "dispense") = (Controller # {})

VARIABLE requestFridge

vars == << pc, Fridge, Controller, requestFridge >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Fridge = "idle"
        /\ Controller = {}
        (* Process machine *)
        /\ requestFridge = [self \in Machines |-> "none"]
        /\ pc = [self \in ProcSet |-> "UserInput"]

UserInput(self) == /\ pc[self] = "UserInput"
                   /\ \/ /\ requestFridge' = [requestFridge EXCEPT ![self] = "none"]
                         /\ IF self \in Controller
                               THEN /\ Controller' = Controller \ {self}
                                    /\ Fridge' = "idle"
                               ELSE /\ TRUE
                                    /\ UNCHANGED << Fridge, Controller >>
                      \/ /\ requestFridge' = [requestFridge EXCEPT ![self] = "dispense"]
                         /\ UNCHANGED <<Fridge, Controller>>
                   /\ IF self \notin Controller'
                          /\ requestFridge'[self] = "dispense"
                          /\ Fridge' = "idle"
                         THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "UserInput"]

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Fridge' = "dispense"
                     /\ Controller' = (Controller \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "UserInput"]
                     /\ UNCHANGED requestFridge

machine(self) == UserInput(self) \/ TakeControl(self)

Next == (\E self \in Machines: machine(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
