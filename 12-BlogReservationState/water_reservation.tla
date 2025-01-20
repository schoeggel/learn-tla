------------------------------- MODULE water_reservation -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* Modul merkt, wenn Controller stirbt.

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2

(* --algorithm water_lock
variables
  Fridge = "idle";
  FridgeReservedFor = {};
  Controller = {};

define
  TypeInvariant == Fridge \in {"idle", "reserved", "dispense"}
  OnlyOneController == Cardinality(Controller) <= 1
  ValidController == (Fridge = "dispense") = (Controller # {})
  ValidReservation == (Fridge = "reserved") = (FridgeReservedFor # {})
end define;

macro putReservation() begin
    if Fridge = "idle" /\ FridgeReservedFor = {} then 
        Fridge := "reserved";
        FridgeReservedFor := {self};
    end if;
end macro;

process machine \in Machines
variables 
  requestFridge =  "none";
begin
    Mainswitch:
    while TRUE do

        either 
            requestFridge :=  "none";
            if self \in Controller then
                Controller := Controller \ {self};
                Fridge := "idle";
            end if
        or  
            requestFridge := "dispense";
        end either;
        
        CheckConditionReservation:
        if self \notin Controller /\ requestFridge = "dispense" /\ Fridge = "idle" then
            TryReservation:
            putReservation();
        end if;
        
        CheckConditionControl:
        if self \notin Controller 
                /\ requestFridge = "dispense" 
                /\ Fridge = "reserved" 
                /\ self \in FridgeReservedFor then
            TakeControl:
            Fridge := "dispense";
            FridgeReservedFor := {};
            Controller := Controller \union {self};
        end if;

    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "9a290e18" /\ chksum(tla) = "fc57852")
VARIABLES pc, Fridge, FridgeReservedFor, Controller

(* define statement *)
TypeInvariant == Fridge \in {"idle", "reserved", "dispense"}
OnlyOneController == Cardinality(Controller) <= 1
ValidController == (Fridge = "dispense") = (Controller # {})
ValidReservation == (Fridge = "reserved") = (FridgeReservedFor # {})

VARIABLE requestFridge

vars == << pc, Fridge, FridgeReservedFor, Controller, requestFridge >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Fridge = "idle"
        /\ FridgeReservedFor = {}
        /\ Controller = {}
        (* Process machine *)
        /\ requestFridge = [self \in Machines |-> "none"]
        /\ pc = [self \in ProcSet |-> "Mainswitch"]

Mainswitch(self) == /\ pc[self] = "Mainswitch"
                    /\ \/ /\ requestFridge' = [requestFridge EXCEPT ![self] = "none"]
                          /\ IF self \in Controller
                                THEN /\ Controller' = Controller \ {self}
                                     /\ Fridge' = "idle"
                                ELSE /\ TRUE
                                     /\ UNCHANGED << Fridge, Controller >>
                       \/ /\ requestFridge' = [requestFridge EXCEPT ![self] = "dispense"]
                          /\ UNCHANGED <<Fridge, Controller>>
                    /\ pc' = [pc EXCEPT ![self] = "CheckConditionReservation"]
                    /\ UNCHANGED FridgeReservedFor

CheckConditionReservation(self) == /\ pc[self] = "CheckConditionReservation"
                                   /\ IF self \notin Controller /\ requestFridge[self] = "dispense" /\ Fridge = "idle"
                                         THEN /\ pc' = [pc EXCEPT ![self] = "TryReservation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "CheckConditionControl"]
                                   /\ UNCHANGED << Fridge, FridgeReservedFor, 
                                                   Controller, requestFridge >>

TryReservation(self) == /\ pc[self] = "TryReservation"
                        /\ IF Fridge = "idle" /\ FridgeReservedFor = {}
                              THEN /\ Fridge' = "reserved"
                                   /\ FridgeReservedFor' = {self}
                              ELSE /\ TRUE
                                   /\ UNCHANGED << Fridge, FridgeReservedFor >>
                        /\ pc' = [pc EXCEPT ![self] = "CheckConditionControl"]
                        /\ UNCHANGED << Controller, requestFridge >>

CheckConditionControl(self) == /\ pc[self] = "CheckConditionControl"
                               /\ IF self \notin Controller
                                          /\ requestFridge[self] = "dispense"
                                          /\ Fridge = "reserved"
                                          /\ self \in FridgeReservedFor
                                     THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                               /\ UNCHANGED << Fridge, FridgeReservedFor, 
                                               Controller, requestFridge >>

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Fridge' = "dispense"
                     /\ FridgeReservedFor' = {}
                     /\ Controller' = (Controller \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                     /\ UNCHANGED requestFridge

machine(self) == Mainswitch(self) \/ CheckConditionReservation(self)
                    \/ TryReservation(self) \/ CheckConditionControl(self)
                    \/ TakeControl(self)

Next == (\E self \in Machines: machine(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
