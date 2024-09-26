------------------------------- MODULE water_reservation -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* Modul merkt, wenn Controller stirbt.

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2

(* --algorithm water_lock
variables
  Cooler = "free";
  CoolerReservedFor = {};
  Controller = {};

define
  TypeInvariant == Cooler \in {"free", "reserved", "controlled"}
  OnlyOneController == Cardinality(Controller) <= 1
  ValidController == (Cooler = "controlled") = (Controller # {})
  ValidReservation == (Cooler = "reserved") = (CoolerReservedFor # {})
end define;

macro putReservation() begin
    if Cooler = "free" /\ CoolerReservedFor = {} then 
        Cooler := "reserved";
        CoolerReservedFor := {self};
    end if;
end macro;

process machine \in Machines
variables 
  power = "off";
begin
    Mainswitch:
    while TRUE do

        either 
            power := "off";
            if self \in Controller then
                Controller := Controller \ {self};
                Cooler := "free";
            end if
        or  
            power := "on";
        end either;
        
        CheckConditionReservation:
        if self \notin Controller /\ power = "on" /\ Cooler = "free" then
            TryReservation:
            putReservation();
        end if;
        
        CheckConditionControl:
        if self \notin Controller /\ power = "on" /\ Cooler = "reserved" /\ self \in CoolerReservedFor then
            TakeControl:
            Cooler := "controlled";
            CoolerReservedFor := {};
            Controller := Controller \union {self};
        end if;

    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3e81f239" /\ chksum(tla) = "2987e90c")
VARIABLES pc, Cooler, CoolerReservedFor, Controller

(* define statement *)
TypeInvariant == Cooler \in {"free", "reserved", "controlled"}
OnlyOneController == Cardinality(Controller) <= 1
ValidController == (Cooler = "controlled") = (Controller # {})
ValidReservation == (Cooler = "reserved") = (CoolerReservedFor # {})

VARIABLE power

vars == << pc, Cooler, CoolerReservedFor, Controller, power >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Cooler = "free"
        /\ CoolerReservedFor = {}
        /\ Controller = {}
        (* Process machine *)
        /\ power = [self \in Machines |-> "off"]
        /\ pc = [self \in ProcSet |-> "Mainswitch"]

Mainswitch(self) == /\ pc[self] = "Mainswitch"
                    /\ \/ /\ power' = [power EXCEPT ![self] = "off"]
                          /\ IF self \in Controller
                                THEN /\ Controller' = Controller \ {self}
                                     /\ Cooler' = "free"
                                ELSE /\ TRUE
                                     /\ UNCHANGED << Cooler, Controller >>
                       \/ /\ power' = [power EXCEPT ![self] = "on"]
                          /\ UNCHANGED <<Cooler, Controller>>
                    /\ pc' = [pc EXCEPT ![self] = "CheckConditionReservation"]
                    /\ UNCHANGED CoolerReservedFor

CheckConditionReservation(self) == /\ pc[self] = "CheckConditionReservation"
                                   /\ IF self \notin Controller /\ power[self] = "on" /\ Cooler = "free"
                                         THEN /\ pc' = [pc EXCEPT ![self] = "TryReservation"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "CheckConditionControl"]
                                   /\ UNCHANGED << Cooler, CoolerReservedFor, 
                                                   Controller, power >>

TryReservation(self) == /\ pc[self] = "TryReservation"
                        /\ IF Cooler = "free" /\ CoolerReservedFor = {}
                              THEN /\ Cooler' = "reserved"
                                   /\ CoolerReservedFor' = {self}
                              ELSE /\ TRUE
                                   /\ UNCHANGED << Cooler, CoolerReservedFor >>
                        /\ pc' = [pc EXCEPT ![self] = "CheckConditionControl"]
                        /\ UNCHANGED << Controller, power >>

CheckConditionControl(self) == /\ pc[self] = "CheckConditionControl"
                               /\ IF self \notin Controller /\ power[self] = "on" /\ Cooler = "reserved" /\ self \in CoolerReservedFor
                                     THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                                     ELSE /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                               /\ UNCHANGED << Cooler, CoolerReservedFor, 
                                               Controller, power >>

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Cooler' = "controlled"
                     /\ CoolerReservedFor' = {}
                     /\ Controller' = (Controller \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                     /\ power' = power

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
