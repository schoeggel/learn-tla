------------------------------- MODULE myticoLock -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* Modul merkt, wenn Controller stirbt.

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2

(* --algorithm water_lock
variables
  Module = "free";
  ModuleReservedFor = {};
  Controller = {};

define
  TypeInvariant == Module \in {"free", "reserved", "controlled"}
  OnlyOneController == Cardinality(Controller) <= 1
  ValidController == (Module = "controlled") = (Controller # {})
  ValidReservation == (Module = "reserved") = (ModuleReservedFor # {})
end define;

macro putReservation() begin
    if Module = "free" /\ ModuleReservedFor = {} then 
        Module := "reserved";
        ModuleReservedFor := {self};
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
                Module := "free";
            end if
        or  
            power := "on";
        end either;
        
        TryReservation:
        if self \notin Controller /\ power = "on" /\ Module = "free" then
            putReservation();
        end if;
        
        TryTakeControl:
        if self \notin Controller /\ power = "on" /\ Module = "reserved" /\ self \in ModuleReservedFor then
            Module := "controlled";
            ModuleReservedFor := {};
            Controller := Controller \union {self};
        end if;

    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "75ae53ac" /\ chksum(tla) = "2a4768d6")
VARIABLES pc, Module, ModuleReservedFor, Controller

(* define statement *)
TypeInvariant == Module \in {"free", "reserved", "controlled"}
OnlyOneController == Cardinality(Controller) <= 1
ValidController == (Module = "controlled") = (Controller # {})
ValidReservation == (Module = "reserved") = (ModuleReservedFor # {})

VARIABLE power

vars == << pc, Module, ModuleReservedFor, Controller, power >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Module = "free"
        /\ ModuleReservedFor = {}
        /\ Controller = {}
        (* Process machine *)
        /\ power = [self \in Machines |-> "off"]
        /\ pc = [self \in ProcSet |-> "Mainswitch"]

Mainswitch(self) == /\ pc[self] = "Mainswitch"
                    /\ \/ /\ power' = [power EXCEPT ![self] = "off"]
                          /\ IF self \in Controller
                                THEN /\ Controller' = Controller \ {self}
                                     /\ Module' = "free"
                                ELSE /\ TRUE
                                     /\ UNCHANGED << Module, Controller >>
                       \/ /\ power' = [power EXCEPT ![self] = "on"]
                          /\ UNCHANGED <<Module, Controller>>
                    /\ pc' = [pc EXCEPT ![self] = "TryReservation"]
                    /\ UNCHANGED ModuleReservedFor

TryReservation(self) == /\ pc[self] = "TryReservation"
                        /\ IF self \notin Controller /\ power[self] = "on" /\ Module = "free"
                              THEN /\ IF Module = "free" /\ ModuleReservedFor = {}
                                         THEN /\ Module' = "reserved"
                                              /\ ModuleReservedFor' = {self}
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << Module, 
                                                              ModuleReservedFor >>
                              ELSE /\ TRUE
                                   /\ UNCHANGED << Module, ModuleReservedFor >>
                        /\ pc' = [pc EXCEPT ![self] = "TryTakeControl"]
                        /\ UNCHANGED << Controller, power >>

TryTakeControl(self) == /\ pc[self] = "TryTakeControl"
                        /\ IF self \notin Controller /\ power[self] = "on" /\ Module = "reserved" /\ self \in ModuleReservedFor
                              THEN /\ Module' = "controlled"
                                   /\ ModuleReservedFor' = {}
                                   /\ Controller' = (Controller \union {self})
                              ELSE /\ TRUE
                                   /\ UNCHANGED << Module, ModuleReservedFor, 
                                                   Controller >>
                        /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                        /\ power' = power

machine(self) == Mainswitch(self) \/ TryReservation(self)
                    \/ TryTakeControl(self)

Next == (\E self \in Machines: machine(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
