------------------------------- MODULE myticoLock -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* Modul merkt, wenn Controller stirbt.

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2



(* --algorithm mytico_abc
variables
  Module = "controlled";
  ModuleReservedFor = {};
  Controller = {1};


define
      
TypeInvariant ==
  /\ Module \in {"free", "reserved", "controlled"}

\* The set of controllers must never contain more than 1 element
OnlyOneController == Cardinality(Controller) <= 1

end define;


\*  implicit self ?
macro putReservation() begin
    if Module = "free" /\ ModuleReservedFor = {} then 
        Module := "reserved";
        ModuleReservedFor := {self};
    end if;
end macro;



\* Machines A and B can switch on or off individually
process machine \in Machines
variables 
  power = "off";
begin
    Mainswitch:
    while TRUE do

        either 
            power := "off";
            Controller := Controller \ {self};
        or  
            power := "on";
        end either;

        
        if self \notin Controller /\ power = "on" /\ Module = "free" then
            putReservation();
        end if;
        
        if self \notin Controller /\ power = "on" /\ Module = "reserved" /\ self \in ModuleReservedFor then
            TakeControl:
            Module := "controlled";
            ModuleReservedFor := {};
            Controller := Controller \union {self};
        end if;

    end while;
end process;



end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "c10e383d" /\ chksum(tla) = "b3f8834d")
VARIABLES Module, ModuleReservedFor, Controller, pc

(* define statement *)
TypeInvariant ==
  /\ Module \in {"free", "reserved", "controlled"}


OnlyOneController == Cardinality(Controller) <= 1

VARIABLE power

vars == << Module, ModuleReservedFor, Controller, pc, power >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Module = "controlled"
        /\ ModuleReservedFor = {}
        /\ Controller = {1}
        (* Process machine *)
        /\ power = [self \in Machines |-> "off"]
        /\ pc = [self \in ProcSet |-> "Mainswitch"]

Mainswitch(self) == /\ pc[self] = "Mainswitch"
                    /\ \/ /\ power' = [power EXCEPT ![self] = "off"]
                          /\ Controller' = Controller \ {self}
                       \/ /\ power' = [power EXCEPT ![self] = "on"]
                          /\ UNCHANGED Controller
                    /\ IF self \notin Controller' /\ power'[self] = "on" /\ Module = "free"
                          THEN /\ IF Module = "free" /\ ModuleReservedFor = {}
                                     THEN /\ Module' = "reserved"
                                          /\ ModuleReservedFor' = {self}
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << Module, 
                                                          ModuleReservedFor >>
                          ELSE /\ TRUE
                               /\ UNCHANGED << Module, ModuleReservedFor >>
                    /\ IF self \notin Controller' /\ power'[self] = "on" /\ Module' = "reserved" /\ self \in ModuleReservedFor'
                          THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Module' = "controlled"
                     /\ ModuleReservedFor' = {}
                     /\ Controller' = (Controller \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                     /\ power' = power

machine(self) == Mainswitch(self) \/ TakeControl(self)

Next == (\E self \in Machines: machine(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
