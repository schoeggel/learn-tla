------------------------------- MODULE mytico -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* 

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2



(* --algorithm mytico_abc
variables
  Module = "free";
  Controller = {};


define
      
TypeInvariant ==
  /\ Module \in {"free", "controlled"}

OnlyOneController == Cardinality(Controller) <= 1
    
end define;

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
            TakeControl:
            Module := "controlled";
            Controller := Controller \union {self};
        end if;

    end while;
end process;



end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "fdf9e3d" /\ chksum(tla) = "b808afa2")
VARIABLES Module, Controller, pc

(* define statement *)
TypeInvariant ==
  /\ Module \in {"free", "controlled"}

OnlyOneController == Cardinality(Controller) <= 1

VARIABLE power

vars == << Module, Controller, pc, power >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Module = "free"
        /\ Controller = {}
        (* Process machine *)
        /\ power = [self \in Machines |-> "off"]
        /\ pc = [self \in ProcSet |-> "Mainswitch"]

Mainswitch(self) == /\ pc[self] = "Mainswitch"
                    /\ \/ /\ power' = [power EXCEPT ![self] = "off"]
                          /\ Controller' = Controller \ {self}
                       \/ /\ power' = [power EXCEPT ![self] = "on"]
                          /\ UNCHANGED Controller
                    /\ IF self \notin Controller' /\ power'[self] = "on" /\ Module = "free"
                          THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Mainswitch"]
                    /\ UNCHANGED Module

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Module' = "controlled"
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
