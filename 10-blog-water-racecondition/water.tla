------------------------------- MODULE water -------------------------------

EXTENDS Integers, Sequences, FiniteSets

Machines == 1..2

(* --algorithm water 
variables
  Cooler = "free";
  Controller = {};

define
  TypeInvariant == Cooler \in {"free", "controlled"}
  OnlyOneController == Cardinality(Controller) <= 1
end define;

process machine \in Machines
variables 
  power = "off";
begin
    SwitchPower:
    while TRUE do
        either 
            power := "off";
            Controller := Controller \ {self};
        or  
            power := "on";
        end either;

        if self \notin Controller 
            /\ power = "on" 
            /\ Cooler = "free" then
            TakeControl:
            Cooler := "controlled";
            Controller := Controller \union {self};
        end if;

    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "73fbe6c9" /\ chksum(tla) = "70dce8b3")
VARIABLES pc, Cooler, Controller

(* define statement *)
TypeInvariant == Cooler \in {"free", "controlled"}
OnlyOneController == Cardinality(Controller) <= 1

VARIABLE power

vars == << pc, Cooler, Controller, power >>

ProcSet == (Machines)

Init == (* Global variables *)
        /\ Cooler = "free"
        /\ Controller = {}
        (* Process machine *)
        /\ power = [self \in Machines |-> "off"]
        /\ pc = [self \in ProcSet |-> "SwitchPower"]

SwitchPower(self) == /\ pc[self] = "SwitchPower"
                     /\ \/ /\ power' = [power EXCEPT ![self] = "off"]
                           /\ Controller' = Controller \ {self}
                        \/ /\ power' = [power EXCEPT ![self] = "on"]
                           /\ UNCHANGED Controller
                     /\ IF self \notin Controller'
                            /\ power'[self] = "on"
                            /\ Cooler = "free"
                           THEN /\ pc' = [pc EXCEPT ![self] = "TakeControl"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "SwitchPower"]
                     /\ UNCHANGED Cooler

TakeControl(self) == /\ pc[self] = "TakeControl"
                     /\ Cooler' = "controlled"
                     /\ Controller' = (Controller \union {self})
                     /\ pc' = [pc EXCEPT ![self] = "SwitchPower"]
                     /\ power' = power

machine(self) == SwitchPower(self) \/ TakeControl(self)

Next == (\E self \in Machines: machine(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
