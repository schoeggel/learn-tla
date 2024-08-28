------------------------------- MODULE myticoLiveness -------------------------------
\* Vereinfachung: Modul C weiss, ob es kontrolliert wird oder nicht.
\* Modul merkt, wenn Controller crasht oder ausgeschaltet wird

EXTENDS Integers, Sequences, FiniteSets, TLC

Machines == 1..2
MaxQsize == 1


(* --algorithm mytico_abc
variables
  Controller = {};

\* requests from Machine to Module are sent through this queue
\* Send machine id (eg. 1..2) to take control, negative id to give up control
  queue = <<>>; 


define
      
\* TypeInvariant ==

\* The set of controllers must never contain more than 1 element
OnlyOneController == Cardinality(Controller) <= 1
isControlled ==  Controller # {}

\* Recover from no controller situation
ControlledEventually == ~isControlled ~> isControlled

end define;


\* Machines A and B can switch on or off individually
\* Fair process can not crash. crashing machine is modeled with power off
fair process machine \in Machines
variables 
begin
    Idle:
    while TRUE do
        
        either 
            if self \in Controller   then
                RequestFree:
                await Len(queue) < MaxQsize;
                queue := Append(queue, -self);
            end if;
        or  
            if self \notin Controller  /\ ~isControlled then
                RequestControl:
                await Len(queue) < MaxQsize;
                queue := Append(queue, self);
            end if;
        end either;

    end while;
end process;


fair process module = (Cardinality(Machines) +1)
variables 
    cmd = 0;

begin
WaitForQueue:
while TRUE do
    await queue # <<>>;
ReadFromQueue:
    cmd := Head(queue);
    queue := Tail(queue);

    if cmd < 0 then
        Controller := Controller \ {-cmd};   
    else
        if Controller = {} then
            Controller := {cmd} \union Controller;
        end if;
    end if;
end while;
end process;


end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4d38152d" /\ chksum(tla) = "6596d88a")
VARIABLES Controller, queue, pc

(* define statement *)
OnlyOneController == Cardinality(Controller) <= 1
isControlled ==  Controller # {}


ControlledEventually == ~isControlled ~> isControlled

VARIABLE cmd

vars == << Controller, queue, pc, cmd >>

ProcSet == (Machines) \cup {(Cardinality(Machines) +1)}

Init == (* Global variables *)
        /\ Controller = {}
        /\ queue = <<>>
        (* Process module *)
        /\ cmd = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Machines -> "Idle"
                                        [] self = (Cardinality(Machines) +1) -> "WaitForQueue"]

Idle(self) == /\ pc[self] = "Idle"
              /\ \/ /\ IF self \in Controller
                          THEN /\ pc' = [pc EXCEPT ![self] = "RequestFree"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Idle"]
                 \/ /\ IF self \notin Controller  /\ ~isControlled
                          THEN /\ pc' = [pc EXCEPT ![self] = "RequestControl"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Idle"]
              /\ UNCHANGED << Controller, queue, cmd >>

RequestFree(self) == /\ pc[self] = "RequestFree"
                     /\ Len(queue) < MaxQsize
                     /\ queue' = Append(queue, -self)
                     /\ pc' = [pc EXCEPT ![self] = "Idle"]
                     /\ UNCHANGED << Controller, cmd >>

RequestControl(self) == /\ pc[self] = "RequestControl"
                        /\ Len(queue) < MaxQsize
                        /\ queue' = Append(queue, self)
                        /\ pc' = [pc EXCEPT ![self] = "Idle"]
                        /\ UNCHANGED << Controller, cmd >>

machine(self) == Idle(self) \/ RequestFree(self) \/ RequestControl(self)

WaitForQueue == /\ pc[(Cardinality(Machines) +1)] = "WaitForQueue"
                /\ queue # <<>>
                /\ pc' = [pc EXCEPT ![(Cardinality(Machines) +1)] = "ReadFromQueue"]
                /\ UNCHANGED << Controller, queue, cmd >>

ReadFromQueue == /\ pc[(Cardinality(Machines) +1)] = "ReadFromQueue"
                 /\ cmd' = Head(queue)
                 /\ queue' = Tail(queue)
                 /\ IF cmd' < 0
                       THEN /\ Controller' = Controller \ {-cmd'}
                       ELSE /\ Controller' = ({cmd'} \union Controller)
                 /\ pc' = [pc EXCEPT ![(Cardinality(Machines) +1)] = "WaitForQueue"]

module == WaitForQueue \/ ReadFromQueue

Next == module
           \/ (\E self \in Machines: machine(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Machines : WF_vars(machine(self))
        /\ WF_vars(module)

\* END TRANSLATION 


=============================================================================
\* Modification History
\* Last modified Tue Aug 27 13:27:18 CEST 2024 by joel.koch
\* Created Tue Aug 27 12:56:18 CEST 2024 by joel.koch
