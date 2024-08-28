---- MODULE threadsweb ----
EXTENDS TLC, Sequences, Integers

NumThreads == 2
Threads == 1..NumThreads

(* --algorithm threads

variables 
  counter = 0;

define
  AllDone == 
    \A t \in Threads: pc[t] = "Done"

  Correct ==
      AllDone => counter = NumThreads
end define;  

process thread \in Threads
variables tmp = 0;
begin
  GetCounter:
    tmp := counter;

  IncCounter:
    counter := tmp + 1;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "98a593c7" /\ chksum(tla) = "db75cf55")
VARIABLES counter, pc

(* define statement *)
AllDone ==
  \A t \in Threads: pc[t] = "Done"

Correct ==
    AllDone => counter = NumThreads

VARIABLE tmp

vars == << counter, pc, tmp >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ counter = 0
        (* Process thread *)
        /\ tmp = [self \in Threads |-> 0]
        /\ pc = [self \in ProcSet |-> "GetCounter"]

GetCounter(self) == /\ pc[self] = "GetCounter"
                    /\ tmp' = [tmp EXCEPT ![self] = counter]
                    /\ pc' = [pc EXCEPT ![self] = "IncCounter"]
                    /\ UNCHANGED counter

IncCounter(self) == /\ pc[self] = "IncCounter"
                    /\ counter' = tmp[self] + 1
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ tmp' = tmp

thread(self) == GetCounter(self) \/ IncCounter(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Threads: thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* Needs to be below translation
TypeInvariant ==
  /\ counter \in 0..NumThreads
  /\ tmp \in [Threads -> 0..NumThreads]


====

\* Modification History
\* Last modified Tue Aug 27 10:09:42 CEST 2024 by joel.koch
\* Created Tue Aug 27 09:50:37 CEST 2024 by joel.koch
