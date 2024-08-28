
---- MODULE reader_writer ----
EXTENDS Integers, Sequences, TLC

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;


process writer = 1
begin
  AddToQueue:
    queue := Append(queue, 1);
end process;

process reader = 0
begin
  ReadFromQueue:
   if queue # <<>> then
    total := total + Head(queue);
    queue := Tail(queue);
   end if;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "90fcbeb6" /\ chksum(tla) = "40a81529")
VARIABLES queue, total, pc

vars == << queue, total, pc >>

ProcSet == {1} \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue == /\ pc[1] = "AddToQueue"
              /\ queue' = Append(queue, 1)
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ total' = total

writer == AddToQueue

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ IF queue # <<>>
                       THEN /\ total' = total + Head(queue)
                            /\ queue' = Tail(queue)
                       ELSE /\ TRUE
                            /\ UNCHANGED << queue, total >>
                 /\ pc' = [pc EXCEPT ![0] = "Done"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == writer \/ reader
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
====


=============================================================================
\* Modification History
\* Last modified Mon Aug 26 13:50:09 CEST 2024 by joel.koch
\* Created Mon Aug 26 13:43:29 CEST 2024 by joel.koch
