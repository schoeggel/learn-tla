---- MODULE threads ----
EXTENDS Integers, Sequences, TLC

Writers == {1, 2, 3}

(* --algorithm reader_writer
variables
  queue = <<>>;
  total = 0;


define
  WritersDone ==  \A w \in Writers: pc[w] = "Done"
  \* Wird nie erreicht: ReadersDone == pc[0] = "Done"
  ReadersDone ==  queue = <<>>
  AllDone == WritersDone /\ ReadersDone
  Correct == AllDone => total = 6
end define;  


process writer \in Writers
begin
  AddToQueue:
    await queue = <<>>;
    queue := Append(queue, self);
end process;

process reader = 0
begin
  ReadFromQueue:
    await queue # <<>>;
      total := total + Head(queue);
      queue := Tail(queue);
    goto ReadFromQueue;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "eb2f969e" /\ chksum(tla) = "9d3546e8")
VARIABLES queue, total, pc

(* define statement *)
WritersDone ==  \A w \in Writers: pc[w] = "Done"

ReadersDone ==  queue = <<>>
AllDone == WritersDone /\ ReadersDone
Correct == AllDone => total = 7


vars == << queue, total, pc >>

ProcSet == (Writers) \cup {0}

Init == (* Global variables *)
        /\ queue = <<>>
        /\ total = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Writers -> "AddToQueue"
                                        [] self = 0 -> "ReadFromQueue"]

AddToQueue(self) == /\ pc[self] = "AddToQueue"
                    /\ queue = <<>>
                    /\ queue' = Append(queue, self)
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ total' = total

writer(self) == AddToQueue(self)

ReadFromQueue == /\ pc[0] = "ReadFromQueue"
                 /\ queue # <<>>
                 /\ total' = total + Head(queue)
                 /\ queue' = Tail(queue)
                 /\ pc' = [pc EXCEPT ![0] = "ReadFromQueue"]

reader == ReadFromQueue

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == reader
           \/ (\E self \in Writers: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 


  
====

\* Modification History
\* Last modified Tue Aug 27 09:58:38 CEST 2024 by joel.koch
\* Created Tue Aug 27 08:40:33 CEST 2024 by joel.koch
