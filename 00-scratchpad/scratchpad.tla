----------------------------- MODULE scratchpad -----------------------------

EXTENDS Integers, TLC, Sequences, FiniteSets



ToSeconds(time) == time[1]*3600 + time[2]*60 + time[3]
Earlier(t1, t2) == ToSeconds(t1) < ToSeconds(t2)

ClockType == (0..23) \X (0..59) \X (0..59)
ToClock(seconds) == CHOOSE x \in ClockType: ToSeconds(x) = seconds % 86400

TruthTable == [p, q \in BOOLEAN |-> p => q]


\* Eval == BOOLEAN
\* Eval == {t \in ClockType: t[1] = 10 /\ t[2] >= 30 /\ t[3] = 0}
\* Eval == ToClock(-30)


S == <<92>>
Eval == Tail(S)

=============================================================================
\* Modification History
\* Last modified Wed Aug 28 10:32:53 CEST 2024 by joel.koch
\* Created Mon Aug 26 09:02:03 CEST 2024 by joel.koch
