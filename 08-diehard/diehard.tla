------------------------------ MODULE diehard ------------------------------
\* Goal: get exactly 4 gallons
\* set model invariant: 'big # 4' and run the modelchecker. 

EXTENDS Integers, Naturals, TLC

Min(m, n) == IF m < n THEN m ELSE n

(* --algorithm DieHard 

variables 
    big = 0;
    small = 0;

define
    NotSolved == big # 4
end define;

begin
    while TRUE do
      either big := 5;    \* fill the big jug
      or     small := 3;  \* fill the small jug
      or     big := 0;    \* empty the big jug
      or     small := 0;  \* empty the small jug
      or                  \* pour from small to big
        with poured = Min(big + small, 5) - big do 
          big := big + poured ;
          small := small - poured;
        end with;
      or                  \* pour from big to small
        with poured = Min(big + small, 3) - small  do 
          big := big - poured ;
          small := small + poured;
        end with;     
    end either;
    end while;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5de266d5" /\ chksum(tla) = "392f9ff9")
VARIABLES big, small

(* define statement *)
NotSolved == big # 4


vars == << big, small >>

Init == (* Global variables *)
        /\ big = 0
        /\ small = 0

Next == \/ /\ big' = 5
           /\ small' = small
        \/ /\ small' = 3
           /\ big' = big
        \/ /\ big' = 0
           /\ small' = small
        \/ /\ small' = 0
           /\ big' = big
        \/ /\ LET poured == Min(big + small, 5) - big IN
                /\ big' = big + poured
                /\ small' = small - poured
        \/ /\ LET poured == Min(big + small, 3) - small IN
                /\ big' = big - poured
                /\ small' = small + poured

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 



=============================================================================
\* Modification History
\* Last modified Wed Aug 28 14:26:34 CEST 2024 by joel.koch
\* Created Tue Aug 27 11:16:04 CEST 2024 by joel.koch
