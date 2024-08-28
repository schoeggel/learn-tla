------------------------ MODULE test1 ------------------------

EXTENDS Integers, Sequences, TLC, FiniteSets

Min(m, n) == IF m < n THEN m ELSE n



(*--algorithm foobar11 
variable 
    big = 0;
    small = 0;

define

  NotSolved == big /= 4
  
end define; 


begin
    while (TRUE) do
      either big := 5    \* fill the big jug
      or     small := 3  \* fill the small jug
      or     big := 0    \* empty the big jug
      or     small := 0  \* empty the small jug
      or                 \* pour from small to big
        with (poured = Min(big + small, 5) - big) { 
          big := big + poured ;
          small := small - poured;
         } 
      or                 \* pour from big to small
        with (poured = Min(big + small, 3) - small) { 
          big := big - poured ;
          small := small + poured;
        }     
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "3e1eec53" /\ chksum(tla) = "da5ecaa6")


\* END TRANSLATION 
====
\* Modification History
\* Last modified Mon Aug 26 13:27:55 CEST 2024 by joel.koch
\* Created Mon Aug 26 10:17:19 CEST 2024 by joel.koch
