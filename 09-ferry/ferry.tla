------------------------------- MODULE ferry -------------------------------
\*  


EXTENDS Integers, TLC

Min(m, n) == IF m < n THEN m ELSE n

(*
--algorithm DieHard {
  variables big = 0, small = 0;
  
{
    while (TRUE) {
      assert big \in 0..5;
      assert small \in 0..3;
      
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
    }
}
}

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 11:30:02 CEST 2024 by joel.koch
\* Created Tue Aug 27 11:28:17 CEST 2024 by joel.koch
