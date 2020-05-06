 ------------------------------- MODULE hanoi1 -------------------------------

EXTENDS Integers, Sequences
(* Wir verwenden diese beiden Module. EXTENDS bedeutet, dass die Deklarationen
   und Definitionen von Integers und Sequences in unserem Modul auch vorhanden
   sind. 
*)
   
(* Das Datenmodell:
   Wir haben die drei Türme links, mitte, rechts
   Jeder Turm ist eine Sequenz, die die Scheiben enthält.
   Die Scheiben sind die Zahlen 1, 2, 3 und 4, die zugleich für die Größe stehen.
*)
VARIABLES l, m, r

Init == /\ l = << 1, 2, 3, 4>>
        /\ m = << >>
        /\ r = << >>
(* Ausgangssituation, der linke Turm ist voll, die beiden anderen leer *)      

Empty(seq) == Len(seq) <= 0
(* == ist eine Definition, die in diesem Fall das Prädikat Empty einführt *)

Cons(elem, seq) == << elem >> \o seq
(* Cons kommt von construct und ist die Sequenz mit dem Kopf elem und dem
   Rest seq *)

CanMove(t1, t2) == 
  /\ ~ Empty(t1)
  /\ Empty(t2) \/ (~ Empty(t2) /\ Head(t1) < Head(t2))
(* TLA+ hat eine spezielle Syntax für Konjunktionen und Disjunktionen.
   In diesem Beispiel haben wir die zwei Zeilen, die durch and verbunden
   sind. In der zweiten Zeile haben wir ein oder.
   Die Aussage ist also:
   t1 ist nicht leer und
   (t2 ist leer oder andernfalls der oberste Ring von t1 < der oberste Ring von t2)
   Ein Zug ist genau dann möglich, wenn diese Bedingung erfüllt ist *)  

Move(t1, t2, t3) ==
  /\ CanMove(t1, t2)
  /\ t1' = Tail(t1) /\ t2' = Cons(Head(t1), t2) /\ t3' = t3
(* Ein Zug kann stattfinden, wenn er möglich ist und hat dann
   die Situation in der Zeile zur Folge *)
   
Next ==
  \/ Move(l, m, r) \/ Move(l, r, m)
  \/ Move(m, l, r) \/ Move(m, r, l)
  \/ Move(r, l, m) \/ Move(r, m, l)
(* Das sind alle möglichen Zustandswechsel nach Init *)

Spec == Init /\ [][Next]_<<l, m, r>>
(* Das ist jetzt die gesamte Formel mit der Möglichkeit, dass auch alles
   gleich bleiben kann (ist das nötig in diesem Beispiel?) *)

Goal == r = <<1, 2, 3, 4>>
(* Das ist das Ziel des Spiels *)

Check == \lnot Goal
(* Wenn man diese Invariante checkt, dann wird TLC einen Fehler finden, d.h.
   eine Folge von Schritten die zu Goal führt *)

=============================================================================
\* Modification History
\* Last modified Thu Apr 02 08:37:09 CEST 2020 by br
\* Created Tue Mar 24 15:06:50 CET 2020 by br
