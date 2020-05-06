------------------------------- MODULE hanoi2 -------------------------------
(* Zweite Variante der Türme von Hanoi mit PlusCal,
   basierend auf einer Lösung von Hillel Wayne *)

EXTENDS TLC, Integers, Sequences
(* TLC wird für assert benötigt *) 


(* --algorithm hanoi {

variable towers = << <<1, 2, 3, 4>>, << >>, << >> >>;
(* Als Datenmodell verwenden wir ein Tupel von drei Türmen, das jeweils eine
   Sequenz von Scheiben als Wert hat, wobei die Scheiben und ihre Größe durch
   Zahlen repräsentiert werden. *)
   
define {pos == DOMAIN towers
        (* pos ist der Definitionsbereich von towers, also 1..3 *)
        Cons(elem, seq) == << elem >> \o seq}
        (* Cons bildet die Sequenz aus dem Element elem und der Sequenz seq mit elem als Kopf *)        
          
{ while (TRUE) {
    assert towers[3] /= <<1, 2, 3, 4>>; 
    (* Wenn diese Assertion falsch wird, dann lioegen alle Scheiben auf dem dritten Turm *)
    with (from \in {i1 \in pos: towers[i1] /= << >>},
            to \in   {i2 \in pos: \/ towers[i2] = <<>>
                                  \/ Head(towers[from]) < Head(towers[i2])}){ 
         towers[from] := Tail(towers[from]) ||
         towers[to] := Cons(Head(towers[from]), towers[to]);
    } 
    (* In jedem Schritt wird eine Wahl von from und to gebildet, d.h. eine Wahl zweier Türme,
       bei denen ein Zug möglich ist und dieser Zug wird ausgeführt *)                          
  }
}
}*)          

(* Das Folgende hat der PlusCal-Translator erzeugt: *)

\* BEGIN TRANSLATION
VARIABLE towers

(* define statement *)
pos == DOMAIN towers
Cons(elem, seq) == << elem >> \o seq


vars == << towers >>

Init == (* Global variables *)
        /\ towers = << <<1, 2, 3, 4>>, << >>, << >> >>

Next == /\ Assert(towers[3] /= <<1, 2, 3, 4>>, 
                  "Failure of assertion at line 14, column 5.")
        /\ \E from \in {i1 \in pos: towers[i1] /= << >>}:
             \E to \in {i2 \in pos: \/ towers[i2] = <<>>
                                    \/ Head(towers[from]) < Head(towers[i2])}:
               towers' = [towers EXCEPT ![from] = Tail(towers[from]),
                                        ![to] = Cons(Head(towers[from]), towers[to])]

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu Apr 02 15:55:48 CEST 2020 by br
\* Created Tue Mar 31 14:09:36 CEST 2020 by br
