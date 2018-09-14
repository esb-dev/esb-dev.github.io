/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 6
   Mengenoperatoren

	$Id: sql06.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */

/* Das Ergebnis einer SQL-Anfrage ist eine (Multi-)Menge von Datensätzen 
   (Tupeln).

   Hat man nun mehrere Ergebnisse, die Tupel derselben Struktur enthalten, 
   die also dasselbe Schema haben, kann man die üblichen Mengenoperationen:
   Vereinigung, Durchschnitt und Differenz verwenden.
*/
    
-- Vereinigung (union)

-- Beispiel: Name aller Kunden und Lieferanten

select Name from Kunde;

/* ergibt:

   name   
----------
 Kehl
 Kehl
 Riesling
*/

select Firma as Name from Lieferant;

/* ergibt:
 
       name        
-------------------
 Weinimport Lehr
 Bremer Weinkontor
*/

/* Wir haben also zwei Ergebnisse mit identischem Schema,
   also können wir die Vereinigung bilden:
*/

select Name from Kunde
union
select Firma as Name from Lieferant;

/* ergibt:

       name        
-------------------
 Bremer Weinkontor
 Riesling
 Weinimport Lehr
 Kehl

Wie wir sehen, ist "union" tatsächlich eine Mengenoperation:
Duplikate sind "verschwunden".
*/



-- Beispiel: Namen, Straße bzw. Postfach, PLZ Ort aller Lieferanten und der Kunden

select * from Lieferant;

select * from Kunde;  

-- Ausgabe genau festlegen

select Firma, Postfach, PLZ, Ort 
  from Lieferant;

select Name, Vorname, Str, PLZ, Ort
  from Kunde;  

-- die Struktur der beiden Ergebnisse angleichen

select Firma as Name, 'PF ' || Postfach as Anschrift1 , PLZ || ' ' || Ort as Anschrift2
  from Lieferant;

/* ergibt:

       name        | anschrift1 |   anschrift2   
-------------------+------------+----------------
 Weinimport Lehr   | PF 45367   | F-68567 Colmar
 Bremer Weinkontor | PF 56      | 28195 Bremen
*/

select Vorname || ' ' || Name as Name, Str as Anschrift1, PLZ || ' ' || Ort as Anschrift2
  from Kunde;

/* ergibt:

      name      |     anschrift1     |    anschrift2     
----------------+--------------------+-------------------
 Thomas Kehl    | Weinstr. 3         | 79675 Kaiserstuhl
 Thomas Kehl    | Im Riesling 3      | 68734 Eltville
 Karin Riesling | 67, Rue du Château | F-68567 Colmar

*/

/*
   Jetzt haben beide Ergebnistabellen denselben Aufbau und 
   wir können ihre Zeilen vereinigen
*/

select Firma as Name, 'PF ' || Postfach as Anschrift1 , PLZ || ' ' || Ort as Anschrift2
  from Lieferant
union  
select Vorname || ' ' || Name as Name, Str as Anschrift1, PLZ || ' ' || Ort as Anschrift2
  from Kunde;

/* ergibt:

       name        |     anschrift1     |    anschrift2     
-------------------+--------------------+-------------------
 Thomas Kehl       | Weinstr. 3         | 79675 Kaiserstuhl
 Bremer Weinkontor | PF 56              | 28195 Bremen
 Thomas Kehl       | Im Riesling 3      | 68734 Eltville
 Karin Riesling    | 67, Rue du Château | F-68567 Colmar
 Weinimport Lehr   | PF 45367           | F-68567 Colmar
*/
  
/* Wenn man Duplikate im Ergebnis behalten möchte,
   verwendet man "union all"
   (Nicht sehr einheitlich: normalerweise elimieren
   Operatoren in SQL Duplikate nicht, die 
   Mengenoperatoren aber schon.)
*/

select Ort from Kunde
union
select Ort from Lieferant;

/* ergibt:

     ort     
-------------
 Bremen
 Eltville
 Colmar
 Kaiserstuhl
*/

select ort from Kunde
union all
select ort from Lieferant;

/* enthält den Ort Colmar doppelt:

     ort     
-------------
 Kaiserstuhl
 Eltville
 Colmar
 Colmar
 Bremen
*/

-- Durchschnitt (intersect)

-- Beispiel: Alle Orte, an denen sowohl ein Kunde als auch ein Lieferant wohnen

select Ort from Kunde
intersect
select Ort from Lieferant;  

/* ergibt:

  ort   
--------
 Colmar
*/

-- Mengendifferenz (except)

-- Beispiel: Alle Orte, an denen ein Kunde wohnt, jedoch kein Lieferant

select Ort from Kunde
except
select Ort from Lieferant;  

/* ergibt:

     ort     
-------------
 Kaiserstuhl
 Eltville
*/

-- Beispiel: Alle Orte, an denen ein Lieferant wohnt, jedoch kein Kunde

select Ort from Lieferant
except
select Ort from Kunde;

/* ergibt:

  ort   
--------
 Bremen
*/
