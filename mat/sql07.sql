/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 7
   Geschachtelte Anweisungen

	$Id: sql07.sql 364 2019-03-04 08:31:40Z br $
   ----------------------------------------------------------------------- */
;
/* In SQL kann man stets

   - an Stelle eines Werts auch einen Ausdruck schreiben, der einen Wert ergibt, 
   - an Stelle einer Folge von Werten einen Ausdruck schreiben, der eine Folge ergibt,
   - an Stelle einer Tabelle einen Ausdruck schreiben, der eine Tabelle ergibt.

   Man nennt dies dann "geschachtelte SQL-Anweisungen".
*/

;
-- Beispiel: Anzahl der Weißweine und Rotweine im Angebot

/* Ziel ist eine Tabelle mit folgendem Aufbau

Anz Weißweine | Anz Rotweine
----------------------------
    n1        |     n2

   Wir bauen dies schrittweise auf:
*/

-- das Folgende tut's nicht
select farbe, count(*) from Artikel
	where Farbe in ('rot', 'weiß')
   group by farbe;


-- zuerst Zahl der Weißweine

select count(*) from Artikel where Farbe = 'weiß';   

-- jetzt Zahl der Rotweine

select count(*) from Artikel where Farbe = 'rot';

-- jetzt zusammensetzen

select 2 as "Anz Weißweine", 2 as "Anz Rotweine";

-- jetzt an Stelle des Werts den Ausdruck einsetzen, der den Wert ergibt
-- vorher einsetzen!!

select (select count(*) from Artikel where Farbe = 'weiß') as "Anz Weißweine",
       (select count(*) from Artikel where Farbe = 'rot') as "Anz Rotweine";

/* ergibt:

 Anz Weißweine | Anz Rotweine 
---------------+--------------
             2 |            2
*/
;


-- Beispiel: Adressen von Lieferanten oder Kunden in Frankreich

/* Wir haben schon weiter oben überlegt, wie wir Kunden und
   Lieferanten in einem Tabelle bekommen
*/

select Vorname || ' ' || Name as Name, Str as Anschrift1, PLZ || ' ' || Ort as Anschrift2
   from Kunde
union
select Firma as Name, 'PF ' || Postfach as Anschrift2, PLZ || ' ' || Ort as Anschrift2  
   from Lieferant;

/* Dieses Konstrukt nehmen wir nun als Tabelle mit der Tupelvariable Anschrift
   Wir erkennen französische Adressen an Anschrift2
*/

select * 
   from (select Vorname || ' ' || Name as Name, Str as Anschrift1, PLZ || ' ' || Ort as Anschrift2
           from Kunde
         union
         select Firma as Name, 'PF ' || Postfach as Anschrift2, PLZ || ' ' || Ort as Anschrift2  
         from Lieferant) as Anschriften
   where Anschrift2 like 'F-%';

/* ergibt:

      name       |     anschrift1     |   anschrift2   
-----------------+--------------------+----------------
 Karin Riesling  | 67, Rue du Château | F-68567 Colmar
 Weinimport Lehr | PF 45367           | F-68567 Colmar
*/
;

-- Beispiel: Artikel mit dem höchsten Preis

select * from Artikel
   where Preis = (select max(Preis) from Artikel);  

/* ergibt:

 artnr  |     bez      |  weingut  | jahrgang | farbe | preis 
--------+--------------+-----------+----------+-------+-------
 100001 | Les Châteaux | Louis Max |     2002 | rot   | 17.90
*/
;

-- Beispiel: Kunden, die einen Auftrag erteilt haben

/* Suchen wir zunächst die KndNr in den Aufrägen
*/

select distinct KndNr from Auftrag where KndNr is not null;

/* ergibt:

 kndnr  
--------
 100101
 100102
*/

/* Also die gesuchten Kunden:
*/

select KndNr, Name, Vorname, Ort 
   from Kunde
   where KndNr in (100101, 100102);

/* ergibt:

 kndnr  | name | vorname |     ort     
--------+------+---------+-------------
 100101 | Kehl | Thomas  | Kaiserstuhl
 100102 | Kehl | Thomas  | Eltville
*/
;

/* Nun setzen wir die erste Anweisung an Stelle der Folge ein:
*/
 
select KndNr, Name, Vorname, Ort 
   from Kunde
   where KndNr in (select KndNr from Auftrag where KndNr is not null);

/* ergibt:

 kndnr  | name | vorname |     ort     
--------+------+---------+-------------
 100101 | Kehl | Thomas  | Kaiserstuhl
 100102 | Kehl | Thomas  | Eltville
*/
;

-- Beispiel: Kunden, die noch KEINEN Auftrag erteilt haben

select KndNr, Name, Vorname, Ort 
   from Kunde
   where KndNr not in (select KndNr from Auftrag where KndNr is not null);

/* ergibt:

 kndnr  |   name   | vorname |  ort   
--------+----------+---------+--------
 100105 | Riesling | Karin   | Colmar
*/
;

/* Diskussion: weshalb braucht man "is not null"

   Die Konstruktion x in (a1, a2, ..., an) bedeutet
   x = a1 or x = a2 or ... or x = an.
   Ist nun eines der ai null, so wird der Ausdruck doch wahr, wenn
   eines der anderen a denselben Wert wie x hat.
   
   Verneint man den Ausdruck, also x not in (a1, a2, ..., an)
   erhält man
   not (x = a1 or x = a2 or ... or x = an)
   Mit dem DeMorganschen Gesetz ist dies äquivalent zu
   (not (x = a1)) and (not (x = a2)) and ... (not (x = an)),
   also
   x <> a1 and x <> a2 and ... and x <> an
   Wenn jetzt eines der ai null ist, dann kann dieser Ausdruck niemals
   true werden, sondern ist selbst null! 
*/

select KndNr, Name, Vorname, Ort 
   from Kunde
   where KndNr not in (select KndNr from Auftrag);


/* In SQL kann man den Verbund durch geschachtelte Anweisungen ausdrücken
   und umgekehrt:
*/
;
-- Beispiel: Kunden, die Weißweine bestellt haben

/* Abfrage mit Verbund
   Wir verfolgen im Datenbankschema die Referenzen
   Kunde -- Auftrag -- AuftrPos -- Artikel
*/

select distinct KndNr, Name
  from Kunde join Auftrag using (KndNr)
    join AuftrPos using (AuftrNr)
    join Artikel using (ArtNr)
  where Farbe = 'weiß';


/* Abfrage mit geschachteltem SQL
   Wir bauen die Anweisung gewissermaßen von innen nach außen auf:
   1. Suche ArtNr der Weißweine in Artikel
   2. Suche AuftrNr der Auftragspositionen mit diesen Artikelnummern
   3. Suche KndNr der Aufträge mit diesen Auftragsnummern
   4. Gebe KndNr und Name der Kunden mit diesen Kundennummern aus
*/
 
select KndNr, Name from Kunde where KndNr in 
  (select KndNr from Auftrag where AuftrNr in 
    (select AuftrNr from AuftrPos where ArtNr in 
      (select ArtNr from Artikel where Farbe = 'weiß')));

/* beides ergibt:

 kndnr  | name 
--------+------
 100101 | Kehl
*/
;

/* Korrelierte geschachtelte Anweisung
   Von einer korrelierten geschachtelten Anweisung spricht man, wenn in der
   inneren Anweisung Angaben aus der äußeren Anweisung verwendet werden
   (ist ähnlich einer geschachtelten Schleife in der Programmierung)
*/
;

-- Beispiel: Ältester Jahrgang jeder Farbe
select * from Artikel;

select A.Bez, A.Weingut, A.Jahrgang, A.Farbe
  from Artikel A
  where A.Jahrgang =
    (select min(B.Jahrgang) from Artikel B where A.Farbe = B.Farbe);

/* In der inneren Anweisung wird A.Farbe der äußeren Anweisung
   verwendet.

   ergibt:

         bez         |  weingut  | jahrgang | farbe 
---------------------+-----------+----------+-------
 Les Châteaux        | Louis Max |     2002 | rot 
 Chablis             | Louis Max |     2005 | weiß
 Château Caraguilhes | Louis Max |     2005 | rosé
*/
;

/* In geschachtelten Anweisungen werden auch noch die
   Ausdrücke _exists_, _all_ und _any_ verwendet.
   Hierzu noch einige Beispiele:
*/

-- Alle Kunden, die einen Auftrag erteilt haben    

select * 
  from Kunde
  where exists (select * from Auftrag where Auftrag.KndNr = Kunde.KndNr);

/* ergibt:

 kndnr  | name | vorname |      str      |  plz  |     ort     
--------+------+---------+---------------+-------+-------------
 100101 | Kehl | Thomas  | Weinstr. 3    | 79675 | Kaiserstuhl
 100102 | Kehl | Thomas  | Im Riesling 3 | 68734 | Eltville

*/

-- Beispiel: Alle Kunden, die KEINEN Auftrag erteilt haben 

select * 
  from Kunde
  where not exists (select * from Auftrag where Auftrag.KndNr = Kunde.KndNr);

/* ergibt:

 kndnr  |   name   | vorname |        str         |   plz   |  ort   
--------+----------+---------+--------------------+---------+--------
 100105 | Riesling | Karin   | 67, Rue du Château | F-68567 | Colmar
*/
;

/* Vorsicht bei geschachtelten Anweisungen, die plötzlich
   korreliert werden:
   
   Die Anweisung [1] zählt die Zahl der Kunden von
   Auftrag 1002 und 1003, das sind natürlich 2
   
   Die Anweisung [2] hat einen Fehler: es gibt gar kein Attribut Name
   in Auftrag, aber in Kunde. Das bedeutet, dass in der inneren Anweisung
   der Name von Kunde genommen wird, d.h. das select lautet
   select 'Riesling' from ... z.B. und gibt also 'Riesling' zurück,
   d.h. das Ergebins ist 3, weil wir 3 Kunden haben.
*/;  

-- [1] 
select count(*)
	from Kunde
	where KndNr in (select KndNr from Auftrag where AuftrNr between 1002 and 1003);
	
-- [2]	
select count(*)
	from Kunde
	where Name in (select Name from Auftrag where AuftrNr between 1002 and 1003);
	
	
/* Für die weiteren Beispiel bauen wir uns eine Tabelle mit den
   Kunden und ihrem Gesamtumsatz:
*/


select Kunde.*, coalesce(sum(Preis * Anzahl), 0.00) as Umsatz 
  into Kunde_Umsatz
  from Kunde left outer join Auftrag using (KndNr)
             left outer join AuftrPos using (AuftrNr)
             left outer join Artikel using (ArtNr)
  group by KndNr;

select * from Kunde_Umsatz;

-- Beispiel: Kunde mit dem höchsten Umsatz
select * from Kunde_Umsatz
  where Umsatz >= all (select Umsatz from Kunde_Umsatz);
  -- Umsatz soll >= jeder Umsatz in Kunde_Umsatz sein, also der höchste

select * from Kunde_Umsatz
  where Umsatz = (select max(Umsatz) from Kunde_Umsatz);

-- die anderen Kunden
select * from Kunde_Umsatz
  where Umsatz < any (select Umsatz from Kunde_Umsatz);
  -- Umsatz soll < irgendein Umsatz, d.h. jeder, aber nicht der höchste

select * from Kunde_Umsatz
  where Umsatz <> (select max(Umsatz) from Kunde_Umsatz);

drop table Kunde_Umsatz;

