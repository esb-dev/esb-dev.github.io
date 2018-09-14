/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 4
   Abfragen mehrerer Tabellen -- Verbund

	 $Id: sql04.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */

/* Bisher haben wir untersucht, wie man mit SQL Informationen aus einer
   Tabelle abfragen kann.

   Nun wenden wir uns dem Thema zu, wie man mehrere Tabellen und ihre 
   Beziehungen in SQL verwenden kann. In diesem Abschnitt beschäftigen wir
   uns mit dem Verbund (englisch: Join)
*/

/* Wie sieht unsere Datenbank "Wein" aus?

   Die Tabelle _Artikel_ enthält die Weine, die ein Weinhändler anbietet: 
   Der Artikel mit der <ArtNr> trägt die Bezeichnung <Bez> und wird 
   produziert vom Weingut <Weingut>, er hat den Jahrgang <Jahrgang>, 
   die Farbe <Farbe> und kostet <Preis>.

   Die Tabelle _Lieferant_ verzeichnet Firmen, die Weine liefern: 
   Der Lieferant mit der Lieferantennummer <LftNr> hat den 
   Namen <Firma>  und als Adresse <Postfach>, <PLZ>, <Ort>.

   Der Weinhändler bezieht seine Artikel nicht direkt bei Weingütern, 
   sondern bei den Lieferanten. Ein Lieferant kann verschiedene Weine 
   liefern. Diese Lieferbeziehung ist in der Tabelle _LieferBez_ verzeichnet: 
   Der Lieferant mit der Lieferantennummer <LftNr> liefert 
   den Wein mit der Artikelnummer <ArtNr>.

   Die Tabelle _Kunde_ verzeichnet die Kunden des Weinhändlers: 
   Der Kunde mit der Kundennummer <KndNr> heißt <Name>, <Vorname> und 
   wohnt in <Str>, <PLZ> <Ort>.

   Die Tabelle _Auftrag_ enthält Aufträge der Kunden: 
   Der Auftrag mit der Auftragsnummer <AuftrNr> wird vom Kunden mit 
   der Kundennummer <KndNr> am <Datum> erteilt.

   Aufträge haben Auftragspositionen, die in der Tabelle _AuftrPos_ 
   verzeichnet sind: Der Auftrag <AuftrNr> hat eine Position, in der 
   die <Anzahl> von dem  Artikel mit der Artikelnummer <ArtNr> bestellt 
   wird.
*/

select * from Artikel;
select * from Lieferant;
select * from LieferBez;
select * from Kunde;
select * from Auftrag;
select * from AuftrPos;

/* Bemerkung:
   Die Tabelle Auftrag hat einen Eintrag, in der die Kundennummer NULL ist.
   Das wird in einem realistischen Szenario nicht der Fall sein und lässt 
   sich auch leicht verhindern (wodurch?). 
   In der Beispieldatenbank kommt aber ein solcher unvollständiger Auftrag vor, 
   weil wir an ihm zeigen können, wie man einen äußeren Verbund in SQL 
   formuliert.
*/

/* Zwischen den Tabellen in der Datenbank "Wein" bestehen Beziehungen, die
   man schematisch so darstellen kann:

   Kunde             Lieferant
     ^                  ^
     |                  |
   Auftrag           Lieferbez
     ^                  |
     |                  v
   AuftrPos   -->    Artikel  

   <KndNr> in _Auftrag_ gibt an, welcher Kunde den Auftrag erteilt hat.
   <AuftrNr> in _AuftrPos_ gibt an, zu welchem Auftrag die Auftragsposition
      gehört.
   <ArtNr> in _AuftrPos_ gibt an, welcher Artikel in dieser Auftragsposition
      bestellt wird.
   <LftNr> und <ArtNr> in _LieferBez_ geben an, welcher Artikel von welchem
      Lieferanten geliefert werden. 
*/      

      
-- Das kartesische Produkt

-- Beispiel: Alle Kombinationen von Kunden mit Aufträgen, unabhängig davon,
-- ob der Kunde den Auftrag gestellt hat

select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum, Auftrag.KndNr
  from Kunde cross join Auftrag;

/* ergibt: 

 kndnr  |   name   | auftrnr |   datum    | kndnr  
--------+----------+---------+------------+--------
 100101 | Kehl     |    1003 | 2007-03-01 | 100101
 100102 | Kehl     |    1003 | 2007-03-01 | 100101
 100105 | Riesling |    1003 | 2007-03-01 | 100101
 100101 | Kehl     |    1001 | 2006-10-12 | 100101
 100102 | Kehl     |    1001 | 2006-10-12 | 100101
 100105 | Riesling |    1001 | 2006-10-12 | 100101
 100101 | Kehl     |    1002 | 2006-02-12 | 100102
 100102 | Kehl     |    1002 | 2006-02-12 | 100102
 100105 | Riesling |    1002 | 2006-02-12 | 100102
 100101 | Kehl     |    1004 | 2006-02-12 |       
 100102 | Kehl     |    1004 | 2006-02-12 |       
 100105 | Riesling |    1004 | 2006-02-12 |       
(12 rows)

   Das Ergebnis hat 12 Zeilen: warum?
*/
  

select KndNr, Name from Kunde;

select AuftrNr, Datum, KndNr from Auftrag; 


-- Variante SQL 89
    
select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum, Auftrag.KndNr
  from Kunde, Auftrag;  

/*
   In aller Regel ist das kartesische Produkt nicht das, was wir wirklich wissen
   wollen!
*/

-- Der (innere) Verbund (Join)

-- Beispiel: Kombinationen Kunde - Auftrag, bei denen der Kunde den Auftrag auch wirklich
-- gestellt hat

select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum -- , Auftrag.KndNr
  from Kunde join Auftrag on  Kunde.KndNr = Auftrag.KndNr;

/* ergibt:

 kndnr  | name | auftrnr |   datum    
--------+------+---------+------------
 100101 | Kehl |    1003 | 2007-03-01
 100101 | Kehl |    1001 | 2006-10-12
 100102 | Kehl |    1002 | 2006-02-12

 Wir beachten, dass in der dritten Zeile ein anderer Kunde vorkommt als in
 den beiden ersten Zeilen, die <KndNr> ist verschieden.
*/


-- Variante mit using, wenn die verbindenden Attribute in beiden Tabelle gleich heißen  

select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum
  from Kunde join Auftrag using (KndNr);

-- Variante natural join, wenn nur die verbindenden Attribute gleich heißen

select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum
  from Kunde natural join Auftrag;

-- Variante SQL 89 -- wir schieben den Verbund in die Filterbedingung  

select Kunde.KndNr, Kunde.Name, Auftrag.AuftrNr, Auftrag.Datum
  from Kunde, Auftrag
  where Kunde.KndNr = Auftrag.KndNr;  

/* Durch das Konstrukt Tabelle1 join Tabelle2 ....
   entsteht eine Tabelle, die wir an der Stelle in der
   Anweisung einsetzen, an der eine Tabelle erwartet wird.
   D.h. wir können alles, was wir im vorherigen Abschnitt
   gelernt haben auch mit dem Verbund anwenden
*/

-- Verbund mit Filterbedingung
-- Beispiel: Welche Weine gehören zum Auftrag mit der AuftrNr 1003

select ArtNr, Bez, Weingut, Jahrgang
  from AuftrPos join Artikel using (ArtNr)
  where AuftrNr = 1003;

/* ergibt:

 artnr  |         bez         |  weingut  | jahrgang 
--------+---------------------+-----------+----------
 100001 | Les Châteaux        | Louis Max |     2002
 100002 | Chablis             | Louis Max |     2005
 100003 | Château Caraguilhes | Louis Max |     2005
*/

-- Variante SQL 89:

select ArtNr, Bez, Weingut, Jahrgang
  from AuftrPos, Artikel 
  where AuftrPos.ArtNr = Artikel.ArtNr
  and AuftrNr = 1003;

/* ergibt:

ERROR:  column reference "artnr" is ambiguous
LINE 1: select ArtNr, Bez, Weingut, Jahrgang
               ^

Warum? Was muss man an der Anweisung ändern?
*/


-- Der Verbund mehrerer Tabellen

-- Beispiel: KndNr, AuftrNr und Angaben zu den bestellten Weinen von Auftrag 1001


select KndNr, AuftrNr, Bez, Weingut, Jahrgang
  from Auftrag join AuftrPos using (AuftrNr)
    join Artikel using (ArtNr)
  where AuftrNr = 1001
  order by ArtNr; 

/* ergibt:

 kndnr  | auftrnr |         bez         |    weingut    | jahrgang 
--------+---------+---------------------+---------------+----------
 100101 |    1001 | Les Châteaux        | Louis Max     |     2002
 100101 |    1001 | Chablis             | Louis Max     |     2005
 100101 |    1001 | Château Caraguilhes | Louis Max     |     2005
 100101 |    1001 | Le Cop de Cazes     | Domaine Cazes |     2004
*/

/* Wie findet man die Attribute, die man für den Verbund verwenden
   muss?
   
   Aus der Darstellung des Schemas im Datenstruktur-Diagramm sieht
   man die Verbindungen
*/


-- Beispiel: Name des Kunden und seine Weine zum Auftrag 1001

select Name, Vorname, KndNr, AuftrNr, Anzahl, Bez
  from Kunde join Auftrag using (KndNr)
             join AuftrPos using (AuftrNr)
             join Artikel using (ArtNr)
    where AuftrNr = 1001
    order by Bez; 

/* ergibt:

 name | vorname | kndnr  | auftrnr | anzahl |         bez         
------+---------+--------+---------+--------+---------------------
 Kehl | Thomas  | 100101 |    1001 |      1 | Chablis
 Kehl | Thomas  | 100101 |    1001 |      1 | Château Caraguilhes
 Kehl | Thomas  | 100101 |    1001 |      1 | Le Cop de Cazes
 Kehl | Thomas  | 100101 |    1001 |      1 | Les Châteaux
*/    

-- kürzer geht auch    
select Name, Vorname, KndNr, AuftrNr, Anzahl, Bez
  from Kunde natural join Auftrag
             natural join AuftrPos
             natural join Artikel
    where AuftrNr = 1001
    order by Bez;     

/* Man muss aber den natürlichen Verbund ("natural join") mit
   Vorsicht einsetzen. Bei natürlichen Verbund werden alle Attribute
   identifiziert, die gleich heißen -- es kann aber vorkommen, dass
   Attribute gleich heißen, aber in der Beziehung der Tabellen gar keine
   Rolle spielen.

   In SQL-Anweisungen in Anwendungen sollte man deshalb immer die
   Version mit "using ..." oder "on ..." verwenden.
*/

-- Beispiel: Kundennummer und Name, Vorname der Kunden, die einen Weißwein bestellt haben

select distinct KndNr, Name, Vorname
  from Kunde join Auftrag using (KndNr)
             join AuftrPos using (AuftrNr)
             join Artikel using (ArtNr)
  where Farbe = 'weiß'; 

/* ergibt:

 kndnr  | name | vorname 
--------+------+---------
 100101 | Kehl | Thomas
*/          

-- Verbund mit ein und derselben Tabelle ("selfjoin")

-- Beispiel: Gibt es zwei Kunden mit demselben Nachnamen und Vornamen, 
--           aber verschiedenen Adressen

select A.Name, A.Vorname, A.Str, A.PLZ, A.Ort
  from Kunde A, Kunde B
  where A.Name = B. Name and A.Vorname = B.Vorname
    and not (A.Str = B.Str and A.PLZ = B.PLZ and A.Ort = B.Ort);

/* ergibt:

 name | vorname |      str      |  plz  |     ort     
------+---------+---------------+-------+-------------
 Kehl | Thomas  | Weinstr. 3    | 79675 | Kaiserstuhl
 Kehl | Thomas  | Im Riesling 3 | 68734 | Eltville
*/

/* Damit wir einen Verbund mit ein und derselben Tabelle machen können,
   müssen wir eine Tupelvariable A für die Tabelle Kunde und eine
   weitere Tupelvariable B für die Tabelle definieren.

   (SQL verwendet immer eine Tupelvariable, die gleich heißt wie
   die Tabelle, es sei denn man gibt die Bezeichnung der Tupelvariablen
   explizit an. D.h. intern wird aus "select * from Kunde" die Anweisung
   "select * from Kunde Kunde" wobei das erste "Kunde" der Name der Tabelle
   und das zweite "Kunde" der Name der Tupelvariablen ist.)
*/ 

-- Variante mit Tupelvergleich  (ist schöner)    

select A.Name, A.Vorname, A.Str, A.PLZ, A.Ort
  from Kunde A cross join Kunde B
  where (A.Name, A. Vorname) = (B. Name, B.Vorname)
    and (A.Str, A.PLZ, A.Ort) <> (B.Str, B.PLZ, B.Ort); 

-- Gruppierung und Verbund

-- Beispiel: Statistik der verkauften Flaschen pro Farbe des Weins

select Farbe, sum(Anzahl) as "Zahl Flaschen"
  from AuftrPos join Artikel using (ArtNr)
  group by Farbe;

/* ergibt:

 farbe | Zahl Flaschen 
-------+---------------
 rosé  |            61
 rot   |            14
 weiß  |            13
*/

-- Beispiel: Aufträge mit mehr als 10 Rotweinen

select AuftrNr, Anzahl as "ZahlRotweine"
  from AuftrPos join Artikel using (ArtNr)
  where Farbe = 'rot';

/* ergibt:

 auftrnr | ZahlRotweine 
---------+--------------
    1003 |           12
    1001 |            1
    1001 |            1
*/

select AuftrNr, sum(Anzahl) as "ZahlRotweine"
  from AuftrPos join Artikel using (ArtNr)
  where Farbe = 'rot'
  group by AuftrNr;

/* ergibt:

 auftrnr | ZahlRotweine 
---------+--------------
    1003 |           12
    1001 |            2
*/

select AuftrNr, sum(Anzahl) as "ZahlRotweine"
  from AuftrPos join Artikel using (ArtNr)
  where Farbe = 'rot'
  group by AuftrNr
  having sum(Anzahl) > 10;

/* ergibt: 

 auftrnr | ZahlRotweine 
---------+--------------
    1003 |           12
*/

-- Beispiel: Warenwert der Aufträge sortiert nach Gesamtpreis (absteigend)

select AuftrNr, sum(Anzahl * Preis) as "Gesamtpreis"
  from AuftrPos join Artikel using (ArtNr)
  group by AuftrNr
  order by 2 desc; 

/* ergibt:

 auftrnr | Gesamtpreis 
---------+-------------
    1002 |      715.20
    1003 |      579.60
    1001 |       55.20
*/


-- Beispiel: Umsatz pro Kunde

select KndNr, Name, sum(Anzahl * Preis) as "Gesamtumsatz"
  from Kunde join Auftrag using (KndNr)
             join AuftrPos using (AuftrNr)
             join Artikel using (ArtNr)
  group by KndNr, Name;

/* ergibt:

 kndnr  | name | Gesamtumsatz 
--------+------+--------------
 100101 | Kehl |       634.80
 100102 | Kehl |       715.20


   Aber wir haben noch eine weitere Kundin, die bisher noch
   keinen Umsatz gemacht hat. Wir wollen, dass sie auch im
   Ergebnis (mit Umsatz 0.00) erscheint.

   Dies ist ein Fall, wo wir fehlende Information (die Kundin
   hat keinen Auftrag erteilt bisher) berücksichtigen müssen.

   Dazu verwendet man den sogenannten äußeren Verbund, den
   wir im folgenden Abschnitt kennenlernen werden:
*/
   
       
select KndNr, Name, (coalesce(sum(Anzahl * Preis), 0.00)) as "Gesamtumsatz"
  from Kunde left outer join Auftrag using (KndNr)
    left outer join AuftrPos using (AuftrNr)
    left outer join Artikel using (ArtNr)
   group by KndNr, Name;  

/* ergibt das Gewünschte:

 kndnr  |   name   | Gesamtumsatz 
--------+----------+--------------
 100105 | Riesling |         0.00
 100101 | Kehl     |       634.80
 100102 | Kehl     |       715.20
*/ 

