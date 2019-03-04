/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 3
   Aggregatfunktionen und Gruppierung mit einer Tabelle

	 $Id: sql03.sql 360 2019-03-04 08:26:31Z br $
   ----------------------------------------------------------------------- */

-- Aggregationen und Aggregatfunktionen

/* Es kommt häufig vor, dass man nicht Informationen über einzelne
   Datensätze haben möchte, sondern Informationen, die die ganze Tabelle
   oder Gruppen von Datensätzen in der Tabelle betreffen.
   Man spricht dann von der Aggregation von Daten.

   Wir betrachten zunächst die wichtigsten Aggregatfunktionen in SQL:

   - Anzahl:       count
   - Summe:        sum
   - Minimum:      min
   - Maximum:      max
   - Durchschnitt: avg 
*/

-- Aggregatfunktion count

-- Beispiel: Anzahl der Artikel zählen

select * from Artikel;

select count(*)
  from Artikel;
  
select count(*) as Anzahl
  from Artikel;

/* ergibt:

 anzahl 
--------
      5
*/

-- Beispiel: Anzahl mit distinct

select Weingut
  from Artikel;

select count(Weingut) as "Anzahl Weingüter"
  from Artikel;

/* ergibt:

 Anzahl Weingüter 
------------------
                5

Tatsächlich sind es aber nur 3 Weingüter,
wie kriegen wir die Duplikate weg?
*/
;

select distinct Weingut
  from Artikel;

-- also:
;
  
select count(distinct Weingut) as "Anzahl Weingüter"
  from Artikel;  

/* ergibt:

 Anzahl Weingüter 
------------------
                3
*/
;

-- was passiert bei der folgenden Anweisung?

select distinct count(Weingut)
  from Artikel;

-- warum ist das Ergebnis 5?
;

-- Aggregatfunktion sum

-- Beispiel: Summe der Preise der drei Artikel von Louis Max
;

select Preis
  from Artikel
  where Weingut = 'Louis Max';
  
select sum(Preis) as "Preis Combo"
  from Artikel
  where Weingut = 'Louis Max';

/* ergibt:

 Preis Combo 
-------------
       48.30
*/
;
  
-- angenommen man bekommt 10% Rabatt auf die Kombination der drei Weine
  
select sum(Preis * 0.9) as "Combo-Preis mit Rabatt"
  from Artikel
  where Weingut = 'Louis Max';

select sum(Preis) * 0.9 as "Combo-Preis mit Rabatt"
  from Artikel
  where Weingut = 'Louis Max';

-- Aggregatfunktion avg

-- Beispiel: Durchschnittlicher Preis einer Flasche unserer Weine

select avg(Preis) as "durchschnittl. Preis"
  from Artikel;

/* ergibt (je nach Abfragewerkzeug):

 durchschnittl. Preis 
----------------------
  12.5600000000000000
*/
;

select round(avg(Preis), 2) as "durchschnittl. Preis"
  from Artikel;

/* ergibt:

 durchschnittl. Preis 
----------------------
                12.56
*/
;

-- Aggregatfunktion min
-- Beispiel: Angabe des frühesten Jahrgangs von Weinen im Angebot

select min(Jahrgang) as "frühester Jahrgang"
  from Artikel;

/* ergibt: 

 frühester Jahrgang 
--------------------
               2002
*/
;

-- Aggregatfunktion max
-- Beispiel: Ausgabe des höchsten Preises der Artikel

select max(Preis) as "höchster Preis"
  from Artikel;

/* ergibt:

 höchster Preis 
----------------
          17.90
*/
;

-- was, wenn wir auch die Bezeichnung des teuersten Artikels sehen wollen?

select Bez, max(Preis) as "höchster Preis"
  from Artikel;
-- gibt Fehler, warum?
;

select Bez "Name des Weins", Preis as "höchster Preis"
  from Artikel
  where Preis = (select max(Preis) from Artikel); 

/* ergibt:

     bez      | preis 
--------------+-------
 Les Châteaux | 17.90
*/   
;

-- besser nicht so:
select Bez, Preis
  from Artikel
  where Preis = max(Preis);  

/* ergibt:
   Error: aggregate functions are not allowed in WHERE
*/ 
;

-- Gruppierung

/* Wir haben bisher aggregierte Werte für eine ganze Tabelle betrachtet,
   oft aber möchte man solche Werte für Gruppen von Datensätzen
   ermitteln.
   Dazu gibt es die Gruppierung mit _group by_.
*/
;

-- Beispiel: Zahl der Weine pro Farbe

/* Angenommen wir möchten wissen, wieviele Weine je Farbe in der
   Tabelle Artikel verzeichnet sind.

   Wir möchten also eine Ergebnistabelle, die so aussieht:

    farbe | anzahl 
   -------+--------
    rot   |      2
    weiß  |      2
    rosé  |      1
*/
;

-- zunächst betrachten wir uns die Werte Farbe und ArtNr sortiert nach Farbe:

select Farbe, ArtNr
  from Artikel
  order by Farbe;

/* ergibt:

 farbe | artnr  
-------+--------
 rosé  | 100003
 rot   | 100001
 rot   | 145119
 weiß  | 100002
 weiß  | 604851
*/
;

-- nun sortieren wir nicht mehr
-- sondern wir gruppieren und zählen die ArtNr pro Gruppe

select Farbe, count(ArtNr) as Anzahl
  from Artikel
  group by Farbe
  order by Farbe;

/* ergibt:

 farbe | anzahl 
-------+--------
 rosé  |      1
 rot   |      2
 weiß  |      2
*/
;

-- Beispiel: Zahl der Weine pro Jahrgang

select Jahrgang, ArtNr
	from Artikel
	order by Jahrgang;

-- wird transformiert in:
	
select Jahrgang, count(*) as Anzahl
  from Artikel
  group by Jahrgang;  

/* ergibt:

 jahrgang | anzahl 
----------+--------
          |      1
     2005 |      2
     2002 |      1
     2004 |      1
*/
;

/* Vorsicht wenn Null-Werte vorkommen:
*/

select Jahrgang, count(Jahrgang) as Anzahl
  from Artikel
  group by Jahrgang;

/* ergibt:

 jahrgang | anzahl 
----------+--------
          |      0
     2005 |      2
     2002 |      1
     2004 |      1
*/

-- warum kommt hier etwas anderes raus als bei der vorherigen Anweisung?
;

-- besser ist folgende Anweisung, weil ArtNr Primärschlüssel der Tabelle ist

select Jahrgang, count(ArtNr) as Anzahl
  from Artikel
  group by Jahrgang;

/* ergibt:

 jahrgang | anzahl 
----------+--------
          |      1
     2005 |      2
     2002 |      1
     2004 |      1
*/
;

-- Wie kann man die Ausgabe des unbekannten Jahrgangs verschönern?

select coalesce(text(Jahrgang), 'ohne Angabe') as Jahrgang, count(ArtNr) as Anzahl
  from Artikel
  group by Jahrgang;

/* ergibt:

  jahrgang   | anzahl 
-------------+--------
 ohne Angabe |      1
 2005        |      2
 2002        |      1
 2004        |      1
*/
;

-- Beispiel: durchschnittlicher Preis je Farbe

select Farbe, Preis from Artikel
  order by Farbe;

-- und nun gruppieren:

select Farbe, round(avg(Preis), 2) as "Durchschnittspreis"
  from Artikel
  group by Farbe;

/* ergibt:

 farbe | Durchschnittspreis 
-------+--------------------
 rosé  |              14.90
 rot   |              12.40
 weiß  |              11.55
*/
;

/* Manchmal möchte man nicht alle Gruppen betrachten,
   sondern nur solche, wo eine bestimmte Bedingung
   für die Gruppe erfüllt ist.
   Dazu gibt es group by ... having ...
*/
;   

-- Beispiel: Alle Farben von Weinen, wo in der Gruppe der
-- jeweiligen Farbe der Durchschnittspreis > 12.00 Euro ist

-- wir starten mit der vorherigen Anweisung

select Farbe, round(avg(Preis), 2) as "Durchschnittspreis"
  from Artikel
  group by Farbe;

-- Die Gruppe der weißen Weine sollte nicht vorkommen, da
-- ihr Durchschnittspreis nicht über 12 Euro ist --
-- dazu formulieren wir eine Bedingung an die Gruppe

select Farbe, avg(Preis)
  from Artikel
  group by Farbe
  having avg(Preis) > 12.00;

/* ergibt:

 farbe 
-------
 rosé
 rot 
*/
;

/* Zusammenfassung:
   
   Wir haben gesehen, wie man Werte für eine gesamte Tabelle oder
   Gruppen von Datensätzen erhält durch
   
   - Aggregatfunktionen count, max, min, avg, sum
   - Gruppierung mit group by ... having ...

   Eine SQL-Anweisung ist jetzt so aufgebaut:

   select <Struktur des gewünschten Ergebnisses>
     from <beteiligte Tabelle>
     where <Filterbedingung>
     group by <Gruppierungsattribute>
     having <Bedingung für Gruppen>
     order by <Sortierattribute>

*/
;

/* Zum Abschluss dieses Abschnitts wollen wir einen kurzen
   Blick auf die Fähigkeiten von SQL in Bezug auf
   Rangabfragen werfen.

   Das folgende Beispiel ist nur ein Hinweis darauf, dass
   SQL mächtige Funktionen hat, die weit über die bisher
   diskutierte Gruppierung hinaus gehen.

   Zunächst kopieren und erweitern wir die Tabelle Artikel
   um eine Spalte Bewertung und geben Bewertungen ein.
*/
;

-- Wir kopieren die Tabelle Artikel in Artikel 2
select * into Artikel2 from Artikel;

select * from Artikel2;

-- Wir fügen eine Spalte Bewertung hinzu
alter table Artikel2 add column bewertung int;

select * from Artikel2;

-- Wir geben Bewertungen ein
update Artikel2 set bewertung = 5 where ArtNr = 100001;
update Artikel2 set bewertung = 4 where ArtNr = 100002;
update Artikel2 set bewertung = 3 where ArtNr = 100003;
update Artikel2 set bewertung = 4 where ArtNr = 604851;
update Artikel2 set bewertung = 3 where ArtNr = 145119;

select * from Artikel2;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis | bewertung 
--------+---------------------+---------------+----------+-------+-------+-----------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90 |         5
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50 |         4
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90 |         3
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60 |         4
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90 |         3
*/
;

-- Beispiel: Rangliste der Weine nach Bewertung

select ArtNr, Bez, Bewertung,
       rank() over (order by Bewertung desc) as Rang
  from Artikel2;

/* ergibt:

 artnr  |         bez         | bewertung | rang 
--------+---------------------+-----------+------
 100001 | Les Châteaux        |         5 |    1
 100002 | Chablis             |         4 |    2
 604851 | Prosecco Val Monte  |         4 |    2
 100003 | Château Caraguilhes |         3 |    4
 145119 | Le Cop de Cazes     |         3 |    4

Die Weine mit gleicher Bewertung werden in denselben Rang
eingeordnet.
*/
;

/* Wer mehr über solche Möglichkeiten von SQL erfahren möchte,
   kann in Kapitel 3.5 "Window Functions" der Dokumentation
   von PostgreSQL nachlesen.
   https://www.postgresql.org/docs/11/tutorial-window.html
*/

-- Löschen der Tabelle Artikel2
drop table Artikel2;

