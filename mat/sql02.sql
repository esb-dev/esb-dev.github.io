/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 2
   Abfragen einer Tabelle

   $Id: sql02.sql 433 2019-04-12 07:02:57Z br $
   ----------------------------------------------------------------------- */

/* Wir verwenden die Tabelle _Artikel_ aus der Datenbank _Wein_ und probieren
   aus, welche Möglichkeiten wir mit SQL im Zugriff auf eine Tabelle haben.

   Zunächst machen wir uns vertraut, um welche Informationen es sich bei den
   Einträgen in der Tabelle _Artikel_ handelt:

   Die Tabelle _Artikel_ enthält die Weine, die ein Weinhändler anbietet: 
   Der Artikel mit der <ArtNr> trägt die Bezeichnung <Bez> und wird 
   produziert vom Weingut <Weingut>, er hat den Jahrgang <Jahrgang>, 
   die Farbe <Farbe> und kostet <Preis>.
*/
;

-- Wiedergabe einer Tabelle
-- Alle Angaben zu allen Artikeln der Tabelle Artikel
;

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/

/* Bemerkung: Verwendet man „*“ muss man sich auf die Anzahl, Bezeichnung und
   Reihenfolge der Attribute verlassen. 
   Also eignet sich dieses Konstrukt im Grunde nur für Ad-hoc-Abfragen.
*/
;

-- Projektion, d.h. Ausgabe bestimmter Spalten einer Tabelle

-- Die Angaben zur Artikelnummer, Bezeichnung und dem Weingut der Artikel:

select ArtNr, Bez, Weingut from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    
--------+---------------------+---------------
 100001 | Les Châteaux        | Louis Max
 100002 | Chablis             | Louis Max
 100003 | Château Caraguilhes | Louis Max
 604851 | Prosecco Val Monte  | Cave Bellenda
 145119 | Le Cop de Cazes     | Domaine Cazes
*/
;

-- Umbenennung der Spalten für das Ergebnis

select ArtNr as "ArtikelNr", Bez as "Bezeichnung", Weingut as "Produzent"
  from Artikel;

/* ergibt:

 ArtikelNr |     Bezeichnung     |   Produzent   
-----------+---------------------+---------------
    100001 | Les Châteaux        | Louis Max
    100002 | Chablis             | Louis Max
    100003 | Château Caraguilhes | Louis Max
    604851 | Prosecco Val Monte  | Cave Bellenda
    145119 | Le Cop de Cazes     | Domaine Cazes
*/
;

-- Projektion kann zu Duplikaten führen

select Weingut from Artikel;

/* ergibt - weil wir drei Weine von Louis Max haben:

    weingut    
---------------
 Louis Max
 Louis Max
 Louis Max
 Cave Bellenda
 Domaine Cazes
*/
;

-- Wir wollen aber nur wissen, welche Weingüter vorkommen:

select distinct Weingut from Artikel;

/* ergibt:

    weingut    
---------------
 Domaine Cazes
 Cave Bellenda
 Louis Max
*/
;

/* Bemerkung
   Manchmal möchte man nur eine Zeile zu einem bestimmten Attribut.  So
   möchte man vielleicht in unserer Tabelle Artikel einen Wein pro
   Weingut sehen, egal welchen. Dafür gibt es distinct on.  Als Ergebnis
   erhält man in unserer Datenbank drei Weine, von jedem Weingut eines; 
   welcher Wein von „Louis Max“ dies ist, ist zufällig.
*/
;

select distinct on (Weingut) * from Artikel;

/* ergibt:

 artnr  |        bez         |    weingut    | jahrgang | farbe | preis 
--------+--------------------+---------------+----------+-------+-------
 604851 | Prosecco Val Monte | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes    | Domaine Cazes |     2004 | rot   |  6.90
 100001 | Les Châteaux       | Louis Max     |     2002 | rot   | 17.90
*/
;

-- Ausgabe von Werten mit gleichzeitiger Berechnung und Umbenennung

-- Artikelnummer, Bezeichnung und Einzelpreis sowie 
-- Kartonpreis (12 zum Preis von 11) aller Weine

select ArtNr, Bez, Preis as "Einzelpreis", 11 * Preis as "Kartonpreis" from Artikel;

/* ergibt:

 artnr  |         bez         | Einzelpreis | Kartonpreis 
--------+---------------------+-------------+-------------
 100001 | Les Châteaux        |       17.90 |      196.90
 100002 | Chablis             |       15.50 |      170.50
 100003 | Château Caraguilhes |       14.90 |      163.90
 604851 | Prosecco Val Monte  |        7.60 |       83.60
 145119 | Le Cop de Cazes     |        6.90 |       75.90
*/
;

-- Der Operator case:

-- Ausgabe von Bezeichnung, Weingut und Jahrgang der Weine. 
-- Ein unbekannter Jahrgang soll als ’o.A.’ ausgegeben werden.

/* Bemerkung: 
   Weil 'o.A.' ein String ist, müssen wir die
   numerischen Werte in Jahrgang zu einem String-Typ umwandeln,
   dies geschieht mit cast
*/

select * from Artikel;

select Bez, Weingut, Jahrgang from Artikel;

select Bez, 
       Weingut,
       case
			    when Jahrgang is null then 'o.A.'
				  else cast(Jahrgang as text)
		  end as Jahrgang 
from Artikel;

/* ergibt:

         bez         |    weingut    | jahrgang 
---------------------+---------------+----------
 Les Châteaux        | Louis Max     | 2002
 Chablis             | Louis Max     | 2005
 Château Caraguilhes | Louis Max     | 2005
 Prosecco Val Monte  | Cave Bellenda | o.A.
 Le Cop de Cazes     | Domaine Cazes | 2004
*/
;

/* Bemerkung:
   Wenn es speziell um Null-Werte geht, kann man die
   Funktion coalesce verwenden, die das erste ihrer
   Argumente zurückgibt, das nicht NULL ist.
*/

select coalesce(null, null, null, 1, null, 2);  -- 1
select coalesce(null, null, null, 2, null, 1);  -- 2

select Bez, Weingut,
       coalesce(cast(Jahrgang as text), 'o.A.') as Jahrgang
			 from Artikel;

/* Zusammenfassung zur Projektion:

   select <gewünschte Felder> 
     from <Tabelle>

*/
;

-- Restriktion

/* Wir haben bisher immer alle Einträge in der Tabelle verwendet.
   Bei der Restriktion (auch Selektion in manchen Büchern genannt)
   wollen wir nur einen Teil der Zeilen ausgeben.

   Wir erreichen die Restriktion dadurch, dass wir eine Bedingung
   angeben:

   select <gewünschte Felder>
     from <Tabelle>
     where <Filterbedingung>
*/
;

-- Einfache Filterbedingung

-- Beispiel: Alle Angaben zu den Rotweinen

select * 
	from Artikel 
	where Farbe = 'rot';

/* ergibt:

 artnr  |       bez       |    weingut    | jahrgang | farbe | preis 
--------+-----------------+---------------+----------+-------+-------
 100001 | Les Châteaux    | Louis Max     |     2002 | rot   | 17.90
 145119 | Le Cop de Cazes | Domaine Cazes |     2004 | rot   |  6.90
*/
;

-- Filterbedingung mit not oder <>

-- Beispiel: Alle Angaben zu Weinen, die nicht rot sind
;
select * from Artikel where Farbe <> 'rot';
select * from Artikel where Farbe != 'rot';
select * from Artikel where not Farbe = 'rot';
select * from Artikel where not (Farbe = 'rot');

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
*/
;

-- Vergleiche in Bedingungen

-- Beispiel: Alle Weine, die weniger als 15 Euro kosten

select * from Artikel where Preis < 15.00;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

/* Wir haben die üblichen Vergleichsoperatoren in SQL:

   - gleich:         =
   - ungleich:       <> (Viele Systeme akzeptieren auch !=)
   - kleiner:        <
   - kleiner gleich: <=
   - größer:         >
   - größer gleich:  >=
*/
;

select 1 < 2;                -- true
select 'abc' < 'abd';        -- true
select 'abc' < 'ab';         -- false
select 'abc' = lower('ABC'); -- true
select false < true;         -- true
select false < null;         -- null
select false >= null;        -- null

;
-- Der Operator and

-- Beispiel: Alle Angaben zu Rotweinen, die weniger als 15 Euro kosten

select * from Artikel
  where Farbe = 'rot' and Preis < 15.00;

/* ergibt:

 artnr  |       bez       |    weingut    | jahrgang | farbe | preis 
--------+-----------------+---------------+----------+-------+-------
 145119 | Le Cop de Cazes | Domaine Cazes |     2004 | rot   |  6.90
*/
;

-- Der Operator or

-- Beispiel: Alle Angaben zu Weinen, die rot oder günstiger als 15 Euro sind.

select * from Artikel
  where Farbe = 'rot' or Preis < 15.00;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

/* Bemerkungen:
   Die Operatoren _and_ und _or_ sind kommutativ. 

   Der Operator _not_ bindet am stärksten, dann _and_ und schließlich _or_. 
   Am besten, man klammert die Operatoren _and_ und _or_ auf jeden Fall, 
   damit keine Unklarheiten auftreten können. 

   Vorsicht ist geboten, wenn man Funktionen in logischen Ausdrücken verwendet: 
   es ist nicht garantiert, dass bei der Auswertung des Ausdrucks alle 
   Funktionen wirklich ausgeführt werden.
*/
;

-- Beispiel: Alle Angaben zu Weißweinen oder günstigen Rotweinen

select * from Artikel
  where Farbe = 'weiß' or Farbe = 'rot' and Preis < 15.00;

/* ergibt:

 artnr  |        bez         |    weingut    | jahrgang | farbe | preis
 -------+--------------------+---------------+----------+-------+-------
 100002 | Chablis            | Louis Max     |     2005 | weiß  | 15.50
 604851 | Prosecco Val Monte | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes    | Domaine Cazes |     2004 | rot   |  6.90

*/
;

select * from Artikel
  where Farbe = 'weiß' or (Farbe = 'rot' and Preis < 15.00);

-- aber

select * from Artikel
  where (Farbe = 'weiß' or Farbe = 'rot') and Preis < 15.00;

/* ergibt:

 artnr  |        bez         |    weingut    | jahrgang | farbe | preis
--------+--------------------+---------------+----------+-------+-------
 604851 | Prosecco Val Monte | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes    | Domaine Cazes |     2004 | rot   |  6.90

*/
;

-- Tupelvergleiche

-- Beispiel: Alle Rotweine des Weinguts 'Louis Max'

select * from Artikel
  where Weingut = 'Louis Max' and Farbe = 'rot';

-- schöner mit Tupelvergleich:

select * from Artikel
  where (Weingut, Farbe) = ('Louis Max', 'rot');

/* ergibt:

 artnr  |     bez      |  weingut  | jahrgang | farbe | preis 
--------+--------------+-----------+----------+-------+-------
 100001 | Les Châteaux | Louis Max |     2002 | rot   | 17.90
*/
;

/* Bemerkung:
   In SQL kann man Tupelvergleiche auch mit anderen Vergleichsoperatoren
   als = machen, die lexikographisch ausgewertet werden. 
   Dies kann verwirrend sein, deshalb rate ich davon ab.
*/
;

-- Der Operator between ... and

-- Beispiel: Alle Angaben zu den Weinen aus den Jahrgängen 2004 - 2006

select * from Artikel
	where Jahrgang >= 2004 and Jahrgang <= 2006;
	
select * from Artikel
  where Jahrgang between 2004 and 2006;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

-- Der Operator in

-- Beispiel: Alle Angaben zu den Weinen von 'Louis Max' und 'Domaine Cazes'

select * from Artikel
  where Weingut = 'Louis Max' or Weingut = 'Domaine Cazes';

-- schöner:

select * from Artikel
  where Weingut in ('Louis Max', 'Domaine Cazes');

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

/* Bemerkung:
   Der Operator in spielt eine wichtige Rolle bei geschachtelten
   SQL-Anweisungen, die wir später kennenlernen werden.

   Wir beobachten schon mal hier:
   Hinter _in_ kommt selbst eine Tabelle, nämlich eine mit genau einer Spalte,
   also eine Liste von Werten --
   das werden wir später brauchen!
*/
;

-- Die Operatoren like und similar to

/* Der Operator _like_ erlaubt die Verwendung von "Wildcards"
   und _similar to_ kann einfache reguläre Ausdrücke auswerten
*/;

-- Beispiel:  Alle Weine, deren Bezeichnung die Zeichenfolge 'Château' enthält

select *
  from Artikel
  where Bez like '%Château%';

/* ergibt:
 artnr  |         bez         |  weingut  | jahrgang | farbe | preis 
--------+---------------------+-----------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max |     2002 | rot   | 17.90
 100003 | Château Caraguilhes | Louis Max |     2005 | rosé  | 14.90
*/;
  
-- Beispiel: Alle Weine, deren Bezeichnung mit der Zeichenfolge 'Château' beginnt

select *
  from Artikel
  where Bez like 'Château%';

/* ergibt:

 artnr  |         bez         |  weingut  | jahrgang | farbe | preis 
--------+---------------------+-----------+----------+-------+-------
 100003 | Château Caraguilhes | Louis Max |     2005 | rosé  | 14.90
*/;
  
-- Beispiel: Alle Weine, deren Bezeichnung als zweiten Buchstaben ein 'e' hat

select *
  from Artikel
  where Bez like '_e%';

/* ergibt:

 artnr  |       bez       |    weingut    | jahrgang | farbe | preis 
--------+-----------------+---------------+----------+-------+-------
 100001 | Les Châteaux    | Louis Max     |     2002 | rot   | 17.90
 145119 | Le Cop de Cazes | Domaine Cazes |     2004 | rot   |  6.90
*/;

/* Wildcards in SQL: 
   
   _ steht für ein einzelnes Zeichen,
   % steht für eine beliebige Zeichenfolge

   will man in einem Ausdruck mit 'like' nach einem der Zeichen % oder _ selbst
   suchen, es also aus wildcard ausschalten, muss man \ davor setzen
   (kann DBMS-spezifisch eingestellt werden)
*/
;

-- Es gibt auch einfache reguläre Ausdrücke mit dem Operator _similar to_

-- Beispiel: Alle Weine, die mit 'L' oder 'P' anfangen

select * 
  from Artikel
  where Bez similar to '(L|P)%';
  
select * from Artikel
  where bez like 'L%' or bez like 'P%';

/* ergibt:

 artnr  |        bez         |    weingut    | jahrgang | farbe | preis 
--------+--------------------+---------------+----------+-------+-------
 100001 | Les Châteaux       | Louis Max     |     2002 | rot   | 17.90
 604851 | Prosecco Val Monte | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes    | Domaine Cazes |     2004 | rot   |  6.90
*/
;

-- Sortierung

-- Beispiel aufsteigende Sortierung: Alle Weine mit Preis, der günstigste zuerst

select * from Artikel
  order by Preis;

select * from Artikel
  order by Preis asc;  -- asc = ascending

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
*/
;
  
-- Beispiel: Alle Rotweine nach Preis sortiert

select *
  from Artikel
  where Farbe = 'rot'
  order by Preis;

/* Wir sehen: order by kommt in der Anweisung an der letzten Stelle
*/

/* ergibt:

 artnr  |       bez       |    weingut    | jahrgang | farbe | preis 
--------+-----------------+---------------+----------+-------+-------
 145119 | Le Cop de Cazes | Domaine Cazes |     2004 | rot   |  6.90
 100001 | Les Châteaux    | Louis Max     |     2002 | rot   | 17.90
*/
;

-- Beispiel: Lexikographische Sortierung nach mehreren Kriterien:

select *
  from Artikel
  order by Weingut, Preis;  

/* ergibt:
 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
*/
;
  
-- Beispiel absteigender Sortierung: Alle Weine mit Preis, der teuerste zuerst

select *
  from Artikel
  order by Preis desc; -- desc = descending

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

-- Aufsteigende und absteigende Sortierung kann man auch kombinieren:
-- Alle Weine sortiert nach Weingut (aufsteigend) und Preis (absteigend)

select *
  from Artikel
  order by Weingut asc, Preis desc;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
*/
;

/* Zusammenfassung:

   Wir haben gesehen:
   
   - Projektion: wie man Werte aus bestimmten Spalten einer Tabelle ausgibt
   - erweiterte Projektion: wie man dabei auch Berechnungen machen kann
   - Restriktion: wie man die Zeilen einschränkt, die ausgegeben werden
     Dazu haben wir viele Operatoren kennengelernt, die man in
     Filterbedingungen verwenden kann
   - Sortierung: zuletzt haben wir die Ergebnistabelle mit _order by_ sortiert

   
   Eine SQL-Anweisung ist jetzt so aufgebaut:

   select <Struktur des gewünschten Ergebnisses>
     from <beteiligte Tabelle>
     where <Filterbedingung>
     order by <Sortierattribute>

*/
