/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 1
   SQL als Taschenrechner

	$Id: sql01.sql 432 2019-04-12 06:55:57Z br $
   ----------------------------------------------------------------------- */


/* Google oder Wolfram Alpha kann man als Taschenrechner
   verwenden. 

   Gibt man in Google z.B. 2 * 21 ein, dann erscheint ein
   Taschenrechner, der das Ergebnis 42 anzeigt

   In Wolfram Alpha erhält man die 42, wenn man 2 x 21 eingibt.

   Das geht auch mit SQL. In diesem Skript wollen wir SQL als
   Taschenrechner verwenden und dabei gleichzeitig lernen,
   welche Datentypen SQL kennt und wie man sie schreibt.
*/

-- Kommentare in SQL:

-- das ist ein einzeiliger Kommentar

/* das ist auch ein Kommentar 
*/


-- Numerische Werte in SQL

select 2 * 21; 

/* ergibt:

?column?
--------
42
*/

select 2 * 21 as Ergebnis;

/* ergibt:

ergebnis
--------
42 
*/

/* Bezeichner in SQL
   - Bezeichner für Spalten, Tabellen etc werden intern
     normiert: Großbuchstaben im SQL Standard,
     PostgreSQL normiert sie auf Kleinbuchstaben
   - Möchte man Sonderzeichen oder Leerstellen in einem
     Bezeichner, setzt man ihn in Anführungszeichen ("),
     dann wird er nicht normiert.
*/

select 2 * 21 as "Dies ist das Ergebnis";

/* ergibt:

Ergebnis
--------
42
*/

-- Rechnen mit numerischen Werten

select 4 * 20 - (76 / 2) as Ergebnis;

/* ergibt:

ergebnis
--------
42 
*/


-- Literale Darstellung numerischer Werte

select 42 as Integer, 3.14 as Numeric, 5e2 as Integer, 1.92e-3 as Real;

/* ergibt:

integer	numeric	   integer	    real
-------------------------------------
42	       3.14	   500	       0.00192
*/

/*
  Es gibt in SQL verschiedene numerische Datentypen.
  Die wichtigsten sind:

  INTEGER, INT       ganzzahlige Werte im Bereich -2147483648 to +2147483647 (4 Bytes)

  NUMERIC(precision, scale) Präzise Dezimalzahlen
                     precision ist die Gesamtzahl der Ziffern
                     scale die Zahl der Ziffern hinter dem Komma

  REAL               Fließkommazahl mit 6 signifikanten Stellen
  DOUBLE PRECISION   Fließkommazahl mit 15 signifikanten Stellen
*/

/* Operatoren für numerische Typen:
    
   - Addition:       +
   - Subtraktion:    -
   - Multiplikation: *
   - Division:       /
   - Modulo:         %
   - Potenz:         ^
*/	

-- Beispiele für die Operatoren

select 39 + 3;    -- 42
select 39 - -3;   -- 42
select 14 * 3;    -- 42
select 42 / 3;    -- 14
select 43 / 3;    -- 14
select 43 % 3;    -- 1
select 2 ^ 3;     -- 8
    

-- Strings in SQL

-- Hello World in SQL

select 'Hello World, this is SQL' as "Diese Nachricht";

/* ergibt:

Diese Nachricht
------------------------
Hello World, this is SQL
*/

/*
  Wie man sieht werden Strings in SQL mit einfachen Anführungszeichen
  (') geschrieben, nicht mit doppelten Anführungszeichen ("), wie das
  oft in anderen Sprachen der Fall ist.

  Grund: Doppelte Anführungszeichen (")  sind in SQL reserviert für die
  Begrenzung von Bezeichnern, siehe im Beispiel den Namen der
  Ergebnisspalte "Diese Nachricht".

*/

-- wie gibt man dann in SQL ein einfaches Anführungszeichen ein?

select 'Das Buch wurde von O''Reilly verlegt' as Text;

-- Verkettung von Strings

select 'ein ' || 'String ' || 'aus ' || 'mehreren ' || 'Teilen' 
       as "Verketteter String"; 

/* ergibt:

Verketteter String
------------------------------
ein String aus mehreren Teilen
*/


-- Teilstrings

select substring('Hello World, this is SQL!' from 7 for 5) as "Teilstring";

select substring('Hello World, this is SQL!' from 7 to 12) as "Teilstring";
-- Fehler bei 'to'


select substring('Hello World, this is SQL!' from 7) as "Teilstring";

/* ergibt:

Teilstring
----------
World
*/

-- Strings zuschneiden

select trim(both from '   SQL hat viele String-Funktionen ') as "Getrimmter String";

/* ergibt:

Getrimmter String
-------------------------------
SQL hat viele String-Funktionen
*/

-- Zeichenfolge in Kleinbuchstaben umwandeln

select lower('KLEIN') as Beispiel;
select upper('groß') as Beispiel;

/* Einige Operatoren und Funktionen mit Strings:
   
- Verkettung:                       ||
- alle Zeichen in Kleinbuchstaben:  lower
- alle Zeichen in Großbuchstaben:   upper
- Teil der Zeichenfolge:            substring
- Teilstring ersetzen:              overlay
- Zeichen am Anfang/Ende entfernen: trim
*/	


-- Datums- und Zeittypen

select date '2019-04-01' as "Erster April";

/* ergibt:

Erster April
------------
2019-04-01
*/

-- Rechnen mit Datumswerten

select date '2019-04-01' + 36 as "Später";

/* ergibt:

Später
----------
2019-05-07
*/

-- Werte aus Datumsangaben extrahieren

select extract(year from date '2019-04-01');
select extract(month from date '2019-04-01');
select extract(day from date '2019-04-01');

/* ergibt:

2019
4
1
*/

/* geht auch: */

select date_part('year', date '2019-04-01');
select date_part('month', date '2019-04-01');
select date_part('day', date '2019-04-01');

-- Datentyp time

select time '10:02';

/* ergibt:

10:02:00
*/

-- Datentypen timestamp und interval

select timestamp '2019-04-01 08:00:30' + interval '1 hour';

/* ergibt

2019-04-01 09:00:30
*/

/*
Die Datentypen time und timestamp gibt es auch jeweils mit Angabe der Zeitzone
*/

-- Datentyp interval

select interval '1 year 2 months'; -- PostgreSQL
select interval '1-2';             -- SQL Standard

select interval '3 days 4 hours';  -- PostgreSQL
select interval '3 4:00:00';       -- SQL Standard


/* Einige Operatoren und Funktionen mit Datums- und Zeittypen

- Addition von Tagen, Stunden, Intervallen: +
- Subtraktion...                          : -
- Differenz von Tagen                     : -
- Teilinformationen heraussuchen          : extract
*/	 

-- Wahrheitswerte

select 1 = 1;          -- True
select 1 = 2;          -- False
select true or false;  -- True
select 't' and 1 = 2;  -- False 
select 'y' and 1 = 1;  -- True


select 'yes' and 1 = 1;  -- True

/* SQL hat eine dreiwertige Logik, denn es gibt außer
   true und false auch noch den Wert null für "unbekannt".
   Es gilt null = null ist _nicht_ true, sondern null.
   Warum?
   Der linke Wert könnten z.B. 1 sein und der rechte 2, als käme false heraus.
   Es könnten aber auch beide Werte 1 sein, dann käme true heraus -
   das Ergebnis ist also "unbekannt", also null
*/

select null = null; -- NULL
select 1 = null;    -- NULL
select 1 = 1;       -- True 


/* Boolesche Operatoren:
   
   - logisches nicht: not
   - logisches und:   and
   - logisches oder:  or
*/


select 1 = 1 and 'a' <> 'b';  -- True
select 1 = 1 and 'a' = 'b';   -- False

select 1 = 1 or 'a' = 'b';    -- True

select not 1 = 1;             -- False

/* Präzedenz der logischen Operatoren
   - not bindet am stärksten
   - and bindet stärker als or
   Kommen in einem Ausdruck and und or vor, sollte man
   Klammern verwenden - bessere Lesbarkeit
*/

/* Wahrheitstafel in SQL */


select * from (values (true), (false)) t(a);
-- siehe https://www.postgresql.org/docs/10/static/queries-values.html

/* Wahrheitstafel für 'not a' */
select a, not a as "not a"
	from (values(true), (false)) t(a);

/* Wahrheitstafel für die Aussage 'a or b' */
select a, b, (a or b) as "a or b"
	from (values(true), (false)) t1(a)
	cross join (values (true), (false)) t2(b);
	
/* Wahrheitstafel für die Aussage 'a and b' */
select a, b, (a and b) as "a and b"
	from (values(true), (false)) t1(a)
	cross join (values (true), (false)) t2(b);
		
	
-- Eingebaute Variablen

-- Aktuellen Tag und aktuelle Zeit ausgeben

select CURRENT_DATE;

select current_date;

select CURRENT_DATE + 30 as demnächst;

select CURRENT_DATE + interval '1' year;

select current_time;  -- mit Zeitzone

select localtime;     -- ohne Zeitzone

select now();


-- Aktueller Benutzer

select CURRENT_USER;

/* Zusammenfassung
   
   - Wir haben die wichtigsten Datentypen gesehen:
     numerische Werte
     Strings
     Datums- und Zeitwerte
     Wahrheitswerte
   - Wir wissen, wie man diese Werte als Literale hinschreibt
   - Wir haben ein paar wenige der vielen Funktionen und
     Operatoren für diese Datentypen gesehen
   - Wir kennen die grundlegende Syntax von SQL 
*/

/* Zum Abschluss ein Überblick über die Entwicklung von SQL:

   1974  IBM entwickelt SEQUEL (Structured English Query Language)
   1977  Relational Software Inc (später Oracle) überarbeitet SEQUEL zu SEQUEL/2, 
         dann SQL genannt
   1986  ANSI standardisiert SQL auf Basis von IBMs Entwurf 
   1989  Revision des Standards publiziert als SQL89 oder auch SQL1, 
         jetzt auch ein ISO-Standard
   1992  ANSI/ISO publiziert SQL92, auch SQL2 genannt 
   1999  Objektrelationale Merkmale werden in den Standard übernommen,
	       ferner Trigger und Rekursion, SQL:1999 oder SQL3
   2004  SQL:2003 wird publiziert (erste Erweiterungen für XML)
   2006  SQL:2006 mit Erweiterungen für XML (SQL/XML) 
   2008  SQL:2008 diverse Erweiterungen
   2011  SQL:2011 Erweiterungen für temporale Daten
   2016  SQL:2016 Erweiterungen für JSON
*/

/* Zum Nachlesen in der PostgreSQL-Dokumentation:
   Datentypen
   Kap. 8 Data Types https://www.postgresql.org/docs/11/datatype.html  
   Operatoren und Funktionen
   Kap. 9 Functions and Operators https://www.postgresql.org/docs/11/functions.html
*/                               
                  
   
