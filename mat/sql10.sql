/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 10
   Views

	$Id: sql10.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */

/* Das Ergebnis einer Select-Anweisung ist konzeptionell aufgebaut wie
   eine Tabelle, man kann es also als eine _logische_ Tabelle sehen.

   Eine Sicht (englisch: View) ist eine solche _logische_ Tabelle, die
   durch eine Select-Anweisung definiert wird. Man kann eine Sicht in
   Select-Anweisungen wie eine Tabelle verwenden.

   In diesem Abschnitt werden wir Views definieren und verwenden (und am Ende
   auch wieder löschen.
*/

-- Erstellen einer View

-- Beispiel: View für Kontakte des Weinhändlers

create view Kontakte as
	select Vorname || ' ' || Name as Name, Str as Anschrift1,
		PLZ || ' ' || Ort as Anschrift2 from Kunde
	union
	select Firma as Name, 'PF '|| Postfach as Anschrift1,
		PLZ || ' ' || Ort as Anschrift2 from Lieferant;
		
select * from Kontakte;

/* ergibt:
  
       name        |     anschrift1     |    anschrift2     
-------------------+--------------------+-------------------
 Thomas Kehl       | Weinstr. 3         | 79675 Kaiserstuhl
 Bremer Weinkontor | PF 56              | 28195 Bremen
 Thomas Kehl       | Im Riesling 3      | 68734 Eltville
 Karin Riesling    | 67, Rue du Château | F-68567 Colmar
 Weinimport Lehr   | PF 45367           | F-68567 Colmar
*/
		
-- Wir können im Systemkatalog sehen, welche Tabellen und Views es in
-- unserer Datenbank gibt

-- alle Tabellen und Views in unserem Schema 'public'

select table_name 
  from information_schema.tables
  where table_schema = 'public';

/* ergibt:

 table_name 
------------
 lieferant
 lieferbez
 kunde
 auftrag
 artikel
 auftrpos
 kontakte
*/

-- nur die Tabellen

select table_name 
  from information_schema.tables
  where table_type = 'BASE TABLE' and table_schema = 'public';

/* ergibt:

 table_name 
------------
 lieferant
 lieferbez
 kunde
 auftrag
 artikel
 auftrpos
*/

-- nur die Views

select table_name 
  from information_schema.tables
  where table_type = 'VIEW' and table_schema = 'public';

/* ergibt:

 table_name 
------------
 kontakte
*/
  
-- geht auch so:

select table_name
	from information_schema.views
	where table_schema = 'public';

/* Diskussion:
   
   Bedeutung von Views für die logische Datenunabhängigkeit: wenn man
   konsequent Views verwendet, kann man die Basistabellen in gewissem Maße
   ändern, ohne dass Anwendungen, die die Views verwenden, geändert werden
   müssen.
   
   Views sind in der ANSI/SPARC-Architektur Teil der externen Sicht, 
   ihre Definition übersetzt die externe Sicht in die konzeptuelle Sicht
*/


-- Eine View kann man (in der Abfrage) verwenden wie eine Tabelle

-- Beispiel: Abfrage mit Bedingung

select * 
  from Kontakte
	where Name like '%Kehl%';

/* ergibt:

    name     |  anschrift1   |    anschrift2     
-------------+---------------+-------------------
 Thomas Kehl | Weinstr. 3    | 79675 Kaiserstuhl
 Thomas Kehl | Im Riesling 3 | 68734 Eltville
*/

/* Updates sind mit Views im Allgemeinen nicht möglich.
   
   In unserem Beispiel der Kontakte wäre bei einem neuen
   Eintrag nicht klar, ob es sich um einen Kunden oder einen
   Lieferanten handelt.

   Es gibt änderbare Sichten (updatable views), der SQL-Standard
   definiert präzise, welche Select-Anweisung für änderbare
   Sichten erlaubt sind. 
*/

-- Wir löschen die View wieder

drop view Kontakte;

-- Noch da?

select table_name 
  from information_schema.tables
  where table_schema = 'public';

select table_name 
  from information_schema.views
  where table_schema = 'public';
