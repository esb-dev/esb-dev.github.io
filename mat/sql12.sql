/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 12
   Trigger

	$Id: sql12.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */

/* 
	 Trigger machen ein Datenbanksystem zu einer sogenannten "aktiven Datenbank":

   Man definiert Funktionen, deren Aufruf durch bestimmte Ereignisse ausgelöst wird,
   z.B. das Hinzufügen eines Datensatzes u.ä.

   Wir wollen als Beispiel Trigger verwenden, um zu protokollieren, was mit unseren 
   Daten geschieht.
   (DBMS haben oft einen eingebauten Mechanismus des sogenannten Auditing, wir
   machen das mit reinen SQL-Mitteln in diesem Beispiel.) 

   Wir wollen protokollieren, was mit der Tabelle "Kunde" passiert,
   deshalb erstellen wir uns eine Tabelle "HistorieKunde", in der wir
   Änderungen an der Tabelle "Kunde" protokollieren werden.
*/

create table HistorieKunde ( 
	like Kunde
);

/* Mit dieser Anweisung wird eine neue (leere) Tabelle erstellt, die genau die
   gleiche Struktur (like!) hat wie die Tabelle "Kunde".
*/

/* Nun reichern wir die Tabelle mit Feldern an, in denen wir die Historie
   speichern können:
  
   In das Attribut "Benutzer" wollen wir eintragen, wer eine Änderung
   gemacht hat.

   In das Attribut "Aktion" wollen wir eintragen, welche Änderung gemacht
   wurde: 'i' für insert, 'u' für update, 'd' für delete

   In das Attribut "Zeitpunkt" wollen wir eintragen, wann genau die Änderung
   gemacht wurde.
*/

alter table HistorieKunde 
	add column Benutzer varchar(20);
alter table HistorieKunde 
	add column Aktion char(1) check (Aktion in ('i', 'u', 'd'));
alter table HistorieKunde
	add column Zeitpunkt timestamp;

select column_name, data_type
	from information_schema.columns
	where table_name = 'kunde';

select column_name, data_type
	from information_schema.columns
	where table_name = 'historiekunde';


/* Nun erzeugen wir eine Funktion , die die Modifikationen an den
   Kundendaten protokollieren soll.
*/

create function auditKunde() returns trigger as $$
	begin
		if ( tg_op = 'INSERT' ) then
			insert into HistorieKunde select new.*, user, 'i', now();
			return new;
		elsif ( tg_op = 'UPDATE' ) then
			insert into HistorieKunde select new.*, user, 'u', now();
			return new;
		elsif ( tg_op = 'DELETE' ) then
			insert into HistorieKunde select old.*, user, 'd', now();
			return old;
		end if;
		return null;
	end;
$$ language plpgsql;	

/* Erläuterungen:
   
   - $$ ist in PostgreSQL ein syntaktischer Ausdruck für eine Klammer
   - Die Funktion ist in der Sprache PL/pgSQL geschrieben
   - tg_op ist eine spezielle Variable, die automatisch gefüllt wird, wenn die
     Funktion in einem Trigger ausgeführt wird. Sie enthält die Aktion (als
     String), die den Trigger ausgelöst hat. (Siehe Abschnitt 40.9 der
     Dokumentation von PostgreSQL)
   - "old" ist der Datensatz vor Ausführen der Aktion, "new" hinterher
*/
  
-- nachsehen:

select routine_name, routine_type
	from information_schema.routines
	where routine_schema = 'public';

/* ergibt:

 routine_name | routine_type 
--------------+--------------
 auditkunde   | FUNCTION
*/

-- Wir verwenden jetzt diese Funktion, um Trigger zu erzeugen:

create trigger InsertTrigger after insert
	on Kunde for each row
	execute procedure auditKunde();
create trigger UpdateTrigger after update
	on Kunde for each row
	execute procedure auditKunde();
create trigger DeleteTrigger after delete
	on Kunde for each row
	execute procedure auditKunde();

-- nachsehen:

select trigger_name, event_manipulation
	from information_schema.triggers
	where trigger_schema = 'public';

/* ergibt:

 trigger_name  | event_manipulation 
---------------+--------------------
 deletetrigger | DELETE
 inserttrigger | INSERT
 updatetrigger | UPDATE
*/
	
-- Wir geben nun einen neuen Kunden ein, ändern ihn und löschen ihn.
-- Danach wollen wir sehen, was in der Tabelle HistorieKunde passiert ist:

insert into Kunde
	values ( 200001, 'Neumann', 'Klaus', 'Hauptstr.', '35390', 'Gießen' );
	
select * from Kunde;

select * from HistorieKunde;

-- wir ändern die Daten des neuen Kunden:
	
update Kunde
	set Str = 'Marktplatz'
	where KndNr = 200001;
	
select * from Kunde;

-- die Straße in der Adresse des neuen Kunden ist geändert worden
	
-- wir löschen diesen Kunden
	
delete from Kunde
	where KndNr = 200001;
	
select * from Kunde;

-- der eben eingefügte, dann  geänderte Kunde ist gelöscht worden.


-- wir wollen jetzt den Effekt der Trigger sehen:

select * from HistorieKunde;

/* ergab beim Vorbereiten:

 kndnr  |  name   | vorname |    str     |  plz  |  ort   | benutzer | aktion |         zeitpunkt          
--------+---------+---------+------------+-------+--------+----------+--------+----------------------------
 200001 | Neumann | Klaus   | Hauptstr.  | 35390 | Gießen | postgres | i      | 2017-03-07 10:15:23.038172
 200001 | Neumann | Klaus   | Marktplatz | 35390 | Gießen | postgres | u      | 2017-03-07 10:15:48.002077
 200001 | Neumann | Klaus   | Marktplatz | 35390 | Gießen | postgres | d      | 2017-03-07 10:16:16.489178
*/


-- wir löschen die Trigger wieder sowie die Historien-Tabelle

drop function auditKunde() cascade;
-- cascade löscht auch die Trigger, die diese Funktion verwenden!
drop table HistorieKunde;
	
