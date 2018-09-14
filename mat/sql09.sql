/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 9
   Datendefinitionen (DDL)

	$Id: sql09.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */

/* Folgende Anweisungen zeigen, wie die Tabellen der Datenbank "Wein"
   definiert wurden:


create table Artikel (
  ArtNr      numeric(6) primary key,
  Bez        varchar(80) not null,
  Weingut    varchar(80) not null,
  Jahrgang   numeric(4),
  Farbe      char(4) check (Farbe in ('rot', 'rosé', 'weiß')),
  Preis      numeric(6,2) not null
);

Struktur der Create-Anweisung

create table <Tabelle>(
  <Attr_1>  <Datentyp> <Integritätsbedingung>,
  <Attr_2>  <Datentyp> <Integritätsbedingung>,
  ... ,
  <Attr_n>  <Datentyp> <Integritätsbedingung>,
  <Integritätsbedingung für mehrere Attribute 1>
  ... ,
  <Integritätsbedingung für mehrere Attribute n>)

In der Definition der Tabelle Artikel sehen wir folgende
Integritätsbedingungen:

- primary key: Primärschlüssel, d.h. Werte müssen eindeutig sein
                                und null ist nicht erlaubt
- not null:    Null-Werte sind nicht erlaubt
- check:       Nur Werte, die die Bedingung erfüllen, sind erlaubt
      

Wir definieren einen Index zur schnellen Suche nach der Bezeichnung
eines Artikels:

create index Artikel_Bez_idx on Artikel(Bez);


create table Lieferant (
  LftNr      numeric(2) primary key,
  Firma      varchar(40) not null,
  Postfach   char(5),
  PLZ        varchar(8) not null,
  Ort        varchar(40) not null
);

create index Lieferant_Firma_idx on Lieferant(Firma);

create table LieferBez (
  LftNr      numeric(2) not null references Lieferant,
  ArtNr      numeric(6) not null references Artikel,
  primary key (LftNr, ArtNr)
);

Weitere Beispiele für Integritätsbedingungen:

- references:  Werte in LftNr von LieferBez müssen in 
               LftNr von Lieferant vorkommen
- primary key: Da der Primärschlüssel aus mehreren Attributen zusammengesetzt
               ist, muss er als gesonderte Zeile in der Anweisung definiert
               werden 

create table Kunde (
  KndNr      numeric(6) primary key,
  Name       varchar(40) not null,
  Vorname    varchar(40),
  Str        varchar(40),
  PLZ        varchar(8) not null,
  Ort        varchar(40) not null
);

Man kann auch mehrere Attribute für einen Index verwenden:

create index Kunde_Name_idx on Kunde(Name, Vorname);

create table Auftrag (
  AuftrNr    numeric(8) primary key,
  Datum      date not null,
  KndNr      numeric(6) references Kunde(KndNr)
);

create table AuftrPos (
  AuftrNr    numeric(8) references Auftrag(AuftrNr),
  Anzahl     integer not null,
  ArtNr      numeric(6) not null references Artikel(ArtNr),
  primary key (AuftrNr, ArtNr)
);
*/

/* Nun folgen Anweisungen, mit denen man ein bereits definiertes
   Datenbankschema ändern kann:
*/

-- Name einer Tabelle ändern

-- Beispiel: Umtaufen der Tabelle "Artikel" in "Wein"

alter table Artikel rename to Wein;

select * from Artikel;

/* ergibt:

ERROR:  relation "artikel" does not exist
LINE 1: select * from Artikel;
*/

select * from Wein;

-- und zurück

alter table Wein rename to Artikel;

select * from Artikel;

-- Name einer Spalte ändern
-- Beispiel: Umtaufen der Spalte "ArtNr" in "WeinId"

alter table Artikel
  rename column ArtNr to WeinId;

select * from Artikel;

/* ergibt:

 weinid |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/

-- und zurück

alter table Artikel
  rename column WeinId to ArtNr;

select * from Artikel;

-- Eine neue Spalte dem Schema einer Tabelle hinzufügen

-- Beispiel: Spalte mit Angabe zu Anbauart

alter table Artikel
  add column Anbauart varchar(12)
    check (Anbauart in ('biologisch', 'herkömmlich'))
    default 'herkömmlich';

/* In der Definition des neuen Attributs geben wir einen
   Default-Wert an, damit jede der Zeilen zum neuen
   Attribut auch einen Wert enthält.
*/

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis |  anbauart   
--------+---------------------+---------------+----------+-------+-------+-------------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90 | herkömmlich
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50 | herkömmlich
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90 | herkömmlich
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60 | herkömmlich
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90 | herkömmlich
*/

-- und zurück

alter table Artikel
  drop column Anbauart;    

select * from Artikel;  

/* Manchmal möchte man, dass beim Einfügen von Datensätzen des DBMS automatisch
   einen fortlaufenden ganzzahligen Wert für eine Primärschlüssel erzeugt.

   Das Konzept in SQL dafür ist der Sequenzgenerator (sequence generator), den 
   wir hier noch betrachten wollen.
*/

-- Beispiel: Erzeugen und Verwenden eines Sequenzgenerators mit Startwert 200000

create sequence KndNr_seq start 200000;

select * from Kunde;

/* ergibt: 

 kndnr  |   name   | vorname |        str         |   plz   |        ort        
--------+----------+---------+--------------------+---------+-------------------
 100101 | Kehl     | Thomas  | Weinstr. 3         | 79675   | Kaiserstuhl
 100102 | Kehl     | Thomas  | Im Riesling 3      | 68734   | Eltville
 100105 | Riesling | Karin   | 67, Rue du Château | F-68567 | Colmar
*/

insert into Kunde(KndNr, Name, Vorname, PLZ, Str, Ort)
  values( nextval('KndNr_seq'), 'Neumann', 'Holger', '60311',
    'Heinestr. 12', 'Frankfurt am Main');
    
select * from Kunde;

/* ergibt:

 kndnr  |   name   | vorname |        str         |   plz   |        ort        
--------+----------+---------+--------------------+---------+-------------------
 100101 | Kehl     | Thomas  | Weinstr. 3         | 79675   | Kaiserstuhl
 100102 | Kehl     | Thomas  | Im Riesling 3      | 68734   | Eltville
 100105 | Riesling | Karin   | 67, Rue du Château | F-68567 | Colmar
 200000 | Neumann  | Holger  | Heinestr. 12       | 60311   | Frankfurt am Main
*/

-- Ermitteln des aktuellen Werts der Sequenz

select currval('KndNr_seq');

/* ergibt:

currval
-------
200000
*/

drop sequence KndNr_seq;

-- Man kann Sequenzgeneratoren verwenden, um automatische Nummernvergabe
-- beim Insert zu erzeugen

create sequence KndNr_seq start 100000;

create table Kunde2 (
  kndnr numeric(6) primary key default nextval('KndNr_seq'),
  name  varchar(40) not null,
  vorname varchar(40),
  str varchar(40),
  plz varchar(8) not null,
  ort varchar(40) not null
);

-- Wir geben Kunden ein
insert into Kunde2(Name, Vorname, Str, PLZ, Ort)
	values ('Schneider', 'Albert', 'Wiesenstr. 14', '35390', 'Gießen');
	
select * from Kunde2;

/* ergibt:

 kndnr  |   name    | vorname |      str      |  plz  |  ort   
--------+-----------+---------+---------------+-------+--------
 100000 | Schneider | Albert  | Wiesenstr. 14 | 35390 | Gießen
*/

insert into Kunde2(Name, Vorname, Str, PLZ, Ort)
	values ('Just', 'Bettina', 'Wiesenstr. 14', '35390', 'Gießen');
	
select * from Kunde2;

/* ergibt:

 kndnr  |   name    | vorname |      str      |  plz  |  ort   
--------+-----------+---------+---------------+-------+--------
 100000 | Schneider | Albert  | Wiesenstr. 14 | 35390 | Gießen
 100001 | Just      | Bettina | Wiesenstr. 14 | 35390 | Gießen
*/

-- Wir wollen vielleicht wissen, welche Nummer der neu eingefügte Kunde hat
-- das geht so

select currval('KndNr_seq');

/* In PostgreSQL wird automatisch ein Sequenzgenerator erzeugt, wenn
   man in der Definition einer Tabelle den Pseudo-Datentyp "serial"
   verwendet:

   Aus der Dokumentation von PostgreSQL:


   In the current implementation, specifying

   CREATE TABLE tablename (
     colname SERIAL
   );
   is equivalent to specifying:

   CREATE SEQUENCE tablename_colname_seq;
   CREATE TABLE tablename (
     colname integer DEFAULT nextval('tablename_colname_seq') NOT NULL
);
*/

/* Man kann insert mit returning verwenden, dann  erhält man den
   automatisch vergebenen Wert:
*/

insert into Kunde2(Name, Vorname, Str, PLZ, Ort)
	values ('Metz', 'Hans-Rudolf', 'Wiesenstr. 14', '35390', 'Gießen') returning KndNr;

/* ergibt:

kndnr
-------
100002
*/

select * from Kunde2;

/* ergibt nun:

 kndnr  |   name    |   vorname   |      str      |  plz  |  ort   
--------+-----------+-------------+---------------+-------+--------
 100000 | Schneider | Albert      | Wiesenstr. 14 | 35390 | Gießen
 100001 | Just      | Bettina     | Wiesenstr. 14 | 35390 | Gießen
 100002 | Metz      | Hans-Rudolf | Wiesenstr. 14 | 35390 | Gießen
*/

-- aufräumen
drop table Kunde2; 
drop sequence KndNr_seq;
 

