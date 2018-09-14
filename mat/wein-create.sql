/* ---------------------------------------------------------------------------
   Copyright (c) 2006 - 2016 by Burkhardt Renz. 
   All rights reserved.
   SQL-Skript zum Erzeugen der Datenbank Wein fuer PostgreSQL
   $Id: wein-create.sql 3705 2016-05-12 05:40:43Z br $
   ---------------------------------------------------------------------------
*/


/* Der Artikel mit der <ArtNr> trägt die Bezeichnung <Bez> und wird produziert
   vom Weingut <Weingut>, er hat den Jahrgang <Jahrgang>, die Farbe <Farbe> und
   kostet <Preis>.
*/

create table Artikel (
  ArtNr      numeric(6) primary key,
  Bez        varchar(80) not null,
  Weingut    varchar(80) not null,
  Jahrgang   numeric(4),
  Farbe      char(4) check (Farbe in ('rot', 'rosé', 'weiß')),
  Preis      numeric(6,2) not null
);

create index Artikel_Bez_idx on Artikel(Bez);

/* Der Lieferant mit der Lieferantennummer <LftNr> hat den Namen <Firma>, und
   als Adresse <Postfach>, <PLZ>, <Ort>.
*/

create table Lieferant (
  LftNr      numeric(2) primary key,
  Firma      varchar(40) not null,
  Postfach   char(5),
  PLZ        varchar(8) not null,
  Ort        varchar(40) not null
);

create index Lieferant_Firma_idx on Lieferant(Firma);

/* Der Lieferant mit der Lieferantennummer <LftNr> liefert den Wein mit der
	 Artikelnummer <ArtNr>.
*/

create table LieferBez (
  LftNr      numeric(2) not null references Lieferant,
  ArtNr      numeric(6) not null references Artikel,
  primary key (LftNr, ArtNr)
);

/* Der Kunde mit der Kundennummer <KndNr> heißt <Name>, <Vorname> und wohnt in
   <Str>, <PLZ> <Ort>.
*/

create table Kunde (
  KndNr      numeric(6) primary key,
  Name       varchar(40) not null,
  Vorname    varchar(40),
  Str        varchar(40),
  PLZ        varchar(8) not null,
  Ort        varchar(40) not null
);

create index Kunde_Name_idx on Kunde(Name, Vorname);

/* Der Auftrag mit der Auftragsnummer <AuftrNr> wird vom Kunden mit der
   Kundennummer <KndNr> am <Datum> erteilt.
*/

create table Auftrag (
  AuftrNr    numeric(8) primary key,
  Datum      date not null,
  KndNr      numeric(6) references Kunde(KndNr)
);

/* Der Auftrag <AuftrNr> hat eine Position, in der die <Anzahl> vom
   Artikel mit der Artikelnummer <ArtNr> bestellt wird.
*/

create table AuftrPos (
  AuftrNr    numeric(8) references Auftrag(AuftrNr),
  Anzahl     integer not null,
  ArtNr      numeric(6) not null references Artikel(ArtNr),
  primary key (AuftrNr, ArtNr)
);

/* Inhalt der Datenbank */

/* Artikel */

insert into Artikel(ArtNr, Bez, Weingut, Jahrgang, Farbe, Preis)
  values (100001, 'Les Châteaux', 'Louis Max', 2002, 'rot', 17.90),
         (100002, 'Chablis', 'Louis Max', 2005, 'weiß', 15.50 ),
         (100003, 'Château Caraguilhes', 'Louis Max', 2005, 'rosé', 14.90),
         (604851, 'Prosecco Val Monte', 'Cave Bellenda',  null, 'weiß', 7.60),
         (145119, 'Le Cop de Cazes', 'Domaine Cazes', 2004, 'rot', 6.90);

/* Lieferanten */

insert into Lieferant(LftNr, Firma, Postfach, PLZ, Ort)
  values (1, 'Weinimport Lehr', '45367', 'F-68567', 'Colmar'),
         (2, 'Bremer Weinkontor', '56', '28195', 'Bremen');

/* LieferBez */

insert into LieferBez(LftNr, ArtNr) 
  values (1, 100001), 
         (1, 100002), 
         (1, 100003),
         (2, 100002),
         (2, 604851),
         (2, 145119);

/* Kunden */

insert into Kunde(KndNr, Name, Vorname, Str, PLZ, Ort)
  values (100101, 'Kehl', 'Thomas', 'Weinstr. 3', '79675', 'Kaiserstuhl'),
         (100102, 'Kehl', 'Thomas', 'Im Riesling 3', '68734', 'Eltville'),
         (100105, 'Riesling', 'Karin', '67, Rue du Château', 'F-68567', 'Colmar');

/* Auftrag samt Positionen */

insert into Auftrag(AuftrNr, Datum, KndNr)
  values (1003, '2007-03-01', 100101);

insert into AuftrPos(AuftrNr, Anzahl, ArtNr)
  values (1003, 12, 100001),
         (1003, 12, 100002),
         (1003, 12, 100003);

insert into Auftrag(AuftrNr, Datum, KndNr)
  values (1001, '2006-10-12', 100101);
        
insert into AuftrPos(AuftrNr, Anzahl, ArtNr)
  values (1001, 1, 100001),
         (1001, 1, 100002),
         (1001, 1, 100003),
         (1001, 1, 145119);

insert into Auftrag(AuftrNr, Datum, KndNr)
  values (1002, '2006-02-12', 100102);

insert into AuftrPos(AuftrNr, Anzahl, ArtNr)
  values (1002, 48, 100003);

/* Auftrag 1004 ist ohne Kundennummer <KndNr>. Das ließe sich
   leicht verhindern, indem in der Definition der Tabelle verlangt wird,
   dass die Spalte <KndNr> keine Null-Werte enthalten darf.
   Wir verwenden den unvollständigen Auftrag hier nur zu
   Demonstrationszwecken - beim äußeren Verbund nämlich
*/

insert into Auftrag( AuftrNr, Datum, KndNr )
  values( 1004, '2006-02-12', null );

/* ------------------------------------------------------------------------ */

