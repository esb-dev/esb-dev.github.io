/* ---------------------------------------------------------------------------
   Copyright (c) 2005 - 2016 by Burkhardt Renz. All rights reserved.
   Datenbank Dozenten
   $Id: doz-create.sql 3558 2016-02-11 12:59:10Z br $
   ---------------------------------------------------------------------------
*/

/* Datenbank Dozent - Fachbereich zur Demonstration von outer joins
*/

-- table Fb Fachbereich
create table Fb (
  fbkurz  char(3) primary key,
  fbname  char(20)
);

-- table Doz Dozenten 
create table Doz (
  dozno    char(3) primary key,
  name     char(20),
  vorname  char(20),
  fbkurz   char(3) references Fb(fbkurz)
);

/* Inhalt Datenbank Dozent - Fachbereich
*/

-- table Fb Fachbereich 
insert into Fb(fbkurz, fbname)
  values ('I', 'Informatik'),
         ('M', 'Mathematik'),
         ('P', 'Physik');

-- table Doz Dozenten
insert into Doz(dozno, name, vorname, fbkurz)
  values ('D01', 'Knuth', 'Donald E.', 'I'),
         ('D02', 'Jackson', 'Michael', 'I'),
         ('D03', 'Brown', 'Kenneth S.', 'M'),
         ('D04', 'Davis', 'Miles', null);






