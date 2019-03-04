/* 
   Beispiele für referenzielle Integrität
   Vorlesung Datenbanksysteme
   (c) 2015 - 2019 by Burkhardt Renz, Technische Hochschule Mittelhessen
   $Id: ref-integritaet.sql 372 2019-03-04 08:58:53Z br $
*/
   
/* Wir erzeugen zwei Tabellen: Instrument und	 Musiker
   Musiker referenziert Instrument
*/	 
create table Instrument(
	IId	char(1) primary key,
	Bez varchar(40) not null
);

create table Musiker(
	Name varchar(20) primary key,
	IId char(1) not null references Instrument(IId)
);	

select * from Instrument;

insert into Musiker 
	values ('Miles', 't');
-- Was passiert?

insert into Instrument
	values ('t', 'Trompete');

select * from Instrument;

insert into Musiker 
	values ('Miles', 't');
-- Was passiert jetzt?

select * 
	from Musiker natural join Instrument;
	
delete from Instrument 
	where Id = 't';
-- Was passiert?

update Instrument
	set IId = 'x'
	where IId = 't';
-- Was passiert?		

-- Kaskadierendes Ändern und Löschen

drop table Musiker;

create table Musiker(
	Name varchar(20) primary key,
	IId char(1) not null references Instrument(IId)
		on delete cascade on update cascade
);	

insert into Musiker 
	values ('Miles', 't');

select * from Musiker;
select * from Instrument;

update Instrument
	set IId = 'x'
	where IId = 't';
-- Was passiert?		

select * from Musiker;

delete from Instrument 
	where IId = 'x';
-- Was passiert?

select * from Musiker;

-- aufräumen
drop table Musiker, Instrument;


