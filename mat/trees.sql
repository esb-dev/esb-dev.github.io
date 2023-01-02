/*
   Beispiele zum Text Bäume in SQL
	 (c) Burkhardt Renz, Jan 2023, all rights reserved
*/	 
create table tree (
	id int primary key,
	pid int references tree(id),
	scope int not null,
	lft int not null,
	rgt int not null,
	name varchar(128)
);

delete from tree; 

insert into tree(id, pid, scope, lft, rgt, name)
values
	(1, null, 1,  1, 16, 'Bundesrepublik'),
	(2,    1, 1,  2,  3, 'Schleswig-Holstein'),
	(3,    1, 1,  4, 13, 'Hessen'),
	(4,    1, 1, 14, 15, 'Thüringen'),
	(5,    3, 1,  5,  6, 'Gießen, RB'),
	(6,    3, 1,  7, 12, 'Darmstadt, RB'),
	(7,    6, 1,  8,  9, 'Darmstadt'),
	(8,    6, 1, 10, 11, 'Frankfurt'),
	(10,null, 2,  1, 18, 'Frankreich'),
	(11,  10, 2,  2, 11, 'PACA'),
	(12,  10, 2, 12, 17, 'Auvergne'),
	(13,  11, 2,  5, 10, 'Var'),
	(14,  11, 2,  3,  4, 'Alpes-Maritime'),
	(15,  13, 2,  6,  7, 'Toulon'),
	(16,  13, 2,  8,  9, 'Saint-Tropez'),
	(17,  12, 2, 13, 16, 'Puy-de-Dôme'),
	(18,  17, 2, 14, 15, 'Clermont-Ferrand');
	
-- Alle Wurzeln finden
select * from tree where pid is null;
select * from tree where lft = 1;

-- Eine bestimmte Wurzel finden
select * from tree where scope = 1 and pid is null;
select * from tree where scope = 1 and lft = 1;

-- Alle Blätter finden
select * from tree 
	where scope = 1
	  and id not in (select pid from tree where pid is not null);
select * from tree 
    where scope = 1 and rgt - lft = 1;

-- Zu einem Knoten den Elternknoten finden
select * from tree where id = (select pid from tree where id = 5);
select tp.* from tree tc join tree tp on tp.id = tc.pid
	where tc.id = 5;


select t2.*
from tree t1, tree t2
where t1.scope = 1 and t2.scope = t1.scope
and t2.lft < t1.lft and t2.rgt > t1.rgt
and t1.id = 5
order by t2.rgt - t2.lft 
limit 1;
-- Diese Anweisung findet zunächst alle Vorfahren
-- Der Knoten unter ihnen mit dem kleinsten Abstand von linker und rechter
-- Position ist der unmittelbar Vorfahr 

-- Zu einem Knoten die Kinder finden
select * from tree where pid = 6 order by lft;

select * from tree where id in (select child.id
	from tree child, tree parent 
	where 
	parent.scope = 2 and child.scope = parent.scope
    and
	parent.lft < child.lft and parent.rgt > child.rgt  -- alle Nachkommen
	group by child.id
	having max(parent.lft) = (select lft from tree where scope = 2 and id = 13)
	order by tree.lft
);  -- jene Nachkommen, bei denen der Elternknoten der nächste Vorfahr ist

  -- Herleitung
  select * from tree child, tree parent 
	where parent.scope = 2 and child.scope = parent.scope
    	and parent.lft < child.lft and parent.rgt > child.rgt
    order by parent.lft;
  -- findet alle Anfangs- und Endpunkte aller möglichen Pfade im Baum 
  select child.*, max(parent.lft) from tree child, tree parent 
	where parent.scope = 2 and child.scope = parent.scope
    	and parent.lft < child.lft and parent.rgt > child.rgt
    group by child.id;	
  -- findet zu allen Endpunkten (child) die linke Position des Elternknotens
  -- Diese Zahl vergleicht man nun mit der linken Position des
  -- Knotens, von dem wir die Kinder suchen	
	
-- Zu einem Knoten alle Nachkommen finden = den Teilbaum dieses Knotens finden
with recursive rt as (
	select * from tree where id = 3
	union
	select t.* from tree t 
	  join rt on rt.id = t.pid -- diejenigen, deren pid die id der bereits aufgesammelten ist
)
select * from rt
	order by lft;

select * from tree
	where scope = 1
	and lft between (select lft from tree where scope = 1 and id = 3)
				and (select rgt from tree where scope = 1 and id = 3)
	order by lft;
	
-- neue Wurzel einfügen
-- Voraussetzung ?id und ?scope sind frisch
insert into tree(id, pid, scope, lft, rgt, name)
  values(20, null, 3, 1, 2, 'Italien');
  
select * from tree order by scope, lft;  

-- neue Wurzel oberhalb der bisherigen einfügen
-- Voraussetzung ?id frisch, ?scope bereits vorhanden
-- Beispiel: Europa als Elternknoten von Italien einfügen
-- (1) Platz schaffen
update tree set lft = lft + 1 where scope = 3;
update tree set rgt = rgt + 1 where scope = 3; 
-- (2) Neue Wurzel einfügen
insert into tree(id, pid, scope, lft, rgt, name)
	values(21, null, 3, 1, (select max(rgt) from tree where scope = 3) + 1, 'Europa');
-- (3) Bisherige Wurzel einhängen
update tree set pid = 21
	where scope = 3 and lft = 2;	

-- Für die folgenden Beispiele nehmen wir nur den Baum der BRD
delete from tree; 

insert into tree(id, pid, scope, lft, rgt, name)
values
	(1, null, 1,  1, 16, 'Bundesrepublik'),
	(2,    1, 1,  2,  3, 'Schleswig-Holstein'),
	(3,    1, 1,  4, 13, 'Hessen'),
	(4,    1, 1, 14, 15, 'Thüringen'),
	(5,    3, 1,  5,  6, 'Gießen, RB'),
	(6,    3, 1,  7, 12, 'Darmstadt, RB'),
	(7,    6, 1,  8,  9, 'Darmstadt'),
	(8,    6, 1, 10, 11, 'Frankfurt');

-- neuen Knoten als erstes Kind einfügen 
-- Beispiel: Regierungsbezirk Kassel im Land Hessen

-- Voraussetzung ?id frisch, ?target gegeben
-- (1) Platz schaffen
update tree set lft = lft + 2
  where scope = 1 and lft > 4; -- scope = ?target.scope and lft > ?target.lft
update tree set rgt = rgt + 2
  where scope = 1 and rgt > 4; -- scope = ?target.scope and rgt > ?target.lft
-- (2) neuen Knoten einfügen
insert into tree(id, pid, scope, lft, rgt, name)
  values(31, 3, 1, 5, 6, 'Kassel, RB');
  -- values(?new.id, ?target.id, ?target.scope, ?target.lft + 1, ?target.lft + 2, ?new.name)
  
select * from tree where scope = 1 order by lft;    
  
-- neuen Knoten als letztes Kind einfügen 
-- Beispiel: Offenbach im Regierungsbezirk Darmstadt

-- Voraussetzung ?id frisch, ?target gegeben
-- (1) Platz schaffen
update tree set lft = lft + 2
  where scope = 1 and lft > 13; -- scope = ?target.scope and lft > ?target.rgt - 1
update tree set rgt = rgt + 2	
  where scope = 1 and rgt > 13; -- scope = ?target.scope and rgt > ?target.rgt - 1
 -- (2) neuen Knoten einfügen
insert into tree(id, pid, scope, lft, rgt, name)
  values(32, 6, 1, 14, 15, 'Offenbach');
  -- values(?new.id, ?target.id, ?target.scope, ?target.rgt, ?target.rgt + 1, ?new.name)
  
select * from tree where scope = 1 order by lft;  

-- neuen Knoten als linkes Geschwister einfügen 
-- Beispiel: Wiesbaden als linkes Geschister von Offenbach
-- Voraussetzung ?id frisch, ?target gegeben
-- (1) Platz schaffen
update tree set lft = lft + 2
  where scope = 1 and lft > 13; -- scope = ?target.scope and lft > ?target.lft - 1
update tree set rgt = rgt + 2	
  where scope = 1 and rgt > 13; -- scope = ?target.scope and rgt > ?target.lft - 1
 -- (2) neuen Knoten einfügen
insert into tree(id, pid, scope, lft, rgt, name)
  values(33, 6, 1, 14, 15, 'Wiesbaden');
  -- values(?new.id, ?target.pid, ?target.scope, ?target.lft, ?target.lft + 1, ?new.name)

select * from tree where scope = 1 order by lft;  

-- neuen Knoten als rechtes Geschwister einfügen 
-- Beispiel: Bergstraße als rechtes Geschister von Wiesbaden
-- Voraussetzung ?id frisch, ?target gegeben
-- (1) Platz schaffen
update tree set lft = lft + 2
  where scope = 1 and lft > 15; -- scope = ?target.scope and lft > ?target.rgt
update tree set rgt = rgt + 2	
  where scope = 1 and rgt > 15; -- scope = ?target.scope and rgt > ?target.rgt
 -- (2) neuen Knoten einfügen
insert into tree(id, pid, scope, lft, rgt, name)
  values(34, 6, 1, 16, 17, 'Bergstraße');
  -- values(?new.id, ?target.pid, ?target.scope, ?target.rgt + 1, ?target.rgt + 2, ?new.name)
	
select * from tree where scope = 1 order by lft;  

-- Verschieben eines Teilbaums
-- wir starten mit folgender Situation

delete from tree; 

insert into tree(id, pid, scope, lft, rgt, name)
values
	(1, null, 1,  1, 16, 'Bundesrepublik'),
	(2,    1, 1,  2,  3, 'Schleswig-Holstein'),
	(3,    1, 1,  4, 13, 'Hessen'),
	(4,    1, 1, 14, 15, 'Thüringen'),
	(5,    3, 1,  5,  6, 'Gießen, RB'),
	(6,    3, 1,  7, 12, 'Darmstadt, RB'),
	(7,    6, 1,  8,  9, 'Darmstadt'),
	(8,    6, 1, 10, 11, 'Frankfurt');

select * from tree where scope = 1 order by lft;  

-- Beispiel: Verschieben des Knotens für Hessen an die Position
--           als erstes Kind der Wurzel
-- sub in diesem Beispiel ist als der Knoten mit der id 3 (samt seiner Kinder)
-- target ist der Knoten mit der Id 1 und die relative Zielposition ist FIRST_CHILD

-- (1)
-- Der Teilbaum bekommt seine künftige neue pid
update tree set pid = 1 where id = 3;
-- (In diesem konkreten Beispiel wäre diese Anweisung nicht erforderlich,
-- weil ja Hessen bereits Kind der BRD ist, im Allgemeinen muss man aber die
-- pid des Teilbaums ändern.

-- (2)
-- Wir schaffen eine Lücke, die dann den Teilbaum aufnehmen kann
-- In unserem Fall beginnt die Lücke nach target.lft und muss soviele
-- Stellen freihalten wie der Teilbaum Platz braucht,
-- d.h. delta = sub.rgt - sub.left + 1, hier 13 - 4 + 1 = 10
-- denn Hessen hat insgesamt 5 Knoten, also 10 Stellen lft und rgt
update tree set lft = lft + 13 - 4 + 1
  where scope = 1 and lft > 1;
update tree set rgt = rgt + 13 - 4 + 1
  where scope = 1 and rgt > 1;
  
select * from tree where scope = 1 order by lft;  

-- (3)
-- Nun können wir den Teilbaum in die Lücke einfüllen.
-- Hier gilt es aufzupassen, denn wenn der
-- Teilbaum nach oben geschoben wird haben sich durch
-- Schritt 2 seine Positionen um delta verschoben
-- d.h. wir müssen jetzt delta zur Start- und Endeposition
-- zu den verschiebenden verschiebenen Knoten
-- Außerdem müssen wir berechnen wie weit wir die
-- Knoten verschieben müssen, nämlich um target.lft + 1 - (sub.lft + delta)
-- hier: 1 + 1 - (4 + 10) = -12
update tree set lft = lft - 12
  where scope = 1 and lft >= 4 + 10 and lft <= 13 + 10;
update tree set rgt = rgt - 12
  where scope = 1 and rgt >= 4 + 10 and rgt <= 13 + 10;  
  
select * from tree where scope = 1 order by lft;  

-- (4) 
-- Jetzt ist Hessen in der Lücke, aber dafür ist eine Lücke
-- dort entstanden, wo Hessen aben noch war
update tree set lft = lft - 10
  where scope = 1 and lft > 13 + 10;
update tree set rgt = rgt - 10
  where scope = 1 and rgt > 13 + 10;   

select * from tree where scope = 1 order by lft;  


-- Löschen eines Teilbaums
-- Beispiel Hessen mit allen Kindern löschen
delete from tree
  where scope = 1 and lft between 2 and 11;
-- Lücke schließen  
update tree set lft = lft - 10
  where scope = 1 and lft > 2;
update tree set rgt = rgt - 10
  where scope = 1 and rgt > 11; 


	 
