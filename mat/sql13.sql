/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 13
   Rekursion in SQL

	$Id: sql13.sql 370 2019-03-04 08:46:45Z br $
   ----------------------------------------------------------------------- */
;

/* Rekursion in SQL

   Wir wollen die rekursiven Techniken in SQL am Beispiel der Tabelle
   "FollowedBy" untersuchen:

   "TwitterUser" sind Personen, die bei Twitter angemeldet sind.
   Ein "Follower" ist ein anderer TwitterUser, der automatisch Kurznachrichten
   des TwitterUsers erhalten will, dem er "folgt".
*/
;
-- Wir legen neue Tabellen an, in der wir TwitterUser und FollowedBy verzeichnen:

create table FollowedBy(
	TwitterUser varchar(20),
	Follower varchar(20),
	primary key (TwitterUser, Follower)
);	

-- Wir tragen ein paar Beziehungen ein:
	
insert into FollowedBy
	values ('Jack', 'Sarah'),
	       ('Sarah', 'Justin'),
	       ('Sarah', 'Jenny'),
	       ('Justin', 'Jenny'),
	       ('Justin', 'Tommy');

-- Tabelle ansehen:

select * from FollowedBy;

/* ergibt:

 twitteruser | follower 
-------------+----------
 Jack        | Sarah
 Sarah       | Justin
 Sarah       | Jenny
 Justin      | Jenny
 Justin      | Tommy
*/
;
/* Diese Information (eine binäre Relation) können wir als gerichteten Graph
   darstellen:

           Jack
            ↓
          Sarah
        ⬋        ⬊          
     Justin   →  Jenny
        ↓
     Tommy
*/
;

-- Es ist einfach, die Follower von 'Jack' zu finden:

select follower
  from FollowedBy
  where TwitterUser = 'Jack';

/* ergibt:

 follower 
----------
 Sarah
*/
;
/*
   Was aber, wenn wir die Anhänger der Anhänger von 'Jack' finden wollen?
*/

/*
  Bisher: Wir brauchen einen Selfjoin
*/
select F1.TwitterUser, F2.Follower
	from FollowedBy F1, FollowedBy F2
	where F1.Follower = F2.TwitterUser
		and F1.TwitterUser = 'Jack';

/* Das geht auch anders:
   SQL-Anweisung mit dem Schlüsselwort WITH:

   Beispiel: Follower von Followern von 'Jack'
*/

With
	FofF(t,f) as (select F1.TwitterUser as t, F2.Follower as f
	                    from FollowedBy F1, FollowedBy F2
	                    where F1.Follower = F2.TwitterUser)
	select t, f from FofF where t = 'Jack';

/* ergibt:

  t   |   f    
------+--------
 Jack | Jenny
 Jack | Justin
	
   in der WITH-Klausel erzeugen wir den Self-Join der Tabelle mit sich selbst
   und verwenden sie dann -- 
   eigentlich auch nicht groß anders wie geschachteltes SQL, bloß
   etwas übersichtlicher hinzuschreiben 
   und besonders geeignet, wenn man in einer Anweisung den geschachtelten Teil
   mehrfach braucht
*/                    
;
-- alle Pfade der Länge 2 in unserem Graphen:

With
	FofF(t,f) as (select F1.TwitterUser as t, F2.Follower as f
	                    from FollowedBy F1, FollowedBy F2
	                    where F1.Follower = F2.TwitterUser)
	select t, f from FofF;

/* ergibt:

   t   |   f    
-------+--------
 Jack  | Jenny
 Jack  | Justin
 Sarah | Tommy
 Sarah | Jenny
*/

/* mit dieser Technik können wir aber nicht die Anhänger der Anhänger ...
   finden, wenn wir nicht wissen, wieviele Stufen es gibt
   => wir brauchen Rekursion:
*/   
;
-- Rekursive SQL-Anweisung

-- Beispiel: Anhänger der Anhänger der Anhänger etc. von ’Jack’ finden

with recursive
  Follower(t,f) as (select TwitterUser as t, Follower as f from Followedby
                    union
                    select Follower.t, FollowedBy.follower as f
                      from Follower, FollowedBy
                      where Follower.f = FollowedBy.TwitterUser)
	select t, f from Follower where t = 'Jack'; 

/* ergibt:

  t   |   f    
------+--------
 Jack | Sarah
 Jack | Jenny
 Jack | Justin
 Jack | Tommy
*/                    
;

/* Beispiel abgewandelt aus der PostgreSQL Doku zur 
   Erläuterung von with recursive:
*/   
   
with recursive
  t(n) as (
    select 1
    union
    select n+1 from t where n < 100 )
  select sum(n) from t;

/* ergibt: 5050
*/

-- wie man hier sukzessive sieht:	

with t1(n) as (select 1)
	select * from t1;

/* ergibt:

 n 
---
 1
*/
;
with t1(n) as (select 1)
	select n+1 from t1;
/* ergibt:

 ?column? 
---
 2
*/	


with t1(n) as (select 1),
     t2(n) as (select n+1 from t1)
	select * from t1 
	union 
	select * from t2;

/* ergibt:

 n 
---
 1
 2
*/
;

with t1(n) as (select 1),
     t2(n) as (select n+1 from t1),
     t3(n) as (select n+1 from t2)
	select * from t1 
	union
	select * from t2
	union
	select * from t3;

/* ergibt:

 n 
---
 1
 2
 3
*/
;
	
with t1(n) as (select 1),
     t2(n) as (select n+1 from t1),
     t3(n) as (select n+1 from t2), 
     t4(n) as (select n+1 from t3)
	select * from t1 
	union
	select * from t2
	union
	select * from t3
	union 
	select * from t4;

/* ergibt:

 n 
---
 1
 2
 3
 4
*/
;

/* An diesem Beispiel kann man auch sehen, warum in dieser Rekursion
   union und union all identisch ist:
   t1 hat das Tupel [1] 
   t2 hat das Tupel [2]
   t3 hat das Tupel [3]
   usw.
*/
;  
-- mit Rekursion:

with recursive
  t(n) as (
    select 1        
    union
    select n+1 from t where n < 10 )
  select * from t;
  
-- nebenbei: PostgreSQL hat eine Funktion für diesen speziellen Fall:

select * from generate_series(1,10) as n;

-- was ergibt folgende Anweisung?

with recursive
  t(n) as (
    select 1        
    union
    select max(n)+1 from t where n < 10 )
  select * from t;
  
-- ERROR: aggregate functions are not allowed in a recursive query's recursive term
;
-- Wie wäre es besser?
with recursive
  t(n) as (
    select 1        
    union
    select n+1 from t where n < 10 )
  select max(n) from t;

-- noch ein Beispiel: Berechnen von 6!

with recursive fac(zahl, produkt) as (
	select 1, 1
	union all
	select zahl + 1, produkt * (zahl + 1) from fac where zahl < 6)
	select produkt from fac where zahl = 6;
 
/*
  1   1
  2   2 =   1 * 2
  3   6 =   2 * 3
  4  24 =   6 * 4
  5 120 =  24 * 5
  6 720 = 120 * 6
  
  Dieses Beispiel zeigt, dass es sich in Wahrheit um Iteration, nicht um
  Rekursion handelt, in SQL wird aber der Begriff "with recursive"
  verwendet.
  
  Viele weitere Beispiele in den Folien:
  Bruce Momjian: Programming the SQL Way with Common Table Expressions
  https://momjian.us/main/writings/pgsql/cte.pdf
*/
;

-- Transitiver Abschluss einer binären Relation 

-- Beispiel: Alle Beziehungen zwischen den Twitterern, egal über welchen Pfad

with recursive
  Follower(t,f) as 
  		(select TwitterUser as t, Follower as f from Followedby
     union
     select Follower.t, FollowedBy.follower as f
       from Follower, FollowedBy
       where Follower.f = FollowedBy.TwitterUser)
	select t, f from Follower order by t; 
                   
/* ergibt:

   t    |   f    
--------+--------
 Jack   | Sarah
 Jack   | Jenny
 Jack   | Justin
 Jack   | Tommy
 Justin | Tommy
 Justin | Jenny
 Sarah  | Tommy
 Sarah  | Justin
 Sarah  | Jenny
*/
;

-- Was passiert, wenn die binäre Relation einen Zyklus hat?

-- Zyklus einbauen

insert into FollowedBy( TwitterUser, Follower)
  values ('Tommy', 'Jack');

select * from FollowedBy;

-- Binäre Relation mit einem Zyklus

-- Beispiel: Alle Anhänger von 'Jack'

with recursive
  Follower(t,f) as (select TwitterUser as t, Follower as f from Followedby
                    union
                    select Follower.t, FollowedBy.follower as f
                      from Follower, FollowedBy
                      where Follower.f = FollowedBy.TwitterUser)
	select * from Follower where t = 'Jack';                    


-- Binäre Relation mit einem Zyklus, 1

/* Jetzt tritt ein Problem auf: die Rekursion endet niemals! 
   Wir stellen vorsichtshalber ein Timeout ein 
*/

set statement_timeout = 800;

with recursive
  Follower(t,f,depth) as (select TwitterUser as t, Follower as f, 0 from Followedby
                    union
                    select Follower.t, FollowedBy.follower as f, Follower.depth + 1
                      from Follower, FollowedBy
                      where Follower.f = FollowedBy.TwitterUser)
	select * from Follower where t = 'Jack';      


-- Binäre Relation mit einem Zyklus, 2
-- Eine einfache Abhilfe: wir limitieren die Zahl der auszugebenden Zeilen:	              

With recursive
  Follower(t,f,depth) as (select TwitterUser as t, Follower as f, 0 from Followedby
                    union
                    select Follower.t, FollowedBy.follower as f, Follower.depth + 1
                      from Follower, FollowedBy
                      where Follower.f = FollowedBy.TwitterUser)
	select * from Follower where t = 'Jack' limit 20;      
    
-- aufräumen

drop table FollowedBy;

-- Sudoku in SQL: Rekursives SQL löst Sudoku

/* Hier ist das Rätsel:

+-------+-------+-------+
| . 2 4 | . . . | 3 8 . |
| 6 . 7 | 2 . 9 | 1 . 4 |
| 8 1 . | 7 . 3 | . 9 6 |
+-------+-------+-------+
| . 4 8 | . . . | 9 7 . |
| . . . | . . . | . . . |
| . 6 9 | . . . | 5 1 . |
+-------+-------+-------+
| 7 5 . | 9 . 8 | . 4 1 |
| 4 . 1 | 6 . 5 | 7 . 9 |
| . 9 6 | . . . | 8 3 . |
+-------+-------+-------+
*/

-- Published by Marcin Mank in pgsql-general,
-- based on an Oracle version by Anton Scheffer

with recursive x(s, ind) as
( select sud, position(' ' in sud)
  from  (select ' 24   38 6 72 91 481 7 3 96 48   97           69   51 75 9 8 414 16 57 9 96   83 '::text 
             as sud) xx
  union all
  select substr( s, 1, ind - 1 ) || z || substr( s, ind + 1 ),
         position(' ' in repeat('x',ind) || substr( s, ind + 1 ) )
  from x,  (select gs::text as z from generate_series(1,9) gs) z
  where ind > 0
  and not exists ( select null
                   from generate_series(1,9) lp
                   where z.z = substr( s, ( (ind - 1 ) / 9 ) * 9 + lp, 1 )
                   or    z.z = substr( s, mod( ind - 1, 9 ) - 8 + lp * 9, 1 )
                   or    z.z = substr( s, mod( ( ( ind - 1 ) / 3 ), 3 ) * 3
                                      + ( ( ind - 1 ) / 27 ) * 27 + lp
                                      + ( ( lp - 1 ) / 3 ) * 6, 1 )
                 )
)
select s as "Lösung"
from x
where ind = 0;


/* und hier die Lösung:

+-------+-------+-------+
| 9 2 4 | 1 5 6 | 3 8 7 |
| 6 3 7 | 2 8 9 | 1 5 4 |
| 8 1 5 | 7 4 3 | 2 9 6 |
+-------+-------+-------+
| 1 4 8 | 5 6 2 | 9 7 3 |
| 5 7 2 | 3 9 1 | 4 6 8 |
| 3 6 9 | 8 7 4 | 5 1 2 |
+-------+-------+-------+
| 7 5 3 | 9 2 8 | 6 4 1 |
| 4 8 1 | 6 3 5 | 7 2 9 |
| 2 9 6 | 4 1 7 | 8 3 5 |
+-------+-------+-------+

*/


