/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 11
   Benutzerdefinierte Funktionen und Prozeduren

	$Id: sql11.sql 368 2019-03-04 08:43:20Z br $
   ----------------------------------------------------------------------- */
;
/* Es ist in SQL möglich, eigene, benutzerdefinierte Funktionen und
   Prozeduren zu definieren. Diese werden vom SQL-Prozessor des DBMS
   übersetzt und in der Datenbank selbst gespeichert.

   Die verschiedenen Datenbankmanagementsysteme unterscheiden sich sehr
   stark, was die Implementierung dieser Möglichkeiten von SQL angeht.
   Wir betrachten ein paar Beispiele für benutzerdefinierte Funktionen
   in PostgreSQL.

   Die verschiedenen Produkte haben oft Programmiersprachen, die über
   SQL hinausgehen, so z.B.
   - PostgreSQL hat eine spezielle Programmiersprache PL/pgSQL
   - Oracle hat PL/SQL
   - Microsoft SQL Server hat TransactSQL

*/
;
-- Definition einer benutzerdefinierten Funktion

-- Beispiel: eine Funktion, die den Kartonpreis für Weine berechnet
;
create function kartonpreis(numeric) returns numeric as $$
	select $1 * 11;
$$ language sql;

/* Spezielle Syntax von PostgreSQL:
   
   - $$ sind Klammern
   - language sql gibt an, in welcher Sprache die Funktion definiert
     wurde
*/
;
-- Nachsehen im information_schema

select routine_name, routine_type
	from information_schema.routines
	where routine_schema = 'public';

/* ergibt:

 routine_name | routine_type 
--------------+--------------
 kartonpreis  | FUNCTION
*/
;
-- Wir verwenden diese Funktion

select ArtNr, Bez, Preis, Preis * 12, kartonpreis(Preis) as "Kartonpreis"
	from Artikel;

/* ergibt:

 artnr  |         bez         | preis | Kartonpreis 
--------+---------------------+-------+-------------
 100001 | Les Châteaux        | 17.90 |      196.90
 100002 | Chablis             | 15.50 |      170.50
 100003 | Château Caraguilhes | 14.90 |      163.90
 604851 | Prosecco Val Monte  |  7.60 |       83.60
 145119 | Le Cop de Cazes     |  6.90 |       75.90
*/
;
-- Man kann auch Funktionen definieren, die eine Tupelvariable als
-- Parameter haben
-- in unserem Beispiel sollen nur die Weißweine einen Rabatt bekommen

create function kartonpreis(Artikel) returns numeric as $$
	declare
		result numeric(6,2);
	begin	
	if $1.farbe = 'weiß' then
		result := $1.preis * 11;
	else	
		result := $1.preis * 12;
	end if;
	return result;
	end
$$ language plpgsql;	

-- nachsehen im information_schema

select routine_name, specific_name, routine_type
	from information_schema.routines
	where routine_schema = 'public';

/* ergibt:

 routine_name |   specific_name   | routine_type 
--------------+-------------------+--------------
 kartonpreis  | kartonpreis_16522 | FUNCTION
 kartonpreis  | kartonpreis_16523 | FUNCTION


   Wir sehen, dass es zwei Funktionen mit demselben Namen gibt:
   SQL unterstützt das Überladen von Funktionen.
*/

;
-- Wir verwenden diese Funktion:

select ArtNr, Bez, Farbe, Preis, Preis * 12 as "Normalpreis", kartonpreis(Artikel) as "Kartonpreis"
	from Artikel;

select ArtNr, Bez, kartonpreis(A) as "Kartonpreis"
	from Artikel A;

/* ergibt:

 artnr  |         bez         | Kartonpreis 
--------+---------------------+-------------
 100001 | Les Châteaux        |      214.80
 100002 | Chablis             |      170.50
 100003 | Château Caraguilhes |      178.80
 604851 | Prosecco Val Monte  |       83.60
 145119 | Le Cop de Cazes     |       82.80
*/
;
-- Wir löschen die beiden Funktionen wieder

drop function kartonpreis(numeric);
drop function kartonpreis(artikel);

-- und sehen wieder nach

select routine_name, routine_type
	from information_schema.routines
	where routine_schema = 'public';

