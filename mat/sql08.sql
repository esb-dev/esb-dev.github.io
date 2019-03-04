/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 8
   Modifizierende Anweisungen

	$Id: sql08.sql 365 2019-03-04 08:36:20Z br $
   ----------------------------------------------------------------------- */
;
/* Modifizierende Anweisungen
   
   insert: neue Datensätze in eine Tabelle einfügen
   update: Werte in vorhandenen Datensätzen ändern
   delete: Datensätze in einer Tabelle löschen
*/ 
;
-- Beispiel für insert: Einfügen eines neuen Artikels

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

insert into Artikel(ArtNr, Bez, Weingut, Jahrgang, Farbe, Preis)
  values (100104, 'Ancien Domaine', 'Louis Max' , 2004, 'rot', 17.00);   


select * from Artikel;   

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 100104 | Ancien Domaine      | Louis Max     |     2004 | rot   | 17.00
*/
;

/* Struktur der Insert-Anweisung:

   insert into <Tabelle>(<Attr1>, <Attr2>, ... , <Attrn>)
     values(<Wert1>, <Wert2>, ... , <Wertn>)

   Wenn man die Werte in der Reihenfolge angibt, wie die Attribute in der
   Definition der Tabelle angegeben wurden, kann man die Attribut-Folge
   in der Anweisung weglassen. Im Standard müssen stets Werte für alle
   Attribute angegeben werden.
   
   In PostgreSQL: Wenn man ein Attribut der Tabelle weglässt, wird der 
   Default-Wert aus der Definition der Tabelle verwendet. 
   Ist kein Default-Wert definiert, wird null eingesetzt, sofern dies erlaubt ist.

   Man kann hinter "values" auch mehrere Werte-Tupel (durch Komma getrennt)
   angeben.

   Zweite Form:

   insert into <Tabelle>(<Attr_1>, <Attr_2>, ... , <Attr_n>)
     select <Select-Anweisung>

   dabei muss die Select-Anweisung eine Tupelmenge liefern, deren Schema dem
   der Tabelle entspricht.
*/
;

-- Beispiel für update: Ändern eines Artikel, 
-- wir erhöhen den Preis des neuen Artikel um 10%

update Artikel
  set Preis = Preis * 1.1
  where ArtNr = 100104;

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 100104 | Ancien Domaine      | Louis Max     |     2004 | rot   | 18.70
*/
;

-- Beispiel für update: Ändern mehrerer Felder  

update Artikel
  set Bez = 'Nouveau Ligne', 
      Jahrgang = 2003,
      Preis = 14.30
   where ArtNr = 100104;   

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
 100104 | Nouveau Ligne       | Louis Max     |     2003 | rot   | 14.30
*/
;

/* Struktur der Update-Anweisung

   update <Tabelle>
     set <Attr_1> = <Wert_1>,
         <Attr_2> = <Wert_2>,
         ... ,
         <Attr_n> = <Wert_n>
     where <Bedingung>
*/
;

-- Beispiel für delete: Löschen des Artikels mit der Artikelnummer 100104

delete from Artikel
  where ArtNr = 100104;

select * from Artikel;

/* ergibt:

 artnr  |         bez         |    weingut    | jahrgang | farbe | preis 
--------+---------------------+---------------+----------+-------+-------
 100001 | Les Châteaux        | Louis Max     |     2002 | rot   | 17.90
 100002 | Chablis             | Louis Max     |     2005 | weiß  | 15.50
 100003 | Château Caraguilhes | Louis Max     |     2005 | rosé  | 14.90
 604851 | Prosecco Val Monte  | Cave Bellenda |          | weiß  |  7.60
 145119 | Le Cop de Cazes     | Domaine Cazes |     2004 | rot   |  6.90
*/
;

/* Struktur der Delete-Anweisung:

   delete from <Tabelle>
     where <Bedingung>
*/
;
/* Was passiert, wenn man ein delete ohne where verwendet?
*/
