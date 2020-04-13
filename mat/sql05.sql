/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 5
   Äußerer Verbund

	$Id: sql05.sql 362 2019-03-04 08:27:03Z br $
   ----------------------------------------------------------------------- */

;
/* Erinnern wir uns an das kartesische Produkt ("cross join"),
   Kombination aller Kunden mit jedem beliebigen Auftrag
*/

select AuftrNr, Kunde.KndNr, Auftrag.KndNr
  from Kunde cross join Auftrag
  order by AuftrNr;

/* ergibt 12 Datensätze : 3 Kunden * 4 Aufträge */
;

/* Der (innere) Verbund ("inner join"), den wir
   bisher betrachtet haben, ergibt die 
   Kombination der Kunden mit IHREN Aufträgen:
*/

select AuftrNr, Kunde.KndNr, Auftrag.KndNr
  from Kunde join Auftrag using (KndNr)
  order by AuftrNr;

/* ergibt:

 auftrnr | kndnr  | kndnr  
---------+--------+--------
    1001 | 100101 | 100101
    1002 | 100102 | 100102
    1003 | 100101 | 100101
*/
;

select count(*) from Auftrag;

/* Wir sehen drei Auftragsnummern, es gibt aber 4 Aufträge.
   Das liegt daran, dass beim (inneren) Verbund über das
   Attribut KndNr nur die Aufträge verwendet werden, die eine
   KndNr haben. Es gibt aber einen Auftrag OHNE KndNr.
*/
       
select AuftrNr, KndNr from Auftrag
	order by 1;

/* ergibt: 

 auftrnr | kndnr  
---------+--------
    1001 | 100101
    1002 | 100102
    1003 | 100101
    1004 |       
*/
;

-- Der linke äußere Verbund ("left outer join")
-- ALLE Aufträge, ggfs. auch ohne Kunde
;
-- bisher hatten wir den inneren Verbund:
select AuftrNr, Datum, KndNr, Name, Vorname, Ort 
	from Auftrag join Kunde using (KndNr);

/* ergibt:
+---------+------------+--------+------+---------+-------------+
| auftrnr | datum      | kndnr  | name | vorname | ort         |
+---------+------------+--------+------+---------+-------------+
| 1003    | 2007-03-01 | 100101 | Kehl | Thomas  | Kaiserstuhl |
| 1001    | 2006-10-12 | 100101 | Kehl | Thomas  | Kaiserstuhl |
| 1002    | 2006-02-12 | 100102 | Kehl | Thomas  | Eltville    |
+---------+------------+--------+------+---------+-------------+
*/
;
-- wir ersetzen "join" durch "left outer join"	
select AuftrNr, Datum, KndNr, Name, Vorname, Ort
  from Auftrag left outer join Kunde using (KndNr); 

/* und erhalten: 

+---------+------------+--------+------+---------+-------------+
| auftrnr | datum      | kndnr  | name | vorname | ort         |
+---------+------------+--------+------+---------+-------------+
| 1003    | 2007-03-01 | 100101 | Kehl | Thomas  | Kaiserstuhl |
| 1001    | 2006-10-12 | 100101 | Kehl | Thomas  | Kaiserstuhl |
| 1002    | 2006-02-12 | 100102 | Kehl | Thomas  | Eltville    |
| 1004    | 2006-02-12 | NULL   | NULL | NULL    | NULL        |
+---------+------------+--------+------+---------+-------------+

*/
;

/* "left" bedeutet, dass ALLE Einträge der Tabelle die in der
   Formulierung der Anweisung links vom Schlüsselwort "join"
   im Ergebnis vorkommen, auch dann, wenn es keinen korrespondierenden
   Datensatz in der Tabelle rechts von "join" gibt. 
   Fehlende Felder bekommen den Wert "NULL", denn ihr Wert ist ja
   unbekannt.

   Was ergibt folgendes?
*/
  
select AuftrNr,Datum, KndNr, Name, Vorname, Ort
  from Kunde right outer join Auftrag using (KndNr); 
  
/* Ergebnis erraten? */;  

-- Nun wollen wir haben: ALLE Kunden, ggfs. auch ohne Aufträge

select AuftrNr,Datum, KndNr, Name, Vorname, Ort
  from Auftrag right outer join Kunde using (KndNr); 

/* ergibt:
+---------+------------+--------+----------+---------+-------------+
| auftrnr | datum      | kndnr  | name     | vorname | ort         |
+---------+------------+--------+----------+---------+-------------+
| 1003    | 2007-03-01 | 100101 | Kehl     | Thomas  | Kaiserstuhl |
| 1001    | 2006-10-12 | 100101 | Kehl     | Thomas  | Kaiserstuhl |
| 1002    | 2006-02-12 | 100102 | Kehl     | Thomas  | Eltville    |
| NULL    | NULL       | 100105 | Riesling | Karin   | Colmar      |
+---------+------------+--------+----------+---------+-------------+

*/
;
  
-- Und jetzt: ALLE Aufträge ggfs. ohne Kunde sowie ALLE Kunden ggfs. ohne Auftrag

select AuftrNr, Datum, KndNr, Name, Vorname, Ort
  from Auftrag full outer join Kunde using (KndNr); 

/* ergibt:

+---------+------------+--------+----------+---------+-------------+
| auftrnr | datum      | kndnr  | name     | vorname | ort         |
+---------+------------+--------+----------+---------+-------------+
| 1003    | 2007-03-01 | 100101 | Kehl     | Thomas  | Kaiserstuhl |
| 1001    | 2006-10-12 | 100101 | Kehl     | Thomas  | Kaiserstuhl |
| 1002    | 2006-02-12 | 100102 | Kehl     | Thomas  | Eltville    |
| 1004    | 2006-02-12 | NULL   | NULL     | NULL    | NULL        |
| NULL    | NULL       | 100105 | Riesling | Karin   | Colmar      |
+---------+------------+--------+----------+---------+-------------+           
*/
;

/* Fazit:
   Der äußere Verbund berücksichtigt auch unbekannte Information,
   fehlende Daten werden durch NULL ersetzt.
   
   Ein weiteres Beispiel zum äußeren Verbund finden Sie in der
   Wikipedia zum Stichwort Join (SQL): https://de.wikipedia.org/wiki/Join_(SQL)
*/;
   

/* Man kann das mit dem äußeren Verbund erreichte Ergebnis auch auf andere
   Weise erreichen, nämlich durch Mengenoperatoren, die wir im nächsten
   Abschnitt diskutieren werden:
*/
;

-- alle Aufträge mit Kunden (innerer Verbund)
select AuftrNr, Datum, KndNr, Name, Vorname, Ort
  from Kunde join Auftrag using (KndNr);

-- alle Kunden ohne Auftrag
select null, null, KndNr, Name, Vorname, Ort
  from Kunde 
  where KndNr not in (select KndNr from Auftrag where KndNr is not null);

-- alle Aufträge ohne Kunde
select AuftrNr, Datum, null, null, null, null
  from Auftrag where KndNr is null;

-- und nun die Vereinigung der drei Ergebnisse

select AuftrNr, Datum, KndNr, Name, Vorname, Ort
  from Kunde join Auftrag using (KndNr)
union  
select null, null, KndNr, Name, Vorname, Ort
  from Kunde 
  where KndNr not in (select KndNr from Auftrag where KndNr is not null)
union  
select AuftrNr, Datum, null, null, null, null
  from Auftrag where KndNr is null;


/* Mehr zu Mengenoperatoren in SQL im nächsten Abschnitt der 
	Einführung in SQL
*/	
