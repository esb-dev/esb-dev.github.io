/* -----------------------------------------------------------------------
   Vorlesung Datenbanksysteme
   Burkhardt Renz, THM 

   SQL Teil 5
   Äußerer Verbund

	$Id: sql05.sql 3907 2017-03-07 09:32:38Z br $
   ----------------------------------------------------------------------- */


/* Erinnern wir uns an das kartesische Produkt ("cross join"),
   Kombination aller Kunden mit jedem beliebigen Auftrag
*/

select AuftrNr, Kunde.KndNr, Auftrag.KndNr
  from Kunde cross join Auftrag
  order by AuftrNr;

/* ergibt 12 Datensätze : 3 Kunden * 4 Aufträge */


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

-- Der linke äußere Verbund ("left outer join")
-- ALLE Kunden mit Aufträgen, ggfs. auch ohne Auftrag

select KndNr, Name, Vorname, Ort, AuftrNr, Datum
	from Kunde join Auftrag using (KndNr);

/* ergibt:

 kndnr  | name | vorname |     ort     | auftrnr |   datum    
--------+------+---------+-------------+---------+------------
 100101 | Kehl | Thomas  | Kaiserstuhl |    1003 | 2007-03-01
 100101 | Kehl | Thomas  | Kaiserstuhl |    1001 | 2006-10-12
 100102 | Kehl | Thomas  | Eltville    |    1002 | 2006-02-12
*/
	
select KndNr, Name, Vorname, Ort, AuftrNr, Datum
  from Kunde left outer join Auftrag using (KndNr); 

/* ergibt: 

 kndnr  |   name   | vorname |     ort     | auftrnr |   datum    
--------+----------+---------+-------------+---------+------------
 100101 | Kehl     | Thomas  | Kaiserstuhl |    1003 | 2007-03-01
 100101 | Kehl     | Thomas  | Kaiserstuhl |    1001 | 2006-10-12
 100102 | Kehl     | Thomas  | Eltville    |    1002 | 2006-02-12
 100105 | Riesling | Karin   | Colmar      |         | 
*/

/* "left" bedeutet, dass ALLE Einträge der Tabelle die in der
   Formulierung der Anweisung links vom Schlüsselwort "outer join"
   verwendet werden, auch dann, wenn es keinen korrespondierenden
   Datensatz in der Tabelle rechts von "outer join" gibt.

   Was ergibt folgendes?
*/
  
select KndNr, Name, Vorname, Ort, AuftrNr,Datum
  from Auftrag right outer join Kunde using (KndNr); 

-- ALLE Aufträge, ggfs. auch ohne Kunden

select KndNr, Name, Vorname, Ort, AuftrNr,Datum
  from Kunde right outer join Auftrag using (KndNr); 

/* ergibt:

 kndnr  | name | vorname |     ort     | auftrnr |   datum    
--------+------+---------+-------------+---------+------------
 100101 | Kehl | Thomas  | Kaiserstuhl |    1003 | 2007-03-01
 100101 | Kehl | Thomas  | Kaiserstuhl |    1001 | 2006-10-12
 100102 | Kehl | Thomas  | Eltville    |    1002 | 2006-02-12
        |      |         |             |    1004 | 2006-02-12
*/
  
-- ALLE Kunden ggfs. ohne Auftrag sowie ALLE Aufträge ggfs. ohne Kunde

select KndNr, Name, Vorname, Ort, AuftrNr,Datum
  from Kunde full outer join Auftrag using (KndNr); 

/* ergibt:

 kndnr  |   name   | vorname |     ort     | auftrnr |   datum    
--------+----------+---------+-------------+---------+------------
 100101 | Kehl     | Thomas  | Kaiserstuhl |    1003 | 2007-03-01
 100101 | Kehl     | Thomas  | Kaiserstuhl |    1001 | 2006-10-12
 100102 | Kehl     | Thomas  | Eltville    |    1002 | 2006-02-12
        |          |         |             |    1004 | 2006-02-12
 100105 | Riesling | Karin   | Colmar      |         |             
*/


/* Man kann das mit dem äußeren Verbund erreichte Ergebnis auch auf andere
   Weise erreichen, nämlich durch Mengenoperatoren, die wir im nächsten
   Abschnitt diskutieren werden:
*/

-- alle Kunden mit Auftrag
select KndNr, Name, Vorname, Ort, AuftrNr, Datum
  from Kunde join Auftrag using (KndNr);

-- alle Kunden ohne Auftrag
select KndNr, Name, Vorname, Ort, null, null
  from Kunde 
  where KndNr not in (select KndNr from Auftrag where KndNr is not null);

-- alle Aufträge ohne Kunde
select null, null, null, null, AuftrNr, Datum
  from Auftrag where KndNr is null;

-- und nun die Vereinigung der drei Ergebnisse

select KndNr, Name, Vorname, Ort, AuftrNr, Datum
  from Kunde join Auftrag using (KndNr)
union
select KndNr, Name, Vorname, Ort, null, null
  from Kunde 
  where KndNr not in (select KndNr from Auftrag where KndNr is not null)
union
select null, null, null, null, AuftrNr, Datum
  from Auftrag where KndNr is null;

