/* ---------------------------------------------------------------------------
   Copyright (c) 2000 - 2016 by Burkhardt Renz, THM
   $Id: azamon-create.sql 3576 2016-02-22 06:39:16Z br $
   ---------------------------------------------------------------------------
*/

/* Tabellen erzeugen */
create table Books(
  isbn           char(13) primary key,
  title          char(80),
  fname          char(40),
  author         char(40),
  price          numeric(6,2),
  year_published integer
);

create table Customers(
  cid            integer primary key,
  cname          char(40),
  address        char(200),
  cardnum        char(16)
);

create table Orders(
  ordernum       integer primary key,
  cid            integer references Customers(cid),
  order_date     date
);

create table Orderitems(
  ordernum      integer references Orders(ordernum),
  isbn          char(13) references Books(isbn),
  qty           integer,
  primary key( ordernum, isbn )
);

/* Inhalt */

/* Tabelle Books */
insert into Books(isbn, title, fname, author, price, year_published) 
  values ('3-257-21755-2','Schwarzrock', 'Brian', 'Moore', 7.90, 1987),
         ('3-257-21931-8', 'Die Große Viktorianische Sammlung', 'Brian', 'Moore', 8.90, 1990),
         ('3-518-37459-1', 'Der Hauptmann und sein Frauenbataillon', 'Mario', 'Vargas Llosa', 8.80, 1984),
         ('3-518-38020-6', 'Tante Julia und der Kunstschreiber', 'Mario', 'Vargas Llosa', 7.80, 1988),
         ('3-499-22410-0', 'Geschichte machen', 'Stephen', 'Fry', 9.90, 1999),
         ('3-257-06209-5', 'Entwurf einer Liebe auf den ersten Blick', 'Erich', 'Hackl', 10.90, 1999),
         ('3-422-72318-3', 'Längengrad', 'Dava', 'Zobel', 6.00, 1988),
         ('3-596-13399-8', 'Glück Glanz Ruhm', 'Robert', 'Gernhardt', 5.90, 1997),
         ('3-8031-3112-X', 'Die nackten Masken', 'Luigi', 'Malerba', 23.00, 1995),
         ('3-446-18298-5', 'Erklärt Pereira', 'Antonio', 'Tabucchi',  18.90, 1997),
         ('3-492-24118-2', 'Mit brennender Geduld', 'Antonio',  'Skármeta', 8.00, 2004);

