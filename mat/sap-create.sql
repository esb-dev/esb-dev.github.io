/* ---------------------------------------------------------------------------
   Copyright (c) 2005 - 2016 by Burkhardt Renz. All rights reserved.
   Datenbank Suppliers and Parts
   $Id: sap-create.sql 3558 2016-02-11 12:59:10Z br $
   ---------------------------------------------------------------------------
*/

/* The Suppliers-and-Parts Database Structure
*/

-- table S Suppliers 
create table S (
  sno     char(3) primary key,
  sname   char(12) not null,
  status  integer not null,
  city    char(15) not null
);

-- table P Parts
create table P (
  pno     char(3) primary key,
  pname	  char(12) not null,
  color	  char(12) not null,
  weight  decimal not null,
  city    char(15) not null
);

-- table SP 
create table SP (
  sno     char(3) references S,
  pno     char(3) references P,
  qty     integer not null,
  primary key(sno, pno)
);

/* The Suppliers-and-Parts Database Content
   see Date: An Introduction to Database Systems 8th edition p. 77
   and Date: SQL and Relational Theory p. 12
*/

-- table S Suppliers 
insert into S(sno, sname, status, city)
  values ('S1', 'Smith', 20, 'London'),
         ('S2', 'Jones', 10, 'Paris'),
         ('S3', 'Blake', 30, 'Paris'),
         ('S4', 'Clark', 20, 'London'),
         ('S5', 'Adams', 30, 'Athens');

-- table P Parts
insert into P(pno, pname, color, weight, city)
  values ('P1', 'Nut', 'Red', 12.0, 'London'),
         ('P2', 'Bolt', 'Green', 17.0, 'Paris'),
         ('P3', 'Screw', 'Blue', 17.0, 'Oslo'),
         ('P4', 'Screw', 'Red', 14.0, 'London'),
         ('P5', 'Cam', 'Blue', 12.0, 'Paris'),
         ('P6', 'Cog', 'Red', 19.0, 'London');

-- table SP
insert into SP(sno, pno, qty)
  values ('S1', 'P1', 300),
         ('S1', 'P2', 200),
         ('S1', 'P3', 400),
         ('S1', 'P4', 200),
         ('S1', 'P5', 100),
         ('S1', 'P6', 100),
         ('S2', 'P1', 300),
         ('S2', 'P2', 400),
         ('S3', 'P2', 200),
         ('S4', 'P2', 200),
         ('S4', 'P4', 300),
         ('S4', 'P5', 400);



