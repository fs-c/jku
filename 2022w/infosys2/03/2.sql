SET ECHO ON

--- setup

CREATE TABLE Person (
    Nr NUMBER(4) PRIMARY KEY,
    Name VARCHAR2(15));
    
CREATE TABLE Bediensteter (
    Nr NUMBER(4) PRIMARY KEY,
    Gehalt NUMBER(6));
    
CREATE TABLE Professor (
    Nr NUMBER(4) PRIMARY KEY,
    HabilThema VARCHAR2(30));

INSERT INTO Person VALUES (1, 'Person');
INSERT INTO Person VALUES (2, 'Bediensteter');
INSERT INTO Person VALUES (3, 'Professor');

INSERT INTO Bediensteter VALUES (2, 2000);
INSERT INTO Bediensteter VALUES (3, 3000);

INSERT INTO Professor VALUES (3, 'A');

--- types

CREATE TYPE person_t AS OBJECT (
    Nr NUMBER(4),
    Name VARCHAR2(15)) NOT FINAL;
/

CREATE TYPE bediensteter_t UNDER person_t (
    Gehalt NUMBER(6)) NOT FINAL;
/

CREATE TYPE professor_t UNDER bediensteter_t (
    HabilThema VARCHAR2(30));
/

--- views

CREATE OR REPLACE VIEW personen_v OF person_t WITH OBJECT OID(Nr) AS
    SELECT person_t(p.Nr, p.Name)
    FROM Person p;
/

SELECT * FROM personen_v;

CREATE OR REPLACE VIEW bedienstete_v OF bediensteter_t WITH OBJECT OID(Nr) AS
    SELECT bediensteter_t(p.Nr, p.Name, b.Gehalt)
    FROM Bediensteter b, Person p
    WHERE b.Nr = p.Nr;
/

SELECT * FROM bedienstete_v;

CREATE OR REPLACE VIEW professoren_attribs_v OF professor_t WITH OBJECT OID(Nr) AS
    SELECT p.Nr, p.Name, b.Gehalt, pr.HabilThema
    FROM Professor pr, Bediensteter b, Person p
    WHERE pr.Nr = b.Nr AND b.Nr = p.Nr;
/

SELECT * FROM professoren_attribs_v;

CREATE OR REPLACE VIEW nur_bedienstete_v OF bediensteter_t WITH OBJECT OID(Nr) AS
    SELECT bediensteter_t(b.Nr, b.Name, b.Gehalt)
    FROM bedienstete_v b, Professor p
    WHERE p.Nr != b.Nr;
/

SELECT * FROM nur_bedienstete_v;

--- cleanup

DROP VIEW personen_v;

DROP TABLE Professor;
DROP TABLE Bediensteter;
DROP TABLE Person;

DROP TYPE professor_t;
DROP TYPE bediensteter_t;
DROP TYPE person_t;
