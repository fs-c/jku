SET ECHO ON

CREATE OR REPLACE TYPE addresse_type AS OBJECT (
    strasse     VARCHAR2(20),
    hausnummer  VARCHAR2(5),
    plz         VARCHAR2(5),
    ort         VARCHAR2(20)
);
/

CREATE OR REPLACE TYPE zimmer_type AS OBJECT (
    kategorie   VARCHAR(20),
    betten      NUMBER(4),
    zimmer      NUMBER(4)
);
/

CREATE OR REPLACE TYPE entity_type AS OBJECT (
    id      NUMBER(4),
    name    VARCHAR2(20)
) NOT FINAL NOT INSTANTIABLE;
/

CREATE OR REPLACE TYPE hotel_type;
/

CREATE OR REPLACE TYPE wellness_type UNDER entity_type (
    ort     VARCHAR2(20),
    art     VARCHAR2(20),
    hotel   REF hotel_type
);
/

CREATE OR REPLACE TYPE wellness_table AS TABLE OF REF wellness_type;
/

CREATE OR REPLACE TYPE wellness_ranked_type AS OBJECT (
    wellness    REF wellness_type,
    rang        NUMBER(4)
);
/

CREATE OR REPLACE TYPE zimmer_table AS TABLE OF zimmer_type;
/

CREATE OR REPLACE TYPE unterkunft_type UNDER entity_type (
    addresse    addresse_type,
    zimmer      zimmer_table
) NOT FINAL NOT INSTANTIABLE;
/

CREATE OR REPLACE TYPE hotel_type UNDER unterkunft_type (
    hotelkategorie  VARCHAR2(20),
    wellness        wellness_table
);
/

CREATE OR REPLACE TYPE privatunterkunft_type UNDER unterkunft_type (
    beschreibung    VARCHAR(20)
);
/

CREATE OR REPLACE TYPE unterkunft_table AS TABLE OF REF unterkunft_type;
/
CREATE OR REPLACE TYPE wellness_ranked_table AS TABLE OF wellness_ranked_type;
/

CREATE OR REPLACE TYPE region_type UNDER entity_type (
    beschreibung        VARCHAR(20),
    reg_unterkuenfte    unterkunft_table,
    reg_wellness        wellness_ranked_table
);
/

--------------------------------------------------------------------------------

--- create tables

CREATE TABLE unterkuenfte OF unterkunft_type
    NESTED TABLE zimmer STORE AS nested_zimmer;

CREATE TABLE wellnesseinrichtungen OF wellness_type;

CREATE TABLE regionen OF region_type
    NESTED TABLE reg_unterkuenfte STORE AS nested_unterkuenfte
    NESTED TABLE reg_wellness STORE AS nested_wellness_ranked;

-- add some wellness facilities

INSERT INTO wellnesseinrichtungen VALUES (0, 'Wellness 1', 'Ort', 'Art', NULL);
INSERT INTO wellnesseinrichtungen VALUES (1, 'Wellness 2', 'Ort', 'Art', NULL);

--- add some accommodations and associate the hotel with the wellness stuff

INSERT INTO unterkuenfte VALUES (hotel_type(
    0, 'Unterkunft 1', addresse_type('Gasse', '2a', '4020', 'Linz'),
    zimmer_table(zimmer_type('Romantikzimmer', 2, 24), zimmer_type('Juniorsuite', 4, 12)),
    '4*', CAST(MULTISET(SELECT REF(w) FROM wellnesseinrichtungen w) AS wellness_table)
));

UPDATE wellnesseinrichtungen w SET hotel = (
    SELECT TREAT(REF(u) AS REF hotel_type) FROM unterkuenfte u WHERE u.id = w.hotel.id
);

INSERT INTO unterkuenfte VALUES (privatunterkunft_type(
    1, 'Unterkunft 2', addresse_type('Weg', '1', '4060', 'Leonding'),
    zimmer_table(zimmer_type('Gartensuite', 6, 8)), 'Privat 1'
));

--- add a region

INSERT INTO regionen VALUES (
    0, 'Region', 'First Region',
    CAST(MULTISET(SELECT REF(u) FROM unterkuenfte u) AS unterkunft_table),
    wellness_ranked_table(
        wellness_ranked_type((SELECT REF(w) FROM wellnesseinrichtungen w WHERE w.id = 0), 1),
        wellness_ranked_type((SELECT REF(w) FROM wellnesseinrichtungen w WHERE w.id = 1), 2)
    )
);

--- cleanup

DROP TABLE unterkuenfte;
DROP TABLE wellnesseinrichtungen;
DROP TABLE regionen;

DROP TYPE region_type FORCE;
DROP TYPE wellness_ranked_table FORCE;
DROP TYPE wellness_ranked_type FORCE;
DROP TYPE wellness_table FORCE;
DROP TYPE wellness_type FORCE;
DROP TYPE zimmer_table FORCE;
DROP TYPE unterkunft_table FORCE;
DROP TYPE unterkunft_type FORCE;
DROP TYPE entity_type FORCE;
DROP TYPE addresse_type FORCE;
DROP TYPE zimmer_type FORCE;
DROP TYPE hotel_type FORCE;
DROP TYPE privatunterkunft_type FORCE;
