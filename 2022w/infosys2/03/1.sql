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

CREATE OR REPLACE TYPE unterkunft_type;
/

CREATE OR REPLACE TYPE wellness_type UNDER entity_type (
    ort     VARCHAR2(20),
    art     VARCHAR2(20),
    hotel   REF unterkunft_type
);
/

CREATE OR REPLACE TYPE wellness_table AS TABLE OF REF wellness_type;
/

CREATE OR REPLACE TYPE wellness_ranked_type AS OBJECT (
    wellness    wellness_type,
    rang        NUMBER(4)
);
/

CREATE OR REPLACE TYPE zimmer_table AS TABLE OF zimmer_type;
/

CREATE OR REPLACE TYPE unterkunft_type UNDER entity_type (
    addresse                addresse_type,
    zimmer                  zimmer_table,
    beschreibung            VARCHAR(20),
    hotelkategorie          VARCHAR2(20),
    wellnesseinrichtungen   wellness_table
);
/

CREATE OR REPLACE TYPE unterkunft_table AS TABLE OF REF unterkunft_type;
/
CREATE OR REPLACE TYPE wellness_ranked_table AS TABLE OF REF wellness_ranked_type;
/

CREATE OR REPLACE TYPE region_type UNDER entity_type (
    beschreibung        VARCHAR(20),
    reg_unterkuenfte    unterkunft_table,
    reg_wellness        wellness_ranked_table
);
/

--------------------------------------------------------------------------------

CREATE TABLE unterkuenfte OF unterkunft_type
    NESTED TABLE wellnesseinrichtungen STORE AS nested_wellnesseinrichtungen
    NESTED TABLE zimmer STORE AS nested_zimmer;

CREATE TABLE wellnesseinrichtungen OF wellness_type;

CREATE TABLE regionen OF region_type
    NESTED TABLE reg_unterkuenfte STORE AS nested_unterkuenfte
    NESTED TABLE ref_wellness STORE AS nested_wellness_ranked;

INSERT INTO unterkuenfte VALUES (
    1, 'Unterkunft 1', addresse_type('Gasse', '2a', '4020', 'Linz'),
    zimmer_table(zimmer_type('Romantikzimmer', 2, 24), zimmer_type('Juniorsuite', 4, 12)),
    'Erste Unterkunft.', '4*', wellness_table()
);

SELECT * FROM unterkuenfte;

--- cleanup

DROP TABLE unterkuenfte;
DROP TABLE wellnesseinrichtungen;

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
