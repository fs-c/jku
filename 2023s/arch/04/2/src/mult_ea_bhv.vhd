library IEEE; 
use IEEE.STD_LOGIC_1164.all;

entity mult is 
    port(a, b:  in std_ulogic_vector(15 downto 0);
        y:      out std_ulogic_vector(31 downto 0));
end;

architecture behav of mult is
    component m4to2
        port(a, b, c, d:    in std_ulogic_vector(31 downto 0);
            x, y:           out std_ulogic_vector(31 downto 0));
    end component;

    component adder
        port(a,b:   in std_ulogic_vector(31 downto 0);
            s:      out std_ulogic_vector(31 downto 0));
    end component;

    -- temporary shifted vectors
    signal temp_0, temp_1, temp_2, temp_3, temp_4, temp_5, temp_6, 
        temp_7, temp_8, temp_9, temp_10, temp_11, temp_12, temp_13, 
        temp_14, temp_15: std_ulogic_vector(31 downto 0);

    -- intermediate addition sums and carries
    signal ints_00, intc_00, ints_01, intc_01, ints_02, intc_02, 
        ints_03, intc_03, ints_10, intc_10, ints_11, intc_11, 
        ints_final, intc_final: std_ulogic_vector(31 downto 0);
begin
    temp_0 <= (15 downto 0 => (b and (15 downto 0 => a(0))), others => '0');
    temp_1 <= (16 downto 1 => (b and (15 downto 0 => a(1))), others => '0');
    temp_2 <= (17 downto 2 => (b and (15 downto 0 => a(2))), others => '0');
    temp_3 <= (18 downto 3 => (b and (15 downto 0 => a(3))), others => '0');

    temp_4 <= (19 downto 4 => (b and (15 downto 0 => a(4))), others => '0');
    temp_5 <= (20 downto 5 => (b and (15 downto 0 => a(5))), others => '0');
    temp_6 <= (21 downto 6 => (b and (15 downto 0 => a(6))), others => '0');
    temp_7 <= (22 downto 7 => (b and (15 downto 0 => a(7))), others => '0');

    temp_8 <= (23 downto 8 => (b and (15 downto 0 => a(8))), others => '0');
    temp_9 <= (24 downto 9 => (b and (15 downto 0 => a(9))), others => '0');
    temp_10 <= (25 downto 10 => (b and (15 downto 0 => a(10))), others => '0');
    temp_11 <= (26 downto 11 => (b and (15 downto 0 => a(11))), others => '0');

    temp_12 <= (27 downto 12 => (b and (15 downto 0 => a(12))), others => '0');
    temp_13 <= (28 downto 13 => (b and (15 downto 0 => a(13))), others => '0');
    temp_14 <= (29 downto 14 => (b and (15 downto 0 => a(14))), others => '0');
    temp_15 <= (30 downto 15 => (b and (15 downto 0 => a(15))), others => '0');

    reduce_00: m4to2 port map(temp_0, temp_1, temp_2, temp_3, intc_00, ints_00);
    reduce_01: m4to2 port map(temp_4, temp_5, temp_6, temp_7, intc_01, ints_01);
    reduce_02: m4to2 port map(temp_8, temp_9, temp_10, temp_11, intc_02, ints_02);
    reduce_03: m4to2 port map(temp_12, temp_13, temp_14, temp_15, intc_03, ints_03);

    reduce_10: m4to2 port map(intc_00, ints_00, intc_01, ints_01, intc_10, ints_10);
    reduce_11: m4to2 port map(intc_02, ints_02, intc_03, ints_03, intc_11, ints_11);

    reduce_final: m4to2 port map(intc_10, ints_10, intc_11, ints_11, intc_final, ints_final);

    add: adder port map(intc_final, ints_final, y);
end;
