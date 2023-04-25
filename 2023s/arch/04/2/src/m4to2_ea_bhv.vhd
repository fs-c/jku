library IEEE; 
use IEEE.STD_LOGIC_1164.all;

entity m4to2 is
    port(a, b, c, d:    in std_ulogic_vector(31 downto 0);
        x, y:           out std_ulogic_vector(31 downto 0));
end;

architecture behav of m4to2 is
    component csava
        port(a, b, c:   in std_ulogic_vector(31 downto 0);
            cout, s:    out std_ulogic_vector(31 downto 0));
    end component;

    signal temp_sum: std_ulogic_vector(31 downto 0);
    signal temp_carry: std_ulogic_vector(31 downto 0);
begin
    csava_0: csava port map(a, b, c, temp_carry, temp_sum);
    csava_1: csava port map(d, temp_carry, temp_sum, x, y);
end;
