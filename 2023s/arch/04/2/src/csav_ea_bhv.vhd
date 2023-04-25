library IEEE; 
use IEEE.STD_LOGIC_1164.all;

entity CSavA is
    port(a, b, c:   in std_ulogic_vector(31 downto 0);
        cout, s:    out std_ulogic_vector(31 downto 0));
end;

architecture behav of CSavA is
    constant width: integer := 32;

    component fa
        port(a, b, cin: in std_ulogic;
            cout, s:    out std_ulogic);
    end component;

    signal temp_carry: std_ulogic_vector(width - 1 downto 0);
begin
    fa_loop: for i in 0 to width - 1 generate
        fa_i: fa port map(a(i), b(i), c(i), temp_carry(i), s(i));
    end generate;

    cout <= temp_carry(width - 2 downto 0) & '0';
end; 