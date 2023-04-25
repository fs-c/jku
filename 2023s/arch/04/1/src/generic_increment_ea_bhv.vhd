library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use IEEE.NUMERIC_STD.all;

entity generic_increment is
    generic(width: integer);
    port(clk, reset: in std_ulogic;
        y: out std_ulogic_vector(width - 1 downto 0));
end;

architecture behavioural of generic_increment is
    component cra 
        generic(width: integer);
        port(a, b: in std_ulogic_vector(width - 1 downto 0);
            cin: in std_ulogic;
            cout: out std_ulogic;
            sum: out std_ulogic_vector(width - 1 downto 0));
    end component;

    signal add_in: std_ulogic_vector(width - 1 downto 0) := (others => '0');
    signal add_out: std_ulogic_vector(width - 1 downto 0) := (others => '0');

    signal current: std_ulogic_vector(width - 1 downto 0) := (others => '0');

    signal increment: std_ulogic_vector(width - 1 downto 0) := (1 => '1', others => '0');

    signal carry: std_ulogic;
begin
    add_in <= current;

    add: cra generic map(width => width) port map(add_in, increment, '0', carry, add_out);

    process(clk, reset)
    begin
        if clk'event and clk = '0' then
            if reset = '1' or carry = '1' then
                current <= (others => '0');
            else
                current <= add_out;
            end if;
        end if;
    end process;

    y <= current;
end;
