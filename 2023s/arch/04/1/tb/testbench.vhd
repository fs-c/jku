library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all; 
use IEEE.NUMERIC_STD.all;

entity testbench is
end;

architecture test of testbench is
    component generic_increment is generic(width:integer);
        port(clk, reset: in STD_ULOGIC;
             y: out STD_ULOGIC_VECTOR(width-1 downto 0));
    end component;
    signal clk, reset: STD_ULOGIC := '0';
    signal y4: STD_ULOGIC_VECTOR(3 downto 0);
    signal y5: STD_ULOGIC_VECTOR(4 downto 0);
begin
    four: generic_increment generic map(width => 4) port map(clk, reset, y4);
    five: generic_increment generic map(width => 5) port map(clk, reset, y5);

    process begin
        for i in 1 to 100 loop
            clk <= '1';
            wait for 5 ns;
            clk <= '0';
            wait for 5 ns;
            report "The value of y4=" & integer'image(to_integer(unsigned(y4))) & "     y5=" & integer'image(to_integer(unsigned(y5)));
        end loop;
        wait;
    end process;

    process begin
        reset <= '1';
        wait for 12 ns;
        reset <= '0';
        wait;
    end process;
end;