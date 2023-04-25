library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use IEEE.NUMERIC_STD.all;

entity generic_increment is
    generic(width: integer);
    port(clk, reset: in STD_ULOGIC;
            y: out STD_ULOGIC_VECTOR(width-1 downto 0));
end;

architecture bhv of generic_increment is
begin
    -- TODO
end;
