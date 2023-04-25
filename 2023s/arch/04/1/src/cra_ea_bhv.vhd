library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity cra is
    generic(width: integer);
    port(a, b: in STD_ULOGIC_VECTOR(width-1 downto 0);
        cin: in STD_ULOGIC;
        cout: out STD_ULOGIC;
        sum: out STD_ULOGIC_VECTOR(width-1 downto 0));
end;

architecture bhv of cra is
begin
    --TODO
end;