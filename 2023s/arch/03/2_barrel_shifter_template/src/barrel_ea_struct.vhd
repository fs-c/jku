library IEEE;
use IEEE.STD_LOGIC_1164.all;
entity barrel is
  generic(width : integer := 8);
  port(n:     in  std_ulogic_vector(width-1 downto 0);
       shamt: in  std_ulogic_vector(2 downto 0);
       y:     out std_ulogic_vector(width-1 downto 0));
end;
