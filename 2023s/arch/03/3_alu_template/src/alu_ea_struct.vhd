library IEEE;
use IEEE.STD_LOGIC_1164.all;
entity alu is
  port(a, b:      in     std_ulogic_vector(31 downto 0);
       mode:      in     std_ulogic_vector(2 downto 0);
       result:    buffer std_ulogic_vector(31 downto 0);
       zero, neg: buffer std_ulogic);
end;
