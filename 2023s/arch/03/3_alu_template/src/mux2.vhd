library IEEE; use IEEE.STD_LOGIC_1164.all;
entity mux2 is
    generic(width : integer := 2);
    port(a, b:  in  std_ulogic_vector(width - 1 downto 0);
        s:      in  std_ulogic; 
        y:      out std_ulogic_vector(width - 1 downto 0));
end;

architecture structural of mux2 is
begin
    y <= (a and (not (width - 1 downto 0 => s))) or (b and (width - 1 downto 0 => s));
end;
