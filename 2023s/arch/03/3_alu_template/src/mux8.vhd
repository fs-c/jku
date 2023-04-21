library IEEE; use IEEE.STD_LOGIC_1164.all;
entity mux8 is
    generic(width : integer := 2);
    port(a, b, c, d, e, f, g, h:    in  std_ulogic_vector(width - 1 downto 0);
        s:                          in  std_ulogic_vector(2 downto 0); 
        y:                          out std_ulogic_vector(width - 1 downto 0));
end;

architecture structural of mux8 is
    signal t0: std_ulogic_vector(width - 1 downto 0);
    signal t1: std_ulogic_vector(width - 1 downto 0);
begin
    m0: entity work.mux4 generic map(width) port map(a, b, c, d, s(1 downto 0), t0);
    m1: entity work.mux4 generic map(width) port map(e, f, g, h, s(1 downto 0), t1);
    
    m2: entity work.mux2 generic map(width) port map(t0, t1, s(2), y);
end;
