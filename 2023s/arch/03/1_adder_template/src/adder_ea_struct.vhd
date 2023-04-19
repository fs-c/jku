library IEEE; use IEEE.STD_LOGIC_1164.all;
entity mux2_gen is
  generic(width : integer := 2);
  port(a, b: in  std_ulogic_vector(width-1 downto 0);
       s:    in  std_ulogic; 
       y:    out std_ulogic_vector(width-1 downto 0));
end;

architecture structural of mux2_gen is
begin
  y <= (a and (not (width-1 downto 0 => s))) or (b and (width-1 downto 0 => s));
end;

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity fa is
	port(a, b, c: 	in std_ulogic;
    	s, cout:	out std_ulogic);
end;

architecture structural of fa is
begin
	cout <= (a and b) or (a and c) or (b and c);
    s <= a xor b xor c;
end;

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity adder_gen is
	generic(width: integer := 8);
	port(a, b:	in std_ulogic_vector(width - 1 downto 0);
    	c:		in std_ulogic;
        s:		out std_ulogic_vector(width downto 0))
end;

architecture structural of adder_gen is
	signal s0: std_ulogic_vector(width / 2 downto 0);
    signal s1: std_ulogic_vector(width / 2 downto 0);
    signal sf: std_ulogic_vector(width - 1 downto 0)
begin
	recursion: if width / 2 > 1 generate 
    	add0_h: entity work.adder_gen generic map(width / 2) port map(a(width - 1 downto width / 2), b(width - 1 downto width / 2), '0', s0);
    	add1_h: entity work.adder_gen generic map(width / 2) port map(a(width - 1 downto width / 2), b(width - 1 downto width / 2), '1', s1);

    	add_l: entity work.adder_gen port_map(a(width / 2 - 1 downto 0), b(width / 2 - 1 downto 0), c, sf(width / 2 downto 0));
    end generate;

    base_case: if width / 2 = 1 generate
    	add: entity work.fa port map(a(0), b(0), c, s(0), sf(0));
        s(1) <= sf(0);
    end generate;

    mux: entity work.mux2_gen generic map (width / 2) port_map(s0, s1, sf(width / 2), sf(width downto width / 2));

    s <= sf;
end;

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity adder is
  	port(a, b: 	in  std_ulogic_vector(7 downto 0);
    	c:		in  std_ulogic;
    	s:		out std_ulogic_vector(8 downto 0));
end;

architecture structural of adder is
begin
	add: entity work.adder_gen port map(a, b, c, s);
end;
