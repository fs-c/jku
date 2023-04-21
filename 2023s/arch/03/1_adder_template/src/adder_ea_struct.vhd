-- addiert werden zwei n-bit zahlen
-- carry ripple adder
--  cost:   n * C(FA)
--  depth:  depth(FA) + 2(n - 1)
-- conditional sum adder
--  cost:   log2(n) * (3 * cost(FA) + cost(MUX))
--  depth:  log2(n) * (depth(FA) + depth(MUX))

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity mux2 is
    port(a, b:  in  std_ulogic;
        s:      in  std_ulogic; 
        y:      out std_ulogic);
end;

architecture structural of mux2 is
begin
    y <= (a and (not s)) or (b and s);
end;

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity mux2_gen is
    generic(width : integer := 2);
    port(a, b:  in  std_ulogic_vector(width - 1 downto 0);
        s:      in  std_ulogic; 
        y:      out std_ulogic_vector(width - 1 downto 0));
end;

architecture structural of mux2_gen is
begin
    y <= (a and (not (width - 1 downto 0 => s))) or (b and (width - 1 downto 0 => s));
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
        s:		out std_ulogic_vector(width - 1 downto 0);
		cout:	out std_ulogic);
end;

-- todo: probably no need to track carry separately from sum
architecture structural of adder_gen is
	signal s0: std_ulogic_vector(width / 2 - 1 downto 0);
    signal s1: std_ulogic_vector(width / 2 - 1 downto 0);
	signal c0: std_ulogic;
	signal c1: std_ulogic;

	signal lower_carry: std_ulogic;
begin
	recursion: if width / 2 > 0 generate 
    	add0_h: entity work.adder_gen generic map(width / 2) port map(
			a(width - 1 downto width / 2), b(width - 1 downto width / 2), '0', s0, c0
		);
    	add1_h: entity work.adder_gen generic map(width / 2) port map(
			a(width - 1 downto width / 2), b(width - 1 downto width / 2), '1', s1, c1
		);

    	add_l: entity work.adder_gen generic map(width / 2) port map(
			a(width / 2 - 1 downto 0), b(width / 2 - 1 downto 0), c, s(width / 2 - 1 downto 0), lower_carry
		);
    
    	mux_s: entity work.mux2_gen generic map (width / 2) port map(
			s0, s1, lower_carry, s(width - 1 downto width / 2)
		);
		mux_c: entity work.mux2 port map(
			c0, c1, lower_carry, cout
		);
	end generate;

    base_case: if width = 1 generate
    	add: entity work.fa port map(a(0), b(0), c, s(0), cout);
    end generate;
end;

library IEEE; use IEEE.STD_LOGIC_1164.all;
entity adder is
  	port(a, b: 	in  std_ulogic_vector(7 downto 0);
    	c:		in  std_ulogic;
    	s:		out std_ulogic_vector(8 downto 0));
end;

architecture structural of adder is
	signal cout: std_ulogic;
	signal temp_s: std_ulogic_vector(7 downto 0);
begin
	add: entity work.adder_gen generic map(8) port map(a, b, c, s(7 downto 0), cout);
	s(8) <= cout;
end;
