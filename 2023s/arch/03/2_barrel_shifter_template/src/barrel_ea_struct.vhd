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
entity barrel is
    generic(width : integer := 8);
    port(n:     in  std_ulogic_vector(width - 1 downto 0);
        shamt:  in  std_ulogic_vector(2 downto 0);
        y:      out std_ulogic_vector(width - 1 downto 0));
end;

-- todo: figure out a way to do this in a loop this is terrible
architecture structural of barrel is
    signal s0: std_ulogic_vector(width - 1 downto 0);
    signal s1: std_ulogic_vector(width - 1 downto 0);
begin
    zero_inner_loop_0: for j in 0 to 2 ** 0 - 1 generate
        mux: entity work.mux2 port map(n(j), '0', shamt(0), s0(j));
    end generate;
    regular_inner_loop_0: for j in 2 ** 0 to width - 1 generate
        mux: entity work.mux2 port map(n(j), n(j - 2 ** 0), shamt(0), s0(j));
    end generate;

    zero_inner_loop_1: for j in 0 to 2 ** 1 - 1 generate
        mux: entity work.mux2 port map(s0(j), '0', shamt(1), s1(j));
    end generate;
    regular_inner_loop_1: for j in 2 ** 1 to width - 1 generate
        mux: entity work.mux2 port map(s0(j), s0(j - 2 ** 1), shamt(1), s1(j));
    end generate;

    zero_inner_loop_2: for j in 0 to 2 ** 2 - 1 generate
        mux: entity work.mux2 port map(s1(j), '0', shamt(2), y(j));
    end generate;
    regular_inner_loop_2: for j in 2 ** 2 to width - 1 generate
        mux: entity work.mux2 port map(s1(j), s1(j - 2 ** 2), shamt(2), y(j));
    end generate;
end;
