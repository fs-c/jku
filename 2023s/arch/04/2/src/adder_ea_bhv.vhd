library IEEE; 
use IEEE.STD_LOGIC_1164.all;

entity ADDER is
    port(a,b: in STD_ULOGIC_VECTOR(31 downto 0);
         s: out STD_ULOGIC_VECTOR(31 downto 0));
  end;
  
  architecture behav of ADDER is
    component FA 
      port(a,b,cin: in STD_ULOGIC;
           cout, s: out STD_ULOGIC);
    end component;
    signal c: STD_ULOGIC_VECTOR(31 downto 0);
    signal s_buf: STD_ULOGIC_VECTOR(31 downto 0);
  begin
    fa0: FA port map(a(0), b(0), '0', c(0), s_buf(0));
    fa1: FA port map(a(1), b(1), c(0), c(1), s_buf(1));
    fa2: FA port map(a(2), b(2), c(1), c(2), s_buf(2));
    fa3: FA port map(a(3), b(3), c(2), c(3), s_buf(3));
    fa4: FA port map(a(4), b(4), c(3), c(4), s_buf(4));
    fa5: FA port map(a(5), b(5), c(4), c(5), s_buf(5));
    fa6: FA port map(a(6), b(6), c(5), c(6), s_buf(6));
    fa7: FA port map(a(7), b(7), c(6), c(7), s_buf(7));
    fa8: FA port map(a(8), b(8), c(7), c(8), s_buf(8));
    fa9: FA port map(a(9), b(9), c(8), c(9), s_buf(9));
    fa10: FA port map(a(10), b(10), c(9), c(10), s_buf(10));
    fa11: FA port map(a(11), b(11), c(10), c(11), s_buf(11));
    fa12: FA port map(a(12), b(12), c(11), c(12), s_buf(12));
    fa13: FA port map(a(13), b(13), c(12), c(13), s_buf(13));
    fa14: FA port map(a(14), b(14), c(13), c(14), s_buf(14));
    fa15: FA port map(a(15), b(15), c(14), c(15), s_buf(15));
    fa16: FA port map(a(16), b(16), c(15), c(16), s_buf(16));
    fa17: FA port map(a(17), b(17), c(16), c(17), s_buf(17));
    fa18: FA port map(a(18), b(18), c(17), c(18), s_buf(18));
    fa19: FA port map(a(19), b(19), c(18), c(19), s_buf(19));
    fa20: FA port map(a(20), b(20), c(19), c(20), s_buf(20));
    fa21: FA port map(a(21), b(21), c(20), c(21), s_buf(21));
    fa22: FA port map(a(22), b(22), c(21), c(22), s_buf(22));
    fa23: FA port map(a(23), b(23), c(22), c(23), s_buf(23));
    fa24: FA port map(a(24), b(24), c(23), c(24), s_buf(24));
    fa25: FA port map(a(25), b(25), c(24), c(25), s_buf(25));
    fa26: FA port map(a(26), b(26), c(25), c(26), s_buf(26));
    fa27: FA port map(a(27), b(27), c(26), c(27), s_buf(27));
    fa28: FA port map(a(28), b(28), c(27), c(28), s_buf(28));
    fa29: FA port map(a(29), b(29), c(28), c(29), s_buf(29));
    fa30: FA port map(a(30), b(30), c(29), c(30), s_buf(30));
    fa31: FA port map(a(31), b(31), c(30), c(31), s_buf(31));
  
    s <= s_buf;
  end;