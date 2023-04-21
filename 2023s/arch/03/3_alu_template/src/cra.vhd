library IEEE;
use IEEE.STD_LOGIC_1164.all;
entity fa is
  port(a, b, cin: in  std_ulogic;
       cout, s:   out std_ulogic);
end;

architecture structural of fa is
begin
    cout <= (a and b) or (a and cin) or (b and cin);
    s <= a xor b xor cin;
end;

library IEEE;
use IEEE.STD_LOGIC_1164.all;
entity cra is
  generic(width: integer);
  port(a, b:      in  std_ulogic_vector(width-1 downto 0);
       sub:       in  std_ulogic;
       sum:       out std_ulogic_vector(width-1 downto 0));
end;    

architecture structural of cra is
  component fa
    port(a, b, cin: in  std_ulogic;
         cout, s:   out std_ulogic);
  end component;
  signal c: std_ulogic_vector(width-1 downto 0) := (others=>'0');
  signal bb: std_ulogic_vector(width - 1 downto 0);
begin
  bb <= b(width - 1 downto 0) xor sub;

  fa0: fa port map(a(0), bb(0), sub, c(0), sum(0));
  
  FA_1: for I in 1 to width-1 generate
    faN: fa port map(a(I), bb(I), c(I-1), c(I), sum(I));
  end generate;
end;
