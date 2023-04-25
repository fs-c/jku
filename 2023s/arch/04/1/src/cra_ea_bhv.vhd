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
    port(a, b: in std_ulogic_vector(width - 1 downto 0);
        cin: in std_ulogic;
        cout: out std_ulogic;
        sum: out std_ulogic_vector(width - 1 downto 0));
end;

architecture structural of cra is
    signal c: std_ulogic_vector(width - 1 downto 0) := (others => '0');
begin
    fa_initial: entity work.fa port map(a(0), b(0), cin, c(0), sum(0));

    fa_loop: for i in 1 to width - 1 generate
        fa_i: entity work.fa port map(a(i), b(i), c(i - 1), c(i), sum(i));
    end generate;

    cout <= c(width - 1);
end;
