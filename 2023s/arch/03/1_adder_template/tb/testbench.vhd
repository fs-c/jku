library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.NUMERIC_STD.all;

entity testbench is
end;

architecture test of testbench is
  
  component adder
    port(a, b:  in std_ulogic_vector(7 downto 0);
         c:     in std_ulogic;
         s:     out std_ulogic_vector(8 downto 0));
  end component;
  signal a, b:  std_ulogic_vector(7 downto 0);
  signal y:     std_ulogic_vector(8 downto 0);
begin
      my_add: adder port map(a, b, '0', y);

    process begin
      a <= std_ulogic_vector(to_unsigned(15, a'length));
      b <= std_ulogic_vector(to_unsigned(10, b'length));
      wait for 40 ns;
      report "15 + 10 = " & integer'image(to_integer(unsigned(y)));

      a <= std_ulogic_vector(to_unsigned(11, a'length));
      b <= std_ulogic_vector(to_unsigned(2, b'length));
      wait for 40 ns;
      report "11 + 2 = " & integer'image(to_integer(unsigned(y)));

      a <= std_ulogic_vector(to_unsigned(19, a'length));
      b <= std_ulogic_vector(to_unsigned(46, b'length));
      wait for 40 ns;
      report "19 + 46 = " & integer'image(to_integer(unsigned(y)));

      a <= std_ulogic_vector(to_unsigned(11, a'length));
      b <= std_ulogic_vector(to_unsigned(200, b'length));
      wait for 40 ns;
      report "11 + 200 = " & integer'image(to_integer(unsigned(y)));

      a <= std_ulogic_vector(to_unsigned(100, a'length));
      b <= std_ulogic_vector(to_unsigned(100, b'length));
      wait for 40 ns;
      report "100 + 100 = " & integer'image(to_integer(unsigned(y)));
      for aa in 0 to 63 loop
        for bb in 0 to 63 loop
          a <= std_ulogic_vector(to_unsigned(aa, a'length));
          b <= std_ulogic_vector(to_unsigned(bb, b'length));
          wait for 5 ns;
          if(aa+bb /= to_integer(unsigned(y))) then
            report integer'image(aa) & " + " & integer'image(bb) & " = " & integer'image(to_integer(unsigned(y))) & " (BREAK)" severity error;
            wait;
          end if;
        end loop;
      end loop;
      wait;
    end process;
end;
