library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all; 
use IEEE.NUMERIC_STD.all;

entity testbench is
end;

architecture test of testbench is
    component mult
      port(a, b:  in STD_ULOGIC_VECTOR(15 downto 0);
           y:     out STD_ULOGIC_VECTOR(31 downto 0));
    end component;
    component ADDER
      port(a, b:  in STD_ULOGIC_VECTOR(31 downto 0);
           s:     out STD_ULOGIC_VECTOR(31 downto 0));
    end component;
    signal a, b:  STD_ULOGIC_VECTOR(15 downto 0);
    signal y:     STD_ULOGIC_VECTOR(31 downto 0);
  begin
  
  my_mult: mult port map(a, b, y);
  
      process is
        variable aa, bb, tests, failed: Integer;
      begin
        a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(15, a'length));
        b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(10, b'length));
        wait for 40 ns;
        report "15 * 10 = " & integer'image(to_integer(unsigned(y)));
  
        a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(131, a'length));
        b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(3, b'length));
        wait for 40 ns;
        report "131 * 3 = " & integer'image(to_integer(unsigned(y)));
  
        a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(19, a'length));
        b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(46, b'length));
        wait for 40 ns;
        report "19 * 46 = " & integer'image(to_integer(unsigned(y)));
  
        a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(11, a'length));
        b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(200, b'length));
        wait for 40 ns;
        report "11 * 200 = " & integer'image(to_integer(unsigned(y)));
  
        a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(100, a'length));
        b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(100, b'length));
        wait for 40 ns;
        report "100 * 100 = " & integer'image(to_integer(unsigned(y)));
  
        aa := 0;
        tests := 0;
        failed := 0;
          
        while(aa < 30000) loop
          bb := 0;
          while(bb < 30000) loop
            a <= STD_ULOGIC_VECTOR(TO_UNSIGNED(aa, a'length));
             b <= STD_ULOGIC_VECTOR(TO_UNSIGNED(bb, b'length));
            tests := tests + 1;
            wait for 5 ns;
            if (aa * bb /= to_integer(unsigned(y))) then
              report integer'image(aa) & " + " & integer'image(bb) & " = " & integer'image(to_integer(unsigned(y))) severity error; 
              failed := failed + 1;
            end if;
            bb := bb + 143;
          end loop;
          aa := aa + 1550;
        end loop;
        report integer'image(failed) & " out of " & integer'image(tests) & " tests failed.";
        wait;
      end process;
  end;
  