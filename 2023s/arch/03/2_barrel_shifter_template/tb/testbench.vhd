library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.NUMERIC_STD.all;

entity testbench is
end;

architecture test of testbench is
  component barrel
    generic(width : integer := 8);
    port(n:     in  std_ulogic_vector(width-1 downto 0);
         shamt: in  std_ulogic_vector(2 downto 0);
         y:     out std_ulogic_vector(width-1 downto 0));
  end component;
  constant width : integer := 8;
  signal n:  std_ulogic_vector(width-1 downto 0);
  signal shamt:  std_ulogic_vector(2 downto 0);
  signal y:  std_ulogic_vector(width-1 downto 0);
begin
  barrelShifter: barrel port map(n, shamt, y);
  
  process begin
    report "-- TRIAL CHECKS --";       
    n <= std_ulogic_vector(to_unsigned(1, n'length)); 
    for s in 0 to width-1 loop
      shamt <= std_ulogic_vector(to_unsigned(s, shamt'length));
      wait for 20 ns;
      report "1 << " & integer'image(s) & " = " & integer'image(to_integer(unsigned(y)));
    end loop;
  
    report "-- ERROR CHECKS --";        
    for inp in 0 to 255 loop
      n <= std_ulogic_vector(to_unsigned(inp, n'length));
      for s in 0 to width-1 loop
        shamt <= std_ulogic_vector(to_unsigned(s, shamt'length));
        wait for 20 ns;
        if (shift_left(unsigned(n), s) /= unsigned(y)) then
          report integer'image(inp) & " << " & integer'image(s) & " = " & integer'image(to_integer(unsigned(y))) severity error;
          wait;
        end if;
      end loop;
    end loop;
    report "none";  
    wait;
  end process;
end;
