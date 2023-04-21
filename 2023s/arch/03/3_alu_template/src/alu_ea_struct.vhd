library IEEE;
use IEEE.STD_LOGIC_1164.all;
entity alu is
    port(a, b:      in     std_ulogic_vector(31 downto 0);
        mode:       in     std_ulogic_vector(2 downto 0);
        result:     buffer std_ulogic_vector(31 downto 0);
        zero, neg:  buffer std_ulogic);
end;

architecture structural of alu is
    component cra
        generic(width: integer);
        port(a, b:      in  std_ulogic_vector(width-1 downto 0);
            sub:        in  std_ulogic;
            sum:        out std_ulogic_vector(width-1 downto 0));
    end component;

    component mux8
        generic(width : integer := 2);
        port(a, b, c, d, e, f, g, h:    in  std_ulogic_vector(width - 1 downto 0);
            s:                          in  std_ulogic_vector(2 downto 0); 
            y:                          out std_ulogic_vector(width - 1 downto 0));
    end component;

    constant width: integer := 32;

    signal addition: std_ulogic_vector(width - 1 downto 0);
    signal a_and_b: std_ulogic_vector(width - 1 downto 0);
    signal a_or_b: std_ulogic_vector(width - 1 downto 0);
    signal a_and_nb: std_ulogic_vector(width - 1 downto 0);
    signal a_or_nb: std_ulogic_vector(width - 1 downto 0);
    signal slt: std_ulogic_vector(width - 1 downto 0) := (others => '0');

    signal placeholder: std_ulogic_vector(width - 1 downto 0) := (others => '0');
begin
    add: cra generic map(width) port map(a, b, mode(2), addition);
    
    a_and_b <= a and b;
    a_or_b <= a or b;
    a_and_nb <= a and (not b);
    a_or_nb <= a or (not b);

    slt(0) <= addition(width - 1);

    mux: mux8 generic map(width) port map(
        addition, a_and_b, a_or_b, placeholder, addition, a_and_nb, a_or_nb, slt, mode, result);

    neg <= result(width - 1);
    zero <= not (or result);
end;
