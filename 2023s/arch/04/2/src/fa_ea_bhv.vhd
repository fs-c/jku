library IEEE; 
use IEEE.STD_LOGIC_1164.all;

entity FA is
  port(a,b,cin: in STD_ULOGIC;
       cout,s: out STD_ULOGIC);
end;

architecture behav of FA is
begin
  cout <= (a AND b) OR (a AND cin) OR (b AND cin);
  s <= a XOR b XOR cin;
end;