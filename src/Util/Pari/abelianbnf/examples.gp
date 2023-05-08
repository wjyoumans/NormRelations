/*

examples.gp
Examples of use under GRH

examples.gp is a part of abelianbnf.
abelianbnf is a gp script computing class groups of abelian fields using the
methods described in the paper "Norm relations and computational problems in
number fields" by Jean-François Biasse, Claus Fieker, Tommy Hofmann and
Aurel Page, available at https://hal.inria.fr/hal-02497890
Author: Aurel Page, Copyright (C) Inria 2020 

abelianbnf is free software: you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

abelianbnf is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with
abelianbnf, in the file COPYING. If not, see <http://www.gnu.org/licenses/>.
Version 1.0 of September 2020.

*/

\r abelianbnf.gp

default(parisize,"50M");

{print("\nThis will reproduce the computation leading to examples 5.2 and 5.3
in the paper \"Norm relations and computational problems in number fields\" by
Jean-François Biasse, Claus Fieker, Tommy Hofmann and Aurel Page, available at
https://hal.inria.fr/hal-02497890\n\n")};

print("Example 5.2: should take approximately 6 seconds.");
pol = polcyclo(216);
abbnf = abelianbnfinit(pol);
print("class group: ", getcyc(abbnf));


default(parisize,"12G");

print("\nExample 5.3: should take approximately 4 hours.");
n = 6552;
pol = polcyclo(n);
abbnf = abelianbnfinit(pol);
cyc = getcyc(abbnf);
print("class group: ", cyc);
h = vecprod(cyc);
hm = hminus(n);
hp = h/hm;
print("h+: ", hp);

