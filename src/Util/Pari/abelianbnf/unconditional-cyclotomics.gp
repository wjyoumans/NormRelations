/*

unconditional-cyclotomics.gp
Unconditional computation of some cyclotomic class groups

unconditional-cyclotomics.gp is a part of abelianbnf.
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

{if(!fastcert,warning("Using slow certification method: the running times will
  differ significantly from the ones displayed in the article."))};

default(parisize,"10G");

{Lcyclo = [255, 272, 320, 340, 408, 480, 273, 315, 364, 456, 468, 504, 520, 560,
624, 720, 780, 840, 455, 585, 728, 936, 1008, 1092, 1260, 1560, 1680, 2520]};

{print("\nThis will reproduce the computation leading to Tables 1 and 2
in the paper \"Norm relations and computational problems in number fields\" by
Jean-François Biasse, Claus Fieker, Tommy Hofmann and Aurel Page, available at
https://hal.inria.fr/hal-02497890\n\n")};

{for(i=1,#Lcyclo,
  n = Lcyclo[i];
  print("\nn=",n," phi=",eulerphi(n), " (i=",i,"/",#Lcyclo,")");
  pol = polcyclo(n);
  T1 = getabstime();
  abbnf = abelianbnfinit(pol);
  T1 = getabstime()-T1;
  cyc = getcyc(abbnf);
  h = vecprod(cyc);
  hm = hminus(n);
  if (h%hm!=0, error("hminus does not divide h!"));
  hp = h \ hm;
  rk2 = #[d | d <- cyc, d%2==0];
  rk3 = #[d | d <- cyc, d%3==0];
  print("hp=",hp," rk2=",rk2," rk3=",rk3," cyc=",cyc);
  print("T1=",strtime(T1));
  T2 = getabstime();
  cert = abelianbnfcertify(abbnf);
  T2 = getabstime()-T2;
  if(!cert, error("certification failed! n=",n));
  print("T2=",strtime(T2));
)};

