/*

test.gp
Test that the script runs correctly

test.gp is a part of abelianbnf.
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

default(parisize,"1G");

\r abelianbnf.gp

multiquad(L,var='x) =
{
  my(pol1,pol2,n=#L,pol);
  if(n==1, return(var^2-L[1]));
  pol1 = multiquad(L[1..n\2],var);
  pol2 = multiquad(L[n\2+1..-1],var);
  pol = polcompositum(pol1,pol2,2);
  if(poldegree(pol)<50,pol=polredbest(pol));
  pol
};

\\special case: L list of primes p=1 mod d
multicyclic(L,d,var='x) =
{
  my(pol1,pol2,n=#L,pol);
  if(n==1, return(polsubcyclo(L[1],d,var)));
  pol1 = multicyclic(L[1..n\2],d,var);
  pol2 = multicyclic(L[n\2+1..-1],d,var);
  pol = polcompositum(pol1,pol2,2);
  if(poldegree(pol)<50,pol=polredbest(pol));
  pol
};

{Lbug = [
y^12 - y^11 - 16*y^10 - 653*y^9 + 393*y^8 + 14950*y^7 + 109304*y^6 -
80835*y^5 - 1707214*y^4 + 2077497*y^3 + 15471868*y^2 - 42167256*y + 33806473,
y^12 - 22*y^11 + 765*y^10 - 4026*y^9 + 149827*y^8 - 71106*y^7 + 55222855*y^6 +
321359298*y^5 + 6692869560*y^4 + 23008175632*y^3 + 340873826176*y^2 +
538377036288*y + 7709755644864,
y^18 + 62*y^17 + 326*y^16 - 24456*y^15 - 217630*y^14 + 3110226*y^13 +
30371737*y^12 - 135906476*y^11 - 1417583059*y^10 + 1902136676*y^9 +
21081090183*y^8 - 25549966768*y^7 - 124600524583*y^6 + 194096174770*y^5 +
257831586326*y^4 - 573685853948*y^3 - 18377734067*y^2 + 522879996388*y -
254528796619,
y^18 - 5*y^17 + 36*y^16 - 169*y^15 + 596*y^14 - 2540*y^13 + 9698*y^12 +
43502*y^11 - 241239*y^10 - 270290*y^9 + 1673169*y^8 + 604847*y^7 - 4765576*y^6 +
1637847*y^5 + 6264731*y^4 - 4368777*y^3 + 946594*y^2 - 2474345*y + 17186723,
y^18 - 5*y^17 + 29*y^16 - 134*y^15 + 631*y^14 - 2792*y^13 + 12330*y^12 -
27954*y^11 + 102538*y^10 - 242276*y^9 + 754958*y^8 - 1565216*y^7 + 3335356*y^6 +
466054*y^5 + 23095713*y^4 - 10218313*y^3 + 157922091*y^2 - 114516604*y +
887503681,
x^36 - 5*x^35 + 30*x^34 - 153*x^33 + 791*x^32 - 4007*x^31 + 20300*x^30 -
18880*x^29 + 99603*x^28 - 104847*x^27 + 399510*x^26 - 455376*x^25 + 1117614*x^24
+ 491197*x^23 + 4509419*x^22 + 2926675*x^21 + 15209460*x^20 + 6907961*x^19 +
46705884*x^18 + 23388099*x^17 + 55481761*x^16 + 26458568*x^15 + 55640490*x^14 +
29243289*x^13 + 53496888*x^12 + 46481985*x^11 + 59963728*x^10 + 45272693*x^9 +
54048922*x^8 + 36802164*x^7 + 41012867*x^6 + 26123526*x^5 + 17374632*x^4 +
9965197*x^3 + 6485963*x^2 + 2737867*x + 1771561,
y^4 - 5*y^3 + 59*y^2 + 30*y + 36
]};

Lquad = [-1,2,3,5,7,11,13,17,19,23]
Lcub = [7,13,19,31,37,43,61];
Lcyc = [56,72,168,104,112,180,208,280,312];

{Lpol = concat([
  Lbug,
  vector(5,i,multiquad(Lquad[1..i+1])),
  vector(3,i,multicyclic(Lcub[1..i+1],3)),
  vector(#Lcyc,i,polcyclo(Lcyc[i])),
  [multicyclic([31,41],5)]
])};
{Lres = [
  \\bugs
  [93,3,3,3],
  [168,3,3],
  [5],
  [532,7],
  [63,9],
  [2394,63,7],
  [2],

  \\multiquad
  [],
  [],
  [2],
  [8,4,4,2],
  [96,48,16,16,16,8,8,4,4,2,2,2,2,2,2,2],

  \\multicubic
  [],
  [],
  [18, 18, 9, 3, 3, 3, 3],

  \\cyclotomic
  [2],
  [3],
  [84],
  [117,3],
  [156,3],
  [15,5],
  [2359305, 195, 65],
  [29494920, 3, 3],
  [199836, 156, 52],

  \\biquintic
  [11]
]};

tott = getabstime();
{for(i=1,#Lpol,
  printf("\n\n[test #%d/%d]  ", i, #Lpol);
  pol = Lpol[i];
  tt = getabstime();
  res = abelianbnfinit(pol);
  tt = getabstime()-tt;
  if(res[2] != Lres[i], error("FAILED test ", i, "\nres=", res[2], "\nLres[i]=", Lres[i]));
  printf("test #%d/%d: %s", i, #Lpol, strtime(tt));
  res = [];
  bad = 0;
  S = [];
)};
tott = getabstime()-tott;
print("\nDone. [",strtime(tott),"]\n");

