/*

certifyslow.gp
Slow certification functions

certifyslow.gp is a part of abelianbnf.
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

warning("using slow certification method.");
fastcert = 0;

abelianbnfcertify(abbnf) =
{
  my(L=[]);
  if(abbnf[1]==2,
    L = abbnf[3];
    for(i=1,#L,
      if(vprintab,print("certify: i=",i,"/",#L));
      if(!abelianbnfcertify(L[i]),return(0))
    );
  ,abbnf[1]==1,
    L = abbnf[5];
    for(j=1,#L,
      if(vprintab,print("certify:   j=",j,"/",#L));
      if(!abelianbnfcertify(L[j]),return(0))
    );
  ,/*else: 0*/
    if(#Lp,
      return(bnfcertify(abbnf[2]))
    ,\\else
      return(bnfcertify(abbnf[2]))
    )
  );
  1
};

