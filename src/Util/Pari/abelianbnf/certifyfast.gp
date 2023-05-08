/*

certifyfast.gp
Fast certification functions

certifyfast.gp is a part of abelianbnf.
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

{iferr(bnfcertify(bnfinit('x),L),E,
error("fast certification not available, please use branch aurel-bnfcertify"))};
fastcert = 1;

\\Bsub>0: type 1, all type 0 subfields have been certified and the unit index is bounded by Bsub.
\\Proposition 4.28
abelianbnfcertify(abbnf,{Lp=[]},{Bsub=0}) =
{
  my(L=[],B,Bmax,Lbnfdata,D);
  if(abbnf[1]==2,
    D = abbnf[6];
    Lp = factor(D[2])[,1];
    Lbnfdata = abbnf[5];
    Bmax = 0;
    for(i=1,#Lbnfdata,
      if(vprintab,print("certify: i=",i,"/",#Lbnfdata));
      B = abelianbnfcertify(Lbnfdata[i][2],Lp);
      if(!B, return(0));
      Bmax = max(Bmax,B)
    );
    L = abbnf[3];
    for(i=1,#L,
      if(vprintab,print("certify: i=",i,"/",#L));
      if(!abelianbnfcertify(L[i],,Bmax),return(0))
    );
  ,abbnf[1]==1,
    L = abbnf[5];
    my(VB,den,coefsbr,c0,S,r1,r2,rk,matextru,precb,prechr,precR0,check,R00,
      detubasis,r0,Lresinfpl,units,normindices,ratmul);
    if(Bsub, \\subfields already certified
      VB = vector(#L,j,Bsub)
    ,\\else
      VB = vector(#L,j,
        if(vprintab,print("certify:   j=",j,"/",#L," deg=",
          poldegree(L[j][2].pol), " disc=", L[j][2].disc, " Mink bnd=",
          nfminkow(L[j][2])));
        abelianbnfcertify(L[j],[abbnf[19]])
      )
    );
    den = abbnf[17];
    coefsbr = abbnf[23];
    c0 = denominator(coefsbr);
    coefsbr *= c0;
    S = abbnf[15];
    [r1,r2] = abbnf[24];
    w = abbnf[25];
    rk = sum(i=1,#S,#S[i][2]) + r1 + r2 - 1;
    B = c0 * den^(rk*c0) * prod(j=1,#L,VB[j]^abs(coefsbr[j]));
    if(vprintab,print("exponent(B): ", exponent(B)));
    precb = expo(B)+5;
    prechr = precbrauerhr(L,coefsbr);
    if(vprintab,print("prechr=",prechr));
    matextru = abbnf[26];
    r0 = matsize(matextru)[1];
    R00 = abbnf[27];
    detubasis = abbnf[28];
    precR0 = precdirectR0(matextru,r0,R00);
    if(vprintab,print("precR0=",precR0));
    localbitprec(precb+max(prechr,precR0));
    L = [[bnf[1],nfnewprec(bnf[2])] | bnf <- L];
    hR = w*prod(i=1,#L,my(bnf=L[i][2]);
      (bnf.reg*bnf.no/bnf.tu[1])^coefsbr[i])^(1/c0);
    Lresinfpl = abbnf[29];
    normindices = abbnf[30];
    ratmul = abbnf[31];
    units = unitmatrix(L,r1,r2,Lresinfpl);
    matextru = vecextract(units,[1..r1+r2-1],normindices);
    R00 = abs(matdet(matextru));
    R0 = R00*detubasis;
    check = R0*ratmul/hR;
    if(abs(check^c0-1) >= 1/B,
      print("certification failed!!! ", exponent(abs(check^c0-1)),
      " ", precision(abs(check^c0-1),1));
      error("certification failed!")
    );
    1
  ,/*else: 0*/
    if(#Lp,
      bnfcertify(abbnf[2],Lp,&B);
      return B;
    ,\\else
      return(bnfcertify(abbnf[2],2))
    )
  );
  1
};

