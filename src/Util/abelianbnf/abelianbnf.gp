/*

abelianbnf.gp
Main functions

abelianbnf.gp is a part of abelianbnf.
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


/*
  Sections:
    I)      Utilities
    II)     Accessors
    III)    Linear algebra
    IV)     Number fields utilities
    V)      Brauer class group
    VI)     Galois, relations and subfields computations
    VII)    Auxiliary functions for type 1
    VIII)   Main functions
    IX)     Certification
*/

{iferr(bnfunits(bnfinit(x^2-2,1)),E,
error("abelianbnf cannot run on this version of Pari/gp. Please use a more recent version."))};

/*     I) Utilities         */

install(ZM_snf_group,"mGD&D&");

vprintab = 0; \\verbose print on/off

\\only remove powers of small primes
cheaprad(N) =
{
  my(M=N,D=1,k,m);
  forprime(p=2,10^5, \\useless to remove more: slow for only a few bits
    v = valuation(M,p);
    if(v>0, M \= p^v; D*=p);
  );
  k = ispower(M,,&m);
  if(k,m*D,M*D)
};

expo(x) = if(x==0,-oo,exponent(x)+1);

preceval0(c,ea,i) =
{
  if(i==0,return(0));
  if(c==0,return(0));
  i*ea + expo(c) + expo(i)
};
preceval(f,a) =
{
  my(ea=expo(a),d=poldegree(f));
  if(d<=0,return(0));
  expo(d) + vecmax([preceval0(polcoef(f,i),ea,i) | i <- [0..d]])
};


/*     II) Accessors         */

getexpo(abbnf) =
{
  my(cyc);
  cyc = getcyc(abbnf);
  if(cyc==[], 1, cyc[1]);
};

getcyc(abbnf) =
{
  if(abbnf[1]==2, abbnf[2]
  ,abbnf[1]==1, abbnf[2]
  ,/*else: 0*/ abbnf[2].cyc
  );
};

getpol(abbnf) =
{
  if(abbnf[1]==2, abbnf[4]
  ,abbnf[1]==1, abbnf[3]
  ,/*else: 0*/ abbnf[2].pol
  );
};

getdisc(abbnf) =
{
  if(abbnf[1]==2, error("not implemented");
  ,abbnf[1]==1, abbnf[18]
  ,/*else: 0*/ abbnf[2].disc
  );
};

abgal_gal(abgal) = abgal[1];
abgal_galgen(abgal) = abgal[2];
abgal_U(abgal) = abgal[3];
abgal_Ui(abgal) = abgal[4];
abgal_cyc(abgal) = abgal[5];


/*     III) Linear algebra         */

\\assume n is a prime power
kermodprimepow(M,n) =
{
  my(e,p,K,Kfin,pid);
  Kfin = matid(matsize(M)[2]);
  e = isprimepower(n,&p);
  pid = p*matid(matsize(M)[2]);
  for(i=1,e,
    K = liftint(matker(Mod(M,p)));
    K = matconcat([pid,K]);
    K = matimagemod(K,n);
    Kfin = (Kfin*K)%n;
    M = ((M*K)%n)\p;
  );
  Kfin = matimagemod(Kfin,n);
  Kfin
};

\\cardinal of subgroup of (Z/d)^m represented by Howell form H
cardmod(H,d) =
{
  my(m,n,card=1,i);
  [m,n] = matsize(H);
  if (m*n==0, return(1));
  i=m;
  forstep(j=n,1,-1,
    while(H[i,j]==0,i--);
    card *= d\H[i,j];
  );
  card
};

\\p-part / p'-part
splitcycsylow(cyc,p) =
{
  my(cycp,cycc);
  cycp = vector(#cyc,i,1);
  cycc = vector(#cyc,i,1);
  for(i=1,#cyc,
    cycp[i] = p^valuation(cyc[i],p);
    cycc[i] = cyc[i] \ cycp[i];
  );
  cycp = [d | d <- cycp, d!=1];
  cycc = [d | d <- cycc, d!=1];
  [cycp, cycc]
};

\\assumed to be coprime
mergecyc(cyc1,cyc2) =
{
  my(n);
  n = max(#cyc1,#cyc2);
  cyc1 = concat(cyc1,vector(n,i,1));
  cyc2 = concat(cyc2,vector(n,i,1));
  vector(n,i,cyc1[i]*cyc2[i])
};

cycsimplify(cyc,{d=0}) =
{
  [di | di <-apply(c->gcd(d,c),cyc), di!=1]
};


/*     IV) Number fields utilities         */

\\Minkowski bound
minkow(D,n,{r2=-1}) =
{
  if(r2<0,if(n%2,r2=0,r2=n\2));
  sqrt(abs(D))*(4/Pi)^r2*n!/n^n
};
nfminkow(nf) =
{
  floor(minkow(nf.disc,poldegree(nf.pol),nf.r2))
};

bern1chi(G,chi,z) =
{
  my(f);
  [G,chi] = znchartoprimitive(G,chi);
  f = zncharconductor(G,chi);
  sum(r=1,f,chareval(G,chi,r,z)*r)/f
};
hminus(n) =
{
  my(h,G,pol,z,e,o,w);
  if(n%4==2,n/=2);
  if(n==1,return(1));
  w = if(n%2==1,2*n,n);
  h = if(isprimepower(n),1,2) * w;
  G = znstar(n,1);
  e = G.cyc[1];
  pol = polcyclo(e,'x);
  z = Mod('x,pol);
  forvec(chi=[[0,c-1] | c <- G.cyc],
    if(chareval(G,chi,-1)==1/2,
      o = charorder(G,chi);
      h *= -bern1chi(G,chi,[z^(e\o),o])/2
    );
  );
  polcoef(lift(h),0)
};

easynf(pol) =
{
  my(nf,cert,fa);
  if(vprintab,print("pol=",pol));
  fa = poldiscfactors(pol)[2];
  nf = nfinit([pol,fa[,1]]);
  cert = nfcertify(nf);
  if(#cert==0,return(nf));
  warning("easynf: computing nf the hard way!");
  /* Here, could be more clever, but rarely ever reached. */
  nfinit(pol)
};

nfhash3(pol) =
{
  my(fa);
  fa = nfdiscfactors([pol,10^5])[2];
  fa = matconcat([f | f <- Col(fa), f[1] <= 10^5]~);
  if(fa==[;],return(1));
  factorback(fa)
};
\\[degree, signature, abs(disc) at primes <= 10^5]
nfhash(pol) =
{
  my(n,s,d);
  n = poldegree(pol);
  s = polsturm(pol);
  d = nfhash3(pol);
  [n,s,d]
};

\\assume pol sqrfree mod p
\\return a vector of [p,1,alpha,f,pi] representing prime ideals:
\\  - [p,alpha] generates pr
\\  - f is the residue degree
\\  - pi has valuation 0 at pr and 1 at other prime divisors of p
myprimedec(pol,p) =
{
  my(fa,lifa,P,good);
  fa = factormod(pol,p)[,1]~;
  if(#fa==1, return([[p,p,poldegree(pol),1]]));
  lifa = liftint(fa);
  \\ensure generators have valuation 1 at corresponding primes
  while(1,
    P = (factorback(lifa)-pol)\p;
    good=1;
    for(i=1,#fa,
      if(Mod(P,fa[i])==0,good=0;break);
    );
    if(good,break);
    lifa = vector(#lifa,i,liftint(Mod(lifa[i]+p*liftint(random(fa[i])),p^2)));
  );
  vector(#fa,i,[p,1,lifa[i],poldegree(fa[i]),liftint(prod(j=1,#fa,if(j==i,1,fa[j])))]);
}

myidealnorm(polrel,idl) =
{
  my(n,k,a,na=[],d,m);
  [n,k,a] = idl;
  d = poldegree(polrel);
  a = Mod(a,polrel);
  m = n^(d*k+1);
  iferr(
    na = liftall(norm(Mod(a,m)));
  ,E,
    na = norm(a);
    na = liftall(Mod(na,m));
  );
  [n,d*k,na]
};

unitrank(nf) =
{
  nf.r1+nf.r2-1
};
colinfdeg(nf) =
{
  vectorv(nf.r1+nf.r2,i,if(i<=nf.r1,1,2));
};
preMi(bnf) =
{
  M = matconcat([real(bnf[3]),colinfdeg(bnf)]);
  M^(-1)
};
logisunit(Mi,logu) =
{
  my(X,rnd,e);
  X = Mi*logu;
  rnd = round(X,&e);
  if(e>-5, error("logisunit: too low precision! e=",e));
  rnd[1..-2]
};

mykeycx(z) = [abs(imag(z)),real(z),imag(z)];
myinfplaces(pol) =
{
  my(r1,r2,evalr,evalc,mycmpcx);
  r1 = polsturm(pol);
  r2 = (poldegree(pol)-r1)\2;
  if(vprintab,print("signature: ", [r1,r2], " unit rank: ", r1+r2-1));
  if(r1, evalr = polrootsreal(pol), evalr=[]~);
  if(r2,
    evalc = polroots(pol);
    evalc = vecsort(evalc,mykeycx);
    evalc = vector(r2,i,evalc[r1+2*i])~;
  ,\\else
    evalc=[]~
  );
  [r1,r2,concat(evalr,evalc)];
};

\\precision to evaluate h*R from Brauer relation
precbrauerhr(Lbnf,coefsbr) =
{
  vecmax(vector(#Lbnf,i,my(bnf=Lbnf[i][2]);
    expo(max(5,bnf.reg)*max(1,bnf.no/bnf.tu[1]))*2*abs(coefsbr[i])))
    + expo(#Lbnf) + 5;
};

\\precision to compute regulator
precdirectR0(matextru,r0,R00) =
{
  sum(i=1,r0,ceil(expo(norml2(matextru[,i]))/2))
    - exponent(R00) + 2*expo(r0) + 5;
};

whichprime(nfsub,decsub,prsub) =
{
  my(v,x=prsub[3]);
  for(i=1,#decsub,
    v = nfeltval(nfsub,x,decsub[i]);
    if(v>0,return(i));
  );
  0
};

\\compute valuations from subfields
valfromsub(bnfsub,x,isub,S,valdata=0) =
{
  my(data,vals,decsub,respr);
  concat(vector(#S,is,
    data = S[is];
    decsub = data[3][isub][1];
    respr = data[3][isub][2];
    if(valdata==0,
      vals = vector(#decsub,i,nfeltval(bnfsub,x,decsub[i]))
    ,\\else
      vals = vector(#decsub,i,valdata[1][vecsearch(valdata[2],decsub[i])])
    );
    vectorv(#respr,i,vals[respr[i]])
  ))
};

\\compute DL of residue modulo prime ideals from subfields
resfromsub(bnfsub,x,isub,T) =
{
  my(modpr,g,xmod,data,expo,n,q);
  vectorv(#T,it,
    data = T[it];
    q = data[1][1];
    g = data[2];
    [expo,n] = data[3];
    modpr = data[4][isub];
    xmod = nfmodpr(bnfsub,x,modpr);
    if(type(xmod)!="t_INT", xmod = polcoef(xmod.pol,0));
    xmod = Mod(xmod,q);
    znlog(xmod^expo,g,n);
  )
};

\\output: [S-units, matrix of their valuations, sorted S]
mysunits(bnf,S,den) =
{
  my(su,K);
  S = vecsort(S);
  su = bnfunits(bnf,S)[1][1..#S];
  K = matrix(#S,#su,i,j,nfeltval(bnf,su[j],S[i]));
  [su,K,S]
};

fetchbnf(pol,Lbnfdata) =
{
  my(n,s,d,L,isom,typ);
  n = poldegree(pol);
  L = [i | i <- [1..#Lbnfdata], Lbnfdata[i][1][1]==n];
  if(#L == 0, return(0));
  s = polsturm(pol);
  L = [i | i <- L, Lbnfdata[i][1][2]==s];
  if(#L == 0, return(0));
  d = nfhash3(pol);
  L = [i | i <- L, Lbnfdata[i][1][3]==d];
  if(#L == 0, return(0));
  foreach(L,i,
    if(getpol(Lbnfdata[i][2])==pol,return([Lbnfdata[i][2],variable(pol),variable(pol)]));
  );
  for(j=1,#L,
    my(i=L[j]);
    typ = Lbnfdata[i][2][1];
    if(typ==0,
      isom = nfisisom(Lbnfdata[i][2][2],pol)
    ,\\else
      isom = nfisisom(getpol(Lbnfdata[i][2]),pol)
    );
    if(isom, return([Lbnfdata[i][2],isom[1],lift(modreverse(Mod(isom[1],pol)))]))
  );
  0
};


/*     V) Brauer class group         */

\\class group at p
\\assume brauer is valid at p
Brauerclgp0(Lbnf,brauer,pk) =
{
  my(Lscyc,mult,cyc,m,co);
  Lscyc = apply(bnf->cycsimplify(getcyc(bnf),pk),Lbnf);
  mult = Map();
  for(i=1,#Lscyc,
    cyc = Lscyc[i];
    co = brauer[i];
    for(j=1,#cyc,
      if(!mapisdefined(mult,cyc[j],&m),
        mapput(mult,cyc[j],co)
      ,\\else
        mapput(mult,cyc[j],m+co)
      )
    );
  );
  mult = Vec(Mat(mult)~);
  mult = [m | m <- mult, m[2]!=0];
  if(#mult==0, [], vecsort(concat([vector(m[2],i,m[1]) | m <- mult, m[2]!=0]),,4))
};

\\class group at d, Lp list of primes corresponding to list of relations
Brauerclgp(Lbnf,Lp,brauer,d) =
{
  my(cyc,Lq,pk);
  Lq = factor(d/prod(i=1,#Lp,p=Lp[i];p^valuation(d,p)))[,1]~;
  cyc = [];
  for(i=1,#Lq,
    p = Lq[i];
    pk = p^valuation(d,p);
    cyc = mergecyc(cyc,Brauerclgp0(Lbnf,brauer[1],pk));
  );
  for(i=1,#Lp,
    p = Lp[i];
    pk = p^valuation(d,p);
    if(pk!=1,
      cyc = mergecyc(cyc,Brauerclgp0(Lbnf,brauer[i],pk));
    );
  );
  cyc
};


/*     VI) Galois, relations and subfields computations         */

\\find a suitable abelian subgroup of the Galois group
abgaloisanalysis(pol) =
{
  my(gal,galgen,U,Ui,cyc,rk,rkbest,rel,relbest,Lsub,sub);
  gal = galoisinit(pol);
  if(!gal, error("The field is not Galois."));
  rel = galoisisabelian(gal);
  if(rel,
    galgen = gal.gen;
  ,\\else: non-abelian
    Lsub = galoissubgroups(gal);
    cardbest=0;
    for(i=1,#Lsub,
      sub = Lsub[i];
      rel = galoisisabelian(sub);
      if(rel,
        rk = #matsnf(rel,4);
        if(rk>rkbest,
          rkbest = rk;
          relbest = rel;
          galgen = sub[1];
        )
      );
    );
    rel = relbest;
  );
  cyc = ZM_snf_group(rel,&U,&Ui);
  /* gal generators <--Ui--  --U--> snf generators */
  if(vprintab,print("galois group: ", cyc));
  [gal,galgen,U,Ui,cyc]
};

abgaloisfixedfield(abgal, K, flag, var) =
{
  my(gal,galgen,Ui,H);
  gal = abgal_gal(abgal);
  galgen = abgal_galgen(abgal);
  Ui = abgal_Ui(abgal);
  H = Ui*K;
  H = vector(#H[1,],i,factorback(galgen,H[,i]));
  galoisfixedfield(gal,H,flag,var)
};

\\[defining pol for subfield, embedding, relative pol]
getsubfield(abgal,K,{var='y},{reduce=0},{emb=1}) =
{
  my(res,redpol,isom,isomi,pol);
  if(emb,
    res = abgaloisfixedfield(abgal, K, 2, var);
    res = [res[1],res[2],res[3][1]*Mod(1,res[1])];
    if(reduce,
      [redpol,isomi] = polredbest(res[1],1);
      isom = lift(modreverse(isomi));
      pol = abgal_gal(abgal).pol;
      res = [redpol, Mod(subst(isom,variable(redpol),res[2]),pol),
        Mod(Pol(apply(c -> subst(lift(c),variable(c),isomi),Vec(res[3])),
        variable(res[3])),redpol)];
    );
  ,\\else
    res = abgaloisfixedfield(abgal, K, 1, var);
    res = subst(res,variable(res),var);
    if(reduce, res = polredbest(res));
    res = [res,0,0]
  );
  res
};

/*
  If p!=0, assume Gal=C*P with C cyclic and P p-Sylow, and write the coefficients
  of the relation coming from the p-Sylow.
*/
getsubfields(abgal,{var='y},{p=0},{reduce=0},{emb=1}) =
{
  my(sub=[], coef=0, r=0, v, valord, ord, C, coefbr = 0, K, cyc);
  cyc = abgal_cyc(abgal);
  if(p,
    r = #cyc;
    v = valuation(factorback(cyc),p);
    C = cyc[1]/p^valuation(cyc[1],p);
  ); 
  if(vprintab,print("generating list"));
  forvec(chi=vector(#cyc,i,[0,cyc[i]-1]),
    K = charker(cyc,chi);
    if(p,
      ord = charorder(cyc,chi);
      valord = valuation(ord,p);
      if(ord!=C*p^valord,next);
      if(valord==0,
        coefbr = (1-(p^r-1)/(p-1));
      ,\\chi_p != 0
        coefbr = if(chi%p!=0,1,1-p^(r-1));
      );
      coef = coefbr/p^(v-valord);
    );
    sub = concat(sub,[[K,[coef,coefbr]]]);
  );
  if(vprintab,print("eliminating duplicates #sub=", #sub));
  sub = Set(sub);
  if(vprintab,print("computing fields, #sub=", #sub));
  sub = vector(#sub,i,
    if(vprintab,print("i=",i,"/",#sub));
    concat(getsubfield(abgal,sub[i][1],var,reduce,emb),sub[i][2])
  ); 
  vecsort(sub,dat->[poldegree(dat[1]),poldisc(dat[1]),polsturm(dat[1])])
};

\\relation from Proposition 2.26
dualfunakurarelation(cyc) =
{
  my(sub=[],Lp,rp,p,H,ord,coef,coefbr,g,h,delta);
  g = vecprod(cyc);
  Lp = factor(cyc[1])[,1];
  rp = vector(#Lp,i,
    p = Lp[i];
    my(j=1);
    while(j<#cyc && cyc[j+1]%p==0, j++);
    j
  );
  forvec(chi=vector(#cyc,j,[0,cyc[j]-1]),
    H = charker(cyc,chi);
    ord = charorder(cyc,chi);
    h = g/ord;
    coefbr = 1;
    for(i=1,#Lp,
      p = Lp[i];
      if(ord%p==0,
        delta=1;
        for(j=1,#cyc,if(cyc[j]%p==0 && chi[j]%p, delta=0; break));
        if(delta, coefbr *= 1-p^(rp[i]-1));
      ,\\else
        coefbr *= -sum(j=1,rp[i]-1,p^j);
      );
    );
    if(coefbr,
      coef = coefbr/h;
      sub = concat(sub,[[H,[coef,coefbr]]]);
    );
  );
  if(vprintab,print("eliminating duplicates #sub=", #sub));
  sub = Set(sub);
  if(vprintab,print("#sub=", #sub));
  sub
};

\\G with two non-cyclic Sylows
\\return a list of subgroups and for each p, a Brauer relation over Z_p
\\relation from Theorem 2.27 (1)
abrelations(cyc) =
{
  my(Lp,p,cycp,cycc,Rels,rel,dat,H,coefbr,coefs);
  Rels = Map();
  Lp = factor(cyc[1])[,1]~;
  for(i=1,#Lp,
    p = Lp[i];
    [cycp,cycc] = splitcycsylow(cyc,p);
    rel = dualfunakurarelation(cycc);
    if(sum(j=1,#rel,rel[j][2])!=[1,1],error("incorrect relation! p=",p," sum=",sum(j=1,#rel,rel[j][2])));
    for(j=1,#rel,
      dat = rel[j];
      H = mathnfmodid(cycp[1]*matconcat([dat[1];vectorv(#cyc-#cycc)]),cyc);
      coefbr = dat[2][2];
      if(!mapisdefined(Rels,H,&coefs),coefs = vector(#Lp));
      coefs[i] = coefbr;
      mapput(Rels,H,coefs);
    );
  );
  Mat(Rels)
};

\\construct all subfields with Galois group C*P
\\with C cyclic and P a non-cyclic p-Sylow of G
getsubfields_CP(abgal,{var='y},{reduce=0},{emb=1}) =
{
  my(rels,cyc,perm);
  cyc = abgal_cyc(abgal);
  rels = abrelations(cyc);
  for(i=1,#rels[,1],
    if(vprintab,print("i=",i,"/",#rels[,1]));
    rels[i,1] = getsubfield(abgal,rels[i,1],var,reduce,emb);
  );
  perm = vecsort(rels[,1],dat->[poldegree(dat[1]),poldisc(dat[1]),polsturm(dat[1])],1);
  vecextract(rels,perm,[1,2])
};


/*     VII) Auxiliary functions for type 1         */

\\assume C*P case
myrootsofunity(pol,Lbnf,p) =
{
  my(w,kinf,ksup,bad,count=0,f,polcyc,nfcyc,q,n=poldegree(pol), disc);
  if(polsturm(pol)>0,return(2));
  w = lcm(vector(#Lbnf,i,Lbnf[i][2].tu[1])); \\from subfields: correct away from p
  kinf = valuation(w,p);
  if(n%(p-1), return(w));
  ksup = valuation(n,p)+1;
  if(ksup==kinf, return(w));
  disc = poldisc(pol);
  if(disc%p, return(w));
  bad = cheaprad(disc);
  w \= p^valuation(w,p);
  while(count<100,
    q = randomprime([10^3,10^5*expo(bad)]);
    if(!(bad%q), next);
    f = factormod(pol,q,1)[1,1];
    ksup = min(ksup, valuation(q^f-1,p));
    if(ksup==kinf, return(w*p^ksup));
    count++;
  );
  if(vprintab,print("kinf=",kinf," ksup=",ksup));
  while(ksup>kinf, \\probably only one iteration
    polcyc = polcyclo(p^ksup);
    nfcyc = nfinit(polcyc);
    if(nfisincl(nfcyc,pol), break);
    ksup--;
  );
  if(vprintab,print("k=",ksup));
  w*p^ksup;
};

maxspecialelt(pol) =
{
  my(s=2,nf);
  while(1,
    if(poldegree(pol)%2^(s-1),break);
    nf = nfinit(galoissubcyclo(2^(s+1),-1));
    if(!nfisincl(nf,pol), break);
    s++
  );
  s
};
\\detect Grunwald-Wang special case
isspecial(pol,Lbnf,p,w,r1,r2) =
{
  my(s,nf);
  if(p!=2, return(0));
  if(w%4==0, return(0));
  s = maxspecialelt(pol);
  if(r1>0, return(s));
  nf = nfinit(galoissubcyclo(2^(s+1),-Mod(5,2^(s+1))^(2^(s-2))));
  if(!nfisincl(nf,pol), return(s));
  0
};

\\identify restrictions of infinite places to subfield
resinfplaces(nf,r1,r2,ro2,emb) =
{
  my(g2,ro,resro2,perm,jbest,r,mul,d);
  g2 = variable(emb);
  emb = liftpol(emb);
  ro = nf.roots;
  resro2 = vector(#ro2, i, subst(emb,g2,ro2[i]));
  perm = vector(#ro2,i,
    r = resro2[i];
    if(imag(r)<0,r=conj(r));
    vecmin(vector(#ro,j,abs(ro[j]-r)),&jbest);
    jbest
  );
  d = poldegree(nf.pol);
  for(j=1,#ro,
    mul = #[i | i <- perm, i==j];
    if(mul != #ro2/d && mul != 2*#ro2/d,
      if(vprintab,print("#ro2: ", #ro2));
      if(vprintab,print("d=",d));
      if(vprintab,print("multiplicities: ", vector(#ro,j,#[i | i <- perm, i==j])));
      error("bug in resinfplaces [wrong multiplicities]")
    )
  );
  perm
};

\\log embedding in K from log embedding in the subfield:
unitmatrix(Lbnf,r1,r2,Lresinfpl) =
{
  Mat(concat(vector(#Lbnf,j,
    vector(unitrank(Lbnf[j][2]),j2,
      vectorv(r1+r2, i, if(Lresinfpl[j][i]<=Lbnf[j][2].r1 && i>r1,2,1)*real(Lbnf[j][2][3][Lresinfpl[j][i],j2]))
    )
  )))
};

increaseT(pol,Lsub,Lnf,T,prodT,nbT,prodS,bad,den,w) =
{
  my(boundq,q,fa,pr,data,prsub,decsub,nfsub,g,modu);
  boundq = 10^3*(1+expo(prodT)+expo(prodS)+expo(bad))*(nbT-#T)*poldegree(pol);
  modu = lcm(den,w);
  while(#T<nbT,
    q = 1+random(boundq)*modu;
    if(!(bad%q) || !(prodS%q) || !(prodT%q), next);
    if(!isprime(q), next);
    fa = factormod(pol,q,1);
    if(fa[1,1]>1, next);
    pr = myprimedec(pol,q)[1];
    sqrtn(Mod(1,q),den,&g);
    data = [pr,g,[(q-1)\den,den],vector(#Lnf,i,
      nfsub = Lnf[i][2];
      prsub = myidealnorm(Lsub[i][3],pr);
      decsub = idealprimedec(nfsub,q);
      prsub = decsub[whichprime(nfsub,decsub,prsub)];
      nfmodprinit(nfsub,prsub)
    )];
    T = concat(T,[data]);
    prodT *= q;
  );
  [T,prodT]
};

increaseS(pol,Lsub,Lbnf,S,prodS,qS,nbS,prodT,bad,disc) =
{
  my(fa,dec,data,nfsub,decsub,respr,prsub,pr);
  boundq = (expo(disc)^3+10^3)*(1+expo(prodT)+expo(prodS)+expo(bad))*(nbS-#S)*poldegree(pol);
  while(1,
    if(#S>=nbS,break);
    q = randomprime(boundq);
    if(!(bad%q) || !(prodT%q) || !(prodS%q), next);
    fa = factormod(pol,q,1);
    if(fa[1,1]>1, next);
    if(!isprime(q),next);
    if(vprintab,print1("    adding q=",q,"... "));
    dec = myprimedec(pol,q);
    data = [q,dec,vector(#Lbnf,i,
      nfsub = Lbnf[i][2];
      decsub = idealprimedec(nfsub,q);
      respr = vectorsmall(#dec,j,
        pr = dec[j];
        prsub = myidealnorm(Lsub[i][3],pr);
        whichprime(nfsub,decsub,prsub)
      );
      [decsub,respr]
    )];
    S = concat(S,[data]);
    qS = q;
    prodS *= q;
    if(vprintab,print("done adding q."));
  );
  [S,prodS,qS]
};

pruneS(S,relp) =
{
  my(m,n,keep=vector(#S),invpivot,i);
  if(vprintab,print("  pruning S"));
  [m,n] = matsize(relp);
  invpivot = vector(n);
  i=m;
  forstep(j=n,1,-1,
    while(i>0 && relp[i,j]==0, i--);
    if(i>0 && relp[i,j]==1, invpivot[j]=i);
  );
  invpivot = Set(invpivot);
  i=1;
  for(k=1,#S,
    for(l=1,#S[k][2],
      if(!vecsearch(invpivot,i),keep[k]=1);
      i++;
    );
  );
  if(vprintab,print("  keep: ", keep));
  [S[i] | i <- [1..#S], keep[i]]
};

\\fundamental units first, then root of unity, then S-units
valresSunits(S,T,Lbnf,subunits,unitcorresp,izp,den) =
{
  my(Mval,Mres,su,Ssub,bnfsub,uc,Stot,Lsu = vector(#Lbnf));
  Stot = sum(i=1,#S,#S[i][2]);
  if(vprintab,print1("  S-units of subfields..."));
  if(#S!=0,
    for(i=1,#Lbnf,
      bnfsub = Lbnf[i][2];
      Ssub = concat(vector(#S,j,S[j][3][i][1]));
      Lsu[i]=mysunits(bnfsub,Ssub,den)
    );
  );
  if(vprintab,print("done."));

  if(vprintab,print1("  valuations..."));
  Mval = matconcat([
    \\units: valuations 0
    matrix(Stot,matsize(subunits)[2]+1),
    \\sunits
    if(#S==0,[;],
      Mat(concat(vector(#Lbnf,i,
        bnfsub = Lbnf[i][2];
        su = Lsu[i];
        vector(#su[1],j,valfromsub(bnfsub,su[1][j],i,S,[su[2][,j],su[3]]))
      )))
    )
  ]);
  if(vprintab,print("done."));

  if(vprintab,print1("  residues and DLs..."));
  Lunits = [bnfunits(bnfsub[2])[1] | bnfsub <- Lbnf];
  Mres = matconcat([
    \\fundamental units
    Mat(vector(#unitcorresp,i,
      uc = unitcorresp[i];
      bnfsub = Lbnf[uc[1]][2];
      resfromsub(bnfsub,Lunits[uc[1]][uc[2]],uc[1],T)
    ))*subunits,
    \\root of unity
    resfromsub(Lbnf[izp][2],Lbnf[izp][2].tu[2],izp,T),
    \\sunits
    if(#S==0,[;],
      Mat(concat(vector(#Lbnf,i,
        bnfsub = Lbnf[i][2];
        su = Lsu[i];
        vector(#su[1],j,resfromsub(bnfsub,su[1][j],i,T))
      )))
    )
  ]);
  if(vprintab,print("done."));

  if(vprintab,print("  Stot: ", Stot));
  if(vprintab,print("  size Mval: ", matsize(Mval)));
  if(vprintab,print("  size Mres: ", matsize(Mres)));
  [Mval,Mres]
};

saturate(S,T,Lbnf,subunits,unitcorresp,izp,den,r1,r2,p,expobound) =
{
    my(Mval,Mres,Mrestot,Mresu,K,indexu,Mvalall);
    \\compute valuations and residues of S-units of subfields
    if(vprintab,print("  computing valuations and residues"));
    [Mval,Mres] = valresSunits(S,T,Lbnf,subunits,unitcorresp,izp,den^2);
    Mrestot = Mres;
    Mres = Mres%den;
    Mresu = Mres[,1..r1+r2];
    \\compute kernels for den-th powers
    if(vprintab,print("  Mresu: ", matsize(Mresu)));
    K = kermodprimepow(Mresu,den);
    if(vprintab,print("  kernel in units: ", matsize(K)));
    \\mod out root of unity component since already counted in w
    if(#K>0, K = matimagemod(K[1..r1+r2-1,],den));
    indexu = cardmod(K,den);
    if(vprintab,print("  indexu = ", indexu, " = ", p, "^", valuation(indexu,p)));
    K = kermodprimepow(matconcat([Mval;Mres]),den);
    if(vprintab,print("  kernel in S-units: ", matsize(K)));
    Mvalall = matconcat([Mval,(Mval*K)\den]);
    relp = matimagemod(Mvalall,expobound);
    if(vprintab,print("  relp: dims=", matsize(relp)));
    hp = expobound^matsize(Mval)[1]\cardmod(relp,expobound);
    if(vprintab,print("  hp = ", hp, " = ", p, "^", valuation(hp,p)));
    [indexu,relp,hp,Mrestot,Mval,K]
};


/*     VIII) Main functions         */
get_primes(pol,{filename=0},{bad=1},{Lbnfdata=[]}) =
{
  my(gal,abgal,cycnc,p,abbnf,Sp,cert);
  if(vprintab,print("\npol=", pol, "\nstarting abelianbnfinit"));
  if(poldegree(pol)==1, return(abelianbnfinit0(pol)));
  abgal = abgaloisanalysis(pol);
  cyc = abgal_cyc(abgal);
  cycnc = vecprod(cyc[2..-1]);
  if(cycnc==1,
    \\return(abelianbnfinit0(pol))
    abbnf = abelianbnfinit0(pol);
    Sp = [];
    FB = abbnf[2][5];
    for(j=1,#FB,
      Sp = concat(Sp,FB[j][1]);
    );
    Sp = vecsort(Set(Sp));
  ,isprimepower(cycnc,&p),
    \\return(abelianbnfinit1(pol,abgal,p,bad,Lbnfdata))
    abbnf = abelianbnfinit1(pol,abgal,p,bad,Lbnfdata);
    Sp = abbnf[length(abbnf)];
  ,/*else: at least two non-cyclic Sylows*/
    abbnf = abelianbnfinit2(pol,abgal,bad,Lbnfdata);
    Sp = abbnf[length(abbnf)];
  );
  \\cert = abelianbnfcertify(abbnf);
  \\[cert, Sp]
  \\system(strprintf("rm %s", filename));

  if(filename!=0,
    write(filename,Sp);
  );
  Sp
};

\\main function
abelianbnfinit(pol,{bad=1},{Lbnfdata=[]}) =
{
  my(gal,abgal,cycnc,p);
  if(vprintab,print("\npol=", pol, "\nstarting abelianbnfinit"));
  if(poldegree(pol)==1, return(abelianbnfinit0(pol)));
  abgal = abgaloisanalysis(pol);
  cyc = abgal_cyc(abgal);
  cycnc = vecprod(cyc[2..-1]);
  if(cycnc==1,
    return(abelianbnfinit0(pol))
  ,isprimepower(cycnc,&p),
    return(abelianbnfinit1(pol,abgal,p,bad,Lbnfdata))
  ,/*else: at least two non-cyclic Sylows*/
    return(abelianbnfinit2(pol,abgal,bad,Lbnfdata))
  );
};

\\denominator 1 relation
abelianbnfinit2(pol,abgal,bad0,Lbnfdata) =
{
  my(LsubC,LsubCP,Lbnf,bad,d,rel,abbnf,brauer,Lp,Lbnfdata2,polsub,k,Sp);
  if(vprintab,print("at least 2 non-cyclic Sylows"));
  LsubCP = getsubfields_CP(abgal,'y,0,0);
  Lp = factor(poldegree(pol))[,1]~;
  brauer = LsubCP[,2]~;
  brauer = vector(#Lp,i,vector(#brauer,j,brauer[j][i]));
  LsubCP = LsubCP[,1]~;
  LsubC = getsubfields(abgal,'z,,1,0);
  if(vprintab,print("computing bnf1"));
  Lbnfdata2 = vector(#LsubC);
  k=0;
  Sp = [];
  for(i=1,#LsubC,
    polsub = LsubC[i][1];
    if(poldegree(polsub)==1 || fetchbnf(polsub,Lbnfdata),next);
    if(vprintab,print1("\ni=",i,"/",#LsubC," "));
    abbnf = abelianbnfinit(polsub,Lbnfdata);
    k++;
    Lbnfdata2[k] = [nfhash(polsub),abbnf];
  );
  Lbnfdata = vecsort(concat(Lbnfdata,Lbnfdata2[1..k]),1);
  Lbnf = vector(#LsubCP,i,
    if(vprintab,print1("\ni=",i,"/",#LsubCP," "));
    abbnf = abelianbnfinit(LsubCP[i][1],,Lbnfdata);

    if(abbnf[1] == 0,
      FB = abbnf[2][5];
      for(j=1,#FB,
        Sp = concat(Sp,FB[j][1]);
      );
      Sp = vecsort(Set(Sp));
    ,\\else
      Sp = vecsort(Set(concat(Sp, abbnf[length(abbnf)])));
    );

    abbnf
  );
  d = lcm(apply(getexpo,Lbnf));
  if(vprintab,print("\n", apply(getcyc,Lbnf)," d=", d));
  [2,Brauerclgp(Lbnf,Lp,brauer,d),Lbnf,pol,Lbnfdata,abgal_cyc(abgal),Sp];
};

\\p-power denominator relation
abelianbnfinit1(pol,abgal,p,bad0,Lbnfdata) =
{
  my(Lsub,Lbnf,d,dc,bad,hc,coefs,den,coefsbr,w,hR,r1,r2,ro,Lresinfpl,units,
    Ubasis,normemb,normindices,R00,R0,check,nbT,nbS,qS,prodT,prodS,T,S,Mval,K,
    indexu,R1,hp,expobound,relp,subunits,denemb,unitcorresp,izp,snfc,snfp,
    cyctot,disc,f,spe,Up,Mrestot,abbnf,matextru,detubasis,detectoo=0,sep,rosub,
    bprec,emb,LMi,precu,prechr,r0,precR0,checksum,Sp);
  if(vprintab,print("non-cyclic galois group"));
  Lsub = getsubfields(abgal,'z,p,1);
  if(vprintab,print("number of subfields: ", #Lsub));
  coefs=[x[4] | x <- Lsub];
  checksum = sum(i=1,#coefs,coefs[i]);
  if(vprintab,print("coefs norm rel: ", coefs, " sum=", checksum, " (must be 1)"));
  if(checksum!=1, error("incorrect norm relation!"));
  den = denominator(coefs);
  coefs *= den;
  if(vprintab,print("den=", den));
  coefsbr = [x[5] | x <- Lsub];
  checksum = sum(i=1,#coefsbr,coefsbr[i]);
  if(vprintab,print("coefs brauer rel: ", coefsbr, " sum=", checksum, " (must be 1)"));
  if(checksum!=1, error("incorrect Brauer relation!"));

  Lbnf = vector(#Lsub,i,
    if(vprintab,print1("\ni=",i,"/",#Lsub," "));
    abbnf = fetchbnf(Lsub[i][1],Lbnfdata);
    if(abbnf,
      if(vprintab,print("found in list."));
      if(abbnf[2]!=x,
        Lsub[i][1] = getpol(abbnf[1]);
        Lsub[i][2] = subst(abbnf[2],variable(abbnf[2]),Lsub[i][2]);
        Lsub[i][3] = Mod(Pol(apply(c ->
          subst(lift(c),variable(c),Mod(abbnf[3],Lsub[i][1])), Vec(Lsub[i][3])),
          variable(Lsub[i][3])),Lsub[i][1]);
      );
      abbnf[1]
    ,\\else
      abbnf = abelianbnfinit0(Lsub[i][1]);
      abbnf
    )
  );

  disc = factorback(vector(#Lbnf,i,Lbnf[i][2].disc),coefsbr);
  f = poldisc(pol)/disc;
  
  check = issquare(f,&f);
  if(vprintab,printf("disc = %Ps\nf = %Ps\n", disc, f));
  if(!check, error("disc pol / disc is not square!"));

  d = lcm(apply(getexpo,Lbnf));
  dc = d/p^valuation(d,p);
  if(vprintab,print(apply(getcyc,Lbnf)," d=", d, " dc=", dc));
  bad = vector(#Lsub,i,poldisc(Lsub[i][1]));
  bad = concat([bad,[disc,f]]);
  bad = cheaprad(lcm(concat(apply(cheaprad,bad),bad0)));
  if(vprintab,print("bad=", bad));

  \\compute p'-part of class group
  snfc = Brauerclgp(Lbnf,[p],[coefsbr],dc);
  hc = vecprod(snfc);

  Sp = [];
  for(i=1,#Lbnf,
    FB = Lbnf[i][2][5];
    for(j=1,#FB,
      Sp = concat(Sp,FB[j][1]);
    );
  );
  Sp = Set(Sp);
    
  \\compute number of roots of unity
  w = myrootsofunity(pol,Lbnf,p);
  if(vprintab,print("w=", w));

  \\compute h*R using subfields
  prechr = precbrauerhr(Lbnf,coefsbr);
  if(prechr>bitprecision(Lbnf),
    if(vprintab,print("increasing prec! bitprec(Lbnf):",bitprecision(Lbnf),
      " prechr=",prechr));
    localbitprec(prechr);
    for(i=1,#Lbnf,Lbnf[i][2]=nfnewprec(Lbnf[i][2]));
  );
  hR = factorback(vector(#Lbnf,i,my(bnf=Lbnf[i][2]); bnf.no*bnf.reg/bnf.tu[1]),coefsbr)*w;
  if(vprintab,print("hR=", precision(hR,30)));
  [r1,r2,ro] = myinfplaces(pol);

  \\detect special case of GW
  spe = isspecial(pol,Lbnf,p,w,r1,r2);
  if(vprintab,print("special field? ", spe));
  if(spe && (den^2)%(2^(spe+1))==0,
    detectoo = 1;
    warning("Grunwald-Wang special field: infinite loop possible"));

  \\compute restrictions of infinite places
  bprec = bitprecision(ro);
  for(i=1,#Lbnf,
    rosub = Lbnf[i][2].nf.roots;
    if(#rosub==1,next);
    sep = vecmax([-expo(abs(rosub[i]-rosub[j])) | i <- [1..#rosub]; j <- [i+1..#rosub]]);
    sep = max(0,2+sep)+5;
    emb = liftpol(Lsub[i][2]);
    sep += vecmax([preceval(emb,r) | r <- ro]);
    if(sep>bprec,bprec=sep);
  );
  if(vprintab,print("resinfplaces: bprec=",bprec));
  localbitprec(bprec);
  [r1,r2,ro] = myinfplaces(pol);
  Lresinfpl = vector(#Lsub,i,resinfplaces(Lbnf[i][2].nf,r1,r2,ro,Lsub[i][2]));

  \\compute regulator of image of units from subfields
  units = unitmatrix(Lbnf,r1,r2,Lresinfpl);
  \\compute a basis of the group of subfield units
  LMi = vector(#Lbnf,i,preMi(Lbnf[i][2]));
  precu = vecmax(vector(#LMi,i,expo(norml2(LMi[i]))));
  precu += vecmax(abs(apply(exponent,units)));
  precu += 2*expo(r1+2*r2) + 5;
  if(precu>bitprecision(Lbnf),
    if(vprintab,print("increasing prec! bitprec(Lbnf):",bitprecision(Lbnf),
      " precu=",precu));
    localbitprec(precu);
    for(i=1,#Lbnf,Lbnf[i][2]=nfnewprec(Lbnf[i][2]));
    units = unitmatrix(Lbnf,r1,r2,Lresinfpl);
    LMi = vector(#Lbnf,i,preMi(Lbnf[i][2]));
  );
  normemb = Mat(vector(#units,j,
    \\norms to all subfields
    concat(vector(#Lsub,i,
      my(lognormu = vectorv(unitrank(Lbnf[i][2])+1));
      for(k=1,r1+r2,lognormu[Lresinfpl[i][k]]+=units[k,j]);
      logisunit(LMi[i],lognormu)
    ));
  ));
  \\compute independent subset of the units
  forprime(ell=100,oo,
    normindices = matindexrank(Mod(normemb,ell))[2];
    if(#normindices == r1+r2-1,
      if(vprintab,print("prime used for independent subset of units: ", ell));
    break);
  );
  if(vprintab,print("indices: ", normindices));
  matextru = vecextract(units,[1..r1+r2-1],normindices);
  r0 = matsize(matextru)[1];
  R00 = abs(matdet(matextru));
  precR0 = precdirectR0(matextru,r0,R00);
  if(precR0>bitprecision(Lbnf),
    if(vprintab,print("increasing prec! bitprec(Lbnf):",bitprecision(Lbnf),
      " precR0=",precR0));
    localbitprec(precR0);
    for(i=1,#Lbnf,Lbnf[i][2]=nfnewprec(Lbnf[i][2]));
    units = unitmatrix(Lbnf,r1,r2,Lresinfpl);
    matextru = vecextract(units,[1..r1+r2-1],normindices);
    R00 = abs(matdet(matextru));
  );

  normemb = matsolve(vecextract(normemb,normindices),normemb);
  denemb = denominator(normemb);
  if(vprintab,print("denemb: ", denemb));
  Ubasis = mathnf(denemb*normemb)/denemb;
  detubasis = matdet(Ubasis);
  if(vprintab,print("index: ", detubasis));
  R0 = R00*detubasis;
  if(vprintab,print("R0=", precision(R0,30))); \\regulator of units of subfields before saturation

  \\basis of units from subfields mod n, expressed in terms of the units of subfields
  matimagemod(denemb*normemb,den*p^valuation(denemb,p),&subunits);
  if(vprintab,print("normemb: ", matsize(normemb)));
  if(vprintab,print("subunits:", matsize(subunits)));
  unitcorresp = concat(vector(#Lsub,i,vector(unitrank(Lbnf[i][2]),j,[i,j])));

  \\subfield containing the root of unity of maximal p-power order
  vecmax(vector(#Lbnf,i,valuation(Lbnf[i][2].tu[1],p)),&izp);

  \\bound on the exponent of Cl(K)_p
  expobound=p^vecmax(vector(#Lbnf,i,if(Lbnf[i][2].no==1,0,valuation(Lbnf[i][2].cyc[1],p))));
  expobound *= den;
  expobound *= p;
  if(vprintab,print("expobound = ",expobound," = ",p,"^",valuation(expobound,p)));
  if(vprintab,print("den = ", den, " = ",p,"^",valuation(den,p)));

  \\initialise a T that hopefully defines an embedding of the Selmer group Sel_den(K)
  if(vprintab,print1("initialising T..."));
  T = [];
  nbT = r1+r2+10;
  [T,prodT] = increaseT(pol,Lsub,Lbnf,T,1,nbT,1,bad,den^2,w);
  if(vprintab,print("done."));

  \\initialise an S that hopefully generates Cl(K)_p
  S = [];
  nbS = 0;
  prodS = 1;
  qS = 1;

  check = oo;
  while(1,
    if(vprintab,print("\nnbT=", nbT));
    if(vprintab,print("nbS=", nbS, " total nb primes=", sum(i=1,#S,#S[i][2])));
    [indexu,relp,hp,Mrestot,Mval,K] = saturate(S,T,Lbnf,subunits,unitcorresp,
      izp,den,r1,r2,p,expobound);
    \\compute corresponding hR and check
    R1 = R0/indexu;
    check=hR/(R1*hc*hp);
    if(vprintab,print("  check: ",p,"^",round(log(check)/log(p))," (",precision(check,30),
    " ~ ", bestappr(check),")"));

    if(check<0.7, error("bug: non-integral check: ", check));
    if(check>1.4,
      if(detectoo>0,
        if(check<3, detectoo++);
        if(detectoo>3, warning("probable infinite loop detected."));
      );
      nbT = ceil(1.05*nbT);
      nbS = round(1.3*nbS);
      if(nbS==0, nbS=2);
      nbS += 1;
      S = pruneS(S,relp);
      if(vprintab,print("  increasing S... "));
      [S,prodS,qS] = increaseS(pol,Lsub,Lbnf,S,prodS,qS,nbS,prodT,bad,disc);
      if(vprintab,print1("  done.\n  increasing T... "));
      [T,prodT] = increaseT(pol,Lsub,Lbnf,T,prodT,nbT,prodS,bad,den^2,w);
      if(vprintab,print("done."));
    ,\\else
      break
    );
  );

  for(i=1,#S,
    q = S[i][1];
    Sp = concat(Sp,q);
  );
  Sp = vecsort(Set(Sp));

  \\compute class group structure
  snfp = ZM_snf_group(relp,&Up);
  if(vprintab,print("snfp = ",snfp));
  cyctot = mergecyc(snfc,snfp);
  if(vprintab,print("cyctot = ",cyctot));

  [ 1,          \\1
    cyctot,     \\2
    pol,        \\3
    Lsub,       \\4
    Lbnf,       \\5
    snfc,       \\6
    0,          \\7
    dc,         \\8
    snfp,       \\9
    0,          \\10
    0,          \\11
    0,          \\12
    Up,         \\13
    coefs,      \\14
    S,          \\15
    T,          \\16
    den,        \\17
    disc,       \\18
    p,          \\19
    0,          \\20
    0,          \\21
    lcm([bad,prodS,prodT]), \\22
    coefsbr,    \\23
    [r1,r2],    \\24
    w,          \\25
    matextru,   \\26
    R00,        \\27
    detubasis,  \\28
    Lresinfpl,  \\29
    normindices,\\30
    hp*hc/indexu,    \\31
    Sp
  ]
};

\\base case: cyclic Galois group
abelianbnfinit0(pol) =
{
  my(nf,bnf,prec=default(realprecision));
  localprec(100);
  if(vprintab,print("base case, starting bnfinit"));
  nf = easynf(pol);
  if(vprintab,print("sig=",nf.sign," disc=",nf.disc," ~ 2^",exponent(nf.disc)));
  bnf = bnfinit(nf,1);
  if(vprintab,print("cyc=",bnf.cyc));
  if(vprintab,print1("increasing precision..."));
  localprec(max(100,prec));
  bnf = nfnewprec(bnf);
  if(vprintab,print("done."));
  [0,bnf];
};


/*     XI) Certification         */
\\{iferr(bnfcertify(bnfinit('x),L);
\\  read("certifyfast.gp"),E,
\\  read("certifyslow.gp")
\\)};

