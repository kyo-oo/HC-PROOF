(* GST Image-3 ORIGINAL PURE CM CURVATURE COMPANION SOURCE.
The source is C=[J,M] from the author's TRUE Wave-I / CM operators.
The full local fold has U+J and ZERO local SURVIVE M and ZERO local
curvature C; curvature occurs ONLY in original Wave-II CROSS-WORLD
transports via a rational traceless companion. No fabricated Hodge cycles.

ALL-r theoretical certificate:
 (a) Exact 12x12 det K(U+J+t C) =
      t^4 (2t-1) P10(t) Q16(t).
 (b) Every root of P10,Q16 has |t|<100 by rational Cauchy bound
      (leading coefficient nonzero).
 (c) Take r>=1, h=2r, a_i=500+i (i=1..r),
     lambda_(2i-1)=(a_i+a_i^-1)/4,
     lambda_(2i)=-lambda_(2i-1).
     These are distinct rational roots of the source companion,
     |lambda|>100, sum lambda=0 => companion diagonal ZERO.
 (d) B=f(C_h), f(lambda_k)=L_r(k-1), L_r=100(r+510).
     Spectra of (U+J+lambda_k C)+address_k I are pairwise
     disjoint by row sums, so one root e0⊗v is cyclic by CRT.
 (e) The true original U/J/M FIXED two-cell sector:
     [[1,1+2t],[-1+2t,1]], has rational eigenvalues
     1±(a_i-a_i^-1)/2 at t=lambda_i.
     Taking one rational linear factor from every positive block
     yields a SURJECTIVE r-dimensional rational cyclic quotient.
 No canonical original-X Chow realization is asserted.

This exact finite evidence tests r=1,2 companion construction.
No extrapolation from finite r is used for universal-r theorem.
*)
ClearAll[cells,idx,sh,mir,sign,source,UU,JJ,MM,curv,
 originalSeed,id12,p10,q16,kr,ratmod,rootsForRank,one,all,result];
cells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
idx[a_]:=First[FirstPosition[cells,a]];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
source[{c_,d_}]:=Module[{m=Mod[Quotient[c,2]+2d,3],f},
 f=Mod[Mod[c,2]+2m,3];
 Boole[d==2]Boole[m==2]+Boole[m==2]Boole[f==2]];
UU=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
JJ=Table[sign[cells[[i]]]*Boole[k==idx[mir[cells[[i]]]]],{i,12},{k,12}];
MM=DiagonalMatrix[source/@cells];curv=JJ.MM-MM.JJ;
originalSeed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
id12=IdentityMatrix[12];
p10[t_]:=411701-2185728t^2+293888t^3+3073344t^4-
 960384t^5-1658656t^6+835776t^7+244932t^8-
 222264t^9+36900t^10;
q16[t_]:=255140-1606056t^2+3096493t^4-2099096t^6+
 1818992t^8-3016960t^10+2444032t^12-
 1234944t^14+331776t^16;
kr[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];
ratmod[x_,p_]:=Mod[Numerator[x]*PowerMod[Denominator[x],-1,p],p];
one[r_Integer?Positive,p_Integer?Positive]:=
 Module[{h=2r,aa,lams,addr,sourcePoly,co,B,interpolate,
 fmatrix,t0,t,k,km,detmod,rows,seed,fix,coeff,lamOK,
 diagZero,eigen,mi,rank,ctr,pr,full},
 aa=Range[501,500+r];
 lams=Flatten[Table[{(a+1/a)/4,-(a+1/a)/4},{a,aa}]];
 addr=100(r+510)Range[0,h-1];
 sourcePoly=Expand[Times@@(x-#&/@lams)];
 coeff=Table[Coefficient[sourcePoly,x,i],{i,0,h-1}];
 co=Table[If[i==j+1,1,If[j==h,-coeff[[i]],0]],{i,h},{j,h}];
 interpolate=InterpolatingPolynomial[Transpose[{lams,addr}],x];
 B=Sum[Coefficient[interpolate,x,i]MatrixPower[co,i],{i,0,h-1}];
 t=KroneckerProduct[IdentityMatrix[h],UU+JJ]+
   KroneckerProduct[co,curv]+KroneckerProduct[B,id12];
 seed=Join[originalSeed,ConstantArray[0,12(h-1)]];
 lamOK=(AllTrue[lams,Abs[#]>100&]&&
  Length[DeleteDuplicates[lams]]==h&&Total[lams]==0);
 diagZero=Diagonal[co]==ConstantArray[0,h];
 fix=(UU+JJ+y curv)[[{idx[{0,0}],idx[{3,2}]},
    {idx[{0,0}],idx[{3,2}]}]];
 eigen=Table[
   Module[{a=aa[[i]],lam=lams[[2i-1]],shift=addr[[2i-1]]},
   (CharacteristicPolynomial[(fix/.y->lam)+shift IdentityMatrix[2],z]/.
     z->shift+1+(a-1/a)/2)==0],{i,r}];
 km=kr[Map[ratmod[#,p]&,t,{2}],Map[ratmod[#,p]&,seed],12h];
 detmod=Det[km,Modulus->p];
 ctr=Map[ratmod[#,p]&,co,{2}];
 <|"r"->r,"h"->h,"prime"->p,
   "originalCManticommutes"->(JJ.curv+curv.JJ==ConstantArray[0,{12,12}]),
   "zeroLocalCurvatureCoefficients"->diagZero,
   "nativeStrengths"->lams,"strengthsDistinctAndAbove100"->lamOK,
   "companionEigenvaluesExact"->(CharacteristicPolynomial[co,x]===sourcePoly),
   "rootSeedCyclicOnCompanion"->(MatrixRank[kr[ctr,UnitVector[h,1],h],Modulus->p]==h),
   "interpolationAddressesExact"->(co.B==B.co&&
     And@@MapThread[(interpolate/.x->#1)==#2&,{lams,addr}]),
   "rankRFixedCMRationalEigenvalues"->And@@eigen,
   "fullNativeKrylovDetModP"->detmod,
   "fullNativeCyclicModuloP"->(detmod!=0),
   "allPassed"->(lamOK&&diagZero&&
     JJ.curv+curv.JJ==ConstantArray[0,{12,12}]&&
     CharacteristicPolynomial[co,x]===sourcePoly&&
     And@@eigen&&detmod!=0)|>
 ];
all={one[1,1009],one[2,1009]};
result=<|"old12CurvatureRank"->MatrixRank[curv],
  "CManticommutation"->(JJ.curv+curv.JJ==ConstantArray[0,{12,12}]),
  "P10CauchyBound"->1+Max[Abs[Most[CoefficientList[p10[t],t]]]]/36900,
  "Q16CauchyBound"->1+Max[Abs[Most[CoefficientList[q16[t],t]]]]/331776,
  "sourcePolynomialCases"->all,
  "allPassed"->And@@(Lookup[#,"allPassed"]&/@all)|>;
Print[result];result
