(* GST ORIGINAL PART-I Z=Z0+N(Z0), not a surrogate.
   Exact ORIGINAL four-carry/three-trit U, rational CM J,
   Wave-I actual SURVIVE M, original mixed seed v.
   In the author's notation N is a cycle OPERATOR whereas n is its
   natural iteration count; the new cardinal world index is separate.

   For all rational source strengths lambda:
   K(F_lambda, (I+F_lambda)v)=(I+F_lambda) K(F_lambda,v).

   Symbolically:
   det(I+F_lambda)=(5+4lambda)(6(lambda+2)^2+1).
   det K(v)=-4lambda^2(1+lambda)P8(lambda)P9(lambda),
   where P8 mod 3 and P9 mod 13 have no roots and their leading
   coefficients are units at the respective primes.
   Hence expanded source is cyclic for EXACTLY
      lambda in Q\{0,-1,-5/4}.
   The factorization and matrix identity checked EXACTLY, not
   inferred from a finite sweep.
*)
ClearAll[cells,idx,sh,mir,sgn,src,u,j,m,seed,f,mat,matExpanded,
  detBase,detExpanded,detI,p8,p9,q8res,q9res,spot,output];
cells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
idx[a_]:=First@FirstPosition[cells,a];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sgn[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{x=Mod[Quotient[c,2]+2d,3],y},
 y=Mod[Mod[c,2]+2x,3];
 Boole[d==2]Boole[x==2]+Boole[x==2]Boole[y==2]];
u=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cells[[i]]]*Boole[k==idx[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cells];
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
f=u+j+lambda m;
mat=Transpose[NestList[f.#&,seed,11]];
matExpanded=Transpose[NestList[f.#&,seed+f.seed,11]];
detBase=Det[mat];detExpanded=Det[matExpanded];
detI=Det[IdentityMatrix[12]+f];
p8[x_]:=411701+899200 x-342272 x^2-123812 x^3-14492 x^4-25296 x^5+4672 x^6-832 x^7+256 x^8;
p9[x_]:=12176+45312 x+72685 x^2+59539 x^3+15088 x^4-15320 x^5-13120 x^6-1376 x^7+1984 x^8+640 x^9;
q8res=Table[Mod[p8[k],3],{k,0,2}];
q9res=Table[Mod[p9[k],13],{k,0,12}];
spot=Table[<|"lambda"->x,"rankBase"->MatrixRank[mat/.lambda->x],
"rankExpanded"->MatrixRank[matExpanded/.lambda->x],
"detExpanded"->(detExpanded/.lambda->x)|>,{x,{-5/4,0,-1,1,5/3}}];
output=<|
"originalU5"->(MatrixPower[u,5]==IdentityMatrix[12]),
"originalJ2"->(j.j==-IdentityMatrix[12]),
"originalCMcommutesNavigation"->(u.j==j.u),
"fullMatrixIdentity"->(Expand[matExpanded-(IdentityMatrix[12]+f).mat]==ConstantArray[0,{12,12}]),
"originalBaseDetIdentity"->(Expand[detBase+4lambda^2(1+lambda)p8[lambda]p9[lambda]]===0),
"expandedDetIdentity"->(Expand[detExpanded-detI detBase]===0),
"exactInvertibilityFactor"->Factor[detI],
"completedSquareFactorProof"->(Expand[detI-(5+4lambda)(6(lambda+2)^2+1)]===0),
"P8noRootModulo3"->(q8res=={2,1,2}),
"P9noRootModulo13"->FreeQ[q9res,0],
"exactExceptionalStrengthCases"->spot,
"allPassed"->(MatrixPower[u,5]==IdentityMatrix[12]&&j.j==-IdentityMatrix[12]&&
 u.j==j.u&&Expand[matExpanded-(IdentityMatrix[12]+f).mat]==ConstantArray[0,{12,12}]&&
 Expand[detBase+4lambda^2(1+lambda)p8[lambda]p9[lambda]]===0&&
 Expand[detExpanded-detI detBase]===0&&
 Expand[detI-(5+4lambda)(6(lambda+2)^2+1)]===0&&
 q8res=={2,1,2}&&FreeQ[q9res,0]&&
 MatrixRank[matExpanded/.lambda->(-5/4)]==11&&
 MatrixRank[matExpanded/.lambda->1]==12)
|>;
Print[output];output