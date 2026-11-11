(* OWNER'S IMAGE-1 Z=Z0+N Z0 + IMAGE-3 true all-h native
   zero-local-SURVIVE companion theorem.

   The full ORIGINAL 12-cell U,J,M and one first-world mixed seed
   are used; no invented spatial Hodge model.
   h original Wave-II worlds: C companion with diag(C)=0, B=f(C)
   exact 10-spaced navigation spectral address, true fold
      F_h=I_h \otimes (U+J)+C\otimes M+B\otimes I_12.

   Test the author's TRANSFORMED original source seed:
      w'=w+F_h w.
   Exact identity:
      Krylov(F_h,w')=(I+F_h)*Krylov(F_h,w).
   Original full-n h-wave cyclicity plus invertibility of (I+F_h)
   => transformed full cyclicity; associated anti-diagonal rational
   moment detector gives Hankel det +1 (n=12h).

   This computation checks cases h=2 and h=3; the ALL h>=2 theorem
   follows from original companion CRT and spectrum separation:
      for the original lambda_i small enough, the address0 block
      has det(I+U+J+lambda_i*M)
      =(5+4lambda_i)(6(lambda_i+2)^2+1)!=0,
      while all address>=10 blocks are invertible by ||U+J+lambda_i M||∞<4.
   Invertible total fold I+F_h preserves full original root cyclicity.
*)
ClearAll[cells,idx,sh,mir,sign,source,u,j,m,v,id12,run,rows,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
idx[q_]:=First[FirstPosition[cells,q]];
sh[{a_,b_}]:={Quotient[a+4b,3],Mod[a+4b,3]};
mir[{a_,b_}]:={3-a,2-b};
sign[{a_,b_}]:=If[MemberQ[{0,1,3,4,5,9},a+4b],1,-1];
source[{a_,b_}]:=Module[{mid=Mod[Quotient[a,2]+2b,3],out},
out=Mod[Mod[a,2]+2mid,3];
Boole[b==2]Boole[mid==2]+Boole[mid==2]Boole[out==2]];
u=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sign[cells[[i]]]*Boole[k==idx[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[source/@cells];id12=IdentityMatrix[12];
v=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
run[lambda_List]:=Module[
 {h=Length[lambda],p,co,sourceC,addressB,F,root,expanded,n,K,Kexpanded,
  orbitNew,probe,detI,specFactors,checked},
 p=Expand[Times@@(x-#&/@lambda)];co=CoefficientList[p,x];
 sourceC=ConstantArray[0,{h,h}];
 Do[sourceC[[i+1,i]]=1,{i,1,h-1}];
 Do[sourceC[[i,h]]=-co[[i]],{i,1,h}];
 addressB=Sum[10(i-1)*Fold[Dot,IdentityMatrix[h],
   Table[(sourceC-lambda[[jj]] IdentityMatrix[h])/
      (lambda[[i]]-lambda[[jj]]),
      {jj,Complement[Range[h],{i}]}]],{i,1,h}];
 F=KroneckerProduct[IdentityMatrix[h],u+j]+
   KroneckerProduct[sourceC,m]+
   KroneckerProduct[addressB,id12];
 root=Join[v,ConstantArray[0,12(h-1)]];
 expanded=root+F.root; n=12h;
 K=Transpose[NestList[F.#&,root,n-1]];
 Kexpanded=Transpose[NestList[F.#&,expanded,n-1]];
 detI=Det[IdentityMatrix[n]+F];
 specFactors=Product[Det[(1+10(i-1))*id12+u+j+lambda[[i]]m],
   {i,1,h}];
 checked=(Kexpanded==(IdentityMatrix[n]+F).K);
 orbitNew=NestList[F.#&,expanded,n-1];
 probe=LinearSolve[Transpose[Kexpanded],UnitVector[n,n]];
 <|"h"->h,"lambda"->lambda,"noLocalOriginalSurviveSource"->(
  Diagonal[sourceC]==ConstantArray[0,h]),
 "oneRootOriginalFullRank"->(MatrixRank[K]==n),
 "expandedImage1FullRank"->(MatrixRank[Kexpanded]==n),
 "exactImage1KrylovMatrixIdentity"->checked,
 "detIplusNativeFullFNonzero"->(detI!=0),
 "exactSpectralBlockFactorization"->(detI==specFactors),
 "firstNExpandedMomentReadouts"->(probe.#&/@orbitNew),
 "exactAntidiagonalDetector"->(
  (probe.#&/@orbitNew)==Join[ConstantArray[0,n-1],{1}]),
 "allPassed"->(Total[lambda]==0&&
  Diagonal[sourceC]==ConstantArray[0,h]&&
  MatrixRank[K]==n&&MatrixRank[Kexpanded]==n&&checked&&
  detI!=0&&detI==specFactors&&
  (probe.#&/@orbitNew)==Join[ConstantArray[0,n-1],{1}])|>];
rows={run[{1/2,-1/2}],run[{1/2,1/3,-5/6}]};
result=<|"cases"->rows,"allPassed"->And@@(Lookup[#,"allPassed"]&/@rows)|>;
Print[result];result