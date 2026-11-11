(* Original GST IMAGE-3: Hodge/Poincare complement, original CM
   cmMat, SURVIVE massMat, all on the owner's 4x3 physical information carrier.

   dualMat u(c)=u(worldDual(c)), worldDual(c,d)=(3-c,2-d).
   phaseMat u(c)=original cmSign(c) u(c) (±1).
   Original cmMat from GSTGraphV2CMWaveFusion is exactly phaseMat.dualMat.

   Exact operator relations:
   dualMat²=I, phaseMat²=I, cmMat²=-I, dualMat.cmMat=-cmMat.dualMat;
   phaseMat.massMat=massMat.phaseMat;
   [cmMat,massMat]=phaseMat.[dualMat,massMat].
   Rank[phaseMat.[dualMat,massMat]]=rank[dualMat,massMat]=rank[cmMat,massMat]=6.

   All matrix entries are EXACT rationals. No metric-dependent
   analytic Hodge star or unknown Chow correspondences assumed.
*)
ClearAll[cells,idx,shuffle,dual,sgn,src,dualMat,phaseMat,cmMat,massMat,navMat,comm,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
idx[c_]:=First@FirstPosition[cells,c];
shuffle[{a_,b_}]:={Quotient[a+4b,3],Mod[a+4b,3]};
dual[{a_,b_}]:={3-a,2-b};
sgn[{a_,b_}]:=If[MemberQ[{0,1,3,4,5,9},a+4b],1,-1];
src[{a_,b_}]:=Module[{k=Mod[Quotient[a,2]+2b,3],l},
l=Mod[Mod[a,2]+2k,3];
Boole[b==2]Boole[k==2]+Boole[k==2]Boole[l==2]];
dualMat=Table[Boole[k==idx[dual[cells[[i]]]]],{i,12},{k,12}];
phaseMat=DiagonalMatrix[sgn/@cells];
cmMat=phaseMat.dualMat;
navMat=Table[Boole[k==idx[shuffle[cells[[i]]]]],{i,12},{k,12}];
massMat=DiagonalMatrix[src/@cells];
comm[x_,y_]:=x.y-y.x;
result=<|"originalWorldDual2"->(dualMat.dualMat==IdentityMatrix[12]),
"originalCMphase2"->(phaseMat.phaseMat==IdentityMatrix[12]),
"originalComplexJ2"->(cmMat.cmMat==-IdentityMatrix[12]),
"originalDanticommutesJ"->(dualMat.cmMat+cmMat.dualMat==ConstantArray[0,{12,12}]),
"originalUJcommute"->(navMat.cmMat==cmMat.navMat),
"originalUMsource"->(massMat!=ConstantArray[0,{12,12}]),
"originalCMsignMcommute"->(phaseMat.massMat==massMat.phaseMat),
"CMcurvatureSignedHodgeCurvature"->(
 comm[cmMat,massMat]==phaseMat.comm[dualMat,massMat]),
"unorientedStarCurvatureRank"->MatrixRank[comm[dualMat,massMat]],
"originalCMcurvatureRank"->MatrixRank[comm[cmMat,massMat]],
"allPassed"->(dualMat.dualMat==IdentityMatrix[12]&&phaseMat.phaseMat==IdentityMatrix[12]&&
 cmMat.cmMat==-IdentityMatrix[12]&&dualMat.cmMat+cmMat.dualMat==ConstantArray[0,{12,12}]&&
 navMat.cmMat==cmMat.navMat&&phaseMat.massMat==massMat.phaseMat&&comm[cmMat,massMat]==phaseMat.comm[dualMat,massMat]&&
 MatrixRank[comm[dualMat,massMat]]==6&&MatrixRank[comm[cmMat,massMat]]==6)|>;
Print[result];result