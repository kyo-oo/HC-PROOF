(* Original GST IMAGE-3: Hodge/Poincare complement, original CM
   J, SURVIVE M, all on the owner's 4x3 physical information carrier.

   D u(c)=u(worldDual(c)), worldDual(c,d)=(3-c,2-d).
   S u(c)=original cmSign(c) u(c) (±1).
   Original J from GSTGraphV2CMWaveFusion is exactly S.D.

   Exact operator relations:
   D²=I, S²=I, J²=-I, D.J=-J.D;
   S.M=M.S;
   [J,M]=S.[D,M].
   Rank[S.[D,M]]=rank[D,M]=rank[J,M]=6.

   All matrix entries are EXACT rationals. No metric-dependent
   analytic Hodge star or unknown Chow correspondences assumed.
*)
ClearAll[cells,idx,shuffle,dual,sgn,src,D,S,J,M,U,comm,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
idx[c_]:=First@FirstPosition[cells,c];
shuffle[{a_,b_}]:={Quotient[a+4b,3],Mod[a+4b,3]};
dual[{a_,b_}]:={3-a,2-b};
sgn[{a_,b_}]:=If[MemberQ[{0,1,3,4,5,9},a+4b],1,-1];
src[{a_,b_}]:=Module[{k=Mod[Quotient[a,2]+2b,3],l},
l=Mod[Mod[a,2]+2k,3];
Boole[b==2]Boole[k==2]+Boole[k==2]Boole[l==2]];
D=Table[Boole[k==idx[dual[cells[[i]]]]],{i,12},{k,12}];
S=DiagonalMatrix[sgn/@cells];
J=S.D;
U=Table[Boole[k==idx[shuffle[cells[[i]]]]],{i,12},{k,12}];
M=DiagonalMatrix[src/@cells];
comm[x_,y_]:=x.y-y.x;
result=<|"originalWorldDual2"->(D.D==IdentityMatrix[12]),
"originalCMphase2"->(S.S==IdentityMatrix[12]),
"originalComplexJ2"->(J.J==-IdentityMatrix[12]),
"originalDanticommutesJ"->(D.J+J.D==ConstantArray[0,{12,12}]),
"originalUJcommute"->(U.J==J.U),
"originalUMsource"->(M!=ConstantArray[0,{12,12}]),
"originalCMsignMcommute"->(S.M==M.S),
"CMcurvatureSignedHodgeCurvature"->(
 comm[J,M]==S.comm[D,M]),
"unorientedStarCurvatureRank"->MatrixRank[comm[D,M]],
"originalCMcurvatureRank"->MatrixRank[comm[J,M]],
"allPassed"->(D.D==IdentityMatrix[12]&&S.S==IdentityMatrix[12]&&
 J.J==-IdentityMatrix[12]&&D.J+J.D==ConstantArray[0,{12,12}]&&
 U.J==J.U&&S.M==M.S&&comm[J,M]==S.comm[D,M]&&
 MatrixRank[comm[D,M]]==6&&MatrixRank[comm[J,M]]==6)|>;
Print[result];result