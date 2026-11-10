(* User Image 3 ORIGINAL GST fusion audit, exact Wolfram rational matrices.
   Original laws: squarePureDual = coordinate reversal J; N-cohomology
   independent channels and manyCausalHoleTensor; proposed navigation
   constant kappa counts actual channel-index steps; CM curvature [J,T].
   Real Chow transport is tested only on an EXPLICIT compatible abstract
   native/Betti module pair, never claimed to construct a Chow
   correspondence on arbitrary X or to prove Hodge algebraicity.
*)
ClearAll[navCase,rows,runs,sourceA,sourceB,rank1,rank2,
  cl,an,ap,jn,ab,bp,jb,seed,index,amp,runF,checks,result];

navCase[n_Integer?Positive] := Module[{s,j,all,delta,uniform,ks,cr},
 s=Table[Boole[i==Mod[k,n]+1],{i,n},{k,n}];
 j=Table[Boole[i+k==n+1],{i,n},{k,n}];
 delta=UnitVector[n,1];uniform=ConstantArray[1,n];
 ks=Table[MatrixPower[j,1].MatrixPower[s,k].MatrixPower[j,1]==
     MatrixPower[Transpose[s],k],{k,0,n+2}];
 cr=j.s-s.j;
 <|"n"->n,"mirrorInvolutive"->(j.j==IdentityMatrix[n]),
   "navigationInverseConjugate"->And@@ks,
   "deltaSeedOrbitRank"->MatrixRank[Transpose[Table[
      MatrixPower[s,k].delta,{k,0,n-1}]]],
   "uniformSeedOrbitRank"->MatrixRank[Transpose[Table[
      MatrixPower[s,k].uniform,{k,0,n-1}]]],
   "curvatureRank"->MatrixRank[cr],
   "passed"->(j.j==IdentityMatrix[n]&&And@@ks&&
      MatrixRank[Transpose[Table[MatrixPower[s,k].delta,{k,0,n-1}]]]==n&&
      MatrixRank[Transpose[Table[MatrixPower[s,k].uniform,{k,0,n-1}]]]==1)
 |>];
runs=Table[navCase[n],{n,1,8}];

sourceA={1,2};sourceB={3,5,7};
rank1=Outer[Times,sourceA,sourceB];
rank2={{1,0,0},{0,1,0}};
(* Original N-cohomology double product: reindexing never converts
   pure tensor rank one to general rank two. *)
cl={{1,0},{0,1},{0,0}};
an={{0,1},{1,0}};
ap={{1,1},{0,1}};
jn=DiagonalMatrix[{1,-1}];
ab={{0,1,0},{1,0,0},{0,0,1}};
bp={{1,1,0},{0,1,0},{0,0,1}};
jb=DiagonalMatrix[{1,-1,1}];
seed={1,0};
(* cardinal navigation of the source words: two families of actual
   compatible native/Betti maps, addressed by 2x3 N-cohomology channels *)
index=Flatten[Table[If[Mod[i+j,2]==0,1,2],{i,1,2},{j,1,3}]];
amp=Flatten[rank1];
runF[k_Integer?NonNegative]:=Module[{nat,bet,shifted,curvNat,curvBet},
 shifted=RotateLeft[index,k];
 nat=Total[MapThread[#1*(If[#2==1,an,ap].seed)&,{amp,shifted}]];
 bet=Total[MapThread[#1*(If[#2==1,ab,bp].(cl.seed))&,{amp,shifted}]];
 curvNat=Total[MapThread[#1*
    (jn.(If[#2==1,an,ap].seed)-If[#2==1,an,ap].(jn.seed))&,
    {amp,shifted}]];
 curvBet=Total[MapThread[#1*
    (jb.(If[#2==1,ab,bp].(cl.seed))-
       If[#2==1,ab,bp].(jb.(cl.seed)))&,
    {amp,shifted}]];
 <|"kappa"->k,"classNaturality"->(cl.nat==bet),
 "curvatureNaturality"->(cl.curvNat==curvBet),
 "sourceThirdCoordinate"->bet[[3]],
 "curvatureThirdCoordinate"->curvBet[[3]],
 "nativeCurvatureNonzero"->(curvNat!={0,0})|>
];
rows=Table[runF[k],{k,0,6}];
checks=<|
 "navigationRanksAndHodgeMirror"->And@@(Lookup[#,"passed"]&/@runs),
 "twoByThreeTensorRankOne"->(MatrixRank[rank1]==1),
 "twoByThreeIndependentTwoSourceRank"->(MatrixRank[rank2]==2),
 "allFiniteImage3NatAndCMNaturality"->And@@(
    (Lookup[#,"classNaturality"]&&Lookup[#,"curvatureNaturality"])&/@rows),
 "allLandedSourcesRemainInOldImage"->And@@(
    (#["sourceThirdCoordinate"]==0 && #["curvatureThirdCoordinate"]==0)&/@rows),
 "nontrivialActualCurvature"->(And@@(Lookup[#,"nativeCurvatureNonzero"]&/@rows)),
 "canonicalAlgebraicSourceMapRank"->MatrixRank[cl]
|>;
result=<|"originalGSTMatrices"->runs,
 "NcohomologyRank1Tensor"->rank1,
 "NcohomologyRank2General"->rank2,
 "Image3NavigationCurvatureTests"->rows,"checks"->checks,
 "allPassed"->(checks["navigationRanksAndHodgeMirror"]&&
 checks["twoByThreeTensorRankOne"]&&
 checks["twoByThreeIndependentTwoSourceRank"]&&
 checks["allFiniteImage3NatAndCMNaturality"]&&
 checks["allLandedSourcesRemainInOldImage"]&&
 checks["nontrivialActualCurvature"]&&
 checks["canonicalAlgebraicSourceMapRank"]==2)|>;
Print[result];result