(* True ORIGINAL GST CM-odd curvature detects both missing native
directions in ONE curvature layer, using TWO true old orbit sources:
v and (U+J)v. It is not a geometric original-X Chow proof.

Exact old-source orbit rank 10. Explicit original physical
rational annihilators d1,d2 kill every old U+J orbit column.
K=[J,M] has full two-dimensional transverse image on the old
cyclic sector, with detector minor det 4.
*)
ClearAll[cc,ix,sh,mir,sgn,src,u,j,m,cm,seed,old,d,out,result];
cc=Flatten[Table[{x,y},{x,0,3},{y,0,2}],1];
ix[a_]:=First@FirstPosition[cc,a];
sh[{x_,y_}]:={Quotient[x+4 y,3],Mod[x+4 y,3]};
mir[{x_,y_}]:={3-x,2-y};
sgn[{x_,y_}]:=If[MemberQ[{0,1,3,4,5,9},x+4 y],1,-1];
src[{x_,y_}]:=Module[{b=Mod[Quotient[x,2]+2y,3],z},
 z=Mod[Mod[x,2]+2 b,3];
 Boole[y==2]Boole[b==2]+Boole[b==2]Boole[z==2]];
u=Table[Boole[k==ix[sh[cc[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cc[[i]]]*Boole[k==ix[mir[cc[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cc];
cm=j.m-m.j;
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cc;
old=Transpose[NestList[(u+j).#&,seed,11]];
d={{0,0,-1,0,0,0,-1,-1,-1,0,-1,1},
   {-1,1,0,1,1,1,0,0,0,1,0,0}};
out=d.cm.old;
result=<|
 "oldOriginalWaveRank"->MatrixRank[old],
 "originalMissingDetectorsAnnihilateOld"->(
   d.old==ConstantArray[0,{2,12}]),
 "CMOnFirstTwoOldVectors"->out[[All,{1,2}]],
 "exactTransverseCurvatureMinor"->Det[out[[All,{1,2}]]],
 "fullTransverseCurvatureRank"->MatrixRank[out],
 "JCurvatureAnticommutation"->(j.cm+cm.j==ConstantArray[0,{12,12}]),
 "allPassed"->(MatrixRank[old]==10 &&
 d.old==ConstantArray[0,{2,12}] &&
 out[[All,{1,2}]]=={{2,1},{0,2}} &&
 Det[out[[All,{1,2}]]]==4 &&
 MatrixRank[out]==2 &&
 j.cm+cm.j==ConstantArray[0,{12,12}])|>;
Print[result];result
