(* GST original Image 3: UNIFY original Poincare complement
   GSTWorldPoincareDuality.worldDual with original 12-cell
   GSTGraphV2CMWaveFusion mirrorCell / signed CM J.

   For ANY positive rectangular GST A×B carrier, the Poincare
   complement is D(c,d)=(A-1-c,B-1-d), D²=I.
   When at least ONE axis even, orientation sign on its first half
   reverses under D; J=sign*D has rational J²=-I.

   For odd×odd, D fixes its central coordinate, so a rational signed
   complement cannot square to -I at that cell.
   This is a structural theorem for all A,B, not a claim that
   native Hodge-star corresponds to algebraic geometry on any X.
*)
ClearAll[test,models,verify,originalCells,origSign,origMirror,origD,
 originalMatches,originalJ,originalSigProperty,summary];
test[a_Integer?Positive,b_Integer?Positive]:=Module[{cells,idx,dual,axis,sgn,dmat,jmat,fixed},
cells=Flatten[Table[{x,y},{x,0,a-1},{y,0,b-1}],1];
idx[c_]:=First@FirstPosition[cells,c];
dual[{x_,y_}]:={a-1-x,b-1-y};
axis=If[EvenQ[a],"carry",If[EvenQ[b],"digit","none"]];
sgn[{x_,y_}]:=Which[
 axis=="carry",If[x<a/2,1,-1],
 axis=="digit",If[y<b/2,1,-1],
 True,1];
dmat=Table[Boole[k==idx[dual[cells[[i]]]]],{i,a b},{k,a b}];
jmat=DiagonalMatrix[sgn/@cells].dmat;
fixed=Count[cells,c_/;dual[c]==c];
<|"A"->a,"B"->b,"size"->a b,
"dualFixedPointCount"->fixed,"evenAxis"->(axis!="none"),
"dualSquareIdentity"->(dmat.dmat==IdentityMatrix[a b]),
"signedDualCMsquareMinusIdentity"->(jmat.jmat==-IdentityMatrix[a b]),
"pass"->If[axis=="none",fixed==1&&
 jmat.jmat!= -IdentityMatrix[a b],
 fixed==0&&jmat.jmat== -IdentityMatrix[a b]]|>];
models=test@@@{{1,1},{1,2},{2,3},{3,3},{4,3},{4,4},{3,4},{5,2},{5,5},{8,9}};
originalCells=Flatten[Table[{x,y},{x,0,3},{y,0,2}],1];
origSign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
origMirror[{c_,d_}]:={3-c,2-d};
origD[{c_,d_}]:={4-1-c,3-1-d};
originalMatches=AllTrue[originalCells,origMirror[#]==origD[#]&];
originalSigProperty=AllTrue[originalCells,
 origSign[#]*origSign[origD[#]]==-1&];
summary=<|"original12JIsSignedPoincareComplement"->originalMatches,
"original12CMphaseAntisymmetric"->originalSigProperty,
"exactRectangularChecks"->models,
"allPassed"->(originalMatches&&originalSigProperty&&
  And@@(Lookup[#,"pass"]&/@models))|>;
Print[summary];summary