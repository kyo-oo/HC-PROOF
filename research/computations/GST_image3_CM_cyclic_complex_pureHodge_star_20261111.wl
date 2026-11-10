(* Image 3 ORIGINAL GST cyclic-complex versus pure-Hodge-star compatibility.
   The original GSTSquarePureHodgeDuality pure mirror squares to +I.
   The original GSTGraphV2CMInfiniteCurvatureBridge CM construction
   requires J_CM^2=-I. These two laws MUST NOT be conflated.

   Exact rational doubled carrier U = V (+) V:
       J_CM(v,w)=(-w,v),    Star(v,w)=(w,v).
       J_CM^2=-I, Star^2=I, Star J_CM=-J_CM Star,
       J_CM^4=I, CM curvature [Star,J_CM] has full rank 2r.
   Tested finite r=1..8. This does not make J_CM a correspondence
   on every original smooth projective X.

   Rational odd-rank obstruction is a proven determinant argument:
   if dim_Q V is odd and J^2=-I, then det(J)^2=(-1)^dim=-1,
   impossible over Q. The finite tests merely confirm parity.
*)
ClearAll[one,tests,result];
one[r_Integer?Positive] := Module[{id,zero,cm,star,c,cyclic},
 id=IdentityMatrix[r];zero=ConstantArray[0,{r,r}];
 cm=ArrayFlatten[{{zero,-id},{id,zero}}];
 star=ArrayFlatten[{{zero,id},{id,zero}}];
 c=star.cm-cm.star;
 cyclic=And@@Table[MatrixPower[cm,4k]==IdentityMatrix[2r],
   {k,0,5}];
 <|"r"->r,"doubledRank"->2r,
 "CMsquareIsNegativeIdentity"->(cm.cm==-IdentityMatrix[2r]),
 "StarSquareIsIdentity"->(star.star==IdentityMatrix[2r]),
 "CMAnticommutesWithStar"->(star.cm==-cm.star),
 "CMFourfoldNavigation"->cyclic,
 "commutatorCurvatureRank"->MatrixRank[c],
 "expectedRank"->2r,
 "oddRankRationalCMObstruction"->If[OddQ[r],True,"not asserted"],
 "allPassed"->(cm.cm==-IdentityMatrix[2r]&&
  star.star==IdentityMatrix[2r]&&star.cm==-cm.star&&cyclic&&
  MatrixRank[c]==2r)|>
];
tests=Table[one[r],{r,1,8}];
result=<|"modelsChecked"->Length[tests],
 "models"->tests,
 "allPassed"->And@@(Lookup[#,"allPassed"]&/@tests)|>;
Print[result];result