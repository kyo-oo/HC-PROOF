(* Exact GST spatial analytic projector + Chern-source arithmetic.
   Arbitrary-X theorem is PROVED separately via Oka/Grauert,
   Thom-Porteous, affine algebraic geometry, and Chow homotopy.
   Finite symbolic tests are independent consistency checks only. *)
ClearAll["Global`*"];
rootChecks=Table[
 Module[{xv=Array[x,n],hv=Array[h,n],lam,proj,defect},
   lam=hv.xv;
   proj=Outer[Times,xv,hv]/lam;
   defect=Together[proj.proj-proj];
   {n,TrueQ[And@@Flatten[(defect==0)]],
      TrueQ[FullSimplify[Tr[proj]==1]]}
 ],{n,2,8}];
chernTests=Flatten[Table[
 Module[{tt=Unique["z"],aa=Unique["a"],trunc,cval},
  trunc=Normal[Series[Exp[(-1)^(p-1) Factorial[p-1] aa tt^p],{tt,0,d}]];
  cval=Coefficient[trunc,tt,p];
  {p,d,TrueQ[FullSimplify[cval==(-1)^(p-1) Factorial[p-1] aa]]}
 ],{p,1,8},{d,p,12}],1];
(* A concrete analytic projector conjugation can have
   nonpolynomial entries without changing its K class. *)
gauge={{1,Exp[z]},{0,1}};
pzero={{1,0},{0,0}};
conjugate=Simplify[gauge.pzero.Inverse[gauge]];
result=<|
 "projectorMatrixDimensionCases"->Length[rootChecks],
 "allIdempotenceAndRankOnePass"->And@@Flatten[rootChecks[[All,2;;3]]],
 "projectorFailures"->Select[rootChecks,Not[And@@#[[2;;3]]]&],
 "totalPureChernGradeCases"->Length[chernTests],
 "pureChernGradeAllPass"->And@@chernTests[[All,3]],
 "pureChernFailures"->Select[chernTests,Not[#[[3]]]&],
 "unboundedSameClassHolomorphicProjector"->conjugate
|>;
Print[result];result