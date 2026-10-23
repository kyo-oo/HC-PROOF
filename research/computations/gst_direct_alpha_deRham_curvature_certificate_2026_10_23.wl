(* Exact Mathbox certificate for the alpha-dependent GST algebraic
   de Rham projector equation. These tests certify the matrix
   equations and correct normalization in stated ranges, not
   unconditional existence for every Hodge alpha. *)
ClearAll["Global`*"];
(* True incidence rank-one P on J(P1):
   x=(1,u), ell=(1,v), denominator 1+u v.
   F_{u v}=Tr P (P_u P_v - P_v P_u). *)
pp={{1,v},{u,u v}}/(1+u v);
pu=D[pp,u];pv=D[pp,v];
omega=FullSimplify[Tr[pp.(pu.pv-pv.pu)]];
rankOne=<|
 "P2equalsP"->TrueQ[FullSimplify[pp.pp-pp]==ConstantArray[0,{2,2}]],
 "TraceOne"->TrueQ[FullSimplify[Tr[pp]]==1],
 "ExactOmegaDuDv"->omega,
 "ExpectedCurvature"->TrueQ[FullSimplify[omega+1/(1+u v)^2]==0]
|>;
(* Full rational degree-two Chern source in true Gr(2,5).
   Use h^2 and independent Schubert s2. *)
ch2S=h^2/2-s2;
ch2Line=h^2/2;
theta=2h^2/5-s2;
grassmann=<|
 "ch2S"->ch2S,
 "ch2Line"->ch2Line,
 "fiveTimesTargetSolved"->TrueQ[Expand[5 ch2S-ch2Line-5 theta]===0],
 "rationalSourceCoefficient"->{1,-1/5}
|>;
(* Every tangent Q to any idempotent is off-diagonal,
   and Q=[[Q,P],P]. Construct exact nontrivial integer tests. *)
testTangent[m_,r_]:=Module[{p,q,lin,g,comm},
 p=DiagonalMatrix[Join[ConstantArray[1,r],ConstantArray[0,m-r]]];
 q=Table[If[Xor[i<=r,j<=r],2i+3j,0],{i,m},{j,m}];
 lin=p.q+q.p-q;
 g=q.p-p.q;
 comm=g.p-p.g-q;
 {m,r,lin==ConstantArray[0,{m,m}],
      comm==ConstantArray[0,{m,m}]}
];
tangentTests=Flatten[Table[testTangent[m,r],{m,1,9},{r,0,m}],1];
out=<|
 "rankOne"->rankOne,
 "Gr25"->grassmann,
 "allTangentPairs"->Length[tangentTests],
 "allTangentEquationsHold"->And@@Flatten[tangentTests[[All,3;;4]]],
 "tangentFailures"->Select[tangentTests,Not[And@@#[[3;;4]]]&]
|>;
Print[out];out