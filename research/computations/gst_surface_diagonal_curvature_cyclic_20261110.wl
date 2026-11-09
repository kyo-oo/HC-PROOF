(* Exact rational and symbolic GST surface-diagonal curvature and cyclic Hankel checks.
   Contract: verifies finite matrices and identities, not existence of a universal
   original-X algebraic source. Run in a fresh Wolfram Language kernel. *)
ClearAll[d,x,y,z,t,gram,aa,bb,cc,dd,pp,qq,lefschetz,basis,
  duals,shift,moment,gTwo,blockMiddle,fullTwo,checks,output];
gram={{0,1,0,1},{1,0,0,1},{0,0,d^2,d},{1,1,d,24}};
aa={1,0,0,0};bb={0,1,0,0};cc={0,0,1,0};dd={0,0,0,1};
pp=cc-d(aa+bb);
qq=dd-aa-bb-cc/d;
lefschetz={{1,0,d,2},{0,1,d,2}};
basis={aa,bb,cc,qq};
duals={bb,aa,cc/d^2,qq/21};
shift[n_Integer?Positive]:=Table[Boole[i==Mod[j,n]+1],{i,n},{j,n}];
moment[n_Integer?Positive]:=Table[
  UnitVector[n,1].MatrixPower[shift[n],i+j].UnitVector[n,1],
  {i,0,n-1},{j,0,n-1}];
gTwo={{x,y},{y,z}};
blockMiddle=KroneckerProduct[gTwo,gTwo];
fullTwo=ArrayFlatten[{
  {{{0,1},{1,0}},ConstantArray[0,{2,4}],ConstantArray[0,{2,1}]},
  {ConstantArray[0,{4,2}],blockMiddle,ConstantArray[0,{4,1}]},
  {ConstantArray[0,{1,2}],ConstantArray[0,{1,4}],{{t}}}
}];
checks=<|
 "K3_Q_orthogonal"->TrueQ[Simplify[And@@( (#.gram.qq==0)& /@ {aa,bb,cc}),d>0]],
 "K3_Q_square_21"->TrueQ[Simplify[qq.gram.qq==21,d>0]],
 "K3_P_square_3d2"->TrueQ[Simplify[pp.gram.pp==3d^2,d>0]],
 "K3_P_Q_orthogonal"->TrueQ[Simplify[pp.gram.qq==0,d>0]],
 "K3_P_primitive"->TrueQ[Simplify[lefschetz.pp=={0,0},d>0]],
 "K3_Q_primitive"->TrueQ[Simplify[lefschetz.qq=={0,0},d>0]],
 "K3_full_gram_det"->TrueQ[Simplify[Det[gram]==-21d^2,d>0]],
 "K3_dual_frame"->TrueQ[Simplify[
   Table[basis[[i]].gram.duals[[j]],{i,4},{j,4}]==IdentityMatrix[4],d>0]],
 "K3_full_hankel_det"->(Det[moment[4]]==-1),
 "rho2_symbolic_det"->(Factor[Det[fullTwo]+t Det[gTwo]^4]===0),
 "rho2_instance_det"->(Det[fullTwo/.{x->2,y->1,z->-2,t->20}]==-12500),
 "rho2_instance_rank"->(MatrixRank[fullTwo/.{x->2,y->1,z->-2,t->20}]==7),
 "rho2_full_hankel_det"->(Det[moment[7]]==-1),
 "curvature_commutator"->(
    ({{1,0},{0,0}}.{{0,0},{1,0}}-{{0,0},{1,0}}.{{1,0},{0,0}}).{1,0}=={0,-1})
|>;
output=<|"all_passed"->And@@Values[checks],"checks"->checks,
  "K3_hankel"->moment[4], "rank7_hankel_det"->Det[moment[7]],
  "rank2_hodge_gram_det"->Factor[Det[fullTwo]]|>;
Print[output];
output
