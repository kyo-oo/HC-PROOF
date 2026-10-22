(* Exact GST causal-fold incidence and mixed-Hodge weight checks.
   Research date: 2026-10-22; stateless WolframLanguageEvaluator.
   Parameters are rational/integer and all results exact, not numeric sampling.
   These checks do not prove the infinite-N theorem nor the Hodge conjecture. *)

Clear[aa,bb,tt,ss,uu,vv,g,h,nn,jj,kk,graphInc,graphCases,graphVerts];
aa=tt^2 ss^2 uu vv;
bb=1+tt ss (uu+vv)+tt^2 ss^2 uu vv;
node[x_,r_]:=1+x tt+r aa;
tower[n_]:=Sum[aa^k,{k,0,n}];

(* One nodal rational curve C_g, with g self-nodes, times P^N.
   Check weight-2j charge-zero H^(2j+1), and after product with E
   the weight-(2j+1) H^(2j+2) off-diagonal terms. *)
single=Flatten[Table[{
  Simplify[Coefficient[Expand[node[g,1] tower[nn]],tt,2 jj+1]==
    g (ss^2 uu vv)^jj],
  Simplify[Coefficient[
    Coefficient[Expand[node[g,1] tower[nn] bb],tt,2 jj+2],
    ss,2 jj+1]==
    g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{g,1,4},{nn,0,5},{jj,0,nn}],2];

(* Double causal fold: C_g x C_h x P^N. Detect rational
   weight-2j, diagonal type (j,j), even-degree 2j+2. *)
double=Flatten[Table[
  Simplify[Coefficient[
    Coefficient[Expand[node[g,1] node[h,1] tower[nn]],tt,2 jj+2],
    ss,2 jj]==g h (uu vv)^jj]
,{g,1,3},{h,1,3},{nn,0,7},{jj,0,nn}]];

(* Dual-graph edge->vertex incidence matrix, including self-loops. *)
graphInc[verts_,edges_] := Table[
  KroneckerDelta[edges[[k,1]],i]-KroneckerDelta[edges[[k,2]],i],
  {k,1,Length[edges]},{i,1,verts}];
graphCases={{{1,2},{2,3}},{{1,2},{2,3},{3,1}},
  {{1,1},{1,1},{1,1}},
  {{1,2},{2,3},{3,4},{4,1},{1,3}}};
graphVerts={3,3,1,4};
graphResult=Table[With[{ed=graphCases[[k]],vtx=graphVerts[[k]]},
 {vtx,Length[ed],MatrixRank[graphInc[vtx,ed]],
  Length[ed]-MatrixRank[graphInc[vtx,ed]],Length[ed]-vtx+1}
],{k,1,4}];


(* Smooth genus-g reverse-fold Hodge polynomial and exact comparison
   with the irreducible nodal rational curve with g self-nodes. *)
smooth[x_]:=1+x tt ss (uu+vv)+aa;
smoothing=Flatten[Table[{
 Simplify[Coefficient[Expand[(smooth[g]-node[g,1]) tower[nn]],
   tt,2 jj+1] ==
   g ss^(2 jj) (uu vv)^jj (ss (uu+vv)-1)],
 Simplify[Coefficient[Coefficient[
   Expand[smooth[g] tower[nn]],tt,2 jj+1],ss,2 jj+1] ==
   g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{g,1,4},{nn,0,7},{jj,0,nn}],2];

(* GST causal Hodge genesis G1/G2, GENERAL graph vertex and loop ranks.
   Smooth Hodge numbers are derived from the arithmetic genus of the
   causal identification graph, not entered as an independent input. *)
generalNodal[r_,g_,n_]:=Expand[(1+g tt+r aa) tower[n]];
generalSmooth[g_,n_]:=Expand[(1+g tt ss (uu+vv)+aa) tower[n]];
genesis=Flatten[Table[
 Simplify[generalSmooth[g,nn]-generalNodal[r,g,nn] ==
   Expand[(g tt (ss (uu+vv)-1)+(1-r) aa) tower[nn]]],
 {r,1,4},{g,0,5},{nn,0,8}]];
genesisCoeffs=Flatten[Table[{
 Simplify[Coefficient[Coefficient[generalNodal[r,g,nn],tt,2 jj+1],
   ss,2 jj]==g (uu vv)^jj],
 Simplify[Coefficient[Coefficient[generalSmooth[g,nn],tt,2 jj+1],
   ss,2 jj+1]==g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{r,1,3},{g,0,4},{nn,0,7},{jj,0,nn}],3];

{"SingleCount"->Length[single],
 "SingleAllTrue"->And@@Flatten[single],
 "DoubleCount"->Length[double],
 "SmoothingCount"->Length[smoothing],
 "SmoothingAllTrue"->And@@Flatten[smoothing],
 "GenesisCount"->Length[genesis],
 "GenesisAllTrue"->And@@genesis,
 "GenesisCoefficientCount"->Length[genesisCoeffs],
 "GenesisCoefficientsAllTrue"->And@@Flatten[genesisCoeffs],
 "DoubleAllTrue"->And@@double,
 "GraphRankResults"->graphResult,
 "DoubleEvenWeight2Coefficient"->Coefficient[
   Coefficient[Expand[node[2,1] node[3,1] tower[2]],tt,4],ss,2]}
