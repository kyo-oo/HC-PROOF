(* Mathbox: ACTUAL all-rank Pluecker projector algebra and Fitting source.
   General theorem proven by the alternating determinant Cramer identity
   in GST_explicit_plucker_fitting_source_algebra_all_rank_original_X_2026_10_23.tex.
   Exact rational tests here independently check low ranks, basis invariance,
   projector idempotence, trace, and determinantal rank-zero locus.
*)
ClearAll["Global`*"];
formEval[vs_List, weights_Association] :=
 Module[{rr=Length[vs],mm=Length[First[vs]],ids},
  ids=Subsets[Range[mm],{rr}];
  Sum[weights[ids[[z]]] Det[
     (Transpose[vs])[[ids[[z]]]]],{z,Length[ids]}]
 ];
projector[frame_List,wt_Association]:=
 Module[{rr=Length[frame],mm=Length[First[frame]],den,entries},
  den=formEval[frame,wt];
  If[den==0,Return[$Failed]];
  entries=Table[
   Sum[frame[[i,j]] formEval[
        ReplacePart[frame,i->UnitVector[mm,k]],wt],
       {i,1,rr}]/den,
   {j,1,mm},{k,1,mm}];
  entries
 ];
frameMake[rr_,mm_,shift_:0]:=
 Table[Table[
  If[i==j,1,0]+If[i>rr,(i+j+shift) Mod 5+1,0],
  {i,1,mm}],{j,1,rr}];
weightMake[rr_,mm_]:=Module[{idxs=Subsets[Range[mm],{rr}]},
 AssociationThread[idxs,
    Table[If[idxs[[a]]===Range[rr],100003,2+Total[idxs[[a]]^2]],
          {a,Length[idxs]}]]
];
testOne[rr_,mm_,shift_]:=
 Module[{u=frameMake[rr,mm,shift],wt=weightMake[rr,mm],
         pp,transform,pp2,traceOK,projectOK,frameOK},
  pp=projector[u,wt];
  If[pp===$Failed,Return[{rr,mm,shift,False,False,False,False}]];
  transform=IdentityMatrix[rr];
  If[rr>=2,transform[[1,2]]=2];
  pp2=projector[transform.u,wt];
  traceOK=TrueQ[Tr[pp]==rr];
  projectOK=TrueQ[pp.pp==pp];
  frameOK=And@@Table[TrueQ[pp.u[[j]]==u[[j]]],{j,rr}];
  {rr,mm,shift,traceOK,projectOK,frameOK,TrueQ[pp2==pp]}
 ];
projectorTests=Flatten[Table[
 testOne[rr,mm,shift],
 {rr,1,4},{mm,rr+1,Min[rr+3,7]},{shift,0,2}],2];
(* Genuine Gr(2,5) incidence zero-locus local test.
   Base S=span(e1,e2), incidence phi(e1,e2)=1.
   P(e5)=0 for phi=e1^e2, while adding phi(e5,e2)=1 gives P(e5)=e1.
   Fitting determinant ideal I_4([I-P | P e5]) vanishes iff section vanishes. *)
u=UnitVector[5,1];v=UnitVector[5,2];U={u,v};
idx=Subsets[Range[5],{2}];base=AssociationThread[idx,ConstantArray[0,Length[idx]]];
wt0=Association[base];wt0[{1,2}]=1;
wt1=Association[wt0];wt1[{2,5}]=-1;
pZero=projector[U,wt0];pNonzero=projector[U,wt1];
e5=UnitVector[5,5];
bZero=Transpose[Append[Transpose[IdentityMatrix[5]-pZero],pZero.e5]];
bNonzero=Transpose[Append[Transpose[IdentityMatrix[5]-pNonzero],pNonzero.e5]];
fittingChecks=<|
 "projectorZeroSection"->TrueQ[pZero.e5==ConstantArray[0,5]],
 "rankZero"->MatrixRank[bZero],
 "rankNonzero"->MatrixRank[bNonzero],
 "predictedRanks"->{3,4},
 "zeroLocusCorrect"->TrueQ[MatrixRank[bZero]==3&&MatrixRank[bNonzero]==4]
|>;
(* Independent original-X Gr(2,5) intersection arithmetic. *)
hh=x+y; ss=x y;
intGr[f_]:=Coefficient[Coefficient[Expand[(x-y)f],x,4],y,3];
theta=2 hh^2/5-ss;
schubertChecks={intGr[hh^6],intGr[ss hh^4],
 intGr[ss^2 hh^2],intGr[theta hh^4],intGr[theta^2 hh^2]};
out=<|
 "projectorCases"->Length[projectorTests],
 "allProjectorTests"->And@@Flatten[projectorTests[[All,4;;7]]],
 "projectorFailures"->Select[projectorTests,Not[And@@#[[4;;7]]]&],
 "fittingScheme"->fittingChecks,
 "schubertPeriods"->schubertChecks,
 "schubertExact"->TrueQ[schubertChecks==={5,2,1,0,1/5}]
|>;
Print[out];out