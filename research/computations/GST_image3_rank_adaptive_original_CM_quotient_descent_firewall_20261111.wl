(* GST Image-3 rank-adaptive original-GST quotient/descent test,
   EXACT original twelve-state Wave-I U,J,Survive M, mixed seed.
   At rational lambda=5/3 the F fold has eigenvalue mu=4 from
   the owner's actual two fixed Poincare-dual information cells.
   The rational quotient functional ell=(1 at null, -3 at max)
   satisfies ell F=4 ell on ALL 12 signal coordinates.

   The native original J²=-I does NOT descend to rank one:
   witness w=e_null+(1/3)e_max is in ker ell but ell(J w)=10/3.
   Even source CM curvature fails to define an endomorphism on
   the quotient: ell([J,F] w)=-80/9.

   This is an exact rational witness, not a negative result on the
   owner's Hodge implication. The correct quotient transports F
   while retaining J and curvature on the original source world.
*)
ClearAll[cells,idx,sh,mir,sgn,src,u,j,m,v,lam,f,mu,ell,w,curv,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
idx[a_]:=First@FirstPosition[cells,a];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sgn[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{k=Mod[Quotient[c,2]+2d,3],q},
 q=Mod[Mod[c,2]+2k,3];Boole[d==2]Boole[k==2]+Boole[k==2]Boole[q==2]];
u=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cells[[i]]]*Boole[k==idx[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cells];v=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
lam=5/3;f=u+j+lam m;mu=4;
ell=UnitVector[12,idx[{0,0}]]-3UnitVector[12,idx[{3,2}]];
w=UnitVector[12,idx[{0,0}]]+1/3UnitVector[12,idx[{3,2}]];
curv=j.f-f.j;
result=<|"originalU5"->(MatrixPower[u,5]==IdentityMatrix[12]),
"originalJ2"->(j.j==-IdentityMatrix[12]),
"FfullRank"->(MatrixRank[Transpose[NestList[f.#&,v,11]]]==12),
"FquotientRationalEigen"->(ell.f==4ell),
"quotientSurjective"->(ell!=ConstantArray[0,12]),
"kernelWitness"->ell.w,
"JdoesNotPreserveKernel"->ell.j.w,
"CMcommutatorNotDescendingKernel"->ell.curv.w,
"allPassed"->(MatrixPower[u,5]==IdentityMatrix[12]&&
j.j==-IdentityMatrix[12]&&ell.f==4ell&&
ell.w==0&&ell.j.w==10/3&&ell.curv.w==-80/9)|>;
Print[result];result