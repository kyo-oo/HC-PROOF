(* 23 October 2026. Mathbox/Wolfram exact GST causal graph fold audit.
   This computes the ACTUAL exterior period determinant and
   independent labelled-simple-graph topology incidence rank.
   Enumerates every labelled simple graph on 1..5 vertices,
   counts 1+2+8+64+1024=1099.
   Compares independent ConnectedComponents[Graph[..]]
   with MatrixRank of signed oriented incidence B and graph cycle
   rank. Period determinant is not inferred from the graph rank.
   No external random seed; exact arithmetic. Does not prove Hodge.
*)
ClearAll["Global`*"];
normal1={1,0,-1,0};
normal2={0,1,0,-1};
holomorphic1={1,tt,0,0};
holomorphic2={0,0,1,ss};
edgePeriod=Factor[Det[{normal1,normal2,holomorphic1,holomorphic2}]];
graphCases=Flatten[Table[
 Module[{allPairs=Subsets[Range[nn],{2}]},
  Table[
   Module[{ed=Select[allPairs,
       BitGet[mask,First@FirstPosition[allPairs,#]-1]==1&],
          B,graph,rank,components,loops,expectedLoops},
    B=Table[Table[If[j==e[[2]],1,
      If[j==e[[1]],-1,0]],{j,1,nn}],{e,ed}];
    rank=If[Length[ed]==0,0,MatrixRank[B]];
    graph=Graph[Range[nn],UndirectedEdge@@@ed];
    components=Length[ConnectedComponents[graph]];
    loops=Length[ed]-rank;
    expectedLoops=Length[ed]-nn+components;
    {nn,Length[ed],rank,components,loops,
       rank==nn-components && loops==expectedLoops &&
       loops>=0}
   ],{mask,0,2^Length[allPairs]-1}]
 ],{nn,1,5}],1];
result=<|
 "exteriorPeriod"->edgePeriod,
 "periodEqualsModuliDifference"->TrueQ[edgePeriod==ss-tt],
 "entirePopulation"->Length[graphCases],
 "allRankAndMixedWeightChecksPass"->And@@graphCases[[All,6]],
 "threeVertexTriangle"->Select[graphCases,
   #[[1]]==3&&#[[2]]==3&],
 "fiveVertexComplete"->Select[graphCases,
   #[[1]]==5&&#[[2]]==10&],
 "failedCases"->Select[graphCases,Not[#[[6]]]&]
|>;
Print[result];result