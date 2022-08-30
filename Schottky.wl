(* Wolfram Language Package *)
BeginPackage["Schottky`"]
(* Exported symbols added here with SymbolName::usage *)  
Generation`GetSimpleSchottkyGroup::usage = "Obtain a simple cover by using circle pairs";

Begin["`Private`"] (* Begin Private Context *) 
Needs["ShkyMath`","setup/Math.wl"];

Mobius`MatrixToTransformation[{{a_, b_}, {c_, d_}}] := Module[{f},
  f[z_] := (a z + b)/(c z + d);
  Return[f];
  ]
Mobius`MatrixToTransformationDer[{{a_, b_}, {c_, d_}}] := Module[{f},
  f[z_] := a/(c z + d) - c (a z + b)/(c z + d)^2;
  Return[f];
  ]
Mobius`MatrixImageInf[{{a_, b_}, {c_, d_}}] := 
  If[c == 0, Return[\[Infinity]], Return[a/c]];
Mobius`MatrixPreImageInf[{{a_, b_}, {c_, d_}}] := 
  If[c == 0, Return[\[Infinity]], Return[-d/c]];
Mobius`FixedPoint[{{a_, b_}, {c_, d_}}] := Module[{term1, term2},
  If[c == 0,
   Return[{(b/d)/(1 - a/d)}]];
  term1 = (a - d)/(2 c);
  term2 = 1/(2 c) ((a - d)^2 + 4 c b)^(1/2);
  Return[{term1 + term2, term1 - term2}];
  ]

Mobius`MatrixToCircle[{{a0_, b0_}, {c0_, d0_}}] := If[a0 == 0,
   Return[{-d0/c0, 0, b0/c0}],
   With[{b = b0/a0, c = c0/a0, d = d0/a0}, Return[{-d/c, 1/c, b/c - d/c^2}]]
   ];
Mobius`CircleToMatrix[{p0_, 
    p1_, \[Phi]_}] := {{p1, -p0 p1 + \[Phi]}, {1, -p0}};
Mobius`CircleToTransformation[{p0_, p1_, r_}] := 
  Module[{f}, f[z_] := r/(z - p0) + p1; Return[f]];
Mobius`TranformCircleFromMatrix[{p_, r_}, {{a_, b_}, {c_, d_}}] := 
 Module[{p0, p1, \[Phi]},
  If[c == 0, Return[{a/d p + b/d, Abs[a/d r]}]];
  With[{A = {{a, b}, {c, d}}},
   {p0, p1, \[Phi]} = Mobius`MatrixToCircle[A];
   Return[{\[Phi] Conjugate[(p - p0)/(Abs[p - p0]^2 - r^2)] + p1, 
     Abs[(\[Phi] r)/(Abs[p - p0]^2 - r^2)]}];
   ]
  ]

Mobius`CircleIsInvertedFromMatrix[{p_, r_}, {{a_, b_}, {c_, d_}}] := 
 Module[{p0, p1, \[Phi]},
  If[c == 0, Return[False]];
  With[{A = {{a, b}, {c, d}}},
   {p0, p1, \[Phi]} = Mobius`MatrixToCircle[A];
   Return[If[Abs[p - p0] < r, True, False]];
   ]
  ]

(*Cross Ratio*)

CrossRatio[x1_, x2_, x3_, x4_] := ((x1 - x2) (x3 - x4))/((x2 - x3) (x4 - x1));

(*Transformation to Matrix*)

Mobius`TransformationToMatrixEval[z1_, z2_, z3_, w1_, w2_, w3_] := 
 Module[{a, b, c, d},
  a = Det[{{z1 w1, w1, 1}, {z2 w2, w2, 1}, {z3 w3, w3, 1}}];
  b = Det[{{z1 w1, z1, w1}, {z2 w2, z2, w2}, {z3 w3, z3, w3}}];
  c = Det[{{z1, w1, 1}, {z2, w2, 1}, {z3, w3, 1}}];
  d = Det[{{z1 w1, z1, 1}, {z2 w2, z2, 1}, {z3 w3, z3, 1}}];
  Return[{{a, b}, {c, d}}/(a d - c b)^(1/2)];
  ]

Mobius`TransformationToMatrixEvalInf[z1_, z2_, z3_, w2_, w3_] := 
 Module[{a, b, c, d},
  a = z1 (w2 - w3) - z2 w2 + z3 w3;
  b = z1 (z2 w3 - z3 w2) + z2 z3 (w2 - w3);
  c = z3 - z2;
  d = z1 (z2 - z3);
  Return[{{a, b}, {c, d}}/(a d - c b)^(1/2)];
  ]

Mobius`TransformationToMatrix[f_] := Module[{InfPos = 0, list = {1, 0, I}},
  Quiet@Check[f[1], InfPos = 1];
  Quiet@Check[f[0], InfPos = 2];
  Quiet@Check[f[I], InfPos = 3];
  If[InfPos == 0,
   With[{z1 = 1, z2 = 0, z3 = I},
    With[{w1 = f[z1], w2 = f[z2], w3 = f[z3]},
     Return[Mobius`TransformationToMatrixEval[z1, z2, z3, w1, w2, w3]];
     ]
    ],
   With[{z1 = list[[InfPos]], z2 = Delete[list, InfPos][[1]], 
     z3 = Delete[list, InfPos][[2]]},
    With[{w2 = f[z2], w3 = f[z3]},
     Return[Mobius`TransformationToMatrixEvalInf[z1, z2, z3, w2, w3]]
     ]
    ]
   ]
  ]
  
(*Basics*)

(*Generator Generation*)

(*Any group generator consists of the following three information: {D, D', A}, 
where D and D' are circles in for form of {center, radius} and A is a matrix 
corresponding to a Moebius Transformation that maps the exterior of D to the interior of D'
 Given D and D', we generate one such element
*)

Generation`IsInner[{p1_, r1_}, {p2_, 
    r2_}] := (Abs[p1 - p2] > r1) && (Abs[p1 - p2] > r2);

Generation`GetSimpleGeneratorMatrix[{p1_, r1_}, {p2_, r2_}, \[Phi]_ :
     0] := Module[{A, inner},
   inner = (Abs[p1 - p2] > r1) && (Abs[p1 - p2] > r2);
   If[inner,
    A = {{p2, e[\[Phi]] r1 r2 - p1 p2}, {1, -p1}},
    A = {{e[\[Phi]] r2/r1, -e[\[Phi]] r2/r1 p1 + p2}, {0, 1}}
    ];
   Return[A]];

Generation`GetSimpleGeneratorMap[c1_, c2_, \[Phi]_ : 0] := 
  Mobius`MatrixToTransformation[
   Generation`GetSimpleGeneratorMatrix[c1, c2, \[Phi]]];

Generation`GetSimpleGroupElement[c1_, c2_, \[Phi]_ : 0] := 
  Return[{c1, c2, 
    Generation`GetSimpleGeneratorMatrix[c1, c2, \[Phi]]}];

Generation`GetSimpleSchottkyGroup[clist_] := 
  If[Length[#] == 3, 
     Generation`GetSimpleGroupElement[#[[1]], #[[2]], #[[3]]], 
     Generation`GetSimpleGroupElement[#[[1]], #[[2]]]] & /@ clist;

(*Getters and Setters*)

IO`GetCirclePair[{c1_, c2_, A_}] := {c1, c2};
IO`GetMatrix[{c1_, c2_, A_}] := A;
IO`GetQ[{c1_, c2_, A_}] := A[[1, 1]]/A[[2, 2]];

(*Generating the Group*)

Group`GetAllMatrices[circpairs_, n_] := 
 With[{generators = IO`GetMatrix[#] & /@ circpairs},
  MatrixGroup`AllMatrices[generators, n] 
  ]

Group`GetAllMaps[circpairs_, n_] := 
 With[{matrices = Group`GetAllMatrices[circpairs, n]}, 
  Mobius`MatrixToTransformation[#] & /@ matrices]

(*Graphics*)

(*Ranges*)

Graphics`GetComplexRange[circpairs_, feather_ : 0.2] := 
 Module[{values, rmin, rmax, imin, imax},
  values = 
   Flatten[{circpairs[[#[[1]]]][[#[[2]]]][[1]] + 
        circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] + 
        I circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] - circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] - 
        I circpairs[[#[[1]]]][[#[[2]]]][[2]]
       } & /@ ListProduct[Table[n, {n, 1, Length[circpairs]}], {1, 2}]];
  rmin = Min[Re[values]] - feather;
  rmax = Max[Re[values]] + feather;
  imin = Min[Im[values]] - feather;
  imax = Max[Im[values]] + feather;
  Return[{{rmin + I imin}, {rmax + I imax}}];
  ]

Graphics`GetGraphicsRange[circpairs_, feather_ : 0.2] := 
 Module[{values, rmin, rmax, imin, imax},
  values = 
   Flatten[{circpairs[[#[[1]]]][[#[[2]]]][[1]] + 
        circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] + 
        I circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] - circpairs[[#[[1]]]][[#[[2]]]][[2]],
       circpairs[[#[[1]]]][[#[[2]]]][[1]] - 
        I circpairs[[#[[1]]]][[#[[2]]]][[2]]
       } & /@ ListProduct[Table[n, {n, 1, Length[circpairs]}], {1, 2}]];
  rmin = Min[Re[values]] - feather;
  rmax = Max[Re[values]] + feather;
  imin = Min[Im[values]] - feather;
  imax = Max[Im[values]] + feather;
  Return[ApplySquarificationOfRange[{{rmin, rmax}, {imin, imax}}]];
  ]

(*Display Cover*)

Graphics`DisplayCirclePair[circpair_] := 
  ComplexCircle[#] & /@ IO`GetCirclePair[circpair];
Graphics`DisplayCirclePair[circpair_, color_] := Return[{
   Style[ComplexCircle[IO`GetCirclePair[circpair][[1]]], color],
   Style[ComplexCircle[IO`GetCirclePair[circpair][[2]]], {color, 
     Dashed}]
   }]

Graphics`DisplayCirclePairList[circpairs_] := 
  Graphics`DisplayCirclePair[#] & /@ circpairs;

Graphics`DisplayCover[circpairs_, n_] := 
 Module[{ret = {}, i}, With[{maps = Group`GetAllMaps[circpairs, n]},
   For[i = 1, i <= Length[circpairs], i++,
    AppendTo[ret, 
     Style[Graphics`DisplayCirclePair[circpairs[[i]], 
         Hue[(i - 1)/Length[circpairs]]], {Thick}] & /@ maps];
    AppendTo[ret, 
     Style[ComplexCircle[
         TransformCircle[IO`GetCirclePair[circpairs[[i]]][[1]], #]], 
        Hue[(i - 1)/Length[circpairs]]] & /@ maps];
    ];
   Return[ret];
   ]
  ]
  
(*Transforming Covers*)

Transformation`TransformCirclePairFromPSL[{{p1_, r1_}, {p2_, r2_}, 
   M_}, A_] := Module[
  {c1, c2},
  c1 = Mobius`TranformCircleFromMatrix[{p1, r1}, A];
  c2 = Mobius`TranformCircleFromMatrix[{p2, r2}, A];
  Return[{c1, c2, A . M . Inverse[A]}]
  ]
Transformation`TransformCoverFromPSL[C_, A_] := 
  Transformation`TransformCirclePairFromPSL[#, A] & /@ C;

(*Canonical B-Cycle*)

(*Fixed Point Inversion*)

BranchCut`GetFixedPoints[{c1_, c2_, M_}] := 
 With[{p = Mobius`FixedPoint[M]},
  If[Length[p] == 1,
   Return[p],
   If[Abs[p[[1]] - c1[[1]]] < c1[[2]], Return[p], Return[{p[[2]], p[[1]]}]]
   ]
  ]

BranchCut`GetFixedPointInversionMatrix[{c1_, c2_, M_}, \[Lambda]_ : 
   1] := With[{p = BranchCut`GetFixedPoints[{c1, c2, M}]},
  If[Length[p] == 1,
   Return[{\[Lambda] {1, -p[[1]]}, {0, 1}}],
   Return[{\[Lambda] {1, -p[[2]]}, {1, -p[[1]]}}];
   ]
  ]
BranchCut`GetNormalizedFixedPointInversionMatrix[C_, 
  p_, \[Lambda]_ : 1] := 
 With[{A0 = BranchCut`GetFixedPointInversionMatrix[C, \[Lambda]]},
  Return[{{1/Mobius`MatrixToTransformation[A0][p], 0}, {0, 1}} . A0];
  ]


(*B Cycle Curve Generation*)

Options[BranchCut`GetConcentricBCycleCurve] = {
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCut`GetConcentricBCycleCurve[{c1_, c2_, M_}, 
  OptionsPattern[]] := Module[{p, q, \[Gamma]},
  q = M[[1, 1]]/M[[2, 2]];
  p = c1[[1]] + e[OptionValue["\[Phi]"]] c1[[2]];
  \[Gamma][t_] := 
   p ComplexPower[q, 
     OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
  Return[\[Gamma]];
  ]

Options[BranchCut`GetBCycleCurve] =
  {
   "\[Lambda]" -> 1,
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCut`GetBCycleCurve[{c1_, c2_, M_}, OptionsPattern[]] := Module[{
   A = BranchCut`GetFixedPointInversionMatrix[{c1, c2, M}, 
     OptionValue["\[Lambda]"]],
   c, p, q, \[Gamma]},
  c = Transformation`TransformCirclePairFromPSL[{c1, c2, M}, A];
  q = c[[3, 1, 1]]/c[[3, 2, 2]];
  p = c[[1, 1]] + e[OptionValue["\[Phi]"]] c[[1, 2]];
  \[Gamma][t_] := 
   p ComplexPower[q, 
     OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
  Return[Mobius`MatrixToTransformation[Inverse[A]]@*\[Gamma]];
  ]

Options[BranchCut`GetBCycleIntersectionPoints] =
  {
   "\[Lambda]" -> 1,
   "\[Phi]" -> 0
   };
BranchCut`GetBCycleIntersectionPoints[C_, OptionsPattern[]] := 
 With[{\[Gamma] = 
    BranchCut`GetBCycleCurve[C, 
     "\[Lambda]" -> OptionValue["\[Lambda]"], 
     "\[Phi]" -> OptionValue["\[Phi]"]]},
  Return[Flatten[{\[Gamma][0], \[Gamma][1]}]];
  ]

Options[BranchCut`GetNormalizedBCycleCurve] =
  {
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCut`GetNormalizedBCycleCurve[{c1_, c2_, M_}, 
   OptionsPattern[]] :=
  If[(c1[[1]] == 0) && (c2[[1]] == 0),
   Return[BranchCut`GetConcentricBCycleCurve[{c1, c2, M}, 
     "range" -> OptionValue["range"], "\[Phi]" -> OptionValue["\[Phi]"]]],
   Module[{
     A = BranchCut`GetFixedPointInversionMatrix[{c1, c2, M}],
     c, p, q, \[Gamma]},
    c = Transformation`TransformCirclePairFromPSL[{c1, c2, M}, A];
    q = c[[3, 1, 1]]/c[[3, 2, 2]];
    p = c[[1, 1]] + e[OptionValue["\[Phi]"]] c[[1, 2]];
    \[Gamma][t_] := 
     p ComplexPower[q, 
       OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
    Return[Mobius`MatrixToTransformation[Inverse[A]]@*\[Gamma]];
    ]
   ];

(*Get List of B Cycles*)

Options[BranchCut`GetNormalizedBCycleCurveList] =
  {
   "\[Phi]" -> {},
   "range" -> {0, 1}
   };
BranchCut`GetNormalizedBCycleCurveList[C_, OptionsPattern[]] := 
 If[Length[OptionValue["\[Phi]"]] == Length[C],
  Return[BranchCut`GetNormalizedBCycleCurve[#[[1]], 
      "\[Phi]" -> #[[2]], "range" -> OptionValue["range"]] & /@ 
    Pair[C, OptionValue["\[Phi]"]]],
  Return[BranchCut`GetNormalizedBCycleCurve[#, 
       "range" -> OptionValue["range"]] & /@ C];
  ]


(*Display All B Cycles*)

Options[BranchCut`DisplayNormalizedBCycleCurveList] =
  {
   "\[Phi]" -> {},
   "range" -> {0, 1}
   };
BranchCut`DisplayNormalizedBCycleCurveList[C_, N_, 
   OptionsPattern[]] := 
  ParametricLine[#, N] & /@ 
   BranchCut`GetNormalizedBCycleCurveList[C, 
    "\[Phi]" -> OptionValue["\[Phi]"], "range" -> OptionValue["range"]];

(*Logarithms and Branch Cuts*)

BranchCut`GetLogMap[q_, b_ : 1] := Module[{c, tr, re, BelowBranch, f},
  c[t_] := b ComplexPower[q, t];
  tr[p_] := Log[Abs[p/b]]/Log[Abs[q]];
  BelowBranch[p_] := ComplexAngle[p] <= ComplexAngle[c[tr[p]]];
  
  f[z_] := If[BelowBranch[z], ComplexLogarithm[z] + 1, ComplexLogarithm[z]];
  Return[f];
  ]

BranchCut`GetLogMapToFundamentalStrip[q_] := 
 Module[{\[Tau] = ComplexLogarithm[q], f},
  f[z_] := 
   With[{l = Lattice`GetLatticeRepresentation[ComplexLogarithm[z], \[Tau]]}, 
    l[[1]] + l[[3]] \[Tau]];
  Return[f];
  ]
  
End[] (* End Private Context *)

EndPackage[]