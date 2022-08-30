(* Wolfram Language Package *)
BeginPackage["Schottky`"]
(* Exported symbols added here with SymbolName::usage *)  

IOGetQ::usage = "get q parameter";
GenerationGetSimpleSchottkyGroup::usage = "Obtain a simple cover by using circle pairs";
BranchCutGetFixedPoints::usage = "Get fixed point of a given schottky generator";
GraphicsDisplayCover::usage = "Get graphics element of a schottky cover";
GraphicsGetGraphicsRange::usage = "Get the real plot range given a Schottky cover";
BranchCutGetLogMap::usage = "Get the ComplexLogarithm function with branch cut along a logarithmic spirad defined by q";
BranchCutGetNormalizedBCycleCurveList::usage = "Get a list of functions parameterizing the loxodromes corresponding to each generator of a Schottky group";
BranchCutDisplayNormalizedBCycleCurveList::usage = "Get a list graphical objects corresponding to the loxodromes corresponding to each generator of a Schottky group";
Transformation::TransformCirclePairFromPSL::usage = "Transform a Schottky cover by a mobius transformation given its matrix representation";
GroupGetAllMaps::usage = "Get a maps up to a certain word length of a Schottky cover";


Begin["`Private`"] (* Begin Private Context *) 
Needs["ShkyMath`","setup/Math.wl"];
Needs["Graphics`","setup/Visual.wl"];

MobiusMatrixToTransformation[{{a_, b_}, {c_, d_}}] := Module[{f},
  f[z_] := (a z + b)/(c z + d);
  Return[f];
  ]
MobiusMatrixToTransformationDer[{{a_, b_}, {c_, d_}}] := Module[{f},
  f[z_] := a/(c z + d) - c (a z + b)/(c z + d)^2;
  Return[f];
  ]
MobiusMatrixImageInf[{{a_, b_}, {c_, d_}}] := 
  If[c == 0, Return[\[Infinity]], Return[a/c]];
MobiusMatrixPreImageInf[{{a_, b_}, {c_, d_}}] := 
  If[c == 0, Return[\[Infinity]], Return[-d/c]];
MobiusFixedPoint[{{a_, b_}, {c_, d_}}] := Module[{term1, term2},
  If[c == 0,
   Return[{(b/d)/(1 - a/d)}]];
  term1 = (a - d)/(2 c);
  term2 = 1/(2 c) ((a - d)^2 + 4 c b)^(1/2);
  Return[{term1 + term2, term1 - term2}];
  ]

MobiusMatrixToCircle[{{a0_, b0_}, {c0_, d0_}}] := If[a0 == 0,
   Return[{-d0/c0, 0, b0/c0}],
   With[{b = b0/a0, c = c0/a0, d = d0/a0}, Return[{-d/c, 1/c, b/c - d/c^2}]]
   ];
MobiusCircleToMatrix[{p0_, 
    p1_, \[Phi]_}] := {{p1, -p0 p1 + \[Phi]}, {1, -p0}};
MobiusCircleToTransformation[{p0_, p1_, r_}] := 
  Module[{f}, f[z_] := r/(z - p0) + p1; Return[f]];
MobiusTranformCircleFromMatrix[{p_, r_}, {{a_, b_}, {c_, d_}}] := 
 Module[{p0, p1, \[Phi]},
  If[c == 0, Return[{a/d p + b/d, Abs[a/d r]}]];
  With[{A = {{a, b}, {c, d}}},
   {p0, p1, \[Phi]} = MobiusMatrixToCircle[A];
   Return[{\[Phi] Conjugate[(p - p0)/(Abs[p - p0]^2 - r^2)] + p1, 
     Abs[(\[Phi] r)/(Abs[p - p0]^2 - r^2)]}];
   ]
  ]

MobiusCircleIsInvertedFromMatrix[{p_, r_}, {{a_, b_}, {c_, d_}}] := 
 Module[{p0, p1, \[Phi]},
  If[c == 0, Return[False]];
  With[{A = {{a, b}, {c, d}}},
   {p0, p1, \[Phi]} = MobiusMatrixToCircle[A];
   Return[If[Abs[p - p0] < r, True, False]];
   ]
  ]

(*Cross Ratio*)

CrossRatio[x1_, x2_, x3_, x4_] := ((x1 - x2) (x3 - x4))/((x2 - x3) (x4 - x1));

(*Transformation to Matrix*)

MobiusTransformationToMatrixEval[z1_, z2_, z3_, w1_, w2_, w3_] := 
 Module[{a, b, c, d},
  a = Det[{{z1 w1, w1, 1}, {z2 w2, w2, 1}, {z3 w3, w3, 1}}];
  b = Det[{{z1 w1, z1, w1}, {z2 w2, z2, w2}, {z3 w3, z3, w3}}];
  c = Det[{{z1, w1, 1}, {z2, w2, 1}, {z3, w3, 1}}];
  d = Det[{{z1 w1, z1, 1}, {z2 w2, z2, 1}, {z3 w3, z3, 1}}];
  Return[{{a, b}, {c, d}}/(a d - c b)^(1/2)];
  ]

MobiusTransformationToMatrixEvalInf[z1_, z2_, z3_, w2_, w3_] := 
 Module[{a, b, c, d},
  a = z1 (w2 - w3) - z2 w2 + z3 w3;
  b = z1 (z2 w3 - z3 w2) + z2 z3 (w2 - w3);
  c = z3 - z2;
  d = z1 (z2 - z3);
  Return[{{a, b}, {c, d}}/(a d - c b)^(1/2)];
  ]

MobiusTransformationToMatrix[f_] := Module[{InfPos = 0, list = {1, 0, I}},
  Quiet@Check[f[1], InfPos = 1];
  Quiet@Check[f[0], InfPos = 2];
  Quiet@Check[f[I], InfPos = 3];
  If[InfPos == 0,
   With[{z1 = 1, z2 = 0, z3 = I},
    With[{w1 = f[z1], w2 = f[z2], w3 = f[z3]},
     Return[MobiusTransformationToMatrixEval[z1, z2, z3, w1, w2, w3]];
     ]
    ],
   With[{z1 = list[[InfPos]], z2 = Delete[list, InfPos][[1]], 
     z3 = Delete[list, InfPos][[2]]},
    With[{w2 = f[z2], w3 = f[z3]},
     Return[MobiusTransformationToMatrixEvalInf[z1, z2, z3, w2, w3]]
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

GenerationIsInner[{p1_, r1_}, {p2_, 
    r2_}] := (Abs[p1 - p2] > r1) && (Abs[p1 - p2] > r2);

GenerationGetSimpleGeneratorMatrix[{p1_, r1_}, {p2_, r2_}, \[Phi]_ :
     0] := Module[{A, inner},
   inner = (Abs[p1 - p2] > r1) && (Abs[p1 - p2] > r2);
   If[inner,
    A = {{p2, e[\[Phi]] r1 r2 - p1 p2}, {1, -p1}},
    A = {{e[\[Phi]] r2/r1, -e[\[Phi]] r2/r1 p1 + p2}, {0, 1}}
    ];
   Return[A]];

GenerationGetSimpleGeneratorMap[c1_, c2_, \[Phi]_ : 0] := 
  MobiusMatrixToTransformation[
   GenerationGetSimpleGeneratorMatrix[c1, c2, \[Phi]]];

GenerationGetSimpleGroupElement[c1_, c2_, \[Phi]_ : 0] := 
  Return[{c1, c2, 
    GenerationGetSimpleGeneratorMatrix[c1, c2, \[Phi]]}];

GenerationGetSimpleSchottkyGroup[clist_] := 
  If[Length[#] == 3, 
     GenerationGetSimpleGroupElement[#[[1]], #[[2]], #[[3]]], 
     GenerationGetSimpleGroupElement[#[[1]], #[[2]]]] & /@ clist;

(*Getters and Setters*)

IOGetCirclePair[{c1_, c2_, A_}] := {c1, c2};
IOGetMatrix[{c1_, c2_, A_}] := A;
IOGetQ[{c1_, c2_, A_}] := A[[1, 1]]/A[[2, 2]];

(*Generating the Group*)

GroupGetAllMatrices[circpairs_, n_] := 
 With[{generators = IOGetMatrix[#] & /@ circpairs},
  MatrixGroupAllMatrices[generators, n] 
  ]

GroupGetAllMaps[circpairs_, n_] := 
 With[{matrices = GroupGetAllMatrices[circpairs, n]}, 
  MobiusMatrixToTransformation[#] & /@ matrices]

(*Graphics*)

(*Ranges*)

GraphicsGetComplexRange[circpairs_, feather_ : 0.2] := 
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

GraphicsGetGraphicsRange[circpairs_, feather_ : 0.2] := 
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

GraphicsDisplayCirclePair[circpair_] := 
  ComplexCircle[#] & /@ IOGetCirclePair[circpair];
GraphicsDisplayCirclePair[circpair_, color_] := Return[{
   Style[ComplexCircle[IOGetCirclePair[circpair][[1]]], color],
   Style[ComplexCircle[IOGetCirclePair[circpair][[2]]], {color, 
     Dashed}]
   }]

GraphicsDisplayCirclePairList[circpairs_] := 
  GraphicsDisplayCirclePair[#] & /@ circpairs;

GraphicsDisplayCover[circpairs_, n_] := 
 Module[{ret = {}, i}, With[{maps = GroupGetAllMaps[circpairs, n]},
   For[i = 1, i <= Length[circpairs], i++,
    AppendTo[ret, 
     Style[GraphicsDisplayCirclePair[circpairs[[i]], 
         Hue[(i - 1)/Length[circpairs]]], {Thick}] & /@ maps];
    AppendTo[ret, 
     Style[ComplexCircle[
         TransformCircle[IOGetCirclePair[circpairs[[i]]][[1]], #]], 
        Hue[(i - 1)/Length[circpairs]]] & /@ maps];
    ];
   Return[ret];
   ]
  ]
  
(*Transforming Covers*)

TransformationTransformCirclePairFromPSL[{{p1_, r1_}, {p2_, r2_}, 
   M_}, A_] := Module[
  {c1, c2},
  c1 = MobiusTranformCircleFromMatrix[{p1, r1}, A];
  c2 = MobiusTranformCircleFromMatrix[{p2, r2}, A];
  Return[{c1, c2, A . M . Inverse[A]}]
  ]
TransformationTransformCoverFromPSL[C_, A_] := 
  TransformationTransformCirclePairFromPSL[#, A] & /@ C;

(*Canonical B-Cycle*)

(*Fixed Point Inversion*)

BranchCutGetFixedPoints[{c1_, c2_, M_}] := 
 With[{p = MobiusFixedPoint[M]},
  If[Length[p] == 1,
   Return[p],
   If[Abs[p[[1]] - c1[[1]]] < c1[[2]], Return[p], Return[{p[[2]], p[[1]]}]]
   ]
  ]

BranchCutGetFixedPointInversionMatrix[{c1_, c2_, M_}, \[Lambda]_ : 
   1] := With[{p = BranchCutGetFixedPoints[{c1, c2, M}]},
  If[Length[p] == 1,
   Return[{\[Lambda] {1, -p[[1]]}, {0, 1}}],
   Return[{\[Lambda] {1, -p[[2]]}, {1, -p[[1]]}}];
   ]
  ]
BranchCutGetNormalizedFixedPointInversionMatrix[C_, 
  p_, \[Lambda]_ : 1] := 
 With[{A0 = BranchCutGetFixedPointInversionMatrix[C, \[Lambda]]},
  Return[{{1/MobiusMatrixToTransformation[A0][p], 0}, {0, 1}} . A0];
  ]


(*B Cycle Curve Generation*)

Options[BranchCutGetConcentricBCycleCurve] = {
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCutGetConcentricBCycleCurve[{c1_, c2_, M_}, 
  OptionsPattern[]] := Module[{p, q, \[Gamma]},
  q = M[[1, 1]]/M[[2, 2]];
  p = c1[[1]] + e[OptionValue["\[Phi]"]] c1[[2]];
  \[Gamma][t_] := 
   p ComplexPower[q, 
     OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
  Return[\[Gamma]];
  ]

Options[BranchCutGetBCycleCurve] =
  {
   "\[Lambda]" -> 1,
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCutGetBCycleCurve[{c1_, c2_, M_}, OptionsPattern[]] := Module[{
   A = BranchCutGetFixedPointInversionMatrix[{c1, c2, M}, 
     OptionValue["\[Lambda]"]],
   c, p, q, \[Gamma]},
  c = TransformationTransformCirclePairFromPSL[{c1, c2, M}, A];
  q = c[[3, 1, 1]]/c[[3, 2, 2]];
  p = c[[1, 1]] + e[OptionValue["\[Phi]"]] c[[1, 2]];
  \[Gamma][t_] := 
   p ComplexPower[q, 
     OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
  Return[MobiusMatrixToTransformation[Inverse[A]]@*\[Gamma]];
  ]

Options[BranchCutGetBCycleIntersectionPoints] =
  {
   "\[Lambda]" -> 1,
   "\[Phi]" -> 0
   };
BranchCutGetBCycleIntersectionPoints[C_, OptionsPattern[]] := 
 With[{\[Gamma] = 
    BranchCutGetBCycleCurve[C, 
     "\[Lambda]" -> OptionValue["\[Lambda]"], 
     "\[Phi]" -> OptionValue["\[Phi]"]]},
  Return[Flatten[{\[Gamma][0], \[Gamma][1]}]];
  ]

Options[BranchCutGetNormalizedBCycleCurve] =
  {
   "\[Phi]" -> 0,
   "range" -> {0, 1}
   };
BranchCutGetNormalizedBCycleCurve[{c1_, c2_, M_}, 
   OptionsPattern[]] :=
  If[(c1[[1]] == 0) && (c2[[1]] == 0),
   Return[BranchCutGetConcentricBCycleCurve[{c1, c2, M}, 
     "range" -> OptionValue["range"], "\[Phi]" -> OptionValue["\[Phi]"]]],
   Module[{
     A = BranchCutGetFixedPointInversionMatrix[{c1, c2, M}],
     c, p, q, \[Gamma]},
    c = TransformationTransformCirclePairFromPSL[{c1, c2, M}, A];
    q = c[[3, 1, 1]]/c[[3, 2, 2]];
    p = c[[1, 1]] + e[OptionValue["\[Phi]"]] c[[1, 2]];
    \[Gamma][t_] := 
     p ComplexPower[q, 
       OptionValue["range"][[1]] (1 - t) + OptionValue["range"][[2]] t];
    Return[MobiusMatrixToTransformation[Inverse[A]]@*\[Gamma]];
    ]
   ];

(*Get List of B Cycles*)

Options[BranchCutGetNormalizedBCycleCurveList] =
  {
   "\[Phi]" -> {},
   "range" -> {0, 1}
   };
BranchCutGetNormalizedBCycleCurveList[C_, OptionsPattern[]] := 
 If[Length[OptionValue["\[Phi]"]] == Length[C],
  Return[BranchCutGetNormalizedBCycleCurve[#[[1]], 
      "\[Phi]" -> #[[2]], "range" -> OptionValue["range"]] & /@ 
    Pair[C, OptionValue["\[Phi]"]]],
  Return[BranchCutGetNormalizedBCycleCurve[#, 
       "range" -> OptionValue["range"]] & /@ C];
  ]


(*Display All B Cycles*)

Options[BranchCutDisplayNormalizedBCycleCurveList] =
  {
   "\[Phi]" -> {},
   "range" -> {0, 1}
   };
BranchCutDisplayNormalizedBCycleCurveList[C_, N_, 
   OptionsPattern[]] := 
  ParametricLine[#, N] & /@ 
   BranchCutGetNormalizedBCycleCurveList[C, 
    "\[Phi]" -> OptionValue["\[Phi]"], "range" -> OptionValue["range"]];

(*Logarithms and Branch Cuts*)

BranchCutGetLogMap[q_] := 
 Module[{\[Tau] = ComplexLogarithm[q], f},
  f[z_] := 
   With[{l = LatticeGetLatticeRepresentation[ComplexLogarithm[z], \[Tau]]}, 
    l[[1]] + l[[3]] \[Tau]];
  Return[f];
  ]
  
End[] (* End Private Context *)

EndPackage[]