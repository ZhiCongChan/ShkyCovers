(* Wolfram Language Package *)

BeginPackage["Graphics`"]
(* Exported symbols added here with SymbolName::usage *)  

ParametricLine::usage = "Draw a line with n connected dots";
ComplexCircle::usage = "Draw a cicle defined by center and radius on the complex plane";

Begin["`Private`"] (* Begin Private Context *) 
Needs["ShkyMath`"];
(*Geometric Objects*)

(*Points*)
ComplexPoint[p_] := Point[ReIm[p]];

(*Lines*)

ComplexLineAB[a_, b_] := Line[ReIm[{a, b}]];
ComplexLinePF[p_, \[Phi]_, L_ : 10] := 
  Line[ReIm[{p - L Exp[I \[Phi]], p + L Exp[I \[Phi]]}]];

(*Circles*)

ComplexCircle[p_, r_] := Circle[ReIm[p], r];
ComplexCircle[{p_, r_}] := Circle[ReIm[p], r];
ComplexCircle[{p_, r_}, style_] := Style[Circle[ReIm[p], r], style];

(*Polygons*)

ComplexTriangle[p1_, p2_, p3_] := Return[{ComplexLineAB[p1, p2],
    ComplexLineAB[p2, p3],
    ComplexLineAB[p3, p1]}];

ComplexParallelogram[b_, {w1_, w2_}] := Return[
  {ComplexLineAB[b, b + w1],
   ComplexLineAB[b, b + w2],
   ComplexLineAB[b + w1, b + w1 + w2],
   ComplexLineAB[b + w2, b + w1 + w2]
   }]
ComplexParallelogram[{b_, w1_, w2_}] := ComplexParallelogram[b, {w1, w2}]

(*Grids*)

ComplexGrid[{c_, w1_, w2_}, n_] := 
 Flatten[{ComplexLineAB[c + w2 # - w1 n, c + w2 # + w1 n], 
     ComplexLineAB[c + w1 # - w2 n, c + w1 # + w2 n]} & /@ 
   Table[i, {i, -n, n}]]

ComplexGridWithColor[{c_, w1_, w2_}, n_, {color1_, color2_}] := 
 Flatten[{Style[ComplexLineAB[c + w2 # - w1 n, c + w2 # + w1 n], color1], 
     Style[ComplexLineAB[c + w1 # - w2 n, c + w1 # + w2 n], color2]} & /@ 
   Table[i, {i, -n, n}]]
   
(*Plot Ranges*)

(*Get minimum square range such that a given complex number range will be displayed*)

SquareRange[range_] := Module[{max},
  max = Max[Flatten[{Abs[Re[range]], Abs[Im[range]]}]];
  Return[max {-1 - I, 1 + I}];
  ]

(*Does the same as the above but gives a range with an x in front*)

SquareRangeX[range_] := Flatten[{x, SquareRange[range]}];

(*Real Ranges*)

SquareRangeR[x_, p_ : 0] := Module[{max, px = Re[p], py = Im[p]},
  max = Max[Flatten[{Abs[Re[x]], Abs[Im[x]]}]];
  Return[{{-max + px, max + px}, {-max + py, max + py}}];
  ]

ComplexToGraphicsRange[{z1_, z2_}] := 
  Return[{{Re[z1], Re[z2]}, {Im[z1], Im[z2]}}];

ApplySquarificationOfRange[{{x1_, x2_}, {y1_, y2_}}, pad_ : 1] := 
  With[{diameter = pad Max[{x2 - x1, y2 - y1}]},
   Return[{{(x1 + x2)/2 - diameter/2, (x1 + x2)/2 + diameter/2}, {(y1 + y2)/
        2 - diameter/2, (y1 + y2)/2 + diameter/2}}];
   ];

(*Contour Plots*)

(*Single Plots*)

Options[ComplexPlotBasic] = {
   "range" -> {x, Corner[3, 1], Corner[1, 3]},
   "label" -> "",
   "Epilog" -> {},
   "size" -> {250, 250}
   };
ComplexPlotBasic[f_, OptionsPattern[]] := Module[{ret, range, label},
   Clear[x];
   range = OptionValue["range"];
   label = OptionValue["label"];
   If[StringLength[label] == 0,
    ret = ComplexPlot[f[x], range, Epilog -> OptionValue["Epilog"], 
      ImageSize -> OptionValue["size"]],
    ret = ComplexPlot[f[x], range, PlotLabel -> label, 
      Epilog -> OptionValue["Epilog"], ImageSize -> OptionValue["size"]]
    ];
   Return[ret];
   ];

Options[ComplexPlotWithGrid] = {
   "range" -> {x, e[5/8] 1, e[1/8] 3},
   "label" -> ""
   };
ComplexPlotWithGrid[f_, paralellogram_, OptionsPattern[]] := 
  Module[{ret, grid, fundplane, range, label},
   Clear[x];
   range = OptionValue["range"];
   label = OptionValue["label"];
   grid = ComplexGrid[paralellogram, 5];
   fundplane = Style[ComplexParallelogram[paralellogram], White];
   AppendTo[grid, fundplane];
   If[StringLength[label] == 0,
    ret = ComplexPlot[f[x], range, Epilog -> grid],
    ret = ComplexPlot[f[x], range, Epilog -> grid, PlotLabel -> label]
    ];
   Return[ret];
   ];

(*Multiple Plots*)

Options[ComplexPlotList] = {
   "range" -> {x, e[5/8] 1, e[1/8] 3},
   "labels" -> {},
   "size" -> {300, 300},
   "Epilog" -> {}
   };
ComplexPlotList[list_, OptionsPattern[]] := Module[{graphs, labels, range},
  labels = OptionValue["labels"];
  range = OptionValue["range"];
  If[Length[labels] == Length[list],
   graphs = 
     ComplexPlotBasic[#[[1]], "range" -> OptionValue["range"], 
        "label" -> #[[2]], "Epilog" -> OptionValue["Epilog"]] & /@ 
      Pair[list, labels];
   ,
   graphs = 
     ComplexPlotBasic[#, "range" -> OptionValue["range"], 
        "Epilog" -> OptionValue["Epilog"]] & /@ list;
   ];
  Return[GraphicsRow[graphs, Frame -> All, 
    ImageSize -> {Length[list], 1} OptionValue["size"]]];
  ]

Options[ComplexPlotWithGridList] = {
   "range" -> {x, Corner[3, 1], Corner[1, 3]},
   "labels" -> {},
   "size" -> {300, 300}
   };
ComplexPlotWithGridList[list_, paralellogram_, OptionsPattern[]] := 
 Module[{graphs, labels, range},
  labels = OptionValue["labels"];
  range = OptionValue["range"];
  If[Length[labels] == Length[list],
   graphs = 
     ComplexPlotWithGrid[#[[1]], paralellogram, 
        "range" -> OptionValue["range"], "label" -> #[[2]]] & /@ 
      Pair[list, labels];
   ,
   graphs = 
     ComplexPlotWithGrid[#, paralellogram, 
        "range" -> OptionValue["range"]] & /@ list;
   ];
  Return[GraphicsRow[graphs, Frame -> All, 
    ImageSize -> {Length[list], 1} OptionValue["size"]]];
  ]

(*Area Plots*)

Options[PlotDomain] = {
   "plotregion1" -> {z, -2 - 1/2 I, 2 + 3.5 I},
   "plotregion2" -> {z, -1 - I, 1 + I},
   "accuracy1" -> 2,
   "accuracy2" -> 5
   };
PlotDomain[cond_, transf_, OptionsPattern[]] := Module[{},
  Clear[z];
  GraphicsRow[{
    ComplexRegionPlot[cond[z], OptionValue["plotregion1"], 
     MaxRecursion -> OptionValue["accuracy1"]],
    ComplexRegionPlot[cond[transf[z]], OptionValue["plotregion2"], 
     MaxRecursion -> OptionValue["accuracy2"]]
    }
   ]
  ]

(*Line Orbit Plots*)

ParametricLine[f_, N_] := Line[ParametricPointsR[f, N]];
ParametricLine[f_, N_, style_] := Style[Line[ParametricPointsR[f, N]], style];
ParametricLinePoints[f_, N_, style_] := 
  Style[ComplexPoint[#], style] & /@ ParametricPoints[f, N];

ParametricLineColored[f_, N_] := 
  Line[ParametricPointsR[f, N], 
   VertexColors -> Table[Blend[{Red, Blue}, n/N], {n, 0, N}]];

MapParametricLineAB[line_, f_, n_] := Line[ReIm[MapLineAB[line, f, n]]]

MapParametricCircle[circle_, f_, n_] := Line[ReIm[MapCircle[circle, f, n]]];

MapParametricGrid[{b_, w1_, w2_}, f_, N_, n_] := 
 Flatten[{MapParametricLineAB[{b + w2 # - w1 N, b + w2 # + w1 N}, f, n], 
     MapParametricLineAB[{b + w1 # - w2 N, b + w1 # + w2 N}, f, n]} & /@ 
   Table[i, {i, -N, N}]]
MapParametricGridWithColor[{b_, w1_, w2_}, f_, N_, n_, {color1_, color2_}] := 
 Flatten[{
     Style[MapParametricLineAB[{b + w2 # - w1 N, b + w2 # + w1 N}, f, n], 
      color1],
     Style[MapParametricLineAB[{b + w1 # - w2 N, b + w1 # + w2 N}, f, n], 
      color2]
     } & /@ Table[i, {i, -N, N}]]

MapParametricCurve[c_, f_, n_] := 
  Module[{g}, g[t_] := f[c[t]]; Return[Line[ParametricPointsR[g, n]]]];
MapParametricCurvePoints[c_, f_, n_] := 
  Module[{g}, g[t_] := f[c[t]]; 
   Return[Point[#] & /@ ParametricPointsR[g, n]]];

(*Point Generation*)

ComplexAnnulusPoints[{r1_, r2_}, {N_, M_}] := 
  Return[(LinearInterpolation[r1, r2, #[[1]]] e[#[[1]] 2 Pi + #[[2]]]) & /@ 
    Flatten[Table[{n/N, m/M}, {n, 0, N}, {m, 0, M}], 1]];

ComplexNonConcentricAnnulusPoints[{{p_, r_}, q_}, {N_, M_}] := 
  Return[q^#[[1]] (p + r e[#[[1]] 2 Pi + #[[2]]]) & /@ 
    Flatten[Table[{n/N, m/M}, {n, 0, N}, {m, 0, M}], 1]];

(*Colored Point Sets*)

(*Manipulating Sets*)

GetColoredSet[U_, fcol_] := Return[{#, fcol[#]} & /@ U];

DisplayColoredSet[UCol_] := 
  Return[Style[ComplexPoint[#[[1]]], #[[2]]] & /@ UCol];

TransformColoredSet[UCol_, f_] := Return[{f[#[[1]]], #[[2]]} & /@ UCol];

(*Set Defaults*)

ComplexHue[z_] := Hue[Arg[z]/(2 Pi)];

GetHueColoredSet[U_] := GetColoredSet[U, ComplexHue];

GetColoredNonConcentricAnnulusPoints[{{p_, r_}, q_}, {N_, M_}] := 
  Return[{ComplexPower[q, #[[1]]] (p + r e[#[[2]]]), Hue[#[[2]]]} & /@ 
    Flatten[Table[{n/N, m/M}, {n, 0, N}, {m, 0, M}], 1]];
   
End[] (* End Private Context *)

EndPackage[]