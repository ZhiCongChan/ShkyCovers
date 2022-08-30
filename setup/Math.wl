(* Wolfram Language Package *)

BeginPackage["ShkyMath`"]
(* Exported symbols added here with SymbolName::usage *)  

Pair::usage = "Combine two lists such that the indices are matched.";
ListProduct::usage = "Gives the Cartesian product of two lists.";

Begin["`Private`"] (* Begin Private Context *) 
Pair[l1_, l2_] := Module[{ret},
  ret = {};
  For[i = 1, i < Length[l1] + 1, i++,
   AppendTo[ret, {l1[[i]], l2[[i]]}]
   ];
  Return[ret];
  ]
ModifyListElement[list_, position_, value_] := Module[{ret, i},
  ret = {};
  For[i = 1, i <= Length[list], i++,
   If[i == position, AppendTo[ret, value], AppendTo[ret, list[[i]]]]
   ];
  Return[ret];
  ]

ListProduct[A_, B_] := Module[{ret, i, j},
  ret = {};
  For[i = 1, i <= Length[A], i++,
   For[j = 1, j <= Length[B], j++,
    AppendTo[ret, Flatten[{A[[i]], B[[j]]}]]
    ]
   ];
  Return[ret]
  ]
 
(*Basic Functions and Redefinitions*)

e[z_] := Exp[2 Pi I z];

TotalProduct[list_] := Times @@ list;
ComplexAngle[q_] := 
  Module[{y = Arg[q]/(2 Pi)}, If[y < 0, Return[y + 1], Return[y]]];
ComplexLogarithm[q_] := 
  If[Arg[q] < 0, 1/(2 Pi I) Log[q] + 1, 1/(2 Pi I) Log[q]];

LinearInterpolation[p1_, p2_, x_] := p1 (1 - x) + p2 x;

ComplexPower[q_, t_] := e[ComplexLogarithm[q] t];

(*Basic Function Manipulation*)


Der[f_, z_] := D[f[\[Xi]], \[Xi]] /. {\[Xi] -> z};

Derf[f_] := Module[{ret},
  ret[z_] := Der[f, z];
  Return[ret];
  ]

MultipleEvaluation[f_, z_, n_] := Module[{ret, i} ,
  ret = z;
  For[i = 1, i <= n, i++,
   ret = f[ret];
   ];
  Return[ret]
  ]
MultipleEvaluationWithInverse[f_, g_, z_, n_] := Module[{ret, i} ,
  ret = z;
  If[n >= 1,
   For[i = 1, i <= n, i++,
     ret = f[ret];
     ];,
   For[i = 1, i <= -n, i++,
     ret = g[ret];
     ];
   ];
  Return[ret]
  ]

GetMultipleEvaluation[f0_, n_] := Module[{f},
  f[z_] := MultipleEvaluation[f0, z, n];
  Return[f];
  ] 
  
  
(*Lattices*)

(*2D Grid Generation*)

CreateSummationGrid[min_, max_, withzero_ : True] := Module[{ret, diff},
   ret = Flatten[Table[Table[{nn, mm}, {nn, min, max}], {mm, min, max}], 1];
   diff = max - min;
   If[withzero || min > 0,
    Return[ret],
    Return[Delete[ret, -min (diff + 2) + 1]]
    ]
   ];

SymmetricGrid[n_, withzero_ : True] := CreateSummationGrid[-n, n, withzero];

PositiveGrid[n_, withzero_ : False] := 
  If[withzero, CreateSummationGrid[0, n], CreateSummationGrid[1, n]];

OddGrid[n_] := Module[{ret},
   ret = {};
   ret = ({2, 2} # + {1, 1}) & /@ PositiveGrid[n, True];
   Return[ret];
   ];

(*2D Coordinate Transformations*)

Lattice`GridPointToComplex[{s_, t_}, {b_, w1_, w2_}] := b + s w1 + t w2;
ComplexToLatticeCoord[z_, \[Tau]_] := {z - (Im[z]/Im[\[Tau]]) \[Tau], 
   Im[z]/Im[\[Tau]]};

Lattice`GetLatticeRepresentation[z_, \[Tau]_] := Module[{n, m, Imz0},
  n = Floor[Im[z]/Im[\[Tau]]];
  Imz0 = Im[z] - n Im[\[Tau]];
  m = Floor[Re[z] - n Re[\[Tau]] - Re[\[Tau]]/Im[\[Tau]] Imz0];
  Return[{z - m - n \[Tau], m, n}];
  ]

Lattice`GetFundamentalPoint[z_, \[Tau]_] := 
  Lattice`GetLatticeRepresentation[z, \[Tau]][[1]];
Lattice`GetLatticePosition[z_, \[Tau]_] := 
  With[{l = Lattice`GetLatticeRepresentation[z, \[Tau]][[2]]},
   Return[{l[[2]], l[[3]]}];
   ];

(*4n-Dimensional Grid Generation*)

Symmetric2NList[n_, N_] := Module[{ret, i},
   ret = SymmetricGrid[N];
   For[i = 1, i < n, i++,
    ret = ListProduct[ret, SymmetricGrid[N]];
    ];
   Return[ret];
   ];

(*Generic Grid Generation*)

SymmetricNList[n_, N_] := Module[{ret, i},
   ret = Table[x, {x, -N, N}];
   For[i = 1, i < n, i++,
    ret = ListProduct[ret, Table[x, {x, -N, N}]];
    ];
   Return[ret];
   ];

(*Returns a List of Arrays of Length n with Numbers from 1 to N*)

PositiveNList[n_, N_] := Module[{ret, i},
   ret = Table[x, {x, 1, N}];
   If[n == 1, Return[({#}) & /@ ret]];
   For[i = 1, i < n, i++,
    ret = ListProduct[ret, Table[x, {x, 1, N}]];
    ];
   Return[ret];
   ];

(*Lattice Summation*)

Options[SumLattice1D] := {
  "range" -> {-10, 10},
  "with_zero" -> True
  }
SumLattice1D[f_, OptionsPattern[]] := Module[{ret, lattice, range},
  range = OptionValue["range"];
  If[OptionValue["with_zero"],
   lattice = Table[n, {n, range[[1]], range[[2]]}]
   ,
   lattice = Table[n, {n, range[[1]], -1}];
   lattice = Flatten[{lattice, Table[n, {n, 1, range[[2]]}]}]
   ];
  ret = Total[f[#] & /@ lattice];
  Return[ret];
  ]

Options[SumLattice2D] := {
  "range" -> {-10, 10},
  "with_zero" -> True
  }
SumLattice2D[f_, OptionsPattern[]] := Module[{ret, lattice, range},
  range = OptionValue["range"];
  lattice = 
   CreateSummationGrid[range[[1]], range[[2]], OptionValue["with_zero"]];
  ret = Total[f[#[[1]], #[[2]]] & /@ lattice];
  Return[ret];
  ]

(*Misc Operators*)

MatrixReal[M_] := Module[{ret},
  ret = Re[#] & /@ M;
  Return[ret];
  ]
MatrixImag[M_] := Module[{ret},
  ret = Im[#] & /@ M;
  Return[ret];
  ]

(*Elliptic Functions*)

ToGridCoord[{a_, b_}, tau_] := Return[{b Re[tau] + a, b Im[tau]}];

(*Contour Integrals*)

LineParametrizationAB[{p1_, p2_}] := Module[{f},
  f[t_] := t p2 + (1 - t) p1;
  Return[f];
  ]

CircleParametrization[{p_, r_}] := Module[{f},
  f[t_] := p + r (Cos[2 Pi t] + I Sin[2 Pi t]);
  Return[f];
  ]

CircleParametrizationWithInitial[{p_, r_}, i_, gap_ : 0] := 
 Module[{a = Re[ComplexLogarithm[i - p]], f},
  f[t_] := p + r e[a] (Cos[2 Pi t] + I Sin[2 Pi t]);
  Return[LinearReparameterization[f, 0 + gap, 1 - gap]];
  ]

PathIntegral[f_, \[Gamma]_] := 
  Integrate[f[\[Gamma][t]] D[\[Gamma][tp], tp] /. {tp -> t}, {t, 0, 1}];

LinearReparameterization[map_, start_, finish_] := Module[{ret},
  ret[t_] := map[(finish - start) t + start];
  Return[ret];
  ]

End[] (* End Private Context *)

EndPackage[]