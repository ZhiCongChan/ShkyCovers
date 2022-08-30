(* Wolfram Language Package *)

BeginPackage["ShkyMath`"]
(* Exported symbols added here with SymbolName::usage *)  

Pair::usage = "Combine two lists such that the indices are matched.";
ListProduct::usage = "Gives the Cartesian product of two lists.";
ParametricPointsR::usage = "Get n points from a path";
Corner::usage = "Get one of the 8 points around the unit circle";
MapLineAB::usage = "Map a line defined by two points";
MapCircle::usage = "Map a circle defined by center and radius";
LinearInterpolation::usage = "Gives the linear interpolation of between two points";
e::usage = "e^(2pi i  z)";
ComplexPower::usage = "Exponential with different branch";


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
  
(*Group Theory*)

(*Group Action*)

(*Generators of the Group are written in the form {{a, a^-1}, {b,b^-1}, ...}. A word will be list of the form {{which generator,how many times}, {gen,n}, ....}
*)
ApplyGroupAction[z_, generators_, word_] := Module[{ret, i},
  ret = z;
  If[word == {{}}, Return[ret]];
  For[i = 1, i <= Length[word], i++,
   If[word[[i, 2]] != 0,
    If[word[[i, 2]] < 0,
     ret = 
      MultipleEvaluation[generators[[word[[i, 1]], 2]], ret, -word[[i, 2]]],
     ret = MultipleEvaluation[generators[[word[[i, 1]], 1]], ret, word[[i, 2]]]
     ]
    ]
   ];
  Return[ret]
  ]

GetGroupAction[generators_, word_] := Module[{ret},
  ret[z_] := ApplyGroupAction[z, generators, word];
  Return[ret];
  ]

(*Group Multiplication of Words*)

(*Reduce a word*)

ReduceWord[word_] := Module[{i, l, ret},
  ret = {};
  AppendTo[ret, word[[1]]];
  For[i = 2, i <= Length[word], i++,
   
   l = Length[ret];
   If[l == 0,
    AppendTo[ret, word[[i]]];,
    If[ret[[l, 1]] == word[[i, 1]],
     If[ret[[l, 2]] == -word[[i, 2]],
      ret = Delete[ret, l];,
      ret = 
        ModifyListElement[ret, l, {word[[i, 1]], word[[i, 2]] + ret[[l, 2]]}];
      ],
     AppendTo[ret, word[[i]]];
     ]
    ]
   ];
  If[Length[ret] == 0, Return[{{}}], Return[ret]];
  ]

(*Multiply two words*)

MultiplyWords[word1_, word2_] := 
  Return[ReduceWord[Flatten[{word1, word2}, 1]]];

(*Generation of all Group Elements of a Freely Generated Group*)

IsReducible[word_] := Module[{i},
  For[i = 1, i < Length[word], i++,
   If[word[[i]] == word[[i + 1]], Return[True]]
   ];
  Return[False]
  ]

integerPartitions[n_, {k_}] := 
 Select[FrobeniusSolve[Table[1, {k}], n], FreeQ[#, 0] &]

(*Gives the Partition of the number n into N different Numbers but consider +i and -i to be the same number for addition.*)

NegativePartitions[n_] := Module[{ret, temp, i, j},
  ret = {};
  For[i = 1, i <= n, i++,
   temp = integerPartitions[n, {i}];
   For[j = 1, j <= Length[temp], j++,
    ret = Join[ret, (# temp[[j]]) & /@ SignList[i]]
    ];
   ];
  Return[ret];
  ]

(*Returns a list of Permutation of N Elements of Length n*)

GenerateIrreducibleList[n_, N_] := Module[{initlist, ret, i},
  initlist = PositiveNList[n, N];
  ret = {};
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]], AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

(*Returns a Word of Length N for a group generated by n Elements*)

GenerateIrreducibleWordList[n_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = GenerateIrreducibleList[Length[numberlist[[i]]], n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

(*Writes out the Group Element Given the Generators and the Word*)

ShowGroupElement[generators_, word_] := Module[{temp, i},
  temp = {};
  If[word == {{}}, Return["e"]];
  For[i = 1, i <= Length[word], i++,
   If[word[[i, 2]] == 1,
    AppendTo[temp, generators[[word[[i, 1]]]]];
    ,
    AppendTo[temp, Superscript[generators[[word[[i, 1]]]], word[[i, 2]]]]
    ]
   ];
  RowBox[temp] // DisplayForm
  ]

(*Writes out all Words of Length N given the generators*)

ShowGroupElementLengthN[generators_, N_] := 
 ShowGroupElement[generators, #] & /@ 
  GenerateIrreducibleWordList[Length[generators], N]

(*Show all words up to length N*)

ShowGroupElementLengthUptoN[generators_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, ShowGroupElementLengthN[generators, i]]
   ];
  Return[Flatten[ret]]
  ]

(*Combined*)

(*Get the action of all elements given the generators of order up to N*)

GetAllGroupActions[generators_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, 
    GetGroupAction[generators, #] & /@ 
     GenerateIrreducibleWordList[Length[generators], i]]
   ];
  Return[Flatten[ret]];
  ]

(*Get the action of all elements given the generators of order up to N together with the word itself {{action, word},{action,word}}*)

GetAllGroupActionsWithWords[generators_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordList[Length[generators], i]]
   ];
  Return[Flatten[ret, 1]];
  ]

(*Applies the group action of all group elements of length up to N to the point z*)

ApplyAllGroupActions[z_, generators_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, 
    ApplyGroupAction[z, generators, #] & /@ 
     GenerateIrreducibleWordList[Length[generators], i]]
   ];
  Return[Flatten[ret]];
  ]



(*Right Subset*)

GenerateIrreducibleListR[n_, rlist_, N_] := 
 Module[{initlist, lastentry, ret, i, j},
  ret = {};
  If[n == 1,
   For[j = 1, j <= N, j++,
    If[ContainsAny[{j}, rlist], AppendTo[ret, {j}]];
    ];
   Return[ret];
   ];
  lastentry = {};
  For[j = 1, j <= N, j++,
   If[ContainsAny[{j}, rlist], AppendTo[lastentry, j]];
   ];
  initlist = ListProduct[PositiveNList[n - 1, N], lastentry];
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]],AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

GenerateIrreducibleWordListR[n_, rlist_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = GenerateIrreducibleListR[Length[numberlist[[i]]], rlist, n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

(*Left Subset*)

GenerateIrreducibleListL[n_, llist_, N_] := 
 Module[{initlist, lastentry, ret, i, j},
  ret = {};
  If[n == 1,
   For[j = 1, j <= N, j++,
    If[ContainsAny[{j}, llist], AppendTo[ret, {j}]];
    ];
   Return[ret];
   ];
  lastentry = {};
  For[j = 1, j <= N, j++,
   If[ContainsAny[{j}, llist], AppendTo[lastentry, j]];
   ];
  initlist = ListProduct[lastentry, PositiveNList[n - 1, N]];
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]],AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

GenerateIrreducibleWordListL[n_, llist_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = GenerateIrreducibleListL[Length[numberlist[[i]]], llist, n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

(*Right Cosets*)

(*Same as above but only for right cosets*)

GenerateIrreducibleListModR[n_, rlist_, N_] := 
 Module[{initlist, lastentry, ret, i, j},
  ret = {};
  If[n == 1,
   For[j = 1, j <= N, j++,
    If[!ContainsAny[{j}, rlist],AppendTo[ret, {j}]];
    ];
   Return[ret];
   ];
  lastentry = {};
  For[j = 1, j <= N, j++,
   If[!ContainsAny[{j}, rlist],AppendTo[lastentry, j]];
   ];
  initlist = ListProduct[PositiveNList[n - 1, N], lastentry];
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]],AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

GenerateIrreducibleWordListModR[n_, rlist_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = 
    GenerateIrreducibleListModR[Length[numberlist[[i]]], rlist, n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

GetAllGroupActionsModR[generators_, rlist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, 
    GetGroupAction[generators, #] & /@ 
     GenerateIrreducibleWordListModR[Length[generators], rlist, i]]
   ];
  Return[Flatten[ret]];
  ]

GetAllGroupActionsWithWordsModR[generators_, rlist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModR[Length[generators], rlist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

GetAllGroupActionsWithWordsModR[generators_, rlist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModR[Length[generators], rlist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

(*Left Cosets*)

GenerateIrreducibleListModL[n_, llist_, N_] := 
 Module[{initlist, lastentry, ret, i, j},
  ret = {};
  If[n == 1,
   For[j = 1, j <= N, j++,
    If[!ContainsAny[{j}, llist], AppendTo[ret, {j}]];
    ];
   Return[ret];
   ];
  lastentry = {};
  For[j = 1, j <= N, j++,
   If[!ContainsAny[{j}, llist], AppendTo[lastentry, j]];
   ];
  initlist = ListProduct[lastentry, PositiveNList[n - 1, N]];
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]], AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

GenerateIrreducibleWordListModL[n_, llist_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = 
    GenerateIrreducibleListModL[Length[numberlist[[i]]], llist, n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

GetAllGroupActionsModL[generators_, llist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, 
    GetGroupAction[generators, #] & /@ 
     GenerateIrreducibleWordListModL[Length[generators], llist, i]]
   ];
  Return[Flatten[ret]];
  ]

GetAllGroupActionsWithWordsModL[generators_, llist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModL[Length[generators], llist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

GetAllGroupActionsWithWordsModL[generators_, llist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModL[Length[generators], llist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

(*Left and Right Cosets*)

GenerateIrreducibleListModLR[n_, llist_, rlist_, N_] := 
 Module[{initlist, firstentry, lastentry, ret, i, j, k},
  ret = {};
  If[n == 1,
   For[j = 1, j <= N, j++,
    If[!ContainsAny[{j}, Union[llist, rlist]],AppendTo[ret, {j}]];
    ];
   Return[ret];
   ];
  
  firstentry = {};
  For[j = 1, j <= N, j++,
   If[!ContainsAny[{j}, llist],AppendTo[firstentry, j]];
   ];
  
  lastentry = {};
  For[k = 1, k <= N, k++,
   If[!ContainsAny[{k}, rlist],AppendTo[lastentry, k]];
   ];
  
  If[n == 2,
   initlist = ListProduct[firstentry, lastentry];,
   initlist = 
     ListProduct[ListProduct[firstentry, PositiveNList[n - 2, N]], lastentry];
   ];
  For[i = 1, i <= Length[initlist], i++,
   If[!IsReducible[initlist[[i]]],AppendTo[ret, initlist[[i]]]]
   ];
  Return[ret]
  ]

GenerateIrreducibleWordListModLR[n_, llist_, rlist_, N_] := 
 Module[{generatorlist, numberlist, ret, i, j},
  numberlist = NegativePartitions[N];
  If[N == 0, Return[{{{}}}]];
  ret = {};
  For[i = 1, i <= Length[numberlist], i++,
   generatorlist = 
    GenerateIrreducibleListModLR[Length[numberlist[[i]]], llist, rlist, n];
   For[j = 1, j <= Length[generatorlist], j++,
    AppendTo[ret, Pair[generatorlist[[j]], numberlist[[i]]]]
    ]
   ];
  Return[ret];
  ]

GetAllGroupActionsModLR[generators_, llist_, rlist_, N_] := Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[ret, 
    GetGroupAction[generators, #] & /@ 
     GenerateIrreducibleWordListModLR[Length[generators], llist, rlist, i]]
   ];
  Return[Flatten[ret]];
  ]

GetAllGroupActionsModLRWithoutTrivial[generators_, llist_, rlist_, N_] := 
 Module[{ret, i},
  ret = {};
  For[i = 1, i <= N, i++,
   AppendTo[ret, 
    GetGroupAction[generators, #] & /@ 
     GenerateIrreducibleWordListModLR[Length[generators], llist, rlist, i]]
   ];
  Return[Flatten[ret]];
  ]

GetAllGroupActionsWithWordsModLR[generators_, llist_, rlist_, N_] := 
 Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModLR[Length[generators], llist, rlist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

GetAllGroupActionsWithWordsModLR[generators_, llist_, rlist_, N_] := 
 Module[{ret, i},
  ret = {};
  For[i = 0, i <= N, i++,
   AppendTo[
    ret, {GetGroupAction[generators, #], #} & /@ 
     GenerateIrreducibleWordListModLR[Length[generators], llist, rlist, i]]
   ];
  Return[Flatten[ret, 1]];
  ]

(*Abelian Groups*)

(*Map a generic word of an free group with n generators to its abelianized element in Z^n*)

AbelianizeWord[word_, n_] := Module[{ret, i},
  ret = ConstantArray[0, n];
  If[word == {{}}, Return[ret]];
  For[i = 1, i <= Length[word], i++,
   ret[[word[[i, 1]]]] = ret[[word[[i, 1]]]] + word[[i, 2]];
   ];
  Return[ret]
  ]

GetAbelianElementMultiplicative[generators_, word_] := Module[{ret, i},
  ret = 1;
  For[i = 1, i <= Length[word], i++,
   ret = ret generators[[i]]^word[[i]];
   ];
  Return[ret];
  ]

(*Matrix Groups*)

MatrixGroup`MatrixGroupElement[M_, word_] := Module[{ret = {}, i},
  ret = IdentityMatrix[Length[M[[1]]]];
  
  If[word == {{}}, Return[ret]];
  
  For[i = 1, i <= Length[word], i++,
   ret = MatrixPower[M[[word[[i, 1]]]], word[[i, 2]]] . ret;
   ];
  Return[ret];
  ]

MatrixGroup`AllMatricesAtN[M_, n_] := 
  MatrixGroup`MatrixGroupElement[M, #] & /@ 
   GenerateIrreducibleWordList[Length[M], n];

MatrixGroup`AllMatrices[M_, n_] := 
  Flatten[MatrixGroup`AllMatricesAtN[M, #] & /@ Table[i, {i, 0, n}], 1];

MatrixGroup`AllMatricesAtNSubL[M_, llist_, n_] := 
 MatrixGroup`MatrixGroupElement[M, #] & /@ 
  GenerateIrreducibleWordListL[Length[M], llist, n]; 
MatrixGroup`AllMatricesSubL[M_, llist_, n_] := 
 Flatten[MatrixGroup`AllMatricesAtNSubL[M, llist, #] & /@ Table[i, {i, 1, n}],
   1];

MatrixGroup`AllMatricesAtNSubR[M_, rlist_, n_] := 
 MatrixGroup`MatrixGroupElement[M, #] & /@ 
  GenerateIrreducibleWordListR[Length[M], rlist, n]; 
MatrixGroup`AllMatricesSubR[M_, rlist_, n_] := 
 Flatten[MatrixGroup`AllMatricesAtNSubR[M, rlist, #] & /@ Table[i, {i, 1, n}],
   1];

(*Elementary Geometry*)

(*Circle Transformations*)

InvertCircle[{p_, r_}] := {p/(p^2 - r^2), Abs[r/(p^2 - r^2)]};
MoveCircle[{p_, r_}, a_] := {p - a, r};
ScaleCicle[{p_, r_}, \[Lambda]_] := {p \[Lambda], r Abs[\[Lambda]]};

TransformCircle[circle_, a_, \[Lambda]_, \[Mu]_, b_] := 
  MoveCircle[
   MultipleEvaluation[InvertCircle, 
    ScaleCicle[MoveCircle[circle, a], \[Lambda]], \[Mu]], b];

TransformCircle[{p_, r_}, \[Gamma]_] := 
 With[{z1 = \[Gamma][p + r], z2 = \[Gamma][p + I r], z3 = \[Gamma][p - r]},
  Return[OuterTriangleCircle[z1, z2, z3]];
  ]

(*Distances to Circles*)

IsInCircle[z_, p_, r_] := If[Abs[z - p] <= r, True, False];
IsInCirclePair[z_, circpair_] := 
  IsInCircle[z, circpair[[1]], circpair[[2]]] || 
   IsInCircle[z, circpair[[3]], circpair[[4]]];
IsNotInCircle[z_, p_, r_] := If[Abs[z - p] <= r, False, True];
IsNotInCirclePair[z_, circpair_] := 
  IsNotInCircle[z, circpair[[1]], circpair[[2]]] && 
   IsNotInCircle[z, circpair[[3]], circpair[[4]]];
IsNotInOuterCirclePair[z_, circpair_] := If[circpair[[2]] > circpair[[4]],
  IsInCircle[z, circpair[[1]], circpair[[2]]] && 
   IsNotInCircle[z, circpair[[3]], circpair[[4]]]
  ,
  IsNotInCircle[z, circpair[[1]], circpair[[2]]] && 
   IsInCircle[z, circpair[[3]], circpair[[4]]]
  ]

(*Triangles*)

OuterTriangleCircle[p1_, p2_, p3_] := Module[{t, s, p, r},
  With[{a1 = Re[(p2 - p3)/(2 I)], a2 = Im[(p2 - p3)/(2 I)], b1 = Re[p1 - p3], 
    b2 = Im[p1 - p3], c1 = Re[p2 - p1], c2 = Im[p2 - p1]},
   {s, t} = Inverse[{{b1, c1}, {b2, c2}}] . {a1, a2}];
  p = (p1 + p2)/2 + t I (p1 - p2);
  r = Abs[p - p1];
  Return[{p, r}]
  ]


(*Map Geometric Objects*)

ParametricPointsR[f_, N_] := ReIm[f[#]] & /@ Table[i/(N - 1), {i, 0, N - 1}];
ParametricPoints[f_, N_] := f[#] & /@ Table[i/(N - 1), {i, 0, N - 1}];


MapCircle[circle_, f_, n_] := With[{c = CircleParametrization[circle]},
  Return[f[#] & /@ ParametricPoints[c, n]];
  ]

MapLineAB[line_, f_, n_] := With[{c = LineParametrizationAB[line]},
  Return[f[#] & /@ ParametricPoints[c, n]];
  ]

(*Misc*)

Corner[n_, d_] := d e[(2 n - 1)/8];
CornerRegion[var_, d_] := {var, Corner[3, d], Corner[1, d]};

SignList[n_] := Module[{i, ret},
  ret = {-1, 1};
  For[i = 1, i < n, i++,
   ret = ListProduct[ret, {-1, 1}];
   ];
  Return[ret];
  ]

GetPointNormalizedFunction[f0_, p_] := (z |-> z/f0[p])@*f0;

End[] (* End Private Context *)

EndPackage[]