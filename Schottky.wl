(* Wolfram Language Package *)

BeginPackage["Schottky`"]
(* Exported symbols added here with SymbolName::usage *)  

Begin["`Private`"] (* Begin Private Context *) 
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
  

  
  
End[] (* End Private Context *)

EndPackage[]