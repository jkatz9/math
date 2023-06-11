(* ::Package:: *)

$PrePrint =.

(*$PrePrint = (TraditionalForm @ HoldForm[In[line] = #] /. line -> $Line
     /. DownValues[In])&;
*)

prec = 10;

Ad[g_] := Function[x,
    g . x . Inverse[g]
];

LieBracket[x_, y] := x . y - y . x;

Commutator[x_, y_] := x  y . Inverse[x] . Inverse[y];

Theta[x_] := x - DiagonalMatrix[{Tr[x] / 2, Tr[x] / 2}];

sqrt[a_, e_:prec] := Sum[Binomial[1 / 2, i] * a^i, {i, 0, e}];

U[x_] := sqrt[Tr[x^2] / 2];

Psi[u_] := u + U[u] * IdentityMatrix[2];

star[x_, y_] := U[x] * y + U[y] * x;

log[t_] := Sum[(-1) ^ (n - 1) (1 - t) ^ n / n, {n, 1, prec}];

exp[t_] := Sum[t^n / Factorial[n], {n, 0, prec}];

PE[a_] := Sum[Subscript[a, i] p^i, {i, 0, 4}];

(* invo[g_]:=Tr[g]*id-g; *)

(* $Assumptions=Det[g1]==1&&Det[g2]==1; *)

R[r_] := {{1, r}, {0, 1}};

L[r_] := {{1, 0}, {r, 1}};

W = {{0, 1}, {-1, 0}};

(* DD[c_]:=DiagonalMatrix[{1+c,1/(1+c)}]; *)

(* W.R[1/b].W //MatrixForm; *)

(* R[b].W.R[1/b] // MatrixForm; *)

(* g = {{1+p a,p b},{p c,1+p d}}; *)

a = PE[\[Alpha]];

b = PE[\[Beta]];

c = PE[\[Gamma]];

d = PE[\[Delta]];

$Assumptions = {Subscript[\[Alpha], 0] == 1}

g = {{a, b}, {c, d}};

A = {{p^j, 0}, {0, 1}};

det = Ad[A][g] // Det;

Collect[g, p]

Collect[det, p]

(* \[Beta] = \[Alpha].W; *)

(* \[Gamma] = {{1,0},{0,p}}; *)

(* \[Delta] = \[Gamma].W; *)

(* \[Alpha] *)

(* Ad[\[Alpha]//Inverse]; *)

(* Ad[\[Alpha]//Inverse][g]; *)

  (* alpha
beta  *)

(* gamma *)

(* delta *) 



