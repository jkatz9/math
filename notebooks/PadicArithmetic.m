(* Copyright 1995 Stany De Smedt *)

(** P-adic Arithmetic **)

BeginPackage["PadicArithmetic`"]

(***************** Public usage documentation ******************)

(* Users who are not familiar with p-adic calculus can   *)

(* find a good introduction in :                         *)

(* W. Schikhof, Ultrametric Calculus : An introduction   *)

(* to p-adic analysis, Cambridge University Press, 1984  *)

(* N. Koblitz, P-adic Numbers, P-adic Analysis and Zeta- *)

(* Functions, Springer-verlag, 1977                      *)

PadicN::usage = "Think of PadicN[] as being a bit like N[], only evaluating to 
give a p-adic number in Hensel-development with a given precision.
The internal representation is given as a PadicRational.  
PadicN[n,p] gives an 8 digit p-adic number, PadicN[n,p,k] gives 
k digits.  The numbers to the right of the radix point represent 
the positive (> 0) powers, the numbers to the left represent the 
negative (<= 0) powers"

PadicRational::usage = "PadicRational[m_,n_,e_,p_] implements the p-adic data type for 
the number m*p^e; p is the prime for the p-adic; n is the number 
of significant p-adic digits in the expansion; (1-e) gives the 
number of digits to the left of the radix point."

PadicOrder::usage = "PadicOrder[s, p] returns the number of times that p divides s 
roughly speaking. PadicOrder[s_PadicRational] also works."

PadicValue::usage = "PadicValue[s,p] = 1/p^(PadicOrder[s,p]).  
PadicValue[s_PadicRational] also works."

SumDigits::usage = "SumDigits[n_,p_] gives the sum of the digits in the Hensel-
development of the positive integer n according to the base p"

PadicNQ::usage = "PadicNQ[x_] is True iff x is a p-adic rational."

PadicIntegerQ::usage = "PadicIntegerQ[x_PadicRational] is True iff x is a p-adic 
integer.  Similarly for PadicIntegerQ[x_Rational, p]."

PadicMantissa::usage = "PadicMantissa[s_PadicRational] returns m; where s==m*p^e."

PadicExponent::usage = "PadicExponent[s_PadicRational] returns e; where s==m*p^e."

PadicToRational::usage = "PadicToRational[s_PadicRational] returns the Rational equal 
to s."

PadicGamma::usage = "PadicGamma[n_,p_] gives the value of the p-adic version of the 
Gammafunction in n"

Mahler::usage = "Mahler[f_,x_,n_Integer] gives the first n coefficients in the 
Mahler expansion of the continuous function f(x)."

Vanderput::usage = "Vanderput[f_,x_,n_Integer?Positive,p_Integer] gives the first
n coefficients in the expansion of the continuous p-adic function 
f(x) regarding to the Vanderput base."

VolkenbornIntegral::usage = "VolkenbornIntegral[f_,x_,n_Integer] gives the sum of the first 
n+1 terms in the expansion of the Volkenborn integral of f(x).  
The calculation is exact for polynomials of the degree less then 
or equal to n"

PadicNewton::usage = "PadicNewton[f_,x0_,epsilon_,p_Integer] is the p-adic equivalent 
of the classical Newton method to find an approximation for the 
root of f in some neighbourhood of x0.  In case there is not given
a starting point, all integer values between 0 and p-1 will be 
considered as possible starting points."

(* Begin["`private`"] *)

(****************** p-adic order and valuation *****************)

PadicOrder[0, p_] :=
    Infinity

PadicOrder[n_Integer, p_Integer] :=
    Block[{number = n, order = 0},
        While[
            Mod[number, p] == 0
            ,
            order += 1;
            number /= p
        ];
        order
    ]

(* Mathematica ensures that rational numbers have no common 
   factors between numerator and denominator.  *)

PadicOrder[r_Rational, p_Integer] :=
    PadicOrder[Numerator[r], p] - PadicOrder[Denominator[r], p]

PadicRational /: PadicOrder[PadicRational[m_, n_, e_, p_Integer], p_Integer
    ] :=
    e + PadicOrder[m, p]

PadicValue[s_, p_] :=
    1 / (p ^ PadicOrder[s, p])

(* We don't require p as a second argument when doing p-adic 
   order or value of a p-adic number. *)

PadicRational /: PadicOrder[PadicRational[m_, n_, e_, p_Integer]] :=
    e + PadicOrder[m, p]

PadicRational /: PadicValue[(s : PadicRational[m_, n_, e_, p_Integer]
    )] :=
    1 / (p ^ PadicOrder[s])

(* We also can find PadicOrder and PadicValue regarding to 
   another base *)

PadicRational /: PadicOrder[(s : PadicRational[m_, n_, e_, p_Integer]
    ), p2_Integer] :=
    PadicOrder[PadicN[s, p2, n]]

PadicRational /: PadicValue[(s : PadicRational[m_, n_, e_, p_Integer]
    ), p2_Integer] :=
    1 / (p ^ PadicOrder[s, p2])

(******************** Conversion to p-adics ********************)

(* 8 p-adic digits is default. *)

PadicN[s_, p_Integer] :=
    PadicN[s, p, 8]

PadicN[0, p_Integer, n_Integer] :=
    PadicRational[0, n, 0, p]

PadicN[s_Integer, p_Integer, n_Integer] :=
    Block[{ord = PadicOrder[s, p]},
        PadicRational[Mod[s / p^ord, p^n], n, ord, p]
    ]

PadicN[s_Rational, p_Integer, n_Integer] :=
    Block[{num = Numerator[s], den = Denominator[s], denord},
        denord = PadicOrder[den, p];
        PadicRational[Mod[num * PowerMod[den / (p^denord), -1, p^n], 
            p^n], n, -denord, p]
    ]

PadicRational /: PadicN[(s : PadicRational[m_, n_, e_, p_]), p2_Integer,
     n2_Integer] :=
    PadicN[PadicToRational[s], p2, n2]

SetAttributes[PadicN, Listable]

PadicN[e_Plus, p_Integer, n_Integer] :=
    PadicN[#, p, n]& /@ e

PadicN[e_Times, p_Integer, n_Integer] :=
    PadicN[#, p, n]& /@ e

PadicN[x_^m_, p_Integer, n_Integer] :=
    PadicN[x, p, n] ^ m

(* Drop the PadicN when applied to an atom. *)

PadicN[e_, _, _] :=
    e /; AtomQ[e]

SumDigits[0, p_Integer?Positive] :=
    0

SumDigits[n_Integer?Positive, p_Integer?Positive] :=
    Block[{j, k},
        j = 0;
        k = n;
        While[
            k != 0
            ,
            {
                j = j + Mod[k, p];
                k = Quotient[k, p]
            }
        ];
        j
    ]

(********************* Printing of p-adics *********************)

Format[PadicRational[m_Integer, n_Integer, e_Integer, p_Integer]] :=
    HoldForm[SequenceForm["<", p, "> ", PadicDigits[m, n, 0, p]] * HoldForm[
        p^e]] /; e + n <= 0 || e >= n

Format[PadicRational[m_Integer, n_Integer, e_Integer, p_Integer]] :=
    SequenceForm["<", p, "> ", PadicDigits[m * p^e, n + e, 0, p]] /; e >
         0

Format[PadicRational[m_Integer, n_Integer, e_Integer, p_Integer]] :=
    SequenceForm["<", p, "> ", PadicDigits[m, n, e, p]]

(* PadicDigits is an auxiliary function to aid formatting. *)

Format[PadicDigits[m_, 0, 1, p_]] :=
    SequenceForm["."]

Format[PadicDigits[m_, 0, e_, p_]] :=
    ""

Format[PadicDigits[m_, n_, e_, p_]] :=
    SequenceForm[". ", Mod[m, p], " ", PadicDigits[Quotient[m, p], n 
        - 1, e + 1, p]] /; e == 1

Format[PadicDigits[m_, n_, e_, p_]] :=
    SequenceForm[Mod[m, p], " ", PadicDigits[Quotient[m, p], n - 1, e
         + 1, p]] /; e != 1

(******************* Basic p-adic arithmetic *******************)

(* p-adic ADDITION *)

PadicRational /: PadicRational[a_, n_, e_, p_] + PadicRational[b_, n_,
     e_, p_] :=
    Block[{n1},
        n1 = n + PadicOrder[a + b, p] - Min[PadicOrder[a, p], PadicOrder[
            b, p]];
        PadicRational[Mod[a + b, p^n1], n1, e, p]
    ]

(* General case of addition of p-adic numbers of different 
   precision *)

PadicRational /: PadicRational[m1_, n1_, e1_, p_] + PadicRational[m2_,
     n2_, e2_, p_] :=
    Block[{e3 = Min[e1, e2], n3},
        n3 = Min[e1 + n1, e2 + n2] - e3;
        PadicRational[Mod[m1 * p ^ (e1 - e3), p^n3], n3, e3, p] + PadicRational[
            Mod[m2 * p ^ (e2 - e3), p^n3], n3, e3, p]
    ]

(* Adding an integer or rational to a p-adic number *)

PadicRational /: (a : PadicRational[_, n_, e_, p_]) + b_ :=
    a + PadicN[b, p, e + n] /; MatchQ[b, _Integer] || MatchQ[b, _Rational
        ]

(* p-adic MULTIPLICATION *)

PadicRational /: PadicRational[a_, n_, e1_, p_] * PadicRational[b_, n_,
     e2_, p_] :=
    PadicRational[Mod[a * b, p^n], n, e1 + e2, p]

(* General case of multiplication of p-adic numbers of different 
   precisions. Just truncate the more precise number to the same 
   precision as the less precise.  *)

PadicRational /: (a : PadicRational[m1_, n1_, e1_, p_]) * PadicRational[
    m2_, n2_, e2_, p_] :=
    a * PadicRational[Mod[m2, p^n1], n1, e2, p] /; n1 < n2

(* Multiplying an integer or rational to a p-adic number *)

PadicRational /: (a : PadicRational[_, n_, _, p_]) * b_ :=
    a * PadicN[b, p, n] /; MatchQ[b, _Integer] || MatchQ[b, _Rational
        ]

(* p-adic DIVISION:  suffices to implement x^m since Mathematica 
   treats x/y as equivalent to x*(y^-1), so we just implement 
   p-adic EXPONENTIATION. *)

PadicRational /: PadicRational[a_, n_, e_, p_] ^ m_Integer :=
    Block[{aord = PadicOrder[a, p]},
        PadicRational[
            PowerMod[a / p^aord, m, p^n]
            ,
            n
            ,
            If[a == 0,
                0
                ,
                m * (e + aord)
            ]
            ,
            p
        ]
    ]

(******** The p-adic version of some classical functions *******)

PadicN[Log[x_], p_Integer, n_Integer] :=
    Log[PadicN[x, p, n]]

PadicRational /: Log[s : PadicRational[a_, n_, e_, p_]] :=
    -Sum[(1 - s) ^ j / j, {j, 1, n}] /; PadicOrder[1 - s] > 0

Log::overflow = "Number not in the region of convergence"

PadicRational /: Log[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Log::overflow]

PadicN[Exp[x_], p_Integer, n_Integer] :=
    Exp[PadicN[x, p, n]]

PadicRational /: Exp[s : PadicRational[a_, n_, e_, p_]] :=
    1 + Sum[s^j / j!, {j, 1, n}] /; PadicOrder[s] > 1 / (p - 1)

Exp::overflow = "Number not in the region of convergence"

PadicRational /: Exp[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Exp::overflow]

PadicN[Sin[x_], p_Integer, n_Integer] :=
    Sin[PadicN[x, p, n]]

PadicRational /: Sin[s : PadicRational[a_, n_, e_, p_]] :=
    Sum[(-1) ^ j * s ^ (2 * j + 1) / (2 * j + 1)!, {j, 0, n}] /; PadicOrder[
        s] > 1 / (p - 1)

Sin::overflow = "Number not in the region of convergence"

PadicRational /: Sin[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Sin::overflow]

PadicN[Cos[x_], p_Integer, n_Integer] :=
    Cos[PadicN[x, p, n]]

PadicRational /: Cos[s : PadicRational[a_, n_, e_, p_]] :=
    Sum[(-1) ^ j * s ^ (2 * j) / (2 * j)!, {j, 0, n}] /; PadicOrder[s
        ] > 1 / (p - 1)

Cos::overflow = "Number not in the region of convergence"

PadicRational /: Cos[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Cos::overflow]

PadicN[Sinh[x_], p_Integer, n_Integer] :=
    Sinh[PadicN[x, p, n]]

PadicRational /: Sinh[s : PadicRational[a_, n_, e_, p_]] :=
    Sum[s ^ (2 * j + 1) / (2 * j + 1)!, {j, 0, n}] /; PadicOrder[s] >
         1 / (p - 1)

Sinh::overflow = "Number not in the region of convergence"

PadicRational /: Sinh[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Sinh::overflow]

PadicN[Cosh[x_], p_Integer, n_Integer] :=
    Cosh[PadicN[x, p, n]]

PadicRational /: Cosh[s : PadicRational[a_, n_, e_, p_]] :=
    -Sum[s ^ (2 * j) / (2 * j)!, {j, 0, n}] /; PadicOrder[s] > 1 / (p
         - 1)

Cosh::overflow = "Number not in the region of convergence"

PadicRational /: Cosh[s : PadicRational[a_, n_, e_, p_]] :=
    Message[Cosh::overflow]

PadicGamma[0, p_Integer?Positive] :=
    1

PadicGamma[1, p_Integer?Positive] :=
    -1

PadicGamma[n_Integer, p_Integer?Positive] :=
    Block[{k, l},
            k = (-1) ^ n * Product[j, {j, 1, n - 1}];
            l = p;
            While[
                l <= n - 1
                ,
                k = k / l;
                l = l + p
            ];
            k
        ] /; n > 1

PadicGamma[n_Integer, p_Integer?Positive] :=
    (-1) ^ (-n + 1 - Quotient[-n, p]) / PadicGamma[-n + 1, p] /; n < 0

(************************** Boolean(s) *************************)

PadicRational /: PadicNQ[PadicRational[_Integer, _Integer, _Integer, 
    _Integer]] :=
    True

PadicNQ[x_] :=
    TrueQ[x - Rationalize[N[x]] == 0]

PadicIntegerQ[_Integer] :=
    True

PadicIntegerQ[x_Rational, p_Integer] :=
    True /; Mod[Denominator[x], p] != 0

PadicRational /: PadicIntegerQ[x_PadicRational] :=
    True /; PadicOrder[x] >= 0

PadicIntegerQ[x_] :=
    False

(**************** Selectors on p-adic rationals ****************)

PadicRational /: Precision[PadicRational[_, n_, _, _]] :=
    n

PadicRational /: PadicMantissa[PadicRational[a_, _, _, _]] :=
    a

PadicRational /: PadicExponent[PadicRational[_, _, e_, _]] :=
    e

PadicRational /: PadicToRational[PadicRational[m_, _, e_, p_]] :=
    m * p^e

(********************* Function expansions *********************)

Mahler[f_, x_, n_Integer] :=
    Do[Print[k, " : ", Sum[(-1) ^ (k - i) * Binomial[k, i] * f /. x ->
         i, {i, 0, k}]], {k, 0, n}]

Vanderput[f_, x_, n_Integer?Positive, p_Integer] :=
    Block[{k},
        Print[0, " : ", f /. x -> 0];
        Do[Print[k, " : ", (f /. x -> k) - (f /. x -> GreatestInitial[
            k, p])], {k, 1, n}]
    ]

(* GreatestInitial is just an auxiliary function which removes 
   the last non-zero term in the Hensel expansion of a positive 
   integer.  There exists no name for this fucntion in p-adic 
   calculus but there is a notation for it. It is usually notated 
   with a subscript minus-sign after it such as k_ *)

GreatestInitial[k_Integer?Positive, p_Integer] :=
    Block[{kmin = k, t = 0},
        While[p ^ (t + 1) < kmin, t = t + 1];
        While[p^t <= kmin, kmin = kmin - p^t];
        kmin
    ]

(********************** VolkenbornIntegral *********************)

VolkenbornIntegral[f_, x_, n_Integer] :=
    Sum[(-1) ^ k / (k + 1) * Sum[(-1) ^ (k - i) * Binomial[k, i] * f 
        /. x -> i, {i, 0, k}], {k, 0, n}]

(********************* p-adic Newton method ********************)

PadicNewton[f_, x_, x0_, epsilon_, p_Integer] :=
    Block[{g, h, t, t0, t1, N},
        t0 = x0;
        g[t_] = f /. x -> t;
        h[t_] = D[g[t], t];
        If[Mod[g[t0], p] != 0,
            Print[t0, " is not an acceptable starting value"]
            ,
            t1 = t0 - g[t0] / h[t0];
            While[
                PadicValue[t1 - t0, p] > epsilon
                ,
                t0 = t1;
                t1 = t0 - g[t0] / h[t0]
            ];
            PadicN[t1, p, Min[-Round[Log[p, epsilon]] + 1, 20]]
        ]
    ]

PadicNewton[f_, x_, epsilon_, p_Integer] :=
    Do[Print[PadicNewton[f, x, i, epsilon, p]], {i, 0, p - 1}]

(* End[] *)

EndPackage[]
