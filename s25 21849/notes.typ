#set heading(numbering: "1.")
#set enum(numbering: "1.a)")



#set page(margin: (
  top: 3cm,
  bottom: 2cm,
  x: 1.5cm,
))

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [21-849: Algebraic Geometry],
  author: "Rohan Jain",
  date: datetime(year: 2025, month: 01, day: 13),
  preface: [
    #align(center + horizon)[
      I don't know what a sheave or a category is. #emoji.heart
    ]
  ],
  table-of-contents: none,
)

#set math.equation(numbering: none)

#pagebreak()
#toc
#counter(page).update(1)
#pagebreak()
#counter(page).update(1)

= Introduction
=== Administrivia
// #let ux = $underline(x)$
// #let angled(..inputs) = {
//   $angle.l #inputs.pos().join(",") angle.r$
// }
- Grade consists of two takehomes and one presentation/paper.
- Exercise List/Notes: Canvas
- Prerequisites: basic algebra, topology, and "multivariable calculus".
- Textbooks: [G] Gathmann, [H1] Hartshorne, [H2] Harris
- OH: 2-4pm Wednesday, Wean 8113
== Features of algebraic geometry
Consider the two functions $e^z$ and $z^2 - 3 z + 2$. 
- Both are continuous in $RR$ or $CC$.
- Both are holomorphic in $CC$.
- Both are analytic (power series expansion at every point).
- Both are $C^oo$.
There are differences as well.
- $f(z) =a $ has no solution or infinitely many solutions for $e^z$, but for almost all $a$, 2 solutions for $z^2 - 3 z + 2$.
- $e^z$ is not definable from $ZZ -> ZZ$ but $z^2 - 3 z + 2$ is.
- $(d/(d z))^ell != 0$ for all $ell > 0$ for $e^z$ but not for $z^2 - 3 z + 2$.
- For nontrivial polynomials, as $z -> oo$, $p(z)$ goes to infinity. So, it can be defined as a function from $hat(C) -> hat(C)$. But $e^z$ can be periodic as the imaginary part tends to infinity.
This motivates the following result:
#theorem[GAGA Theorems][
  Compact (projective)  $CC$-manifolds are algebraic.
]
Here are more cool things about algebraic geometry:
1. *Enumeration*:
  - How many solutions to $p(z)$?
  - How many points in ${f(x, y) = g(x, y) = 0}$?
  - How many lines meet a given set of 4 general lines in $CC^3$? The answer is 2.
  - How many conics $({f(x, y) = 0}, deg f = 2)$ are tangent to given 5 conics (in 2-space)? Obviously it's 3264...
  - Now for any question of the previous flavor, the answer is coefficients of chromatic polynomials of graphs.
2. *Birationality*: 
  - Open sets are _huge_. That is, if we have $X,Y$ and $U subset.eq X, V subset.eq Y$ such that $U tilde.equiv V$, then $X$ and $Y$ are closely related.
3. *Arithmetic Geometry*:
  - Over $ZZ, ZZ_p, QQ_p$, etc. 
  - Weil conjectures: $X$ carved by polynomials with $ZZ$-coefficients. $H^2(X_CC, QQ)$ related to integer solutions.



= Affine algebraic sets
== Nullstellensatz
Notation: $bb(k)$ is an algebraically closed field $(bb(k) = CC)$.

#definition[Affine space][
  An $n$-affine space $bb(A)^n_bb(k)$ is the set $
  {(a_1, dots, a_n) | a_i in bb(k)\, forall i = 1, dots, n} = bb(k)^n.
  $
  An affine algebraic subset of $bb(A)^n$ is a subset $Z subset.eq bb(A)^n$ such that
  $
    Z = {(a_1, dots, a_n) in bb(A)^n | f(a_1, dots, a_n) = 0, forall f in T}
  $ 
  for some subset $T subset.eq bb(k)[x_1, dots, x_n]$. We write $Z = V(T)$.
]

#example[An affine space][
  - $V(x^2 - y) subset bb(A)^2$. This is a parabola.
  - $V(x^2 + y^2) subset bb(A)^2$. Note that $x^2 + y^2 = (x + i y)(x - i y)$, so this is two lines.
  - $V(x^2 - y, x y - z) subset.eq bb(A)^3$. We actually have $V(x^2 - y, x y - z) = {(x, x^2, x^3) | x in bb(k)}$. Then note that if we project to any two dimensional plane $(x y, y z, x z)$, then we get another affine subset but on $bb(A)^2$.
]
This leads us to the following question:
#question[
  $X subset.eq bb(A)^n => pi(X) subset.eq bb(A)^{n - 1}$?
]
#solution[
  Consider $V(1 - x y) subset.eq bb(A)^2$. If we project this to either axis, then we will miss the origin. 
]

#definition[Ideal][
  Let $Z subset.eq bb(A)^n$ be an algebraic subset. Then 
  $
    I(Z) = {f in bb(k)[x] | f(p) = 0, forall p in Z}.
  $
]
#example[
  0. $Z = V(x^2) subset.eq bb(A)^2$, then $I(Z) = angle.l x angle.r$.
  1. If $Z = V(x^2 - y)$, then $I(Z) = angle.l x^2 -y angle.r$
  2. If $Z = V(x^2 - y, x y - z)$, then $I(Z) = angle.l x^2 - y, x y - z angle.r$.
]

#proposition[
1. $I(Z)$ an ideal. $Z_1 subset.eq Z_2 => I(Z_1) supset.eq I(Z_2)$.
2. $T subset.eq bb(k)[x]$. $V(T) = V(angle.l T angle.r)$ AND $V(T) = V(f_1, dots, f_m)$ for some $f_i$.
3. For $frak(a) subset.eq bb(k)[x]$ ideal, $V(frak(a)) = V(sqrt(frak(a)))$, where $sqrt(frak(a)) = {f in bb(k)[x] | f^m in frak(a), exists m > 0}$.
4. Algebraic subsets of $cal(A)^n$ are closed under finite unions and arbitrary intersections.
]
#proof[
  We prove number 2 by using the Hilbert Basis Theorem. In particular, $bb(k)[x]$ is Noetherian. 
]
#theorem[Nullstellensatz][
  Let $Z$ be an algebraic subset. Then $V(I(Z)) = Z$ and $I(V(frak(a))) = sqrt(frak(a))$. That is, 
  $
    {"algebraic subsets of" bb(A)^n} <-> {"radical ideals in" bb(k)[x]}.
  $
]

#proof[
  1. Finite type field extensions $L supset.eq F$ are finite. Rember that finite type means that $F[x_1, dots, x_m] ->> L$. 
  2. This implies that maximal ideals of $bb(k)[x]$ are of the form $angle.l x_1 - a_1, dots, x_n - a_n angle.r$ for $a_i in bb(k)$, using the fact that $bb(k)$ is algebraically closed. So, $k[x] slash frak(m) tilde.eq bb(k)$.
  3. (Weak Nullstellensatz) $V(frak(a)) = emptyset <==> frak(a) = angle.l 1 angle.r$. That is, $frak(a) subset.neq k[x], exists frak(m) supset.eq frak(a)$.
  4. So if $f in I(V(frak(a)))$, then consider $frak(a) + angle.l 1 - y f angle.r subset.eq k[x, y]$. So for any $(a_1, dots, a_n, b)$ that vanishes on $frak(a) + angle.l 1 - y  f angle.r$, we realize that since $1 - y f = 1$, we have a unit ideal. That is, we can say $1 = g_1 h_1 + g_2(1 - y f)$ for $h_1 in frak(a)$ and $g_1, g_2 in k[x, y]$. From here, we can conclude that $f^ell in frak(a)$ for some $ell$.

  But also 
  $
    k[x, y] \/ angle.l 1 - y f angle.r tilde.eq k[x][1/f] = R.
  $
  So, 
  $
    1/1 = g_1 + g_2/f + g_3/f^2 + dots.c + g_ell/f^(ell-1)
  $
  for $g_i in "ideal" frak(a) "inside" R$.
]
Remark: We say $R$ is Jacobson if every radical ideal $= sect.big_(frak(m) supset.eq I) frak(m)$.
#theorem[
  $R$ Jacobson $=>$ $R[x]$ Jacobson.
]
#definition[Coordinate ring][
  The coordinate ring $A(X)$ of $X subset.eq AA^n$ is $bb(k)[x] \/ I(X)$.
  1. $X ->^f bb(k)$
  2. $"maxSpec" A(X) = {"maximal ideals in" A(X)} = X$.
]

= Projective Spaces
#definition[
  $PP^n = (bb(k)^(n+1) without {0}) \/ tilde$. That is, $v tilde v'$ if $v = lambda v'$ for some $lambda in bb(k)$. That is, $PP^n = {"1-subspaces of" bb(k)^{n+1}}$. For $(a_0, dots, a_n) in k^(n+1) without {0}$, we write $[a_0:dots:a_n] in PP^n$.
]
Remark: $V tilde.eq bb(k)^(n+1)$. $PP V = V without {0} \/ tilde$
#definition[
  $f in bb(k)[underline(x)]$ is homogeneous if $f(lambda x_1, dots, lambda x_n) = lambda^ell f(x_1, dots, x_n)$.
]
#definition[
  A projective algebraic set, $X subset.eq PP^n$ is 
  $
    V(T) = {[x_0: dots.c : x_n] | f(x) = 0, forall f in T}
  $
  for $T$ a set of homogeneous polynomials.
]
We have that $PP^n supset U_i = {[x_0: dots: x_n] | x_i != 0, x_i = 1}$. So then 
$
  PP^n = (U_i = AA^n) union.sq  PP^(n-1).
$
#example[
  Let $W subset.eq bb(k)^(n+1)$ of $dim_k W = m+1$. Then $PP W subset.eq PP^n$ is a projective algebraic subset which is an $m$-plane in $PP^n$.
]

#example[Twisted cubic curve][
  We have $PP^3 supset C = {[s^3: s^2 t : s t^2 : t^3] | [s:t} in PP^1]}$. Then we have that $C = V(x_0 x_3 - x_1 x_2, x_1^2 - x_0 x_2, x_2^2 - x_1 x_3)$. Then $U_0 sect C = {[1: t: t^2: t^3]}$. Additionally, we have $C without U_0 = {[0: 0: 0: 1]}$. Another way we can view this is 
  $
    V("2 by 2 minors of" mat(x_0, x_1, x_2; x_1, x_2, x_3)).
  $
  Now note that for a matrix $A$, $"rank"(A) <= r <==>$ all $(r+1) times (r+1)$ minors $=0$.
]
#question[
  Can there exist $F,G$ such that $V(F, G) = C$? (Answer is yes)
]
For $X subset.eq PP^n$, algebraic subset, let 
$
  I(X) = {"homogeneous" f in bb(k)[ux] | f(p) = 0, forall p in X}
$
be the homogeneous ideal of $X$. 

#pagebreak()

#exercise[
  $
  {emptyset != X subset.eq PP^n "algebraic subsets"} <--> 
  \ {"homogeneous radical ideals" frak(a) subset.eq bb(k)[ux] "such that" frak(a) != bb(k)[ux] "or" angle.l x_0, dots, x_n angle.r}.
  $
  This last part is called the "irrelevant ideal".
]
#definition[General Position][
  In $PP^n$, any subset of size $<= n+1$ points are linearly independent. 
]
#theorem[
  Every set $Gamma$ of $2n$ points in $PP^n$ in general position is carved out by quadrics. 
]
#proof[
  We want to show that if $q in V({"all quadrics vanishing on" Gamma})$, then $q in Gamma$. Suppose $q$ is given. For any partition of $Gamma = Gamma_1 union.sq Gamma_2$, $|Gamma_i| = n$, $"span"(Gamma_1)$ is a hyperplane. Then for every such equi-partition, $q in "span"(Gamma_1)$ or $q in "span"(Gamma_2)$. 

  Let $p_1, dots, p_k$ be a minimal subset of $Gamma$ whose span $in.rev q$ ($k <= n$). Now pick any $Lambda$ such that $|Lambda| = n - k + 1$ whcih does not contain any of the $p_i$. We claim that $q in.not "span"(p_2, dots, p_k, Lambda)$. 

  We then conclude that for any $|S| = n-1$, $S subset.eq Gamma without p_1, dots, p_k$, we have that $"span"(p_1, S) in.rev q$. Because then
  $
    sect.big_S "span"(p, S)
  $
  is the intersection at least $n$ many hyperplanes, each of them containing $p_1, q$. But the intersection of $n$ many hyperplanes is a point, so $q = p_1$. This also  concludes that in fact $k=1$.
]
#definition[
  Two sets $X, X' subset PP^n$ are projectively equivalent if $X' = g dot X$, $exists g in P G L_(n+1)$.
]
#proposition[
  Let $(M_0, dots, M_3)$ be any $bb(k)$-basis of 
  $
    bb(k)[s, t]_3 = {f in bb(k)[s, t] "homog degree" 3} union {0}.
  $
  Then $phi: PP^1 -> PP^3$ by $phi: [s: t] |-> [M_0(s, t): dots : M_3(s, t)]$. Also, $phi(PP^1)$ is projectively equivalent to $C = {[s^3: s^2 t : s t^2 : t^3]}$. 
]
#example[Rational normal curve][
  Let $phi: PP^1 -> PP^n$ via $phi: [s: t] |-> [s^n: s^(n-1) t : dots.c : t^n]$. Or we could map it to any basis of $bb(k)[s: t]_n$.
]
#exercise[
  $I(phi(PP^1)) = ?$.
]
#example[
  $[s^3: s^2 t : t^3]$ is the same as $V(y^3 - x^2 z)$. Also take $[s t^2 - s^3 : t^3 - s^2 t : s^3]$. This is carved out by $V(y^2z - x^3 - x^2 z)$. 
]
*Fact:* If we pick any 3 linearly independent $M_0, M_1, M_2 in bb(k)[s,t]_3$. Then $phi: PP^1 -> PP^2$ by $M_0, M_1, M_2$ has image projectively equivalent to one of the two curves above. 

Now consider $PP^1 -> PP^3$ using 4 elements from $bb(k)[s, t]_4$. We consider $P tilde.eq C = {[s^4 : s^3 t: s t^3: t^4]}$. This is called the twisted quartic curve.

#question[
  Are all twisted quartic curves projectively equivalent?
]
#solution[
  No. In fact, there are infinitely many distinct families.
]
#question[Hartshorne's Question][
  Is every irreducible curve in $PP^3$ carved out by 2 equations?
]
= The Zariski Topology
#definition[Zariski topology][
  The sets ${V(I) subset.eq AA^n | I subset.eq bb(k)[ux]}$ form the closed sets of a tpology on $AA^n$ called teh Zariski topology.
]
Given $X subset.eq AA^n$, give it the subspace topology. 
#example[
  Take $AA^1$. Two closed subsets are $AA^1$ and $emptyset$. The other closed subsets are collections of finitely many points. As such, the open subsets are the complements of finitely many points. 
]

#definition[
  A topological space $X$ is irreducible $X = Y_1 union Y_2$ (each closed) implies that $X = Y_1$ or $X = Y_2$.

  By definition, we will also say that irreducible implies nonempty.
]

#remark[
  - Irreducible implies connected
  - Connected does not imply irreducible
  - Irreducible is useless in Hausdorff setting.
]

#proposition[
  Let $X subset.eq AA^n$ be a nonempty algebraic subset. $X$ is irreducible if and only if $I(X)$ is prime if and only if $A(X)$ is a domain.
 ]
#proof[
  - $==>$: Suppose $ f g in I(X)$. This means $V(f) union V(g) supset.eq X$. If $X$ is irreducible, then at least one of them completely contains $X$. That is, $V(f) supset.eq X$ or $V(g) supset.eq X$. But this exactly means $f$ or $g in I(X)$.
  - $<==$: Suppose for sake of contradiction that $X$ is not irreducible. We have $X = Y_1 union Y_2$ (both proper), then $I(Y_2) supset.neq I(X)$. Take $f_i in I(Y_i) without I(X)$. Now analyze $f_1 f_2$. $V(f_1 f_2) supset Y_1 union Y_2 = X$. Therefore, $f_1 f_2 in I(X)$. But this is a contradiction, so we are done.
]

#remark[
  When people say affine variety, some people mean that it is also irreducible. But for us, affine variety is the same thing as affine algebraic set.

  Then a quasi-affine variety is an open subset of an affine variety.
]
#example[
  1. $AA^n$ is irreducible. ($bb(k)[ux]$ domain)
  2. $V(x^2 + y^2) subset AA^2$ is reducible ($"char" bb(k) != 2$)
  3. Let $f in bb(k)[ux]$ be square-free ($f = f_1 dots f_ell$ irreducible). Then $V(f)$ is irreducible if and only if $f$ is irreducible. 
  4. $X = V(x^2 - y z) subset.eq AA^3$. Then $A(X) = (bb(k)[x,y,z])/(angle.l x^2 - y z angle.r)$. This is irreducible due to Eisenstein's on $f$. Now if we take $f in A(X)$ and look at $V_X (f) subset X$ is irreducible $arrow.l.not.double$ $f$ irreducible element in $A(X)$.
]
#definition[
  A topological space $X$ is Noetherian if $exists.not X supset.eq Y_0 supset.neq Y_1 supset.neq dots.c$ such that each $Y_i$ is closed.
]
#proposition[
  An affine variety is Noetherian. (Because $A(X)$ is Noetherian).
]

#theorem[
  A Noetherian topological space $X$ is uniquely a finite union of maximal irreducible closed subsets.
]
#proof[
  Consider 
  $
    {"nonempty closed subsets of" X "that does not admit a decomposition into irreducible closed subsets."}.
  $
  Suppose it is nonempty. Then it has a minimal element $Y$. $Y$ is not irreducible, so $Y = Y_1 union Y_2$ (both proper and closed). Since $Y$ is minimal, $Y_1$ and $Y_2$ both have decompositions into irreducible closed subsets. So if we just union those decompositions, then we contradict $Y$'s membership in the set. As such, the original set must have actually been empty.

  Uniqueness and maximality are left as an exercise.
]
#proposition[
  1. $X$ irreducible and $U subset.eq X$ open. Then $overline(U) = X$.
  2. $V subset.eq X$, $V$ irreducible $==>$ $overline(V)$ irreducible.
  3. $f: X -> Y$ continuous. Image of irreducible set under $f$ is irreducible. (Irreducibility is a topological property).
]
#example[
  Let's have $phi: AA^n -> AA^m$ by $phi(ux) = (f_1 (ux), dots, f_m (ux))$ for some $f_1, dots, f_m in bb(k)[ux]$. Then $im(phi)$ is irreducible. It is left to show that $phi$ is a continuous map.
]

#definition[
  Let $X$ be a nonempty topological space. 
  $
    dim X := sup{n | exists Y_0 subset.neq dots.c subset.neq Y_n, "each" Y_i "irreducible and closed"}.
  $
  Then let $Y subset.eq X$ closed irreducible subset. 
  $
    "codim"_X Y := sup{n | exists Y subset.eq Y_0 subset.neq dots.c subset.neq Y_n, "each" Y_i "irreducible and closed"}.
  $
]
#example[
  1. $dim AA^1 = 1$. 
  2. $X = V(x z, y z) subset.eq AA^3$. Then $dim X = 2$. Let $p$ be a point on the axis not touching the $x$-$y$ plane. Then let $q$ be the origin. We have that $"codim"_X p = 1$ and $"codim"_X q = 2$. Also $dim p = dim q = 0$.
]
#definition[
  Height of a prime $frak(p) subset R$ is 
  $
    "ht" frak(p) := sup{n | frak(p) = frak(p)_0 supset.neq dots.c supset.neq frak(p)_n, "each" frak(p)_i "prime"}.
  $
  Then Krull dimension of $R$ is
  $
    dim R := sup{"ht" frak(p) | frak(p) subset.eq R "prime"}.
  $
]

#definition[
  For an ideal $I$, we have that 
  $
    "ht" I := inf{"ht" frak(p) | frak(p) supset.eq I "prime"}.
  $
  "inf of sup".
]
From these, we can basically show from definition that 
$
  "ht" I + dim R\/I <= dim R.
$
The $<$ case is possible if $R$ is not a domain. For example, if we have that $R = bb(k)[x,y,z]\/ angle.l x z, y z angle.r$ and then $I = angle.l x, y, z-1 angle.r$.

But the $<$ case is also possible even if $R$ is a domain and $I$ prime.

Before we cover the next theorem, we note that 
$
  {"minimal primes over" I} = {frak(p) "prime" frak(p) supset.eq I, "and" exists.not frak(p) supset.neq frak(q) supset.eq I, "prime" frak(q)}
$
#pagebreak()
#theorem[Krull Principal Ideal Theorem / Height Theorem][
  Let $R$ be a Noetherian ring and $f_1, dots, f_c in R$. 
  1. Minimal primes over $angle.l f_1 angle.r$ have height $<= 1$. And the height is equal to 1 if $f_1$ is nonzerodivisor and nonunit.
  2. Minimal primes over $angle.l f_1, dots, f_c angle.r$ have height $<= c$.
]
"We could do this proof, but it's like proving that there exists a complete ordered field satisfying the least upper bound property."
#theorem[
  Let $X subset.eq AA^n$ and $YY subset.eq AA^m$ irreducible affine varieties. 
  1. $dim(X times Y) = dim X + dim Y$.
  2. If $Y subset.eq X$, then $dim Y + "codim"_X Y = dim X$.
]
#remark[Noether normalization][
  For $X subset.eq AA^n$ irreducible affine variety. There exists $y_1, dots, y_d in A(X)$ such that $bb(k)[Y_1, dots, Y_d] -> A(X)$ with $Y_i |-> y_i$ which is a finite extension (injective and $A(X)$ is finitely generated $bb(k)[Y]$-module) and $d = dim X$.
]
#corollary[
  1. $dim AA^n = n$.
  2. $X subset.eq AA^n$ irreducible affine variety. $0 != f in A(X)$ non unit. Then $V_X (f) = V(f) sect X$ has dimension $dim X - 1$.
]
#exercise[
  Let $U subset.eq X$ be open for $X$ affine variety irreducible. Then $dim U = dim X$.
]
#proposition[
  Let $R$ be Noetherian domain. Then $R$ UFD $<==>$ every $"ht" = 1$ prime is principal.
]
#proof[
  $R$ being a UFD implies that $frak(p)$ has height 1. So let $f = f_1, dots, f_ell in frak(p)$. Suppose $f_1 in frak(p)$. So then $0 != angled(f_1) subset.eq frak(p)$. But as $"ht" frak(p) = 1$, we have that $angled(f_1) eq frak(p)$.

  Conversely, we need to show that irreducible implies prime. That is, recall that (ACCP + irreducible = prime) implies that we have a UFD.

  So let $f in "irred"$. Krull's PIT says $angled(f) subset.eq frak(p)$ where $frak(p)$ has height 1. So by definition, $frak(p) = angled(g)$, but $angled(f) subset.eq angled(g)$ implies that $f = g$ because $f$ is irreducible.
]
#pagebreak()
#example[
  Let $X = V(x^2 - y  z) subset.eq AA^3$. Then let $Y = V(x, y) subset.eq X subset.eq AA^3$. Then $dim X = 2$. Then $dim Y = 1$. So can we find $f$ such that $angled(f"," x^2 - y z) = I(Y)$? The answer to this is no.

  But can we find $f$ such that $sqrt(angled(f"," x^2 - y z)) = angled(x"," y)$? Take $f=y$ and analyze $angled(y"," x^2 - y z)$. This is the same as $angled(y"," x^2)$, whose radical is $angled(x"," y)$ as we desire.
]
#example[
  Now consider $X = V(x w - y z) subset.eq AA^4$. $dim X = 3$ and let $Y = V(x, y)$. Now does there exist $f$ such that $sqrt(angled(f"," x w - y z)) = angled(x, y)$?

  This is false, but we don't have the tools to prove it.
]


#definition[
  Zariski topology on $PP^n$ has projective algebraic sets as its closed subsets.
]
Two ways: projective varieties $->$ affine varieties. 
1. $U_i = {x_i != 0} = {[x_0 : dots : x_i = 1: dots: x_n]} tilde.eq AA^n$.

#proposition[
  $forall i = 0, dots, n$, say $i = 0$, $AA^n --> U_0$, $(x_1, dots, x_n) |-> [1: x_1: dots: x_n]$ is a homeomorphism.
]
#proof[
  - _Homogenization_: let $f in bb(k)[x_1, dots x_n]$. Then we have
    $
      f^h := x_0^(deg f) f(x_1/x_0, dots, x_n/x_0) in bb(k)[x_1, dots, x_n].
    $
    If $Z = V(f_1, dots, f_m) subset.eq AA^n$, $phi(Z) = U_0 sect V(f_1^h, dots f_m^h)$ is closed. 

    If $Z' = V(F_1, dots, F_ell) sect U_0$, then $phi(Z') = V(F_1(1, x_2, dots, x_n), dots, F_ell (1, x_2, dots, x_n))$. 

    Now $U_0 union dots union U_n = PP^n$.
]

#exercise[
  Let $Y subset.eq AA^n tilde.eq U_0$ be an affine variety. $overline(Y) = V(?)$. Suppose $V(f_1, dots, f_m) = Y$. It is tempting to say $overline(Y) = V(f_1^h, dots, f^h_m)$. 
]

#corollary[
  1. $dim PP^n = n$.
  2. If $H_i = V(x_i) subset.eq PP^n$ does not contain any irreducible components of $Y subset.eq PP^n$, then $dim Y = dim Y sect U_i$. 
]

#definition[
  Let $Y subset.eq PP^n$ be a projective variety. The affine cone $hat(Y) = C(Y)$ is 
  $
    theta^(-1) (Y) union {0} subset.eq AA^(n+1)
  $
  where 
  $
    theta: AA^(n+1) without {0} --> PP^n.
  $
]

#proposition[
  1. $hat(Y) = V(I(Y))$. In fact, $I(hat(Y)) = I(Y)$.
  2. $dim hat(Y) = dim Y + 1$.
  3. $hat(Y)$ is irreducible if and only if $Y$ is irreducible.
]

#theorem[
  If $X,Y subset.eq PP^n$ are projective varieties and $dim X + dim Y >= n$, then $X sect Y != emptyset$.
]

#lemma[
  If $X,Y subset.eq AA^n$ affine varieties, then $X sect Y = nothing$ or every irreducible component of $X sect Y$ has $dim >= dim X + dim Y - n$.
]
#proof[
  Let $Delta = V(x_1 - y_1, dots, x_n - y_n) subset.eq AA^(n+n)$. Note that
    $
      X times Y sect Delta tilde.eq X sect Y.
    $
    So, $dim(X times Y sect Delta) >= dim X + dim Y - n$ by Krull's height theorem.

    If $underline(a) = (a_1, dots a_n)$ are varieties, then $I_a(X) = {f(underline(a) | f in I(X)}$. Then, 
    $
      A(X sect Y) = frac(bb(k)[underline(z)], sqrt(angled(I_z(X) + I_z(Y))))
    $
    and
    $
      A(X times Y sect Delta) = frac(bb(k)[ux, underline(y)], sqrt(angled(I_x(X) + I_y(Y) + I(A)))).
    $
    So this implies that $x_i = y_i$ for all $i$, meaning they are isomorphic rings.
]

#proof[of Theorem 4.28][
  $X,Y$ irreducible implies that $hat(X)$ and $hat(Y)$ are irreducible. So, then
  $
    dim(hat(X) sect hat(Y)) >= dim X + 1 + dim Y + 1 - (n+1) >= dim X + dim Y - n + 1.
  $
  $hat(X) sect hat(Y)$ contains origin by construction, but it has at least one other point because dimension.
]
= Morphisms
#definition[
  For $U subset.eq RR^n$, $U' subset.eq RR^m$ open, $phi: U -> U'$ is continuous/continuously differentiable/smooth if $f compose phi$ is smooth for any smooth $f: U' -> RR$.

  $f': U' -> RR$ is smooth if $f$ is smooth at every point $p in U'$. 
]

#definition[
  For affine variety $X subset.eq AA^n$ and $U subset.eq X$ open, a function $phi: U -> bb(k) = AA^1$ is regular if $forall p in U$, $exists U_p in.rev p$ open and $f_p, g_p in A(X)$ such that $phi(x) = frac(f_p (x), g_p (x))$ for all $x in U_p$. In particular, $g_p (x) != 0$ for all $x in U_p$.

  $cal(O)_X (U) := {"regular functions on" U}$. This is also a $bb(k)$-algebra.
]
#example[
  Let $U subset.eq X$, $phi : U -> AA^1$ regular $arrow.not.double$ $phi = f/g$ globally for some $f,g in A(X)$.

  $X = V(x w - y z) subset AA^4$, $U = X without V(x,y)$. 
  $
    phi(x,y,z,w) = cases( z/x "if" x!=0,
    w/y "if" y!=0).
  $
]

#lemma[
  $phi: U -> AA^1$ regular, then $V(phi) = {x in U | phi(x) = 0}$ is closed in $U$. In particular $phi$ is continuous.
]
#proof[
  Closedness is a local condition, and around any $p in U$, ${phi harpoon.tr U_p : 0} = V(f_p) sect U_p$.
]
#remark[
  If $phi_1, phi_2 in cal(O)_X (U)$ for $U$ irreducible, and $phi_1 harpoon.tr U' = phi_2 harpoon.tr U'$ for some $emptyset != U' subset.eq U$, then $phi_1 = phi_2$.
]
#definition[
  $X subset.eq AA^n$ affine variety. A distinguished open subset $U$ of $X$ is an open subset of the form $X without V(f)$ for some $f in A(X)$, denoted $D(f), D_f, U_f, X_f$. $X_f$ is probably the most descriptive as it actually mentions $X$.
]
#remark[
  ${D(f)}_(f in A(X))$ form a basis for Zariski topology. What that means is that any $U subset.eq X$ is a union for $D(f)$'s.
]

#exercise[
  $D(f)$ is homeomorphic to $V(I(X) + angled(1 - y f)) subset.eq AA^(n+1)$.
]
#theorem[
  $cal(O)_X (D(f)) = {g/f^m | g in A(X), m in ZZ_(>= 0)}$. In fact, $cal(O)_X (D(f)) = A(X)_f$.
]
#example[
  $cal(O)_(AA^2)(AA^2 without {0}) = A(AA^2) = bb(k)[x,y].$ Then,
  $
    AA^2 in.rev phi = cases(
      f/x^m "for some" f in bb(k)[x,y] "on" AA^2 without V(x),
      g/y^ell "for some" g in bb(k)[x,y] "on" AA^2 without V(y)
    ).
  $
  Then we say $y^ell f = x^m g$ on $AA^2$. Because we are in a UFD, this means that $x^m divides f$ and $y^ell divides g$. But this implies $m = ell = 0$, so $f=g=phi$.
]
#proof[of Theorem 5.7][
  $supset.eq$ is clear. So we only prove the $subset.eq$ case.

  Suppose we have $phi in cal(O)_X (D(f))$. Then for all $p in D(f)$, $exists U_p in.rev p$ and $phi harpoon.tr U_p = g_p'/f_p'$ for $g_p', f_p' in A(X)$. 

  Take a nonempty $D(h_p) subset.eq U_p$ and write $g_p = g_p' h_p$ and $f_p = f_p' h_p$.

  Then $phi harpoon.tr D(f_p) = g_p/f_p = (g_p f_p)/(f_p^2)$. So assume $g_p = 0$ on $V(f_p)$. 

  Now we claim that $forall p,q in D(f)$, we have $g_p f_q = g_q f_p$ in $A(X)$.

  Then $D(f) = union.big_p D(f_p)$. Then $V(f) = sect.big_p V(f_p)$. Nullstellensatz says that $sqrt(angled(f)) = sqrt(angled(f_p : p in D(f)))$ as ideals in $A(X)$. But then, $f^m = sum k_p f_p$. By Noetherian-ness, this is a finite sum. We claim that $g = sum k_p f_p$.

  Then $g/f^m = g_q/f_q$ on $D(f_q)$ for all $q in D(f)$. So,
  $
    g f_q = sum_p k_p g_p f_q = sum_p k_p f_p g_q = g_q f^m.
  $
]
= Sheaves
Let $cal(A)$ be a category: AbGrp, Rings, $bb(k)$-algebras. Given a topological space $X$, $"Top"(X)$ is a category where the objects are open subsets $U subset.eq X$ and morphisms are inclusions between $U subset.eq V$ open subsets.
#definition[
  A presheaf (with values in $cal(A)$) on $X$ is a contravariant functor $cal(F): "Top"(X) -> cal(A)$.

  $cal(F)$ is further a sheaf if for every open cover ${U_i}_i$ of any open subset $U subset.eq X$ if
  $
  cal(F)(U) -> product_(i) cal(F)(U_i) arrows.rr product_(i, j) cal(F)(U_i sect U_j)
  $
  is an equalizer. 
]
*Translation*: 
1. Assignment $U |-> cal(F)(U) in "obj"(cal(A))$ such that $forall U subset.eq V subset.eq X$ open, 
  $
    "res"_(V, U) : cal(F)(V) -> cal(F)(U)
  $
  such that $"res"_(U, U) = id$ and $"res"(V, U) compose "res"(W, V) = "res"(W, U)$.
2. If $(f_i)_i in product_i cal(F)(U_i)$ such that $"res"_(U_i, U_i sect U_j)(f_i) = "res"_(U_j, U_i sect U_j)(f_j)$, then $exists! f in cal(F)(U)$ such that $"res"_(U, U_i)(f) = f_i$. Also $cal(F)(nothing) = 0$ as a consequence.

  $f harpoon.tr V := "res"_(U, V)(f)$, $f in cal(F)(U)$. $cal(F)(U)$ elements are called sections of $cal(F)$ over $U$.

#example[
  Note that throughout these examples, $X$ is a topological space and $U subset.eq X$.
  1. $cal(F)_("ct")(U) := {phi: U -> RR}$. Then if $U' subset.eq U$, $"res"_(U, U')(f) := f harpoon.tr U'$. 
  2. $C(U) := {phi: U -> RR "cts"}$.
  3. $C^oo (U) := {phi: U -> RR "smooth"}$ $(X subset.eq RR^n$ open). 
  4. $underline(RR)(U) := {phi: U -> RR, "constant"}$. This is not a sheaf. If we consider a constant function that takes the value $a$ on $U$ and $b$ on $U'$, then there is no value $c$ such that they can be glued together to be equal on both sets.
  5. $cal(O)_X(U) := {phi: U -> bb(k) "regular"}$
]
#remark[
  A constant sheaf $A_X(U "conn") = A$. A locally constant sheaf (locally $cal(F) harpoon.tr U$ is constant). Locally constant does not imply constant.
]
#definition[
  $U subset.eq X$, $cal(F)$ sheaf on $X$, $cal(F) harpoon.tr U(V) = cal(F)(V)$ for $V subset.eq U$ open. 
]
#definition[
  $cal(F)$ sheaf on $X$. $p in X$.  The stalk of $cal(F)$ at $p$, $cal(F)_p := lim_(U in.rev p) cal(F)(U)$. This is actually just equal to ${(U, f) | U in.rev p, f in cal(F)(U) slash ~}$ where $(U_1, f_1) ~ (U_2, f_2)$ if $exists V in.rev p$ such that $f_1 harpoon.tr V = f_2 harpoon.tr V$.
]
Remember that $cal(F)"ct"_S (U) = {f: U -> S}$ and $C(U) = {f: U -> R "cts"}$.
#remark[
  $cal(F)(V) -> cal(F)(U)$ by $'"res"_(V, U)$. This map need not be surjective. 
]
#theorem[
  Let $X$ be an affine variety and $x in X$. $cal(O)_(X, x) = A(X)_(frak(m)_X)$.
]
#proof[
  Consider the ring map $A(X)_(frak(m)_x) -> cal(O)_(X, x)$ where we map $f/g |-> f/g$. 

  Now if $f/g = f'/g'$ in $A(X)_(frak(m)_x)$, then we need to check that the same is true around $x$ in $cal(O)_(X, x)$.

  Now if $f/g$ is 0 around $x$ (in $D(h)$), we can deduce that $f/g = 0$ in $A(X)_(frak(m)_x)$.
]
#definition[
  A ringed space $(X, cal(O)_X)$ where $X$ is a topological space and $cal(O)_X$ is a sheaf on $X$ with values in $"Ring"$. We call $cal(O)_X$ the structure sheaf of this ringed space.
]
#definition[
  $f: X -> Y$ continuous and $cal(F)$ a sheaf on $X$. 
  $
    "pushforward" f_* cal(F)(V) = cal(F)(f^(-1) V)
  $
  where $V supset Y$ is open.
]
#definition[
  Let $cal(F)$ and $cal(G)$ be sheaves on $X$. $Phi: cal(F) -> cal(G)$ means that for each $U subset.eq X$, we specify $Phi(U): cal(F)(U) -> cal(G)(U)$  where for $U subset.eq V$,
  we have the following diagram commuting:
  #align(center)[#commutative-diagram(
  node((0, 0), $cal(F)(U)$),
  node((0, 1), $cal(G)(U)$),
  node((1, 0), $cal(F)(V)$),
  node((1, 1), $cal(G)(V)$),
  arr($cal(F)(U)$, $cal(G)(U)$, $Phi(U)$),
  arr($cal(F)(V)$, $cal(G)(V)$, $Phi(V)$),
  arr($cal(F)(V)$, $cal(F)(U)$, "res"),
  arr($cal(G)(V)$, $cal(G)(U)$, "res")
)]
  where $V supset Y$ is open.
]
#definition[
  A morphism of ringed spaces $(X, cal(O)_X) -> (Y, cal(O)_Y)$ is a  pair $(f, f^\#)$ where $f: X -> Y$ is continuous and $f^\#: cal(O)_Y -> f_* cal(O)_X$.
]
#example[
  $(U subset.eq RR^n, C^1) -> (V subset.eq RR^m, C^1)$.
]
#remark[
  When we say $(X, cal(O)_X)$, we mean that $cal(O)_X$ is a subsheaf of $cal(F)"ct"_(bb(k))$ for some fixed $bb(k)$. Then $cal(O)_X = {phi:  U-> bb(k) | phi "satisfies some condition"}$. And, $cal(O)_X -> f_* cal(O)_Y$ is always given by precomposition.
]
== Category of quasi Affine varieties "qAffVar".
To define this cateogry, we'll have the objects be open subsets of an affine variety consdiered as a ringed space. The morphisms will be maps of ringed spaces with $f^\#$ being the precomposition as our convention above dictates. 

#theorem[
  $X, Y$ both affine varieties. $U subset.eq X$ open. Then there exists a natural bijection.
  $
    "Mor"(U, Y) tilde.eq "Hom"_(bb(k)"-alg")(A(Y), cal(O)(U)).
  $
]

#pagebreak()
= Projective morphisms
=== Ok unfortunately i was forced to miss two classes so there is gap here
#proposition[
  Suppose $X, Y$ are prevarieties with affine covers ${U_i}$ and ${V_j}$ respectively. Then $X times Y$ is a product in the category of prevarieties constructed by gluing together $U_i times V_j$ and $U_(i') times V_(j')$,
  $
    (U_i sect U_(i')) times (V_j sect V_(j'))
  $
  for all such pairs. 
]
We did not prove that gluing gives you a prevariety, but we will believe it. Also note that $X times Y$ is a prevariety by affine cover ${U_i times V_j}$. 
#proposition[
  For $Y subset.eq X$ closed where $iota : Y -> X$ and $X$ is a prevariety. Then for $U' subset.eq Y$ open,
  $
    iota^* cal(O)_X (U') = {f: U' -> bb(k) | forall y in U', exists U_y subset X "with" phi in cal(O)_X (U_y) "such that" f restriction U_y sect Y = phi}.
  $
  Then $iota^* cal(O)_X$ is a sheaf and $(Y, iota^* cal(O)_X)$ is a prevariety, and $iota : Y -> X$ is a morphism.
]
#proof[
  We will believe that $iota^* cal(O)_X$ is a sheaf. Also $iota$ is a morphism of prevarieties. 

  Let $U subset.eq X$ be affine open. We claim that $(U cap Y, iota^* cal(O)_X restriction U cap Y)$ is affine. We claim that $Y = V(I)$ for some $I subset.eq A(X)$.

  Then, $iota^* cal(O)_X$ are the functions that are locally restrictions of regular functions on $X$. Then $cal(O)_(V(I))$ are functions that are locally quotient of polynomials on $AA^n$. These are equal.
]
We say that $iota$ is a closed embedding. 
#example[
  1. $AA^2 -> AA^2$ via $(x,y) |-> (x, x y)$. This maps $AA^2$ to itself without the $y$-axis, but still including the origin. Note that the image of this map is neither open nor closed in $AA^2$. 
    #remark[
      $Y subset.eq X$ is locally closed if it is $U cap V$ where $U$ is open in $X$ and $V$ is closed in $X$.
  ]
    This example is not even locally closed.
  2. Glue $AA^1$ and $AA^1$ along $AA^1 without {0} -> AA^1 without {0}$ via the identity. This is basically a line with two origins. Let this line be called $X$. Consider $g:  X-> X$ via switching the origins and keeping the other points the same. This is a morphism where our open subsets are lines including only one of the origins, and it is not hard to check that this is actually a morphism. Then,
      ${g(x) = x)}  tilde.eq AA^1 without {0}$
    which is not closed in $X$.
]
#definition[
  A prevariety of $X$ is a variety of the diagonal map $Delta: X -> X times X$ defined by $x |-> (x, x)$ is a closed embedding. 
]
#lemma[
  For checking if something is a variety, $Delta$ being a topologically closed embedding is a sufficient condition.
]
#corollary[
  Open and closed subprevarieties of varieties are varieties. 
]
#lemma[
  Let $X$ and $Y$ be affine varieties and $f: X -> Y$. If $f^\# : A(Y) ->> A(X)$, then $f$ is a closed embedding.
]
#proof[
  Let $J$ be the kernel. And consider the surjective map 
  $
    k[uy]/I(Y) ->> k[ux]/I(X).
  $
  This is also surjective onto $k[uy]/(I(Y) + J)$. This is $V_Y (J)$, so we get that $A(V_Y (J)) tilde.eq A(X)$ as desired.
]

#lemma[
  Let $X$ be an affine variety, then $Delta: X -> X times X$ defined by $x mapsto (x, x)$ is a closed embedding.
]
#proof[
  $A(X) = k[ux]/I(X)$, $A(X times X) tilde.eq A(X) times.circle A(X)$. THen we can map
  $
    k[ux, uy]/(I_x(X) + I_y(Y)) ->> k[ux]/I(X)
  $
  via $x_i mapsto x_i$ and $y_i mapsto x_j$.
]
#proposition[
  $X$ prevariety is a variety if $Delta(X) subset.eq X times X$ is closed.
]
#proof[
  We claim that $forall x in X$, take any $x in U subset X$ affine open. Then $Delta restriction U : U -> U times U$ is a closed embedding.

  Since $Delta (X) subset.eq X times X$ is closed (topologically closed embedding, locally closed embedding implies closed embedding. So $cal(O)_X tilde.eq cal(O)_(Delta(X))$.

  It is important theat $Delta restriction U$ is closed because of the following:

  $Y subset.eq X$ such that $forall y in Y$, $exists U_y subset X$ containing $y$ such that $U_y cap Y$ is closed in $U_y$ does not imply that $Y subset.eq X$ is closed. However, under our assumption, it would be that way.
]
#corollary[
  $"qAffVar"$ are varieties.
]
#corollary[
  $X ->^f Y$ morphism of varieties. The graph $Gamma_f := {(x,y) in X times Y | y  =f(x)}$ is closed in $X times Y$.
]
#proof[
  $X times Y ->^(f times id) Y times Y$. Then $(f compose id)^(-1) (Delta(Y)) = Gamma_f$.
]
#exercise[
  Let $X$ be a variety and $U, U' subset.eq X$ open affine subsets. Then $U cap U'$ is also affine open.
]

#definition[
  Let $X subset.eq PP^n$ be a projective algebraic subset. $cal(O)_X (U) = {phi : U -> bb(k) | "locally encrypted" (phi restriction U') = F/G "for some homogeneous poly" F,G "of same degree."}$.
]
#proposition[
  $X subset.eq PP^n$ projected algebraic set $arrow.squiggly (X, cal(O)_X)$ if for all $i = 0,1,dots, n$, let $U_i = PP^n without V(x_i) tilde.eq^"homeo" AA^n$. Then $(X cap U_i, cal(O)_X restriction U_i)$ is isomorphic as a ringed space  to $X cap U_i$ considered as a closed subset in $AA^n$ under $AA^n tilde.eq U_i$ and hence an affine variety. In particular, $X$ is a prevariety.
]
#proof[
  $X = V(F_1, dots, F_m)$. Then $X cap U_i  subset AA^n$ is $V(F_1(x_0, dots, x_i = i, dots, x_n), dots, F_m)$.

  If we have $F/G in (X cap U_i, cal(O)_X restriction U_i)$, then we can just dehomogenize to get $f/g in (X cap U_i, cal(O)_(X cap U_i subset.eq AA^n))$.
]

#lemma[
  $X subset PP^n$ a projective variety. Let $F_0, dots, F_m$ be homogeneous polynomials on $PP^n$ of same degree. Then $F: X without V(F_0, dots, F_m) -> PP^m$ by $x mapsto (F_0(x), dots, F_m (x))$ is a morphism.
]
#proof[
  As a set map, this is well-defined. We will verify that $forall j = 0, dots, m$, the distinguished open subset $U_j = {[underline(Y)] in PP^m | Y_j != 0}$. We have 
  $
    F^(-1)(U_j) =  PP^n without V(F_j).
  $
  Then $F^(-1)(U_j) -> U_j$ where $U_j tilde.eq AA^m$. We'll call the coordinates of $AA^m$ by $(Y_0/Y_j, dots, Y_m/Y_j)$. So if we have a point $x in F^(-1)(U_j)$, then the associated point in $AA^m$ would attained by sending  
  $
    x mapsto ((F_0 (x))/(F_j (x)), dots, (F_m (x))/(F_j (x))).
  $
  We showed that if we had a map from a quasi affine variety $W ->X$ where $X$ is an affine variety, we just had to map $A(X) -> cal(O) (W)$. In an exercise, we showed that you can replace "quasi affine variety" with "prevariety" and get the same result. 
]
#example[
  1. $PP^1 -> PP^n$ where we map $[s: t] mapsto [s^n: s^(n-1) t : dots.c : t^n]$. We know this will be a morphism by our lemma as long as we verify that it is full of zeroes only when $s=t=0$, but this is clear.

    We can also map $PP^1 -> PP^2$ by $[s: t] mapsto [s^3: s^2 t: t^3]$. This is because it maps nicely as above to $[s^3: s^2 t: s t^2 : t^3]$, then we can project to drop the third coordinate to get the map we are describing. We are left to show that projections are morphisms
  2. Projections: $PP^n without {[1: 0: dots.c : 0]} -> PP^(n-1)$ by mapping 
    $
      [x_0: dots.c x_n] mapsto [x_1: dots.c: x_n].
    $
    More formally, we can consider $PP V without {[v]} -> PP(V / span(v))$, or $PP V without PP W -> PP (V slash W)$ where $W subset V$.

    So, the second example above becomes $PP^3 without [0: 0: 1: 0] -> PP^2$. 
  3. Veronese embedding. 
    $
      nu_d: PP^n -> PP^(binom(n + d, d) - 1)
    $
    by $[x] mapsto ["every monomial of" x "of degree" d]$.
  #exercise[
    $nu_d$ is a closed embedding.
  ]
  4. Segre embedding:
    $
      PP^n times PP^m -> PP^((n+1)(m+1))
    $
    by $([underline(X)], [underline(Y)]) mapsto mat(x_0 y_0, dots, x_0 y_m; dots.v, , dots.v; x_n y_0, dots,  x_n y_m)$ where this really should just be one long vector, but it is easier to represent as such. We will prove that this is a closed embedding.
    #proof[
      Fix some $0 <= i <= n$ and $0 <= j <= m$. Then we have 
      $
        U_(i j) &tilde.eq AA^(m n + m + n) \
        &={[z_(a b)] in PP^((n+1)(m+1) - 1) | z_(i j) != 0}.        
      $
      Then $S^(-1) (U_(i j)) = U_i times U_j$ where $U_i  subset PP^n$ and $U_j subset PP^m$.The coordinates are $x_a/x_i$'s and $y_b / y_j$'s. This maps $AA^(n+m) -> AA^(n + m + n m)$ where the coordinates are $z_(a b)/z_(i j)$'s. We could map 
      $
        z_(a b) / z_(i j) mapsto (x_a y_b) / (x_i y_j).
      $
      We claim that this is surjective. This is clear, as for example $z_(a j) / z_(i j) mapsto x_a/ x_i$.
    ]
  5. $PP^1 times PP^1 -> PP^3$ maps $(mat(a; b), mat(c, d)) mapsto mat(a c , a d ; b c, b d)$. The matrix is isomorphic to $PP^1 times PP^1$. Then the image is the same as $V(x w - y z)$ where $mat(a c , a d ; b c, b d) = mat(x, y; z, w)$.
  6. $X subset PP^n$ and $V(F_0, dots, F_m) cap X = emptyset$. Then $F: X -> PP^m$ is a well-defined morphism. The question is: do all maps from $X -> PP^m$ arise in this way?

    Well the answer is no because $P^1 times P^1 -> PP^3$ as defined in the last example works. We can project $PP^1 times PP^1$ to $PP^1$. And the counterexample arises because there is no $F_0, F_1$ of the same degree such that there is no map $PP^3 without V(F_0, F_1) -> PP^1$ that makes the diagram commute.

    Let $S: PP^1 times PP^1 -> PP^3$ and let $Q = im(S)$. We want $Q cap V(F_0, F_1) = emptyset$. However, $V(Q, F_0, F_1)$ has codimension at most 3, so dimension at least 0, in particular non-empty. This comes from Krull's height theorem.
  7. If we are given four random lines in $PP^3$, how many meets all $4$? The answer is 2.

    As an exercise, consider $3$ random lines in $PP^3$, we can consider the union of all lines that touch all $3$ and show that it is a projective variety.
]


=== I skipped class again oops

#pagebreak()

= Rational maps
For today and the rest of the week, we assume that every variety is irreducible. 

*Warm-up*: Let $f,g: X -> Y$ be maps of varieties such that $f restriction U = g restriction U$, $exists space emptyset != U subset.eq^("open") X$, then $f = g$. 
#proof[
  Let $X -> X times X$ by the diagonal map $Delta$. Then let $X times X -> Y times Y$ by $f times g$. The inverse image of $Delta(Y)$ is ${x | f(x) = g(x)}$. Since they agree on an open subset and it is dense, they are actually equal.
]
#definition[
  A rational map $phi : X arrow.dashed Y$ is an equivalence class of pairs $(U, phi_U)$ where we have that $nothing != U subset X$ is open and $phi_U: U -> Y$ is a morphism. Then we have $(U, phi_U) tilde (V, psi_V)$ if we have that $phi_U restriction U cap V = psi_V restriction U cap V$.

  
]
#definition[
  $phi: X arrow.dashed Y$ is dominant if $phi(U)$ is dense in $Y$ or some/every rep $(U, phi_U)$.

  $phi$ is birational if $exists psi: Y arrow.dashed X$ such that $phi compose psi = id_Y$ and $psi compose phi = id_X$.

  Two varieties are birational if there exists a birational map between them.
]

#remark[
  In general, you cannot compose rational maps. 
]
#example[
  1. $PP^(n + m)$ and $PP^n times PP^m$ are birational. This is because there is a copy of $AA^(n+m)$ in both of them.
  2. $AA^1$ and $V(x^3 - y^2)$ are birational. Consider $t mapsto (t^2, t^3)$, or rather $(x,y) mapsto y/x$ in the opposite direction.
  3. $PP^1$ and $V(y^2 z - x^3 - x^2 z) subset PP^2$. Take $[x: y] mapsto [x : y : frac(x^3, y^2 - x^2)]$.
]

#remark[
  A variety $X$ is rational if it is birational to $AA^n$ for some $n$. 
    #question[
  Is there a non-rational variety? (Yes.)
]
]
Is $phi: X arrow.dashed Y$ dominant and injective in a nonempty open subset, is it birational? This is true for characteristic zero, but false for characteristic $> 0$. 
#remark[
  $X$ is unirational if $exists$ dominant $AA^n arrow.dashed X$. Rational and unirational are not equivalent. There are also non unirational varieties.
]
#definition[
  A rational function on $X$ is a rational map from $X arrow.dashed AA^1$. We denote
  $
    K(X) := {"rational functions on" X}
  $
  and call it the (rational) function field. 
]

#theorem[
  $
    {"dominant rational maps" X arrow.dashed Y} <--> {k"-alg extensions" K(Y) subset.eq K(X)}
  $
  by the map $f mapsto (phi mapsto phi compose f)$.
]
#proof[
  Let $Theta: K(Y) arrow.hook K(X)$. We may assume $Y$ is affine, $Y subset.eq AA^n$. Now look at the functions $Theta(y_1), dots, Theta(y_m)$, where $A(Y) = kk[uy]/I$ for some ideal $I$. All of the functions listed are regular on some open $U subset X$. 

  So we have made a map from $A(Y) -> cal(O)_X (U)$ by $y_i mapsto Theta(y_i)$, which defines a morphism (there is some theorem that says having a map from a coordinate ring to the structure sheaf defines a morphism).
]

#corollary[
  This bijection is an equivalence of categories:
  $
    {"vars and rational dominant maps"} <-> {"finitely generated field extensions over" kk}.
  $
]
#corollary[
  $X$ and $Y$ varieties. The following are equivalent:
  1. $X$ and $Y$ are birational.
  2. $exists thin emptyset != U subset.eq^("open") X$, $V subset.eq^("open") Y$ such that $U tilde.eq V$ isomorphic.
  3. $K(X) tilde.eq K(Y)$.
]
1 to 2 can be verified. 2 to 3 uses the theorem above. 

#theorem[
  Let $f: X arrow.dashed Y$ be a dominant map. Then $f$ is generically finite (i.e. for any representative $f: U -> Y$, general fiber is finite) if and only if $K(Y) subset.eq K(X)$ is a finite extension. Further, if gen. fin. and $"char" k = 0$, then general fiber has exactly $[K(X) : K(Y)]$.
]
#corollary[
  In characteristic zero, a rational dominant map that is generically one to one is birational. This is very false in positive characteristic.
]
#proof[of Theorem 8.8][
  Reduce to $X, Y$ affine, $X ->^f Y$ where $X subset.eq AA^n$ and $Y subset.eq AA^m$ where $m <= n$. Reduce to $m = n-1$, where this map is now $(z_1, dots, z_n) mapsto (z_1, dots, z_(n-1))$. 
  
  Now we split into cases: 
  1. $z_n in K(X) = kk[z_1, dots, z_n] slash I$ is algebraic over $K(Y)$. By definition, there is a minimal polynomial $G = a_d (z_1, dots, z_(n-1))z_n^d + dots.c + a_1 (z_1, dots, z_(n-1)) z_n + a_o (z_1, dots, z_(n-1)) in K(Y)[z_n]$. We may assume that $G in A(Y)[z_n]$.

    $D_Y (a_d) != emptyset$ open in $Y$, $f$ is finite over $D(a_d)$. The discrimnant $Delta$ of $G$ will be nonzero on $Y$. In other words, on $D_y(a_d dot Delta)$, $|"fiber"| = d$.
]

== Wasn't here for first part of blowups 
#definition[
  Let $X subset.eq AA^n$ be an affine variety, $I = angled(f_0, dots, f_m) subset A(X)$. The blowup, which we define as $tilde(X) = B ell_I X$, is the subvariety of $X times PP^m (subset AA^n times PP^m)$ given by $u$-homogeneous elements of $ker(kk[ux][underline(u)] ->> A(X)[t I] subset.eq A(X)[t])$. $pi: tilde(X) -> X$ the "blow-down" map.
]

#proposition[
  $B ell_I X$ is independent of the choice of generators $f_0, dots, f_m$.
]
#proof[
  $B ell_(angled(f_0, dots, f_m)) X tilde.eq B ell_(angled(f_0, dots, f_m, g)) X$.
]
#proposition[
  $I = angled(f_0, dots, f_m) subset A(X)$. Then $tilde(X) = B ell_I X tilde.eq$ closure in $X times PP^m$ of the image of 
  $
    (X without V(I)) -> X times PP^m
  $
  given by $
             x mapsto (x, [f_0(x), dots, f_m(x)]).
           $
]
#proof[
  1. $overline(X) subset.eq tilde(X)$: 
  2. $tilde(X) subset.eq overline(X)$: 
]
== im retarded
= Smoothness/Nonsingularness

What is a tangent vector? Rather, for $0 in X subset.eq AA^n$, how can we find a tangent vector to $X$?
1. Something in the tangent space?
#example[
  Suppose $char k != 2$, $X = V((x-1)^2 + (y-1)^2 - 2)$. Then we can say that 
  $
    T_0 X = V(x + y).
  $
  But how do we get this? We can see that 
  $
    (x-1)^2 + (y-1)^2 - 2 = x^2 - 2x + y^2 - 2y.
  $
  And we see $-2(x+y)$ is the gradient of this function or something idk.
]
#definition[
  For $0 in X subset.eq AA^n$, 
  $
    T_0 X := V(f^"linear" | f in I(X)).
  $
  For $p in X subset.eq AA^n$, 
  $
    T_p K := ker Jac[frac(partial f_i, partial x_j) (p)]_(i, j)
  $
  for any generating set $f_1, dots, f_m$ of $I(X)$.
]
#definition[
  Let $A$ be a $k$-alg and $M$ an $A$-module. Then 
  $
    Der_k (A, M) := {delta in Hom_k (A, M) | forall f, g in A, delta(f g) = f delta(g) + g delta(f)}.
  $
]
#example[
  Let $A  = k[x, y]$ and $M = k[x, y] slash angled(x-a,y-b)$ for $a, b in k$. Then this is isomorphism by $k$ with the group action of acting by $a$ on $x$.

  Then 
  $
    Der_k (A, M) = k[frac(partial, partial x)|_(x = a\ y = b), frac(partial, partial y)|_(x = a\ y = b)].
  $
  So for $delta in A$, we have $delta(x^n) = n x^(n-1) dot delta(x) = n a^(n-1) delta(x)$.
]
#definition[
  Zariski cotangent space of $p in X$ is $frak(m) slash frak(m)^2 tilde.eq frak(m) times.circle A(X) slash frak(m)$. 
]
#proposition[
  Let $0 in X subset.eq AA^n$. Then
  $
    T_0 X tilde.eq Hom_k (frak(m) slash frak(m)^2 , k) tilde.eq Der_k (A(X), A(X) slash frak(m) tilde.eq k)
  $
  where $frak(m) = angled(overline(x)_1, dots, overline(x)_n)$. We can accomplish this with the maps 
  $
    v mapsto (overline(f) mapsto f^"linear" (v))
  $
  from first to second and 
  $
    delta mapsto (overline(f) mapsto delta(f))
  $
  for third to second.
]
#proof[
  Let $phi(delta) = overline(f) mapsto delta(f)$. Then $delta(frak(m)^2) = 0$ implies that $delta = 0$. Also $delta(1) = 0$, so it is injective. 

  I'm too lazy to write this whole thing out
]
#remark[
  Note that $dim T_p X >= codim_X p$.
]
#definition[
  $X$ variety is nonsingular at a point $p in X$ if 
  $
    dim T_p X = codim_X p.
  $
]
#proposition[
  $p in X$ is nonsingular if and only if $dim T_p X <= codim_X p$. Also if and only if $T_p X = T C_p X$. Also if and only if $dim (frak(m) / frak(m)^2) = dim cal(O)_(X, p)$. Also if and only if $rank Jac [(frac(partial f_i, partial x_j) (p))]_(i, j) = n - codim_X p$ when $X subset.eq AA^n$.
]

#example[
  $X = V(x^3 + x^2 - y^2) subset AA^2$. $T C_0 X = V(x^2 - y^2)$. $T_0 X = AA^2$. 
]

#remark[
  A Noetherian ring $(R, frak(m))$ is a regular local ring if $dim frak(m) slash frak(m)^2 = dim R$.
]
#theorem[
  Regular local rings are UFDs.
]
#proof[
  Something something Nakayama.
]
#proposition[
  Let $p in X subset.eq AA^n$ is nonsingular if $rank Jac_p (f_1, dots, f_m) >= n - codim_X p$ for any $f_1, dots, f_m$ such that $V(f_1, dots, f_m) = X$.
]

#exercise[
  Suppose $Y subset PP^n$, $angled(F_1, dots, F_m) = I(Y)$. To test $X subset AA^n$ is nonsingular, 
  $
    sum_(i=0)^n frac(partial F, partial x_i) = (deg F) F.
  $ 
]
#theorem[
  Let $X$ be a variety. Then the nonsingular loci is open and nonempty in $X$. 
]
#proof[
  Reduce to $X$ being affine. $X$ is irreducible, $X subset.eq AA^n$, $V(f_1, dots, f_m) = X$. Then 
  $
    rank [Jac_p (f_1, dots, f_m)] >= n - dim X
  $
  so $X_("sing") = V(codim X + 1 "minors of" Jac) cap X$.
]
#lemma[
  Any irreducible variety $X$ is birational to an irreducible hypersurface $V(f) subset AA^n$.
]
#proof[
  Take $K(X) slash k$ which is separable and finitely generated and separably generated. So there exists $x_1, dots, x_d in K(X)$ such that $K(X) supset k(x_1, dots, x_d)$ where $d = dim X$. Then 
  $
    K(X) tilde.eq (k(x_1, dots, x_d)[y])/(f(y))
  $
  where the coefficients of $f$ are in $x_1, dots, x_d$. 
]

#definition[
  $PP$ irreducible smooth variety, $X, Y$ irreducible subvarieties of $PP$, and $X cap Y supset Z$ an irreducible comp. We say $X$ and $Y$ intersect transversally at $p in Z$ if
  1. $p$ is smooth on $X$ and $Y$. 
  2. $codim_(T_p PP) T_p X + codim_(T_p PP) T_p Y = codim_(T_p PP) (T_p X cap T_p Y)$.
]
#pagebreak()
#lemma[
  If $X sect.and Y$ at $p in Z$, then $p$ is nonsingular on $Z$ and $codim Z = codim X + codim Y$.
]
#proof[
  Reduce to $PP = AA^n$. Then $I(X) = angled(f_1, dots, f_k)$ and $I(Y) = angled(g_1, dots, g_ell)$. Then 
  $
    rank Jac_p (f_1, dots, f_k, g_1, dots, g_ell) <= codim T_p Z = rank Jac_p (f_1, dots, f_k) + rank Jac_p (g_1, dots, g_ell)\
    codim X + codim Y <= codim T_P Z <= codim Z <= codim X + codim Y.
  $
  Therefore they are all equal. 
]
#theorem[Bertini][
  Fix $X subset.eq PP^n$. Then a general hyperplane $H subset.eq PP^n$ intersects $X$ transversally at all nonsingular points in $X$.
]
#proof[
  Let $Gamma = {(x, H) | H "not transversally intersecting" X "at" x} subset.eq X_("sm") times (PP^n)^(or.curly)$. We claim this is closed. 

  Fact 1: Let $X ->> Y$ and general fiber has $dim X - dim Y$. Then
  $
    dim Gamma = dim X + codim X _ 1 = n-1.
  $
  So then 
  $
    dim pi_2(Gamma) <= n-1
  $
  which shows us that $pi_2(Gamma)  subset.neq (PP^n)^(or.curly)$. Then another fact is that image of a morphism of varieties is constructible. 
]
#remark[
  Let $f : X -> PP^n$ and $X$ smooth. For general $H subset.eq PP^n$, is $f^(-1)(H)$ smooth? This is true for $char = 0$ and false otherwise. 
]
#remark[
  If $X subset.eq PP^n$ is smooth and irreducible with $dim X > 1$. Then for general $H subset.eq PP^n$, $X cap H$ is smooth, but is it irreducible?

  This is true but very hard to prove.
]

= Hilbert functions

Given $X subset.eq PP^n$, what is $deg(X subset.eq PP^n)$?

Requirements:
1. $deg (X "finite") = \# |X|$.
2. $deg (V(F)) = deg(F)$.
5. $(deg X)(deg Y) = deg(X cap Y)$ when $X$ transversally intersects $Y$.
6. $deg(I(X) + I(Y)) = sum_(z "irred comp" X cap Y) "mult"_z (deg z)$.
idk i cant read the rest of the board
#definition[
  Let $S = k[x_0, dots, x_n]$ and $I$ a homogeneous ideal. The Hilbert function of the ideal $I$ is defined as $h_I : ZZ_(>= 0) -> ZZ_(>= 0)$ where
  $
    h_I(d) := dim_k (S slash I)_d.
  $
  For $X subset.eq PP^n$, $h_X(d) := h_(I(X))(d)$.
]
#example[
  1. $h_(PP^n) (d) = binom(d + n, n)$.
  2. $h_("pt") (d) = 1$.
  3. Suppose $V(I) = emptyset$. Then $h_I (d) = 0$ for $d >>0$. 
  4. Let $I = angled(x_0^3, x_0^2 x_1) subset.eq k[x_0, x_1]$.
]
#lemma[
  Let $I, J subset.eq S$. Then $h_(I cap J) + h_(I + J) = h_I + h_J$.
]
#proof[
  $0 -> S slash (I cap J) -> S slash I plus.circle S slash J -> S slash (I + J) -> 0$. The first map is $f mapsto (f, f)$ and the second is $(f,g) mapsto f - g$.
]
#lemma[
  Let $I subset.eq S$. Let $f in S$ be a nonzerodivisor on $(S slash I)_d$ for $d >>0$. Then $h_(I + angled(f)) = h_I (d) - h_I (d - deg f)$. 
]
#proof[
  Consider the sequence $0 -> (S slash I)_(d - deg f) -> (S slash I)_d -> (S slash I + f)_d -> 0$.
]

#pagebreak()
#theorem[
  Let $I subset.eq S$ be homoegenous. There exists a unique Hilbert polynomial $chi_I (t)$ such that $h_I (d) = chi_I (d)$ for $d >>0$. Moreover $deg chi_I (t) = dim V(I) subset.eq PP^n$. Note that we will say $deg 0 := -1$ and $dim emptyset := -1$.
]
#definition[
  A polynomial $P(t) in QQ(t)$ is numerical if $P(d) in ZZ$ for all $d >> 0$, $d in ZZ$.
]
#lemma[
  1. If $P(t)$ numerical of degree $r$, then there exists unique $c_0, dots, c_r in ZZ$ such that
  $
    P(t) = c_r binom(t, r) + c_(r-1) binom(t, r-1) + dots.c + c_0.
  $
  2. If $f: ZZ -> ZZ$ such that $Delta f (d) := f(d+1) - f(d)$ is a numerical polynmoial for $d >> 0$, then so is $f$ for $d >> 0$. 
]
#proof[
  1. Induct on $deg P$. 
  $
    P &= c_r binom(t, r) + dots.c + c_1 binom(t, 1) + c_0 \
    Delta P &= c_r binom(t, r-1) + dots.c + c_1.
  $
  In particular, $P(d) in ZZ$ for all $d$.
  2. Let $Q(t)$ such that $Q(d) = Delta f(d)$ for all $d >> 0$. 
  $
    Q(t) &= c_r binom(t, r) + dots.c + c_1 binom(t, 1) + c_0 \
    P(t) &= c_r binom(t, r+1) + dots.c + c_1 binom(t, 2) + c_0 binom(t, 1) + C \
    Delta (P-f) (d) &= 0.
  $
  This last statement implies $P-f$ is a constant. Now we induct on $V(I)$.
    - Base case: $V(I) = emptyset$. Then $chi_I = 0$.
    - Now pick $f$ homogeneous linear such that the lemma applies. So the lemma then tells us that  $Delta h_I (d) = h_(I + angled(f)) (d + 1) = chi_(I + angled(f)) (d + 1)$. We would be done, but this relies on the claim that $dim  V(I  + angled(f)) = dim V(I) - 1$.

    So let $f$ be a nonzerodivisor, $S slash angled(I_d)$, $dim  V(angled(I_d) + f)= dim V(I_d) - 1$. We claim that in fact $dim V(I_d) = dim V(I)$. 
]
#definition[
  For $I subset.eq S$, $deg(I) := "coefficient of" binom(t, dim V(I)) "in" chi_I $. This is also the leading coefficient of $t^(dim V(I))$. Then $deg(X subset.eq PP^n) := deg I(X)) dot (dim V(I))!$.
]
#example[
  1. $chi_(PP^n) (d) = binom(d + n, n) = h_(PP^n) (d)$. Also $deg(PP^n subset.eq PP^n) = 1$.
  2. $$
]