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
#let ux = $underline(x)$
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