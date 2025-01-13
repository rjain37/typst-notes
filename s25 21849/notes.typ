#set heading(numbering: "1.")
#set enum(numbering: "1.a)")

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [21-849: Algebraic Geometry I],
  author: "Rohan Jain",
  date: datetime(year: 2025, month: 01, day: 13),
  preface: [
    #align(center + horizon)[
      I don't know what a sheave or a category is. #emoji.heart
    ]
  ],
  table-of-contents: none,
)

#pagebreak()
#toc
#counter(page).update(1)
#pagebreak()
#counter(page).update(1)

= 
=== Administrivia
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




= Chapter 2
== Section 2