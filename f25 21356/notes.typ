#set heading(numbering: "1.")
#set enum(numbering: "1.a)")

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [Real Analysis II],
  author: "Rohan Jain",
  date: datetime(year: 2025, month: 08, day: 25),
  preface: [
    #align(center + horizon)[
      No more tice!
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
= Sequences

#theorem[Bolzano Weierstrass][
  If a sequence $(x_n)$ in $RR^d$ is bounded, then it has a convergent subsequence.
]
#proof[
  We take $(x_(n, 1))$. By the $d=1$ case, it has a convergent subsequence, let's say $(x_(n_k, 1))$.  Then we take $(x_(n_k, 2))$, it has a convergent subsequence, let's say $(x_(n_(k_ell), 2))$. Etc. Once we have reached the $d$th coordinate, we can guarantee that we have convergent on every coordinate. 

  This shows that we have a convergent subsequence because $x_n -> x^*$ iff $forall j <= d$, we have that $x_(n, j) -> x_j^*$.
]
#definition[
  We say a sequence $(x_n)$ is Cauchy if $forall epsilon > 0$, $exists N$ s.t. $forall n, m >= N$, we have that $|x_n - x_m| < epsilon$.
]
#definition[
  We say that $(X, rho)$ is complete if every Cauchy sequence $(x_n)$ in $X$ is convergent.
]

#theorem[
  $(RR^d, | dot |)$ is complete.
]
#proof[
  $d=1$ is known. Coordinate wise application of the $d=1$ case shows that $(RR^d, | dot |)$ is complete.
]
= Continuity
#definition[
  Let $D subset RR^d$, $F: D -< RR^ell$ is continuous at a point $a in D$ if $ forall epsilon >0$, there is $delta > 0$ such that for all $x in D$, 
  $
    |x - a| < delta &=> |F(x) - F(a)| < epsilon.
  $
]
#lemma[
  $F$ being continuous at $a$ is equivalent to $forall (x_n)$ in $D$, $x_n -> A => F(x_n) -> F(a)$. 
]