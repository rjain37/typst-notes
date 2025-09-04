#set heading(numbering: "1.")
#set enum(numbering: "1.a)")

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [Category Theory],
  author: "Rohan Jain",
  date: datetime(year: 2025, month: 08, day: 25),
  preface: [
    #align(center + horizon)[
      I LOVE LEAN #emoji.heart.purple
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
= What is Category Theory?

Category theory is a language for talking about structuralist mathematics.

- materialism: an object is understood in terms of what it consists of 
- structuralism: an object is understood in terms of its relationships to other objects

== Motivating example

Let $D^2 = {(x, y) in RR^2 | x^2 + y^2 <= 1}$. Then let $S^1 = {(x, y) in RR^2 | x^2 + y^2 = 1} subset.eq D^2$.

#theorem[Brouwer's fixed point theorem][
  If $f: D^2 -> D^2$ is continuous, then $f$ has a fixed point. That is, there is some $x in D^2$ such that $f(x) = x$. 
]
The proof uses a trick and facts about homology. Effectively, there is a machine that takes a topological space (subsets of $RR^2$) and spits out a vector space (over $RR$).
1. For every topological space $X$, there is a vector space $H(X)$ (omitting actual definition).
2. For every continuous function $f: X -> Y$, there is an "induced" linear map given by $H(f): H(X) -> H(Y)$.
3. If $X ->^f Y ->^g Z$ are continuous maps, $H(f): H(X) -> H(Y)$, $H(g): H(Y) -> H(Z)$ and $H(g compose f): H(X) -> H(Z)$, then $H(g compose f) = H(g) compose H(f)$.
4. For any $X$, $H("id"_X) = id_(H(X)): H(X) -> H(X)$. 
Computations:
5. $H(D^2) tilde.equiv 0$.
6. $H(S^1) tilde.equiv RR$.
#proof[
  Assume $f: D^2 -> D^2$ is continuous and $f(x) = x$ for all $x in D^2$. Define a new function $r: D^2 -> S^1$ such that $r(x) = "intersection of the ray from " f(x) " to " x$ with $S^1 subset.eq D^2$. 

  Key fact: If $x in S^1$, then $r(x) = x$. Check that $r$ is also continuous.

  #align(center)[#commutative-diagram(
    node((0, 0), $D^2$, "disk"),
    node((1, -1), $S^1$, "first"),
    node((1, 1), $S^1$, "second"),
    arr("first", "disk", $iota$),
    arr("disk", "second", $r$),
    arr("first", "second", $id_(S^1)$)
  )
  ]
  #colbreak()
  The diagram above commutes. Now we can apply homology to it.

  #align(center)[#commutative-diagram(
    node((0, 0), $H(D^2)$, "disk"),
    node((1, -1), $H(S^1)$, "first"),
    node((1, 1), $H(S^1)$, "second"),
    arr("first", "disk", $H(iota)$),
    arr("disk", "second", $H(r)$),
    arr("first", "second", $H(id_(S^1))$)
  )
  ]

  We can check that 
  $
  H(r) compose H(iota) &= H(r compose iota) \
  &= H(id_(S^1)) \
  &= id_(H(S^1)).
  $
  Therefore, the new diagram also commutes. So, if $w in H(S^1)$, then 
  $
    w &= id_(H(S^1)) (w) = H(r)(H(iota)(w)) = 0.
  $
  This is a contradiction as $H(S^1) != 0$.
]

== Categories
#definition[Category][
  A category $cal(C)$ consists of: 
  - a collection of objects, $Ob(cal(C))$. For any $A in Ob(cal(C))$, we usually write $A in cal(C)$.
  - for any pair of objects $A, B in cal(C)$, there is a collection of morphisms $Hom_(cal(C))(A, B)$, or $Hom(A, B)$, or $cal(C)(A, B)$. Instead of $f in cal(C)(A, B)$, we write $f: A -> B$  or $A ->^f B$. 
  - for any objects $A, B, C in cal(C)$ and morphisms $f: A->B$ and $g: B->C$, there is a specified composition $g compose f : A->C$.
  - for any object $A in cal(C)$, there is a given $id_A : A-> A$
  - compositions are associative: $(g compose f) compose h = g compose (f compose h)$
  - for any $A ->^f B$, $f compose id_A = f = id_B compose f$
]

#example[
  - Set, the category of sets (& functions). 
]

#definition[Monoid][
  A monoid $(M, *)$ consists of: 
  - a set $M$
  - a binary operation $*: M times M -> M$ 
  - an identity element $e in M$ such that $forall x in M$, $e * x = x * e = x$.
]
#definition[Monoid Homomorphism][
  A monoid homomorphism $f: M -> N$ is a function satisfying 
  - $f(x y) = f(x) f(y)$.
  - $f(e) = e$.
]
#definition[Functor][
  A functor $F: cal(C) -> cal(D)$ is a function satisfying 
  - $F(A) in cal(D)$ for all $A in cal(C)$.
  - $F(f): F(A) -> F(B)$ for all $f: A -> B$ in $cal(C)$.
  - $F(g compose f) = F(g) compose F(f)$ for all $f: A -> B$ and $g: B -> C$ in $cal(C)$.
  - $F(id_A) = id_(F(A))$ for all $A in cal(C)$.
]

== 09/02/2025
Two "sorts" of categories:
- "concrete" categories: sets with smoe sort of familiar structure (groups, rings, modules, etc.)
- "abstract" categories: $bb(1)$, $bb(2)$, $bb(3)$, etc. More formal symbols than not.

#definition[Endomorphism][
  An endomorphism $f: A -> A$ is a morphism from an object to itself.
]

New categories from old:
1. Product category. 
  - input: two categories $cal(C)$ and $cal(D)$
  - output: $cal(C) times cal(D)$
  - objects: $(A, B)$ where $A in Ob(cal(C))$ and $B in Ob(cal(D))$
  - morphisms: $(f, g)$ where $f: A -> A'$ in $cal(C)$ and $g: B -> B'$ in $cal(D)$
  - composition: $(f, g) compose (f', g') = (f compose f', g compose g')$
  - identity: $(id_A, id_B)$

  Projection functors on $cal(C) times cal(D)$:
  - $pi_1: cal(C) times cal(D) -> C$, $pi_2: cal(C) times cal(D) -> cal(D)$.
  - on objects: $pi_1((A, B)) = A$
  - on morphisms: $pi_1((f, g)) = f: A -> A'$.
2. Slice categories, coslice categories
  - input: a category $cal(C)$ and an object $X in Ob(cal(C))$
  - output: $cal(C)slash X$ or $X slash cal(C)$
  description of coslice:
  - objects: pair $(A, f)$, where $A in Ob(cal(C))$ and $f: A -> X$ in $cal(C)$
  - morphisms: from $(A, f) -> (B, g)$: morphism $k: A ->B$ of $cal(C)$ such that $k compose f = g$.
  - composition: $(A, f) ->^k (B, g) ->^l (C, h)$ is $(A, f) ->^(l compose k) (C, h)$. We can check that $(l compose k) compose f = h$. The TLDR for this is that you can copy and paste commutative diagrams and get another commutative diagram. 
  
#example[Coslice][
  Let $cal(C) = Set$, $X = 1 = {*}$. So coslice $X slash cal(C) = 1 slash Set = ?$.
  - objects: pairs $(A, f)$ of a set $A$ and a function $f: 1-> A$.
  - morphisms: functions $k$ such that $k compose f = g$.
  Elements of sets categorically. $A$ is a set. How do we express $a in A$ in terms of the category $Set$? 
  $
    "elements of" A &<--> "functions "f:1 -> A \
    a in A &<--> f: 1 -> A, f(*) = a \
    f(x) in A &<--> f: 1->A.
  $
]
3. Opposite category.
  - input: a category $cal(C)$
  - output: $cal(C)^op$
  - objects of $cal(C)^op$: $A^*$ for $A in cal(C)$.
  - morphisms of $cal(C)^op (A^*, B^*)$: $f^*$ for $f: A -> B$ in $cal(C)$.
  - composition: $(f^* compose g^*) = (g compose f)^*$
  