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
- "concrete" categories: sets with some sort of familiar structure (groups, rings, modules, etc.)
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
  
== 09/04/2025
Examples of functors between concrete categories:
1. Forgetful functors. E.g. $U: "Mon" -> Set$. $U(M) = M$. And if $f: M->N$ is a monoid homomorphism. Then $U(f): U M -> U N$, so we just take $U(f) = f$. Then we just have to check that $U(g compose f) = U(g) compose U(f)$ but this is obvious. There are other similar examples like $"Vect"_k ->Set$ or $"Top" -> Set$. Basically it's just "forgetting" some sort of structure from the original category.
2. Free functors. E.g. $F: Set -> "Mon"$ which is the free monoid functor. 

  Let $A$ be a set, $"List"(A) = {"strings" a_1, dots, a_n | n >= 0, a_i in A}$. So if $A  = {"a", "b", "c"}$, then we have that 
  $
    "List"(A) = {"<>", "a", "b", "c", "aa", "ab", "ac"...}.
  $
  Define concatenation as $dot$ where 
  $
    (a_1 a_2 dots a_n) dot (b_1 b_2 dots b_m) = (a_1 a_2 dots a_n b_1 b_2 dots b_m).
  $
  We claim that $"List"(A)$ is a monoid with unit $"<>"$. Call that monoid $F A in "Mon"$. 

  On morphisms: given $f: A->B$, get monoid homomorphism $F(f) = F A -> F B$, we define 
  $
    F(f)(a_1 a_2 dots a_n) = f(a_1) f(a_2) dots f(a_n).
  $
  We can also check that $F(f compose g) = F(f) compose F(g)$ and $F(id_A) = id_(F A)$.

#definition[Contravariant Functor][
  A contravariant functor from $cal(C)$ to $cal(D)$ is a functor $F: cal(C)^op -> cal(D)$.
]

*Universal Mapping Property*

Idea: universal property of $X$ is a description of morphisms into/out of $X$. 

== 09/11/2025
*Natural Transformations*

Let $cal(C)$ and $cal(D)$ be categories, $F, G: cal(C) -> cal(D)$. A natural transformation $alpha: F->G$ consists of components $alpha_A: F(A) -> G(A)$ for each $A in cal(C)$, such that for any $f: A -> B$ in $cal(C)$, we have that $G(f) compose alpha_A = alpha_B compose F(f)$. This latter condition is called the naturality condition.

#definition[
  The category of graphs is $[J^op, Set]$. The objects of graphs are all the functors $F: J^op -> Set$, which consists of:
    - a set $F(0)$ "vertices"
    - a set $F(1)$ "edges"
    - a function $F(sigma): F(1) -> F(0)$ "source"
    - a function $F(tau): F(1) -> F(0)$ "target"
]

#definition[
  A category $cal(C)$ is small if $Ob(cal(C))$ and every $cal(C)(A, B)$ is a set.

  Examples of small categories: $bb(2)$, $J$.

  Large or non-small categories: $Set$, $Mon$, $Top$.
]


#definition[
  $Cat$ is the category of small categories. The objects of $Cat$ are small categories, and the morphisms are functors.
]

= Limits
== 09/16/2025
We start by talking about the construction of objects. For sets $A, B$, we can form:
- Disjoint union $A + B$, which is a coproduct (colimit).
- Cartesian product $A times B$, which is a product (limit).
- Set of functions $B^A$, which is exponential (adjunctions).
*Products* of sets. 
#definition[
  Let $A, B$ be sets. Their Cartesian product $A times B$ is the set of pairs $(a, b)$ where $a in A$ and $b in B$. 
]
We write $pi_1: A times B -> A$ and $pi_2: A times B -> B$ for the projection maps.

What is UMP of $A times B$? For a set $S$, giving a function $f: S -> A times B$ is the same thing as giving for each $s in S$, an element $f(s) in A times B$, which is the same thing as giving each $s in S$ an element $a(s) in A$ and an element $b(s) in B$. Explicitly, $a = pi_1 compose f$ and $b = pi_2 compose f$. 

*UMP of $A times B$*

For any set $S$ and $f_1: S->A$ and $f_2: S->B$, there is a unique $u: S -> A times B$ such that $f_1 = pi_1 compose u$ and $f_2 = pi_2 compose u$. 

#definition[
  $cal(C)$ a category, $A, B in cal(C)$. A diagram $A <-_(p_1) P ->_(p_2) B$ is a product diagram if: for any object $X$ and $f_1: X->A$ and $f_2: X->B$, there is a unique $u: X -> P$ such that $f_1 = p_1 compose u$ and $f_2 = p_2 compose u$. 
]

Terminology: 
- $p_1, p_2$ are "projections" and $P$ is the "product" of $A$ and $B$.
- $u: X->P$ is the map induced by $f_1, f_2$. Write $u = angled(f_1, f_2)$ or $u = (f_1, f_2)$.
- $P$ is "the product" of $A$ and $B$, but:
  - being "a product" is a property of the whole diagram and not just a property of $P$,
  - "the" product may not be unique,
  - it also may not exist. 

#definition[
  Given $cal(C)$, and $A,B in cal(C)$, define the double slice category $cal(C) slash (A, B)$ by:
  - objects: ($X in cal(C)$, $f_1; X->A$, $f_2: X->B$). That is, $A <-_(f_1) X ->_(f_2) B$.
  - morphisms: from $(X, f_1, f_2)$ to $(X', f_1 ', f_2 ')$ is a morphism $f: X->X'$ such that $f compose f_1 = f_1 '$ and $f compose f_2 = f_2 '$. 
]

Fact: a diagram in $cal(C)$ $A <-_(p_1) P ->_(p_2) B$ is a product diagram iff in $cal(C) slash (A, B)$, it is a terminal object: for every object of $cal(C) slash (A, B) ni (A <-_(p_1) P ->_(p_2) B)$, there is a unique morphism of $cal(C) slash (A, B)$ from it to $(A <-_(p_1) P ->_(p_2) B)$.

#proposition[
  $cal(D)$ category. If $X, Y in cal(D)$ are both terminal objects, then there is a unique isomorphism $X -> Y$.
]
#proof[
  Get (unique) morphism $f: X->Y$ since $Y$ is terminal. Get (unique) morphism $g: Y->X$ since $X$ is terminal. We have that $g compose f: X->X$ and want to show that it is the identity. But since $X$ is terminal, there is only one map from $X->X$, so therefore $g compose f = id_X$. Likewise with $f compose g$ and $id_Y$. Therefore, $f$ is an isomorphism with $g$ as its inverse.
]
"Product diagrams are unique up to unique isomorphism."
== 09/18/2025
#theorem[
  $cal(C)$ has finite products if and only if $cal(C)$ has binary products and a terminal object.
]
#proof[sketch][

  $==>$:  binary products, terminal object are finite products

  $<==$: Given a finite family $(A_i)_(i in I)$, need to build a product.

  if $I = emptyset$: terminal object.

  if $|I| = 1$: then $A$ is the product of $(A)$.

  if $|I| = 2$: binary product.
]
#colbreak()
*Equalizers*

#definition[
  Given $A arrows.rr_g^f B$, form $E = {a in A | f(a) = g(a)} subset.eq A$ and the inclusion map $e: E ->A$ defined as $e(a) = a$.

  In $E ->^e A arrows.rr_g^f B$, we have $f compose e = g compose e$. If FINISH LATER
]
#definition[
  $cal(C)$ a category, $(A arrows.rr_g^f B) = P$ "parallel pair" in $cal(C)$. A fork on $P$ is $(E, e)$ where $E ->^e A arrows.rr_g^f B$ such that $f compose e = g compose e$. 

  A fork $E ->^e P$ is an equalizer (diagram) if for any $X->^f A$ such that $f compose h = g compose h$, there is a unique $u$ such that $e compose u = h$.
 
]

== 09/23/2025
#definition[
  A commutative square is called a pullback if for every $T$, $q_1: T->X$, $q_2: T->Y$ such that $f compose q_1 = g compose q_2$, there is a unique $u: T->P$ such that $p_1 compose u = q_1$ and $p_2 compose u = q_2$.
]

*Fact*: In $Set$, a square is a pullback iff for every $x in X$ and $y in Y$ with $f(x) = g(y)$, there is a unique $a in P$ such that $p_1(a) = x$ and $p_2(a) = y$. 

#proof[
  Elements correspond to map from $1 =:T$. Also, given $q_1: T->X$ and $q_2: T->Y$, define $u: T->P$ by $u(t) = "the unique" a in P "such that" p_1(a) = q_1(t)$ and $p_2(a) = q_2(t)$.
]
#definition[
  Given $f: X->Z$ and $z in Z$, the fiber of $f$ (or $X$) over $z$ is 
  $
    X_z := fib_f (z) := {x in X | f(x) = z} subset.eq X.
  $
]
#lemma[Two pullbacks lemma][
  In any category $cC$, given a diagram
    #align(center)[#commutative-diagram(
  node((1, 1), $X'$),
  node((1, 2), $Y'$),
  node((2, 1), $X$),
  node((2, 2), $Y$),
  node((1, 3), $Z'$),
  node((2, 3), $Z$),
  arr($X'$, $X$, $p$),
  arr($Y'$, $Y$, $q$),
  arr($X$, $Y$, $f$),
  arr($Y$, $Z$, $g$),
  arr($X'$, $Y'$, $f'$),
  arr($Y'$, $Z'$, $g'$),
  arr($Z'$, $Z$, $r$),
)]
#align(center)[#commutative-diagram(
  node((1, 1), $X'$),
  node((2, 1), $X$),
  node((1, 2), $Z'$),
  node((2, 2), $Z$),
  arr($X'$, $X$, $p$),
  arr($X'$, $Z'$, $g'f'$),
  arr($Z'$, $Z$, $r$),
  arr($X$, $Z$, $g f$),
)]
then
- if the first and second squares are pullbacks, then so is the third square.
- if the second and third squares are pullbacks, then so is the first square.
]
*Limits*

Products, equalizers, and pullbacks are all instances of limits. Fix an "index category" $I$ (small). A diagram (of shape $I$ in $cC$) is a function $D: I-> cC$. A cone in a diagram $D$ consists of an object $X$ ("vertex") plus maps $f_i: X-> D(i)$
for $i in I$ such that for each $h: i->j$ in $I$, we have that the diagram below commutes:
#align(center)[#commutative-diagram(
  node((1, 1), $X$),
  node((1, 2), $D(i)$),
  node((2, 2), $D(j)$),
  arr($X$, $D(i)$, $f_i$),
  arr($X$, $D(j)$, $f_j$),
  arr($D(i)$, $D(j)$, $D(h)$),
)]
#colbreak()
== 09/25/2025
#definition[
  - $cC$ has limits of shape $I$ if every diagram $D: I-> cC$ has a limit cone.
  - $cC$ has all limits if it has limits of shape of $I$ for all small categories $I$.
  - $cC$ has finite limits if it has limits of shape of $I$ for all finite categories $I$.
    $I$ is finite if it has finitely many objects and finitely many morphisms.
]

#proposition[
  $cC$ has all limits if and only if $cC$ has all products and equalizers.
]
#proof[
  Forward direction is clearly true, as we know that products and equalizers are both limits.

  $
    lim_I D = "equalizer of" [product_(i in I) D(i) arrows.rr^s_t product_(h: j->k) D(k)]
  $
]
= Duality
If $cC$ is a category, then $C^op$ is also a category. 

Dictionary:
- $cC$, $cC^op$
- $A$, $A^*$
- $f: A->B$, $f^*: B^*->A^*$
- isomorphism $f: A->B$ ($exists g: B->A$ such that $f g = id$, $g f= id$). In the opposite category, $f^*: B^* -> A^*$ ($exists g^*: A^* -> B^*$ such that $f^* g^* = id$, $g^* f^* = id$)
- a terminal object $X$ in $cC$ is an initial object $X^*$ in $cC^op$.

We saw that terminal objects of $cC$ are unique up to unique isomorphism. This means that initial objects of $cC$ are unique up to unique isomorphism. 

This is what we call a "proof by duality": we apply a theorem to $cC^op$ and translate it to $cC$.

*Coproducts*

A diagram is a coproduct diagram if for all $X, j_1: A->X, j_2: B->X$, there is a unique $u: C-> X$ such that $i_1 u = j_1$ and $i_2 u = j_2$.
#align(center)[#commutative-diagram(
  node((0, 0), $A$),
  node((0, 2), $B$),
  node((1, 1), $C$),
  node((2, 1), $X$),
  arr($A$, $C$, $i_1$),
  arr($B$, $C$, $i_2$),
  arr($C$, $X$, $exists ! u$),
  arr($A$, $X$, $j_1$, curve: -20deg),
  arr($B$, $X$, $j_2$, curve: 20deg),
)]
$i_1$, $i_2$ called "inclusions", $C$ a "coproduct", and $C = A + B$.


== 09/30/2025
*Colimits*

After learning about limits, I believe I know everything about colimits.

== 10/02/2025
