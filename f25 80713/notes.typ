#set heading(numbering: "1.")
#set enum(numbering: "1.a)")
#set math.equation(numbering: none)

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

#pagebreak()
#toc
#counter(page).update(1)
#pagebreak()
#counter(page).update(1)
= Chapter 1
== Section 1
#theorem[Erdos][
  Idk this guy basically did everything
]
#proof[
  insert some proof here
]
#corollary[
  literally everything
]
#definition[Integer][
 whole number, positive or negative 
]

= Chapter 2
== Section 2