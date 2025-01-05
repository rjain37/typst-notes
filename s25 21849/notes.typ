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
= Chapter 1
== Section 1

= Chapter 2
== Section 2