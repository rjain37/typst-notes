#import "@preview/ctheorems:1.1.3": *
#show: thmrules


#let blue = rgb("#d8d8f7")
#let purple = rgb("#efe6ff")
#let red = rgb("#FFDBDD")
#let black = rgb("#000000")
#let gray = rgb("#a7a3a3")
#let green = rgb("#c5e0c5")

#let blue_stroke = rgb("#363699")
#let green_stroke = rgb("#196214")

#let theorem = thmbox(
	"global",
	"Theorem",
	fill: blue,
	base_level: 1,
  stroke: (left: black)
)

#let lemma = thmbox(
  "global",
  "Lemma",
  fill: purple,
  base_level: 1,
  stroke: (left: black)
)

#let corollary = thmbox(
  "global",
  "Corollary",
  fill: red,
  base_level: 1,
  stroke: (left: black)
)

#let proposition = thmbox(
  "global",
  "Proposition",
  fill: green,
  base_level: 1,
  stroke: (left: black)
)

#let definition = thmbox(
  "definition",
  "Definition",
  stroke: green_stroke,
  base_level: 1
)

#let example = thmplain(
  "example",
  "Example",
  base_level: 1,
  titlefmt: strong
)

#let exercise = thmplain(
  "example",
  "Exercise",
  base_level: 1,
  titlefmt: strong
)

#let remark = thmbox(
  "",
  "Remark",
  fill: gray
).with(numbering: none)

#let question = thmbox(
  "question",
  "Question",
  base_level: 1,
  titlefmt: strong,
  stroke: blue_stroke
).with(numbering: none)

#let proof = thmproof("proof", "Proof", titlefmt: smallcaps,)
#let solution = thmproof("solution", "Solution", titlefmt: smallcaps)

#let toc = {
	pagebreak(weak: true)
	show outline.entry.where(
		level: 1
	): it => {
		v(1em, weak: true)
		strong(it)
	}
	outline(
		title: "Table of Contents",
		indent: 1.5em,
		fill: repeat[]
	)
}
