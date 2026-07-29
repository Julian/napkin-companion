import VersoManual
import Napkin.Meta.Lean
import Napkin.Meta.Directives
import Napkin.Meta.Citations

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

open Napkin

set_option pp.rawOnError true

#doc (Manual) "Colophon" =>

%%%
number := false
%%%

:::epigraph "Ravi Vakil" (cite := "ref:vakil")
When introduced to a new idea, always ask why you should care.
Do not expect an answer right away, but demand one eventually.
:::

# The Napkin

The _Infinitely Large Napkin_ was written by Evan Chen as a light, mostly self-contained tour of a wide range of higher math.
The original LaTeX source and PDF live at [https://github.com/vEnhance/napkin](https://github.com/vEnhance/napkin).

If you like this book and want to support Evan, please consider buying him a coffee!

[![Ko-fi](kofi4.png)](https://ko-fi.com/evanchen)

[https://ko-fi.com/evanchen/](https://ko-fi.com/evanchen/)

*For Brian and Lisa, who finally got me to write it*.

© 2026 Evan Chen.
Text licensed under [CC-by-SA-4.0](https://creativecommons.org/licenses/by-sa/4.0/).
Source files licensed under [GNU GPL v3](https://choosealicense.com/licenses/gpl-3.0/).

This is (still!) an *incomplete draft*, and an incomplete companion to an incomplete draft!

For corrections, comments, or pictures of kittens regarding the original Napkin, contact Evan at [evan@evanchen.cc](mailto:evan@evanchen.cc), or pull-request at [https://github.com/vEnhance/napkin](https://github.com/vEnhance/napkin).

# A Lean companion

This rendering is a Lean & Mathlib companion to the Napkin prepared by [Julian](https://github.com/Julian).

The companion was prepared for Julian himself to read, and it targets an audience (undoubtedly bigger than one in theory) who simultaneously:

  * wants to learn more math
  * wants to learn more Lean & Mathlib
  * wants (or is forced) to do so in a self-guided way outside of a formal degree program

Each chapter ends with a *Formalization* section that revisits its content in Mathlib's vocabulary — pointing at the names, lemmas, and (occasionally) design choices you'd reach for to formalize what you've just read.
The body of each chapter stays free of Lean, so you can focus on it as mathematical knowledge beforehand.

The math prose began from Evan's, with executable Lean and Mathlib excerpts and minor presentation tweaks added by Julian.
Evan's voice and first-person pronouns have been preserved in the book contents wherever feasible — so when the body of a chapter says "I" or "mine", that's Evan.

LLMs were a big part of porting the prose and images, and of authoring exercises.
The goal however is for Julian to read the book cover-to-cover in its new state and correct any AI-induced errors.
Julian is a fan and hobbyist, not a mathematician, so undoubtedly any errors introduced are his (even those via LLMs), not Evan's!
If you find an error in the math that isn't in the [original Napkin](https://github.com/vEnhance/napkin), it has very likely been introduced by the port and is Julian's responsibility, not Evan's.
Please report companion-specific issues, corrections, or suggestions at [github.com/Julian/napkin-companion](https://github.com/Julian/napkin-companion/issues).

# How to read the Formalization sections

*What they assume.*
They assume you can read a Lean theorem statement and are on speaking terms with the basic tactics — `intro`, `exact`, `apply`, `rw`, `simp`, `cases`, `induction`, `obtain`, `refine`.
Nothing beyond that, and in particular no Mathlib.
If Lean itself is new, the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) is the shortest way in and [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) is the standard follow-up; both teach *Lean*, whereas what these sections teach is *Mathlib* — which typeclass holds a given concept, what its lemmas are called, and why they are stated the way they are.
Where a chapter's material has a counterpart in that book, its Formalization section opens by naming the relevant chapter.
The math itself is assumed only as far as the chapter above has taken you.

*What is in them.*
Each new idea gets a paragraph naming the Mathlib object that carries it, followed by code you can read as a worked model.
A `recall` block quotes a real Mathlib declaration's signature; it is checked against Mathlib as the book is built, so a quoted statement cannot silently drift out of date.
Mathematical notation is sometimes live too: where a symbol is underlined with dots, hovering it shows the signature and doc-string of the Mathlib definition behind it.
Exercises are labelled — "Lean exercise", numbered alongside the chapter's other callouts — and their proof is left as `sorry`.
The prose above states the task; where the guidance separates cleanly from the statement, the sentences naming which lemmas to reach for sit in a collapsible *Hint* beneath, so the exercise can be attempted cold and you decide when to be told.
A chili pepper (🌶) marks a section's closing exercise where the intended solution runs to several steps, the same difficulty glyph the problem sections use.
Under that sits a collapsible solution — a complete proof, commented to explain the move rather than merely to display the term.
Within a section the exercises escalate: the first is usually a step or two, the last is a small theorem.

*Where Mathlib has nothing to offer.*
A few chapters reach objects Mathlib does not define.
Rather than stopping at a note, the companion defines them — as faithfully as Lean allows — in a namespace `Napkin.Missing`, and builds the worked models and exercises on top.
These are stopgaps awaiting the real thing, and each is flagged where it is used.

*Where the code says something false.*
Every function in Mathlib is total: it returns a value on every input, including the inputs where the mathematics defines none.
So `1 / 0` is `0`, and so is `(0 : ℝ)⁻¹`; `Real.log 0` is `0`; subtraction on `ℕ` stops at zero, making `2 - 3 = 0`; the supremum of the empty set of reals is `0`; and `∑' n, f n` and `deriv f x` are `0` whenever the series does not converge or the function is not differentiable there.
None of these are claims about mathematics.
They are the price of totality, paid so that every expression means something and no function needs to carry a proof of its own applicability just to be written down.
The mathematics is restored by the *theorems*, which carry the hypotheses the definitions dropped: the lemma that lets you cancel `n - m + m` wants `m ≤ n`, and the one computing a logarithm wants `0 < x`.
When a statement in this book looks too strong, the usual explanation is that its hypotheses are excluding a junk value, and the chapters point this out where it first bites.

*Running it yourself.*
Every code block in the book is elaborated during the build, against the Mathlib and Lean versions pinned in the [companion's repository](https://github.com/Julian/napkin-companion).
You do not have to reassemble a chapter's imports to work in it: each chapter is also published as a pair of ready-to-open files, `<Chapter>-exercises.lean` (every code block in order, exercises still `sorry`) and `<Chapter>-solutions.lean`, under `exercises/` alongside these pages, and regenerated by `lake exe exercises`.
Both are elaborated on every build of the book, so a file that fails to compile is a bug and worth reporting.

*When you cannot guess a name.*
Guessing is a real skill and worth practising: Mathlib names describe the statement, read left to right, in the `mul_one`, `sub_nonneg`, `map_mul`, `isOpen_iInter` style, with `_iff_` joining the two halves of an equivalence.
When guessing fails, ask: `exact?` searches for a lemma closing the goal outright, `apply?` for one that reduces it, and `rw?` for one that rewrites with it.
Reaching for these is expected, not cheating — no exercise in this book is meant to hinge on your having memorized a name.
