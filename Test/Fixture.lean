/-
Self-contained Verso doc that exercises every directive in
`Napkin.Meta.Directives` and the `{cite}` role from
`Napkin.Meta.Citations`. Used by `tests/check-fixture.sh` as a
render-diff regression check: refactors that don't change the
rendered HTML pass; refactors that do require regenerating the
golden file (and reviewing the diff).

Coverage strategy: each helper that has a conditional branch is
exercised in both branches at least once. Specifically:

* `numberedKindLabel`: callouts inside numbered chapter (label
  assigned) AND callouts in unnumbered intro (no label).
* `renderTitledLabel` / `renderParenLabel`: empty title and
  non-empty title for each.
* `renderTitleMarkup`: plain text, `$`math` segment, multiple
  segments, an unclosed `$`.
* `renderBoxCallout` with `extraCls`: each Statement variant
  (Theorem/Lemma/Proposition/Corollary/Fact).
* `chiliPeppers`: 0, 1, 2, 3.
* `citeRef`: known key (`ref:vakil`) and deliberately-unknown key.
* `epigraph`: with cite, attribution-only, neither.
-/

import VersoManual
import Napkin.Meta.Directives
import Napkin.Meta.Citations
import Napkin.Bibliography

open Verso.Genre Manual
open Napkin

set_option pp.rawOnError true

#doc (Manual) "Directive Fixture" =>

%%%
htmlToc := false
%%%

Intro paragraph.
The numbered-callout below sits in the doc intro, outside any chapter.
Because `assignCalloutNumber` requires two numbered ancestors, it
should render with no label.

:::THEOREM
Theorem outside any numbered chapter — should have no label.
:::

:::REMARK
Remark outside any numbered chapter — should also have no label.
:::

# Numbered Part

%%%
file := "Numbered-Part"
%%%

## Numbered Chapter

Body text.
The callouts under this section get labels of the form `1.1.N`.

### Title rendering

:::THEOREM
Untitled theorem.
:::

:::THEOREM "Plain title"
Theorem with a plain-text title.
:::

:::THEOREM "$`\\mathbb{R}` is complete"
Theorem whose title contains a math segment.
:::

:::THEOREM "Multiple math: $`\\mathbb{R}` and $`\\mathbb{Z}`"
Theorem title with multiple math segments.
:::

:::THEOREM "Mismatched $`\\open"
Theorem title with an unclosed math segment (degraded fallback).
:::

### Statement variants

:::LEMMA "A named lemma"
Body of a titled lemma.
:::

:::LEMMA
Body of an untitled lemma.
:::

:::PROPOSITION "Named"
Body of a titled proposition.
:::

:::COROLLARY
Body of an untitled corollary.
:::

:::FACT
Body of a fact.
:::

:::FACT "With title"
Body of a titled fact.
:::

### Box callouts

:::DEFINITION "Group"
Body of a titled definition.
:::

:::DEFINITION
Body of an untitled definition.
:::

:::EXAMPLE "The integers"
Body of a titled example.
:::

:::EXAMPLE
Body of an untitled example.
:::

:::EXERCISE "Easy"
Body of a titled exercise.
:::

:::EXERCISE
Body of an untitled exercise.
:::

### Problems with chili counts

:::PROBLEM "Hard problem" (chili := 2)
Problem with title and 2 chilis.
:::

:::PROBLEM (chili := 0)
Problem with no title and no chili.
:::

:::PROBLEM "Three-chili problem" (chili := 3)
Problem with 3 chilis.
:::

:::PROBLEM (chili := 1)
Problem with 1 chili and no title.
:::

### Inline-label callouts

:::REMARK
Untitled remark.
:::

:::REMARK "Important"
Titled remark.
:::

:::ABUSE
Untitled abuse of notation.
:::

:::ABUSE "Notation"
Titled abuse of notation.
:::

### Unnumbered callouts and structural blocks

:::PROOF
First paragraph of the proof.

Second paragraph (gets a QED marker via CSS).
:::

:::QUESTION
Body of a question.
:::

:::PROTOTYPE
Body of a prototype.
:::

:::MORAL
Body of a moral.
:::

:::quote
First paragraph of an extended quotation.

Second paragraph.
:::

:::aside
Body of a default-titled aside.
:::

:::aside "Detail"
Body of a custom-titled aside.
:::

:::aside "Math title $`\\mathbb{C}`"
Aside with a math title.
:::

:::chiliPara (chili := 1)
A paragraph with 1 chili in the margin.
:::

:::chiliPara (chili := 3)
A paragraph with 3 chilis in the margin.
:::

### Citations

Inline cite to a known key {cite}`ref:vakil` and an unknown key {cite}`ref:nonexistent`.

:::epigraph "Author Name" (cite := "ref:vakil")
Epigraph with both attribution and cite.
:::

:::epigraph "Just Author"
Epigraph with attribution only.
:::

:::epigraph
Epigraph with neither attribution nor cite.
:::
