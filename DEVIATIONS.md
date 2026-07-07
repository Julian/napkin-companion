# Deviations from the upstream text

This book is a faithful port of Evan Chen's *An Infinitely Large Napkin*
(the LaTeX source lives under `book/`) interleaved with Lean/Mathlib
formalization content. The prose is ported verbatim wherever possible.
This file records every place the port deliberately deviates, and why.

Formalization commentary itself — `recall` blocks, worked `example`s,
Mathlib naming discussions — is the point of the project, not a
deviation, and is not listed here.

## Book-wide conventions

These apply to every chapter and are not repeated in the per-chapter
lists below.

1. **Types, not sets.** Carriers of algebraic and topological
   structures are types ("a type of points $M$") rather than sets, and
   element-of is written `x : X` instead of $x \in X$, matching the
   Lean code alongside. Genuine subset membership (a subgroup $H$, an
   ideal $I$, a subspace $W$) keeps $\in$. Set-theory chapters are the
   planned exception, where sets are the actual subject matter.

2. **The `Group`/`AddGroup` split.** Upstream has a single "group with
   operation $\star$" concept; Mathlib maintains parallel multiplicative
   and additive hierarchies related by `to_additive`. Chapters
   acknowledge this divergence where it first bites (Groups, chapter on
   the structure theorem) rather than hiding it.

3. **Units instead of "nonzero residues".** Upstream's
   $(\mathbb{Z}/n\mathbb{Z})^\times$ is modeled as `(ZMod n)ˣ`, the
   group of *units*, which is a group for every $n$, not only primes.
   The Groups chapter works through why this is the right generality.

4. **Figures.** Some upstream Asymptote/tikz art is redrawn as SVG
   (with captions written for this edition); the rest is currently
   omitted, with the surrounding prose adjusted to stand alone.
   Omitted figures are itemized per chapter below; restoring more of
   them as SVGs is ongoing work, not a settled decision.

5. **Hints and solutions.** Upstream collects `\begin{hint}` /
   `\begin{sol}` blocks into backmatter appendices. The port inlines
   short hints as "(Hint: …)" parentheticals in some chapters; a
   ported hints/solutions appendix does not exist yet.

6. **Cross-references.** Upstream's `\Cref` links become descriptive
   phrases ("the basis-completion theorem", "a problem at the end of
   the previous chapter"), since the port does not yet have a
   cross-reference mechanism for numbered callouts across chapters.

7. **Footnotes.** Footnotes are either inlined as parentheticals,
   converted to `{margin}[…]` notes, or dropped when purely
   digressive. Mathematically substantive drops are itemized below.

8. **Starred problems.** Upstream marks some problems as required
   (`\sproblem`) or important (`\dproblem`); the port currently renders
   all problems uniformly (chili difficulty counts are preserved).

9. **Titles.** Some upstream untitled theorem/definition/example
   blocks gain short descriptive titles, and a few long titles are
   shortened, so that the HTML callout headers stay readable.

10. **Voice.** Upstream's self-references ("in Napkin", "Evan
    yapping") are removed or recast so the book reads as
    self-contained; the body text never frames itself as a port.

11. **Silent typo fixes.** Upstream mathematical typos are corrected
    without comment (itemized per chapter below).

## Formalization-forced deviations

Places where Mathlib's design genuinely differs from the chapter's
mathematical framing, acknowledged in the text where they occur:

- **Calculus / Limits.** Mathlib's `Real.sSup` returns `0` for empty
  or unbounded sets, versus the chapter's $\sup S = +\infty$
  convention; `ENNReal`/`EReal` are named as the faithful carriers.
  Mathlib's `HasSum` is unconditional (net) convergence over finite
  subsets, unlike the chapter's prefix-sum definition, so
  permutation-invariance is automatic and conditional convergence has
  to be reintroduced by hand.
- **Calculus / Limits.** The chapter constructs $\mathbb{R}$ by
  Dedekind cuts; Mathlib's `Real` is the Cauchy completion of `ℚ`.
- **Calculus / p-adics.** Mathlib defines `ℚ_[p]` first and carves out
  `ℤ_[p]` as the closed unit ball — the reverse of the chapter's
  inverse-limit-first construction.
- **Calculus / Integration.** Mathlib's `intervalIntegral` is a
  Bochner (Lebesgue-flavored) integral; the chapter's Riemann
  construction is presented for pedagogy and connected to the Mathlib
  API afterward.

## Per-chapter notes

Chapters not listed deviate only via the book-wide conventions above.

### Frontmatter

- **Colophon** is a reconstruction rather than a verbatim port: the
  epigraph is relocated, first-person recast, dates pinned, and a new
  "A Lean companion" section added. The dedication ("For Brian and
  Lisa…") is not ported.
- **Preface** adds one sentence directing companion-specific errata to
  this repository.
- **Advice** replaces the LaTeX dependency digraph with a regenerated
  clickable SVG chapter graph.

### Starting Out

- **Groups.** The D₁₀ art is redrawn as SVG with a new caption. Two
  parenthetical pointers to the sets-and-functions appendix are
  dropped (the appendix is not yet ported). The forward reference to
  Lagrange becomes "we'll prove it later in more generality". The
  trailing "Formalities" section is companion-only content.
- **Metric spaces.** Four figures redrawn as SVG with new captions.
  One bridging sentence to an unported problem dropped. A margin note
  is imported from a footnote in a different upstream chapter
  (metric-prop.tex) where it fit naturally.

### Basic Abstract Algebra

- **Quotients.** Cosets/fibers picture recreated as SVG with a new
  caption; otherwise verbatim.
- **Rings.** Verbatim modulo conventions.
- **Flavors.** The ℤ[i] lattice-rounding figure, the ℤ[√11] hyperbola
  figure, and both side-divisor lattice figures are omitted with prose
  adjusted. The contributed section's non-native English is lightly
  copy-edited.

### Basic Topology

- **Metric properties.** The $[0,1]^2$ covering figure is omitted.
  The Makholm problem's yes/no table is rendered as prose, with the
  math.SE attribution moved into the body.
- **Topological spaces.** The open-neighborhood, Hausdorff, and
  subspace figures are omitted (the homotopy-motivation figures are
  redrawn as SVG); the sentence motivating connectedness via the
  $\{0,1\}$-valued map problem dropped.
- **Compactness.** Three figures omitted. Upstream's "Proof using
  covers" / "Proof using sequences" headers are currently untitled
  PROOF blocks.

### Linear Algebra

- **Vector spaces.** The pictorial matrix displays and the linear-map
  cartoon are replaced with prose/arrays. Hints are inlined as
  parentheticals.
- **Eigen-things.** Jordan-block displays condensed; two illustrative
  block matrices omitted. The cross-referenced problem is given the
  coined name "the eventual-kernel-image splitting".
- **Dual space and trace.** Two intermediate computation displays
  condensed.
- **Determinant.** The parallelogram-area figure is omitted; one
  expanded determinant display condensed; one problem retitled.
- **Inner product spaces.** Two "abbreviated in the literature"
  sentences and two intermediate Cauchy-Schwarz displays condensed.
- **Fourier analysis (bonus).** The solution to the final problem
  (the exact-probability lemma behind Arrow) awaits the
  hints/solutions backmatter, per the book-wide convention.
  Upstream's multi-line `align` chains are split into consecutive
  displayed equations.
- **Adjoints.** Several optional proofs are condensed or omitted (row
  rank = column rank; the full matrix proof of the conjugate-transpose
  identity; normal ⟺ orthonormally diagonalizable), keeping the
  one-line versions upstream also gives. Two upstream typos fixed
  ($T^\vee \to T^\dagger$; basis for $V$ → basis for $W$). The $T^\dagger$
  vs $T^\vee$ diagram is rendered as prose.

### More on Groups

- **Group actions.** The orbits-partition and orbit-stabilizer figures
  are omitted.
- **Structure theorem.** The $R^{\oplus f} \to K \hookrightarrow
  R^{\oplus d} \to M$ diagram is rendered as an inline composition.

### Representation Theory

- **Semisimple.** Upstream's "inclusion to the $j$th component" is
  corrected to *projection*. Two commutative diagrams rendered as
  prose.
- **Characters.** Upstream's character "attached to $A$" corrected to
  "attached to $V$"; the "mysterious properties" renumbered (I)–(IV) →
  1–4.

### Quantum Algorithms

- **Circuits.** Every upstream Qcircuit diagram is rendered as prose,
  truth tables, or explicit matrices (Verso has no circuit-diagram
  machinery yet). New body material connects the gates to
  `Matrix.unitaryGroup`. An aside acknowledges the query-complexity
  content of Deutsch–Jozsa has no Mathlib formalization.
- **Shor.** The QFT circuit diagrams are described as gate lists in
  prose. An aside notes Mathlib has no named discrete Fourier
  transform on tuples (the `ZMod N` one exists).

### Calculus 101

- **Limits.** Two number-line figures omitted; see also the
  formalization-forced items above.
- **p-adics.** One footnote and two literature citations dropped; the
  "remark for experts" is promoted to an aside; upstream's off-by-one
  in the geometric series partial sums fixed. An aside notes
  Strassmann and Skolem–Mahler–Lech are not in Mathlib.
- **Differentiation.** Five figures (including the xkcd strip) are
  omitted. A new paragraph connects bump functions to
  `Real.smoothTransition` and partitions of unity.
- **Taylor.** Upstream's "It terms out" typo fixed. A parenthetical
  notes the $|h| = R$ boundary case is intentionally ambiguous.
- **Integration.** Both commutative diagrams rendered as
  equations/prose; four figures omitted.

### Complex Analysis

- **Holomorphic functions.** Seven figures omitted. The optional
  section proving holomorphic ⟹ analytic is not yet ported.
- **Meromorphic functions.** The $z^3$ winding figure omitted; two
  footnotes dropped.
- **Log.** The four red/blue-point diagrams are replaced with prose
  about loops and jumps; both lifting tikz-cds inlined. "Identify them
  with $S^1$" corrected to "identify their fundamental groups with ℤ".
- **Quintic.** Both figures omitted (upstream's imprecise "solvable"
  definition is faithfully preserved).

### Measure Theory

- **Carathéodory.** The first process table drops the "Construct
  order" column; the unit-disk covering picture and Cantor
  middle-thirds image are omitted; the proof that Lebesgue is the
  completion of Borel is omitted; the trailing stub section is
  omitted.
- **Lebesgue integration.** Upstream's four titled "step" boxes are
  flattened into running prose.
- **Swap sum.** The "Fubini and Tonelli" section and the three
  end-of-chapter problems are **newly written** — upstream has literal
  `\todo` stubs there.
- **Pontryagin.** Upstream's DTFT/DFT mix-up corrected. The answer to
  the counting-measure problem is stated inline.

### Probability

Upstream marks this entire part "(TO DO)": every chapter has `\todo`
stubs alongside real content. The port fills the gaps with **newly
written** material (in upstream's style, at comparable length) and
drops the "(TO DO)" from the part, chapter, and sales-pitch titles.

- **Random variables.** Upstream provides only the "Random variables"
  section and the two problems; the sections on distribution
  functions, examples of random variables, characteristic functions,
  and independent random variables are newly written.
- **Large number laws.** The "Convergence in law" section, the weak
  law's statement and proof (with Chebyshev's inequality stated there
  rather than in the strong-law section, since upstream's weak-law
  section was empty), the Weierstrass-approximation application, and
  the general-proof sketch are newly written; the rest is verbatim.
  The upstream title typo "convorgence" in the final problem is fixed.
- **Stopped martingales.** Newly written: the properties-of-
  conditional-expectation proposition (upstream `\todo{properties}`),
  the name-etymology aside (upstream `\todo`), the proof of the
  optional stopping theorem (upstream `\todo{do later tonight}`), the
  ABRACADABRA section, and the USA TST 2018 section (both "To be
  written" upstream, keyed off the reference links upstream left).
  The ballot-problem figure (upstream `\missingfigure{path}`) is
  drawn as an SVG.

### Differential Geometry

- **Multivariable calculus.** The tangent-line figure and
  `tangent.pdf` image are omitted.
- **Differential forms.** All six pictures omitted. The
  $\bigwedge^k(V^\vee)$ digression is abridged to a bridging sentence.
  Six footnotes dropped, including the finite-dimensionality caveat.
- **Stokes.** Both "Picture:" diagrams and the 18.02 grad/curl/div
  chart are omitted. Several upstream errors silently fixed (chain
  integrals, form-degree mislabels, the cross-product derivation).
- **Manifolds.** Four figures omitted; the π₂(Earth) aside and the
  historical footnote dropped; "level hypersurfaces" promoted from
  corollary to theorem.

### Riemann Surfaces

- **Complex structure.** All five figures omitted; upstream's garbled
  torus sentence repaired.
- **Morphisms.** The counterexample figure replaced by prose. The
  **Hurwitz formula section is newly written** — upstream is an empty
  `\todo`.
- **Affine and projective varieties.** The most heavily adapted
  chapter: many figures omitted and several passages condensed rather
  than verbatim; "Filling in the holes" and "Nodes of a plane curve"
  are **newly written** over upstream `\todo` stubs. A faithful
  re-port closer to upstream's wording is desirable.
- **Differential forms.** The final section ("Putting the pieces
  together: 1-forms on a Riemann surface") is **newly written** over
  upstream's one-sentence `\todo{write this}` stub. All four asy
  quiver figures are redrawn as TikZ SVGs. An aside notes
  manifold-level differential forms and holomorphic forms are absent
  from Mathlib.
- **Riemann–Roch.** The canonical-divisor passage and the
  applications list are **newly written** over upstream `\todo`
  stubs. Upstream's internally inconsistent "More complicated L(−)
  spaces" example is corrected (pole orders and dimension count made
  consistent with its own setup); "Riemann manifold" → "Riemann
  surface". Reveals use `meromorphicOrderAt` and
  `MeromorphicOn.divisor` (with the caveat the latter currently only
  covers subsets of ℂ); an aside notes Riemann–Roch itself is not in
  Mathlib.
- **Line bundles.** The final section ("Relation to invertible
  sheaves") is **newly written** over upstream's `\todo` stub, framed
  as a preview since sheaves come later. All nine 2D asy figures are
  redrawn as TikZ; the four 3D figures are converted from the
  vendored `book/3dfigures` PDFs as static SVGs. Upstream's
  "$U_1 \times U_2$" typo in the line-bundle definition is corrected
  to $U_1 \cap U_2$. Reveals connect to `Trivialization` /
  `VectorBundle` (noting Mathlib's base-first product convention) and
  `CommRing.Pic` / `ClassGroup.equivPic`; asides note holomorphic
  bundles are not in Mathlib.

### Algebraic NT I: Rings of Integers

- **Algebraic integers.** `\cite{ref:oggier_NT}` becomes a prose
  mention (key absent from the bibliography); "my blog" → "Evan's
  blog"; the blog URL moves to a margin note.
- **The ring of integers.** The two `subproof` environments are
  rendered as italic run-in headers within one PROOF block; the
  remark title "What went wrong with $\mathcal{O}_K$?" is
  de-symbolized. Upstream's grammatical quirks are preserved.
- **Unique factorization.** "the only case we'll use in Napkin" →
  "in this book"; `\cite{ref:ullery}` becomes a prose mention; one
  sentence pointing at a problem in an unported chapter is reworded
  to stand alone; two footnotes become margin notes.
- **Minkowski bound and class groups.** All seven asy lattice/region
  figures are redrawn as TikZ SVGs; the tikzcd "ingredients" diagram
  becomes a table plus prose. Upstream's garbled
  "$id(\kb) \mid (n)$" is corrected to $\mathfrak{b} \mid (n)$; one
  section header is de-symbolized; two upstream-untitled lemmas gain
  short titles; four footnotes become margin notes.
- **More properties of the discriminant.** Ported as the reminder-
  plus-problems chapter it is upstream; one added orientation
  paragraph notes that two of the problems are Mathlib's definitions
  (`Algebra.discr_def`, `Algebra.discr_powerBasis_eq_prod`).
- **Pell's equation.** Both display tables become Markdown tables;
  upstream's quirks (including the Hastings quotation as printed)
  preserved. Reveals connect to `Pell.Solution₁` /
  `Pell.IsFundamental` and `NumberField.Units` (Dirichlet), noting
  Mathlib covers the norm $+1$ equation only.

### Algebraic NT II: Galois and Ramification Theory

- **Things Galois.** The two embedding-tower diagrams and the two
  field/subgroup lattice diagrams are redrawn as SVGs (the latter
  combined into one side-by-side Galois-correspondence figure). Cross-
  references become descriptive phrases; "every field we see in the
  Napkin" → "in this book". Reveals cover `IsGalois`, the fundamental
  theorem (`IsGalois.intermediateFieldEquivSubgroup`), fixed
  fields/fixing subgroups, and splitting fields.
- **Finite fields.** The 𝔽₉ Frobenius-orbit diagram is redrawn as an
  SVG; a hint's upstream Fibonacci/field-symbol typo is corrected.
  Reveals cover `GaloisField p n` (the classification), `frobenius`,
  freshman's dream (`add_pow_char`), and cyclicity of `Fˣ`.
- **Ramification theory.** Two problems are **newly written** over
  upstream's `\todo{more problems}` stub. All four upstream diagrams
  are drawn as SVGs; one section header is de-symbolized. Reveals
  cover `Ideal.ramificationIdx`/`inertiaDeg`,
  `Ideal.sum_ramification_inertia` (the e·f identity), and Galois
  transitivity on primes above `p`; an aside notes the
  decomposition-group surjectivity and the inertia tower are not yet
  in Mathlib.
- **The Frobenius element.** Reveals connect quadratic reciprocity
  (`ZMod.legendreSym`, `legendreSym.quadratic_reciprocity`) and
  cyclotomic Galois groups (`IsCyclotomicExtension.autEquivPow`) to
  the Frobenius/Chebotarev story; asides note Chebotarev density is
  absent from Mathlib.

### Backmatter

- **References** is an auto-generated bibliography; upstream's
  per-topic "Pedagogical comments and references" prose is not yet
  ported.

## Unported content

Tracked as open work, not deviations:
Parts XIV–XXII (Algebraic NT I/II, Topology II, Category Theory,
Homology, Algebraic Geometry I/II, Set Theory I/II), and the
hints/solutions, notation, and sets-and-functions backmatter.
