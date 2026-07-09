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
   `\begin{sol}` blocks into two backmatter appendices ("Hints to
   selected problems" and "Sketches of selected solutions"). The port
   both inlines short hints as "(Hint: …)" parentheticals in chapters
   *and* gathers the full set into a single "Hints and Solutions"
   backmatter part (details in its per-chapter note below).

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

### Algebraic Topology I: Homotopy

- **Some topological constructions.** All of the chapter's Asymptote
  art (the $S^0$/$D^1$/$D^2$ sketches, the product-topology and unit-
  square pictures, the figure-eight, the CW-cell diagrams, and the
  torus/Klein/$\mathbb{RP}^2$ edge-identification squares) is omitted
  with the prose adjusted to stand alone; the two vendored raster
  images (`Projection_color_torus.jpg`, the Klein-bottle photos, and
  `earth.pdf`) are likewise dropped. The section header "The torus,
  Klein bottle, $\mathbb{RP}^n$, $\mathbb{CP}^n$" is de-symbolized to
  unicode. Reveals cover `Metric.sphere`/`Metric.closedBall`, the
  quotient/product/sum topologies (`Setoid`/`Quotient` with
  `isOpen_coinduced`, `isOpen_prod_iff`, `isOpen_sum_iff`),
  `UnitAddCircle` for the torus, `Projectivization` for real/complex
  projective space (noting the general topology instance is not yet in
  Mathlib), and `Topology.CWComplex`. The **wedge sum**, absent from
  Mathlib, is **built from scratch** as a quotient of `X ⊕ Y`.
- **Fundamental groups.** The path-fusing, loop, basepoint-independence,
  and homotopy-equivalence figures are omitted (prose stands alone); the
  `S2-simply.png` raster is dropped. The `\venus`/`\mars` symbols (not in
  KaTeX) become unicode ♀/♂. The higher-homotopy table is ported as a
  KaTeX array with `\{1\}` rendered as `1` and `\Zc{n}` as
  `\mathbb{Z}_n`. Two cross-references (to the category-theory chapters
  and to the covariant-Yoneda example) become descriptive phrases, and
  the commented-out functor diagram is realized as prose. Reveals cover
  `Path`/`Path.trans`/`Path.symm`/`Path.refl`, `Path.Homotopic`(`.Quotient`),
  `FundamentalGroup` (with a note on Mathlib's reversed `mul_def`
  composition order), `PathConnectedSpace`, `SimplyConnectedSpace`,
  `GenLoop`/`HomotopyGroup.Pi` for $\pi_n$, `ContinuousMap.HomotopyEquiv`
  /`ContractibleSpace`, and `FundamentalGroupoid.fundamentalGroupoidFunctor`.
- **Covering projections.** All Asymptote/TikZ art (the helix, the
  even-covering pancakes, the lifting diagrams, and the $\mathbb{R}/G$,
  torus, and $\mathbb{RP}^2$ pictures) is omitted along with the
  `even-covering.png` and `warsaw_circle.png` rasters; prose is adjusted
  to stand alone. Upstream's Problems section is only a `\todo{problems}`
  stub, so the port has none either. A cross-reference to the complex-
  logarithm chapter becomes a descriptive phrase. Reveals cover
  `IsEvenlyCovered`/`IsCoveringMap`, path lifting
  (`IsCoveringMap.liftPath`/`liftPath_lifts`/`liftPath_zero`), the general
  lifting criterion (`existsUnique_continuousMap_lifts` with
  `LocPathConnectedSpace`), homotopy lifting (`liftHomotopy`), and regular
  coverings (`IsQuotientCoveringMap`).

### Category Theory

- **Objects and morphisms** and the first two sections of **Functors
  and natural transformations** were ported in an earlier pass; the
  remaining functor sections and the two following chapters are new
  here.
- **Functors and natural transformations.** The remaining sections
  ("indexed family of objects", "contravariant functors", "equivalence
  of categories", "natural transformations", "the Yoneda lemma") are
  ported. The large Asymptote picture of a natural transformation
  dragging one functor's image onto another's is omitted, its content
  absorbed into the surrounding prose. All TikZ commutative diagrams
  become prose or inline arrows. Upstream's "Equivalence of categories"
  is only a `\todo{fully faithful and essentially surjective}` stub;
  it is **newly written** as a short section stating the definition and
  the fully-faithful-plus-essentially-surjective criterion. Cross-refs
  to the double-dual problem and the Hurewicz remark become descriptive
  phrases. Reveals cover the product category `C × D` and `Discrete`,
  `Functor.op`/`yoneda`/`coyoneda`, `Equivalence`/`Functor.FullyFaithful`
  /`Functor.EssSurj`, `NatTrans`/`NatIso.ofComponents`, and the Yoneda
  lemma (`yonedaEquiv`, `yonedaLemma`, `Yoneda.fullyFaithful`).
- **Limits in categories.** Upstream is an explicitly incomplete
  chapter (its title carries "(TO DO)", the pullback section is a
  `\todo{write me}` stub, and it trails off in author notes-to-self).
  The port keeps the complete Equalizers section verbatim, writes a
  short self-contained **Pullback squares** section over the stub
  (keeping upstream's differentiable-functions example), and ports the
  brief Limits section; the stray trailing notes ("pushout square gives
  tensor product", "p-adic", "relative Chinese remainder theorem") are
  dropped as they are not content. All fork/cone TikZ diagrams become
  prose. Reveals cover `Limits.Fork`/`equalizer`/`HasEqualizer`,
  `Limits.pullback`/`HasPullback`, and `Limits.Cone`/`IsLimit`/`limit`
  /`HasLimit`.
- **Abelian categories.** All TikZ diagrams (the kernel/cokernel/image
  factorizations, the exact-sequence splicing, and the five-/four-
  /snake-lemma squares) become prose or inline sequences. The nested
  block quote from Aluffi on diagram chasing is **summarized in prose**
  rather than reproduced verbatim. Several `\Cref` cross-references
  (rank-nullity, the equalizer-monic problem, PairTop) become
  descriptive phrases. Reveals cover `HasZeroObject`/`HasZeroMorphisms`,
  `Limits.kernel`/`cokernel`, `Abelian.image`, `Preadditive`/`Abelian`,
  `ShortComplex`/`.Exact`/`.ShortExact`, and `Abelian.Pseudoelement` for
  diagram chasing; an aside notes the Freyd–Mitchell embedding theorem
  is not in Mathlib, though pseudoelements recover its practical payoff.

### Algebraic Topology II: Homology

- **Singular homology.** All Asymptote art (the singular-simplex,
  annulus-cycle, boundary-in-$S^1$, and prism-operator figures) is
  omitted with prose adjusted; footnotes become `{margin}[…]` notes;
  cross-references (Hurewicz, the figure-eight example, the torus
  homology proposition) become descriptive phrases. Inline hints stay
  as "(Hint: …)" parentheticals and the two problems keep their
  upstream statements. Reveals cover the topological simplex
  (`SimplexCategory.toTop`), the singular simplicial set
  (`TopCat.toSSet`), the singular chain complex and its $H_n$
  (`singularChainComplexFunctor`, `singularHomologyFunctor`), the
  abstract `HomologicalComplex`/`ChainComplex` with `d_comp_d` for
  $\partial^2 = 0$, and chain homotopy (`Homotopy`).
- **The long exact sequence.** Figures/diagrams omitted; the snake-lemma
  and connecting-map discussion is ported in prose. Reveals cover
  `CategoryTheory.ShortComplex`, `.Exact`, `.ShortExact`, and
  `.Splitting`.
- **Excision and relative homology.** Figures omitted, cross-references
  to the good-pair theorem and triple sequence become descriptive
  phrases. Relative/reduced singular homology, the category of pairs,
  excision, and deformation retracts are honestly flagged as **not
  present in Mathlib** (prose asides, no invented names).
- **Cellular homology.** Upstream's "Bonus:" title prefix becomes a
  one-line "this is a bonus chapter" note; figures omitted. Cellular
  homology, degree, Euler characteristic, and Betti numbers are flagged
  as absent from Mathlib; `Topology.CWComplex` (which does exist) is
  cited for the underlying complexes.
- **Singular cohomology.** Figures omitted. Reveals cover
  `CochainComplex`/`HomologicalComplex.homology`; the universal
  coefficient theorem and the elementary one-step `Ext` recipe are
  flagged as absent (a note distinguishes Mathlib's derived-category
  `Ext`).
- **Application of cohomology (cup products).** Figures omitted. The
  cohomology ring, cup product on singular cohomology, Poincaré
  duality, and Künneth are flagged as absent from Mathlib; the graded/
  anticommutative-ring backdrop is illustrated with `GradedRing` and
  `ExteriorAlgebra`, which do exist. Incidental solution-only citations
  (`ref:maxim752`) were dropped.

### Algebraic Geometry I: Classical Varieties

- **Affine varieties.** All figures (the parabola, the $\mathbb{A}^1$/
  $\mathbb{A}^2$ sketches, the double-point) omitted; the "flavors of
  ideals" table rendered as a prose list; footnotes → parentheticals/
  margin; `\Cref`s → descriptive phrases. Problems ported with hints
  inlined and solutions deferred. Reveals cover
  `MvPolynomial.zeroLocus`/`vanishingIdeal`, the Nullstellensatz
  (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, over an
  algebraically closed field in finitely many variables) and its Galois
  connection, `Ideal.span`/`radical`/`IsRadical`, `IsNoetherianRing`,
  `Ideal.IsPrime`/`IsMaximal`, and `PrimeSpectrum`.
- **Affine varieties as ringed spaces.** Figures omitted; problems
  ported. Reveals cover `PrimeSpectrum.zariskiTopology`/`zeroLocus`/
  `basicOpen`, `IsLocalization.Away`, and `AlgebraicGeometry.RingedSpace`.
- **Projective varieties.** Figures (cone, conic) omitted. Upstream has
  only a `\todo` for problems, so the port has no Problems section (not
  a content deviation). Reveals cover `GradedRing`,
  `Ideal.IsHomogeneous`/`HomogeneousIdeal`, `ProjectiveSpectrum`, and
  `HomogeneousLocalization`.
- **Bézout's theorem** (kept as a bonus chapter). SES diagrams rendered
  as prose; Pascal/parabola figures omitted; two problems ported (hints
  inlined). Classical projective Bézout, the degree of a projective
  variety, and Pascal's theorem are flagged as **absent from Mathlib**,
  with an explicit warning that Mathlib's `IsBezout` means the unrelated
  "Bézout domain"; `Polynomial.hilbertPoly` and
  `ShortComplex.ShortExact` are cited where they do apply.
- **Morphisms of varieties.** Figures omitted; four problems ported
  (hints inlined). Reveals cover `AlgebraicGeometry.LocallyRingedSpace`,
  `AffineScheme`, `Scheme.Opens`, and `IsAffineOpen`; an aside notes
  Mathlib has no separate quasi-projective-variety type and works with
  open subschemes instead.

### Algebraic Geometry II: Affine Schemes

- **Sheaves and ringed spaces.** Section/germ figures omitted; the
  categorical pullback-square and colimit remarks ported as prose; one
  footnote inlined. Reveals cover `TopCat.Presheaf`/`Sheaf`,
  `TopCat.Presheaf.stalk`/`germ`, and sheafification
  (`sheafify`/`toSheafify`/`stalkToFiber`), with a buildable
  presheaf-as-functor block.
- **Localization.** Cross-references become descriptive phrases.
  Reveals cover `Submonoid`, `Localization`/`IsLocalization`,
  `Localization.Away`/`AtPrime`, `FractionRing`/`IsFractionRing`,
  `IsLocalization.orderIsoOfPrime`, and `Ideal.comap`/`map`.
- **Affine schemes: the Zariski topology.** The Calvin-and-Hobbes and
  parabola figures omitted; the post-`\endinput` Critch problem is
  correctly excluded. Reveals cover `PrimeSpectrum` with
  `zeroLocus`/`vanishingIdeal`, `isClosed_singleton_iff_isMaximal`,
  `isIrreducible_iff_vanishingIdeal_isPrime`, and Krull dimension
  (`ringKrullDim`/`topologicalKrullDim`).
- **Affine schemes: the sheaf.** A Vakil footnote becomes a
  `{cite}`ref:vakil`` margin note. Reveals cover
  `AlgebraicGeometry.Spec.structureSheaf`,
  `StructureSheaf.globalSectionsIso`, `PrimeSpectrum.basicOpen`,
  `Localization.AtPrime`, and `IsLocalRing`/`ResidueField` (with a
  buildable local-ring instance block).
- **Eighteen examples of affine schemes** (interlude). All 18 figures
  (including the Mumford raster) omitted; section headers containing
  `[…]`/`_` are escaped so Verso does not read them as markup. One
  orienting aside; the rest are worked examples.
- **Morphisms of locally ringed spaces.** Ported through the upstream
  `\endinput` (the later projective-scheme and morphisms-of-sheaves
  sections are excluded upstream); a MathOverflow quote is dropped;
  figures omitted; two problems ported (hints inlined). Reveals cover
  `AlgebraicGeometry.Scheme`/`Scheme.Hom`/`stalkMap`,
  `LocallyRingedSpace`, `IsLocalHom`, and `Spec`/`Spec.map` (buildable
  `noncomputable` blocks).

### Set Theory I: ZFC, Ordinals, and Cardinals

Per the book-wide types-not-sets exception, this part models sets *as*
sets (`ZFSet`/`Class`), since sets are the actual subject.

- **Cauchy's functional equation and Zorn's lemma** (the interlude).
  Figures (apples, the "zornaholic" cartoon) omitted; problems ported
  with hints inlined. Reveals cover `zorn_le`/`zorn_subset`, `IsMax`,
  and the Hamel-basis existence (`Module.Basis.ofVectorSpace` via
  `LinearIndependent`).
- **Zermelo–Fraenkel with choice.** The universe-triangle figure and
  the Cantor-diagonal table are rendered in prose; footnotes →
  `{margin}[…]`; cross-references become descriptive phrases. Reveals
  cover `ZFSet` with its axiom-operations (`empty`/`pair`/`sUnion`/
  `powerset`/`sep`/`image`/`omega`), `Class`, Cantor's theorem
  (`Function.cantor_injective`/`cantor_surjective`, with a buildable
  block), and `WellOrderingRel`/`IsWellOrder`.
- **Ordinals.** The ω-spiral figure omitted. An aside notes Mathlib
  defines `Ordinal` as order-isomorphism classes of well-orders rather
  than as transitive ∈-sets, with `ZFSet.rank` and `ZFSet.vonNeumann`
  as the ∈-set bridge; ordinal exponentiation is discussed via `opow`
  (there is no bare `Ordinal.opow` constant). Reveals also cover
  `Ordinal.omega0`, `Order.IsSuccLimit`, and `Ordinal.limitRecOn`.
- **Cardinals.** Equinumerosity and cardinal-squaring tables rendered
  as prose. Reveals cover `Cardinal.mk`/`aleph`/`aleph0`, Cantor
  (`Cardinal.cantor`), cardinal arithmetic collapse
  (`Cardinal.mul_eq_self`/`mul_eq_max`/`add_eq_max`), cofinality
  (`Ordinal.cof`), and `Cardinal.IsRegular`/`IsInaccessible`. The one
  `\sproblem` is rendered as a plain problem per the starred-problem
  convention.

### Set Theory II: Model Theory and Forcing

Sets are modeled as sets throughout, per the set-theory exception.

- **Inner model theory.** The two universe-diagram figures omitted;
  footnotes → `{margin}[…]`; `\Cref`s → descriptive phrases; the
  ZFC-axiom macros spelled out ("Empty Set", "Power Set", …); three
  problems ported with hints inlined. Reveals cover Mathlib's
  first-order logic: `FirstOrder.Language`/`Structure`/`Sentence`
  (with `Sentence.Realize`, `M ⊨ φ`), `Theory`/`Theory.Model`,
  `ElementarySubstructure`/`ElementarilyEquivalent`/`ElementaryEmbedding`,
  and downward Löwenheim–Skolem
  (`FirstOrder.Language.exists_elementaryEmbedding_card_eq`). Transitive/
  inner models of ZFC, absoluteness, the Levy hierarchy, Mostowski
  collapse, reflection, and Replacement-as-a-schema are flagged as
  **absent from Mathlib** (honest prose asides).
- **Forcing.** Binary-tree/universe figures omitted; two problems
  ported (Rasiowa–Sikorski hint inlined). Only the poset scaffolding
  (`PartialOrder`, order density/bounds) is cited; generic filters,
  $\mathbb{P}$-names, $M[G]$, and the forcing relation are flagged as
  **entirely beyond Mathlib**.
- **Breaking the continuum hypothesis.** The `Add(ω, ω₂)`/binary-tree
  figures omitted; the commented-out `V ≠ L` section is left out (it is
  commented out upstream); one problem ported with hint inlined. The
  cardinal-arithmetic backdrop cites `Cardinal.aleph`, `Ordinal.cof`,
  and `Cardinal.IsRegular`; the forcing-based independence of CH,
  cardinal collapse, ccc-preservation, and the constructible universe
  $L$ are flagged as absent from Mathlib.

### Backmatter

- **References** is an auto-generated bibliography; upstream's
  per-topic "Pedagogical comments and references" prose is not yet
  ported.
- **Glossary of notations** is ported verbatim as a reference list.
  Custom upstream macros are rewritten into KaTeX-safe forms: bra–ket
  notation becomes `\langle`/`\rangle` (the `\ket`/`\bra` macros are
  not available), spin states are spelled with arrows, cyclic groups
  become `\mathbb{Z}/n\mathbb{Z}` and units `(\mathbb{Z}/n\mathbb{Z})^\times`,
  and fraktur ideals/sheaves use `\mathfrak{…}`/`\mathcal{…}`. Being a
  glossary, it carries no formalization asides. It still lists notation
  from not-yet-ported chapters (set theory, algebraic geometry), as a
  glossary should.
- **Terminology on sets and functions.** Ported verbatim; the
  cross-reference to the ZFC chapter becomes a descriptive phrase.
  This is prerequisite set/function vocabulary, so it stays in the
  language of sets (not the book-wide types convention). Asides connect
  each notion to its Mathlib counterpart: `Set`/`∈`/`⊆`/`𝒫`, the
  `∪`/`∩`/`\` operations, `Function.Injective`/`Surjective`/`Bijective`,
  `Equiv` for bijections, `Set.image`/`Set.preimage`, and
  `Setoid`/`Quotient` with `Setoid.IsPartition`.

### Hints and Solutions

- Upstream's two separate backmatter appendices ("Hints to selected
  problems" and "Sketches of selected solutions", both flat lists keyed
  by a global problem number) are **merged into one "Hints and
  Solutions" part**, organized by chapter, with each problem's hint and
  solution shown together. The port has no global problem numbering, so
  entries are keyed by a short problem descriptor (reusing the ported
  chapter's `:::PROBLEM` title where it has one) instead of a number.
- For build hygiene the part is split across five files by book area
  (`Napkin/Backmatter/Solutions/`), covering ~226 problem entries
  (~228 hints and ~136 solutions in the source). Chapters with no
  `\begin{hint}`/`\begin{sol}` blocks are simply absent.
- All hint/solution prose is ported verbatim and rewritten KaTeX-safe
  (custom macros expanded, kets spelled with `\langle`/`\rangle`,
  `align*` → `aligned`); `\Cref`s become descriptive phrases, `\url`/
  `\href` become Markdown links, figures/tikz diagrams are dropped or
  replaced by a prose sentence, and a few digressive footnotes become
  `{margin}[…]` notes.
- The `frobenius` and `artin` source chapters (both ported into
  `FrobeniusElements.lean`) have their problems collected under one
  "The Frobenius element" header. Problems sitting after an upstream
  `\endinput`, and one entirely commented-out problem, are excluded.
- **Silent typo fix** (per convention 11): in the large-numbers
  "quantifier hell" solution, the final displayed limit read `= 1` in
  the source where the almost-sure limit is the random variable's
  value; corrected to `= 0`.

## Unported content

The port is now content-complete: every chapter of the book, the
notation and sets-and-functions appendices, and the merged hints/
solutions appendix are all ported and building. The one small piece not
yet carried over is upstream's per-topic "Pedagogical comments and
references" prose in the References appendix (noted under Backmatter).
