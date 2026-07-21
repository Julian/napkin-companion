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

4. **Figures.** Upstream Asymptote/tikz art is redrawn as SVG (with
   captions written for this edition), and externally-sourced raster
   images (photos, comics, Wikimedia diagrams) are vendored into
   `media/` and served via `Render.lean`'s `extraFiles`, with the
   upstream "Image from …" attributions preserved as `{cite}` captions.
   Evan's own 3D-rendered PDF figures are converted to SVG under
   `figures/`. Every upstream figure is now shown; the only figures
   drawn differently from upstream are Asymptote/tikz pictures redrawn as
   SVG (functionally identical, captions rewritten for this edition),
   itemized per chapter below.

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

12. **The `Napkin.Missing` layer.** Where a chapter introduces a
    mathematical object Mathlib has no definition for, the Lean
    companion does not stop at a prose note: the object is defined —
    as faithfully to the chapter's definition as Lean allows — under
    `Napkin/Missing/`, and the companion's worked models and exercises
    are built on it. These are stopgaps: each definition carries a
    doc-string line beginning `Not in Mathlib.` naming the upstream
    object to watch for, so `grep -rn "Not in Mathlib." Napkin/Missing`
    enumerates every one. When Mathlib gains the real object, delete the
    stopgap and repoint the chapter. Deep *theorems* with no
    constructible content (Riemann–Roch, projective Bézout, excision,
    Chebotarev, Artin reciprocity, Riemann–Hurwitz, …) are bundled as
    "statement-as-structure" `*Data` records so their consequences stay
    derivable even though the theorem itself is assumed; this is flagged
    in each such definition's doc-string.

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
  inverse-limit-first construction. The chapter's inverse limit
  $\varprojlim \mathbb{Z}/p^n\mathbb{Z}$ is defined as a genuine object
  in `Napkin.Missing.PadicInverseLimit`, with an injective bridge from
  Mathlib's `ℤ_[p]`.
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
  Lisa, who finally got me to write it.") is now restored in its
  original position (between the Ko-fi block and the copyright line).
- **Preface** is verbatim; it adds one sentence directing
  companion-specific errata to this repository.
- **Advice** is verbatim (the "ring naming" table, the reading-order
  advice, and all margin-note footnotes match), with one medium
  adaptation: upstream's "the length of the entire PDF" becomes "the
  length of the entire book" (this rendering is a web book, not a PDF).
  It also replaces the LaTeX dependency digraph with a regenerated
  clickable SVG chapter graph.
- **Sales pitches** is verbatim (all six section pitches match
  sentence-for-sentence; `g ∈ G` → `g : G` per the types-not-sets
  convention).

### Starting Out

- **Groups.** Prose is verbatim (the group definition with its
  identity/associativity/inverse axioms, the pedantic-point and
  abelian remarks, the examples and non-examples), modulo the
  book-wide types-not-sets convention. The D₁₀ art is redrawn as SVG
  with a new caption. Two parenthetical pointers to the sets-and-
  functions appendix are dropped (the appendix is not yet ported). The
  forward reference to Lagrange becomes "we'll prove it later in more
  generality". The trailing "Formalities" section is companion-only
  content.
- **Metric spaces.** Prose is verbatim (the point-set-topology
  motivation and the metric-space definition, modulo types-not-sets).
  Four figures redrawn as SVG with new captions.
  One bridging sentence to an unported problem dropped. A margin note
  is imported from a footnote in a different upstream chapter
  (metric-prop.tex) where it fit naturally.

### Basic Abstract Algebra

- **Quotients.** Prose is verbatim (the generators/"put x in a box"
  motivation, the generated-subgroup definition, and onward through
  homomorphisms and quotient groups), modulo types-not-sets. The
  cosets/fibers picture is recreated as SVG with a new caption.
- **Rings.** Verbatim modulo conventions (the rings-vs-groups metaphors
  and analogy table, the ring definition and its axioms, the examples).
- **Flavors.** Prose is verbatim (the flavors-of-rings overview and its
  completed analogy table, the fields/integral-domains/PID/Noetherian
  definitions), modulo types-not-sets. The ℤ[i] lattice-rounding figure,
  the ℤ[√11] hyperbola figure, and both side-divisor lattice figures are
  redrawn as SVG. The contributed section's non-native English is lightly
  copy-edited.

### Basic Topology

- **Metric properties.** Prose is verbatim (the open/closed opening,
  the boundedness/completeness definitions). The $[0,1]^2$ covering
  figure is redrawn as SVG with a new caption. The Makholm problem's
  yes/no table is rendered as prose, with the math.SE attribution moved
  into the body.
- **Topological spaces.** Prose is verbatim (the "forgetting the
  metric" opening, the re-definitions, and the Hausdorff section's
  metrizability/separation-axiom exposition all match upstream, with
  `\Cref`s → descriptive phrases and the footnote → `{margin}`).
  All of the chapter's figures — the open-neighborhood, Hausdorff, and
  subspace sketches together with the path and homotopy-motivation
  figures — are redrawn as SVG with new captions; the sentence
  motivating connectedness via the $\{0,1\}$-valued map problem dropped.
- **Compactness.** Prose is verbatim (the sequential/open-cover
  motivation, the subsequence definition). All three figures (the
  Hawaiian earring, the open cover, and the $[0,1]^2$ subdivision) are
  redrawn as SVG with new captions. Upstream's "Proof using covers" /
  "Proof using sequences" headers are currently untitled PROOF blocks.

### Linear Algebra

- **Vector spaces.** Prose is verbatim (the "pretty light chapter"
  opening, the informal ring/field/abelian-group definitions, the
  modules-and-vector-spaces exposition), modulo types-not-sets. The
  linear-map cartoon is redrawn as SVG and the matrix-multiplication
  picture is restored as a vendored raster; other pictorial matrix
  displays are rendered as arrays. Hints are inlined as parentheticals.
- **Eigen-things.** Prose is verbatim (the "why you should care"
  motivation, the "getting lucky" example, the Jordan-canonical-form
  theorem and its block-diagonal example), and all fifteen matrix
  displays match upstream (an earlier note claiming Jordan displays were
  condensed / two block matrices omitted was itself stale — none are).
  The cross-referenced problem is given the coined name "the eventual-
  kernel-image splitting".
- **Dual space and trace.** Prose is verbatim (the high-school
  trace/determinant motivation, the intrinsic-trace goal, the
  tensor-product and dual-space introduction). Two intermediate
  computation displays condensed.
- **Determinant.** Prose is verbatim (the basis-free-determinant goal,
  the finite-dimensionality note, the wedge-product definition and its
  relations). The parallelogram-area figure is redrawn as SVG; one
  expanded determinant display condensed; one problem retitled.
- **Inner product spaces.** Prose is verbatim (the inner-form/dot-
  product motivation, the orthogonality/distance bullets, the
  chapter-highlights list, and the "all vector spaces over ℂ or ℝ"
  convention). Two "abbreviated in the literature" sentences and two
  intermediate Cauchy-Schwarz displays condensed.
- **Fourier analysis (bonus).** Prose is verbatim (the bonus-chapter
  framing, the circle-group $\mathbb{T} = \mathbb{R}/\mathbb{Z}$ setup,
  and the canonical map $e$), with the `AddCircle` reveal inline. The
  solution to the final problem (the exact-probability lemma behind
  Arrow) awaits the hints/solutions backmatter, per the book-wide
  convention. Upstream's multi-line `align` chains are split into
  consecutive displayed equations.
- **Adjoints.** Prose is verbatim (the basis-free transpose framing,
  the poster corollary, the dual-map definition). Several optional
  proofs are condensed or omitted (row rank = column rank; the full
  matrix proof of the conjugate-transpose identity; normal ⟺
  orthonormally diagonalizable), keeping the one-line versions upstream
  also gives. Two upstream typos fixed ($T^\vee \to T^\dagger$; basis
  for $V$ → basis for $W$). Upstream's $T^\dagger$-vs-$T^\vee$ `tikzcd`
  square is redrawn as an SVG (`transpose-square`).

### More on Groups

- **Group actions.** Prose is verbatim (the AIME-1996 motivation, the
  group-action definition and its two axioms), modulo types-not-sets;
  the `MulAction` reveal is inline. The orbits-partition and orbit-
  stabilizer figures are redrawn as SVG.
- **Find all groups (Sylow).** Verbatim (the "Find all groups" opening
  problem and the Sylow-theorems statement match upstream); the only
  upstream image is commented out in the source, so nothing is omitted.
- **Structure theorem.** Prose is verbatim (the classification-theorem
  overview and corollaries, the finitely-generated definition and the
  free-module reduction), modulo types-not-sets. Upstream's
  $R^{\oplus f} \to R^{\oplus d} \to M$ `tikzcd` diagram is redrawn as
  an SVG (`cokernel-diagram`), with the composition also stated inline.
  Seven build-verified formalization reveals were added, matching each
  theorem to Mathlib: `AddCommGroup.equiv_free_prod_directSum_zmod`
  (f.g. abelian groups), the `PrincipalIdealRing.isNoetherianRing` /
  `UniqueFactorizationMonoid` instances (PIDs are Noetherian UFDs),
  `ZMod.chineseRemainder` (CRT), `isNoetherian_def`,
  `Module.equiv_free_prod_directSum` (the PID structure theorem),
  `Module.finrank_eq_card_basis` (rank invariance), and
  `Submodule.smithNormalForm` (Smith normal form).

### Representation Theory

- **Representations of algebras.** Verbatim (the "in the 19th century
  the word 'group' hadn't been invented yet" opening and the
  representation-theory-of-groups motivation); upstream's two `tikzcd`
  diagrams are rendered inline.
- **Semisimple.** Prose is verbatim (the "assume $k$ is algebraically
  closed" opening and the irreducible/completely-reducible motivation).
  Upstream's "inclusion to the $j$th component" is corrected to
  *projection*. Two commutative diagrams rendered as prose. Four
  build-verified formalization reveals were added: Schur via
  `LinearMap.bijective_or_eq_zero` and
  `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`,
  Artin–Wedderburn `isSemisimpleRing_iff_pi_matrix_divisionRing`, and the
  `IsSemisimpleRing (MonoidAlgebra k G)` instance (Maschke).
- **Characters.** Prose is verbatim (the "characters are basically the
  best thing ever" opening and the character $\chi_V = \mathrm{Tr}\circ
  \rho$ definition). Upstream's character "attached to $A$" corrected to
  "attached to $V$"; the "mysterious properties" renumbered (I)–(IV) →
  1–4. Eight build-verified formalization reveals were added:
  `FDRep.character`, `char_one`, `char_mul_comm`/`char_conj`,
  `char_tensor`/`char_dual`, and the orthogonality lemmas
  `char_orthonormal`/`scalar_product_char_eq_finrank_equivariant`.
- **Some applications.** Verbatim (the "with all this setup … results
  of independent interest" opening and the Frobenius-divisibility
  theorem statement). Three build-verified formalization reveals were
  added: `IsIntegrallyClosed ℤ` for the $\overline{\mathbb{Z}} \cap
  \mathbb{Q} = \mathbb{Z}$ fact, `IsIntegral.of_finite` for the "elements
  of $\mathbb{Z}[G]$ are integral" lemma, and
  `FDRep.finrank_hom_simple_simple` (Schur's lemma) for the intertwiner-
  is-a-scalar step. The capstone theorems themselves (Frobenius
  divisibility, Burnside's $p^aq^b$, Frobenius determinant) are not in
  Mathlib, so only their ingredients are pointed to.

### Quantum Algorithms

- **Circuits.** Prose is verbatim (the "now that we've discussed qubits
  … allowing linear combinations of 0 and 1" opening and the
  classical-logic-gates section). All ~20 upstream Qcircuit gate/wire
  schematics are redrawn as figures: the `Qcircuit` source was ported to
  `quantikz` (`figures/quantum/*.tex` → SVG via the usual pipeline) and
  reinstated in the original page positions, with the surrounding prose
  restored verbatim ("It is depicted as follows.", "So pictorially, the
  quantum CNOT gate is given by", "Picture:", "Thus, the picture so far
  is:", etc.). The upstream truth tables remain as `array` tables (they
  are `array`s, not `Qcircuit`, upstream too). New body material connects
  the gates to `Matrix.unitaryGroup`. An aside acknowledges the
  query-complexity content of Deutsch–Jozsa has no Mathlib formalization.
- **Shor.** Both QFT circuit diagrams (the concrete $n=3$ circuit and the
  general-$n$ inductive schematic) are redrawn from the upstream
  `Qcircuit` source into `quantikz` figures
  (`figures/quantum/shor-qft{,-general}.svg`) in their original
  positions, with the verbatim lead-ins restored ("Then, for $n=3$ the
  circuit is given by using controlled $R_k$'s as follows:", "For general
  $n$, we can write this as inductively as"). An aside notes Mathlib has
  no named discrete Fourier transform on tuples (the `ZMod N` one exists).

### Calculus 101

- **Limits.** Prose is verbatim (completeness, inf/sup, the "why is
  max not good enough" motivation, the Supremums list — upstream's "has
  not bounded above" is even preserved), with the completeness/`sSup`/
  `Monotone`/`atTop`/geometric-series reveals kept inline as first-class
  reveals (the port's dominant convention). Two number-line figures
  redrawn as SVG.
- **p-adics.** Prose is verbatim (the bonus-chapter framing, the
  olympiad motivation and the four properties of $\mathbb{Q}_p$), with
  the `ℚ_[p]`/`ℤ_[p]` reveals inline. One footnote and two literature
  citations dropped; the "remark for experts" is promoted to an aside;
  upstream's off-by-one in the geometric series partial sums fixed. An
  aside notes Strassmann and Skolem–Mahler–Lech are not in Mathlib.
- **Differentiation.** All five figures are included: the four
  Asymptote pictures are redrawn as SVG and the xkcd strip is a
  vendored raster (`img:xkcd_rolles`). A new paragraph connects bump
  functions to `Real.smoothTransition` and partitions of unity.
- **Taylor.** Prose is verbatim (the power-series introduction, the
  radius-of-convergence definitions and propositions, the analyticity
  results). Upstream's "It terms out" typo fixed. A parenthetical
  notes the $|h| = R$ boundary case is intentionally ambiguous.
- **Integration.** Prose is verbatim (the Gaitsgory epigraph, the
  uniform-continuity definition and its "this difference is that…"
  explanation, the failure examples), with `UniformContinuous` and the
  other reveals inline; a port-added two-sentence bridge before the
  uniform-continuity definition was removed to match upstream's flow.
  Both commutative diagrams and the four figures are redrawn as SVG.

### Complex Analysis

- **Holomorphic functions.** Prose is verbatim (the "$U$ open / $\Omega$
  simply connected" setup, the "nicest functions on earth" section, and
  the real-vs-complex-analysis motivation). All eight of the chapter's
  Asymptote figures are redrawn as SVG, and the Weierstrass-function
  image (`img:weierstrass`) is included as a vendored raster. The
  optional section proving holomorphic ⟹ analytic is not yet ported.
- **Meromorphic functions.** Prose is verbatim (the "second nicest
  functions on earth" opening, the $A/B$ definition, the $1/z$ example,
  and the almost-holomorphic/poles discussion). The $z^3$ winding figure
  redrawn as SVG; two footnotes dropped. Five build-verified
  formalization reveals were added (`MeromorphicAt`, `meromorphicOrderAt`
  and `meromorphicOrderAt_mul`, the fundamental theorem of algebra via
  `Complex.exists_root`/`Complex.isAlgClosed`, and the maximum-modulus
  principle `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`).
  **Correction:** an earlier pass's formalization *commentary* named
  several Mathlib lemmas that do not exist (`MeromorphicAt.order`,
  `Function.Meromorphic.residue`, `MeromorphicOn.residueTheorem`,
  `Complex.windingNumber`, `Complex.argumentPrinciple`, `Complex.rouche`,
  `MeromorphicAt.order_logDeriv`, and a wrong open-mapping name); these
  were corrected to the real names where one exists (`meromorphicOrderAt`,
  `AnalyticOnNhd.is_constant_or_isOpen`) and otherwise rewritten to state
  honestly that Mathlib lacks residues, winding numbers, the residue
  theorem, the argument principle, and Rouché's theorem.
- **Log.** Prose is verbatim (the "make sense of a holomorphic square
  root and logarithm" opening — with `\Cref`s → descriptive phrases —
  the $n$th-root/logarithm definitions, and the branch-cut/"ray of
  death" narrative). The four upstream Asymptote $z_i$/$w_i$ monodromy
  point-diagrams are **redrawn as TikZ SVGs** (`log-sqrt-1..4`,
  computed from Evan's asy coordinates), restored to their upstream
  positions with the surrounding figure-referencing prose reverted from
  the earlier descriptive rewrite; both lifting tikz-cds are inlined.
  "Identify them with $S^1$" corrected to "identify their fundamental
  groups with ℤ".
- **Quintic.** Both figures (the two-path root swap and the $\alpha$/
  $\beta$ commutator loops) are redrawn as SVG. Upstream's imprecise
  "solvable" definition is faithfully preserved.

### Measure Theory

- **Measure spaces.** Verbatim (the "here is an outline of where we are
  going… law of large numbers and central limit theorem" opening and
  the measure-spaces/Lebesgue-integral motivation); modulo the
  set-theory-chapter exception, carriers are still discussed as sets
  since measurable sets are the subject.
- **Carathéodory.** Prose is verbatim (the "difficult to define in one
  breath a measure on $\mathcal{B}(\mathbb{R}^n)$" opening and the
  pre-measure/outer-measure weaker-notions setup). The first process
  table drops the "Construct
  order" column; the Cantor middle-thirds image (`img:cantor`) is
  included as a vendored raster, though the unit-disk covering picture
  is still omitted; the proof that Lebesgue is the
  completion of Borel is omitted; the trailing stub section is
  omitted.
- **Lebesgue integration.** Prose is verbatim (the "on any measure
  space we can define an integral $\int_\Omega f\,d\mu$ … this chapter
  will be quite short" opening). Upstream's four titled "step" boxes are
  flattened into running prose.
- **Swap sum.** Prose is verbatim (the "motivating limit interchange"
  opening on the Riemann integral behaving badly with convergence, and
  the $\mathbf{1}_\mathbb{Q}$ example). The "Fubini and Tonelli" section
  and the three end-of-chapter problems are **newly written** — upstream
  has literal `\todo` stubs there.
- **Pontryagin.** Prose is verbatim (the bonus-chapter "generalize our
  Fourier analysis to a wider class of groups" opening and the LCA-
  groups/topological-group definitions). Upstream's DTFT/DFT mix-up
  corrected. The answer to the counting-measure problem is stated inline.

### Probability

Upstream marks this entire part "(TO DO)": every chapter has `\todo`
stubs alongside real content. The port fills the gaps with **newly
written** material (in upstream's style, at comparable length) and
drops the "(TO DO)" from the part, chapter, and sales-pitch titles.

- **Random variables.** The ported "Random variables" section is
  verbatim (the "having properly developed the Lebesgue measure … we
  can now proceed to develop random variables" opening and the
  random-variable definition). Upstream provides only the "Random
  variables" section and the two problems; the sections on distribution
  functions, examples of random variables, characteristic functions,
  and independent random variables are newly written.
- **Large number laws.** The ported content is verbatim (the "notions
  of convergence" section — the almost-sure-convergence definition, the
  "very strong notion … almost every world" gloss, and the immortal-
  skeleton-archer non-example). The "Convergence in law" section, the
  weak law's statement and proof (with Chebyshev's inequality stated
  there rather than in the strong-law section, since upstream's weak-law
  section was empty), the Weierstrass-approximation application, and the
  general-proof sketch are newly written. The upstream title typo
  "convorgence" in the final problem is fixed.
- **Stopped martingales.** The ported "how to make money almost surely"
  opening (the casino coin-flip game with bad odds) is verbatim; the
  newly-written ballot section adds a `ballot-path` SVG illustration.
  Newly written: the properties-of-
  conditional-expectation proposition (upstream `\todo{properties}`),
  the name-etymology aside (upstream `\todo`), the proof of the
  optional stopping theorem (upstream `\todo{do later tonight}`), the
  ABRACADABRA section, and the USA TST 2018 section (both "To be
  written" upstream, keyed off the reference links upstream left).
  The ballot-problem figure (upstream `\missingfigure{path}`) is
  drawn as an SVG.

### Differential Geometry

- **Multivariable calculus.** Prose is verbatim (single-sentence
  Mathlib reveals kept inline as first-class reveals). The high-school
  tangent-line figure is redrawn as a TikZ SVG (`multivar-tangent`), and
  the 3D tangent-plane figure is restored from Evan's `tangent.pdf` as
  SVG (`multivar-tangent-plane`, attribution `img:tangentplane`).
- **Differential forms.** Prose is verbatim (the "pictures of
  differential forms" section, the $0$/$1$/$2$-form definitions, and
  the wedge-product exposition), with the `AlternatingMap`/
  `ExteriorAlgebra` reveal kept in an `:::aside`. The chapter's
  Asymptote pictures are redrawn as SVG and the Stokes-patch image
  (`img:stokes`) is included. Six footnotes dropped, including the
  finite-dimensionality caveat.
- **Stokes.** Prose is verbatim (the line-integral motivation, the
  pullback construction, and the Stokes-theorem statement), with the
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` and
  `AlternatingMap.compLinearMap` reveals kept in `:::aside`s. All five
  figures are present as SVG — both "Picture:" diagrams and the 18.02
  grad/curl/div chart (redrawn as TikZ, `stokes-integral-zoo`). Several
  upstream errors silently fixed (chain integrals, form-degree
  mislabels, the cross-product derivation).
- **Manifolds.** Prose is verbatim (topological/smooth-manifold
  definitions, the Earth/`π₂` motivation, the tangent/cotangent
  construction), with the three multi-paragraph Mathlib reveals
  (`ChartedSpace`, `IsManifold`, `PointDerivation`) kept in `:::aside`s.
  Four figures redrawn as SVG; the π₂(Earth) aside and the historical
  footnote dropped; "level hypersurfaces" promoted from corollary to
  theorem.

### Riemann Surfaces

- **Complex structure.** All five figures are redrawn as SVG (the
  chart-transition, lattice-quotient, open-set, and chart sketches),
  with Evan's Riemann-sphere 3D render (`riemsphere.pdf`) restored as
  SVG. The chapter opening is re-ported to upstream's verbatim wording
  (a light paraphrase was reverted; the compact-Liouville Mathlib reveal
  is moved into an `:::aside`). Upstream's garbled torus sentence
  repaired.
- **Morphisms.** The smooth-manifold counterexample figure is restored
  from Evan's `morphism-scm-counterexample.pdf` (converted to SVG), and
  the example's fiber-count list (points $A$–$D$) is restored verbatim.
  The prose body is re-ported to upstream's verbatim wording (the two
  Mathlib reveals — `MDifferentiable`, `MeromorphicAt` — are moved into
  `:::aside`s). The **Hurwitz formula section is newly written** —
  upstream is an empty `\todo`.
- **Affine and projective varieties.** The chapter's figures are redrawn
  as SVG, and Evan's 3D Riemann-surface renders (`parabola.pdf`,
  `circle.pdf`) are restored as SVG alongside the 2D real-part sketches.
  The whole prose body — chapter intro, "Affine plane curves",
  "The projective line ℂP¹", and "Projective plane curves", together
  with all six worked examples (parabola, circle, elliptic, Riemann
  sphere, elliptic-again, hyperelliptic), the definitions, questions and
  exercises — has been **re-ported to upstream's verbatim wording** (an
  earlier pass had paraphrased it). Footnotes become `{margin}` notes and
  the Mathlib `Projectivization`/`IsHomogeneous` reveals are moved into
  `:::aside`s so the body reads verbatim. Only "Filling in the holes" and
  "Nodes of a plane curve" remain **newly written**, since upstream has
  just empty `\todo` stubs there.
- **Differential forms.** The prose body (the $1$-form definition, the
  visualization section, and the $dz$ / $d(z^2)$ / $d\overline z$
  examples) is verbatim; the `Complex.reCLM`/`imCLM` reveal is moved
  into an `:::aside`. The final section ("Putting the pieces together:
  1-forms on a Riemann surface") is **newly written** over upstream's
  one-sentence `\todo{write this}` stub. All four asy quiver figures are
  redrawn as TikZ SVGs. An aside notes manifold-level differential forms
  and holomorphic forms are absent from Mathlib.
- **Riemann–Roch.** The Motivation section, the order/divisor
  definitions, and the worked $L(4\cdot\infty)$ example are verbatim,
  with the three `meromorphicOrderAt`/`locallyFinsuppWithin`/
  `MeromorphicOn.divisor` reveals kept in `:::aside`s. The
  canonical-divisor passage and the applications list are **newly
  written** over upstream `\todo` stubs. Upstream's internally
  inconsistent "More complicated L(−)
  spaces" example is corrected (pole orders and dimension count made
  consistent with its own setup); "Riemann manifold" → "Riemann
  surface". Reveals use `meromorphicOrderAt` and
  `MeromorphicOn.divisor` (with the caveat the latter currently only
  covers subsets of ℂ); an aside notes Riemann–Roch itself is not in
  Mathlib.
- **Line bundles.** The prose body (Overview, the line-bundle and
  section definitions, the Warning remark, and the visualization
  sections) is verbatim, with the two `Trivialization`/`VectorBundle`
  and `CommRing.Pic` reveals kept in `:::aside`s. The final section
  ("Relation to invertible sheaves") is **newly written** over
  upstream's `\todo` stub, framed as a preview since sheaves come later.
  All nine 2D asy figures are redrawn as TikZ; the four 3D figures are
  converted from the vendored `book/3dfigures` PDFs as static SVGs.
  Upstream's "$U_1 \times U_2$" typo in the line-bundle definition is
  corrected
  to $U_1 \cap U_2$. Reveals connect to `Trivialization` /
  `VectorBundle` (noting Mathlib's base-first product convention) and
  `CommRing.Pic` / `ClassGroup.equivPic`; asides note holomorphic
  bundles are not in Mathlib.

### Algebraic NT I: Rings of Integers

- **Algebraic integers.** `\cite{ref:oggier_NT}` becomes a prose
  mention (key absent from the bibliography); "my blog" → "Evan's
  blog"; the blog URL moves to a margin note.
- **The ring of integers.** Prose is verbatim (the norms/traces
  section — the olympiad-norm motivation, the conjugate definition, the
  irreducible-distinct-roots lemma — and onward). The two `subproof`
  environments are rendered as italic run-in headers within one PROOF
  block; the remark title "What went wrong with $\mathcal{O}_K$?" is
  de-symbolized. Upstream's grammatical quirks are preserved.
- **Unique factorization.** Prose is verbatim (the "Took long enough"
  opening and the ideals-as-generalized-GCD motivation, the ℤ[√−5]
  factorization examples), modulo types-not-sets for genuine ideal
  membership. "the only case we'll use in Napkin" → "in this book";
  `\cite{ref:ullery}` becomes a prose mention; one sentence pointing at
  a problem in an unported chapter is reworded to stand alone; two
  footnotes become margin notes.
- **Minkowski bound and class groups.** Prose is verbatim (the
  "neat theory of unique factorization … Sweet" opening, the
  class-group-as-distance-from-PID framing, and the Minkowski-theorem
  overview). All seven asy lattice/region figures are redrawn as TikZ
  SVGs; the tikzcd "ingredients" diagram becomes a table plus prose.
  Upstream's garbled
  "$id(\kb) \mid (n)$" is corrected to $\mathfrak{b} \mid (n)$; one
  section header is de-symbolized; two upstream-untitled lemmas gain
  short titles; four footnotes become margin notes.
- **More properties of the discriminant.** Prose is verbatim (the
  discriminant reminder-formula and the problem statements). Ported as
  the reminder-plus-problems chapter it is upstream; one added
  orientation paragraph notes that two of the problems are Mathlib's
  definitions (`Algebra.discr_def`, `Algebra.discr_powerBasis_eq_prod`).
- **Pell's equation.** Prose is verbatim (the optional-aside framing,
  the Units section, the unit-group/`O_K^×` definitions). Both display
  tables become Markdown tables; upstream's quirks (including the
  Hastings quotation as printed) preserved. Reveals connect to
  `Pell.Solution₁` / `Pell.IsFundamental` and `NumberField.Units`
  (Dirichlet), noting Mathlib covers the norm $+1$ equation only.

### Algebraic NT II: Galois and Ramification Theory

- **Things Galois.** Prose is verbatim (the embeddings motivation and
  the embedding definition). The two embedding-tower diagrams and the
  two field/subgroup lattice diagrams are redrawn as SVGs (the latter
  combined into one side-by-side Galois-correspondence figure). Cross-
  references become descriptive phrases; "every field we see in the
  Napkin" → "in this book". Reveals cover `IsGalois`, the fundamental
  theorem (`IsGalois.intermediateFieldEquivSubgroup`), fixed
  fields/fixing subgroups, and splitting fields.
- **Finite fields.** Prose is verbatim (the classification opening and
  the four-point "whole point of this chapter" list). The 𝔽₉
  Frobenius-orbit diagram is redrawn as an SVG; a hint's upstream
  Fibonacci/field-symbol typo is corrected. Reveals cover
  `GaloisField p n` (the classification), `frobenius`, freshman's dream
  (`add_pow_char`), and cyclicity of `Fˣ`.
- **Ramification theory.** Prose is verbatim (the ℤ[i] factorization
  motivation, the ramified/inert/split framing and its prototype). Two
  problems are **newly written** over upstream's `\todo{more problems}`
  stub. The upstream diagrams are drawn as SVGs; one section header is
  de-symbolized. Reveals cover `Ideal.ramificationIdx`/`inertiaDeg`,
  `Ideal.sum_ramification_inertia` (the e·f identity), and Galois
  transitivity on primes above `p`; an aside notes the
  decomposition-group surjectivity and the inertia tower are not yet
  in Mathlib.
- **The Frobenius element.** Prose is verbatim (the Galois-extension
  setup, the "Picture:" tower, the Frobenius-map extension discussion);
  upstream's `tikzcd` towers are redrawn as SVGs and the IMO-2003 logo
  is a vendored raster on the worked problem. Reveals connect quadratic
  reciprocity (`ZMod.legendreSym`, `legendreSym.quadratic_reciprocity`)
  and cyclotomic Galois groups (`IsCyclotomicExtension.autEquivPow`) to
  the Frobenius/Chebotarev story; asides note Chebotarev density is
  absent from Mathlib.
- **Bonus: A Bit on Artin Reciprocity.** This bonus chapter
  (`artin.tex`) was overlooked in the first porting pass and restored
  by the full-book audit; the Frobenius chapter covers only
  `frobenius.tex`. All eight sections are ported verbatim. Every
  `tikzcd` diagram (the embedding lift, the Artin-map factoring, the
  restriction square, the two modulus correspondence lattices, the
  short-exact-sequence square) is rendered as a prose/inline chain; two
  footnotes become `{margin}` notes and the LMFDB-diagram footnote is
  dropped. Reveals cover `NumberField.InfinitePlace`
  (with `IsReal`/`IsComplex`) for infinite primes, `ClassGroup` for the
  trivial-modulus case, and `legendreSym` as the symbol the Artin symbol
  generalizes; moduli, rays, ray class groups, congruence subgroups, the
  Artin symbol/map, Artin reciprocity, the conductor, Takagi existence,
  and the Hilbert class field are honestly flagged as absent from
  Mathlib.

### Algebraic Topology I: Homotopy

- **Some topological constructions.** Prose is verbatim (the
  short-chapter opening and the Spheres section's $S^n$/$D^{n+1}$
  definitions). All of the chapter's Asymptote
  art (the $S^0$/$D^1$/$D^2$ sketches, the product-topology and unit-
  square pictures, the figure-eight, the CW-cell diagrams, and the
  torus/Klein/$\mathbb{RP}^2$ edge-identification squares) is redrawn
  as SVG, and the vendored raster images (`Projection_color_torus.jpg`,
  the two Klein-bottle photos `img:kleinfold`/`img:kleinbottle`, and
  the Riemann-sphere `earth.pdf` as an SVG) are all included. The
  section header "The torus,
  Klein bottle, $\mathbb{RP}^n$, $\mathbb{CP}^n$" is de-symbolized to
  unicode. Reveals cover `Metric.sphere`/`Metric.closedBall`, the
  quotient/product/sum topologies (`Setoid`/`Quotient` with
  `isOpen_coinduced`, `isOpen_prod_iff`, `isOpen_sum_iff`),
  `UnitAddCircle` for the torus, `Projectivization` for real/complex
  projective space (noting the general topology instance is not yet in
  Mathlib), and `Topology.CWComplex`. The **wedge sum**, absent from
  Mathlib, is **built from scratch** as a quotient of `X ⊕ Y`.
- **Fundamental groups.** Prose is verbatim (the coffee-cup/doughnut
  opening, the invariants motivation, and the homology-vs-homotopy-
  groups comparison). The path-fusing, loop, basepoint-independence,
  and homotopy-equivalence figures are redrawn as SVG, and the
  `S2-simply.png` raster is included. The `\venus`/`\mars` symbols (not in
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
- **Covering projections.** Prose is verbatim (the "few chapters ago
  we talked about the fundamental group" opening and the even-coverings/
  covering-projections introduction). All Asymptote/TikZ art (the helix,
  the even-covering pancakes, the lifting diagrams, and the
  $\mathbb{R}/G$, torus, and $\mathbb{RP}^2$ pictures) is redrawn as SVG,
  and the
  `even-covering.png` (`img:even_covering`) and `warsaw_circle.png`
  (`ref:hatcher`) rasters are included. Upstream's Problems section is only a `\todo{problems}`
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
  here. Prose is verbatim: Objects-and-morphisms' "high-level overview
  … re-cast into categorical terms" opening and "Motivation:
  isomorphisms" section, and Functors' "functors are maps between
  categories; natural transformations are maps between functors" opening
  and "many examples of functors" moral, all match upstream. Upstream's
  16/18 `tikzcd` commutative diagrams are a mix of SVG redraws and
  inline arrows.
- **Functors and natural transformations.** The remaining sections
  ("indexed family of objects", "contravariant functors", "equivalence
  of categories", "natural transformations", "the Yoneda lemma") are
  ported. The large Asymptote picture of a natural transformation
  dragging one functor's image onto another's is redrawn as SVG. The
  larger TikZ commutative diagrams are likewise redrawn as SVG; smaller
  ones become inline arrows. Upstream's "Equivalence of categories"
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
  The port keeps the complete Equalizers section verbatim (the
  equalizer prototype/definition and "we would like a categorical way
  of defining this, too"), writes a
  short self-contained **Pullback squares** section over the stub
  (keeping upstream's differentiable-functions example), and ports the
  brief Limits section; the stray trailing notes ("pushout square gives
  tensor product", "p-adic", "relative Chinese remainder theorem") are
  dropped as they are not content. The equalizer/fork TikZ diagrams are
  redrawn as SVG; the remaining cone diagrams become prose. Reveals
  cover `Limits.Fork`/`equalizer`/`HasEqualizer`,
  `Limits.pullback`/`HasPullback`, and `Limits.Cone`/`IsLimit`/`limit`
  /`HasLimit`.
- **Abelian categories.** Prose is verbatim (the "translate familiar
  concepts into categorical language" opening, the monic/epic notation
  note, and the zero-objects/kernels/cokernels definitions). The TikZ
  diagrams (the kernel/cokernel/image factorizations, the exact-sequence
  splicing, and the five-/four-/snake-lemma squares) are redrawn as SVG;
  smaller diagrams become
  inline sequences. The nested
  block quote from Aluffi on diagram chasing is reproduced verbatim.
  Several `\Cref` cross-references
  (rank-nullity, the equalizer-monic problem, PairTop) become
  descriptive phrases. Reveals cover `HasZeroObject`/`HasZeroMorphisms`,
  `Limits.kernel`/`cokernel`, `Abelian.image`, `Preadditive`/`Abelian`,
  `ShortComplex`/`.Exact`/`.ShortExact`, and `Abelian.Pseudoelement` for
  diagram chasing. Mathlib gained the full Freyd–Mitchell embedding
  theorem (`Abelian.freyd_mitchell`) in early 2025, so the companion
  uses it directly — the concrete embedding into `ModuleCat`, its
  `Full`/`Faithful`/exactness, and the mono/epi reflection that makes a
  diagram chase in `R`-Mod rigorous — with pseudoelements kept as the
  lighter in-category alternative.

### Algebraic Topology II: Homology

- **Singular homology.** Prose is verbatim (the "turn our attention to
  $H_1(X)$" opening, the $H_n$-vs-$\pi_n$ tradeoff, and the standard-
  simplex/boundary definitions). All Asymptote art (the singular-
  simplex, annulus-cycle, boundary-in-$S^1$, and prism-operator figures)
  is redrawn as SVG, together with the chapter's commutative diagrams;
  footnotes become `{margin}[…]` notes;
  cross-references (Hurewicz, the figure-eight example, the torus
  homology proposition) become descriptive phrases. Inline hints stay
  as "(Hint: …)" parentheticals and the two problems keep their
  upstream statements. Reveals cover the topological simplex
  (`SimplexCategory.toTop`), the singular simplicial set
  (`TopCat.toSSet`), the singular chain complex and its $H_n$
  (`singularChainComplexFunctor`, `singularHomologyFunctor`), the
  abstract `HomologicalComplex`/`ChainComplex` with `d_comp_d` for
  $\partial^2 = 0$, and chain homotopy (`Homotopy`).
- **The long exact sequence.** Prose is verbatim (the "key fact about
  chain complexes" opening and the exactness definition with its
  injective/surjective examples). Figures and commutative diagrams are
  redrawn as SVG; the snake-lemma and connecting-map discussion is
  ported in prose. Reveals cover
  `CategoryTheory.ShortComplex`, `.Exact`, `.ShortExact`, and
  `.Splitting`.
- **Excision and relative homology.** Prose is verbatim (the
  Mayer–Vietoris recap and the relative-homology chain-complex setup
  with its `hPairTop → Grp` functor). Figures and commutative diagrams
  redrawn as SVG; cross-references
  to the good-pair theorem and triple sequence become descriptive
  phrases. Relative/reduced singular homology, the category of pairs,
  excision, and deformation retracts are honestly flagged as **not
  present in Mathlib** (prose asides, no invented names). Four
  build-verified reveals were added on the parts that *do* exist: the
  short exact sequence `CategoryTheory.ShortComplex.ShortExact` and the
  long-exact connecting map `.δ` with `.homology_exact₃`, plus
  contractibility `ContractibleSpace.hequiv_unit` and homotopy
  equivalence `ContinuousMap.HomotopyEquiv`.
- **Cellular homology.** Prose is verbatim (the "we now introduce
  cellular homology … any CW complex we like" opening and the Degrees
  section's degree definition). Upstream's "Bonus:" title prefix becomes
  a one-line "this is a bonus chapter" note; figures and commutative
  diagrams redrawn as SVG. Cellular
  homology, degree, Euler characteristic, and Betti numbers are flagged
  as absent from Mathlib; `Topology.CWComplex` (which does exist) is
  cited for the underlying complexes. Five build-verified reveals were
  added on the present building blocks: `Topology.CWComplex`, the free
  cellular chain group via `Finsupp.basisSingleOne`, `ChainComplex` with
  `HomologicalComplex.homology`, Betti numbers/Euler characteristic via
  `Module.finrank_pi`, and the Klein-bottle 2-torsion via `ZMod`.
- **Singular cohomology.** Prose is verbatim (the "here's one way to
  motivate this chapter" opening with the $\mathbb{CP}^2$/$S^2\vee S^4$
  homology-coincidence examples and the universal-coefficient-theorem
  motivation). Figures and commutative diagrams redrawn as SVG. Reveals
  cover `CochainComplex`/`HomologicalComplex.homology`; the universal
  coefficient theorem and the elementary one-step `Ext` recipe are
  flagged as absent (a note distinguishes Mathlib's derived-category
  `Ext`).
- **Application of cohomology (cup products).** Figures and commutative
  diagrams redrawn as SVG; Evan's `1cycle.pdf` (a 1-cycle on
  $\mathbb{RP}^2$ drawn on the 2-sphere) is restored as SVG, with its
  upstream "$\mathbb{RP}^2$ isn't too hard to visualize … maps each such
  1-cycle to 1" passage re-inserted verbatim at its upstream position
  (this gives the later "we have already seen above why
  $\alpha \smile \alpha \neq 0$" remark its referent). The
  cohomology ring, cup product on singular cohomology, Poincaré
  duality, and Künneth are flagged as absent from Mathlib; the graded/
  anticommutative-ring backdrop is illustrated with `GradedRing` and
  `ExteriorAlgebra`, which do exist. Incidental solution-only citations
  (`ref:maxim752`) were dropped. The subsection heading "Cross product
  is not a $\ZZ$-module homomorphism" uses the Unicode glyph ℤ in place
  of inline `$\ZZ$`, since Verso cannot render inline math inside a
  heading; body prose keeps the usual `$`\mathbb{Z}`` form.

### Algebraic Geometry I: Classical Varieties

- **Affine varieties.** Prose is verbatim (the coordinates-first
  introduction and the $\mathbb{V}(S)$-as-zero-locus definition). All
  figures (the parabola, the $\mathbb{A}^1$/
  $\mathbb{A}^2$ sketches, the double-point) redrawn as SVG; the "flavors
  of ideals" table rendered as a prose list; footnotes → parentheticals/
  margin; `\Cref`s → descriptive phrases. Problems ported with hints
  inlined and solutions deferred. Reveals cover
  `MvPolynomial.zeroLocus`/`vanishingIdeal`, the Nullstellensatz
  (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`, over an
  algebraically closed field in finitely many variables) and its Galois
  connection, `Ideal.span`/`radical`/`IsRadical`, `IsNoetherianRing`,
  `Ideal.IsPrime`/`IsMaximal`, and `PrimeSpectrum`.
- **Affine varieties as ringed spaces.** Figures redrawn as SVG;
  problems ported. Reveals cover `PrimeSpectrum.zariskiTopology`/`zeroLocus`/
  `basicOpen`, `IsLocalization.Away`, and `AlgebraicGeometry.RingedSpace`.
- **Projective varieties.** Prose is verbatim (the $\mathbb{CP}^n$
  opening and the graded-ring definition); upstream's "this definition
  is the same as [the graded-ring definition]" cross-reference — which
  points forward to the cohomology chapter — is dropped per the
  cross-reference/no-forward-reference conventions rather than rendered
  as a phrase. The cone figure is redrawn as SVG (from Evan's `cone.pdf`
  3D render). Upstream has only a `\todo` for problems, so the port has
  no Problems section (not a content deviation). Reveals cover
  `GradedRing`,
  `Ideal.IsHomogeneous`/`HomogeneousIdeal`, `ProjectiveSpectrum`, and
  `HomogeneousLocalization`.
- **Bézout's theorem** (kept as a bonus chapter). Prose is verbatim
  (the "de points" overview and the non-radical-ideals / multiplicities
  motivation). SES diagrams rendered as prose; the Pascal and conic
  figures are redrawn as SVG; two problems ported (hints inlined). Classical projective Bézout, the degree of a projective
  variety, and Pascal's theorem are flagged as **absent from Mathlib**,
  with an explicit warning that Mathlib's `IsBezout` means the unrelated
  "Bézout domain"; `Polynomial.hilbertPoly` and
  `ShortComplex.ShortExact` are cited where they do apply.
- **Morphisms of varieties.** Prose is verbatim (the locally-ringed-
  space framing and the "morphisms via sections" construction — even
  upstream's "give a define" wording is preserved). Figures and
  commutative diagrams redrawn as SVG; four problems ported
  (hints inlined). Reveals cover `AlgebraicGeometry.LocallyRingedSpace`,
  `AffineScheme`, `Scheme.Opens`, and `IsAffineOpen`; an aside notes
  Mathlib has no separate quasi-projective-variety type and works with
  open subschemes instead.

### Algebraic Geometry II: Affine Schemes

- **Sheaves and ringed spaces.** Prose is verbatim (the "complexity of
  the affine variety comes from O_V" opening and the motivation/warnings
  section on sheaves of "functions with property P"). Section/germ
  figures and the categorical pullback-square diagram redrawn as SVG;
  the colimit remarks ported as prose; one footnote inlined. Reveals
  cover `TopCat.Presheaf`/`Sheaf`,
  `TopCat.Presheaf.stalk`/`germ`, and sheafification
  (`sheafify`/`toSheafify`/`stalkToFiber`), with a buildable
  presheaf-as-functor block.
- **Localization.** Prose is verbatim (the "adding denominators"
  moral and the affine-scheme motivation). Cross-references become
  descriptive phrases.
  Reveals cover `Submonoid`, `Localization`/`IsLocalization`,
  `Localization.Away`/`AtPrime`, `FractionRing`/`IsFractionRing`,
  `IsLocalization.orderIsoOfPrime`, and `Ideal.comap`/`map`.
- **Affine schemes: the Zariski topology.** Prose is verbatim (the
  affine-scheme "set of points / topology / structure sheaf" opening
  and the quick-note pointer to the examples chapter; `\Cref`s →
  descriptive phrases). The parabola figure is redrawn as SVG and the
  Calvin-and-Hobbes strip is included as a vendored raster
  (`img:calvin_hobbes_fly`); the post-`\endinput` Critch problem is
  correctly excluded. Reveals cover `PrimeSpectrum` with
  `zeroLocus`/`vanishingIdeal`, `isClosed_singleton_iff_isMaximal`,
  `isIrreducible_iff_vanishingIdeal_isPrime`, and Krull dimension
  (`ringKrullDim`/`topologicalKrullDim`).
- **Affine schemes: the sheaf.** Prose is verbatim (the "complete our
  definition of $X = \operatorname{Spec} A$" opening and the
  regular-functions moral). A Vakil footnote becomes a
  `{cite}`ref:vakil`` margin note. Reveals cover
  `AlgebraicGeometry.Spec.structureSheaf`,
  `StructureSheaf.globalSectionsIso`, `PrimeSpectrum.basicOpen`,
  `Localization.AtPrime`, and `IsLocalRing`/`ResidueField` (with a
  buildable local-ring instance block).
- **Eighteen examples of affine schemes** (interlude). Prose is
  verbatim (the "to cement the previous two chapters" opening and the
  geometric-intuition theme, upstream's grammatical quirks preserved).
  The chapter's Asymptote figures are redrawn as SVG and the Mumford
  "red book" raster is included as a vendored image; section headers
  containing `[…]`/`_` are escaped so Verso does not read them as
  markup. One orienting aside; the rest are worked examples. Four
  build-verified formalization reveals were added: Spec of a field is a
  point (`Unique (PrimeSpectrum K)`), the Zariski open/closed sets
  (`PrimeSpectrum.basicOpen`/`zeroLocus`), Spec A/I as the closed V(I)
  (`PrimeSpectrum.comap` is a closed embedding with range `zeroLocus I`),
  and Spec A[1/r] as the distinguished open D(r)
  (`localization_away_comap_range`).
- **Morphisms of locally ringed spaces.** Ported through the upstream
  `\endinput` (the later projective-scheme and morphisms-of-sheaves
  sections are excluded upstream); two problems ported (hints inlined). Reveals cover
  `AlgebraicGeometry.Scheme`/`Scheme.Hom`/`stalkMap`,
  `LocallyRingedSpace`, `IsLocalHom`, and `Spec`/`Spec.map` (buildable
  `noncomputable` blocks).

### Set Theory I: ZFC, Ordinals, and Cardinals

Per the book-wide types-not-sets exception, this part models sets *as*
sets (`ZFSet`/`Class`), since sets are the actual subject.

- **Cauchy's functional equation and Zorn's lemma** (the interlude).
  Prose is verbatim (the informal-chapter note with "Napkin" → "book",
  the Cauchy-functional-equation opening, and the "mumble grumble …
  pathological … Axiom of Choice" humour). The vendored rasters (the
  ordinal spiral `img:omega500` and the "zornaholic" cartoon
  `img:zornaholic`) are included; problems ported with hints inlined.
  Reveals cover `zorn_le`/`zorn_subset`, `IsMax`,
  and the Hamel-basis existence (`Module.Basis.ofVectorSpace` via
  `LinearIndependent`).
- **Zermelo–Fraenkel with choice.** Prose is verbatim (the "ultimate
  functional equation" opening and the vector-space/abelian-group/
  binary-operation/set definitional regress). The universe-triangle
  figure and the Cantor-diagonal table are rendered in prose; footnotes
  → `{margin}[…]`; cross-references become descriptive phrases. Reveals
  cover `ZFSet` with its axiom-operations (`empty`/`pair`/`sUnion`/
  `powerset`/`sep`/`image`/`omega`), `Class`, Cantor's theorem
  (`Function.cantor_injective`/`cantor_surjective`, with a buildable
  block), and `WellOrderingRel`/`IsWellOrder`.
- **Ordinals.** Prose is verbatim (the "counting for set theorists"
  proposal to name the first number not said, the von-Neumann ordinal
  definitions $0=\varnothing,1=\{0\},\dots$, and the $\omega$/$\omega+1$/
  $\omega\cdot2$ constructions), with `align*` displays rendered as
  inline comma-separated equations. The three vendored rasters — the counting-apples photo
  (`img:apples`), the velociraptor photo (`img:velociraptor`), and the
  ordinal ω-spiral (`img:omega500`) — are all included. An aside notes Mathlib
  defines `Ordinal` as order-isomorphism classes of well-orders rather
  than as transitive ∈-sets, with `ZFSet.rank` and `ZFSet.vonNeumann`
  as the ∈-set bridge; ordinal exponentiation is discussed via `opow`
  (there is no bare `Ordinal.opow` constant). Reveals also cover
  `Ordinal.omega0`, `Order.IsSuccLimit`, and `Ordinal.limitRecOn`.
- **Cardinals.** Prose is verbatim (the "an ordinal … does not do a
  fantastic job at measuring size" opening motivating cardinals). The
  ω↔ω+1 and ω↔ω² bijection displays and the cardinal-squaring tables are
  rendered as prose. Reveals cover `Cardinal.mk`/`aleph`/`aleph0`, Cantor
  (`Cardinal.cantor`), cardinal arithmetic collapse
  (`Cardinal.mul_eq_self`/`mul_eq_max`/`add_eq_max`), cofinality
  (`Ordinal.cof`), and `Cardinal.IsRegular`/`IsInaccessible`. The one
  `\sproblem` is rendered as a plain problem per the starred-problem
  convention.

### Set Theory II: Model Theory and Forcing

Sets are modeled as sets throughout, per the set-theory exception.

- **Inner model theory.** Prose is verbatim (the "model theory is
  really meta" opening and the "model of ZFC is a set with a binary
  relation" motivation). The universe-diagram figure is redrawn as
  SVG; footnotes → `{margin}[…]`; `\Cref`s → descriptive phrases; the
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
- **Forcing.** Prose is verbatim (the "Paul Cohen's technique of
  forcing" opening and the transitive-model/generic-$G$/$M[G]$
  construction with its $\mathbb{Z}[\sqrt2]$ analogy). The binary-tree
  and forcing-extension figures are redrawn as SVG; two problems
  ported (Rasiowa–Sikorski hint inlined). Only the poset scaffolding
  (`PartialOrder`, order density/bounds) is cited; generic filters,
  $\mathbb{P}$-names, $M[G]$, and the forcing relation are flagged as
  **entirely beyond Mathlib**.
- **Breaking the continuum hypothesis.** Prose is verbatim (the "we now
  use forcing to break the Continuum Hypothesis" opening and the
  constructible-universe-$L$ / "more fun when things break" motivation).
  The `Add(ω, ω₂)`/binary-tree figure is redrawn as SVG; the
  commented-out `V ≠ L` section is left out (it is commented out
  upstream); one problem ported with hint inlined. The
  cardinal-arithmetic backdrop cites `Cardinal.aleph`, `Ordinal.cof`,
  and `Cardinal.IsRegular`; the forcing-based independence of CH,
  cardinal collapse, ccc-preservation, and the constructible universe
  $L$ are flagged as absent from Mathlib. Build-verified reveals were
  added: `Cardinal.two_power_aleph0` ($2^{\aleph_0} = \mathfrak{c}$),
  `aleph0_lt_aleph_one`, CH itself as a `def … : Prop`
  (`continuum = aleph 1`, stated not proved since it is independent of
  ZFC), and cardinal regularity (`isRegular_aleph_one`).

### Backmatter

- **Pedagogical comments and references.** The full upstream
  `ch:refs` chapter is now ported verbatim (all four sections —
  Basic algebra and topology, Second-year topics, Advanced topics,
  Topics not in Napkin — with every subsection), followed by the
  auto-generated bibliography. The `\Cref{sec:basis_evil}` at the top
  becomes a descriptive phrase ("the pedagogical digression on how
  arrays of numbers are evil"); the Miranda-preface `quote` block is a
  `:::quote`; all `\cite` pointers are preserved. Eleven bibliography
  entries the prose newly cites (Axler, Math 55b, Cheng/Lebesgue,
  Yang/Dartmouth, Miquel, Munkres, Maxim, Oggier, Lenstra, Miranda,
  Hildebrand) were added to `Bibliography.lean` from the upstream
  `references.bib`.
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
  `\href` become Markdown links, and a few digressive footnotes become
  `{margin}[…]` notes.
- A verbatim-verification sweep over all five files (2026-07-14)
  confirmed the prose matches the source, and restored the two figures
  a solution embeds: the `love-proper-isomorphic-subgroup.jpg` "joke"
  image in the Groups solution, and the `tikzcd` diagram of restriction
  maps in the punctured-gyrotop solution (redrawn as
  `figures/algebraic-geometry/gyrotop-restriction.svg`). The sweep also
  reverted a handful of small paraphrases back to the source wording
  (e.g. the Rabinowitsch "smaller ring" parenthetical, the terse
  localization answer, the Cauchy-equation Wikipedia pointer, the
  Rasiowa–Sikorski "(this is actually trivial)", the hats "QED" ending,
  and the "As before," / "This completes the proof." openers/closers).
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
frontmatter (preface, advice, sales pitches, colophon), the notation,
sets-and-functions, and "Pedagogical comments and references"
appendices, and the merged hints/solutions appendix are all ported and
building. No upstream prose chapter remains unported.
