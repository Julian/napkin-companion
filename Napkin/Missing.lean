/-
# `Napkin.Missing` — the companion's stopgap definitions

The chapters' Lean companions rebuild the text in Mathlib.  Where a
chapter introduces a mathematical object Mathlib has **no** definition
for, the object is defined under `Napkin/Missing/` — as faithfully to the
text as Lean allows — so the companion's worked models and exercises have
something concrete to work with instead of stopping at a prose note.

This module re-exports every shim, so a reader (or a tool) can pull in the
whole layer with a single `import Napkin.Missing`.  Chapters themselves
import only the specific shim they use.

## Conventions

* **Namespace.** Everything lives in `namespace Napkin.Missing`.  A few
  objects that would clash with Mathlib names (topology's `Dense`, the
  order-theoretic `Filter`, the two `ExteriorDerivative`s) sit in a nested
  namespace — `Napkin.Missing.Forcing`, `…ManifoldForm`, etc. — and are
  referred to by that qualified name from the chapters.

* **Retirement tag.** Every stopgap definition carries a doc-string line
  beginning `Not in Mathlib.` naming the upstream object to watch for.
  Enumerate the outstanding stopgaps with

      grep -rn "Not in Mathlib." Napkin/Missing

  When Mathlib gains the real object, delete the stopgap here and repoint
  the chapters that `open Napkin.Missing` at the Mathlib name.  (This has
  already happened once: the Categories/Abelian chapter dropped its planned
  Freyd–Mitchell shim when Mathlib gained `Abelian.freyd_mitchell`.)

* **Statement-as-structure.** A deep *theorem* with no constructible
  content (Riemann–Roch, projective Bézout, excision, Chebotarev, Artin
  reciprocity, Riemann–Hurwitz, …) is bundled as a `*Data` structure whose
  fields include the theorem's conclusion as a hypothesis, so its
  consequences stay derivable even though the theorem itself is assumed.

The chapters consume these as hypotheses; none construct a `*Data` value,
so an unsatisfiable bundle can never poison a derived exercise.
-/

module
public import Napkin.Missing.ArtinMap
public import Napkin.Missing.BooleanFourier
public import Napkin.Missing.Chains
public import Napkin.Missing.Cochains
public import Napkin.Missing.ContinuumHypothesis
public import Napkin.Missing.CoveringClassification
public import Napkin.Missing.CupProduct
public import Napkin.Missing.DifferentialForms
public import Napkin.Missing.Divisors
public import Napkin.Missing.Forcing
public import Napkin.Missing.Frobenius
public import Napkin.Missing.GroupDeterminant
public import Napkin.Missing.HolomorphicForm
public import Napkin.Missing.HolomorphicLineBundle
public import Napkin.Missing.Homotopy
public import Napkin.Missing.IntersectionMultiplicity
public import Napkin.Missing.ManifoldForm
public import Napkin.Missing.MappingDegree
public import Napkin.Missing.PadicInverseLimit
public import Napkin.Missing.PlaneCurveNode
public import Napkin.Missing.Quantum
public import Napkin.Missing.RamifiedMap
public import Napkin.Missing.RelativeHomology
public import Napkin.Missing.Residue
public import Napkin.Missing.RiemannSphere
public import Napkin.Missing.SetModels
