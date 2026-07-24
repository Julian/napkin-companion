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

import Napkin.Missing.ArtinMap
import Napkin.Missing.BooleanFourier
import Napkin.Missing.Chains
import Napkin.Missing.Cochains
import Napkin.Missing.ContinuumHypothesis
import Napkin.Missing.CoveringClassification
import Napkin.Missing.CupProduct
import Napkin.Missing.DifferentialForms
import Napkin.Missing.Divisors
import Napkin.Missing.Forcing
import Napkin.Missing.Frobenius
import Napkin.Missing.GroupDeterminant
import Napkin.Missing.HolomorphicForm
import Napkin.Missing.HolomorphicLineBundle
import Napkin.Missing.Homotopy
import Napkin.Missing.IntersectionMultiplicity
import Napkin.Missing.ManifoldForm
import Napkin.Missing.MappingDegree
import Napkin.Missing.PadicInverseLimit
import Napkin.Missing.PlaneCurveNode
import Napkin.Missing.Quantum
import Napkin.Missing.RamifiedMap
import Napkin.Missing.RelativeHomology
import Napkin.Missing.Residue
import Napkin.Missing.RiemannSphere
import Napkin.Missing.SetModels
