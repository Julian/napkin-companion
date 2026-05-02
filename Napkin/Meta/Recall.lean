/-
Extends Mathlib's `recall` command with an unnamed form. Mathlib's
`recall foo (bar : T) : U` requires a named declaration. We add

  recall : AddGroup ℤ
  recall (n : ℕ) : AddCommGroup (ZMod n)

which read as "recall that ℤ is an additive group" / "recall that
`ZMod n` is an additive commutative group for any `n`" — the
proposition is the only thing we want to display, and the existing
Mathlib instance satisfying it is verified by `synthInstance`
(under any binders in scope). Renders in code blocks exactly as
written.
-/

import Mathlib.Tactic.Recall
import Lean.Elab.Command

open Lean Elab Command Term

namespace Napkin.Meta.Recall

/-- `recall (binders)? : <type>` — verify that an instance of
    `<type>` exists in the current Mathlib environment, optionally
    under binders that quantify over universe / type / instance
    parameters. Doesn't introduce any new declaration; doesn't
    shadow Mathlib's named `recall <name> ...` form (different next
    token after `recall`). -/
syntax (name := recallType) (docComment)? "recall " (bracketedBinder)* " : " term : command

elab_rules : command
  | `(recallType| $[$_doc?:docComment]? recall $binders* : $type) =>
    runTermElabM fun _ => do
      elabBinders binders fun _xs => do
        let t ← elabType type
        synthesizeSyntheticMVarsNoPostponing
        discard <| Meta.synthInstance t

end Napkin.Meta.Recall
