/-
Hover documentation for math-mode entities.

The body of a chapter writes $`\mathbb{Z}`, not `Int`, so the two channels
never meet: Verso attaches Mathlib signatures and doc-strings to code
spans (that is what `{name}` does), while math is handed to KaTeX as
opaque source. A reader looking at $`\mathcal{O}_K` gets no way to ask
what it is called.

The `{mathname}` role bridges them. `{mathname NumberField.RingOfIntegers}`
followed by a code span holding the math renders the math exactly as
usual, but wrapped in the hover machinery Verso already ships: the
constant's signature and doc-string are looked up at elaboration time,
registered with `addHover`, and the resulting id is attached to the
rendered math. Because the tooltip script only binds tokens inside a
`.hl.lean` container, the wrapper carries those classes, and the CSS below
undoes the code styling they would otherwise bring.

Resolution happens during elaboration, so a name that no longer exists is
a build error rather than a silently dead tooltip.
-/

import VersoManual
import Verso.Doc.ArgParse
import Verso.Doc.Elab

open Lean Elab
open Lean.Doc.Syntax
open Verso
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Verso.Code

namespace Napkin

/-! The inline element: math source, plus the signature and doc-string of
the constant it denotes. -/

inline_extension Inline.mathName (math : String) (sig : String)
    (docs : String) via withHighlighting where
  data := .arr #[.str math, .str sig, .str docs]
  traverse _ _ _ := pure none
  toTeX := some <| fun _ _ _ _ => pure .empty
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[.str math, .str sig, .str docs] := data
        | pure .empty
      let docsHtml : Verso.Output.Html :=
        if docs.isEmpty then .empty
        else {{ <pre class="docstring">{{docs}}</pre> }}
      let hoverId ← addHover (g := Manual) {{ <code>{{sig}}</code> {{docsHtml}} }}
      pure {{
        <code class="hl lean inline napkin-mathname" "data-lean-context"="examples">
          <span class="const token" "data-verso-hover"={{toString hoverId}}>
            <code class="math inline">{{math}}</code>
          </span>
        </code>
      }}
  extraCss := [r#"
    /* Undo the code-block styling that `.hl.lean.inline` brings, so the
       math renders as math; only the hover behaviour is borrowed. */
    code.napkin-mathname,
    code.napkin-mathname > span.token {
      background: none !important;
      border: none !important;
      padding: 0 !important;
      font-family: inherit;
      font-size: inherit;
      color: inherit;
    }
    /* Mark it as consultable without shouting. */
    code.napkin-mathname > span.token {
      cursor: help;
      border-bottom: 1px dotted #b0b0b0 !important;
    }
  "#]

/-- The Lean constant a `{mathname}` role documents. -/
structure MathNameConfig where
  /-- The constant whose signature and doc-string to show. -/
  name : Ident

section
variable [Monad m] [MonadError m]

def MathNameConfig.parse : ArgParse m MathNameConfig :=
  MathNameConfig.mk <$> .positional `name {
    description := "the Lean name to document"
    signature := .Ident
    get := fun
      | .name x => pure x
      | other => throwError "Expected a name, got {repr other}"
  }

instance : FromArgs MathNameConfig m := ⟨MathNameConfig.parse⟩
end

/-- `{mathname Foo}`\LaTeX`` — render the math, with `Foo`'s Mathlib
    signature and doc-string available on hover. -/
@[role]
def mathname : RoleExpanderOf MathNameConfig
  | cfg, #[arg] => do
    let `(inline|code( $mathStr:str )) := arg
      | throwErrorAt arg "Expected a code span holding the math source"
    let resolved ← realizeGlobalConstNoOverloadWithInfo cfg.name
    let sig := toString (← (PrettyPrinter.ppSignature resolved)).1
    let docs := (← findDocString? (← getEnv) resolved).getD ""
    `(Inline.other
        (Inline.mathName $(quote mathStr.getString) $(quote sig) $(quote docs))
        #[Inline.code $(quote mathStr.getString)])
  | _, more =>
    if h : more.size > 0 then
      throwErrorAt more[0] "Unexpected contents"
    else
      throwError "Expected a code span holding the math source"

end Napkin
