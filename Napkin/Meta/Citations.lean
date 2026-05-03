import VersoManual
import Verso.Doc.ArgParse
import Verso.Doc.Elab
import Napkin.Bibliography

open Lean Elab
open Lean.Doc.Syntax
open Verso
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse

namespace Napkin

/-! ## Citation helpers

Shared by the inline `{cite}` role here and by `:::epigraph` in
`Napkin.Meta.Directives`. The bibliography lives on its own page;
with the multi-page HTML output's `<base href="..."/>` set to the
rendered tree root, the relative href resolves correctly from any
chapter. -/

/-- Resolve a citation key to its short bibliography label
    (e.g. `Vakil`), falling back to the raw key when no entry matches. -/
def citeShortLabel (key : String) : String :=
  match lookupRef key with
  | some r => r.short
  | none   => key

/-- The href into the bibliography page for citation `key`. -/
def citeHref (key : String) : String :=
  s!"Backmatter/References/#{key.replace ":" "-"}"

/-- Render `[Short]` as an `<a class="cite">` link to the bibliography. -/
def renderCiteRef (key : String) : Verso.Output.Html :=
  .tag "a" #[("class", "cite"), ("href", citeHref key)]
    (.text true s!"[{citeShortLabel key}]")

/-! ## Inline citation element

`{cite}` `ref:vakil` renders a small bracketed link to the bibliography
entry with the entry's short label, e.g. `[Vakil]` linking to
`#ref-vakil`. -/

inline_extension Inline.napkinRef (key : String) where
  data := .str key
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ _ _ _ => do
      pure .empty
  toHtml :=
    some <| fun _ _ data _ => do
      let k : String := match data with | .str s => s | _ => ""
      pure (renderCiteRef k)
  extraCss := [r#"
    a.cite {
      text-decoration: none;
      color: var(--napkin-link-color, #2a5a8a);
    }
    a.cite:hover { text-decoration: underline; }
  "#]

/-- `{cite}` `ref:KEY`. The cite key is a code-span string literal. -/
@[role]
def cite : RoleExpanderOf Unit
  | (), inlines => do
    let #[arg] := inlines
      | throwError "Expected exactly one argument (the citation key)"
    let `(inline|code( $key:str )) := arg
      | throwErrorAt arg "Expected a code-span string with the citation key"
    let keyStr := key.getString
    ``(Verso.Doc.Inline.other
        (Napkin.Inline.napkinRef $(quote keyStr)) #[])

/-! ## Bibliography block

`:::bibliography` renders the full reference list. -/

block_extension Block.bibliography where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ _ _ _ _ => do
      pure .empty
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ _ _ => do
      let entries := references.qsort (fun a b => a.short < b.short)
      let mut items : Array Verso.Output.Html := #[]
      for r in entries do
        let slug := r.key.replace ":" "-"
        let titleHtml : Verso.Output.Html :=
          match r.url with
          | some u =>
            .tag "a" #[("href", u)] (.text true r.title)
          | none =>
            .text true r.title
        let entry : Verso.Output.Html := {{
          <dt id={{slug}}>{{r.short}}</dt>
          <dd>
            <span class="bib-authors">{{r.authors}}</span>
            ", " <span class="bib-year">{{r.year}}</span>
            ". " <em class="bib-title">{{titleHtml}}</em>
            ". " <span class="bib-source">{{r.source}}</span> "."
          </dd>
        }}
        items := items.push entry
      pure {{
        <dl class="bibliography">
          {{Verso.Output.Html.seq items}}
        </dl>
      }}
  extraCss := [r#"
    dl.bibliography { margin: 1em 0; }
    dl.bibliography > dt {
      font-weight: 700;
      margin-top: 0.75em;
    }
    dl.bibliography > dd {
      margin: 0.1em 0 0.6em 0;
      padding-left: 1em;
    }
    dl.bibliography .bib-source { color: #555; }
  "#]

@[directive]
def bibliography : DirectiveExpanderOf Unit
  | (), _ => do
    ``(Verso.Doc.Block.other Block.bibliography #[])

end Napkin
