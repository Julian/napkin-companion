/-
Source-level linters for Verso markup mistakes. Hooks into Lean's
standard linter framework via `register_option linter.X` and
`addLinter`, so warnings appear inline in editors and during the
ordinary `lake build` pipeline.

Currently checks for:
  * Bare `<URL>`-style autolinks (with `https`, `http`, or `www`
    schemes). Verso's parser doesn't recognize these as links — they
    pass through as plain text and render as inert text in the HTML.
    Use `[text](url)` instead.
-/

import Lean.Linter.Basic
import Lean.Meta.Hint
import Verso.Parser
import Lean.Elab.Command
import Lean.Data.Options

open Lean Linter Elab Command
open Lean.Doc.Syntax

/-- Generates suggestions to convert bare-URL autolinks into proper
    `[text](url)` links. -/
register_option linter.napkin.bareUrl : Bool := {
  defValue := true
  descr := "if true, warn on bare `<https://...>`-style autolinks \
    (which Verso renders as inert text)"
}

namespace Napkin.Linter

private def autolinkPrefixes : List String := ["<https://", "<http://", "<www."]

/-- If the source at `pos` starts with one of `autolinkPrefixes`,
    return the matched byte length. -/
private def matchPrefix (source : String) (pos : String.Pos.Raw) : Option Nat := Id.run do
  for pfx in autolinkPrefixes do
    let plBytes := pfx.utf8ByteSize
    if pos.byteIdx + plBytes > source.utf8ByteSize then
      continue
    let stop : String.Pos.Raw := ⟨pos.byteIdx + plBytes⟩
    if pos.extract source stop == pfx then
      return some plBytes
  pure none

/-- Walk forward from `from_` looking for a closing `>` on the same
    line. Returns its position if found before `limit`/EOL. -/
private partial def findClose (source : String) (from_ limit : String.Pos.Raw)
    : Option String.Pos.Raw :=
  if from_.byteIdx ≥ limit.byteIdx then none
  else
    let c := from_.get source
    if c == '>' then some from_
    else if c == '\n' then none
    else findClose source (from_.next source) limit

/-- Scan `[start, stop)` of `source` for autolink-style URLs. For
    each hit, run `report` with the start position and one-past-end. -/
private partial def scanRange (source : String) (start stop : String.Pos.Raw)
    (report : String.Pos.Raw → String.Pos.Raw → CommandElabM Unit) :
    CommandElabM Unit := do
  if start.byteIdx ≥ stop.byteIdx then return
  let c := start.get source
  if c == '<' then
    if let some pl := matchPrefix source start then
      let after : String.Pos.Raw := ⟨start.byteIdx + pl⟩
      if let some closeAt := findClose source after stop then
        let endPos := closeAt.next source
        report start endPos
        scanRange source endPos stop report
        return
  scanRange source (start.next source) stop report

/-- The actual linter. Runs over Verso `inline|$s:str` text nodes;
    Verso's parser keeps `<` and `>` chars in the source verbatim,
    so we just scan for the pattern in the raw substring. -/
def bareUrl : Linter where
  run := withSetOptionIn fun stx => do
    unless (`Verso.Doc.Concrete).isPrefixOf stx.getKind do return
    unless getLinterValue linter.napkin.bareUrl (← getLinterOptions) do return
    let text ← getFileMap
    discard <| stx.replaceM fun
      | `(inline|$s:str) => do
        if let some ⟨start, stop⟩ := s.raw.getRange? then
          scanRange text.source start stop fun hitStart hitStop => do
            let snippet : String := hitStart.extract text.source hitStop
            let url := snippet.drop 1 |>.dropEnd 1
            let strLit :=
              Syntax.mkStrLit snippet
                (info := .original
                  {str := text.source, startPos := hitStart, stopPos := hitStart} hitStart
                  {str := text.source, startPos := hitStop,  stopPos := hitStop}  hitStop)
            let h ← liftTermElabM <| MessageData.hint
              m!"Use a Markdown link"
              #[{suggestion := s!"[{url}]({url})"}]
              (ref? := strLit)
            logLint linter.napkin.bareUrl strLit
              (m!"Bare `<URL>` autolink — Verso renders this as inert \
                text, not a link" ++ h)
        pure none
      | _ => pure none

initialize addLinter bareUrl

end Napkin.Linter
