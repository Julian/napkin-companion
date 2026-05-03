/-
Render-diff regression check for `Napkin.Meta.Directives`.

Renders `Test.Fixture` to a known output directory and diffs the
produced HTML files against committed golden files in
`Test/fixtures/`.

Invoked by the dispatcher in `Test.Main` via `Test.CheckFixture.run`.
The `--update` arg is plumbed through from `lake test -- --update`,
which copies the freshly-rendered HTML over the golden files (review
the diff before committing).
-/

import Std.Data.HashSet
import VersoManual
import Test.Fixture

open Std (HashSet)
open Verso.Doc
open Verso.Genre Manual

namespace Test.CheckFixture

/-- Minimal renderer config: no extra typography, fonts, or JS, so
    the fixture HTML stays stable across changes to the production
    `Render.lean` config. `RenderConfig` extends `Config`; the Config
    fields below set the rendering pipeline and `linkTargets` defaults. -/
def fixtureRenderConfig : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraHead := #[]
  extraFiles := []

/-- Where the renderer writes its output. Stable so re-runs overwrite
    in place; cleaned at the start of every run. -/
def renderOutDir : System.FilePath := "_out/test-fixture"

/-- Where committed golden files live. -/
def fixturesDir : System.FilePath := "Test/fixtures"

/-- Recursively collect every `index.html` file under `dir`, returning
    paths relative to `dir`. Skips directories whose name starts with
    `-` (Verso machinery: `-verso-data/`, `-verso-search/`, etc.).
    Restricted to the exact filename `index.html` because that's what
    Verso's multi-page emitter produces — keeping the filter tight
    avoids picking up unrelated `.html` files that may end up in the
    fixture tree (editor backups, manually-saved comparisons, etc.).
    Returns `#[]` if `dir` doesn't exist (e.g. before the first render). -/
private partial def collectHtmlFiles (dir : System.FilePath)
    (rel : System.FilePath := "") : IO (Array System.FilePath) := do
  let absDir := if rel.toString.isEmpty then dir else dir / rel
  if !(← absDir.pathExists) then return #[]
  let mut out : Array System.FilePath := #[]
  for entry in (← absDir.readDir) do
    let name := entry.fileName
    if name.startsWith "-" then continue
    let entryRel : System.FilePath :=
      if rel.toString.isEmpty then ⟨name⟩ else rel / name
    if (← entry.path.isDir) then
      out := out ++ (← collectHtmlFiles dir entryRel)
    else if name == "index.html" then
      out := out.push entryRel
  return out

/-- Render `Test.Fixture` to `renderOutDir` (clearing any prior
    contents first). Returns the renderer's exit code. -/
def renderFixture : IO UInt32 := do
  if (← renderOutDir.pathExists) then
    IO.FS.removeDirAll renderOutDir
  IO.FS.createDirAll renderOutDir
  manualMain (%doc Test.Fixture)
    (options := ["--output", renderOutDir.toString])
    (config := fixtureRenderConfig)

/-- Truncate a line for display, marking the cut point. HTML output
    can have lines >1KB; full lines drown the diff message. -/
private def truncateLine (s : String) (maxLen : Nat := 200) : String :=
  if s.length ≤ maxLen then s
  else (s.take maxLen).toString ++ s!"… [+{s.length - maxLen} more chars]"

/-- A unified-style diff window around the first divergence between two
    line lists, with `ctx` lines of context on each side. `none` when
    the two lists are identical. -/
structure DiffWindow where
  /-- 1-indexed line number of the first divergent line. -/
  line : Nat
  /-- Up to `ctx` shared lines preceding the divergence. -/
  before : List String
  /-- Lines on each side, paired with their source. The first entry is
      always the diverging pair; subsequent entries are trailing-context
      lines (which may also differ in long divergent runs). -/
  expected : List String
  actual : List String
  /-- Up to `ctx` shared lines following the diverging run. -/
  after : List String

/-- Walk past the common prefix of two line lists. Returns
    `(prefixLen, expSuffix, actSuffix)` where the suffixes start at
    the first divergence (one is empty if a side ended first). -/
private def splitAtFirstDiff
    : List String → List String → Nat → Nat × List String × List String
  | [], [], n => (n, [], [])
  | e :: es, a :: as, n =>
    if e == a then splitAtFirstDiff es as (n + 1) else (n, e :: es, a :: as)
  | exps, acts, n => (n, exps, acts)

/-- Walk a divergent run, capped at `bound` lines per side. Stops as
    soon as the two sides match again or one ends. The `<EOF>`
    sentinel marks a side that ended while the other still has lines.
    Returns `(expRun, actRun, expRest, actRest)`. -/
private def divergentRun
    : List String → List String → Nat → Array String → Array String
    → List String × List String × List String × List String
  | [], [], _, expRun, actRun =>
    (expRun.toList, actRun.toList, [], [])
  | exps, acts, 0, expRun, actRun =>
    (expRun.toList, actRun.toList, exps, acts)
  | e :: es, [], n + 1, expRun, actRun =>
    divergentRun es [] n (expRun.push e) (actRun.push "<EOF>")
  | [], a :: as, n + 1, expRun, actRun =>
    divergentRun [] as n (expRun.push "<EOF>") (actRun.push a)
  | e :: es, a :: as, n + 1, expRun, actRun =>
    if e == a then (expRun.toList, actRun.toList, e :: es, a :: as)
    else divergentRun es as n (expRun.push e) (actRun.push a)

/-- Up to `n` matching trailing lines following a divergent run. -/
private def commonSuffix : List String → List String → Nat → List String
  | _, _, 0 => []
  | e :: es, a :: as, n + 1 =>
    if e == a then e :: commonSuffix es as n else []
  | _, _, _ => []

/-- Compute a `DiffWindow` for the first divergence between `expected`
    and `actual`, with `ctx` lines of context on each side and the
    divergent run capped at `bound` lines per side. Longer divergences
    are reported truncated; the full `diff` command printed alongside
    covers the rest. -/
private def firstDiffWindow (expected actual : String)
    (ctx : Nat := 3) (bound : Nat := 10) : Option DiffWindow :=
  let exp := expected.splitOn "\n"
  let act := actual.splitOn "\n"
  let (prefLen, expSuf, actSuf) := splitAtFirstDiff exp act 0
  if expSuf.isEmpty && actSuf.isEmpty then none
  else
    let (expRun, actRun, expRest, actRest) :=
      divergentRun expSuf actSuf bound #[] #[]
    let before := (exp.take prefLen).reverse.take ctx |>.reverse
    let after := commonSuffix expRest actRest ctx
    some {
      line := prefLen + 1, before,
      expected := expRun, actual := actRun, after
    }

/-- Print a `DiffWindow` to stderr in unified-diff style. -/
private def printDiffWindow (rel : System.FilePath) (expectedPath actualPath : System.FilePath)
    (w : DiffWindow) : IO Unit := do
  IO.eprintln s!"DRIFT in {rel} (first divergence at line {w.line}):"
  for ln in w.before do IO.eprintln s!"   {truncateLine ln}"
  for ln in w.expected do IO.eprintln s!"  -{truncateLine ln}"
  for ln in w.actual do IO.eprintln s!"  +{truncateLine ln}"
  for ln in w.after do IO.eprintln s!"   {truncateLine ln}"
  IO.eprintln s!"  full diff: diff {expectedPath} {actualPath}"

/-- Take the union of two file-path arrays, deduplicated by string
    representation. Order: all of `xs` (in input order), then any
    new entries from `ys`. O(n) amortized via `HashSet`. -/
private def unionPaths (xs ys : Array System.FilePath)
    : Array System.FilePath := Id.run do
  let mut seen : HashSet String := {}
  let mut out : Array System.FilePath := Array.emptyWithCapacity (xs.size + ys.size)
  for p in xs ++ ys do
    let s := p.toString
    if !seen.contains s then
      seen := seen.insert s
      out := out.push p
  return out

/-- Compare the freshly-rendered output at `renderOutDir/html-multi/`
    against the golden files in `fixturesDir/`. Walks both directories
    so a file appearing in one but not the other is reported as drift.
    Returns `true` if any file differs (or is missing on either side). -/
def diffAgainstGolden : IO Bool := do
  let multiDir := renderOutDir / "html-multi"
  let actualFiles ← collectHtmlFiles multiDir
  let goldenFiles ← collectHtmlFiles fixturesDir
  let mut drift := false
  for rel in unionPaths actualFiles goldenFiles do
    let actual := multiDir / rel
    let expected := fixturesDir / rel
    if !(← actual.pathExists) then
      IO.eprintln s!"Stale golden (no longer rendered): {expected}"
      IO.eprintln "Run `lake test -- --update` to remove it."
      drift := true
      continue
    if !(← expected.pathExists) then
      IO.eprintln s!"New rendered file with no golden: {expected}"
      IO.eprintln "Run `lake test -- --update` to record it."
      drift := true
      continue
    let exp ← IO.FS.readFile expected
    let act ← IO.FS.readFile actual
    if let some w := firstDiffWindow exp act then
      printDiffWindow rel expected actual w
      drift := true
  pure drift

/-- Copy every rendered fixture file into `fixturesDir/` and remove
    any pre-existing goldens the renderer no longer produces, so the
    on-disk fixture stays in sync with the doc structure.

    The pre-existing golden set is snapshotted before any writes —
    walking after writing would re-discover everything we just wrote
    and only flag genuinely stale files anyway, but the pre-write
    snapshot is both faster and clearer about intent. -/
def writeGolden : IO Unit := do
  let multiDir := renderOutDir / "html-multi"
  let actualFiles ← collectHtmlFiles multiDir
  let preexistingGoldens ← collectHtmlFiles fixturesDir
  let actualSet : HashSet String :=
    actualFiles.foldl (init := {}) fun s p => s.insert p.toString
  for rel in actualFiles do
    let src := multiDir / rel
    let dst := fixturesDir / rel
    if let some parent := dst.parent then
      IO.FS.createDirAll parent
    IO.FS.writeBinFile dst (← IO.FS.readBinFile src)
    IO.println s!"Updated {dst}"
  for rel in preexistingGoldens do
    if !actualSet.contains rel.toString then
      let stale := fixturesDir / rel
      IO.FS.removeFile stale
      IO.println s!"Removed stale {stale}"

/-- Run the render-diff check. Returns 0 on pass, nonzero on drift or
    renderer failure. With `--update` in `args`, copies the freshly-
    rendered HTML over the golden files instead of diffing. -/
def run (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  let rc ← renderFixture
  if rc != 0 then return rc
  if update then
    writeGolden
    IO.println "Golden files regenerated. Review the diff before committing."
    return 0
  if (← diffAgainstGolden) then
    IO.eprintln ""
    IO.eprintln "Render-diff check failed. If the change is intentional,"
    IO.eprintln "regenerate the golden with: lake test -- --update"
    return 1
  IO.println "Render-diff check passed."
  return 0

end Test.CheckFixture
