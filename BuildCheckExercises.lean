/-
`lake exe checkexercises` — elaborate every generated exercise and
solution file, so a reader who downloads one gets something that compiles.

The book building is not evidence that these do. Each file is reassembled
from a chapter: the chapter's header, then its code blocks in order, with
solution bodies substituted into the exercises for the `-solutions` half.
Anything the reassembly drops — an `open` from a block above the
Formalization section, a declaration another one depends on — leaves the
chapter compiling happily while the file a reader opens does not.

Usage: `lake exe checkexercises [--jobs N] [--dir DIR]`. With no `--dir`
the files are regenerated into a scratch directory first, so what gets
checked is what `lake exe exercises` would hand a reader right now.

Every file is elaborated in its own `lean` process, since each has its own
header; `--jobs` (default 4) bounds how many run at once. Expect this to
take tens of minutes for the whole book — it is a release gate, not an
inner-loop check.
-/

import Napkin.Meta.Exercises

-- The generated files import these, and `lean` can only load a module that
-- has already been compiled. Importing them here makes building this
-- executable build them too, so the check does not quietly depend on
-- whatever happens to be in `.lake` already — which is the difference
-- between a developer's tree and a fresh CI checkout.
import Napkin.Meta
import Napkin.Missing

open System (FilePath)

/-- Elaborate one file, returning its diagnostics if it failed. -/
private def elaborate (file : FilePath) : IO (Option String) := do
  let out ← IO.Process.output
    { cmd := "lake", args := #["env", "lean", file.toString] }
  if out.exitCode == 0 then
    return none
  else
    return some (out.stdout ++ out.stderr)

/-- Run `f` over `xs`, at most `jobs` at a time. -/
private def inParallel {α β} (jobs : Nat) (xs : Array α)
    (f : α → IO β) : IO (Array β) := do
  let width := max 1 jobs
  let mut out : Array β := #[]
  let mut rest := xs
  while !rest.isEmpty do
    let batch := rest.take width
    rest := rest.drop width
    let tasks ← batch.mapM fun x => IO.asTask (f x)
    for t in tasks do
      out := out.push (← IO.ofExcept t.get)
  return out

structure Options where
  jobs : Nat := 4
  dir : Option FilePath := none

private def parse : List String → Except String Options
  | [] => .ok {}
  | "--jobs" :: n :: rest => do
    let some j := n.toNat? | .error s!"--jobs expects a number, got {n}"
    return { ← parse rest with jobs := j }
  | "--dir" :: d :: rest => do return { ← parse rest with dir := some d }
  | a :: _ => .error s!"unexpected argument {a}"

def main (args : List String) : IO UInt32 := do
  let opts ←
    match parse args with
    | .ok o => pure o
    | .error e =>
      IO.eprintln s!"checkexercises: {e}"
      IO.eprintln "usage: lake exe checkexercises [--jobs N] [--dir DIR]"
      return 1
  let dir ←
    match opts.dir with
    | some d => pure d
    | none => do
      let d : FilePath := "_out" / "check-exercises"
      IO.FS.createDirAll d
      let n ← Napkin.Meta.Exercises.writeAll d
      IO.println s!"checkexercises: regenerated {n} chapters into {d}"
      pure d
  let files ← Napkin.Meta.Extract.collectLean dir
  if files.isEmpty then
    IO.eprintln s!"checkexercises: no .lean files under {dir}"
    return 1
  IO.println s!"checkexercises: elaborating {files.size} files, \
    {opts.jobs} at a time…"
  let results ← inParallel opts.jobs files fun f => do
    let err ← elaborate f
    if err.isSome then IO.println s!"  FAIL {f}" else pure ()
    return (f, err)
  let failures := results.filterMap fun (f, e) => e.map (f, ·)
  if failures.isEmpty then
    IO.println s!"checkexercises: OK ({files.size} files elaborate)"
    return 0
  IO.eprintln s!"\ncheckexercises: FAIL — {failures.size} of {files.size} \
    files do not elaborate:"
  for (f, err) in failures do
    IO.eprintln s!"\n--- {f}"
    IO.eprintln err
  return 1
