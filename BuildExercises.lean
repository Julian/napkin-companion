/-
`lake exe exercises` — write each chapter's Lean out as a pair of
standalone files (exercises with `sorry`s left in, and solutions), so a
reader can open one and work in it directly.

Usage: `lake exe exercises [--output DIR]` (default `_out/exercises`).
The extraction itself lives in `Napkin.Meta.Exercises`, which the book's
render step also calls so the same files ship with the site.
-/

import Napkin.Meta.Exercises

open Napkin.Meta.Exercises

def main (args : List String) : IO UInt32 := do
  let dest : System.FilePath :=
    match args with
    | ["--output", d] => d
    | [] => "_out/exercises"
    | _ =>
      panic! "usage: lake exe exercises [--output DIR]"
  let n ← writeAll dest
  IO.println s!"exercises: wrote {n} chapters into {dest}"
  return 0
