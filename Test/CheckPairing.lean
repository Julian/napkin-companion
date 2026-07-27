/-
Regression check pinning each exercise to its worked solution.

An exercise and the solution beneath it are two independently elaborated
code blocks that happen to restate the same theorem. Nothing in the build
ties them together, so an edit to one can silently leave the other proving
a *different* statement — and both still compile. This test closes that
gap with two invariants over every chapter's `# Formalization` section:

  1. **Every exercise has a solution.** A ```lean block containing
     `sorry` must be immediately followed by a `:::solution` block.

  1b. **Every exercise is wrapped in `:::exercise`,** so that it renders
     labelled and numbered rather than looking like one more worked
     model.

  2. **The statements agree.** The signature of the `sorry`-bearing
     declaration — everything up to the proof, i.e. up to the first
     top-level `:=` or `where` — must appear verbatim (modulo line
     breaking) among the signatures in the solution block.

Comparing signatures rather than whole blocks is what makes this robust:
a stub written `… := by sorry` matches a solution written `… where` or
`… := term`, and a block that defines a helper alongside its exercise
still matches, since every declaration in the solution is a candidate.

Invoked by the dispatcher in `Test.Main` via `Test.CheckPairing.run`.
-/

import Napkin.Meta.Extract

namespace Test.CheckPairing

open Napkin.Meta.Extract

/-- Line numbers of ```lean fences that open a `sorry`-bearing block not
    preceded by a `:::exercise` opener, i.e. unwrapped exercises. -/
private def unwrappedExercises (text : String) : Array Nat := Id.run do
  let lines := (text.splitOn "\n").toArray
  let mut out : Array Nat := #[]
  let mut started := false
  let mut inCode := false
  let mut inSol := false
  let mut fence := 0
  let mut cur : Array String := #[]
  for i in [0:lines.size] do
    let some raw := lines[i]? | continue
    let t := strip raw
    if !started then
      if t == "# Formalization" then started := true
    else if inCode then
      if t == "```" then
        inCode := false
        if !inSol && hasSorry (String.intercalate "\n" cur.toList) then
          -- The opener must sit on the line just above the fence.
          let prev := (lines[fence - 1]?).map strip |>.getD ""
          if !prev.startsWith ":::exercise" then out := out.push (fence + 1)
        cur := #[]
      else
        cur := cur.push raw
    else if t.startsWith "```lean" then
      inCode := true; fence := i; cur := #[]
    else if t == ":::solution" then
      inSol := true
    else if t == ":::" && inSol then
      inSol := false
  return out

def run (_args : List String) : IO UInt32 := do
  let files ← collectLean sourceRoot
  let mut pairs : Nat := 0
  let mut problems : Array String := #[]
  for f in files do
    let text ← IO.FS.readFile f
    for line in unwrappedExercises text do
      problems := problems.push
        s!"  {f}:{line}: exercise is not wrapped in `:::exercise`"
    let blocks := collectBlocks text
    for i in [0:blocks.size] do
      let some b := blocks[i]? | continue
      if b.kind != Kind.plain then continue
      -- A block without `sorry` is a worked model; nothing to pair.
      if !hasSorry b.code then continue
      -- The exercise is the last declaration carrying the `sorry`.
      let withSorry := (decls b.code).filter hasSorry
      let some stub := withSorry.back? | continue
      let sig := signature stub
      match blocks[i + 1]? with
      | some sol =>
        if sol.kind != Kind.solution then
          problems := problems.push
            s!"  {f}: exercise has no solution block\n      {sig}"
        else
          pairs := pairs + 1
          let sigs := (decls sol.code).map signature
          if !sigs.contains sig then
            problems := problems.push
              s!"  {f}: statement drift\n      exercise: {sig}\n      \
                solution: {String.intercalate " | " sigs.toList}"
      | none =>
        problems := problems.push
          s!"  {f}: exercise has no solution block\n      {sig}"

  if problems.isEmpty then
    IO.println s!"check-pairing: OK ({pairs} exercise/solution pairs agree)"
    return 0
  IO.eprintln "check-pairing: FAIL"
  for p in problems do IO.eprintln p
  IO.eprintln "Each exercise must be followed by a `:::solution` restating \
    it verbatim; fix whichever of the two drifted."
  return 1

end Test.CheckPairing
