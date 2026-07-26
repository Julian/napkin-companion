/-
Regression check pinning each exercise to its worked solution.

An exercise and the solution beneath it are two independently elaborated
code blocks that happen to restate the same theorem. Nothing in the build
ties them together, so an edit to one can silently leave the other proving
a *different* statement — and both still compile. This test closes that
gap with two invariants over every chapter's `# Formalization` section:

  1. **Every exercise has a solution.** A ```lean block containing
     `sorry` must be immediately followed by a `:::solution` block.

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

import Test.Chapters

namespace Test.CheckPairing

open Test.Chapters

/-- Whether a fenced code block sat inside a `:::solution` directive. -/
inductive Kind where
  /-- A code block in the chapter body: a worked model or an exercise. -/
  | plain
  /-- A code block inside `:::solution`. -/
  | solution
deriving BEq

/-- One fenced ```lean block of a chapter's formalization section. -/
structure Block where
  /-- Whether the block is a solution. -/
  kind : Kind
  /-- The block's source text, fences excluded. -/
  code : String

/-- Split a chapter's `# Formalization` section into its ```lean blocks,
    in order, tagging each with whether it sits inside `:::solution`. -/
private def collectBlocks (text : String) : Array Block := Id.run do
  let mut out : Array Block := #[]
  let mut started := false
  let mut inCode := false
  let mut inSol := false
  let mut cur : Array String := #[]
  for line in text.splitOn "\n" do
    let t := strip line
    if !started then
      if t == "# Formalization" then started := true
    else if inCode then
      if t == "```" then
        inCode := false
        out := out.push
          { kind := if inSol then .solution else .plain,
            code := String.intercalate "\n" cur.toList }
        cur := #[]
      else
        cur := cur.push line
    else if t.startsWith "```lean" then
      inCode := true
      cur := #[]
    else if t == ":::solution" then
      inSol := true
    else if t == ":::" && inSol then
      inSol := false
  return out

/-- Keywords that can begin a top-level declaration in a chapter snippet. -/
private def starters : List String :=
  ["example", "theorem", "lemma", "def", "instance", "abbrev", "recall",
   "noncomputable", "open", "private", "protected", "structure"]

/-- Does this line begin a new top-level declaration? Declarations start in
    column zero, so an indented line yields an empty first word and is
    correctly rejected; everything indented belongs to the one above. -/
private def isDeclStart (line : String) : Bool :=
  starters.contains (line.takeWhile (fun c => !c.isWhitespace)).toString

/-- Split a code block into its top-level declarations. -/
private def decls (code : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array String := #[]
  for line in code.splitOn "\n" do
    if isDeclStart line then
      if !cur.isEmpty then
        out := out.push (String.intercalate "\n" cur.toList)
      cur := #[line]
    else if !cur.isEmpty then
      cur := cur.push line
  if !cur.isEmpty then
    out := out.push (String.intercalate "\n" cur.toList)
  return out

/-- Strip `--` line comments. -/
private def stripComments (s : String) : String :=
  String.intercalate "\n" ((s.splitOn "\n").map fun l =>
    match l.splitOn "--" with
    | [] => l
    | h :: _ => h)

private def openers : List Char := ['(', '[', '{', '⟨']
private def closers : List Char := [')', ']', '}', '⟩']

/-- The declaration's statement: its text up to the proof. The proof begins
    at the first `:=` or `where` occurring outside every bracket, so named
    arguments like `(R := k)` — always parenthesised — do not end it. -/
private def signature (decl : String) : String := Id.run do
  let arr := (stripComments decl).toList.toArray
  let n := arr.size
  let mut depth : Int := 0
  let mut i := 0
  let mut acc : Array Char := #[]
  while i < n do
    let c := arr[i]!
    let mut stop := false
    if openers.contains c then depth := depth + 1
    else if closers.contains c then depth := depth - 1
    else if depth == 0 then
      if c == ':' && i + 1 < n && arr[i + 1]! == '=' then
        stop := true
      else if c == 'w' && i + 4 < n
          && arr[i + 1]! == 'h' && arr[i + 2]! == 'e'
          && arr[i + 3]! == 'r' && arr[i + 4]! == 'e'
          && (i == 0 || !arr[i - 1]!.isAlphanum)
          && (i + 5 >= n || !arr[i + 5]!.isAlphanum) then
        stop := true
    if stop then
      break
    acc := acc.push c
    i := i + 1
  return normalizeWs (String.ofList acc.toList)

def run (_args : List String) : IO UInt32 := do
  let files ← collectLean sourceRoot
  let mut pairs : Nat := 0
  let mut problems : Array String := #[]
  for f in files do
    let blocks := collectBlocks (← IO.FS.readFile f)
    for i in [0:blocks.size] do
      let some b := blocks[i]? | continue
      if b.kind != Kind.plain then continue
      -- A block without `sorry` is a worked model; nothing to pair.
      if (b.code.splitOn "sorry").length == 1 then continue
      -- The exercise is the last declaration carrying the `sorry`.
      let withSorry := (decls b.code).filter fun d =>
        (d.splitOn "sorry").length > 1
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
