/-
Test runner. Dispatches to each registered test in sequence and
aggregates exit codes. Wired up as the package's `testDriver`, so
`lake test` runs everything here.

Argument routing:

* An arg of the form `<test-name>:<flag>` is forwarded only to the
  named test, with the prefix stripped (e.g. `check-fixture:--update`
  passes `--update` to `check-fixture` only).
* An arg with no `<test-name>:` prefix goes to every test (so a
  test that doesn't recognize it should ignore it).
* `--only=<test-name>` filters which tests run; only matching tests
  are dispatched (useful for iterating on one test without rerunning
  the rest).

To add a new test:

  1. Define `<YourTest>.run : List String → IO UInt32` in a new module.
  2. Import that module below.
  3. Append a `TestEntry` to `tests`.
-/

import Test.CheckFixture

namespace Test

structure Entry where
  /-- User-facing name; matches `<name>:` arg prefixes and `--only=`. -/
  name : String
  /-- Test runner. Returns 0 on pass, nonzero on failure. -/
  run : List String → IO UInt32

/-- The list of registered tests. Order is the run order. -/
def tests : List Entry := [
  { name := "check-fixture", run := Test.CheckFixture.run }
]

/-- Prefixes of args consumed by the dispatcher itself. These are
    filtered out before any test sees its argument list, so a test
    that wants to define its own `--only=` (or any flag listed here)
    can do so without a name clash. -/
def dispatcherFlagPrefixes : List String := ["--only="]

/-- Filter `args` to those that should be passed to the test named
    `forName`, given the full set of registered test names.

    * Dispatcher-owned flags (see `dispatcherFlagPrefixes`) are dropped.
    * `<name>:<rest>` is targeted: kept (with prefix stripped) iff
      `name == forName`.
    * Other args go to every test. -/
def argsFor (forName : String) (allNames : List String) (args : List String)
    : List String :=
  args.filterMap fun a =>
    if dispatcherFlagPrefixes.any (a.startsWith ·) then none
    else
      match allNames.find? (fun (n : String) => a.startsWith s!"{n}:") with
      | some target =>
        if target == forName then some ((a.drop (target.length + 1)).toString)
        else none
      | none => some a

/-- Parse a `--only=<name>` flag (last one wins if repeated). -/
def parseOnly (args : List String) : Option String :=
  args.foldl (init := none) fun acc a =>
    if a.startsWith "--only=" then some (a.drop "--only=".length).toString
    else acc

end Test

def main (args : List String) : IO UInt32 := do
  let allNames := Test.tests.map (·.name)
  let only? := Test.parseOnly args
  let toRun : List Test.Entry := match only? with
    | some n => Test.tests.filter fun e => e.name == n
    | none => Test.tests
  if toRun.isEmpty then
    IO.eprintln s!"No tests matched --only={only?.getD ""}."
    IO.eprintln s!"Registered tests: {", ".intercalate allNames}"
    return 1
  let mut failed : Nat := 0
  for t in toRun do
    IO.println s!"=== {t.name} ==="
    let testArgs := Test.argsFor t.name allNames args
    if (← t.run testArgs) != 0 then failed := failed + 1
  IO.println ""
  if failed != 0 then
    IO.eprintln s!"{failed} of {toRun.length} test(s) failed."
    return 1
  IO.println s!"All {toRun.length} test(s) passed."
  return 0
