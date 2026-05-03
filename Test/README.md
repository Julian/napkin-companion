# Tests

`lake test` runs every registered test and exits nonzero on any
failure. The dispatcher lives in `Test/Main.lean`; individual tests
are sibling modules.

## Running

| Command | Behavior |
| --- | --- |
| `lake test` | Run every test. |
| `lake test -- --only=<name>` | Run only the named test (helpful while iterating). |
| `lake test -- --update` | Generic flag forwarded to every test. |
| `lake test -- <name>:<flag>` | Forward `<flag>` only to the test named `<name>` (e.g. `check-fixture:--update`). |

## Registered tests

### `check-fixture`

Render-diff regression check for `Napkin.Meta.Directives`. Builds
`Test.Fixture` (a self-contained Verso doc that exercises every
directive) and diffs the rendered HTML against the committed golden
files in `Test/fixtures/`.

| Flag | Behavior |
| --- | --- |
| (default) | Diff against the golden; nonzero exit on drift. |
| `--update` | Overwrite the golden with freshly-rendered output. **Review the diff before committing.** |

When the check fails, the report prints a unified-diff window
(3 lines of context on each side) around the first divergence, and
the full `diff` command for deeper investigation.

#### Coverage

`Test/Fixture.lean` exercises every conditional branch in the
shared rendering helpers:

- `numberedKindLabel`: callouts inside a numbered chapter (label
  assigned) and outside (no label).
- `renderTitledLabel` / `renderParenLabel`: empty-title and
  non-empty-title cases.
- `renderTitleMarkup`: plain text, single math segment, multiple
  math segments, unclosed math.
- `renderBoxCallout` with `extraCls`: every Statement variant
  (Theorem / Lemma / Proposition / Corollary / Fact).
- `chiliPeppers`: 0, 1, 2, 3.
- `renderCiteRef`: known and unknown bibliography keys.
- `epigraph`: with cite, attribution-only, neither.

#### Adding fixture coverage

If a new directive (or a new branch in an existing directive)
should be covered:

1. Edit `Test/Fixture.lean` to use it.
2. Run `lake test -- check-fixture:--update` to regenerate the
   golden, and review the diff.
3. Commit the updated golden alongside the directive change.

## Adding a new test

1. Define `<YourTest>.run : List String → IO UInt32` in a new
   module under `Test/`.
2. Import that module in `Test/Main.lean`.
3. Append a `Test.Entry` to `tests` there.

The runner forwards generic args to every test and `<name>:<flag>`-prefixed
args only to the matching test, so per-test flags compose without
collisions.
