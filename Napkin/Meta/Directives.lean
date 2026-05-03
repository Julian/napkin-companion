/-
Verso block / inline extensions for Napkin's structural callouts:
theorems, lemmas, definitions, examples, exercises, problems, asides,
remarks, abuses, prototypes, epigraphs, figures, and so on. Each
declares a `block_extension` (storing per-block data in JSON), a
`@[directive]` to invoke it from `:::DIRECTIVE` markup, and inline
HTML+CSS rendering.

Numbered callouts share a per-chapter counter assigned during the
traverse pass (see `assignCalloutNumber`) so cross-references like
"Theorem 4.5.2" stay consistent with Napkin's print numbering.
-/

import VersoManual
import Napkin.Meta.Lint
import Napkin.Meta.Citations
import Verso.Doc.ArgParse
import Verso.Doc.Elab
import Napkin.Bibliography

open Verso
open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean Elab

namespace Napkin

/-- Render a directive-title string, treating `$`…`` segments as
    inline math the way Verso does in body prose: emit
    `<code class="math inline">…</code>` so KaTeX picks it up.
    Plain text outside math is HTML-escaped via `.text true`.

    A title like `"$`\mathbb{R}` is complete"` produces
    `<code class="math inline">\mathbb{R}</code> is complete`,
    which KaTeX renders as `ℝ is complete` — instead of the literal
    backtick-laden text the previous behavior emitted. -/
def renderTitleMarkup (s : String) : Verso.Output.Html := Id.run do
  let parts := s.splitOn "$`"
  let mut out : Array Verso.Output.Html := #[]
  match parts with
  | [] => return .empty
  | first :: rest =>
    if !first.isEmpty then
      out := out.push (.text true first)
    for part in rest do
      match part.splitOn "`" with
      | [] => pure ()  -- unreachable: splitOn always returns a non-empty list
      | [_] =>
        -- No closing backtick — emit `$`<rest>` as literal text
        -- (degraded but visible) instead of swallowing the marker.
        out := out.push (.text true ("$`" ++ part))
      | math :: after =>
        let textAfter := "`".intercalate after
        out := out.push
          (.tag "code" #[("class", "math inline")] (.text true math))
        if !textAfter.isEmpty then
          out := out.push (.text true textAfter)
  if out.size = 1 then return out[0]!
  return .seq out

/-! ## Shared callout rendering helpers -/

/-- "Kind N" when the block has been assigned label `N`, else just "Kind".
    Numbered callouts feed this into the title formatters below. -/
def numberedKindLabel (kind : String) (label : String) : String :=
  if label.isEmpty then kind else s!"{kind} {label}"

/-- Title HTML for a callout whose label-and-title reads as
    "Kind N. *Title*" (theorem-, definition-, example-style). -/
def renderTitledLabel (kindLabel : String) (titleStr : String)
    : Verso.Output.Html :=
  if titleStr.isEmpty then
    .text true (kindLabel ++ ".")
  else
    .seq #[
      .text true (kindLabel ++ ". "),
      .tag "em" #[] (renderTitleMarkup titleStr)
    ]

/-- Title HTML for a callout whose label-and-title reads as
    "Kind N (Title). " (remark-, abuse-style; italic prefix folded
    into the body paragraph via CSS). -/
def renderParenLabel (kindLabel : String) (titleStr : String)
    : Verso.Output.Html :=
  if titleStr.isEmpty then
    .text true (kindLabel ++ ". ")
  else
    .seq #[
      .text true (kindLabel ++ " ("),
      renderTitleMarkup titleStr,
      .text true "). "
    ]

/-- `<div class="cls"><div class="cls-title">…</div>…</div>` wrapper
    used by box-style numbered callouts (Example, Definition, Exercise,
    Problem, Statement). `extraCls` is appended to the wrapper's class
    list (e.g. `"statement-theorem"`) but does not affect the inner
    title's class. -/
def renderBoxCallout (baseCls : String) (title : Verso.Output.Html)
    (body : Array Verso.Output.Html) (extraCls : String := "")
    : Verso.Output.Html :=
  let wrapperCls :=
    if extraCls.isEmpty then baseCls else s!"{baseCls} {extraCls}"
  .tag "div" #[("class", wrapperCls)]
    (.seq #[
      .tag "div" #[("class", baseCls ++ "-title")] title,
      .seq body
    ])

/-- `<div class="cls"><span class="cls-label">…</span>…</div>` wrapper
    used by inline-label callouts (Remark, Abuse). -/
def renderInlineLabelCallout (baseCls : String) (label : Verso.Output.Html)
    (body : Array Verso.Output.Html) : Verso.Output.Html :=
  .tag "div" #[("class", baseCls)]
    (.seq #[
      .tag "span" #[("class", baseCls ++ "-label")] label,
      .seq body
    ])

/-- N chili-pepper emoji as a string. -/
def chiliPeppers (n : Nat) : String :=
  String.ofList (List.replicate n '🌶')

/-- Read a string out of a JSON `data` payload, falling back to
    `default` when the data is not a string. Used by `block_extension`
    `toHtml` callbacks that store a single string in their `data` field. -/
private def dataStr (data : Lean.Json) (default : String := "") : String :=
  match data with | .str s => s | _ => default

/-! ## Shared "title-only" config

Most callouts (Example, Definition, Exercise, Aside, Remark, Abuse,
Statement) accept the same single optional positional title argument,
so they all use this one config + parser. Blocks that need additional
arguments (Problem, ChiliPara, Figure, ObjSvg, Epigraph) keep their
own. -/

structure TitledConfig where
  title : Option String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def TitledConfig.parse : ArgParse m TitledConfig :=
  TitledConfig.mk <$> ((some <$> .positional `title .string) <|> pure none)

instance : FromArgs TitledConfig m := ⟨TitledConfig.parse⟩

end

/-! ## Numbering for math callouts

Napkin numbers theorems, examples, definitions, and so on with a
shared per-chapter counter — "Theorem 1.1.1", "Example 1.1.2",
"Definition 1.1.3", … — so that cross-references like "by
Theorem 4.5.2" point unambiguously to a single numbered box.

To replicate that here we run a small assignment pass during
Verso's traverse phase. Each numbered block_extension calls
{name}`assignCalloutNumber` with its `InternalId`. That helper:

* finds the chapter prefix from `TraverseContext.sectionNumber`,
* increments a per-chapter counter stored under
  `Napkin.calloutCounters` in `TraverseState`, and
* records the resulting "1.2.3" label in
  `Napkin.calloutNumbers`, keyed by the block's `InternalId`.

Then the `toHtml` callbacks read the label back out via
{name}`lookupCalloutNumber` and prepend it to the kind label
("Theorem 1.2.3.").
-/

/-- Per-chapter counter, stored as a JSON object mapping
    chapter section-number strings (e.g. `"1.2."`) to the
    next-available counter value. -/
def calloutCounterKey : Lean.Name := `Napkin.calloutCounters
/-- Per-block assigned label, stored as a JSON object mapping
    `InternalId` (as a stringified Nat) to its assigned label
    (e.g. `"1.2.3"`). -/
def calloutNumberKey : Lean.Name := `Napkin.calloutNumbers

/-- Read a JSON value out of a TraverseState, returning an empty
    object `{}` when the key is absent or fails to deserialize. -/
private def stateJsonOr (st : Verso.Genre.Manual.TraverseState)
    (key : Lean.Name) : Lean.Json :=
  match st.get? (α := Lean.Json) key with
  | some (.ok v) => v
  | _ => Lean.Json.mkObj []

/-- Increment the chapter's callout counter and record the
    resulting "chapter.N" label for this block. No-ops if the
    block is outside any numbered section. -/
def assignCalloutNumber (blockId : Verso.Genre.Manual.InternalId)
    : ReaderT Verso.Genre.Manual.TraverseContext
        (StateT Verso.Genre.Manual.TraverseState IO) Unit := do
  let ctx ← read
  -- Take the first two numbered ancestors as the chapter prefix.
  -- For Napkin's part/chapter/section nesting that's "{part}.{chapter}";
  -- the within-chapter counter we maintain becomes the third
  -- component, matching Napkin's "1.2.3" convention regardless of
  -- which section the callout sits in.
  let sectionNums : Array Verso.Genre.Manual.Numbering :=
    ctx.sectionNumber.filterMap id
  if sectionNums.size < 2 then return
  let chapterPrefix := sectionNums.extract 0 2
  let chapterStr :=
    -- Drop the trailing "." that sectionNumberString appends so
    -- our final "{chapter}.{counter}" doesn't double up periods.
    let s := Verso.Genre.Manual.sectionNumberString chapterPrefix
    if s.endsWith "." then (s.dropEnd 1).toString else s
  let key := (Lean.toJson blockId).compress
  let st ← get
  let nums := stateJsonOr st calloutNumberKey
  -- Idempotency: Verso may run the traverse pass multiple times
  -- (e.g. to converge cross-references). If this block already has
  -- a label, leave it alone so the counter doesn't drift up.
  if (nums.getObjValAs? String key).toOption.isSome then return
  let counters := stateJsonOr st calloutCounterKey
  let cur : Nat := (counters.getObjValAs? Nat chapterStr).toOption.getD 0
  let next := cur + 1
  let counters' := counters.setObjVal! chapterStr (Lean.toJson next)
  let label := s!"{chapterStr}.{next}"
  let nums' := nums.setObjVal! key (Lean.toJson label)
  set ((st.set calloutCounterKey counters').set calloutNumberKey nums')

/-- Look up a previously-assigned "1.2.3" label for the block at
    `id`, returning `none` if the block was never assigned (e.g.
    appeared outside a numbered chapter). Reads `TraverseState`
    via the surrounding `HtmlT` context. -/
def lookupCalloutNumber {m : Type → Type} [Monad m]
    (blockId : Verso.Genre.Manual.InternalId)
    : Verso.Doc.Html.HtmlT Verso.Genre.Manual m (Option String) := do
  let st ← Verso.Doc.Html.HtmlT.state
  let key := (Lean.toJson blockId).compress
  return ((stateJsonOr st calloutNumberKey).getObjValAs? String key).toOption

block_extension Block.prototype where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="prototype">{{← content.mapM goB}}</div>}}
  extraCss := [r#"
    /* Prototype boxes are rendered in red per Napkin's convention:
       "I also often highlight a 'prototypical example' for some
       sections, and reserve the color red for such a note." */
    div.prototype {
      border-left: 4px solid #b03a2e;
      background: #fdf3f1;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
      color: #6e1f15;
    }
    div.prototype::before {
      content: "Prototypical example for this section:";
      font-weight: bold;
      color: #b03a2e;
      display: block;
      margin-bottom: 0.25em;
    }
    div.prototype > *:first-child,
    div.prototype::before + * { margin-top: 0; }
    div.prototype > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def PROTOTYPE : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.prototype #[$[$(← contents.mapM elabBlock)],*])

-- Embed an SVG as `<object>` rather than `<img>`. With <img>, links
-- and hover styling inside the SVG are inert; <object> loads the SVG
-- as a document so internal `<a>` and `:hover` work.
block_extension Block.objSvg (src : String) where
  data := .str src
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      pure {{
        <object class="napkin-svg" type="image/svg+xml"
                data={{dataStr data}}></object>
      }}
  extraCss := [r#"
    /* Break out of the 36rem text-measure so the diagram is readable.
       The page lays everything out within a narrow column; for a
       dense chart that becomes microscopic. We center via
       left:50%/translateX(-50%) and cap at 90vw. */
    /* Render the SVG at ~800px (modest 22% breakout past the 36rem
       text measure). The viewBox is set to ~600 so the browser
       scales it up by ~1.3×, making in-box text larger than the
       body font without inflating the layout. */
    object.napkin-svg {
      display: block;
      /* Stay within the parent section: the previous breakout via
         `left: 50%; translateX(-50%)` centered on the section, but
         with the ToC sidebar pushing the section to the right, the
         left edge of an 800px-wide SVG runs under the sidebar. */
      width: 100%;
      max-width: 800px;
      height: auto;
      /* `<object>` doesn't infer aspect ratio from the embedded SVG's
         viewBox the way `<img>` does, so `height: auto` collapses
         without an explicit ratio. Matches the chart's 646×562
         viewBox. */
      aspect-ratio: 646 / 562;
      margin: 1.25em auto;
    }
  "#]

structure ObjSvgConfig where
  src : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def ObjSvgConfig.parse : ArgParse m ObjSvgConfig :=
  ObjSvgConfig.mk <$> .positional `src .string

instance : FromArgs ObjSvgConfig m := ⟨ObjSvgConfig.parse⟩

end

@[directive]
def objSvg : DirectiveExpanderOf ObjSvgConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other (Block.objSvg $(quote cfg.src))
        #[$[$(← contents.mapM elabBlock)],*])

-- Title-page subtitle. Verso's `titlePage` renders <h1>, then
-- .authors, then intro children — so we emit a div with a
-- recognizable class and reorder via CSS to put it between the h1
-- and the authors block.
block_extension Block.subtitle where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="book-subtitle">{{← content.mapM goB}}</div>}}

@[directive]
def subtitle : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.subtitle
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.example (title : String) where
  data := .str title
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let titleStr := dataStr data
      let kindLabel := numberedKindLabel "Example"
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderBoxCallout "example"
              (renderTitledLabel kindLabel titleStr)
              (← content.mapM goB))
  extraCss := [r#"
    div.example {
      border: 1px solid #c8c8c8;
      background: #fafafa;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
    }
    div.example > div.example-title {
      font-weight: 700;
      margin-bottom: 0.4em;
      color: #2a2a2a;
    }
    div.example > div.example-title em {
      font-weight: 400;
    }
    div.example > div.example-title + * { margin-top: 0; }
    div.example > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def EXAMPLE : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.example $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.aside (title : String) where
  data := .str title
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let titleStr := dataStr data "Aside"
      pure {{
        <details class="aside">
          <summary>{{renderTitleMarkup titleStr}}</summary>
          <div class="aside-body">{{← content.mapM goB}}</div>
        </details>
      }}
  extraCss := [r#"
    details.aside {
      margin: 1.25em 0;
      border-left: 3px solid #aaa;
      background: #fafafa;
      border-radius: 3px;
    }
    details.aside > summary {
      cursor: pointer;
      font-variant: small-caps;
      letter-spacing: 0.04em;
      font-size: 0.9em;
      padding: 0.5em 0.75em;
      color: #555;
      list-style-position: inside;
    }
    details.aside > summary:hover {
      background: #f0f0f0;
    }
    details.aside[open] > summary {
      border-bottom: 1px solid #ddd;
    }
    details.aside > .aside-body {
      padding: 0.5em 0.75em;
    }
    details.aside > .aside-body > *:first-child { margin-top: 0; }
    details.aside > .aside-body > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def aside : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD "Aside"
    ``(Verso.Doc.Block.other (Block.aside $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.definition (title : String) where
  data := .str title
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let titleStr := dataStr data
      let kindLabel := numberedKindLabel "Definition"
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderBoxCallout "definition"
              (renderTitledLabel kindLabel titleStr)
              (← content.mapM goB))
  extraCss := [r#"
    div.definition {
      border-left: 4px solid #6a4ca0;
      background: #f7f4fa;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
    }
    div.definition > div.definition-title {
      font-weight: 700;
      margin-bottom: 0.4em;
      color: #4a3678;
    }
    div.definition > div.definition-title em {
      font-weight: 400;
    }
    div.definition > div.definition-title + * { margin-top: 0; }
    div.definition > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def DEFINITION : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.definition $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.remark (title : String) where
  data := .str title
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let titleStr := dataStr data
      let kindLabel := numberedKindLabel "Remark"
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderInlineLabelCallout "remark"
              (renderParenLabel kindLabel titleStr)
              (← content.mapM goB))
  extraCss := [r#"
    div.remark {
      margin: 1em 0;
    }
    div.remark > span.remark-label {
      font-style: italic;
      font-weight: 600;
    }
    div.remark > span.remark-label + p {
      display: inline;
    }
    div.remark > *:first-child { margin-top: 0; }
    div.remark > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def REMARK : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.remark $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.figure (src : String) where
  data := .str src
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      pure {{
        <figure class="napkin-figure">
          <img src={{dataStr data}} alt=""/>
          <figcaption>{{← content.mapM goB}}</figcaption>
        </figure>
      }}
  extraCss := [r#"
    figure.napkin-figure {
      margin: 1.25em 0;
      text-align: center;
    }
    figure.napkin-figure > img {
      max-width: 100%;
      height: auto;
    }
    figure.napkin-figure > figcaption {
      font-size: 0.92em;
      color: #555;
      margin-top: 0.5em;
      text-align: center;
    }
  "#]

structure FigureConfig where
  src : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `src .string

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩

end

@[directive]
def figure : DirectiveExpanderOf FigureConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other (Block.figure $(quote cfg.src))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.exercise (title : String) where
  data := .str title
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let titleStr := dataStr data
      let kindLabel := numberedKindLabel "Exercise"
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderBoxCallout "exercise"
              (renderTitledLabel kindLabel titleStr)
              (← content.mapM goB))
  extraCss := [r#"
    div.exercise {
      border: 1px solid #d6c8a0;
      background: #fef9ec;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
    }
    div.exercise > div.exercise-title {
      font-weight: 700;
      margin-bottom: 0.4em;
      color: #6b4a00;
    }
    div.exercise > div.exercise-title em {
      font-weight: 400;
    }
    div.exercise > div.exercise-title + * { margin-top: 0; }
    div.exercise > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def EXERCISE : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.exercise $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

-- Shared "statement" block: theorem/lemma/proposition/corollary/fact all
-- use this with a different `kind` label.
block_extension Block.statement (kind : String) (title : String) where
  data := .arr #[.str kind, .str title]
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let (kindStr, titleStr) : String × String :=
        match data with
        | .arr #[.str k, .str t] => (k, t)
        | _ => ("Statement", "")
      let kindLabel := numberedKindLabel kindStr
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderBoxCallout "statement"
              (renderTitledLabel kindLabel titleStr)
              (← content.mapM goB)
              (extraCls := "statement-" ++ kindStr.toLower))
  extraCss := [r#"
    /* Shared box for theorem/lemma/proposition/corollary; FACT has its
       own minimal treatment below. The kind class (statement-theorem,
       statement-lemma, ...) sets the border-left color so the family
       reads as related but distinguishable at a glance. */
    div.statement {
      border-left: 4px solid #2a5a8a;
      background: #f4f8fc;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
    }
    div.statement > div.statement-title {
      font-weight: 700;
      margin-bottom: 0.4em;
      color: #1f4a6a;
    }
    div.statement > div.statement-title em {
      font-weight: 400;
    }
    div.statement > div.statement-title + * { margin-top: 0; }
    div.statement > *:last-child { margin-bottom: 0; }

    /* Theorem: the canonical blue, full panel. */
    div.statement-theorem    { border-left-color: #2a5a8a; }
    /* Lemma: teal, marking it as a supporting result. */
    div.statement-lemma      { border-left-color: #2a7a7a; }
    div.statement-lemma > div.statement-title { color: #1f5a5a; }
    /* Proposition: slate, between theorem and lemma in weight. */
    div.statement-proposition { border-left-color: #4a6a8a; }
    div.statement-proposition > div.statement-title { color: #2a4a6a; }
    /* Corollary: thinner border, slightly indented — visually
       "follows from" something else. */
    div.statement-corollary {
      border-left-width: 2px;
      border-left-color: #6a7a4a;
      margin-left: 1em;
    }
    div.statement-corollary > div.statement-title { color: #4a5a2a; }
    /* Fact: no panel, just a bold inline label — declarative aside. */
    div.statement-fact {
      border: none;
      background: none;
      padding: 0;
      margin: 1em 0;
      border-radius: 0;
    }
    div.statement-fact > div.statement-title {
      display: inline;
      margin-right: 0.4em;
      color: inherit;
    }
    div.statement-fact > div.statement-title + p {
      display: inline;
    }
  "#]

@[directive]
def THEOREM : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.statement "Theorem" $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def LEMMA : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.statement "Lemma" $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def PROPOSITION : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.statement "Proposition" $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def COROLLARY : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.statement "Corollary" $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

@[directive]
def FACT : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.statement "Fact" $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

-- Lightweight "abuse of notation" callout.
block_extension Block.abuse (title : String) where
  data := .str title
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let titleStr := dataStr data
      let kindLabel := numberedKindLabel "Abuse of notation"
        ((← lookupCalloutNumber blockId).getD "")
      pure (renderInlineLabelCallout "abuse"
              (renderParenLabel kindLabel titleStr)
              (← content.mapM goB))
  extraCss := [r#"
    div.abuse {
      margin: 1em 0;
      padding-left: 0.75em;
      border-left: 2px dotted #888;
    }
    /* Inline label rendered as the first child of the block; the
       following <p> picks up next to it via display:inline on the
       label and a small right margin. */
    div.abuse > span.abuse-label {
      font-style: italic;
      font-weight: 600;
    }
    /* Fold the label into the first paragraph visually. */
    div.abuse > span.abuse-label + p {
      display: inline;
    }
    div.abuse > *:first-child { margin-top: 0; }
    div.abuse > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def ABUSE : DirectiveExpanderOf TitledConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other (Block.abuse $(quote title))
        #[$[$(← contents.mapM elabBlock)],*])

-- Proof block, with a "Proof." prefix and a small QED marker on the
-- last paragraph.
block_extension Block.proof where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{
        <div class="proof">{{← content.mapM goB}}</div>
      }}
  extraCss := [r#"
    div.proof {
      margin: 1em 0 1.25em 0;
    }
    div.proof > p:first-of-type::before {
      content: "Proof. ";
      font-style: italic;
      font-weight: 600;
    }
    div.proof > p:last-of-type::after {
      content: " \220E";
      font-weight: 700;
      margin-left: 0.3em;
    }
    div.proof > *:first-child { margin-top: 0; }
    div.proof > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def PROOF : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.proof
        #[$[$(← contents.mapM elabBlock)],*])

-- A `:::chiliPara (chili := N)` block renders its content as a
-- normal paragraph but with N chili peppers floated in the left
-- whitespace margin, matching Napkin's `\onechili` / `\twochili`
-- / `\threechili` paragraph markers (which render in the LaTeX
-- `\marginpar`).
block_extension Block.chiliPara (chili : Nat) where
  data := .num (.fromNat chili)
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let chiliN : Nat :=
        match data with
        | .num n => n.toFloat.toUInt32.toNat
        | _ => 0
      pure {{
        <div class="chili-para">
          <span class="chili-marker"
                title={{s!"Difficulty: {chiliN}/3"}}>
            {{.text true (chiliPeppers chiliN)}}
          </span>
          {{← content.mapM goB}}
        </div>
      }}
  extraCss := [r#"
    div.chili-para {
      position: relative;
      margin: 1em 0;
    }
    div.chili-para > .chili-marker {
      position: absolute;
      /* Anchor the marker at the section's left edge by negating the
         list indentation that paragraphs inside a `<ul>` inherit, so
         the chili sits in the left page-margin whitespace next to the
         body text — matching Napkin's `\reversemarginpar` placement
         in the LaTeX rendering. */
      right: 100%;
      top: 0.1em;
      margin-right: 5rem;
      font-size: 1.1em;
      letter-spacing: 0.05em;
      white-space: nowrap;
      user-select: none;
    }
    /* On phones there is no left whitespace margin to float into,
       so fall back to inline placement. */
    @media screen and (max-width: 700px) {
      div.chili-para > .chili-marker {
        position: static;
        margin-right: 0.4em;
        font-size: 1em;
      }
    }
    div.chili-para > *:first-child:not(.chili-marker) {
      margin-top: 0;
    }
    div.chili-para > *:last-child {
      margin-bottom: 0;
    }
  "#]

structure ChiliParaConfig where
  chili : Nat

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def ChiliParaConfig.parse : ArgParse m ChiliParaConfig :=
  ChiliParaConfig.mk <$> .namedD `chili .nat 1

instance : FromArgs ChiliParaConfig m := ⟨ChiliParaConfig.parse⟩

end

@[directive]
def chiliPara : DirectiveExpanderOf ChiliParaConfig
  | cfg, contents => do
    ``(Verso.Doc.Block.other (Block.chiliPara $(quote cfg.chili))
        #[$[$(← contents.mapM elabBlock)],*])

block_extension Block.question where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="question">{{← content.mapM goB}}</div>}}
  extraCss := [r#"
    div.question {
      margin: 1em 0;
    }
    div.question > p:first-of-type::before {
      content: "Question. ";
      font-style: italic;
      font-weight: 600;
    }
    div.question > *:first-child { margin-top: 0; }
    div.question > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def QUESTION : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.question
        #[$[$(← contents.mapM elabBlock)],*])

-- A problem's `chili` count (0–3) controls a difficulty marker shown
-- next to the "Problem." label. Matches Napkin's `\onechili`,
-- `\twochili`, `\threechili` annotations.
block_extension Block.problem (title : String) (chili : Nat) where
  data := .arr #[.str title, .num (.fromNat chili)]
  traverse blockId _ _ := do assignCalloutNumber blockId; return none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    some <| fun _ goB blockId data content => do
      let (titleStr, chiliN) : String × Nat :=
        match data with
        | .arr #[.str s, .num n] => (s, n.toFloat.toUInt32.toNat)
        | _ => ("", 0)
      let chiliHtml : Verso.Output.Html :=
        if chiliN == 0 then .seq #[]
        else .tag "span"
          #[("class", "problem-chili"),
            ("title", s!"Difficulty: {chiliN}/3")]
          (.text true (chiliPeppers chiliN))
      let kindLabel := numberedKindLabel "Problem"
        ((← lookupCalloutNumber blockId).getD "")
      let baseTitle := renderTitledLabel kindLabel titleStr
      let titleHtml :=
        if chiliN == 0 then baseTitle else .seq #[baseTitle, chiliHtml]
      pure (renderBoxCallout "problem" titleHtml (← content.mapM goB))
  extraCss := [r#"
    div.problem {
      border-left: 3px solid #8a4a4a;
      background: #fdf5f5;
      padding: 0.75em 1em;
      margin: 1.25em 0;
      border-radius: 3px;
    }
    div.problem > div.problem-title {
      font-weight: 700;
      margin-bottom: 0.4em;
      color: #6a2a2a;
    }
    div.problem > div.problem-title em {
      font-weight: 400;
    }
    div.problem > div.problem-title .problem-chili {
      margin-left: 0.5em;
      font-size: 0.9em;
      letter-spacing: 0.05em;
      vertical-align: 0.05em;
    }
    div.problem > div.problem-title + * { margin-top: 0; }
    div.problem > *:last-child { margin-bottom: 0; }
  "#]

structure ProblemConfig where
  title : Option String
  chili : Nat

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def ProblemConfig.parse : ArgParse m ProblemConfig :=
  ProblemConfig.mk
    <$> ((some <$> .positional `title .string) <|> pure none)
    <*> .namedD `chili .nat 0

instance : FromArgs ProblemConfig m := ⟨ProblemConfig.parse⟩

end

@[directive]
def PROBLEM : DirectiveExpanderOf ProblemConfig
  | cfg, contents => do
    let title := cfg.title.getD ""
    ``(Verso.Doc.Block.other
        (Block.problem $(quote title) $(quote cfg.chili))
        #[$[$(← contents.mapM elabBlock)],*])

-- Title-page-style epigraph: pull quote with attribution. The
-- optional `cite` arg, if provided, renders a bibliography-linked
-- short label (e.g. `[Vakil]`) immediately after the attribution.
block_extension Block.epigraph (attribution : String) (citeKey : String) where
  data := .arr #[.str attribution, .str citeKey]
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ data content => do
      let (attr, cite) : String × String :=
        match data with
        | .arr #[.str a, .str c] => (a, c)
        | _ => ("", "")
      let citeHtml : Verso.Output.Html :=
        if cite.isEmpty then .seq #[]
        else .seq #[.text true " ", renderCiteRef cite]
      let attribHtml : Verso.Output.Html :=
        if attr.isEmpty && cite.isEmpty then .seq #[]
        else .tag "div"
              #[("class", "epigraph-attribution")]
              (.seq #[.text true ("— " ++ attr), citeHtml])
      pure {{
        <blockquote class="epigraph">
          {{← content.mapM goB}}
          {{attribHtml}}
        </blockquote>
      }}

structure EpigraphConfig where
  attribution : Option String
  cite : Option String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m] [MonadFileMap m]

def EpigraphConfig.parse : ArgParse m EpigraphConfig :=
  EpigraphConfig.mk
    <$> ((some <$> .positional `attribution .string) <|> pure none)
    <*> .named `cite .string true

instance : FromArgs EpigraphConfig m := ⟨EpigraphConfig.parse⟩

end

@[directive]
def epigraph : DirectiveExpanderOf EpigraphConfig
  | cfg, contents => do
    let attr := cfg.attribution.getD ""
    let cite := cfg.cite.getD ""
    ``(Verso.Doc.Block.other (Block.epigraph $(quote attr) $(quote cite))
        #[$[$(← contents.mapM elabBlock)],*])

-- Napkin's `\begin{moral}` callout. Rendered as a green-tinted box,
-- matching the printed book — no "Moral." label. The italic context
-- comes from the original `\begin{moral}` styling.
block_extension Block.moral where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<div class="moral">{{← content.mapM goB}}</div>}}
  extraCss := [r#"
    div.moral {
      margin: 1.25em 0;
      padding: 0.75em 1em;
      background: #eaf3ea;
      border-left: 3px solid #5a8a5a;
      border-radius: 3px;
      font-style: italic;
    }
    /* nested italic in an italic block flips back to upright,
       matching LaTeX \emph behavior */
    div.moral em { font-style: normal; }
    div.moral > *:first-child { margin-top: 0; }
    div.moral > *:last-child { margin-bottom: 0; }
  "#]

@[directive]
def MORAL : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.moral
        #[$[$(← contents.mapM elabBlock)],*])

-- Multi-paragraph block quote. Each `> line` in Verso markup parses as
-- its own `<blockquote>`, so for an extended quotation we group the
-- paragraphs explicitly.
block_extension Block.quote where
  traverse _ _ _ := pure none
  toTeX :=
    some <| fun _ goB _ _ content => do
      content.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      pure {{<blockquote>{{← content.mapM goB}}</blockquote>}}

@[directive]
def quote : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.quote
        #[$[$(← contents.mapM elabBlock)],*])
