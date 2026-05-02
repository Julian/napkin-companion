import Std.Data.HashMap
import VersoManual
import Napkin

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Napkin

-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

/--
Extract the marked exercises and example code.
-/
partial def buildExercises (mode : Mode) (logError : String → IO Unit) (cfg : Config) (_state : TraverseState) (text : Part Manual) : IO Unit := do
  let .multi := mode
    | pure ()
  let code := (← part text |>.run {}).snd
  let dest := cfg.destination / "example-code"
  let some mainDir := mainFileName.parent
    | throw <| IO.userError "Can't find directory of `Render.lean`"

  IO.FS.createDirAll <| dest
  for ⟨fn, f⟩ in code do
    if let some fn' := fn.dropPrefix? mainDir.toString then
      let fn' := fn'.toString.dropWhile (· ∈ System.FilePath.pathSeparators : Char → Bool)
      let fn := dest / fn'.copy
      fn.parent.forM IO.FS.createDirAll
      if (← fn.pathExists) then IO.FS.removeFile fn
      IO.FS.writeFile fn f
    else
      logError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."

where
  part : Part Manual → StateT (HashMap String String) IO Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT (HashMap String String) IO Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | logError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | logError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          let prior := saved[fn]?.getD ""
          saved.insert fn (code.trimAsciiEnd.copy ++ "\n" ++ prior)

      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()


def napkinTypographyCSS : String := r#"
:root {
  --verso-text-font-family: "Bitter", "Charter", "Georgia", "Cambria", serif;
  --verso-structure-font-family: "Bitter", "Charter", "Georgia", "Cambria", serif;
  --verso-code-font-family: "JetBrains Mono", "SF Mono", "Menlo", "Consolas", "DejaVu Sans Mono", monospace;
  --verso-text-color: #1a1a1a;
  --verso-font-size: 18px;
  --verso-mobile-font-size: 17px;
  --verso-content-max-width: 36rem;
  --napkin-link-color: #2a5a8a;
  --napkin-code-bg: #eef0f2;
  --napkin-block-bg: #f7f7f5;
  --napkin-block-border: #c8c8c8;
}

body {
  font-family: var(--verso-text-font-family);
  color: var(--verso-text-color);
  line-height: 1.5;
}

/* Constrain measure to ~65 characters. The variable above flows through
   book.css's `main section { max-width: var(--verso-content-max-width) }`. */
main section, main .content-wrapper {
  max-width: var(--verso-content-max-width);
}

main h1, main h2, main h3, main h4 {
  font-family: var(--verso-structure-font-family);
  margin-top: 1.6em;
  margin-bottom: 0.5em;
}
/* H1 (chapter titles) takes Butterick's light-weight + small-caps
   treatment: size and small-caps carry the hierarchy, so the weight
   can drop to 300. Slightly more letter-spacing because small caps
   read better with a touch of extra tracking. */
main h1 {
  font-size: 1.9rem;
  font-weight: 300;
  font-variant-caps: all-small-caps;
  letter-spacing: 0.04em;
}
main h2 { font-size: 1.35rem; font-weight: 700; }
main h3 { font-size: 1.12rem; font-weight: 600; }
main h4 { font-weight: 600; }

/* Inline code (in prose) — distinct chip without competing with math. */
code:not(.math) {
  background: var(--napkin-code-bg);
  color: #2a2a2a;
  padding: 0.1em 0.3em;
  border-radius: 3px;
  font-size: 0.92em;
}

code.math.inline, code.math.display {
  background: none;
  padding: 0;
}

/* Inline math must never wrap mid-equation. */
code.math.inline, .katex {
  white-space: nowrap;
}

/* Display math: centered standalone block, breathing room above/below. */
code.math.display {
  display: block;
  text-align: center;
  margin: 1em 0;
}
code.math.display, code.math.display .katex {
  white-space: normal;
}

/* But when display math sits inside a list item, centering makes it
   appear shifted right of page center — keep it left-aligned there. */
li code.math.display {
  text-align: left;
  margin: 0.5em 0;
}

/* Lean code blocks — give them a quiet panel so they read as code, not
   as accidentally-indented prose. */
code.hl.lean.block {
  display: block;
  background: var(--napkin-block-bg);
  border-left: 3px solid var(--napkin-block-border);
  padding: 0.75em 1em;
  margin: 1.25em 0;
  font-family: var(--verso-code-font-family);
  font-size: 0.9em;
  line-height: 1.5;
  border-radius: 3px;
  overflow-x: auto;
}

/* Lists: book.css already gives 0.5rem between siblings; just enable
   harmonious spacing for the example callouts where bullets matter. */
main section ul > li, main section ol > li {
  margin: 0.4em 0;
}

/* Block quotes (Butterick): indented both sides, no border, slightly
   smaller text, upright (italics are for emphasis, not for long
   passages). One paragraph of margin separates internal paragraphs. */
main blockquote {
  margin: 1.25em 2em;
  padding: 0;
  border: none;
  text-align: justify;
  hyphens: auto;
  color: #2a2a2a;
  font-size: 0.95em;
}
main blockquote > p {
  margin: 0.5em 0;
}
main blockquote > p:first-child { margin-top: 0; }
main blockquote > p:last-child  { margin-bottom: 0; }

/* Title-page cover artwork: emulates the LaTeX `\fbox{\fboxrule=4pt}`
   black-bordered image at the top of the book, constrained to the
   text measure rather than the wider content-wrapper. */
img[src$="cover-art.jpg"] {
  display: block;
  width: 100%;
  max-width: var(--verso-content-max-width);
  height: auto;
  border: 4px solid #000;
  margin: 2em auto;
  box-sizing: border-box;
}

/* Title-page layout: Verso renders <h1>, then <div class="authors">
   (which contains the authorshipNote as <p class="note">), then any
   intro children. We use flex order so the subtitle sits between the
   h1 and the authors block. */
.titlepage {
  display: flex;
  flex-direction: column;
}
.titlepage > h1                 { order: 1; margin-bottom: 0.25em; }
.titlepage > .book-subtitle     { order: 2; }
.titlepage > .authors           { order: 3; }
.titlepage > *                  { order: 4; }

.book-subtitle {
  font-style: italic;
  font-size: 1.25em;
  color: #555;
  margin: 0 0 2em 0;
  text-align: center;
}
.book-subtitle > p { margin: 0; }

.titlepage > .authors {
  text-align: center;
  margin-top: 0;
}
.titlepage > .authors > .author {
  font-size: 1.1em;
  font-weight: 500;
}
.titlepage > .authors > .note {
  display: block;
  margin: 1.5em 0 0 0;
  font-size: 0.85em;
  color: #666;
  font-style: italic;
  font-weight: 400;
}
/* Verso's default `main .authors:has(.author) .note::before { content: ", " }`
   inlines the note after the author name with a comma. We render the
   note on its own line, so suppress it. The leading `main` matches
   Verso's specificity (otherwise we'd lose). */
main .titlepage > .authors > .note::before { content: ""; }

/* Hide the "Colophon" h1 on its own page. The page is unlabeled
   intentionally — its content (Vakil quote, copyright, etc.) speaks
   for itself, and "Colophon" as a heading would be redundant.
   (No Verso metadata flag for suppressing a part's title; CSS is the
   only available knob.) */
main section:has(> h1 a[href*="--Colophon"]) > h1 { display: none; }

/* Ko-fi support badge on the Colophon page. */
img[src$="kofi4.png"] {
  display: block;
  max-width: 200px;
  height: auto;
  margin: 1em auto;
}
img[src$="kofi4.png"] + * { margin-top: 1em; }

/* Hide the Colophon entry from the sidebar TOC. The prev/next nav
   still links to it so the title page has a working "next" button —
   the page is reachable, just not listed in the sidebar contents. */
.split-toc tr:has(a[href$="--Colophon"]),
.split-toc tr:has(a[href*="/Colophon/"]) { display: none; }

/* Title-page-style epigraph. The original Napkin gives the Vakil
   quote roughly half a printed page; we approximate that with
   generous vertical breathing room, larger italic text, and a thin
   rule below to separate it from the colophon body. */
.epigraph {
  margin: 4em auto 4em auto;
  max-width: 32rem;
  text-align: right;
  font-style: italic;
  color: #333;
  font-size: 1.25em;
  line-height: 1.55;
  border: none;
  padding: 2em 0 3em 0;
  border-bottom: 1px solid #ddd;
  min-height: 40vh;
  display: flex;
  flex-direction: column;
  justify-content: center;
}
.epigraph > p {
  margin: 0.3em 0;
}
.epigraph > .epigraph-attribution {
  font-style: normal;
  font-size: 0.78em;
  color: #666;
  margin-top: 1.2em;
  letter-spacing: 0.02em;
}

/* Selection / focus / link accents. */
main a {
  color: var(--napkin-link-color);
  text-underline-offset: 2px;
}
::selection {
  background: #fde68a;
  color: inherit;
}
:focus-visible {
  outline: 2px solid var(--napkin-link-color);
  outline-offset: 2px;
}

/* Tighter table spacing. Verso's default `border-spacing: 1rem`
   leaves too much vertical air between rows; the printed book uses
   roughly the same vertical density as body text. */
table.tabular {
  border-spacing: 0.6rem 0.15rem;
}
table.tabular td,
table.tabular th {
  padding: 0.05em 0;
}

/* Footnotes-as-tooltips. Verso renders `{margin}[...]` notes as
   `<span class="marginalia"><span class="note">…</span></span>`,
   inline on narrow viewports and floated into the right margin at
   ≥1400px. We override that to render the note as a hover/focus
   tooltip with a small dagger marker, so the right margin stays
   reserved for genuinely-prominent `:::aside` blocks. */
.marginalia {
  position: relative;
  display: inline;
  /* Prevent the underlying note text from showing as plain inline
     content if the tooltip styles fail to load. */
  cursor: help;
}

/* Visible dagger marker after the preceding word, sized as a small
   superscript. Hover/focus turns it darker. */
.marginalia::after {
  content: "†";
  font-size: 0.85em;
  vertical-align: super;
  color: #b78c20;
  margin-left: 0.05em;
  font-weight: 600;
}
.marginalia:hover::after,
.marginalia:focus-within::after {
  color: #8a5a00;
}

/* The actual note: hidden by default; shown as a popover on hover
   or keyboard focus. Override Verso's float/inline rules at every
   breakpoint with `!important` so the tooltip behaviour is
   uniform. */
.marginalia .note {
  position: absolute;
  bottom: calc(100% + 0.4rem);
  left: 50%;
  transform: translateX(-50%);
  z-index: 50;
  width: max-content;
  max-width: min(22rem, 80vw);
  padding: 0.6rem 0.8rem;
  /* Solid background; `!important` overrides Verso's `:hover .note`
     rule, which otherwise paints the tooltip transparent on hover
     (when its accent-color variable is undefined). */
  background: #fffaf0 !important;
  color: var(--verso-text-color, #1a1a1a);
  border: 1px solid #d8c890;
  border-radius: 4px;
  box-shadow: 0 3px 12px rgba(0, 0, 0, 0.12);
  font-size: 0.88rem;
  font-style: normal;
  line-height: 1.45;
  text-align: left;
  visibility: hidden;
  opacity: 0;
  /* Delay visibility on fade-out so the tooltip stays around long
     enough for the cursor to enter it. */
  transition: opacity 0.15s ease, visibility 0s linear 0.15s;
  /* Override Verso's wide-viewport float-right rules. */
  float: none !important;
  margin: 0 !important;
}
@media (max-width: 700px) {
  .marginalia .note {
    max-width: 88vw;
  }
}

.marginalia:hover .note,
.marginalia:focus-within .note,
.marginalia:focus .note,
.marginalia .note:hover {
  visibility: visible;
  opacity: 1;
  transition: opacity 0.15s ease;
}

/* Suppress Verso's hover-highlight background on the marker
   (outer .marginalia) only — keep the inner .note's solid
   background so the tooltip remains readable on hover. */
.marginalia:hover {
  background-color: transparent;
}
"#

/-- Self-hosted Bitter and JetBrains Mono. The woff2 files live in
the repo's `fonts/` directory, copied to the output via
`extraFiles`. Both are SIL Open Font License. Subsetted to latin and
latin-ext (sufficient for English plus diacritics in author names). -/
def napkinFontsCSS : String := r#"
@font-face {
  font-family: 'Bitter';
  font-style: italic;
  font-weight: 100 900;
  font-display: swap;
  src: url(fonts/bitter-italic-latin.woff2) format('woff2');
  unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
}
@font-face {
  font-family: 'Bitter';
  font-style: italic;
  font-weight: 100 900;
  font-display: swap;
  src: url(fonts/bitter-italic-latin-ext.woff2) format('woff2');
  unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF;
}
@font-face {
  font-family: 'Bitter';
  font-style: normal;
  font-weight: 100 900;
  font-display: swap;
  src: url(fonts/bitter-latin.woff2) format('woff2');
  unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
}
@font-face {
  font-family: 'Bitter';
  font-style: normal;
  font-weight: 100 900;
  font-display: swap;
  src: url(fonts/bitter-latin-ext.woff2) format('woff2');
  unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF;
}
@font-face {
  font-family: 'JetBrains Mono';
  font-style: normal;
  font-weight: 100 800;
  font-display: swap;
  src: url(fonts/jetbrains-mono-latin.woff2) format('woff2');
  unicode-range: U+0000-00FF, U+0131, U+0152-0153, U+02BB-02BC, U+02C6, U+02DA, U+02DC, U+0304, U+0308, U+0329, U+2000-206F, U+20AC, U+2122, U+2191, U+2193, U+2212, U+2215, U+FEFF, U+FFFD;
}
@font-face {
  font-family: 'JetBrains Mono';
  font-style: normal;
  font-weight: 100 800;
  font-display: swap;
  src: url(fonts/jetbrains-mono-latin-ext.woff2) format('woff2');
  unicode-range: U+0100-02BA, U+02BD-02C5, U+02C7-02CC, U+02CE-02D7, U+02DD-02FF, U+0304, U+0308, U+0329, U+1D00-1DBF, U+1E00-1E9F, U+1EF2-1EFF, U+2020, U+20A0-20AB, U+20AD-20C0, U+2113, U+2C60-2C7F, U+A720-A7FF;
}
"#

-- Verso's stylesheet collapses the ToC into a burger-menu drawer
-- only at viewports ≤700px. We extend that behaviour up to 1500px
-- so the always-visible ToC only appears at large-desktop widths
-- where it doesn't compete with body text or left-margin annotations
-- (chili peppers etc.) for horizontal space. Mirrors the rules Verso
-- applies at `max-width: 700px`. At ≥1501px we also widen the main
-- padding past the ToC so chili markers have a clear gutter to live
-- in without overlapping the ToC.
def napkinTocCollapseCSS := r#"
@media screen and (701px <= width <= 1500px) {
  /* Replace the 18rem ToC reservation with a smaller fixed left
     gutter so margin-floated elements (chili-pepper markers,
     marginalia notes) still have whitespace to live in. */
  .with-toc > main { padding-left: 6rem; }

  /* Slide the ToC off the left edge by default; the burger toggle
     slides it back in. */
  #toc {
    right: 100%;
    transition: transform var(--verso-toc-transition-time) ease;
  }
  #toc:has(#toggle-toc:checked) {
    transform: translateX(var(--verso-toc-width));
  }

  /* Show the burger toggle, hide the desktop logo, shift the
     header title to make room for the burger. */
  #toggle-toc-click {
    display: inline-flex;
    cursor: pointer;
    box-sizing: content-box;
    width: var(--verso-burger-width);
    height: var(--verso-burger-height);
    flex-direction: column;
    justify-content: space-between;
    padding: 0.5rem;
    position: fixed;
    z-index: 100;
    top: calc((var(--verso-header-height) - var(--verso-burger-height) - 2 * 0.5rem) / 2);
  }
  .header-logo-wrapper { display: none; }
  .header-title {
    margin-left: calc(var(--verso-burger-width) + 1.5rem);
    max-width: unset;
  }

  /* Backdrop dims the body when the drawer is open. */
  .toc-backdrop { display: block; }
  body:has(#toggle-toc:checked) .toc-backdrop {
    position: fixed;
    inset: 0;
    background-color: #aaa8;
    z-index: 9;
  }
  html:has(#toggle-toc:checked) { overflow: hidden; }
}

/* At very wide viewports the ToC stays pinned visible. Add 6rem of
   padding past the ToC width so left-margin annotations (chili
   peppers etc.) sit in a clear gutter rather than overlapping the
   ToC's right edge. */
@media screen and (min-width: 1501px) {
  .with-toc > main {
    padding-left: calc(var(--verso-toc-width) + 6rem);
  }
}
"#

/-- Rewrite Verso's auto-numbering to match Napkin's hierarchy:

      * Part number: arabic → Roman (`1.` → `I.`)
      * Chapter number: part-relative → Napkin's flat global counter
        starting at 0 (Sales Pitches = 0, Groups = 1, Quotient = 3,
        Adjoints = 15 — the gap reflects that Ch 14 / Fourier is
        skipped). Lookup via the `chapterMap` table.
      * Section number: `§N.M ` with section-sign prefix and no
        trailing dot (matching Napkin's print form `§3.2 Foo`),
        where `N` is the global chapter number from `chapterMap`.

    Done in JS because Verso's `assignedNumber` is overwritten by
    its own traversal pass, so user metadata can't pre-set it.
    Walks all `<h1>`–`<h6>` headings, TOC `td.num` cells, and
    inline `.number` spans. -/
def napkinSectionNumberStripJS : String := r#"
document.addEventListener('DOMContentLoaded', function () {
  // Verso "part.chapter" key → Napkin's global chapter number.
  // Keep in sync with `Napkin.lean`'s include-order.
  var chapterMap = {
    '1.1':  0, '1.2':  1, '1.3':  2,
    '2.1':  3, '2.2':  4, '2.3':  5,
    '3.1':  6, '3.2':  7, '3.3':  8,
    '4.1':  9, '4.2': 10, '4.3': 11, '4.4': 12, '4.5': 13, '4.6': 15,
    '5.1': 16, '5.2': 17, '5.3': 18,
    '6.1': 19, '6.2': 20, '6.3': 21, '6.4': 22
  };
  var roman = ['', 'I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII',
               'IX', 'X', 'XI', 'XII', 'XIII', 'XIV', 'XV', 'XVI',
               'XVII', 'XVIII', 'XIX', 'XX'];

  // Translate one Verso number string. Returns the new string (with
  // any preserved trailing whitespace) or `null` if the input
  // doesn't look like a Verso section number.
  var translate = function (raw) {
    var m = raw.match(/^(\s*)(\d+(?:\.\d+)*)\.?(\s*)$/);
    if (!m) return null;
    var leading = m[1], body = m[2], trailing = m[3];
    var parts = body.split('.');
    if (parts.length === 1) {
      var n = parseInt(parts[0], 10);
      var r = roman[n];
      return r ? leading + r + '.' + trailing : null;
    }
    var key = parts[0] + '.' + parts[1];
    var ch = chapterMap[key];
    if (ch === undefined) return null;
    if (parts.length === 2) {
      return leading + ch + '.' + trailing;
    }
    var rest = parts.slice(2).join('.');
    return leading + '§' + ch + '.' + rest + trailing;
  };

  // Replace any leading "1.2. " / "1.2.3. " prefix in a text string,
  // returning the new string or `null` if no match. Used for places
  // where the number appears inline before the title (prev/next nav,
  // ToC link spans, anchor title attributes).
  var translatePrefix = function (raw) {
    var m = raw.match(/^(\s*)(\d+(?:\.\d+)*\.?)(\s+)/);
    if (!m) return null;
    var t = translate(m[2] + m[3]);
    if (t === null) return null;
    return m[1] + t + raw.slice(m[0].length);
  };

  // Whole-string replacements: ToC number cells and inline `.number`
  // spans contain just the number.
  document.querySelectorAll('td.num, .number').forEach(function (el) {
    var t = translate(el.textContent);
    if (t !== null) el.textContent = t;
  });

  // Heading prefixes are inline text in <h1>–<h6>; the rest of the
  // heading content (title plus permalink widget) follows. Replace
  // just the leading text node when it matches the number pattern.
  document.querySelectorAll('main h1, main h2, main h3, main h4, main h5, main h6').forEach(function (h) {
    for (var node = h.firstChild; node; node = node.nextSibling) {
      if (node.nodeType !== Node.TEXT_NODE) continue;
      var t = translatePrefix(node.nodeValue);
      if (t === null) continue;
      node.nodeValue = t;
      break;
    }
  });

  // ToC entries that combine number + title in one span (e.g. the
  // prev/next navigation bar's `.where`, search-jump `.title`, and
  // breadcrumb-style entries that include the section number).
  document.querySelectorAll('.where, .toc-title, a.local-button .where').forEach(function (el) {
    var t = translatePrefix(el.textContent);
    if (t !== null) el.textContent = t;
  });

  // Anchor `title` attributes mirroring those visible labels.
  document.querySelectorAll('a[title]').forEach(function (a) {
    var t = translatePrefix(a.getAttribute('title') + ' ');
    if (t !== null) a.setAttribute('title', t.replace(/\s+$/, ''));
  });
});
"#

/-- Verso emits margin notes as `<span class="marginalia">` without
    `tabindex`, so by default our hover tooltip isn't reachable via
    keyboard. This script promotes each marginalia to a focusable
    element on load and adds `aria-describedby` linking the note for
    screen readers. -/
def napkinMarginaliaA11yJS : String := r#"
document.addEventListener('DOMContentLoaded', function () {
  var i = 0;
  document.querySelectorAll('.marginalia').forEach(function (m) {
    if (!m.hasAttribute('tabindex')) m.setAttribute('tabindex', '0');
    if (!m.hasAttribute('role')) m.setAttribute('role', 'note');
    var note = m.querySelector('.note');
    if (note && !note.id) {
      note.id = 'marginalia-note-' + (++i);
    }
    if (note && !m.hasAttribute('aria-describedby')) {
      m.setAttribute('aria-describedby', note.id);
    }
  });
});
"#

def napkinExtraHead : Array Verso.Output.Html := #[
  .tag "style" #[] (.text false napkinFontsCSS),
  .tag "style" #[] (.text false napkinTypographyCSS),
  .tag "style" #[] (.text false napkinTocCollapseCSS),
  .tag "script" #[] (.text false napkinSectionNumberStripJS),
  .tag "script" #[] (.text false napkinMarginaliaA11yJS)
]

def config : Config where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraHead := napkinExtraHead
  extraFiles := [("figures", "figures"), ("fonts", "fonts"),
                 ("book/cover-art.jpg", "cover-art.jpg"),
                 ("book/media/kofi4.png", "kofi4.png"),
                 ("book/media/abstruse-goose-exercise.png", "abstruse-goose-exercise.png"),
                 ("book/media/read-with-pencil.jpg", "read-with-pencil.jpg"),
                 ("book/media/chili.png", "chili.png"),
                 ("book/media/love-proper-isomorphic-subgroup.jpg",
                  "love-proper-isomorphic-subgroup.jpg"),
                 ("book/media/matrix-mult.jpg", "matrix-mult.jpg")]

def main := manualMain (%doc Napkin)
  (extraSteps := [buildExercises]) (config := {config with})
