#!/usr/bin/env python3
"""Assemble the report from its section files.

    build.py [--html] [--pdf] [--out FILE]

Concatenates report/0*.md in file order into one Markdown document with a
title block, the build date and commit, and a contents list of the
top-level sections. Notes to resolve are the blocks between <!-- note -->
and <!-- /note --> in the section files, the open points the text leaves
for the team and the reviewers; the build keeps them, rendered as block
quotes headed "Note to resolve". The output is report/REPORT.md.

--pdf writes a PDF next to the Markdown with pandoc and the tectonic
XeTeX engine (`brew install pandoc tectonic`), after the Leios design
document's recipe: the settings are in report/pdf-metadata.yaml. The PDF
takes its title block from pandoc's metadata and its contents from
pandoc's table of contents, and every pipe table gets column widths in
proportion to its longest cells, since LaTeX wraps cells instead of
scrolling.
"""
import argparse, datetime as dt, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPORT = os.path.join(HERE, "..", "report")
TITLE = "Leios technical feasibility: a measured assessment of the pipeline on the public testnet and the benchmarking cluster"
AUTHOR = "Ezequiel Postan, ezequiel.postan@iohk.io"
PDF_METADATA = os.path.join(REPORT, "pdf-metadata.yaml")
NOTE = re.compile(r"<!--\s*note\s*-->\s*(.*?)\s*<!--\s*/note\s*-->", re.S)


def pdf_tables(md):
    """Rewrite each pipe table's separator line so that the dashes per column are in proportion to
    the column's longest cell; pandoc reads the relative widths from them when a table is wider
    than its text width, which every table of the report is."""
    out, table = [], []

    def flush():
        if len(table) >= 2 and re.match(r"^\|[\s:|-]+\|$", table[1]):
            cells = [[c.strip() for c in row.strip().strip("|").split("|")] for row in table]
            ncol = len(cells[1])
            longest = [max(len(r[i]) for r in cells if len(r) > i and r is not cells[1]) or 1 for i in range(ncol)]
            total = sum(longest)
            seps = []
            for i, c in enumerate(cells[1]):
                n = max(3, round(60 * longest[i] / total))
                seps.append(("-" * n + ":") if c.endswith(":") and not c.startswith(":") else "-" * (n + 1))
            table[1] = "|" + "|".join(seps) + "|"
        out.extend(table)
        table.clear()

    for line in md.splitlines():
        if line.startswith("|"):
            table.append(line)
        else:
            flush()
            out.append(line)
    flush()
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--html", action="store_true", help="also write the self-contained preview page next to the Markdown")
    ap.add_argument("--pdf", action="store_true", help="also write the PDF next to the Markdown (pandoc + tectonic)")
    ap.add_argument("--out")
    a = ap.parse_args()
    files = sorted(f for f in os.listdir(REPORT) if re.match(r"\d\d-.*\.md$", f))
    if not files:
        sys.exit("no section files in " + REPORT)
    try:
        commit = subprocess.run(["git", "-C", HERE, "rev-parse", "--short", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
        top = subprocess.run(["git", "-C", HERE, "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
        status = subprocess.run(["git", "-C", HERE, "status", "--porcelain"], capture_output=True, text=True, check=True).stdout.splitlines()
        # the output file itself does not make the tree dirty: it is rewritten by this build
        out_rel = os.path.relpath(os.path.abspath(a.out), top) if a.out else None
        dirty = any(l[3:].strip() != out_rel for l in status if l.strip())
    except Exception:
        commit, dirty = "unknown", False
    sections, headings = [], []
    for f in files:
        with open(os.path.join(REPORT, f)) as fh:
            text = fh.read().strip()
        text = NOTE.sub(lambda m: "> **Note to resolve.** " + " ".join(m.group(1).split()), text)
        text = re.sub(r"\n{3,}", "\n\n", text)
        m = re.match(r"# (.*)", text)
        headings.append(m.group(1) if m else f)
        sections.append(text)
    head = ["# " + TITLE, "", "Ezequiel Postan, ezequiel.postan@iohk.io", "",
            "Build of %s, from commit %s%s. Sections in this build: %s." % (
                dt.date.today().isoformat(), commit, " (uncommitted changes)" if dirty else "", ", ".join(h.split(".")[0] for h in headings)),
            "", "## Contents", ""] + ["- " + h for h in headings] + [""]
    tail = [""]
    out = a.out or os.path.join(REPORT, "REPORT.md")
    md = "\n".join(head) + "\n" + "\n\n".join(sections) + "\n" + "\n".join(tail)
    with open(out, "w") as fh:
        fh.write(md)
    print("wrote %s (%d sections, %d words)" % (out, len(sections), sum(len(s.split()) for s in sections)))
    if a.html:
        page = HTML.replace("%%TITLE%%", TITLE).replace("%%KIND%%", "Draft build") \
                   .replace("%%STAMP%%", "%s, commit %s%s" % (dt.date.today().isoformat(), commit, ", uncommitted changes" if dirty else "")) \
                   .replace("%%MARKDOWN%%", md.replace("</script", "<\\/script"))
        html_out = os.path.splitext(out)[0] + ".html"
        with open(html_out, "w") as fh:
            fh.write(page)
        print("wrote %s (%d kB)" % (html_out, len(page) // 1000))
    if a.pdf:
        stamp = "Build of %s, from commit %s%s" % (dt.date.today().isoformat(), commit, " (uncommitted changes)" if dirty else "")
        meta = ["---", "title: \"%s\"" % TITLE, "author: \"%s\"" % AUTHOR, "date: \"%s\"" % stamp, "---", ""]
        body = re.sub(r"(\d) %", "\\1\u00a0%", "\n\n".join(sections))  # a percent sign stays with its number
        pdf_md = "\n".join(meta) + pdf_tables(body) + "\n"
        pdf_src = os.path.splitext(out)[0] + ".pdf.md"
        pdf_out = os.path.splitext(out)[0] + ".pdf"
        with open(pdf_src, "w") as fh:
            fh.write(pdf_md)
        cmd = ["pandoc", pdf_src, "--pdf-engine=tectonic", "--from=markdown", "--to=pdf",
               "--metadata-file", PDF_METADATA, "--output", pdf_out]
        res = subprocess.run(cmd, capture_output=True, text=True)
        os.remove(pdf_src)
        if res.returncode != 0:
            sys.exit("pandoc failed:\n" + res.stderr[-3000:])
        warn = [l for l in res.stderr.splitlines() if "Overfull" in l or "Missing character" in l]
        print("wrote %s (%d kB%s)" % (pdf_out, os.path.getsize(pdf_out) // 1000, ", %d TeX warnings" % len(warn) if warn else ""))


# The self-contained preview page: the assembled Markdown is embedded and rendered in the browser (marked, pinned),
# with a contents rail, tables in scrolling containers, tabular figures and the notes to resolve as marked boxes.
HTML = r"""<title>Leios Feasibility Report</title>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Source+Serif+4:opsz,wght@8..60,400;8..60,600&family=Source+Sans+3:wght@400;600&family=JetBrains+Mono:wght@400;500&display=swap">
<style>
/* layout: a narrow measure for the prose (68ch), a sticky contents rail on wide screens, tables allowed wider than the measure */
:root {
  --bg: #f7f6f2; --fg: #1f2328; --muted: #5d6671; --rule: #d9d6cf; --accent: #1f6f8b; --note-bg: #fbf3e4; --note-rule: #c9a35a; --table-head: #ece9e1; --code-bg: #efede7;
  --serif: "Source Serif 4", Georgia, "Times New Roman", serif; --sans: "Source Sans 3", "Helvetica Neue", Arial, sans-serif; --mono: "JetBrains Mono", "SF Mono", Menlo, Consolas, monospace;
}
@media (prefers-color-scheme: dark) { :root:not([data-theme="light"]) { --bg: #16191d; --fg: #e4e6e9; --muted: #9aa3ad; --rule: #30363d; --accent: #6fb3cc; --note-bg: #2a2418; --note-rule: #b8923f; --table-head: #22272d; --code-bg: #1f242a; color-scheme: dark } }
:root[data-theme="dark"] { --bg: #16191d; --fg: #e4e6e9; --muted: #9aa3ad; --rule: #30363d; --accent: #6fb3cc; --note-bg: #2a2418; --note-rule: #b8923f; --table-head: #22272d; --code-bg: #1f242a; color-scheme: dark }
body { background: var(--bg); color: var(--fg); font-family: var(--sans); font-size: 17px; line-height: 1.55; margin: 0; }
.wrap { max-width: 1120px; margin: 0 auto; padding-block: 20px 64px; padding-inline: 16px; display: grid; grid-template-columns: minmax(0, 1fr); gap: 0 40px; }
@media (min-width: 1000px) { .wrap.with-toc { grid-template-columns: 220px minmax(0, 1fr); } }
nav.toc { font-size: 14px; color: var(--muted); margin-bottom: 24px; }
.wrap:not(.with-toc) nav.toc { display: none; }
@media (min-width: 1000px) { nav.toc { position: sticky; top: calc(env(safe-area-inset-top, 0px) + 16px); align-self: start; max-height: calc(100vh - 32px); overflow-y: auto; margin-bottom: 0; } }
nav.toc .label { text-transform: uppercase; letter-spacing: 0.08em; font-size: 12px; font-weight: 600; margin-bottom: 8px; }
nav.toc a { display: block; color: inherit; text-decoration: none; padding: 3px 0; border-left: 2px solid transparent; padding-left: 10px; }
nav.toc a.l3 { padding-left: 22px; font-size: 13px; }
nav.toc a:hover, nav.toc a:focus-visible { color: var(--accent); border-left-color: var(--accent); outline: none; }
main { min-width: 0; }
/* one reading column: text, tables and notes share the same left edge and the same width */
article { max-width: 760px; }
.bar { display: flex; align-items: center; gap: 14px; flex-wrap: wrap; margin-bottom: 28px; font-size: 14px; color: var(--muted); font-family: var(--mono); }
.bar strong { color: var(--fg); font-weight: 500; }
.bar button { font: 500 13px var(--sans); color: var(--fg); background: var(--code-bg); border: 1px solid var(--rule); border-radius: 4px; padding: 5px 10px; cursor: pointer; }
.bar button:hover, .bar button:focus-visible { border-color: var(--accent); color: var(--accent); outline: none; }
article h1, article h2, article h3 { font-family: var(--serif); text-wrap: balance; line-height: 1.2; font-weight: 600; }
article > h1 { font-size: 2rem; margin: 0 0 8px; }
article h2 { font-size: 1.5rem; margin: 48px 0 12px; padding-top: 16px; border-top: 1px solid var(--rule); }
article h3 { font-size: 1.2rem; margin: 32px 0 8px; }
article h4 { font-family: var(--sans); font-size: 1rem; margin: 24px 0 6px; }
article p { margin: 0 0 14px; }
article ul, article ol { padding-left: 1.4em; margin: 0 0 14px; }
article a { color: var(--accent); }
article code { font-family: var(--mono); font-size: 0.86em; background: var(--code-bg); padding: 1px 5px; border-radius: 3px; }
article pre { background: var(--code-bg); padding: 12px 14px; overflow-x: auto; border-radius: 4px; font-family: var(--mono); font-size: 0.86em; line-height: 1.45; }
article pre code { background: none; padding: 0; }
article hr { border: 0; border-top: 1px solid var(--rule); margin: 40px 0; }
.tablewrap { overflow-x: auto; margin: 10px 0 4px; max-width: 100%; border-top: 2px solid var(--fg); border-bottom: 1px solid var(--fg); }
article table { border-collapse: collapse; font-size: 14px; line-height: 1.35; font-variant-numeric: tabular-nums; width: 100%; }
article th, article td { text-align: left; vertical-align: top; padding: 7px 10px; border: 0; }
article thead th { border-bottom: 1px solid var(--fg); font-weight: 600; font-family: var(--sans); color: var(--muted); font-size: 13px; text-transform: uppercase; letter-spacing: 0.04em; }
article tbody tr:nth-child(even) { background: var(--table-head); }
article tbody td:first-child { font-weight: 600; }
article td:first-child, article th:first-child { padding-left: 8px; }
article td:last-child, article th:last-child { padding-right: 8px; }
article p.caption { font-size: 14px; color: var(--muted); margin: 6px 0 24px; line-height: 1.45; }
article p.lead { margin: 32px 0 6px; }
.tablewrap + .tablewrap { margin-top: 28px; }
article blockquote { margin: 18px 0; padding: 10px 14px; border-left: 3px solid var(--note-rule); background: var(--note-bg); font-size: 15.5px; }
article blockquote p { margin: 0; }
article blockquote strong:first-child { font-family: var(--sans); text-transform: uppercase; letter-spacing: 0.06em; font-size: 12px; display: block; margin-bottom: 4px; color: var(--note-rule); }
@media (prefers-reduced-motion: no-preference) { html { scroll-behavior: smooth; } }
</style>
<div class="wrap with-toc" id="wrap">
  <nav class="toc" id="toc" aria-label="Contents"><div class="label">Contents</div></nav>
  <main>
    <div class="bar"><button type="button" id="toggle" aria-pressed="true">Hide contents</button><span><strong>%%KIND%%</strong> · %%STAMP%%</span></div>
    <article id="report"></article>
  </main>
</div>
<script type="text/markdown" id="src">%%MARKDOWN%%</script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/marked/12.0.2/marked.min.js"></script>
<script>
(function () {
  var src = document.getElementById("src").textContent.replace(/<\\\/script/g, "<" + "/script");
  var art = document.getElementById("report");
  marked.use({ gfm: true, breaks: false });
  art.innerHTML = marked.parse(src);
  // the "Contents" list the build writes into the Markdown duplicates the rail: drop its heading and list
  var h = Array.prototype.find.call(art.querySelectorAll("h2"), function (x) { return x.textContent.trim() === "Contents"; });
  if (h && h.nextElementSibling && h.nextElementSibling.tagName === "UL") { h.nextElementSibling.remove(); h.remove(); }
  var toc = document.getElementById("toc"), n = 0;
  art.querySelectorAll("h2, h3").forEach(function (hd) {
    if (!hd.id) { hd.id = "s" + (++n); }
    var a = document.createElement("a"); a.href = "#" + hd.id; a.textContent = hd.textContent;
    if (hd.tagName === "H3") { a.className = "l3"; }
    toc.appendChild(a);
  });
  // a paragraph opening with a bold "Table n." introduces the table below it (a lead); a plain
  // paragraph opening with "Table n." after a table is that table's caption
  function isLead(p) { var f = p.firstElementChild; return !!f && f.tagName === "STRONG" && f === p.firstChild && /^Table \d/.test(f.textContent); }
  art.querySelectorAll("p").forEach(function (p) { if (isLead(p)) { p.className = "lead"; } });
  art.querySelectorAll("table").forEach(function (t) {
    var w = document.createElement("div"); w.className = "tablewrap"; t.parentNode.insertBefore(w, t); w.appendChild(t);
    var nx = w.nextElementSibling;
    if (nx && nx.tagName === "P" && !isLead(nx) && /^Table \d/.test(nx.textContent)) { nx.className = "caption"; }
  });
  // the contents rail can be hidden for reading; the choice is kept in this browser only
  var wrap = document.getElementById("wrap"), btn = document.getElementById("toggle");
  function setToc(on) {
    wrap.classList.toggle("with-toc", on);
    btn.textContent = on ? "Hide contents" : "Show contents";
    btn.setAttribute("aria-pressed", on ? "true" : "false");
    try { localStorage.setItem("toc", on ? "1" : "0"); } catch (e) {}
  }
  var saved = null;
  try { saved = localStorage.getItem("toc"); } catch (e) {}
  setToc(saved === null ? window.innerWidth >= 1000 : saved === "1");
  btn.addEventListener("click", function () { setToc(!wrap.classList.contains("with-toc")); });
  if (location.hash) { var tg = document.getElementById(location.hash.slice(1)); if (tg) { tg.scrollIntoView(); } }
})();
</script>
"""


if __name__ == "__main__":
    main()
