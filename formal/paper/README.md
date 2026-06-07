# Vendored Paper

This directory contains a local copy of the arXiv paper used by the repository:

- `2504.17033v2.pdf` — ready-to-read PDF.
- `2504.17033.tar.gz` — original arXiv TeX source archive.
- `source/` — extracted TeX source.

For quick reading, open `2504.17033v2.pdf`; rebuilding the paper from TeX is
not required for the Rust or Lean checks.

## Rebuilding The PDF

The arXiv source expects a reasonably complete TeX Live installation. Minimal
Linux TeX installs often miss packages such as `stmaryrd` and `dsfont`, which
causes `pdflatex` to stop with `File '...sty' not found`.

If TeX Live is complete enough, rebuild with:

```bash
cd formal/paper/source
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

The source archive may include files such as `main.bbl`; keep tracked files from
the archive, but do not archive local build products such as `.aux`, `.log`,
`.out`, and `.synctex.gz`.
