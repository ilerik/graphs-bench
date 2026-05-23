# Convenience Makefile for paper.tex
#
# Standard targets:
#   make       - build paper.pdf (latexmk if available, else 3-pass pdflatex)
#   make watch - rebuild on change with viewer (requires latexmk)
#   make clean - remove auxiliary files (keeps paper.pdf)
#   make distclean - remove paper.pdf as well
#   make check - lint TODOs, citation usage, and unused refs.bib keys

LATEXMK ?= latexmk
PDFLATEX ?= pdflatex
BIBTEX ?= bibtex

PAPER = paper

.PHONY: all watch clean distclean view check

all: $(PAPER).pdf

# Use latexmk when available; otherwise fall back to a standard
# pdflatex / bibtex / pdflatex / pdflatex pipeline that works on
# minimal TeX Live installs.
$(PAPER).pdf: $(PAPER).tex refs.bib
	@if command -v $(LATEXMK) >/dev/null 2>&1; then \
	  echo ">>> using latexmk"; \
	  $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(PAPER).tex; \
	else \
	  echo ">>> latexmk not found, using pdflatex/bibtex pipeline"; \
	  $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex && \
	  $(BIBTEX) $(PAPER) && \
	  $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex && \
	  $(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex; \
	fi

watch:
	$(LATEXMK) -pdf -pvc -interaction=nonstopmode $(PAPER).tex

clean:
	@if command -v $(LATEXMK) >/dev/null 2>&1; then \
	  $(LATEXMK) -c $(PAPER).tex; \
	else \
	  rm -f $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).toc \
	        $(PAPER).fdb_latexmk $(PAPER).fls $(PAPER).synctex.gz; \
	fi
	rm -f $(PAPER).bbl $(PAPER).blg $(PAPER).run.xml

distclean: clean
	rm -f $(PAPER).pdf

view: $(PAPER).pdf
	@command -v xdg-open >/dev/null && xdg-open $(PAPER).pdf || \
	 command -v open     >/dev/null && open     $(PAPER).pdf || \
	 echo "No PDF viewer found; open $(PAPER).pdf manually."

# Sanity check: list \todo{} markers, undefined refs, and citation count.
check:
	@printf '=== TODO markers ===\n'
	@grep -n 'todo{' $(PAPER).tex || echo "  (none)"
	@printf '\n=== cite keys used ===\n'
	@grep -ohE '\\cite\{[^}]+\}' $(PAPER).tex | \
	  sed 's/\\cite{//;s/}//' | tr ',' '\n' | sed 's/^ *//' | \
	  sort -u
	@printf '\n=== cite count ===\n'
	@grep -ohE '\\cite\{[^}]+\}' $(PAPER).tex | \
	  sed 's/\\cite{//;s/}//' | tr ',' '\n' | sed 's/^ *//' | \
	  sort -u | wc -l
	@printf '\n=== refs.bib entry count ===\n'
	@grep -cE '^@[A-Za-z]+{' refs.bib
	@printf '\n=== unused refs.bib keys ===\n'
	@bash -c 'comm -23 \
	  <(grep -oE "^@[A-Za-z]+\\{[^,]+" refs.bib | sed "s/^@[A-Za-z]*{//" | sort -u) \
	  <(grep -ohE "\\\\cite\\{[^}]+\\}" $(PAPER).tex | sed "s/\\\\cite{//;s/}//" | tr "," "\n" | sed "s/^ *//" | sort -u)' \
	  || true

.SUFFIXES:
