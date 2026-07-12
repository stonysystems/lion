#!/bin/bash
set -e

cd "$(dirname "$0")"

MAIN="main"

if command -v latexmk >/dev/null 2>&1; then
  latexmk -pdf -halt-on-error -interaction=nonstopmode "$MAIN.tex"
else
  pdflatex -halt-on-error -interaction=nonstopmode "$MAIN.tex"
  pdflatex -halt-on-error -interaction=nonstopmode "$MAIN.tex"
fi

echo ""
echo "=========================================="
echo "Output: $(pwd)/$MAIN.pdf"
echo "=========================================="
