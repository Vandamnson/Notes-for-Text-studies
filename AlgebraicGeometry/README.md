# Algebraic Geometry

Independent reading and worked problems in algebraic geometry. In
progress.

## Current text

**Ravi Vakil — *The Rising Sea: Foundations of Algebraic Geometry***
(latest draft, math216.github.io/foundations-of-algebraic-geometry).
Started May 2026.

Working through it from the beginning. Goal: get to schemes,
quasi-coherent sheaves, and cohomology comfortably, then push into the
later chapters as time allows.

## Files

| File | Topic | Status |
|---|---|---|
| [`RisingSea.tex`](RisingSea.tex) | Typed notes + worked exercises | Active |
| `RisingSea.pdf` | Compiled output | Built from .tex on push |

Handwritten scratchwork lives in a separate notebook and gets exported
to PDF and pushed here when a chapter is finished (same pattern as the
[Algebra/](../Algebra) D&F notes).

## Build

```bash
pdflatex RisingSea.tex
pdflatex RisingSea.tex   # second pass for hyperref refs
```

Standard TeXLive: amsmath, amssymb, amsthm, mathtools, hyperref,
parskip, xcolor.
