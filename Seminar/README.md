# Seminar Report — Polynomials and High-Dimensional Spheres

Write-up of a research seminar talk by **Prof. Ambar Sengupta**
(University of Connecticut), delivered at Northeastern University on
**November 12, 2024**, attended as part of the *Research Seminar*
course (Fall 2024, Prof. Jonathan Weitsman).

The talk drew on Peterson \& Sengupta (2019),
[*Polynomials and High-Dimensional Spheres*](https://arxiv.org/abs/1903.07697)
(arXiv:1903.07697 \[math.MP\]).

## Topics covered

1. **Gaussian integration as the limit of spherical integration.** The
   identity
   $a_{d,N}\,\langle p, q\rangle_{L^2(S^{N-1},\bar{\sigma})}
    = \langle p, q\rangle_{L^2(\mathbb{R}^N,\mu)}$,
   with $a_{d,N}\to 1$ as $N\to\infty$, recovers the Gaussian inner
   product as the $N\to\infty$ limit of the spherical inner product.
2. **Harmonic polynomials and operators on polynomial spaces.** The
   operators $L_a, M_{jk}, \|M\|^2$ and their algebraic properties; the
   decomposition $\mathcal{P}_N^d = \mathcal{H}_N^d \oplus \|X\|^2
   \mathcal{P}_N^{d-2}$; the construction of zonal harmonics via
   projection onto $\mathcal{H}_N$.
3. **Hermite limits.** Gegenbauer polynomials converge to Hermite
   polynomials,
   $\lim_{N\to\infty} q_m(\sqrt{N};X)
    = \lim_{N\to\infty} C_m^{(N-2)/2}(X/\sqrt{N})
    = H_m(X)$.
4. **The spherical Laplacian in higher dimensions.**
   $\lim_{N\to\infty}\Delta_{S^{N-1}(\sqrt{N})}
   = \sum_{i=1}^{\infty}(\partial_i^2 - X_i\,\partial_i)$,
   i.e., the spherical Laplacian on a sphere of radius $\sqrt{N}$
   converges to the Hermite differential operator.

## Files

- [`Seminar_Report.pdf`](Seminar_Report.pdf) — 4 pages.
- [`Seminar_Report.tex`](Seminar_Report.tex) — LaTeX source.

## Build

```bash
pdflatex Seminar_Report.tex
pdflatex Seminar_Report.tex   # second pass for hyperref refs
```

No external dependencies beyond standard TeXLive (amsmath, amssymb,
amsthm, mathtools, hyperref, parskip, xcolor).
