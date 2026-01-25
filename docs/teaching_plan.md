# Teaching Plan: Complex Analysis Game

This document outlines the pedagogical approach for the game, strictly following the **Theory → Practice** model.

## Philosphy
1.  **Theory First**: Every level must start with a dedicated "Introduction" or "Lecture" phase where definitions and theorems are explained clearly using standard mathematical notation ($\LaTeX$).
2.  **Theorem Documentation**: Before asking the user to use a theorem, explicit `TheoremDoc` entries must be visible and explained.
3.  **Scaffolded Exercises**: Exercises should start simple (confirming understanding of the definition) before moving to complex proofs.


## World 1: Complex Numbers
Foundational arithmetic and geometry.

### Level 1: The Basics
*   See [Lecture 1 Plan](lectures/lecture_01_basics.md)

### Level 2: Arithmetic & Modulus
*   See [Lecture 2 Plan](lectures/lecture_02_arithmetic.md)

### Level 3: The Complex Plane
*   See [Lecture 3 Plan](lectures/lecture_03_geometry.md)

## World 2: Analysis
Calculus on the complex plane.

### Level 1: Analytic Functions
*   **Theory**: Complex Differentiability & Cauchy-Riemann Equations.
*   **Exercise**: Verifying CR equations for polynomial functions.

## Documentation Standards
*   Use `Introduction` blocks for the "Lecture" portion.
*   Use `TheoremDoc` for all accessible lemmas.
*   Use `Hint` heavily in the first few lines of a proof.

## Future Levels (Advanced Topics)
*Based on `docs/complex_analysis_topics.md`*

### Integration & Cauchy Theory
*   Line Integrals & Antiderivatives
*   Cauchy-Goursat Theorem
*   Cauchy Integral Formula
*   Applications: Liouville, Fundamental Theorem of Algebra

### Series Representations
*   Power Series & Radius of Convergence
*   Taylor & Laurent Series
*   Singularity Classification (Removable, Poles, Essential)

### Residue Theory
*   Residue Theorem
*   Argument Principle & Rouché's Theorem
*   Real Integrals evaluation

### Advanced Geometry
*   Möbius Transformations
*   Conformal Mapping
*   Riemann Mapping Theorem
