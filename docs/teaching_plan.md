# Teaching Plan: Complex Analysis Game

This document outlines the pedagogical approach for the game, strictly following the **Theory → Practice** model.

## Philosphy
1.  **Theory First**: Every level must start with a dedicated "Introduction" or "Lecture" phase where definitions and theorems are explained clearly using standard mathematical notation ($\LaTeX$).
2.  **Theorem Documentation**: Before asking the user to use a theorem, explicit `TheoremDoc` entries must be visible and explained.
3.  **Scaffolded Exercises**: Exercises should start simple (confirming understanding of the definition) before moving to complex proofs.

## Level Structure

### Level 1: The Basics (Existing)
*   **Theory**: Definition of $\mathbb{C}$, Re/Im parts, Conjugates.
*   **Practice**: $z + \bar{z} = 2\text{Re}(z)$.

### Level 2: Arithmetic & Modulus (Refined)
*   **Theory Page 1**: Arithmetic
    *   Explain addition/multiplication.
    *   Show distributivity.
*   **Theory Page 2**: The Modulus
    *   Definition: $|z| = \sqrt{x^2 + y^2}$.
    *   Identity: $z \bar{z} = |z|^2$.
*   **Exercise 1**: Calculation (e.g., $(1+i) + (1-i)$).
*   **Exercise 2**: Proof of $z \bar{z} = |z|^2$ (using the `mul_conj` theorem).

### Level 3: The Complex Plane / Geometry (Planned)
*   **Theory**: Polar form $z = re^{i\theta}$.
*   **Visual**: Use `ComplexQuiz` to identify points in the plane.
*   **Exercise**: Proving properties of the triangle inequality (if feasible) or simple argument properties.

## Documentation Standards
*   Use `Introduction` blocks for the "Lecture" portion.
*   Use `TheoremDoc` for all accessible lemmas.
*   Use `Hint` heavily in the first few lines of a proof.
