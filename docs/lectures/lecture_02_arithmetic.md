# Lecture 2: Arithmetic & Modulus

## Theory
- **Addition**: $(a+bi) + (c+di) = (a+c) + (b+d)i$.
- **Multiplication**: $(a+bi)(c+di) = (ac-bd) + (ad+bc)i$.
- **Modulus**: $|z| = \sqrt{x^2 + y^2}$.
- **Identity**: $z \bar{z} = |z|^2$.

## Theorems
- `Complex.mul_conj`: $z \bar{z} = |z|^2$.

## Exercises
1.  **Computation**: Calculate $(1+i) + (1-i)$.
2.  **Proof**: Show that $z \bar{z} = |z|^2$ (using `Complex.mul_conj`).
