import GameServer.Commands
import Mathlib.Data.Complex.Basic

World "ComplexNumbers"
Level 1
Title "Real and Imaginary Parts"

Introduction "
Every complex number $z$ can be written as $x + iy$, where $x$ and $y$ are real numbers.
$x$ is called the real part, denoted $\\text{Re}(z)$, and $y$ is the imaginary part, denoted $\\text{Im}(z)$.

In Lean, `Complex` is defined as a structure with two fields: `re` and `im`.
"

open Complex

/--
Prove that for any complex number $z$, $z + \bar{z} = 2 \cdot \text{Re}(z)$.
-/
Statement (z : ℂ) : z + star z = 2 * z.re := by
  simp [Complex.add_conj]

Conclusion "
Great job! You've verified a fundamental property of complex conjugates.
"
