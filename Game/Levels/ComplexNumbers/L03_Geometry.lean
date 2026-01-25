import GameServer.Commands
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Game.Widgets.MultipleChoice
import Game.Widgets.Quiz
import ProofWidgets.Component.HtmlDisplay

World "ComplexNumbers"
Level 3
Title "The Complex Plane"

open Complex

Introduction "
# The Complex Plane

We can visualize a complex number $z = x + iy$ as a point $(x, y)$ in a 2D plane, known as the **Argand Plane**.
- The horizontal axis is the **Real Axis**.
- The vertical axis is the **Imaginary Axis**.

In this way, complex numbers behave like 2D vectors. Addition of complex numbers is just vector addition!

## Polar Form

We can also describe a point by its distance from the origin $r = |z|$ and its angle $\\theta = \\arg(z)$.
This leads to the **polar form**:
$$ z = |z| (\\cos \\theta + i \\sin \\theta) $$
"

/-- `norm_num` is a tactic for solving numerical goals. -/
TacticDoc norm_num

/-- The relation between algebraic and polar forms: $z = |z| * (\cos (\arg z) + i \sin (\arg z))$. -/
TheoremDoc Complex.norm_mul_cos_add_sin_mul_I as "norm_mul_cos_add_sin_mul_I" in "Complex"

/-- `ComplexQuiz` allows you to answer multiple choice questions. -/
TacticDoc ComplexQuiz
/-- `simp` is a powerful tactic that simplifies goals using theorems. -/
TacticDoc simp
/-- `ring` can solve equations closer to a commutative ring. -/
TacticDoc ring
/-- `rw` (rewrite) replaces subterms with equal ones. -/
TacticDoc rw
/-- `Hint` provides a hint to the player. -/
TacticDoc Hint

NewTactic simp ring rw norm_num ComplexQuiz Hint
/-- $\pi > 0$ -/
TheoremDoc Real.pi_pos as "pi_pos" in "Real"

NewTheorem Complex.norm_mul_cos_add_sin_mul_I Real.pi_pos

/--
# Geometry Quiz & Proof

First, let's check your understanding of the complex plane.
-/
TheoremDoc PolarForm as "PolarForm" in "Complex"
Statement PolarForm (z : ℂ) : z = ↑‖z‖ * (Complex.cos (arg z) + Complex.sin (arg z) * I) := by
  Hint "Think about where the number $i$ is located."
  ComplexQuiz "Which axis corresponds to the imaginary part?" ["x-axis", "y-axis", "z-axis"] 1
  Hint "Now, let's confirm the polar decomposition formula. Mathlib has a build-in theorem for this!"
  rw [Complex.norm_mul_cos_add_sin_mul_I]

Conclusion "
Correct! You've established the link between the Cartesian ($x, y$) and Polar ($r, \\theta$) forms.
"
