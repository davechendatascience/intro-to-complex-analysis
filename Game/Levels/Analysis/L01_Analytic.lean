import GameServer.Commands
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Game.Widgets.MultipleChoice
import Game.Widgets.Quiz
import ProofWidgets.Component.HtmlDisplay

World "Analysis"
Level 1
Title "Analytic Functions"

open Complex

Introduction "
# Analytic Functions

A complex function $f(z)$ is **analytic** (or holomorphic) if it has a complex derivative.
This is a very strong condition! It implies that the real and imaginary parts of $f(z) = u(x,y) + i v(x,y)$ must satisfy the **Cauchy-Riemann equations**:

$$ \\frac{\\partial u}{\\partial x} = \\frac{\\partial v}{\\partial y} \\quad \\text{and} \\quad \\frac{\\partial u}{\\partial y} = -\\frac{\\partial v}{\\partial x} $$

In this level, we will check these equations for the function $f(z) = z^2$.
"

/-- `dsimp` (definitional simplification) simplifies terms by expanding definitions. -/
TacticDoc dsimp

/-- `hint` gives you a hint. -/
TacticDoc Hint

/-- `ComplexQuiz` allows you to answer multiple choice questions. -/
TacticDoc ComplexQuiz

/-- `simp` is a powerful tactic that simplifies goals using theorems. -/
TacticDoc simp
/-- `ring` can solve equations closer to a commutative ring. -/
TacticDoc ring
/-- `rw` (rewrite) replaces subterms with equal ones. -/
TacticDoc rw

NewTactic simp ring rw dsimp ComplexQuiz Hint

/--
# Cauchy-Riemann Check
Let $f(z) = z^2$. We can write $f(x+iy) = (x^2 - y^2) + i(2xy)$.
Let's verify the first Cauchy-Riemann equation: $\frac{\partial u}{\partial x} = \frac{\partial v}{\partial y}$.

Here, $u(x,y) = x^2 - y^2$ and $v(x,y) = 2xy$.
-/
TheoremDoc CR_Equation_Check as "CR_Equation_Check" in "Analysis"
Statement CR_Equation_Check (x y : ℝ) :
    deriv (fun x => x^2 - y^2) x = deriv (fun y => 2*x*y) y := by
  Hint "Compute the derivatives on both sides. `simp` can usually handle simple real derivatives."
  ComplexQuiz "Is the function f(z) = \\bar{z} analytic?" ["Yes", "No", "Only at z=0"] 1
  ComplexQuiz "Is the function f(z) = \\bar{z} analytic?" ["Yes", "No", "Only at z=0"] 1
  simp
  rw [deriv_const_mul]
  simp
  exact differentiableAt_id


Conclusion "
Correct! You've verified that $\\frac{\\partial u}{\\partial x} = 2x$ and $\\frac{\\partial v}{\\partial y} = 2x$, so they are equal.
"
