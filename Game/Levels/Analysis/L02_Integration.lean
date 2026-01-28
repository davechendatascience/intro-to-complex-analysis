import GameServer.Commands
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Game.Widgets.MultipleChoice
import Game.Widgets.Quiz
import ProofWidgets.Component.HtmlDisplay

World "Analysis"
Level 2
Title "Integration"

Introduction "
# Complex Integration

In real calculus, we integrate over intervals $[a, b]$. In complex analysis, we integrate over **curves** (paths) in the complex plane.

One of the most important paths is the circle. We denote the integral of a function $f(z)$ over a circle of radius $R$ centered at $c$ as:

$$ \\oint_{|z-c|=R} f(z) \\, dz $$

In this level, we will explore the **Cauchy-Goursat Theorem** and **Cauchy's Integral Formula**.
"

open Complex MeasureTheory Set Metric Real

/-- `circleIntegral f c R` is the integral of `f` over the circle with center `c` and radius `R`. -/
DefinitionDoc circleIntegral as "\\oint"

/-- **Cauchy-Goursat Theorem**: The integral of a function differentiable on a disk is 0. -/
TheoremDoc Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable as "cauchy_goursat" in "Integration"

/-- The integral of $z^n$ over a circle around 0 is 0 if $n \\neq -1$. -/
TheoremDoc circleIntegral.integral_sub_zpow_of_ne as "integral_zpow" in "Integration"

/-- **Cauchy's Integral Formula**: The integral of $1/(z-c)$ over a circle around $c$ is $2\\pi i$. -/
TheoremDoc Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable as "cauchy_integral_one" in "Integration"

NewDefinition circleIntegral
NewTheorem Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable circleIntegral.integral_sub_zpow_of_ne Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable

/--
Answer: \"0\"
-/
Statement IntegralOfOne (c : ℂ) (R : ℝ) (h : 0 ≤ R) : (∮ z in C(c, R), (1 : ℂ)) = 0 := by
  Hint "This is a direct consequence of the Cauchy-Goursat theorem, or simply the integral of a constant."
  Hint "Try `simp` or look for a theorem about constant integrals."
  ComplexQuiz "What is the integral of the constant function 1 over any closed loop?" ["0", "2πi", "π", "Undefined"] 0
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h (s := ∅)
  · exact countable_empty
  · exact continuousOn_const
  · intro z _
    apply differentiableAt_const (1 : ℂ)

/--
Answer: \"2πi\"
-/
Statement IntegralOfOneDivZ (R : ℝ) (h : R > 0) : (∮ z in C(0, R), (z - 0)⁻¹) = 2 * (π : ℂ) * I := by
  Hint "This is the fundamental integral in complex analysis."
  Hint "Look at `circleIntegral.integral_sub_inv_smul_of_differentiable_on_off_countable`."
  ComplexQuiz "What is the value of $\\oint_{|z|=1} \\frac{1}{z} dz$?" ["0", "2πi", "π", "1"] 1
  -- We need to set up the conditions for the theorem
  rw [show (2 * (π : ℂ) * I) = (2 * (π : ℂ) * I) • (1 : ℂ) by simp]
  rw [show (∮ z in C(0, R), (z - 0)⁻¹) = ∮ z in C(0, R), (z - 0)⁻¹ • 1 by simp]
  apply Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable h (s := ∅)
  · exact countable_empty
  · exact continuousOn_const
  · intro z _
    apply differentiableAt_const (1 : ℂ)

Conclusion "
Excellent! You've seen that the integral of $1$ is $0$, but the integral of $1/z$ captures the \"hole\" at the origin, giving $2\\pi i$.
"
