
import GameServer.Commands
import Mathlib.Data.Complex.Basic
import Game.Widgets.MultipleChoice
import Game.Widgets.Quiz
import ProofWidgets.Component.HtmlDisplay

World "ComplexNumbers"
Level Modulus
Title "Arithmetic and Modulus"

open Complex ComplexConjugate

Introduction "
# Arithmetic and Modulus

We have seen how to define complex numbers. Now let's do some arithmetic.

## Addition and Multiplication
Addition and multiplication work just like you expect, using the distributive law and $i^2 = -1$.
$$ (a + bi) + (c + di) = (a+c) + (b+d)i $$
$$ (a + bi) \\cdot (c + di) = (ac - bd) + (ad + bc)i $$

## The Modulus
We also define the **modulus** (or absolute value) of $z = x + iy$ as:
$$ |z| = \\sqrt{x^2 + y^2} $$

In Lean, we use the notation `|z|`.
A key identity relating the conjugate and the modulus is:
$$ z \\cdot \\bar{z} = |z|^2 $$
"

/-- `ComplexQuiz` displays a multiple-choice question in the Infoview. -/
TacticDoc ComplexQuiz
/-- `simp` is a powerful tactic that simplifies goals using theorems. -/
TacticDoc simp
/-- `ring` can solve equations closer to a commutative ring. -/
TacticDoc ring
/-- `rw` (rewrite) replaces subterms with equal ones. -/
TacticDoc rw

/-- The property that $z \\cdot \\bar{z} = |z|^2$ (lifted to $\\mathbb{C}$). -/
TheoremDoc Complex.mul_conj as "mul_conj" in "Complex"

NewTactic simp ring rw ComplexQuiz
NewTheorem Complex.mul_conj

/--
Let's practice some basic addition.
Compute the sum of $(1 + i) + (1 - i)$.
-/
Statement : (1 + Complex.I) + (1 - Complex.I) = 2 := by
  ComplexQuiz "What is (1+i) + (1-i)?" ["2", "2i", "0", "1"] 0
  ring

/--
Now, let's look at the relationship between the conjugate and the modulus.
We want to prove that $z \\cdot \\bar{z} = |z|^2$.
Which theorem should we use?
-/
Statement (z : ℂ) : z * conj z = ↑(Complex.normSq z) := by
  ComplexQuiz "Which theorem relates z * conj z to |z|^2?" ["Complex.add_conj", "Complex.mul_conj", "Complex.normSq"] 1
  rw [Complex.mul_conj]

Conclusion "
Excellent! You now understand how the modulus relates to the conjugate.
"
