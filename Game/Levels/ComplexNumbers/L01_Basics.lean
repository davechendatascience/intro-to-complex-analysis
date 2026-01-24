
import GameServer.Commands
import Mathlib.Data.Complex.Basic
import Game.Widgets.MultipleChoice
import Game.Widgets.Quiz
import ProofWidgets.Component.HtmlDisplay

World "ComplexNumbers"
Level Basics
Title "Real and Imaginary Parts"

Introduction "
Every complex number $z$ can be written as $x + iy$, where $x$ and $y$ are real numbers.
$x$ is called the real part, denoted $\\text{Re}(z)$, and $y$ is the imaginary part, denoted $\\text{Im}(z)$.

In Lean, `Complex` is defined as a structure with two fields: `re` and `im`.
"

/-- `ComplexQuiz` displays a multiple-choice question in the Infoview. -/
TacticDoc ComplexQuiz
/-- `simp` is a powerful tactic that simplifies goals using theorems. -/
TacticDoc simp
/-- `ring` solves goals that follow from the axioms of a ring (like `a + b = b + a`). -/
TacticDoc ring
/-- `rw` (rewrite) replaces subterms with equal ones. -/
TacticDoc rw
/-- `apply` matches the goal against the conclusion of a theorem. -/
TacticDoc apply

/-- The property that $z + \bar{z} = 2 \text{Re}(z)$. -/
TheoremDoc Complex.add_conj as "add_conj" in "Complex"
/-- The real part of a sum is the sum of real parts. -/
TheoremDoc Complex.add_re as "add_re" in "Complex"
/-- The imaginary part of a sum is the sum of imaginary parts. -/
TheoremDoc Complex.add_im as "add_im" in "Complex"
/-- The real part of a conjugate is the same. -/
TheoremDoc Complex.conj_re as "conj_re" in "Complex"
/-- The imaginary part of a conjugate is the negative. -/
TheoremDoc Complex.conj_im as "conj_im" in "Complex"
/-- The real part of a real number is itself. -/
TheoremDoc Complex.ofReal_re as "ofReal_re" in "Complex"
/-- The imaginary part of a real number is zero. -/
TheoremDoc Complex.ofReal_im as "ofReal_im" in "Complex"

NewTactic simp ring rw apply ComplexQuiz
NewTheorem Complex.add_conj Complex.add_re Complex.add_im Complex.conj_re Complex.conj_im Complex.ofReal_re Complex.ofReal_im


open Complex ComplexConjugate

/--
Prove that for any complex number $z$, $z + \bar{z} = 2 \cdot \text{Re}(z)$.
-/
Statement (z : ℂ) : z + conj z = 2 * z.re := by
  ComplexQuiz "Quiz: What is the real part of 3 + 4i?" ["3", "4", "3 + 4i", "7"] 0
  rw [Complex.add_conj]
  simp




Conclusion "
Great job! You've verified a fundamental property of complex conjugates.
"

