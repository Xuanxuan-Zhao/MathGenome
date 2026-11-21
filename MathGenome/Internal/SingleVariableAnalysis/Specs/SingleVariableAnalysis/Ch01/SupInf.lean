import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar
import Mathlib.Data.EReal.Basic

/-!
Independent specification for paper.tex:190–207, K03.01.sup_inf.
The real operations require nonemptiness and the appropriate boundedness.
Extended bounds use the canonical two-sided extended real line. In particular,
the total library `sSup : Set ℝ → ℝ` at the empty set is not a real supremum.
-/

namespace Specs.SingleVariableAnalysis.Ch01.SupInf

/-- A real supremum is exposed only on its mathematical domain. -/
def realSupremumType : Type :=
  (A : Set ℝ) → A.Nonempty → BddAbove A → ℝ

noncomputable def realSupremumValue : realSupremumType := fun A _ _ => sSup A

/-- The infimum is defined by negating the supremum of the negated set. -/
def realInfimumType : Type :=
  (A : Set ℝ) → A.Nonempty → BddBelow A → ℝ

noncomputable def realInfimumValue : realInfimumType :=
  fun A _ _ => -sSup ((fun x : ℝ => -x) '' A)

def extendedSupremumType : Type := Set EReal → EReal

noncomputable def extendedSupremumValue : extendedSupremumType := sSup

def extendedInfimumType : Type := Set EReal → EReal

noncomputable def extendedInfimumValue : extendedInfimumType := sInf

/-- `IsLUB` states both the upper-bound property and leastness. -/
def realSupremumIsLUB : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddAbove A → IsLUB A (sSup A)

def realInfimumIsGLB : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddBelow A →
    IsGLB A (-sSup ((fun x : ℝ => -x) '' A))

/-- Agreement with the canonical greatest lower bound. -/
def realInfimumEqCsInf : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddBelow A →
    -sSup ((fun x : ℝ => -x) '' A) = sInf A

def realSupremumApprox : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddAbove A →
    ∀ ε : ℝ, 0 < ε → ∃ a ∈ A, sSup A - ε < a ∧ a ≤ sSup A

def realInfimumApprox : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddBelow A →
    ∀ ε : ℝ, 0 < ε →
      ∃ a ∈ A, -sSup ((fun x : ℝ => -x) '' A) ≤ a ∧
        a < -sSup ((fun x : ℝ => -x) '' A) + ε

def realNoSupremumEmpty : Prop := ∀ s : ℝ, ¬ IsLUB (∅ : Set ℝ) s

def realNoInfimumEmpty : Prop := ∀ t : ℝ, ¬ IsGLB (∅ : Set ℝ) t

def extendedSupremumIsLUB : Prop := ∀ A : Set EReal, IsLUB A (sSup A)

def extendedInfimumIsGLB : Prop := ∀ A : Set EReal, IsGLB A (sInf A)

def extendedSupremumEmpty : Prop := sSup (∅ : Set EReal) = ⊥

def extendedInfimumEmpty : Prop := sInf (∅ : Set EReal) = ⊤

/-- The extended operations agree with the finite real bounds whenever they exist. -/
def extendedSupremumOfReal : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddAbove A →
    sSup (Real.toEReal '' A) = ((sSup A : ℝ) : EReal)

def extendedInfimumOfReal : Prop :=
  ∀ (A : Set ℝ), A.Nonempty → BddBelow A →
    sInf (Real.toEReal '' A) = (-sSup ((fun x : ℝ => -x) '' A) : ℝ)

/-- Unboundedness is in the indicated real direction; EReal itself is bounded. -/
def extendedSupremumUnbounded : Prop :=
  ∀ A : Set ℝ, ¬ BddAbove A → sSup (Real.toEReal '' A) = ⊤

def extendedInfimumUnbounded : Prop :=
  ∀ A : Set ℝ, ¬ BddBelow A → sInf (Real.toEReal '' A) = ⊥

end Specs.SingleVariableAnalysis.Ch01.SupInf
