import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CStar.CyclicGNS
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The all-states part of paper.tex, fa2:p2:gns (12327–12375).
The algebra and its original norm are unchanged. States are the shared algebraic
positive functionals. No order, nontriviality, separability or representation is
assumed. The empty family for the zero algebra is allowed. -/
noncomputable section
namespace ExpandedFA.CStar.FaithfulGNS.Spec
universe u v w

/-- The norm-one, unital positivity criterion used in the extension argument. -/
def NormOnePositive : Prop := ∀ (A : Type u) [CStarAlgebra A]
  (f : A →L[ℂ] ℂ), ‖f‖ = 1 → f 1 = 1 →
    Conventions.Spec.PositiveFunctionalValue A f.toLinearMap

/-- Every nonzero element has a state attaining its squared C*-norm. -/
def NormingState : Prop := ∀ (A : Type u) [CStarAlgebra A]
  (a : A), a ≠ 0 → ∃ φ : Conventions.Spec.StateValue A,
    φ.val (star a * a) = (‖a‖ ^ 2 : ℝ)

/-- A family indexed by exactly all states, each with its cyclic GNS construction. -/
structure Family (A : Type u) [CStarAlgebra A] where
  H : Conventions.Spec.StateValue A → Type u
  normed : ∀ φ, NormedAddCommGroup (H φ)
  inner : ∀ φ, letI := normed φ; InnerProductSpace ℂ (H φ)
  complete : ∀ φ, letI := normed φ; CompleteSpace (H φ)
  realization : ∀ φ, letI := normed φ; letI := inner φ; letI := complete φ
    CyclicGNS.Spec.Construction (H := H φ) φ

attribute [instance] Family.normed Family.inner Family.complete

/-- The genuine Hilbert direct sum acts coordinatewise by the GNS operators.
It preserves the original norm, is injective and is an isometry. The final
clause records the norming vector in an actual single-state summand. -/
def FaithfulSum : Prop := by
  classical
  exact ∀ (A : Type u) [CStarAlgebra A],
  ∃ F : Family A, ∃ π : A →⋆ₐ[ℂ] (lp F.H 2 →L[ℂ] lp F.H 2),
    (∀ a x φ, (π a x) φ = (F.realization φ).π a (x φ)) ∧
    (∀ a, ‖π a‖ = ‖a‖) ∧ Function.Injective π ∧ Isometry π ∧
    ∀ a, a ≠ 0 → ∃ φ : Conventions.Spec.StateValue A,
      ‖π a (lp.single 2 φ (F.realization φ).ξ)‖ = ‖a‖

/-- Schwarz and the automatic norm formula include the zero algebra. No
continuity assumption is imposed on the original functional. -/
def PositiveAssertions : Prop := ∀ (A : Type u) [CStarAlgebra A]
  (φ : A →ₗ[ℂ] ℂ), Conventions.Spec.PositiveFunctionalValue A φ →
  ((∀ a, (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re) ∧
    ∀ a b, ‖φ (star b * a)‖ ^ 2 ≤
      (φ (star a * a)).re * (φ (star b * b)).re) ∧
  Continuous φ ∧ ∃ F : A →L[ℂ] ℂ, F.toLinearMap = φ ∧
    (‖F‖ : ℂ) = φ 1 ∧ ‖F‖ = (φ 1).re ∧
    ∀ a, ‖φ a‖ ≤ (φ 1).re * ‖a‖

/-- The remaining clauses of the source theorem use the shared state and
cyclic interfaces. Uniqueness allows arbitrary Hilbert-space universes. -/
def PositiveAndCyclic : Prop := PositiveAssertions.{u} ∧
  CyclicGNS.Spec.Existence.{u} ∧ CyclicGNS.Spec.Uniqueness.{u,v,w}

end ExpandedFA.CStar.FaithfulGNS.Spec
