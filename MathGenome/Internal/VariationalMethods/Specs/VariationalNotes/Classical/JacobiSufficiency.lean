import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.JacobiCoercivity

/-! The complete sufficient condition, paper.tex:3419–3483.
The hypotheses use the same scalar curves, coefficient functions, normalized
Jacobi solution, and full H¹ norm as the frozen coercivity specification.
No coercivity or Taylor certificate is included among the hypotheses. -/
noncomputable section
open Set

namespace VariationalNotes.Classical.JacobiSufficiency
open JacobiCoercivity

/-- Strict minimum relative to the fixed-endpoint admissible C¹ class. -/
def StrictWeakLocalMinimum {I : Interval} (L : Lagrangian 1)
    (u : C1Curve I 1) : Prop :=
  u ∈ fixedEndpointClass L (u.state I.left) (u.state I.right) ∧
    ∃ ρ > 0, ∀ v ∈ fixedEndpointClass L (u.state I.left) (u.state I.right),
      ‖v - u‖ < ρ → v ≠ u → action L u < action L v

/-- Continuity, extension of the classical form, and coercivity on every
actual H¹₀ class. This is the conclusion of the preceding source theorem
at the specified curve, with its full norm and no change of coefficients. -/
def CoercivityAt {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) : Prop :=
  Continuous (reducedForm I (coefficientP L u) (coefficientV L u)) ∧
    (∀ η : C1Curve I 1, η ∈ endpointZero I 1 →
      ∃ h : Variation I, Represents η h ∧
        reducedForm I (coefficientP L u) (coefficientV L u) h =
          secondVariationForm L u η) ∧
    ∃ κ : ℝ, 0 < κ ∧ ∀ η : Variation I,
      κ * ‖η‖ ^ 2 ≤ reducedForm I (coefficientP L u) (coefficientV L u) η

/-- Quantitative weak growth measured in the full H¹ norm of the classical
variation, represented in the shared Sobolev space. -/
def QuadraticGrowth {I : Interval} (L : Lagrangian 1) (u : C1Curve I 1) : Prop :=
  ∃ c > 0, ∃ ρ > 0, ∀ η : C1Curve I 1,
    η ∈ endpointZero I 1 → ‖η‖ < ρ → graphAdmissible L (u + η) →
      ∃ h : Variation I, Represents η h ∧
        action L u + c * ‖h‖ ^ 2 ≤ action L (u + η)

end VariationalNotes.Classical.JacobiSufficiency

namespace Specs.VariationalNotes.Classical.JacobiSufficiency
open _root_.VariationalNotes.Classical
open _root_.VariationalNotes.Classical.JacobiCoercivity
open _root_.VariationalNotes.Classical.JacobiSufficiency

/-- All the original strengthened Legendre–Jacobi assumptions, and the
complete coercive and strict weak minimum conclusions. The Jacobi field is
universally quantified, with precisely the source normalization. -/
def CompleteSufficientCondition : Prop :=
  ∀ (I : Interval) (L : Lagrangian 1) (u : C1Curve I 1),
    ContDiffOn ℝ 2 (stateField I 1 u) (Icc I.a I.b) →
    stateStationary L u → regularNearGraph L u 3 →
    (∀ t ∈ Icc I.a I.b, 0 < coefficientP L u t) →
    ∀ Y₀ : ℝ → ℝ × ℝ,
      Jacobi.IsSolution (coefficientP L u) (coefficientV L u) I.a I.b Y₀ →
      Y₀ I.a = (0, coefficientP L u I.a) →
      (∀ t ∈ Ioc I.a I.b, (Y₀ t).1 ≠ 0) →
      CoercivityAt L u ∧ QuadraticGrowth L u ∧ StrictWeakLocalMinimum L u

end Specs.VariationalNotes.Classical.JacobiSufficiency
