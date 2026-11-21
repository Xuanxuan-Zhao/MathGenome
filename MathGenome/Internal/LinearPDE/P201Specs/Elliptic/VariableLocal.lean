import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeightedInterpolation

/-! Independent local variable-coefficient a priori estimates, corresponding to
paper.tex:2034–2113. Constants precede every coefficient field and every scale.
The half-ball contains the flat face; its jets are the genuine within jets.
No equation or condition on the source is imposed on that face. -/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.VariableLocal
open NewtonHessian PoissonSchauder ConstantSchauder WeightedInterpolation

/-- Full scaled interior estimate, under local C²,α regularity on the outer
ball. The coefficient conditions and their canonical norm sum are expanded. -/
def InteriorBallEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : Space n → Matrix (Fin n) (Fin n) ℝ)
          (b : Space n → Space n) (c : Space n → ℝ)
          (z : Space n) (r : ℝ), 0 < r → r ≤ 1 →
          (∀ x ∈ ball z (2 * r), ∀ i j, a x i j = a x j i) →
          (∀ x ∈ ball z (2 * r), ∀ ξ : Space n,
            ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) →
          (∀ i j, IsHolderOn α (fun x => a x i j) (ball z (2 * r))) →
          (∀ i, IsHolderOn α (fun x => b x i) (ball z (2 * r))) →
          IsHolderOn α c (ball z (2 * r)) →
          (∑ i, ∑ j, holderNormOn α (fun x => a x i j) (ball z (2 * r))) +
            (∑ i, holderNormOn α (fun x => b x i) (ball z (2 * r))) +
            holderNormOn α c (ball z (2 * r)) ≤ K →
          ∀ u f : Space n → ℝ,
            IsC2HolderLocOn α u ⟨ball z (2 * r), isOpen_ball⟩ →
            IsBoundedOn u (ball z (2 * r)) →
            IsHolderOn α f (ball z (2 * r)) →
            (∀ x ∈ ball z (2 * r), nondivergenceOperator a b c u x = f x) →
            IsC2HolderOn α u (ball z r) ∧
            scaledSolutionNorm α r u (ball z r) ≤
              C * scaledDataNorm α r u f (ball z (2 * r))

/-- One-sided local C²,α regularity is assumed on the full outer half-ball
including its face. This includes `m = 0`, and no sign condition on c occurs. -/
def HalfBallEstimateStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 →
    ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
          (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ)
          (r : ℝ), 0 < r → r ≤ 1 →
          (∀ x ∈ halfBallWithFace m (2 * r), ∀ i j, a x i j = a x j i) →
          (∀ x ∈ halfBallWithFace m (2 * r), ∀ ξ : Space (m + 1),
            ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) →
          (∀ i j, IsHolderOn α (fun x => a x i j) (halfBallWithFace m (2 * r))) →
          (∀ i, IsHolderOn α (fun x => b x i) (halfBallWithFace m (2 * r))) →
          IsHolderOn α c (halfBallWithFace m (2 * r)) →
          (∑ i, ∑ j, holderNormOn α (fun x => a x i j) (halfBallWithFace m (2 * r))) +
            (∑ i, holderNormOn α (fun x => b x i) (halfBallWithFace m (2 * r))) +
            holderNormOn α c (halfBallWithFace m (2 * r)) ≤ K →
          ∀ u f : Space (m + 1) → ℝ,
            ContDiffOn ℝ 2 u (halfBallWithFace m (2 * r)) →
            (∀ x ∈ halfBallWithFace m (2 * r), ∃ δ : ℝ, 0 < δ ∧
              IsC2HolderUpToOn α u (halfBallWithFace m (2 * r) ∩ ball x δ)) →
            (∀ x ∈ flatFace m (2 * r), u x = 0) →
            IsBoundedOn u (halfBallWithFace m (2 * r)) →
            IsHolderOn α f (halfBallWithFace m (2 * r)) →
            (∀ x ∈ halfBall m (2 * r), nondivergenceOperator a b c u x = f x) →
            IsC2HolderUpToOn α u (halfBallWithFace m r) ∧
            scaledWithinSolutionNorm α r u (halfBallWithFace m r) ≤
              C * scaledDataNorm α r u f (halfBallWithFace m (2 * r))

end P201Specs.Elliptic.VariableLocal
