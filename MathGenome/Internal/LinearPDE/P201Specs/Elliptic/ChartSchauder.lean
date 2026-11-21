import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.ConstantSchauder

/-! Independent single-chart form of the boundary-straightening step in
`pde:elliptic-variable-estimate`, paper.tex:2115–2127. The chart is the genuine
one-sided graph chart from the shared spatial interfaces. The radii precede
all PDE data, and the estimate constant precedes the coefficients and functions.
The equation holds only in the open domain; the trace equality holds only on
its frontier. All boundary jets are actual derivatives within the indicated set.
-/
noncomputable section
open Set Metric
open scoped ContDiff

namespace P201Specs.Elliptic.ChartSchauder
open NewtonHessian PoissonSchauder ConstantSchauder
open P102.Sobolev.Geometry P102.U4.GraphPieces

/-- Quantitative Schauder estimate near one C²,α graph boundary chart.
There is no global geometric, connectedness, nonemptiness, or sign assumption.
In particular, the dimension-one case is `m = 0`. -/
def LocalEstimateStatement : Prop :=
  ∀ m : ℕ, ∀ α : ℝ, 0 < α → α < 1 →
    ∀ (Ω : Domain (m + 1))
      (C : BoundaryChart
        (P102.Sobolev.Extension.geometricOpen (graphFrame m) Ω :
          Set (Ambient m))),
      IsC2HolderOn α C.graphFunction (ball C.center C.radius) →
      let p : Space (m + 1) :=
        graphFrame m (C.frame (graph C.graphFunction C.center))
      ∀ W : Set (Space (m + 1)), IsOpen W → p ∈ W →
        ∃ ρ R : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ R ≤ 1 ∧
          ball p R ⊆ W ∧
          ball p R ⊆ graphFrame m ''
            chartImage C.frame C.graphFunction C.center C.radius C.height ∧
          ∀ ell K : ℝ, 0 < ell → 0 ≤ K →
            ∃ A : ℝ, 0 < A ∧
              let S := closure (Ω : Set (Space (m + 1))) ∩ ball p R
              let T := closure (Ω : Set (Space (m + 1))) ∩ ball p ρ
              ∀ (a : Space (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
                (b : Space (m + 1) → Space (m + 1)) (c : Space (m + 1) → ℝ),
                (∀ x ∈ S, ∀ i j, a x i j = a x j i) →
                (∀ x ∈ S, ∀ ξ : Space (m + 1),
                  ell * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * ξ i * ξ j) →
                (∀ i j, IsHolderOn α (fun x => a x i j) S) →
                (∀ i, IsHolderOn α (fun x => b x i) S) →
                IsHolderOn α c S →
                (∑ i, ∑ j, holderNormOn α (fun x => a x i j) S) +
                  (∑ i, holderNormOn α (fun x => b x i) S) +
                  holderNormOn α c S ≤ K →
                ∀ u f G : Space (m + 1) → ℝ,
                  ContDiffOn ℝ 2 u S →
                  (∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧
                    IsC2HolderUpToOn α u (S ∩ ball x δ)) →
                  IsBoundedOn u S → IsHolderOn α f S →
                  IsC2HolderUpToOn α G S →
                  (∀ x ∈ (Ω : Set (Space (m + 1))) ∩ ball p R,
                    nondivergenceOperator a b c u x = f x) →
                  (∀ x ∈ frontier (Ω : Set (Space (m + 1))) ∩ ball p R,
                    u x = G x) →
                  IsC2HolderUpToOn α u T ∧
                  scaledWithinSolutionNorm α 1 u T ≤
                    A * (supNormOn u S + holderNormOn α f S +
                      scaledWithinSolutionNorm α 1 G S)

end P201Specs.Elliptic.ChartSchauder
