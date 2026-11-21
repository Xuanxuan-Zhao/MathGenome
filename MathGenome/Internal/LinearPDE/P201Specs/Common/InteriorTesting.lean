import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff InnerProductSpace
namespace P201Specs.InteriorTesting

/-- The classical equation and all compact smooth interior tests are equivalent.
No boundary condition, boundedness, symmetry or ellipticity is imposed. -/
def ClassicalTestingStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (u f : Space n → ℝ),
    ContDiffOn ℝ 1 A Ω → ContDiffOn ℝ 2 u Ω → ContinuousOn f Ω →
    ((∀ x ∈ Ω, positiveDivergence A u x = f x) ↔
      ∀ φ : Test ℝ Ω,
        weakNegativeDivergence Ω (fun x => A x (gradient u x)) φ =
          ∫ x in Ω, f x * φ x)

/-- Distributional equality with an H⁻¹ datum means equality on the smooth
classes in H¹₀. The underlying-class equality identifies the test embedding
without making any choice of representatives. -/
def EnergyTestingStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n)
    (F : MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)) (f : Hminus1 ℝ Ω),
    (∀ (φ : Test ℝ Ω) (w : H10 ℝ Ω),
      hZeroUnderlying Ω w = P102.U4.testToDomainLp Ω 2 φ →
      negativeDivergenceDistribution Ω F φ = f w) →
    ∀ v : H10 ℝ Ω,
      (∫ x in Ω, inner ℝ (F x) (hGradient v.val x)) = f v

/-- On every open set, in particular on every ball, every constant (including
zero) satisfies the homogeneous interior Laplace tests. -/
def ConstantTestingStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (c : ℝ),
    (∀ x ∈ Ω, laplacian (fun _ : Space n => c) x = 0) ∧
    ∀ φ : Test ℝ Ω,
      weakNegativeDivergence Ω (gradient (fun _ : Space n => c)) φ =
        ∫ x in Ω, (0 : ℝ) * φ x

end P201Specs.InteriorTesting
