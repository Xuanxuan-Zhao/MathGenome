import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NewtonHessian
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WholeSpaceW2p

/-! Independent targets for the compact-source stage of paper.tex:1855–1890.
The potential is the already fixed ordinary Newton integral. Essential support
allows arbitrary representatives of Lᵖ data. The observation domains need only
be bounded and open. In particular no boundary regularity is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace P201Specs.Elliptic.NewtonLp

/-- Full local W²ᵖ membership and estimate, for the actual Newton integral.
The constant is selected before the datum, for a fixed compact source set and
bounded observation domain. This includes every positive dimension and every
finite real exponent greater than one, using the shared sum Sobolev norm. -/
def PotentialEstimateInDimension (n : ℕ) : Prop :=
  ∀ (p : P102.U2.CZLpData.Exponent)
    (K : Compacts (Space n)) (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      MemLp F p.val volume → (∀ᵐ x ∂volume, x ∉ K → F x = 0) →
      (∀ᵐ x ∂volume, Integrable (fun y => fundamentalKernel n y * F (x-y)) volume) ∧
      LocallyIntegrable (NewtonHessian.holderPotential F) volume ∧
      -distributionLaplacian
        (regularDistribution (⊤ : Domain n) (NewtonHessian.holderPotential F)) =
          regularDistribution (⊤ : Domain n) F ∧
      ∃ w : W ℝ Ω 2 p.val,
        (P102.U4.sobolevUnderlying w : Space n → ℝ) =ᵐ[domainMeasure Ω]
          NewtonHessian.holderPotential F ∧
        ‖w‖ ≤ C * (eLpNorm F p.val volume).toReal

/-- The complete compact-source conclusion in every positive dimension. -/
def PotentialEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → PotentialEstimateInDimension n

/-- The complete local W²ᵖ estimate at the endpoint dimension one. -/
def DimensionOnePotentialEstimateStatement : Prop := PotentialEstimateInDimension 1

/-- The smooth-source Hessian has exactly the same Lᵖ Riesz realization as
in the whole-space estimate. Complexification is only used for the library
Riesz operators; both components of equality are asserted, so there is no
implicit change from a complex identity to just its real part. -/
def SmoothHessianInDimension (n : ℕ) : Prop :=
  ∀ (p : P102.U2.CZLpData.Exponent)
    (R : Fin n → P102.U2.CZLpData.StrongOperator n p),
    (∀ i, P102.U2.CZLpData.Agrees (P102.U3.Riesz.rieszL2 i) p (R i)) →
    ∀ (F : Test ℝ (⊤ : Domain n)) (i j : Fin n),
      ∃ hF : MemLp (fun x => (F x : ℂ)) p.val volume,
        (R i (R j (hF.toLp (fun x => (F x : ℂ)))) : Space n → ℂ) =ᵐ[volume]
          (fun x => ((multiPartial (𝕜 := ℝ) (newtonPotential F) {i,j} x : ℝ) : ℂ)) ∧
        distributionDerivative {i,j}
          (regularDistribution (⊤ : Domain n) (newtonPotential F)) =
          regularDistribution (⊤ : Domain n)
            (fun x => (R i (R j (hF.toLp (fun x => (F x : ℂ)))) x).re)

/-- The full smooth-source identification in every positive dimension. -/
def SmoothHessianStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → SmoothHessianInDimension n

/-- The one-dimensional endpoint of the same identity, with the same Riesz
normalization and both its pointwise and distributional conclusions. -/
def DimensionOneSmoothHessianStatement : Prop := SmoothHessianInDimension 1

/-- Absolute existence and the distribution equation require no initial weak
or classical derivative of the compactly supported datum. -/
def PotentialEquationStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ≥0∞), 1 ≤ p →
    ∀ (F : Space n → ℝ), MemLp F p volume →
      P102.U4.HasCompactEssentialSupport F →
      (∀ᵐ x ∂volume, Integrable (fun y => fundamentalKernel n y * F (x-y)) volume) ∧
      LocallyIntegrable (NewtonHessian.holderPotential F) volume ∧
      -distributionLaplacian
        (regularDistribution (⊤ : Domain n) (NewtonHessian.holderPotential F)) =
          regularDistribution (⊤ : Domain n) F

/-- A local Young bound used for the zero and first derivative kernels.
The datum has a fixed essential support. Both compact sets precede the constant. -/
def LocalKernelEstimateStatement : Prop :=
  ∀ (n : ℕ) (k : Space n → ℝ), LocallyIntegrable k volume →
    ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (A B : Compacts (Space n)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
        MemLp F p volume → (∀ᵐ x ∂volume, x ∉ A → F x = 0) →
        MemLp (P102.U4.functionConvolution k F) p (volume.restrict B) ∧
        (eLpNorm (P102.U4.functionConvolution k F) p (volume.restrict B)).toReal ≤
          C * (eLpNorm F p volume).toReal

/-- The full zero and first kernel bounds, before using any Hessian regularity.
The first-order functions here are ordinary convolution integrals. -/
def LowerOrderEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ≥0∞), 1 ≤ p →
    ∀ (A B : Compacts (Space n)), ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      MemLp F p volume → (∀ᵐ x ∂volume, x ∉ A → F x = 0) →
      MemLp (NewtonHessian.holderPotential F) p (volume.restrict B) ∧
      (∀ i : Fin n, MemLp (P102.U4.functionConvolution (NewtonHessian.gradientKernel i) F)
        p (volume.restrict B)) ∧
      (eLpNorm (NewtonHessian.holderPotential F) p (volume.restrict B)).toReal +
        (∑ i : Fin n, (eLpNorm
          (P102.U4.functionConvolution (NewtonHessian.gradientKernel i) F)
          p (volume.restrict B)).toReal) ≤ C * (eLpNorm F p volume).toReal

/-- Weak gradient identification for merely Lᵖ sources in every positive
dimension, including the corner of the line fundamental solution. -/
def WeakGradientStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ≥0∞), 1 ≤ p →
    ∀ (F : Space n → ℝ), MemLp F p volume →
      P102.U4.HasCompactEssentialSupport F → ∀ i : Fin n,
        distributionDerivative {i}
          (regularDistribution (⊤ : Domain n) (NewtonHessian.holderPotential F)) =
          regularDistribution (⊤ : Domain n)
            (P102.U4.functionConvolution (NewtonHessian.gradientKernel i) F)

/-- The endpoint dimension's entire Hessian is already determined by the
Poisson equation, with no regularity assumptions beyond the Lᵖ datum. -/
def DimensionOneHessianStatement : Prop :=
  ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (F : Space 1 → ℝ), MemLp F p volume →
    P102.U4.HasCompactEssentialSupport F →
    distributionDerivative ({0,0} : MultiIndex 1)
      (regularDistribution (⊤ : Domain 1) (NewtonHessian.holderPotential F)) =
        -(regularDistribution (⊤ : Domain 1) F)


/-- The complete lower-order Sobolev stage for rough compact Lᵖ data in all
positive dimensions, using the shared full first-order Sobolev norm. -/
def FirstOrderPotentialEstimateStatement : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ≥0∞), (hp : 1 ≤ p) →
    ∀ (K : Compacts (Space n)) (Ω : Domain n), Bornology.IsBounded (Ω : Set (Space n)) →
    letI : Fact (1 ≤ p) := ⟨hp⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Space n → ℝ,
      MemLp F p volume → (∀ᵐ x ∂volume, x ∉ K → F x = 0) →
      ∃ w : W ℝ Ω 1 p,
        (P102.U4.sobolevUnderlying w : Space n → ℝ) =ᵐ[domainMeasure Ω]
          NewtonHessian.holderPotential F ∧
        ‖w‖ ≤ C * (eLpNorm F p volume).toReal

/-- Smooth approximation with one compact support chosen before the datum.
No Sobolev or Hölder regularity is imposed on the datum. -/
def CommonSupportApproximationStatement : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
    ∀ K : Compacts (Space n), ∃ L : Compacts (Space n),
      (K : Set (Space n)) ⊆ L ∧ ∀ F : Space n → ℝ,
      MemLp F p volume → (∀ᵐ x ∂volume, x ∉ K → F x = 0) →
      ∃ f : ℕ → Test ℝ (⊤ : Domain n),
        (∀ m, tsupport (f m) ⊆ L) ∧
        Tendsto (fun m => (eLpNorm (fun x => f m x - F x) p volume).toReal)
          atTop (𝓝 0)

/-- Every locally integrable convolution kernel acts continuously from data
with one fixed compact essential support to Lᵖ on each compact observation set.
The conclusion concerns the actual ordinary convolution integrals. -/
def LocalConvolutionConvergenceStatement : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞), 1 ≤ p →
    ∀ (A B : Compacts (Space n)) (k : Space n → ℝ),
      LocallyIntegrable k volume →
    ∀ (f : ℕ → Space n → ℝ) (F : Space n → ℝ),
      (∀ m, MemLp (f m) p volume) → MemLp F p volume →
      (∀ m, ∀ᵐ x ∂volume, x ∉ A → f m x = 0) →
      (∀ᵐ x ∂volume, x ∉ A → F x = 0) →
      Tendsto (fun m => (eLpNorm (fun x => f m x - F x) p volume).toReal)
        atTop (𝓝 0) →
      (∀ m, MemLp (P102.U4.functionConvolution k (f m)) p (volume.restrict B)) ∧
      MemLp (P102.U4.functionConvolution k F) p (volume.restrict B) ∧
      Tendsto (fun m => (eLpNorm (fun x =>
        P102.U4.functionConvolution k (f m) x - P102.U4.functionConvolution k F x)
        p (volume.restrict B)).toReal) atTop (𝓝 0)

end P201Specs.Elliptic.NewtonLp
