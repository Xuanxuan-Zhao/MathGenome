import MathGenome.Internal.FourierSobolev.Specs.P102.U4.PointSupport
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionConvolution
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.NegativeSobolev
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SchwartzRestriction

/-! Independent statements for the complete zero-dimensional conventions,
paper.tex:1703–1705. All spaces below are the canonical upstream spaces.
The closure defining W₀ is retained, also at p = ∞. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Classical
open scoped ContDiff Distributions ENNReal
namespace P102.U4
namespace ZeroDimensionData

def fullCompact : Compacts (Space 0) := ⟨Set.univ, isCompact_univ⟩

def constantStage (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space 0))
    (hK : (0 : Space 0) ∈ K) (c : 𝕜) : FixedSupport 0 𝕜 K where
  toFun _ := c
  contDiff' := contDiff_const
  zero_on_compl' := by
    intro x hx
    apply False.elim
    apply hx
    change x ∈ K
    rw [Subsingleton.elim x 0]
    exact hK

def constantTest (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 0))
    (hΩ : (0 : Space 0) ∈ Ω) (c : 𝕜) : TestSpace 𝕜 Ω where
  toFun _ := c
  contDiff' := contDiff_const
  hasCompactSupport' := isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  tsupport_subset' := by
    intro x _
    change x ∈ Ω
    rw [Subsingleton.elim x 0]
    exact hΩ

end ZeroDimensionData
namespace ZeroDimensionExpected

def Geometry : Prop :=
  (∀ x : Space 0, x = 0) ∧
  (volume : Measure (Space 0)) = Measure.dirac 0 ∧
  volume (Set.univ : Set (Space 0)) = 1 ∧
  (∀ Ω : Opens (Space 0), Ω = ⊥ ∨ Ω = ⊤) ∧
  (∀ α : MultiIndex 0, α = 0) ∧ IsEmpty (Fin 0)

def Functions : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    (∀ f : Space 0 → 𝕜, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f) ∧
    (∀ (Ω : Opens (Space 0)), (0 : Space 0) ∈ Ω →
      ∃ e : TestSpace 𝕜 Ω ≃L[𝕜] 𝕜, ∀ φ, e φ = φ 0) ∧
    (∀ (K : Compacts (Space 0)), (0 : Space 0) ∈ K →
      ∃ e : FixedSupport 0 𝕜 K ≃L[𝕜] 𝕜, ∀ φ, e φ = φ 0) ∧
    (∃ e : SchwartzTests 0 𝕜 ≃L[𝕜] 𝕜, ∀ φ, e φ = φ 0)

def Order : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 0)) (hΩ : (0 : Space 0) ∈ Ω),
    (∀ (K : Compacts (Space 0)) (m : ℕ) (φ : FixedSupport 0 𝕜 K),
      coordinateSupSeminorm 𝕜 K m φ = ‖φ 0‖) ∧
    (∀ T : TestSpace 𝕜 Ω →ₗ[𝕜] 𝕜,
      Continuous T ∧ ∀ φ,
        T φ = φ 0 * T (ZeroDimensionData.constantTest 𝕜 Ω hΩ 1) ∧
        ‖T φ‖ ≤ ‖T (ZeroDimensionData.constantTest 𝕜 Ω hΩ 1)‖ * ‖φ 0‖)

def Distributions : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 0)) (a : Space 0), a ∈ Ω →
    (∀ S : DistributionSpace 𝕜 Ω, ∃! c : 𝕜, S = c • pointMass 𝕜 Ω a) ∧
    (∀ f : Space 0 → 𝕜, regularDistribution Ω f = f a • pointMass 𝕜 Ω a) ∧
    (∀ S : DistributionSpace 𝕜 Ω,
      relativeSupport S = if S = 0 then ∅ else {a}) ∧
    (∀ (S : DistributionSpace 𝕜 Ω) (α : MultiIndex 0), distributionPartial α S = S) ∧
    (∀ (m : ℕ) (S : DistributionSpace 𝕜 Ω),
      ∃! c : BoundedMultiIndex 0 m → 𝕜, S = pointDerivativeSum Ω a m c)

/-- Any convolution satisfying the canonical right-compact pairing is scalar
multiplication. Existence with that pairing is required as well. -/
def Convolution : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    (∃ C : DistributionSpace 𝕜 (⊤ : Opens (Space 0)) →
        DistributionSpace 𝕜 (⊤ : Opens (Space 0)) →
        DistributionSpace 𝕜 (⊤ : Opens (Space 0)),
      (∀ T S φ, ∃ ψ : WholeTests 0 𝕜,
        (∀ x, ψ x = convolutionInner S φ x) ∧ C T S φ = T ψ) ∧
      ∀ c b : 𝕜, C (c • pointMass 𝕜 ⊤ 0) (b • pointMass 𝕜 ⊤ 0) =
        (c * b) • pointMass 𝕜 ⊤ 0) ∧
    (∀ (T : DistributionSpace 𝕜 (⊤ : Opens (Space 0)))
      (ρ : WholeTests 0 𝕜) (x : Space 0),
      localConvolution T ρ x = ρ 0 * T (ZeroDimensionData.constantTest 𝕜 ⊤ (by trivial) 1)) ∧
    (∀ (f g : Space 0 → 𝕜) (x : Space 0), functionConvolution f g x = f x * g x) ∧
    (∀ ρ : Space 0 → 𝕜, (∫ x, ρ x) = 1 → ρ = fun _ => 1)

def SobolevSpaces : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (∃ e : DomainLp 𝕜 (⊤ : Opens (Space 0)) p ≃ₗᵢ[𝕜] 𝕜,
      ∀ u, e u = u 0) ∧
    (∀ Ω : Opens (Space 0),
      (∃ e : Sobolev 𝕜 Ω m p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
        ∀ u, e u = sobolevUnderlying u) ∧
      sobolevZeroSubmodule 𝕜 Ω m p = ⊤ ∧
      (∃ e : SobolevZero 𝕜 Ω m p ≃ₗᵢ[𝕜] DomainLp 𝕜 Ω p,
        ∀ u, e u = sobolevUnderlying u.val) ∧
      (∀ u : Sobolev 𝕜 Ω m p, ‖u‖ = ‖sobolevUnderlying u‖))

def Negative : Prop :=
  NegativeSobolevExpected.ZeroDimension ∧
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 0)) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    1 < p → p ≠ (∞ : ℝ≥0∞) →
    ∃ R : NegativeSobolev 𝕜 Ω p →ₗ[𝕜] DistributionSpace 𝕜 Ω,
      IsNegativeRealization Ω p R ∧
      ∀ f : NegativeSobolev 𝕜 Ω p,
        ∃ a₀ : DomainLp 𝕜 Ω (ENNReal.conjExponent p),
          ‖a₀‖ = ‖f‖ ∧ R f = regularDistribution Ω a₀ ∧
          ∀ u, f u = ∫ x in Ω, a₀ x * sobolevUnderlying u.val x

/-- Empty domains use their upstream ambient-zero-extension representations. -/
def Empty : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜],
    (∀ φ : TestSpace 𝕜 (⊥ : Opens (Space 0)), φ = 0) ∧
    (∀ φ : FixedSupport 0 𝕜 (⊥ : Compacts (Space 0)), φ = 0) ∧
    (∀ S : DistributionSpace 𝕜 (⊥ : Opens (Space 0)), S = 0 ∧ relativeSupport S = ∅) ∧
    (∀ (p : ℝ≥0∞) (u : DomainLp 𝕜 (⊥ : Opens (Space 0)) p), u = 0) ∧
    (∀ (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : Sobolev 𝕜 (⊥ : Opens (Space 0)) m p), u = 0) ∧
    (∀ (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (u : SobolevZero 𝕜 (⊥ : Opens (Space 0)) m p), u = 0) ∧
    (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (f : NegativeSobolev 𝕜 (⊥ : Opens (Space 0)) p), f = 0)

end ZeroDimensionExpected
end P102.U4
