import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! Multiplication and restriction, paper.tex:1329–1336. Coefficients are ambient
representatives with smoothness required only on Ω. A multiplier family is specified
by its pointwise graph; existence is a separate obligation, so the product rules do
not assume the existence or continuity of multiplication. -/
noncomputable section
open Set TopologicalSpace Filter
open scoped ContDiff Distributions Topology
namespace P102.U4

abbrev SmoothCoefficient {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :=
  {a : Space d → 𝕜 // ContDiffOn ℝ (⊤ : ℕ∞) a Ω}

def coefficientPartial {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (i : Fin d) (a : SmoothCoefficient 𝕜 Ω) : SmoothCoefficient 𝕜 Ω :=
  ⟨fun x => fderiv ℝ a.val x (coordinateVector d i),
    (a.property.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_const⟩

/-- Ordinary pointwise multiplication, including the ambient zero extension. -/
def coefficientTestProduct {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (a : SmoothCoefficient 𝕜 Ω) (φ : TestSpace 𝕜 Ω) : TestSpace 𝕜 Ω := by
  have hs : tsupport (fun x => a.val x * φ x) ⊆ tsupport φ := tsupport_mul_subset_right
  refine ⟨fun x => a.val x * φ x, ?_, φ.hasCompactSupport.of_isClosed_subset
    isClosed_closure hs, hs.trans φ.tsupport_subset⟩
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact (a.property.contDiffAt (Ω.isOpen.mem_nhds hx)).mul φ.contDiff.contDiffAt
  · have hz : (fun y => a.val y * φ y) =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds
        (fun h => hx (φ.tsupport_subset h))] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq hz

/-- Weak topology: pointwise convergence of the scalar pairings. -/
@[instance_reducible] def distributionWeakTopology {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :
    TopologicalSpace (DistributionSpace 𝕜 Ω) :=
  TopologicalSpace.induced (fun T : DistributionSpace 𝕜 Ω => (fun φ => T φ)) inferInstance

/-- Strong topology: uniform convergence on von Neumann bounded subsets of tests. -/
@[instance_reducible] def distributionStrongTopology {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :
    TopologicalSpace (DistributionSpace 𝕜 Ω) :=
  UniformConvergenceCLM.instTopologicalSpace (RingHom.id 𝕜) 𝕜
    {B : Set (TestSpace 𝕜 Ω) | Bornology.IsVonNBounded 𝕜 B}

abbrev TestMultiplierFamily {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :=
  SmoothCoefficient 𝕜 Ω → TestSpace 𝕜 Ω →L[𝕜] TestSpace 𝕜 Ω

def HasMultiplierGraph {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (M : TestMultiplierFamily 𝕜 Ω) : Prop :=
  ∀ a φ x, M a φ x = a.val x * φ x

/-- Transposed multiplication. Its graph is supplied by the construction theorem. -/
def transposeMultiplier {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (M : TestMultiplierFamily 𝕜 Ω) (a : SmoothCoefficient 𝕜 Ω)
    (T : DistributionSpace 𝕜 Ω) : DistributionSpace 𝕜 Ω := T.comp (M a)

/-- Restriction is precisely transposition of the canonical zero extension. -/
def restrictDistribution {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {V Ω : Opens (Space d)}
    (h : V ≤ Ω) (T : DistributionSpace 𝕜 Ω) : DistributionSpace 𝕜 V :=
  T.comp (zeroExtension 𝕜 h)

/-- Fully expanded iterated Leibniz rule. Each coordinate derivative splits
into differentiating the coefficient and differentiating the distribution.
Repeated equal coordinates therefore give the usual binomial multiplicities. -/
def leibnizExpansion {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (M : TestMultiplierFamily 𝕜 Ω) :
    List (Fin d) → SmoothCoefficient 𝕜 Ω → DistributionSpace 𝕜 Ω → DistributionSpace 𝕜 Ω
  | [], a, T => transposeMultiplier M a T
  | i :: l, a, T => leibnizExpansion M l (coefficientPartial i a) T +
      leibnizExpansion M l a (distributionPartial {i} T)

namespace OperationsExpected

def RestrictionType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  {V Ω : Opens (Space d)} → (V ≤ Ω) →
    DistributionSpace 𝕜 Ω →L[𝕜] DistributionSpace 𝕜 V

def RestrictionValue : RestrictionType := fun {_} {𝕜} _ {_ _} h =>
  ContinuousLinearMap.precomp 𝕜 (zeroExtension 𝕜 h)

def TestProductContinuity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (a : SmoothCoefficient 𝕜 Ω), Continuous (coefficientTestProduct a)

def ProductType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  SmoothCoefficient 𝕜 Ω → TestSpace 𝕜 Ω → TestSpace 𝕜 Ω

def ProductValue : ProductType := @coefficientTestProduct

def MultiplierConstruction : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    ∃ M : TestMultiplierFamily 𝕜 Ω, HasMultiplierGraph M

def TransposeContinuity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d))
    (A : TestSpace 𝕜 V →L[𝕜] TestSpace 𝕜 Ω),
    @Continuous _ _ (distributionWeakTopology 𝕜 Ω) (distributionWeakTopology 𝕜 V)
      (fun T : DistributionSpace 𝕜 Ω => T.comp A) ∧
    @Continuous _ _ (distributionStrongTopology 𝕜 Ω) (distributionStrongTopology 𝕜 V)
      (fun T : DistributionSpace 𝕜 Ω => T.comp A)

def WeakConvergence : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ι : Type) (p : Filter ι) (u : ι → DistributionSpace 𝕜 Ω) (T : DistributionSpace 𝕜 Ω),
    Tendsto u p (@nhds _ (distributionWeakTopology 𝕜 Ω) T) ↔
      ∀ φ, Tendsto (fun i => u i φ) p (𝓝 (T φ))

def StrongConvergence : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ι : Type) (p : Filter ι) (u : ι → DistributionSpace 𝕜 Ω) (T : DistributionSpace 𝕜 Ω),
    Tendsto u p (@nhds _ (distributionStrongTopology 𝕜 Ω) T) ↔
      ∀ B : Set (TestSpace 𝕜 Ω), Bornology.IsVonNBounded 𝕜 B →
        TendstoUniformlyOn (fun i φ => u i φ) (fun φ => T φ) p B

def RestrictionTransitive : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (W V Ω : Opens (Space d))
    (hWV : W ≤ V) (hVΩ : V ≤ Ω) (T : DistributionSpace 𝕜 Ω),
    restrictDistribution hWV (restrictDistribution hVΩ T) =
      restrictDistribution (hWV.trans hVΩ) T

def ProductRule : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (M : TestMultiplierFamily 𝕜 Ω), HasMultiplierGraph M →
    ∀ (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω) (i : Fin d),
      distributionPartial {i} (transposeMultiplier M a T) =
        transposeMultiplier M (coefficientPartial i a) T +
        transposeMultiplier M a (distributionPartial {i} T)

def IteratedProductRule : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (M : TestMultiplierFamily 𝕜 Ω), HasMultiplierGraph M →
    ∀ (l : List (Fin d)) (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω),
      distributionPartial (l : Multiset (Fin d)) (transposeMultiplier M a T) =
        leibnizExpansion M l a T

/-- All conclusions hold for one constructed multiplier family, without any
additional certificate or regularity assumption on its input coefficients. -/
def MultiplicationOperations : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    ∃ M : TestMultiplierFamily 𝕜 Ω, HasMultiplierGraph M ∧
      (∀ a : SmoothCoefficient 𝕜 Ω,
        @Continuous _ _ (distributionWeakTopology 𝕜 Ω) (distributionWeakTopology 𝕜 Ω)
          (transposeMultiplier M a) ∧
        @Continuous _ _ (distributionStrongTopology 𝕜 Ω) (distributionStrongTopology 𝕜 Ω)
          (transposeMultiplier M a)) ∧
      (∀ (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω) (i : Fin d),
        distributionPartial {i} (transposeMultiplier M a T) =
          transposeMultiplier M (coefficientPartial i a) T +
          transposeMultiplier M a (distributionPartial {i} T)) ∧
      (∀ (l : List (Fin d)) (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω),
        distributionPartial (l : Multiset (Fin d)) (transposeMultiplier M a T) =
          leibnizExpansion M l a T)

def RestrictionOperations : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d)) (h : V ≤ Ω),
    Continuous (zeroExtension 𝕜 h) ∧
      (∀ (φ : TestSpace 𝕜 V) x, zeroExtension 𝕜 h φ x = φ x) ∧
      @Continuous _ _ (distributionWeakTopology 𝕜 Ω) (distributionWeakTopology 𝕜 V)
        (restrictDistribution h) ∧
      @Continuous _ _ (distributionStrongTopology 𝕜 Ω) (distributionStrongTopology 𝕜 V)
        (restrictDistribution h)

end OperationsExpected
end P102.U4
