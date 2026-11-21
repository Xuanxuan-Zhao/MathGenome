import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Canonical derivative graph for the integer order Sobolev spaces on arbitrary
open Euclidean sets. Scalars are real or complex, and p includes infinity.
The finite index type includes order zero, also in dimension zero. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Distributions

namespace ExpandedFA.Sobolev
open ExpandedFA.Distributions

/-- Every multi-index of total degree at most m, listed exactly once. -/
abbrev DerivativeIndex (d m : ℕ) :=
  {α : Fin d → Fin (m + 1) // ∑ i, (α i).val ≤ m}

def zeroIndex (d m : ℕ) : DerivativeIndex d m := ⟨fun _ => 0, by simp⟩

def natIndex {d m : ℕ} (α : DerivativeIndex d m) : Fin d → ℕ := fun i => (α.val i).val

abbrev DomainLp (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] := Lp 𝕜 p (volume.restrict (Ω : Set (Domain d)))

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An Lp element is locally integrable for the restricted volume. -/
theorem domainLp_locallyIntegrable (u : DomainLp 𝕜 Ω p) :
    LocallyIntegrableOn u Ω (volume.restrict (Ω : Set (Domain d))) :=
  ((Lp.memLp u).locallyIntegrable Fact.out).locallyIntegrableOn _

/-- The scalar-linear regular distribution of the Lp a.e. class. The restricted
measure means values outside Ω carry no data and impose no boundary condition. -/
def lpDistribution (u : DomainLp 𝕜 Ω p) : ScalarDistribution 𝕜 Ω :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜)
    (volume.restrict (Ω : Set (Domain d))) u

@[simp] theorem lpDistribution_apply (u : DomainLp 𝕜 Ω p) (φ : Tests 𝕜 Ω) :
    lpDistribution u φ = ∫ x, φ x * u x ∂(volume.restrict (Ω : Set (Domain d))) :=
  TestFunction.integralAgainstBilinCLM_eq_integral (domainLp_locallyIntegrable u)

/-- Integration respects the quotient's scalar-linear structure. -/
def lpDistributionLM : DomainLp 𝕜 Ω p →ₗ[𝕜] ScalarDistribution 𝕜 Ω where
  toFun := lpDistribution
  map_add' u v := by
    ext φ
    simp only [lpDistribution_apply, add_apply]
    have hu : Integrable (fun x => φ x * u x) (volume.restrict (Ω : Set (Domain d))) :=
      φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable u)
    have hv : Integrable (fun x => φ x * v x) (volume.restrict (Ω : Set (Domain d))) :=
      φ.integrable_bilin (ContinuousLinearMap.mul 𝕜 𝕜) (domainLp_locallyIntegrable v)
    rw [← integral_add hu hv]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add u v] with x hx
    rw [hx]
    exact mul_add _ _ _
  map_smul' c u := by
    ext φ
    simp only [lpDistribution_apply, smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp [hx, mul_left_comm]

/-- The finite derivative tuple uses the sum norm, regardless of p. -/
abbrev DerivativeTuple (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  PiLp 1 (fun _ : DerivativeIndex d m => DomainLp 𝕜 Ω p)

/-- Distributional derivative compatibility. Pairings have no conjugation. -/
def derivativeGraph (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule 𝕜 (DerivativeTuple 𝕜 Ω m p) where
  carrier := {v | ∀ α, lpDistributionLM (v α) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
      𝕜 d Ω (natIndex α) (lpDistributionLM (v (zeroIndex d m)))}
  zero_mem' := by
    intro α
    ext φ
    simp [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue]
  add_mem' := by
    intro u v hu hv α
    simp only [PiLp.add_apply, map_add, hu α, hv α]
    simp [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, smul_add]
  smul_mem' := by
    intro c v hv α
    simp only [PiLp.smul_apply, map_smul, hv α]
    ext φ
    simp [Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue, mul_left_comm]

end ExpandedFA.Sobolev

namespace Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions

def SpaceType := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
  (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], Type

abbrev SpaceValue : SpaceType := fun 𝕜 _ _ Ω m p _ => derivativeGraph 𝕜 Ω m p

def NormType := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
  (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], SpaceValue 𝕜 d Ω m p → ℝ

def NormValue : NormType := fun _ _ _ _ _ _ _ u => ∑ α, ‖u.val α‖

def HilbertNormType := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
  (m : ℕ), SpaceValue 𝕜 d Ω m 2 → ℝ

def HilbertNormValue : HilbertNormType :=
  fun _ _ _ _ _ u => Real.sqrt (∑ α, ‖u.val α‖ ^ 2)

/-- Compactly supported smooth members, as actual a.e. classes on Ω. -/
def SmoothMembers (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Set (SpaceValue 𝕜 d Ω m p) :=
  {u | ∃ φ : Tests 𝕜 Ω, u.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ}

/-- The compactly supported smooth classes form a linear subspace. -/
def smoothSubmodule (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule 𝕜 (SpaceValue 𝕜 d Ω m p) where
  carrier := SmoothMembers 𝕜 d Ω m p
  zero_mem' := by
    refine ⟨0, ?_⟩
    exact Lp.coeFn_zero 𝕜 p (volume.restrict (Ω : Set (Domain d)))
  add_mem' := by
    rintro u v ⟨φ, hφ⟩ ⟨ψ, hψ⟩
    refine ⟨φ + ψ, ?_⟩
    filter_upwards [Lp.coeFn_add (u.val (zeroIndex d m)) (v.val (zeroIndex d m)),
      hφ, hψ] with x hx hφx hψx
    change ((u.val (zeroIndex d m) + v.val (zeroIndex d m)) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg₂ (· + ·) hφx hψx
  smul_mem' := by
    rintro c u ⟨φ, hφ⟩
    refine ⟨c • φ, ?_⟩
    filter_upwards [Lp.coeFn_smul c (u.val (zeroIndex d m)), hφ] with x hx hφx
    change (c • u.val (zeroIndex d m) : DomainLp 𝕜 Ω p) x = _
    rw [hx]
    exact congrArg (c • ·) hφx

/-- Only finite p is assigned a W₀ space by the paper's closure definition. -/
def ZeroSpaceType := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
  (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → Submodule 𝕜 (SpaceValue 𝕜 d Ω m p)

def ZeroSpaceValue : ZeroSpaceType :=
  fun 𝕜 _ d Ω m p _ _ => (smoothSubmodule 𝕜 d Ω m p).topologicalClosure

/-- Projection onto order zero identifies graph elements with Lp functions. -/
def UnderlyingInjective : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  Function.Injective (fun u : SpaceValue 𝕜 d Ω m p => u.val (zeroIndex d m))

/-- Exact characterization of the Lp functions which occur, using all ordinary
natural-valued multi-indices of total order ≤ m. -/
def Membership : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p),
  (∃ v : SpaceValue 𝕜 d Ω m p, v.val (zeroIndex d m) = u) ↔
  ∀ α : Fin d → ℕ, (∑ i, α i) ≤ m → ∃ g : DomainLp 𝕜 Ω p,
    lpDistribution g =
      Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
        𝕜 d Ω α (lpDistribution u)

def NormFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
  (u : SpaceValue 𝕜 d Ω m p), ‖u‖ = NormValue 𝕜 d Ω m p u

/-- Equivalence to the Euclidean derivative-tuple norm; its Hilbert structure
and completeness are proved in the separate Sobolev-completeness goal. -/
def HilbertNormEquivalent : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (u : SpaceValue 𝕜 d Ω m 2),
  HilbertNormValue 𝕜 d Ω m u ≤ ‖u‖ ∧
  ‖u‖ ≤ Fintype.card (DerivativeIndex d m) * HilbertNormValue 𝕜 d Ω m u

/-- Closure uses the sum norm on this very graph space. -/
def ZeroClosure : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
  (ZeroSpaceValue 𝕜 d Ω m p hp : Set _) = closure (SmoothMembers 𝕜 d Ω m p)

/-- Every test function is represented in the derivative graph, with no
finite-p or boundary-regularity assumption needed for this inclusion. -/
def SmoothInclusion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : Tests 𝕜 Ω),
  ∃ u : SpaceValue 𝕜 d Ω m p,
    u.val (zeroIndex d m) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ

end Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
