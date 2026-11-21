import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import Mathlib.Topology.ContinuousMap.Compact

/-! Smooth functions on an open set, with their actual local derivative topology.
Representatives are normalized to zero outside Ω, so equality is equality on Ω.
No regularity at the boundary or global extension is imposed. -/
open Set TopologicalSpace
open scoped Distributions Topology ContDiff

namespace ExpandedFA.Distributions

/-- Smooth functions on Ω, represented by their zero extensions as raw functions.
The zero extension is required to be smooth only inside Ω. -/
def smoothFunctionsSubmodule (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : Submodule 𝕜 (Domain d → 𝕜) where
  carrier := {f | ContDiffOn ℝ ∞ f Ω ∧ EqOn f 0 (Ω : Set (Domain d))ᶜ}
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, hf0⟩ ⟨hg, hg0⟩
    exact ⟨hf.add hg, fun x hx => by simp [hf0 hx, hg0 hx]⟩
  smul_mem' := by
    rintro c f ⟨hf, hf0⟩
    exact ⟨hf.const_smul c, fun x hx => by simp [hf0 hx]⟩

abbrev SmoothFunctions (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :=
  smoothFunctionsSubmodule 𝕜 Ω

/-- Indexing set for compact-local derivatives. -/
abbrev SmoothJetIndex {d : ℕ} (Ω : Opens (Domain d)) :=
  {K : Compacts (Domain d) // (K : Set (Domain d)) ⊆ Ω} × ℕ

/-- Restriction of the n-th derivative to a compact subset of Ω. -/
noncomputable def smoothJetLM (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (q : SmoothJetIndex Ω) :
    SmoothFunctions 𝕜 Ω →ₗ[𝕜] C(q.1.val, (Domain d) [×q.2]→L[ℝ] 𝕜) where
  toFun f := ⟨fun x => iteratedFDeriv ℝ q.2 (f : Domain d → 𝕜) x,
    ((ContinuousOn.continuousOn_iteratedFDeriv f.property.1 Ω.isOpen (by simp)).mono
      q.1.property).domRestrict⟩
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    exact iteratedFDeriv_add_apply
      ((f.property.1.contDiffAt (Ω.isOpen.mem_nhds (q.1.property x.property))).of_le (by simp))
      ((g.property.1.contDiffAt (Ω.isOpen.mem_nhds (q.1.property x.property))).of_le (by simp))
  map_smul' c f := by
    apply ContinuousMap.ext
    intro x
    exact iteratedFDeriv_const_smul_apply
      ((f.property.1.contDiffAt (Ω.isOpen.mem_nhds (q.1.property x.property))).of_le (by simp))

/-- The compact-local sup seminorm of a full derivative. Full Fréchet derivatives
are equivalent to all coordinate partials in finite dimension. -/
noncomputable def smoothSeminorm (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (q : SmoothJetIndex Ω) : Seminorm 𝕜 (SmoothFunctions 𝕜 Ω) :=
  (normSeminorm 𝕜 C(q.1.val, (Domain d) [×q.2]→L[ℝ] 𝕜)).comp (smoothJetLM 𝕜 Ω q)

noncomputable instance smoothFunctionsTopology (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) : TopologicalSpace (SmoothFunctions 𝕜 Ω) :=
  (SeminormFamily.moduleFilterBasis (smoothSeminorm 𝕜 Ω)).topology

/-- The natural inclusion of test functions into C∞(Ω). -/
noncomputable def testToSmoothLM (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d)) :
    Tests 𝕜 Ω →ₗ[𝕜] SmoothFunctions 𝕜 Ω where
  toFun φ := ⟨φ, φ.contDiff.contDiffOn, fun _ hx => φ.zero_on_compl hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The local sup seminorm of an ordered coordinate partial derivative. -/
abbrev SmoothCoordinateIndex {d : ℕ} (Ω : Opens (Domain d)) :=
  Σ q : SmoothJetIndex Ω, Fin q.2 → Fin d

noncomputable def smoothCoordinateSeminorm (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (a : SmoothCoordinateIndex Ω) : Seminorm 𝕜 (SmoothFunctions 𝕜 Ω) :=
  (normSeminorm 𝕜 C(a.1.1.val, 𝕜)).comp
    (((coordinateEvaluation 𝕜 a.2).compLeftContinuous 𝕜 a.1.1.val).toLinearMap.comp
      (smoothJetLM 𝕜 Ω a.1))

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual
open _root_.ExpandedFA.Distributions

/-- Zero extension as a representative loses no smooth functions on Ω. -/
def representativesType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (f : Domain d → 𝕜), ContDiffOn ℝ ∞ f Ω →
  ∃! g : SmoothFunctions 𝕜 Ω, EqOn g.val f Ω

/-- The chosen topology is also the topology of uniform convergence of every
coordinate partial derivative on every compact subset. -/
def coordinateTopologyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), WithSeminorms (smoothCoordinateSeminorm 𝕜 Ω)

/-- Compact support is the only extra assumption on the distribution. The extension
is unique among all continuous scalar-linear functionals agreeing on tests. -/
def extensionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  IsCompact (distributionSupport u) →
  ∃! L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜,
    ∀ φ : Tests 𝕜 Ω, L (testToSmoothLM 𝕜 Ω φ) = u φ

/-- The extension can be evaluated using any cutoff equal to one on an open
neighborhood of the support, with independence of that cutoff. -/
def cutoffFormulaType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω),
  IsCompact (distributionSupport u) →
  ∃ L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜,
    (∀ φ : Tests 𝕜 Ω, L (testToSmoothLM 𝕜 Ω φ) = u φ) ∧
    ∀ (χ : Tests 𝕜 Ω) (V : Set (Domain d)),
      IsOpen V → distributionSupport u ⊆ V → EqOn χ 1 V →
      ∀ f : SmoothFunctions 𝕜 Ω,
        ∃ ψ : Tests 𝕜 Ω, (∀ x, ψ x = χ x * f.val x) ∧ L f = u ψ

/-- Every continuous scalar-linear functional on C∞ restricts to an LF-continuous
distribution and its actual support is compact in Ω. -/
def converseType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜),
  ∃ u : ScalarDistribution 𝕜 Ω,
    (∀ φ : Tests 𝕜 Ω, u φ = L (testToSmoothLM 𝕜 Ω φ)) ∧
    IsCompact (distributionSupport u)

/-- The explicit one-dimensional distribution counterexample, over either scalar
field. The function x vanishes on the exact support of δ′, but its product with
δ′ is −δ. Delta and its derivative are specified by their actual test pairings. -/
def deltaCounterexampleType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  let Ω : Opens (Domain 1) := ⊤
  ∃ (δ δ' : ScalarDistribution 𝕜 Ω)
    (X : Domain 1 → 𝕜) (hX : ContDiff ℝ (⊤ : ℕ∞) X),
    (∀ φ : Tests 𝕜 Ω, δ φ = φ 0) ∧
    (∀ φ : Tests 𝕜 Ω, δ' φ = -fderiv ℝ φ 0 (coordinateVector 0)) ∧
    (∀ x, X x = (x 0 : 𝕜)) ∧
    distributionSupport δ' = {0} ∧
    EqOn X 0 (distributionSupport δ') ∧
    δ'.comp (multiplyTest X hX) = -δ ∧ δ ≠ 0

end Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual
