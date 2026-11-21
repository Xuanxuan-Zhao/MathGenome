import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveRieszMarkov
import MathGenome.Internal.RealAnalysis.D11.Ch19.CzeroDuality
import MathGenome.Internal.RealAnalysis.D11.Ch18.RadonSigmaFiniteInner
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.CompactRepresentation
import Mathlib.Analysis.Normed.Operator.NormedSpace

noncomputable section
namespace D11.Ch19.CompactRepresentation
open Set MeasureTheory
universe u
variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

/-- On a compact domain, the native C(X) and C0 spaces are linearly isometric
by the identity on underlying functions. This also handles the empty space. -/
def continuousCzeroEquiv (𝕜 : Type) [RCLike 𝕜] :
    C(X, 𝕜) ≃ₗᵢ[𝕜] ZeroAtInftyContinuousMap X 𝕜 where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl
  norm_map' f := by
    apply le_antisymm
    · apply (czero_norm_le_iff X 𝕜 _ ‖f‖ (norm_nonneg f)).mpr
      exact f.norm_coe_le_norm
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      exact (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f).toBCF.norm_coe_le_norm x

@[simp] lemma continuousCzeroEquiv_apply (𝕜 : Type) [RCLike 𝕜]
    (f : C(X, 𝕜)) (x : X) : continuousCzeroEquiv 𝕜 f x = f x := rfl

@[simp] lemma continuousCzeroEquiv_symm_apply (𝕜 : Type) [RCLike 𝕜]
    (f : ZeroAtInftyContinuousMap X 𝕜) (x : X) :
    (continuousCzeroEquiv 𝕜).symm f x = f x := rfl

theorem function_spaces : Specs.D11.Ch19.CompactRepresentation.function_spaces.{u} := by
  intro X _ _ _ 𝕜 _ f
  constructor
  · refine ⟨CompactlySupportedContinuousMap.continuousMapEquiv f, rfl, ?_⟩
    intro g hg
    exact DFunLike.coe_injective hg
  · refine ⟨continuousCzeroEquiv 𝕜 f, rfl, ?_⟩
    intro g hg
    exact DFunLike.coe_injective hg

theorem positive_real_representation :
    Specs.D11.Ch19.CompactRepresentation.positive_real_representation.{u} := by
  intro X _ _ _ I hI
  let J : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ :=
    I.comp
      ({ toFun := fun f => f.toContinuousMap
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => by ext x; rfl } :
        CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] C(X, ℝ))
  obtain ⟨μ, hμ, huniq⟩ := PositiveRieszMarkov.real_representation J (fun f hf => hI _ hf)
  have hfin : IsFiniteMeasure μ := ⟨hμ.1.1 univ isCompact_univ⟩
  let _ := hfin
  refine ⟨μ, ⟨D11.Ch18.RadonSigmaFiniteInner.sigmaFinite_fully_regular μ hμ.1 inferInstance,
    hfin, ?_⟩, ?_⟩
  · intro f
    exact hμ.2 (CompactlySupportedContinuousMap.continuousMapEquiv f)
  · intro η hη
    apply huniq η
    refine ⟨hη.1.1, ?_⟩
    intro f
    exact hη.2.2 f.toContinuousMap

theorem bounded_real_representation :
    Specs.D11.Ch19.CompactRepresentation.bounded_real_representation.{u} := by
  intro X _ _ _ L
  let e := continuousCzeroEquiv (X := X) ℝ
  let M := L.comp (e.symm : ZeroAtInftyContinuousMap X ℝ →L[ℝ] C(X, ℝ))
  obtain ⟨T, hT, hn, _, hsurj⟩ := CzeroDuality.real_duality X
  obtain ⟨ν, ⟨hν, he⟩, huniq⟩ := hsurj M
  have hnorm : ‖M‖ = ‖L‖ := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv L e.symm
  refine ⟨ν, hν, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨hf, hfint⟩ := hT ν (e f)
    refine ⟨hf, ?_⟩
    rw [he] at hfint
    exact hfint
  · rw [← hnorm, ← he]
    exact hn ν hν
  · intro η hη hηrep
    apply huniq η
    refine ⟨hη, ?_⟩
    ext f
    obtain ⟨hf, hfint⟩ := hT η f
    obtain ⟨hg, hgint⟩ := hηrep (e.symm f)
    exact hfint.trans hgint.symm

theorem bounded_complex_representation :
    Specs.D11.Ch19.CompactRepresentation.bounded_complex_representation.{u} := by
  intro X _ _ _ L
  let e := continuousCzeroEquiv (X := X) ℂ
  let M := L.comp (e.symm : ZeroAtInftyContinuousMap X ℂ →L[ℂ] C(X, ℂ))
  obtain ⟨T, hT, hn, _, hsurj⟩ := CzeroDuality.complex_duality X
  obtain ⟨ν, ⟨hν, he⟩, huniq⟩ := hsurj M
  have hnorm : ‖M‖ = ‖L‖ := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv L e.symm
  refine ⟨ν, hν, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨hf, hfint⟩ := hT ν (e f)
    refine ⟨hf, ?_⟩
    rw [he] at hfint
    exact hfint
  · rw [← hnorm, ← he]
    exact hn ν hν
  · intro η hη hηrep
    apply huniq η
    refine ⟨hη, ?_⟩
    ext f
    obtain ⟨hf, hfint⟩ := hT η f
    obtain ⟨hg, hgint⟩ := hηrep (e.symm f)
    exact hfint.trans hgint.symm

end D11.Ch19.CompactRepresentation
