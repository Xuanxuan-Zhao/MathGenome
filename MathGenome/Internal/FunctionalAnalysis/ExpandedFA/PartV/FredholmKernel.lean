import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.FredholmKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.RieszSchauder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.ContinuousKernelTranspose
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2KernelCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeaklySingularSurface
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Fredholm alternatives for the established kernel maps. We apply the
accepted Riesz–Schauder theorem to z • K. Closed range and Hahn–Banach
separation identify the range with the preannihilator of the transpose
kernel; Hilbert orthogonal complements give the conjugated-adjoint form. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate InnerProductSpace NNReal ENNReal
namespace ExpandedFA.PartV.FredholmKernel
universe u v
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- Closed subspaces are recovered by their continuous annihilators.
lemma mem_closed_submodule_iff (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)) (f : E) :
    f ∈ M ↔ ∀ φ : E →L[𝕜] 𝕜, (∀ x ∈ M, φ x = 0) → φ f = 0 := by
  constructor
  · exact fun hf φ hφ => hφ f hf
  · intro hf
    by_contra hn
    let : IsClosed (M : Set E) := hM
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := 𝕜)
      (show M.mkQ f ≠ 0 from fun h => hn ((Submodule.Quotient.mk_eq_zero M).mp h))
    apply hφ
    apply hf (φ.comp M.mkQL)
    intro x hx
    change φ (M.mkQ x) = 0
    rw [M.mkQ_apply, (Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]

lemma solvable_iff_transpose (A : E →L[𝕜] E)
    (hA : IsClosed (A.toLinearMap.range : Set E)) (f : E) :
    (∃ u, A u = f) ↔ ∀ φ : E →L[𝕜] 𝕜,
      P1.C04Annihilators.Spec.BanachTransposeValue 𝕜 E E A φ = 0 → φ f = 0 := by
  constructor
  · rintro ⟨u, rfl⟩ φ hφ
    exact DFunLike.congr_fun hφ u
  · intro hf
    change f ∈ A.toLinearMap.range
    apply (mem_closed_submodule_iff _ hA f).mpr
    intro φ hφ
    apply hf φ
    ext u
    exact hφ (A u) ⟨u, rfl⟩

lemma homogeneous_iff_eigenvector (K : E →L[𝕜] E) (z : 𝕜) (hz : z ≠ 0) (u : E) :
    u - z • K u = 0 ↔ K u = z⁻¹ • u := by
  rw [sub_eq_zero]
  constructor
  · intro h
    calc
      K u = z⁻¹ • (z • K u) := (inv_smul_smul₀ hz (K u)).symm
      _ = z⁻¹ • u := congrArg (fun x : E => z⁻¹ • x) h.symm
  · intro h
    rw [h, smul_inv_smul₀ hz]

lemma injective_iff_no_eigenvector (K : E →L[𝕜] E) (z : 𝕜) (hz : z ≠ 0) :
    Function.Injective (ContinuousLinearMap.id 𝕜 E - z • K) ↔
      ¬ ∃ u : E, u ≠ 0 ∧ K u = z⁻¹ • u := by
  change Function.Injective (ContinuousLinearMap.id 𝕜 E - z • K).toLinearMap ↔ _
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro h ⟨u, hu, he⟩
    apply hu
    have hm : u ∈ (ContinuousLinearMap.id 𝕜 E - z • K).toLinearMap.ker :=
      (homogeneous_iff_eigenvector K z hz u).mpr he
    rw [h] at hm
    exact hm
  · intro h
    apply bot_unique
    intro u hu
    change u = 0
    by_contra hn
    exact h ⟨u, hn, (homogeneous_iff_eigenvector K z hz u).mp hu⟩

theorem compact_alternative : Spec.CompactAlternative.{u,v} := by
  intro 𝕜 E _ _ _ K hK z hz
  let A := ContinuousLinearMap.id 𝕜 E - z • K
  have hc : Compactness.IsCompactLinearMap (z • K).toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr (hK.smul z)
  have h := Fredholm.riesz_schauder (z • K) hc
  refine ⟨?_, ?_, h.1, h.2.1, ?_⟩
  · change (∀ f, ∃! u, A u = f) ↔ _
    rw [← Function.bijective_iff_existsUnique]
    have hi := injective_iff_no_eigenvector K z hz
    constructor
    · exact fun hb => hi.mp hb.1
    · intro hn
      exact ⟨hi.mpr hn, h.2.2.2.1.mp (hi.mpr hn)⟩
  · intro f
    exact solvable_iff_transpose A h.2.1 f
  · intro f u₀ hu₀ u
    change A u = f ↔ ∃ v ∈ A.toLinearMap.ker, u = u₀ + v
    change A u₀ = f at hu₀
    constructor
    · intro hu
      refine ⟨u - u₀, ?_, by abel⟩
      change A (u - u₀) = 0
      rw [map_sub, hu, hu₀, sub_self]
    · rintro ⟨v, hv, rfl⟩
      change A v = 0 at hv
      rw [map_add, hv, add_zero, hu₀]

theorem hilbert_alternative : Spec.HilbertAlternative.{u,v} := by
  intro 𝕜 H _ _ _ _ K hK z hz
  have h := compact_alternative K hK z hz
  have ha : ContinuousLinearMap.adjoint (ContinuousLinearMap.id 𝕜 H - z • K) =
      ContinuousLinearMap.id 𝕜 H - conj z • ContinuousLinearMap.adjoint K := by
    simp only [map_sub, ContinuousLinearMap.adjoint_id, map_smulₛₗ]
  refine ⟨h, ha, ?_⟩
  intro f
  let A := ContinuousLinearMap.id 𝕜 H - z • K
  have hr : A.range = A.adjoint.kerᗮ := by
    rw [← A.orthogonal_range, Submodule.orthogonal_orthogonal_eq_closure]
    exact h.2.2.2.1.submodule_topologicalClosure_eq.symm
  change f ∈ A.range ↔ _
  rw [hr]
  rw [ha]

theorem continuous_application : Spec.ContinuousApplication.{u,v} := by
  intro 𝕜 X _ _ _ _ _ _ μ _ k z hz
  apply compact_alternative _ _ z hz
  exact (ContinuousKernel.canonical_operator_properties 𝕜 X X μ k).2.2.1

theorem l2_application : Spec.L2Application.{v} := by
  intro 𝕜 X _ _ μ _ k z hz
  have hc := L2KernelCompact.kernel_compact μ μ k
  have hn : IsCompactOperator (L2KernelSpec.OperatorValue μ μ k) :=
    (Compactness.compact_iff_isCompactOperator _).mp hc
  have h := hilbert_alternative _ hn z hz
  refine ⟨h.1, ?_⟩
  rw [← (L2KernelCompact.l2_kernel_adjoint_correct μ μ k).1]
  exact h.2.2

theorem established_integral_application : Spec.EstablishedIntegralApplication := by
  intro X 𝕜 _ _ _ _ μ k hk
  obtain ⟨⟨T, hT, hform⟩, hLp⟩ := hk
  refine ⟨⟨T, hform, fun z hz => compact_alternative T hT z hz⟩, ?_⟩
  intro p hp
  obtain ⟨T, hT, hform⟩ := hLp p
  exact ⟨T, hform, fun z hz => compact_alternative T hT z hz⟩

theorem euclidean_application : Spec.EuclideanApplication := by
  intro d 𝕜 _ _ _ G hG k α C M hα hk
  let : CompactSpace G := isCompact_iff_compactSpace.mp hG
  exact established_integral_application _ _
    (WeaklySingularEuclidean.euclidean_compactness d 𝕜 G hG k α C M hα hk)

theorem surface_application : Spec.SurfaceApplication := by
  intro n d 𝕜 _ _ _ S hS hcharts k α C M hα hk
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  exact established_integral_application _ _
    (WeaklySingularSurface.surface_compactness n d 𝕜 S hS hcharts k α C M hα hk)

end ExpandedFA.PartV.FredholmKernel
