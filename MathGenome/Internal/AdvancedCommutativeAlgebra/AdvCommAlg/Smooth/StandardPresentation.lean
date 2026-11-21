import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.JacobianPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.StandardPresentation

/-! Standard smooth presentations, SM-03. The presentation includes generators
and relations spanning precisely the kernel. Selected rows use every relation
column, in the convention of KD-12. -/
namespace AdvCommAlg.Smooth

universe u v
noncomputable section
open Specs.AdvCommAlg.Smooth

abbrev selectedMinor : selectedMinorType.{u,v} := @selectedMinorValue
abbrev PresentationStandardSmooth : presentationStandardSmoothType.{u,v} :=
  @presentationStandardSmoothValue
abbrev StandardSmooth : standardSmoothType.{u,v} := standardSmoothValue

theorem selected_minor_entries : minorEntries.{u,v} := by
  intro A B _ _ _ n c P a i j
  rfl

theorem selected_minor_jacobian : minorJacobian.{u,v} := by
  intro A B _ _ _ n c P
  rw [P.jacobian_eq_jacobiMatrix_det, RingHom.map_det]
  congr 1
  ext i j
  change algebraMap P.Ring B (P.jacobiMatrix i j) = _
  rw [P.jacobiMatrix_apply, P.algebraMap_apply]
  rfl

theorem presentation_standard_smooth_iff_submersive : submersiveIff.{u,v} := by
  intro A B _ _ _ n c P
  constructor
  · rintro ⟨a, ha⟩
    let Q : Algebra.PreSubmersivePresentation A B (Fin n) (Fin c) :=
      { P with map := a, map_inj := a.injective }
    refine ⟨{ Q with jacobian_isUnit := ?_ }, rfl⟩
    rw [selected_minor_jacobian Q]
    exact ha
  · rintro ⟨Q, rfl⟩
    refine ⟨⟨Q.map, Q.map_inj⟩, ?_⟩
    rw [← selected_minor_jacobian Q.toPreSubmersivePresentation]
    exact Q.jacobian_isUnit

theorem presentation_standard_smooth_bounds : presentationBounds.{u,v} := by
  intro A B _ _ _ n c P h
  obtain ⟨a, _⟩ := h
  simpa using Fintype.card_le_of_injective a a.injective

theorem standard_smooth_iff : standardSmoothIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h
    obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := h.out
    letI := hσ
    letI := hι
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite σ
    let Q := P.reindex (Fintype.equivFin ι).symm (Fintype.equivFin σ).symm
    exact ⟨_, _, Q.toPresentation,
      (presentation_standard_smooth_iff_submersive _).mpr ⟨Q, rfl⟩⟩
  · rintro ⟨n, c, P, hP⟩
    obtain ⟨Q, _⟩ := (presentation_standard_smooth_iff_submersive P).mp hP
    exact Q.isStandardSmooth

theorem empty_minor : emptyMinor.{u,v} := by
  intro A B _ _ _ n P a
  exact Matrix.det_isEmpty

theorem empty_presentation : emptyPresentation.{u,v} := by
  intro A B _ _ _ n P
  refine ⟨⟨Fin.elim0, by intro x; exact Fin.elim0 x⟩, ?_⟩
  rw [empty_minor P]
  exact isUnit_one

theorem selected_minor_reindex : minorReindex.{u,v} := by
  intro A B _ _ _ n c P a e f
  ext i j
  simp only [Specs.AdvCommAlg.Smooth.selectedMinor,
    Specs.AdvCommAlg.Differentials.presentationJacobian, Matrix.submatrix_apply,
    Algebra.Presentation.reindex, Algebra.Generators.reindex_val,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Function.comp_apply,
    MvPolynomial.pderiv_rename e.symm.injective]
  simp [← MvPolynomial.aeval_rename]

theorem selected_minor_det_reindex : minorDetReindex.{u,v} := by
  intro A B _ _ _ n c P a e f
  rw [selected_minor_reindex]
  exact Matrix.det_submatrix_equiv_self f _

theorem ordered_rows : orderedRows.{u,v} := by
  intro A B _ _ _ n c P a
  have h : c ≤ n := by simpa using Fintype.card_le_of_injective a a.injective
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castLE h) a (Fin.castLE_injective h) a.injective
  refine ⟨h, e, he, ?_⟩
  have ha : (Equiv.refl (Fin c)).toEmbedding.trans (a.trans e.symm.toEmbedding) =
      (⟨Fin.castLE h, Fin.castLE_injective h⟩ : Fin c ↪ Fin n) := by
    apply Function.Embedding.ext
    intro j
    change e.symm (a j) = Fin.castLE h j
    exact e.symm_apply_eq.mpr (he j).symm
  rw [← ha, selected_minor_reindex]
  rfl

theorem ordered_presentation : orderedPresentation.{u,v} := by
  intro A B _ _ _ n c P
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨h, e, _, hm⟩ := ordered_rows P a
    exact ⟨h, e, hm.symm ▸ ha⟩
  · rintro ⟨h, e, he⟩
    let a : Fin c ↪ Fin n :=
      (⟨Fin.castLE h, Fin.castLE_injective h⟩ : Fin c ↪ Fin n).trans e.toEmbedding
    refine ⟨a, ?_⟩
    have ha : (Equiv.refl (Fin c)).toEmbedding.trans (a.trans e.symm.toEmbedding) =
        (⟨Fin.castLE h, Fin.castLE_injective h⟩ : Fin c ↪ Fin n) := by
      apply Function.Embedding.ext
      intro j
      change e.symm (e (Fin.castLE h j)) = Fin.castLE h j
      exact e.symm_apply_apply _
    have hm := selected_minor_det_reindex P a e (Equiv.refl _)
    rw [ha] at hm
    exact hm ▸ he

end
end AdvCommAlg.Smooth
