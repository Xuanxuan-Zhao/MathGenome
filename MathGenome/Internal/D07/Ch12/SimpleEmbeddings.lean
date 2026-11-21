import MathGenome.Internal.Specs.D07.Ch12.SimpleEmbeddings
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Simple embeddings and conjugate roots (K07.12.simple_embeddings).

The fixed-base correspondence uses the power basis of the simple field.
For a base isomorphism σ, the transported minimal polynomial is monic and
irreducible and vanishes at β, hence is its minimal polynomial. Transporting
the quotient presentation along σ constructs the desired field isomorphism.
Agreement on constants and the class of X proves uniqueness on the quotient,
then on the simple field. No separability or closedness hypothesis is used.
-/

universe u v w z

namespace D07.Ch12.SimpleEmbeddings

open Polynomial IntermediateField
open Specs.D07.Ch12.SimpleEmbeddings

theorem embeddingsRoots : EmbeddingsRoots.{u, v, w} := by
  intro K L Ω _ _ _ _ _ α hα
  let e := IntermediateField.algHomAdjoinIntegralEquiv (K := Ω) K hα.isIntegral
  have hm : minpoly K α ≠ 0 := minpoly.ne_zero hα.isIntegral
  let r : {β : Ω // β ∈ (minpoly K α).aroots Ω} ≃
      {β : Ω // aeval β (minpoly K α) = 0} :=
    Equiv.subtypeEquiv (Equiv.refl Ω) (fun β => by
      simp only [Equiv.refl_apply, mem_aroots, hm, ne_eq, not_false_eq_true, true_and])
  refine ⟨e.trans r, ?_⟩
  intro f
  change (e f).val = f (AdjoinSimple.gen K α)
  have h := algHomAdjoinIntegralEquiv_symm_apply_gen (K := Ω) K hα.isIntegral (e f)
  change e.symm (e f) (AdjoinSimple.gen K α) = (e f).val at h
  simpa only [Equiv.symm_apply_apply] using h.symm

theorem baseIsomorphismExtension : BaseIsomorphismExtension.{u, v, w, z} := by
  intro K K' L L' _ _ _ _ _ _ σ α hα β hβ
  have hmon : ((minpoly K α).map σ.toRingHom).Monic :=
    (minpoly.monic hα.isIntegral).map _
  have hirr : Irreducible ((minpoly K α).map σ.toRingHom) := by
    change Irreducible ((Polynomial.mapEquiv σ) (minpoly K α))
    exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv σ)).mpr
      (minpoly.irreducible hα.isIntegral)
  have hmin : (minpoly K α).map σ.toRingHom = minpoly K' β :=
    minpoly.eq_of_irreducible_of_monic hirr hβ hmon
  have hβint : IsIntegral K' β := ⟨_, hmon, hβ⟩
  let eα := adjoinRootEquivAdjoin K hα.isIntegral
  let eβ := adjoinRootEquivAdjoin K' hβint
  let q := AdjoinRoot.mapRingEquiv σ (minpoly K α) (minpoly K' β)
    (hmin ▸ Associated.refl _)
  let e := eα.symm.toRingEquiv.trans (q.trans eβ.toRingEquiv)
  have hegen : e (AdjoinSimple.gen K α) = AdjoinSimple.gen K' β := by
    simp [e, q, eα, eβ, adjoinRootEquivAdjoin_symm_apply_gen,
      AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.map_root,
      adjoinRootEquivAdjoin_apply_root]
  have hescal : ∀ a : K, e (algebraMap K (adjoin K {α}) a) =
      algebraMap K' (adjoin K' {β}) (σ a) := by
    intro a
    simp [e, q, AdjoinRoot.coe_mapRingEquiv, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.map_of]
    exact eβ.commutes (σ a)
  refine ⟨e, ⟨hegen, hescal⟩, ?_⟩
  intro e' he'
  have hcomp : e'.toRingHom.comp eα.toAlgHom.toRingHom =
      e.toRingHom.comp eα.toAlgHom.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro a
      change e' (eα (algebraMap K _ a)) = e (eα (algebraMap K _ a))
      rw [eα.commutes]
      exact (he'.2 a).trans (hescal a).symm
    · change e' (eα (AdjoinRoot.root _)) = e (eα (AdjoinRoot.root _))
      rw [adjoinRootEquivAdjoin_apply_root K hα.isIntegral]
      exact he'.1.trans hegen.symm
  apply RingEquiv.ext
  intro x
  obtain ⟨p, rfl⟩ := eα.surjective x
  exact RingHom.congr_fun hcomp p

theorem transcendentalBoundary : TranscendentalBoundary.{u, v, w} := by
  intro K L Ω _ _ _ _ _ α hα
  have hm : minpoly K α = 0 :=
    minpoly.eq_zero (fun h => hα h.isAlgebraic)
  refine ⟨?_, hm, ?_⟩
  · intro f hf
    have hgen : IsAlgebraic K (AdjoinSimple.gen K α) :=
      (isAlgebraic_algHom_iff f f.injective).mp hf
    exact hα (hgen.algHom (adjoin K {α}).val)
  · intro β
    rw [hm, map_zero]

end D07.Ch12.SimpleEmbeddings
