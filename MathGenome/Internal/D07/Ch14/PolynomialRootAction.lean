import MathGenome.Internal.Specs.D07.Ch14.PolynomialRootAction
import MathGenome.Internal.D07.Ch14.SplittingCriterion
import Mathlib.FieldTheory.Normal.Basic

/-!
Root permutation actions, K07.14.polynomial_root_action.
Fixing the roots fixes the field they generate. Separability and splitting
give the root count, and conjugation by a numbering gives the S_n embedding.
For irreducible f, all roots have the same minimal polynomial; the normal
extension's conjugate-root orbit theorem supplies an automorphism between them.
-/

universe u v

namespace D07.Ch14.PolynomialRootAction

open Polynomial Specs.D07.Ch14.PolynomialRootAction

def rootPermutation : RootPermutationType.{u, v} := rootPermutationValue

theorem rootPermutation_apply : RootPermutationApply.{u, v} := by
  intro K L _ _ _ f σ a
  rfl

theorem rootCount : RootCount.{u, v} := by
  intro K L _ _ _ f _hpos hsep hsplit
  exact Polynomial.card_rootSet_eq_natDegree hsep hsplit.2.1

theorem rootActionFaithful : RootActionFaithful.{u, v} := by
  intro K L _ _ _ f _hpos _hsep hsplit σ τ hστ
  apply AlgEquiv.ext
  intro x
  have hx : x ∈ IntermediateField.adjoin K (f.rootSet L) := by
    rw [hsplit.2.2]
    exact IntermediateField.mem_top
  refine IntermediateField.adjoin_induction K
    (motive := fun x _ => σ x = τ x) ?_ ?_ ?_ ?_ ?_ hx
  · intro a ha
    exact congrArg Subtype.val (Equiv.congr_fun hστ ⟨a, ha⟩)
  · intro a
    rw [σ.commutes, τ.commutes]
  · intro a b _ _ ha hb
    rw [map_add, map_add, ha, hb]
  · intro a _ ha
    rw [map_inv₀, map_inv₀, ha]
  · intro a b _ _ ha hb
    rw [map_mul, map_mul, ha, hb]

theorem embeddingAfterNumbering : EmbeddingAfterNumbering.{u, v} := by
  intro K L _ _ _ f n hpos hsep hsplit _hn b
  let ρ : (L ≃ₐ[K] L) →* Equiv.Perm (Fin n) :=
    b.symm.permCongrHom.toMonoidHom.comp (rootPermutation K L f)
  refine ⟨ρ, ?_, ?_⟩
  · exact b.symm.permCongrHom.injective.comp
      (rootActionFaithful K L f hpos hsep hsplit)
  · intro σ i
    change (b (b.symm (rootPermutationValue K L f σ (b i)))).val = _
    rw [b.apply_symm_apply]
    rfl

theorem numberedEmbedding : NumberedEmbedding.{u, v} := by
  intro K L _ _ _ f n hpos hsep hsplit hn
  let b := (Fintype.equivFinOfCardEq ((rootCount K L f hpos hsep hsplit).trans hn)).symm
  exact ⟨b, embeddingAfterNumbering K L f n hpos hsep hsplit hn b⟩

theorem rootActionTransitive : RootActionTransitive.{u, v} := by
  intro K L _ _ _ f _hpos hsep hsplit hirr a b
  let : Normal K L := (SplittingCriterion.separableSplittingFieldGalois K L f hsep hsplit).2.1
  have ha := minpoly.eq_of_irreducible hirr (Polynomial.mem_rootSet.mp a.property).2
  have hb := minpoly.eq_of_irreducible hirr (Polynomial.mem_rootSet.mp b.property).2
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).mp (hb.symm.trans ha)
  exact ⟨σ, Subtype.ext hσ⟩

end D07.Ch14.PolynomialRootAction
