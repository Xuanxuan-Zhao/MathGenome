import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.CyclotomicAbelianFields
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.PrescribedExtension
import Mathlib.Data.Fintype.Powerset
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.LinearDisjoint
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.DisjointAbelianRealization

namespace GaloisFormalization.IG

open GH.KrullLayers IntermediateField

/-- A finite abelian group has a realization disjoint from a prescribed finite Galois field. -/
theorem exists_disjoint_abelian_realization :
    Specs.GaloisFormalization.IG.disjointAbelianRealization_type := by
  intro Ω _ _ _ A _ _ E
  let : Algebra ℚ E := E.toIntermediateField.algebra'
  let : Finite (Subgroup (LayerGroup E)) :=
    Finite.of_injective (fun H : Subgroup (LayerGroup E) => (H : Set (LayerGroup E)))
      SetLike.coe_injective
  let correspondence : IntermediateField ℚ E ≃o (Subgroup (LayerGroup E))ᵒᵈ :=
    IsGalois.intermediateFieldEquivSubgroup
  let : Finite (IntermediateField ℚ E) := Finite.of_injective correspondence
    correspondence.injective
  let n := Nat.card (IntermediateField ℚ E)
  obtain ⟨K, hK, hpair, htrivial⟩ :=
    exists_pairwise_disjoint_galois_realizations Ω A (n + 1)
  have hdisjoint : ∃ j, K j ⊓ E.toIntermediateField = ⊥ := by
    by_contra h
    let intersection (j : Fin (n + 1)) : IntermediateField ℚ E :=
      IntermediateField.restrict (inf_le_right : K j ⊓ E.toIntermediateField ≤ _)
    have hinj : Function.Injective intersection := by
      intro i j hij
      by_contra hne
      have heq : K i ⊓ E.toIntermediateField = K j ⊓ E.toIntermediateField := by
        simpa only [intersection, IntermediateField.lift_restrict] using
          congrArg E.toIntermediateField.lift hij
      apply h
      refine ⟨i, le_antisymm ?_ bot_le⟩
      calc
        K i ⊓ E.toIntermediateField ≤ K i ⊓ K j :=
          le_inf inf_le_left (heq ▸ inf_le_left)
        _ = ⊥ := hpair i j hne
    have hcard := Nat.card_le_card_of_injective intersection hinj
    rw [Nat.card_fin] at hcard
    exact Nat.not_succ_le_self n hcard
  obtain ⟨j, hj⟩ := hdisjoint
  obtain ⟨hf, hg, ⟨e⟩⟩ := hK j
  let F : FiniteGaloisIntermediateField ℚ Ω :=
    { toIntermediateField := K j
      finiteDimensional := hf
      isGalois := hg }
  refine ⟨F, e, hj, fun h => FiniteGaloisIntermediateField.val_injective ?_⟩
  exact htrivial h j

/-- For finite Galois layers with trivial intersection, joint restriction from
their compositum is bijective. -/
private theorem compositum_restriction_bijective {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    (F E : FiniteGaloisIntermediateField ℚ Ω)
    (h : F.toIntermediateField ⊓ E.toIntermediateField = ⊥) :
    Function.Bijective
      ((transition (le_sup_left : F ≤ F ⊔ E)).toMonoidHom.prod
        (transition (le_sup_right : E ≤ F ⊔ E)).toMonoidHom) := by
  change Function.Bijective (restrictNormalHomSupProd F.toIntermediateField E.toIntermediateField)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨restrictNormalHomSupProd_injective _ _, ?_⟩
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank]
  exact (LinearDisjoint.of_inf_eq_bot h).finrank_sup

/-- The proper solution for the second projection has solution field the
compositum of the prescribed field and the disjoint realization. -/
theorem exists_disjoint_abelian_embedding_solution :
    Specs.GaloisFormalization.IG.disjointAbelianEmbeddingSolution_type := by
  intro Ω _ _ _ A _ _ E
  dsimp only
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let π := ContinuousMonoidHom.snd A (LayerGroup E)
  have hπ : Function.Surjective π := fun g => ⟨(1, g), rfl⟩
  obtain ⟨F, e, hdisjoint, htrivial⟩ := exists_disjoint_abelian_realization Ω A E
  let L := F ⊔ E
  have hFL : F ≤ L := le_sup_left
  have hEL : E ≤ L := le_sup_right
  let ι : LayerGroup L →* A × LayerGroup E :=
    (e.toMonoidHom.comp (transition hFL).toMonoidHom).prod (transition hEL).toMonoidHom
  have hbij : Function.Bijective ι :=
    (e.prodCongr (MulEquiv.refl (LayerGroup E))).bijective.comp
      (compositum_restriction_bijective F E hdisjoint)
  have hcomm : π.toMonoidHom.comp ι = (transition hEL).toMonoidHom := by
    ext1 σ
    rfl
  obtain ⟨s, hlift, hfield, hproper⟩ :=
    weakSolution_of_extension E π hπ L hEL ι hbij.injective hcomm
  exact ⟨⟨MonoidHom.inr A (LayerGroup E), rfl⟩, F, e, hdisjoint, htrivial, s,
    hproper.mpr ⟨MulEquiv.ofBijective ι hbij, rfl⟩, hlift, hfield.symm⟩

/-- Every finite abelian group occurs as a Galois group over `ℚ`. -/
theorem exists_finite_abelian_realization :
    Specs.GaloisFormalization.IG.finiteAbelianRealization_type := by
  intro A _ _
  obtain ⟨F, e, _, _⟩ :=
    exists_disjoint_abelian_realization (AlgebraicClosure ℚ) A ⊥
  exact ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, ⟨e⟩⟩

end GaloisFormalization.IG
