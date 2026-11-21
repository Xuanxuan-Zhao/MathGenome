import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.Series
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Chief.EquivariantSecondIso

/-! Quotient maps for the diamond in the ambient-normal subgroup poset. -/

namespace ALG02GroupTheory.Chief

open Specs.ALG02GroupTheory.Chief.EquivariantSecondIso

attribute [local instance] quotientImageAction

universe u

variable {G : Type u} [Group G]

/-- Interpret the common factor model as the image of the upper subgroup in the
ambient quotient, with the same conjugation action. -/
theorem factor_quotient_image_equiv (K L : Subgroup G) [K.Normal] [L.Normal] (_ : K ≤ L) :
    letI := quotientImageAction K L
    ∃ e : GEquiv G (Factor K L) (quotientImage K L),
      ∀ x : L, (e.1 (factorMk K L x) : G ⧸ K) = QuotientGroup.mk' K (x : G) := by
  let φ : L →* quotientImage K L :=
    ((QuotientGroup.mk' K).comp L.subtype).codRestrict _ (fun x => ⟨x, x.property, rfl⟩)
  have hsurj : Function.Surjective φ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : K.subgroupOf L = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker, ← Subtype.coe_inj]
    exact (QuotientGroup.eq_one_iff (x : G)).symm
  let e : Factor K L ≃* quotientImage K L :=
    QuotientGroup.liftEquiv (K.subgroupOf L) hsurj hker
  refine ⟨⟨e, ?_⟩, fun _ => rfl⟩
  intro g z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf L) z
  change e (g • factorMk K L x) = g • e (factorMk K L x)
  rw [factor_smul_mk]
  apply Subtype.ext
  change QuotientGroup.mk' K (g * (x : G) * g⁻¹) =
    QuotientGroup.mk' K g * QuotientGroup.mk' K (x : G) * (QuotientGroup.mk' K g)⁻¹
  simp only [map_mul, map_inv]

/-- The representative map `yL ↦ yX` is an isomorphism for the normal
intersection `L = X ⊓ Y` and join `N = X ⊔ Y`. -/
theorem equivariant_second_iso (X Y L N : Subgroup G) [X.Normal] [Y.Normal]
    [L.Normal] [N.Normal] (hL : X ⊓ Y = L) (hN : X ⊔ Y = N) :
    ∃ e : GEquiv G (Factor L Y) (Factor X N),
      ∀ y : Y, e.1 (factorMk L Y y) =
        factorMk X N (Subgroup.inclusion (hN ▸ le_sup_right) y) := by
  have hKer : L.subgroupOf Y = X.subgroupOf Y := by
    rw [← hL]
    ext y
    exact ⟨fun hy => hy.1, fun hy => ⟨hy, y.property⟩⟩
  have hJoin : Y ⊔ X = N := (sup_comm Y X).trans hN
  let e : Factor L Y ≃* Factor X N :=
    (QuotientGroup.quotientMulEquivOfEq hKer).trans
      ((QuotientGroup.quotientInfEquivProdNormalQuotient Y X).trans
        (QuotientGroup.equivQuotientSubgroupOfOfEq rfl hJoin))
  have he (y : Y) :
      e (factorMk L Y y) = factorMk X N (Subgroup.inclusion (hN ▸ le_sup_right) y) := rfl
  refine ⟨⟨e, ?_⟩, he⟩
  intro g z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf Y) z
  change e (g • factorMk L Y y) = g • e (factorMk L Y y)
  simp only [factor_smul_mk, he]
  rfl

/-- The same comparison with codomain the image subgroup of `G ⧸ X`. -/
theorem equivariant_second_iso_image (X Y L N : Subgroup G) [X.Normal] [Y.Normal]
    [L.Normal] [N.Normal] (hL : X ⊓ Y = L) (hN : X ⊔ Y = N) :
    letI := quotientImageAction X N
    ∃ e : GEquiv G (Factor L Y) (quotientImage X N),
      ∀ y : Y, (e.1 (factorMk L Y y) : G ⧸ X) = QuotientGroup.mk' X (y : G) := by
  obtain ⟨e, he⟩ := equivariant_second_iso X Y L N hL hN
  obtain ⟨f, hf⟩ := factor_quotient_image_equiv X N (hN ▸ le_sup_left)
  refine ⟨⟨e.1.trans f.1, fun g z => ?_⟩, fun y => ?_⟩
  · change f.1 (e.1 (g • z)) = g • f.1 (e.1 z)
    rw [e.2, f.2]
  · change (f.1 (e.1 (factorMk L Y y)) : G ⧸ X) = QuotientGroup.mk' X (y : G)
    rw [he, hf]
    rfl

private theorem inf_covBy_right_of_covBy_sup (X Y : Subgroup G) [X.Normal] [Y.Normal]
    (h : AmbientCovBy X (X ⊔ Y)) : AmbientCovBy (X ⊓ Y) Y := by
  refine ⟨lt_of_le_of_ne inf_le_right ?_, ?_⟩
  · intro he
    have hYX : Y ≤ X := he ▸ inf_le_left
    exact (not_lt_of_ge (sup_le le_rfl hYX)) h.1
  · intro M hM hLM hMY
    have hmeet : (X ⊔ M) ⊓ Y = M := by
      refine le_antisymm ?_ (le_inf le_sup_right hMY.le)
      intro a ha
      obtain ⟨x, hx, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha.1
      have hxY : x ∈ Y := (Y.mul_mem_cancel_right (hMY.le hm)).mp ha.2
      exact M.mul_mem (hLM.le ⟨hx, hxY⟩) hm
    have hgt : X < X ⊔ M := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro he
      have hMX : M ≤ X := he.symm ▸ le_sup_right
      exact (not_lt_of_ge (le_inf hMX hMY.le)) hLM
    have hlt : X ⊔ M < X ⊔ Y := by
      refine lt_of_le_of_ne (sup_le_sup_left hMY.le X) ?_
      intro he
      have hYM : Y ≤ M := by
        rw [← hmeet, he]
        exact le_inf le_sup_right le_rfl
      exact (not_lt_of_ge hYM) hMY
    exact h.2 _ inferInstance hgt hlt

/-- Distinct immediate predecessors have the given top as their join, and
their intersection is an immediate predecessor of each. -/
theorem ambient_diamond (X Y N : Subgroup G) [X.Normal] [Y.Normal]
    (hX : AmbientCovBy X N) (hY : AmbientCovBy Y N) (hne : X ≠ Y) :
    X ⊔ Y = N ∧ AmbientCovBy (X ⊓ Y) X ∧ AmbientCovBy (X ⊓ Y) Y := by
  have hYX : ¬ Y ≤ X := by
    intro hle
    exact hY.2 X inferInstance (lt_of_le_of_ne hle hne.symm) hX.1
  have hXsup : X < X ⊔ Y := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    exact hYX (he.symm ▸ le_sup_right)
  have hN : X ⊔ Y = N := by
    refine (sup_le hX.1.le hY.1.le).eq_of_not_lt ?_
    exact hX.2 _ inferInstance hXsup
  refine ⟨hN, ?_, inf_covBy_right_of_covBy_sup X Y (hN.symm ▸ hX)⟩
  have hN' : Y ⊔ X = N := (sup_comm Y X).trans hN
  simpa only [inf_comm Y X] using inf_covBy_right_of_covBy_sup Y X (hN'.symm ▸ hY)

/-- Both crossed factor isomorphisms for a diamond, using the same intersection
and the same ambient conjugation action. -/
theorem diamond_factor_equivs (X Y N : Subgroup G) [X.Normal] [Y.Normal] [N.Normal]
    (hX : AmbientCovBy X N) (hY : AmbientCovBy Y N) (hne : X ≠ Y) :
    (∃ e : GEquiv G (Factor (X ⊓ Y) Y) (Factor X N),
      ∀ y : Y, e.1 (factorMk (X ⊓ Y) Y y) =
        factorMk X N (Subgroup.inclusion hY.1.le y)) ∧
    (∃ e : GEquiv G (Factor (X ⊓ Y) X) (Factor Y N),
      ∀ x : X, e.1 (factorMk (X ⊓ Y) X x) =
        factorMk Y N (Subgroup.inclusion hX.1.le x)) := by
  have hN := (ambient_diamond X Y N hX hY hne).1
  exact ⟨equivariant_second_iso X Y _ N rfl hN,
    equivariant_second_iso Y X _ N (inf_comm Y X) ((sup_comm Y X).trans hN)⟩

end ALG02GroupTheory.Chief
