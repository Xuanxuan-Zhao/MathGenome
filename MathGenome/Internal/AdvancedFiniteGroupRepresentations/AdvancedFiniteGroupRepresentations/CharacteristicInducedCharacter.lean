import MathGenome.Internal.AdvancedFiniteGroupRepresentations.AdvancedFiniteGroupRepresentations.CharacteristicMultiplication
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicInducedCharacter
import MathGenome.Internal.AlgebraCore.P103.Ch09.InducedCharacter

noncomputable section
open scoped TensorProduct BigOperators MonoidAlgebra
open Classical Representation
namespace AdvancedFiniteGroupRepresentations

abbrev externalTensorRepresentation :=
  @Specs.AdvancedFiniteGroupRepresentations.externalTensorRepresentation

section InductionAlongEmbedding

variable {H G U : Type*} [Group H] [Group G]
  [AddCommGroup U] [Module ℂ U]
  (φ : H →* G) (hφ : Function.Injective φ) (π : Representation ℂ H U)

private def rangeRepresentation : Representation ℂ φ.range U :=
  π.comp (MonoidHom.ofInjective hφ).symm.toMonoidHom

/-- Transporting the diagonal action along the isomorphism onto the range leaves
its coinvariant relations unchanged. -/
private theorem embedding_coinvariantRelations :
    Coinvariants.ker (tprod ((leftRegular ℂ G).comp φ) π) =
      Coinvariants.ker (tprod ((leftRegular ℂ G).comp φ.range.subtype)
        (rangeRepresentation φ hφ π)) := by
  let e := MonoidHom.ofInjective hφ
  have action (h : H) :
      (tprod ((leftRegular ℂ G).comp φ.range.subtype)
        (rangeRepresentation φ hφ π)) (e h) =
      (tprod ((leftRegular ℂ G).comp φ) π) h := by
    simp only [tprod_apply, MonoidHom.comp_apply, rangeRepresentation,
      MulEquiv.coe_toMonoidHom]
    change TensorProduct.map (leftRegular ℂ G (φ h)) (π (e.symm (e h))) = _
    rw [e.symm_apply_apply]
  unfold Coinvariants.ker
  congr 1
  ext z
  constructor
  · rintro ⟨⟨h, u⟩, rfl⟩
    exact ⟨(e h, u), by simp only [action]⟩
  · rintro ⟨⟨j, u⟩, rfl⟩
    obtain ⟨h, rfl⟩ := e.surjective j
    exact ⟨(h, u), by simp only [action]⟩

private def embeddingCoinvariantsEquiv :
    IndV φ π ≃ₗ[ℂ] IndV φ.range.subtype (rangeRepresentation φ hφ π) :=
  Submodule.quotEquivOfEq _ _ (embedding_coinvariantRelations φ hφ π)

private theorem embeddingCoinvariantsEquiv_mk (x : G) (u : U) :
    embeddingCoinvariantsEquiv φ hφ π (IndV.mk φ π x u) =
      IndV.mk φ.range.subtype (rangeRepresentation φ hφ π) x u := rfl

private theorem embeddingCoinvariantsEquiv_intertwines (σ : G) (z : IndV φ π) :
    embeddingCoinvariantsEquiv φ hφ π (ind φ π σ z) =
      ind φ.range.subtype (rangeRepresentation φ hφ π) σ
        (embeddingCoinvariantsEquiv φ hφ π z) := by
  let e := (embeddingCoinvariantsEquiv φ hφ π).toLinearMap
  have he : e ∘ₗ ind φ π σ =
      ind φ.range.subtype (rangeRepresentation φ hφ π) σ ∘ₗ e := by
    apply IndV.hom_ext
    intro x
    ext u
    change embeddingCoinvariantsEquiv φ hφ π (ind φ π σ (IndV.mk φ π x u)) =
      ind φ.range.subtype (rangeRepresentation φ hφ π) σ
        (embeddingCoinvariantsEquiv φ hφ π (IndV.mk φ π x u))
    rw [ind_mk, embeddingCoinvariantsEquiv_mk, embeddingCoinvariantsEquiv_mk, ind_mk]
  exact LinearMap.congr_fun he z

open P103.Ch09 in
private theorem embeddingInduced_character_range [Fintype G] [FiniteDimensional ℂ U] (σ : G) :
    (ind φ π).character σ =
      InducedCharacterSpecs.inductionValue φ.range
        (P103.Ch08.CharacterSpecs.characterValue (rangeRepresentation φ hφ π)) σ := by
  let π' := rangeRepresentation φ hφ π
  let _ := inducedScalarModule φ.range π'
  let e := (TensorBridge.mathlibEquiv φ.range π').trans
    (embeddingCoinvariantsEquiv φ hφ π).symm
  have he (z : Induced φ.range π') :
      e (induction φ.range π' σ z) = ind φ π σ (e z) := by
    apply (embeddingCoinvariantsEquiv φ hφ π).injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      embeddingCoinvariantsEquiv_intertwines, TensorBridge.mathlibEquiv_equivariant, π']
  have hconj : e.conj (induction φ.range π' σ) = ind φ π σ := by
    apply LinearMap.ext
    intro z
    change e (induction φ.range π' σ (e.symm z)) = ind φ π σ z
    rw [he, e.apply_symm_apply]
  calc
    (ind φ π).character σ = LinearMap.trace ℂ _ (e.conj (induction φ.range π' σ)) := by
      rw [hconj]
      rfl
    _ = LinearMap.trace ℂ _ (induction φ.range π' σ) := LinearMap.trace_conj' _ _
    _ = _ := (induced_character φ.range π' (inductionData φ.range π')
      (functionModelData φ.range π')).2.1 σ

include hφ in
private theorem embeddingInduced_character [Fintype G] [Fintype H]
    [FiniteDimensional ℂ U] (σ : G) :
    (ind φ π).character σ = (Fintype.card H : ℂ)⁻¹ *
      ∑ x : G, ∑ h : H, if x * φ h * x⁻¹ = σ then π.character h else 0 := by
  classical
  rw [embeddingInduced_character_range φ hφ π]
  have hcard : Nat.card φ.range = Fintype.card H :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).symm.toEquiv).trans Nat.card_eq_fintype_card
  change (Nat.card φ.range : ℂ)⁻¹ * _ = _
  rw [hcard]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hconj (h : H) : x * φ h * x⁻¹ = σ ↔ φ h = x⁻¹ * σ * x := by
    constructor <;> intro hh
    · rw [← hh]
      group
    · rw [hh]
      group
  split_ifs with hx
  · let j : φ.range := ⟨x⁻¹ * σ * x, hx⟩
    let h := (MonoidHom.ofInjective hφ).symm j
    have hj : φ h = x⁻¹ * σ * x := MonoidHom.apply_ofInjective_symm hφ j
    rw [Finset.sum_eq_single h]
    · rw [ite_eq_left ((hconj h).2 hj)]
      rfl
    · intro t _ ht
      rw [ite_eq_right (fun he => ht (hφ ((hconj t).1 he |>.trans hj.symm)))]
    · simp
  · symm
    apply Finset.sum_eq_zero
    intro h _
    rw [ite_eq_right]
    intro hh
    exact hx ⟨h, (hconj h).1 hh⟩

end InductionAlongEmbedding

section BlockInduction

variable {a b : ℕ} {V : Type*} {W : Type*}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ (SymmetricGroup a) V)
  (τ : Representation ℂ (SymmetricGroup b) W)

/-- The actual induced carrier is a quotient of a finite-dimensional tensor product. -/
theorem blockInduced_finiteDimensional :
    FiniteDimensional ℂ (IndV (blockEmbedding a b) (externalTensorRepresentation ρ τ)) := by
  infer_instance

/-- The trace of the block-induced external tensor, at each permutation. -/
theorem blockInduced_character_apply (σ : SymmetricGroup (a + b)) :
    (ind (blockEmbedding a b) (externalTensorRepresentation ρ τ)).character σ =
      (Fintype.card (SymmetricGroup a × SymmetricGroup b) : ℂ)⁻¹ *
        ∑ x : SymmetricGroup (a + b), ∑ h : SymmetricGroup a × SymmetricGroup b,
          if x * blockEmbedding a b h * x⁻¹ = σ then
            ρ.character h.1 * τ.character h.2 else 0 := by
  rw [embeddingInduced_character _ (blockEmbedding_injective a b)]
  have ht (h : SymmetricGroup a × SymmetricGroup b) :
      (externalTensorRepresentation ρ τ).character h =
        ρ.character h.1 * τ.character h.2 := by
    change LinearMap.trace ℂ (V ⊗[ℂ] W) (TensorProduct.map (ρ h.1) (τ h.2)) = _
    exact LinearMap.trace_tensorProduct' (ρ h.1) (τ h.2)
  simp only [ht]

/-- The class function of Mathlib induction is the FR-C05 induction of characters. -/
theorem blockInduced_character :
    representationClassFunction (ind (blockEmbedding a b) (externalTensorRepresentation ρ τ)) =
      inducedExternal (representationClassFunction ρ) (representationClassFunction τ) := by
  funext c
  induction c using Quotient.inductionOn with
  | _ σ =>
    change (ind (blockEmbedding a b) (externalTensorRepresentation ρ τ)).character σ =
      ordinaryInduction (blockEmbedding a b) (fun h => ρ.character h.1 * τ.character h.2)
        (ConjClasses.mk σ)
    rw [ordinaryInduction_mk, blockInduced_character_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro h _
    split_ifs <;> rfl

end BlockInduction

end AdvancedFiniteGroupRepresentations
