import MathGenome.Internal.LieTheoryDeepening.LieNotes.Contragredient.CartanData
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.Presentation

/-! The presentation, its universal property, and the interchange of the simple generators. -/

namespace LieNotes.Contragredient.Presentation

open Specs.LieNotes.Contragredient.Presentation
  (Generators Free freeCartan freeE freeF Relator relationIdeal quotientMap)
open scoped Classical

noncomputable section

universe u v w

variable {I : Type u} {A : Matrix I I ℤ} {H : Type v} [AddCommGroup H] [Module ℂ H]

private theorem freeCartan_basis (b : Module.Basis.ofVectorSpaceIndex ℂ H) :
    freeCartan (I := I) (Module.Basis.ofVectorSpace ℂ H b) = FreeLieAlgebra.of ℂ (.inl b) :=
  (Module.Basis.ofVectorSpace ℂ H).constr_basis ℂ _ b

section

variable {L : Type w} [LieRing L] [LieAlgebra ℂ L]

private def freeAssignment (C : H →ₗ[ℂ] L) (E F : I → L) : Free I H →ₗ⁅ℂ⁆ L :=
  FreeLieAlgebra.lift ℂ (Sum.elim (C ∘ Module.Basis.ofVectorSpace ℂ H) (Sum.elim E F))

@[simp]
private theorem freeAssignment_cartan (C : H →ₗ[ℂ] L) (E F : I → L) (h : H) :
    freeAssignment C E F (freeCartan h) = C h := by
  have hcomp : (freeAssignment C E F).toLinearMap.comp freeCartan = C := by
    apply (Module.Basis.ofVectorSpace ℂ H).ext
    intro b
    rw [LinearMap.comp_apply, LieHom.coe_toLinearMap, freeCartan_basis]
    exact FreeLieAlgebra.lift_of_apply _ _
  exact LinearMap.congr_fun hcomp h

@[simp]
private theorem freeAssignment_e (C : H →ₗ[ℂ] L) (E F : I → L) (i : I) :
    freeAssignment C E F (freeE i) = E i :=
  FreeLieAlgebra.lift_of_apply _ _

@[simp]
private theorem freeAssignment_f (C : H →ₗ[ℂ] L) (E F : I → L) (i : I) :
    freeAssignment C E F (freeF i) = F i :=
  FreeLieAlgebra.lift_of_apply _ _

end

variable [Finite I]

abbrev Algebra (R : Realization A H) := Specs.LieNotes.Contragredient.Presentation.Algebra R

abbrev cartan (R : Realization A H) : H →ₗ[ℂ] Algebra R :=
  Specs.LieNotes.Contragredient.Presentation.cartan R

abbrev e (R : Realization A H) (i : I) : Algebra R :=
  Specs.LieNotes.Contragredient.Presentation.e R i

abbrev f (R : Realization A H) (i : I) : Algebra R :=
  Specs.LieNotes.Contragredient.Presentation.f R i

abbrev positive (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.Presentation.positive R

abbrev negative (R : Realization A H) : LieSubalgebra ℂ (Algebra R) :=
  Specs.LieNotes.Contragredient.Presentation.negative R

variable {L : Type w} [LieRing L] [LieAlgebra ℂ L]

abbrev Relations (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L) :=
  Specs.LieNotes.Contragredient.Presentation.Relations R C E F

open Specs.LieNotes.Contragredient.Presentation (Extends IsInterchange)

private theorem relator_zero {R : Realization A H} {x : Free I H} (hx : Relator R x) :
    quotientMap R x = 0 :=
  LieSubmodule.Quotient.mk_eq_zero'.2 (LieSubmodule.subset_lieSpan hx)

theorem definingRelations (R : Realization A H) : Relations R (cartan R) (e R) (f R) := by
  constructor
  · intro h k
    exact (LieHom.map_lie (quotientMap R) _ _).symm.trans
      (relator_zero (Relator.cartan_cartan (R := R) h k))
  · intro h i
    apply sub_eq_zero.mp
    simpa only [map_sub, LieHom.map_lie, map_smul] using!
      relator_zero (Relator.cartan_e (R := R) h i)
  · intro h i
    apply eq_neg_of_add_eq_zero_left
    simpa only [map_add, LieHom.map_lie, map_smul] using!
      relator_zero (Relator.cartan_f (R := R) h i)
  · intro i j
    apply sub_eq_zero.mp
    have hz := relator_zero (Relator.e_f (R := R) i j)
    by_cases hij : i = j
    · simpa only [map_sub, LieHom.map_lie, ite_eq_left hij] using! hz
    · simpa only [map_sub, LieHom.map_lie, ite_eq_right hij, map_zero] using! hz

@[simp]
theorem lie_cartan_cartan (R : Realization A H) (h k : H) :
    ⁅cartan R h, cartan R k⁆ = 0 :=
  (definingRelations R).cartan_cartan h k

theorem lie_cartan_e (R : Realization A H) (h : H) (i : I) :
    ⁅cartan R h, e R i⁆ = R.α i h • e R i :=
  (definingRelations R).cartan_e h i

theorem lie_cartan_f (R : Realization A H) (h : H) (i : I) :
    ⁅cartan R h, f R i⁆ = -(R.α i h • f R i) :=
  (definingRelations R).cartan_f h i

theorem lie_e_f (R : Realization A H) (i j : I) :
    ⁅e R i, f R j⁆ = if i = j then cartan R (R.h i) else 0 :=
  (definingRelations R).e_f i j

private theorem quotientMap_surjective (R : Realization A H) :
    Function.Surjective (quotientMap R) :=
  Quot.mk_surjective

private theorem relationIdeal_le_ker (R : Realization A H) {C : H →ₗ[ℂ] L} {E F : I → L}
    (hR : Relations R C E F) : relationIdeal R ≤ (freeAssignment C E F).ker := by
  apply LieSubmodule.lieSpan_le.mpr
  intro x (hx : Relator R x)
  change freeAssignment C E F x = 0
  cases hx with
  | cartan_cartan h k => simpa only [LieHom.map_lie, freeAssignment_cartan] using hR.cartan_cartan h k
  | cartan_e h i =>
      simp only [map_sub, LieHom.map_lie, map_smul, freeAssignment_cartan, freeAssignment_e,
        hR.cartan_e, sub_self]
  | cartan_f h i =>
      simp only [map_add, LieHom.map_lie, map_smul, freeAssignment_cartan, freeAssignment_f,
        hR.cartan_f, neg_add_cancel]
  | e_f i j =>
      by_cases hij : i = j
      · simp only [map_sub, LieHom.map_lie, freeAssignment_e, freeAssignment_f, hR.e_f,
          ite_eq_left hij, freeAssignment_cartan, sub_self]
      · simp only [map_sub, LieHom.map_lie, freeAssignment_e, freeAssignment_f, hR.e_f,
          ite_eq_right hij, map_zero, sub_self]

/-- Descend a relation-preserving assignment from the free Lie algebra to the presentation. -/
def lift (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L) (hR : Relations R C E F) :
    Algebra R →ₗ⁅ℂ⁆ L :=
  { (relationIdeal R).toSubmodule.liftQ (freeAssignment C E F).toLinearMap
      (relationIdeal_le_ker R hR) with
    map_lie' := by
      intro x y
      obtain ⟨x, rfl⟩ := quotientMap_surjective R x
      obtain ⟨y, rfl⟩ := quotientMap_surjective R y
      exact (freeAssignment C E F).map_lie x y }

@[simp]
theorem lift_cartan (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L)
    (hR : Relations R C E F) (h : H) : lift R C E F hR (cartan R h) = C h :=
  freeAssignment_cartan C E F h

@[simp]
theorem lift_e (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L)
    (hR : Relations R C E F) (i : I) : lift R C E F hR (e R i) = E i :=
  freeAssignment_e C E F i

@[simp]
theorem lift_f (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L)
    (hR : Relations R C E F) (i : I) : lift R C E F hR (f R i) = F i :=
  freeAssignment_f C E F i

theorem hom_ext {R : Realization A H} {φ ψ : Algebra R →ₗ⁅ℂ⁆ L}
    (hc : ∀ h, φ (cartan R h) = ψ (cartan R h))
    (he : ∀ i, φ (e R i) = ψ (e R i))
    (hf : ∀ i, φ (f R i) = ψ (f R i)) : φ = ψ := by
  have hcomp : φ.comp (quotientMap R) = ψ.comp (quotientMap R) := by
    apply FreeLieAlgebra.hom_ext
    rintro (b | i | i)
    · rw [LieHom.comp_apply, LieHom.comp_apply, ← freeCartan_basis]
      exact hc (Module.Basis.ofVectorSpace ℂ H b)
    · exact he i
    · exact hf i
  apply LieHom.ext
  intro x
  obtain ⟨y, rfl⟩ := quotientMap_surjective R x
  exact LieHom.congr_fun hcomp y

theorem universalProperty (R : Realization A H) (C : H →ₗ[ℂ] L) (E F : I → L)
    (hR : Relations R C E F) : ∃! φ, Extends R C E F φ := by
  refine ⟨lift R C E F hR, ⟨lift_cartan R C E F hR, lift_e R C E F hR, lift_f R C E F hR⟩, ?_⟩
  rintro φ ⟨hc, he, hf⟩
  apply hom_ext <;> intro x <;> simp only [lift_cartan, lift_e, lift_f, hc, he, hf]

open LieSubalgebra in
theorem generated (R : Realization A H) :
    lieSpan ℂ (Algebra R) (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R)) = ⊤ := by
  let S := lieSpan ℂ (Algebra R) (Set.range (cartan R) ∪ Set.range (e R) ∪ Set.range (f R))
  have hgen (g : Generators I H) : quotientMap R (FreeLieAlgebra.of ℂ g) ∈ S := by
    rcases g with b | i | i
    · rw [← freeCartan_basis]
      exact subset_lieSpan (Or.inl (Or.inl (Set.mem_range_self _)))
    · exact subset_lieSpan (Or.inl (Or.inr (Set.mem_range_self i)))
    · exact subset_lieSpan (Or.inr (Set.mem_range_self i))
  let intoSpan : Free I H →ₗ⁅ℂ⁆ S :=
    FreeLieAlgebra.lift ℂ (fun g => ⟨_, hgen g⟩)
  have hcomp : S.incl.comp intoSpan = quotientMap R := by
    apply FreeLieAlgebra.hom_ext
    intro g
    exact congrArg Subtype.val (FreeLieAlgebra.lift_of_apply _ g)
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := quotientMap_surjective R x
  rw [← LieHom.congr_fun hcomp y]
  exact (intoSpan y).property

private theorem interchange_relations (R : Realization A H) :
    Relations R (-cartan R) (f R) (e R) := by
  constructor
  · intro h k
    simp
  · intro h i
    simp only [LinearMap.neg_apply, neg_lie, lie_cartan_f, neg_neg]
  · intro h i
    simp only [LinearMap.neg_apply, neg_lie, lie_cartan_e]
  · intro i j
    rw [← lie_skew (x := f R i) (y := e R j), lie_e_f]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Ne.symm hij]

private def interchangeHom (R : Realization A H) : Algebra R →ₗ⁅ℂ⁆ Algebra R :=
  lift R (-cartan R) (f R) (e R) (interchange_relations R)

@[simp]
private theorem interchangeHom_cartan (R : Realization A H) (h : H) :
    interchangeHom R (cartan R h) = -cartan R h := by
  simp [interchangeHom]

@[simp]
private theorem interchangeHom_e (R : Realization A H) (i : I) :
    interchangeHom R (e R i) = f R i :=
  lift_e R _ _ _ _ i

@[simp]
private theorem interchangeHom_f (R : Realization A H) (i : I) :
    interchangeHom R (f R i) = e R i :=
  lift_f R _ _ _ _ i

private theorem interchangeHom_involutive (R : Realization A H) :
    Function.Involutive (interchangeHom R) := by
  have h : (interchangeHom R).comp (interchangeHom R) = LieHom.id := by
    apply hom_ext <;> intro x <;> simp
  exact LieHom.congr_fun h

/-- The Lie algebra involution that exchanges the two families of simple generators. -/
def involution (R : Realization A H) : Algebra R ≃ₗ⁅ℂ⁆ Algebra R :=
  LieEquiv.ofBijective (interchangeHom R)
    ⟨(interchangeHom_involutive R).injective, (interchangeHom_involutive R).surjective⟩

@[simp]
theorem involution_cartan (R : Realization A H) (h : H) :
    involution R (cartan R h) = -cartan R h :=
  interchangeHom_cartan R h

@[simp]
theorem involution_e (R : Realization A H) (i : I) :
    involution R (e R i) = f R i :=
  interchangeHom_e R i

@[simp]
theorem involution_f (R : Realization A H) (i : I) :
    involution R (f R i) = e R i :=
  interchangeHom_f R i

theorem involution_involutive (R : Realization A H) : Function.Involutive (involution R) :=
  interchangeHom_involutive R

theorem hasInterchange (R : Realization A H) : ∃ σ, IsInterchange R σ :=
  ⟨involution R, involution_involutive R, involution_cartan R, involution_e R, involution_f R⟩

end

end LieNotes.Contragredient.Presentation
