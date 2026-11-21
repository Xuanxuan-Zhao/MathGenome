import MathGenome.Internal.Specs.D07.Ch14.BaseChange

/-!
Galois base change, K07.14.base_change (paper.tex:4230–4243).

A separable splitting polynomial for E/K also generates the compositum
as a splitting field over F. This proves finite degree and Galoisness
without requiring F/K to be algebraic. Restriction is injective by
compositum generation. Its image has fixed field precisely E ∩ F,
so the finite Galois correspondence identifies that image with the
pointwise fixing subgroup of E ∩ F. The final equivalence retains the
restriction map on elements. Automorphism counts give the relative
degree identity, and the two tower laws give the product formula.

The fixed-field argument also appears in J. S. Milne, Fields and Galois
Theory, v5.10, Proposition 3.19 and Corollary 3.20 (printed pp. 40–41).
-/

universe u v
namespace D07.Ch14.BaseChange
open IntermediateField Polynomial Module

/-- The splitting-field proof also records finite degree after changing the base. -/
theorem finiteGalois_of_sup_eq_top {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (E F : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E]
    (h : E ⊔ F = ⊤) : FiniteDimensional F Ω ∧ IsGalois F Ω := by
  obtain ⟨p, hp, hsplit⟩ := IsGalois.is_separable_splitting_field K E
  let q := p.map (algebraMap K F)
  have hq : q.IsSplittingField F Ω := by
    rw [isSplittingField_iff_intermediateField] at hsplit ⊢
    constructor
    · rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
      exact Polynomial.Splits.of_algHom hsplit.1 (IsScalarTower.toAlgHom K E Ω)
    · have hroots : q.rootSet Ω = p.rootSet Ω := by simp [q]
      rw [← lift_inj, lift_adjoin, ← coe_val, hsplit.1.image_rootSet] at hsplit
      rw [← restrictScalars_eq_top_iff (K := K), restrictScalars_adjoin, adjoin_union,
        adjoin_self, hroots, hsplit.2, lift_top, sup_comm, h]
  let := hq
  exact ⟨Polynomial.IsSplittingField.finiteDimensional Ω q,
    IsGalois.of_separable_splitting_field (p := q) (hp.map (f := algebraMap K F))⟩

theorem finite_galois_base_change :
    Specs.D07.Ch14.BaseChange.FiniteGaloisBaseChange.{u, v} := by
  intro K Ω _ _ _ E F _ _
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  let E' := restrict (le_sup_left : E ≤ E ⊔ F)
  let F' := restrict (le_sup_right : F ≤ E ⊔ F)
  let e := restrictAlgEquiv (le_sup_left : E ≤ E ⊔ F)
  let f := restrictAlgEquiv (le_sup_right : F ≤ E ⊔ F)
  let : FiniteDimensional K E' := e.toLinearEquiv.finiteDimensional
  let : IsGalois K E' := IsGalois.of_algEquiv e
  have hsup : E' ⊔ F' = ⊤ := by
    apply lift_injective (E ⊔ F)
    simp [E', F', lift_sup, lift_top]
  obtain ⟨hfd, hgal⟩ := finiteGalois_of_sup_eq_top E' F' hsup
  let := hfd
  let := hgal
  have hcomp : (algebraMap F' ↥(E ⊔ F)).comp f.toRingEquiv.toRingHom =
      (RingEquiv.refl ↥(E ⊔ F)).toRingHom.comp (algebraMap F ↥(E ⊔ F)) := by
    ext x
    rfl
  have hd := Algebra.finrank_eq_of_equiv_equiv f.toRingEquiv
    (RingEquiv.refl ↥(E ⊔ F)) hcomp
  refine ⟨FiniteDimensional.of_finrank_pos ?_, ?_⟩
  · rw [hd]
    exact Module.finrank_pos
  · exact IsGalois.of_equiv_equiv (f := f.symm.toRingEquiv)
      (g := RingEquiv.refl ↥(E ⊔ F)) (by
        apply RingHom.ext
        intro x
        obtain ⟨y, rfl⟩ := f.surjective x
        change algebraMap F ↥(E ⊔ F) (f.symm (f y)) = algebraMap F' ↥(E ⊔ F) (f y)
        rw [f.symm_apply_apply]
        rfl)

section Restriction
variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
variable (E F : IntermediateField K Ω)

local instance compositumLeft : Algebra E ↥(E ⊔ F) := (inclusion le_sup_left).toAlgebra
local instance compositumRight : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
local instance intersectionLeft : Algebra ↥(E ⊓ F) E := (inclusion inf_le_left).toAlgebra
local instance towerLeft : IsScalarTower K E ↥(E ⊔ F) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance towerRight : IsScalarTower K F ↥(E ⊔ F) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)
local instance towerIntersection : IsScalarTower K ↥(E ⊓ F) E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The two factors generate the compositum. -/
theorem compositum_aut_eq_one (σ : ↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F))
    (hE : ∀ x : E, σ (algebraMap E ↥(E ⊔ F) x) = algebraMap E ↥(E ⊔ F) x) :
    σ = 1 := by
  let E' := restrict (le_sup_left : E ≤ E ⊔ F)
  let F' := restrict (le_sup_right : F ≤ E ⊔ F)
  have hs : E' ⊔ F' = ⊤ := by
    apply lift_injective (E ⊔ F)
    simp [E', F', lift_sup, lift_top]
  have hmem : σ.restrictScalars K ∈ (⊤ : IntermediateField K ↥(E ⊔ F)).fixingSubgroup := by
    rw [← hs, fixingSubgroup_sup]
    constructor
    · change σ.restrictScalars K ∈ E'.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro x ⟨y, rfl⟩
      exact hE y
    · change σ.restrictScalars K ∈ F'.fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      rintro x ⟨y, rfl⟩
      exact σ.commutes y
  rw [fixingSubgroup_top, Subgroup.mem_bot] at hmem
  exact AlgEquiv.ext fun x => congrArg (fun τ : ↥(E ⊔ F) ≃ₐ[K] ↥(E ⊔ F) => τ x) hmem

variable [Normal K E]
local notation "R" => (restrictRestrictAlgEquivMapHom K E F (E ⊔ F : IntermediateField K Ω))

/-- Restriction commutes with the given embeddings into the compositum. -/
theorem restriction_commutes (σ : ↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F)) (x : E) :
    algebraMap E ↥(E ⊔ F) (R σ x) = σ (algebraMap E ↥(E ⊔ F) x) :=
  AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) E x

theorem restriction_injective : Function.Injective R := by
  apply (injective_iff_map_eq_one R).mpr
  intro σ hσ
  apply compositum_aut_eq_one E F σ
  intro x
  rw [← restriction_commutes E F σ x, hσ]
  rfl

/-- Restrict a compositum automorphism, recording that it fixes the intersection. -/
noncomputable def restrictionHom :
    (↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F)) →* (E ≃ₐ[↥(E ⊓ F)] E) where
  toFun σ :=
    { (R σ).toRingEquiv with
      commutes' := fun x => by
        apply (algebraMap E ↥(E ⊔ F)).injective
        change algebraMap E ↥(E ⊔ F) (R σ (algebraMap ↥(E ⊓ F) E x)) = _
        rw [restriction_commutes E F σ (algebraMap ↥(E ⊓ F) E x)]
        have hi : algebraMap E ↥(E ⊔ F) (algebraMap ↥(E ⊓ F) E x) =
            algebraMap F ↥(E ⊔ F) ⟨x.val, x.property.2⟩ := rfl
        rw [hi, σ.commutes] }
  map_one' := by
    apply AlgEquiv.ext
    intro x
    change R 1 x = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    change R (σ * τ) x = R σ (R τ x)
    rw [map_mul]
    rfl

theorem restrictionHom_injective : Function.Injective (restrictionHom E F) := by
  intro σ τ h
  apply restriction_injective E F
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun g : E ≃ₐ[↥(E ⊓ F)] E => g x) h

variable [FiniteDimensional K E] [IsGalois K E]

/-- The fixed field of the restriction image is exactly the intersection. -/
theorem restriction_image_fixedField :
    fixedField (R).range = restrict (inf_le_left : E ⊓ F ≤ E) := by
  obtain ⟨hfd, hgal⟩ := finite_galois_base_change K Ω E F
  let := hfd
  let := hgal
  ext x
  rw [mem_fixedField_iff, mem_restrict]
  constructor
  · intro hx
    have hc : algebraMap E ↥(E ⊔ F) x ∈ Set.range (algebraMap F ↥(E ⊔ F)) := by
      apply (IsGalois.mem_range_algebraMap_iff_fixed _).mpr
      intro σ
      rw [← restriction_commutes E F σ x]
      exact congrArg (algebraMap E ↥(E ⊔ F)) (hx (R σ) ⟨σ, rfl⟩)
    obtain ⟨y, hy⟩ := hc
    exact ⟨x.property, (congrArg Subtype.val hy) ▸ y.property⟩
  · intro hx φ hφ
    obtain ⟨σ, rfl⟩ := hφ
    apply (algebraMap E ↥(E ⊔ F)).injective
    rw [restriction_commutes]
    have heq : algebraMap E ↥(E ⊔ F) x = algebraMap F ↥(E ⊔ F) ⟨x.val, hx.2⟩ := rfl
    rw [heq, σ.commutes]

/-- The finite correspondence turns the fixed-field identity into an image identity. -/
theorem restriction_range :
    (R).range = (restrict (inf_le_left : E ⊓ F ≤ E)).fixingSubgroup := by
  rw [← restriction_image_fixedField E F]
  exact (fixingSubgroup_fixedField (R).range).symm

theorem restrictionHom_surjective : Function.Surjective (restrictionHom E F) := by
  intro τ
  have ht : τ.restrictScalars K ∈ (restrict (inf_le_left : E ⊓ F ≤ E)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    exact τ.commutes y
  rw [← restriction_range E F] at ht
  obtain ⟨σ, hσ⟩ := ht
  refine ⟨σ, ?_⟩
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun g : E ≃ₐ[K] E => g x) hσ

/-- Equality of the relative degrees holds without any finiteness premise on F/K. -/
theorem compositum_relative_degree :
    Module.finrank F ↥(E ⊔ F) = Module.finrank ↥(E ⊓ F) E := by
  obtain ⟨hfd, hgal⟩ := finite_galois_base_change K Ω E F
  let := hfd
  let := hgal
  let : FiniteDimensional ↥(E ⊓ F) E := FiniteDimensional.right K ↥(E ⊓ F) E
  let : IsGalois ↥(E ⊓ F) E := IsGalois.tower_top_of_isGalois K ↥(E ⊓ F) E
  let e := MulEquiv.ofBijective (restrictionHom E F)
    ⟨restrictionHom_injective E F, restrictionHom_surjective E F⟩
  calc
    Module.finrank F ↥(E ⊔ F) = Nat.card (↥(E ⊔ F) ≃ₐ[F] ↥(E ⊔ F)) :=
      (IsGalois.card_aut_eq_finrank F ↥(E ⊔ F)).symm
    _ = Nat.card (E ≃ₐ[↥(E ⊓ F)] E) := Nat.card_congr e.toEquiv
    _ = Module.finrank ↥(E ⊓ F) E := IsGalois.card_aut_eq_finrank ↥(E ⊓ F) E

end Restriction

theorem restriction_isomorphism :
    Specs.D07.Ch14.BaseChange.RestrictionIsomorphism.{u, v} := by
  intro K Ω _ _ _ E F _ _
  let : Algebra E ↥(E ⊔ F) := (inclusion le_sup_left).toAlgebra
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  let : Algebra ↥(E ⊓ F) E := (inclusion inf_le_left).toAlgebra
  let e := MulEquiv.ofBijective (restrictionHom E F)
    ⟨restrictionHom_injective E F, restrictionHom_surjective E F⟩
  refine ⟨e, ?_⟩
  intro σ x
  exact congrArg Subtype.val (restriction_commutes E F σ x)

theorem compositum_degree_formula :
    Specs.D07.Ch14.BaseChange.CompositumDegreeFormula.{u, v} := by
  intro K Ω _ _ _ E F _ _ _
  let : Algebra F ↥(E ⊔ F) := (inclusion le_sup_right).toAlgebra
  let : IsScalarTower K F ↥(E ⊔ F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra ↥(E ⊓ F) E := (inclusion inf_le_left).toAlgebra
  let : IsScalarTower K ↥(E ⊓ F) E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hrel := compositum_relative_degree E F
  calc
    Module.finrank K ↥(E ⊔ F) * Module.finrank K ↥(E ⊓ F) =
        (Module.finrank K F * Module.finrank F ↥(E ⊔ F)) *
          Module.finrank K ↥(E ⊓ F) := by rw [Module.finrank_mul_finrank K F ↥(E ⊔ F)]
    _ = (Module.finrank K ↥(E ⊓ F) * Module.finrank ↥(E ⊓ F) E) *
          Module.finrank K F := by rw [hrel]; ac_rfl
    _ = Module.finrank K E * Module.finrank K F := by
      rw [Module.finrank_mul_finrank K ↥(E ⊓ F) E]

end D07.Ch14.BaseChange
