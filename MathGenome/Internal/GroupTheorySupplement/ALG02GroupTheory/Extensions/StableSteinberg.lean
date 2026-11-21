import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.StableSteinberg

/-!
# The stable Steinberg map and its kernel

This module exposes the stable matrix groups and proves the presentation and
surjectivity properties of the canonical map. Naturals index rows and columns
starting at zero, so index `i` here denotes the classical index `i + 1`.
-/

namespace ALG02GroupTheory.Extensions.StableSteinberg

open scoped commutatorElement

abbrev FiniteGL := Spec.FiniteGL
abbrev blockGL := @Spec.blockGL
abbrev StableGL := Spec.StableGL
noncomputable abbrev ofFinite := @Spec.ofFinite

abbrev Generator := Spec.Generator
abbrev finiteTransvection := @Spec.finiteTransvection
noncomputable abbrev transvection := @Spec.transvection
noncomputable abbrev ElementarySubgroup := Spec.ElementarySubgroup
abbrev Elementary := Spec.Elementary
noncomputable abbrev elementary := @Spec.elementary

abbrev relators := Spec.relators
abbrev Steinberg := Spec.Steinberg
abbrev generator := @Spec.generator
abbrev SatisfiesRelations := @Spec.SatisfiesRelations

variable {R : Type*} [Ring R]

theorem blockGL_apply {n m : ℕ} (h : n ≤ m) (A : FiniteGL R n) (i j : Fin m) :
    (blockGL h A).val i j =
      if hi : (i : ℕ) < n then
        if hj : (j : ℕ) < n then A.val ⟨i, hi⟩ ⟨j, hj⟩ else 0
      else if (j : ℕ) < n then 0 else (1 : Matrix (Fin m) (Fin m) R) i j :=
  Spec.blockMatrix_apply h A.val i j

theorem blockGL_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (blockGL (R := R) h) := by
  intro A B hAB
  apply Units.ext
  ext i j
  have e := congrArg (fun g : FiniteGL R m ↦ g.val (Fin.castLE h i) (Fin.castLE h j)) hAB
  simpa [blockGL_apply, i.is_lt, j.is_lt] using e

theorem ofFinite_injective (n : ℕ) : Function.Injective (ofFinite (R := R) n) :=
  DirectLimit.mk_injective (fun _ _ h ↦ blockGL h) (fun _ _ h ↦ blockGL_injective h) n

@[simp]
theorem ofFinite_blockGL {n m : ℕ} (h : n ≤ m) (A : FiniteGL R n) :
    ofFinite m (blockGL h A) = ofFinite n A :=
  Spec.ofFinite_blockGL h A

theorem exists_ofFinite (A : StableGL R) : ∃ (n : ℕ) (B : FiniteGL R n), A = ofFinite n B :=
  DirectLimit.exists_eq_mk _ A

theorem transvection_eq_ofFinite (g : Generator R) {n : ℕ}
    (hi : g.row < n) (hj : g.col < n) :
    transvection g = ofFinite n (finiteTransvection (⟨g.row, hi⟩ : Fin n) ⟨g.col, hj⟩
      (fun e ↦ g.distinct (congrArg Fin.val e)) g.coeff) :=
  Spec.transvection_eq_ofFinite g hi hj

theorem elementary_satisfiesRelations : SatisfiesRelations (elementary (R := R)) :=
  Spec.elementary_satisfiesRelations

theorem steinberg_satisfiesRelations : SatisfiesRelations (generator (R := R)) := by
  have relator_eq_one {w : FreeGroup (Generator R)} (hw : Spec.IsRelator R w) :
      PresentedGroup.mk (relators R) w = 1 :=
    PresentedGroup.one_of_mem hw
  have mk_of (g : Generator R) : PresentedGroup.mk (relators R) (FreeGroup.of g) =
      generator g := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij r s
    apply eq_of_mul_inv_eq_one
    simpa only [map_mul, map_inv, mk_of] using relator_eq_one (.add hij r s)
  · intro g h hjk hil
    simpa only [map_commutatorElement, mk_of] using relator_eq_one (.disjoint g h hjk hil)
  · intro i j k hij hjk hik r s
    apply eq_of_mul_inv_eq_one
    simpa only [map_mul, map_inv, map_commutatorElement, mk_of] using
      relator_eq_one (.chain hij hjk hik r s)

/-- The reverse chain case in the classical presentation follows from the other relations. -/
theorem SatisfiesRelations.reverse_chain {G : Type*} [Group G] {x : Generator R → G}
    (hx : SatisfiesRelations x) {i j k : ℕ} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (r s : R) :
    ⁅x ⟨i, j, hij, r⟩, x ⟨k, i, hki, s⟩⁆ = x ⟨k, j, hkj, -(s * r)⟩ := by
  have hzero : x ⟨k, j, hkj, 0⟩ = 1 := by
    have hz := hx.1 k j hkj 0 0
    rw [add_zero] at hz
    exact mul_left_cancel (hz.trans (mul_one _).symm)
  have hneg := hx.1 k j hkj (s * r) (-(s * r))
  rw [add_neg_cancel, hzero] at hneg
  rw [← commutatorElement_inv, hx.2.2 k i j hki hij hkj s r]
  exact inv_eq_of_mul_eq_one_right hneg

/-- Extend a family satisfying the Steinberg relations to the presented group. -/
def lift {G : Type*} [Group G] {x : Generator R → G} (hx : SatisfiesRelations x) :
    Steinberg R →* G :=
  PresentedGroup.toGroup (Spec.killsRelators hx)

@[simp]
theorem lift_generator {G : Type*} [Group G] {x : Generator R → G} (hx : SatisfiesRelations x)
    (g : Generator R) : lift hx (generator g) = x g :=
  PresentedGroup.toGroup.of (Spec.killsRelators hx)

theorem hom_ext {G : Type*} [Group G] {φ ψ : Steinberg R →* G}
    (h : ∀ g, φ (generator g) = ψ (generator g)) : φ = ψ :=
  PresentedGroup.ext h

theorem existsUnique_lift {G : Type*} [Group G] (x : Generator R → G) (hx : SatisfiesRelations x) :
    ∃! φ : Steinberg R →* G, ∀ g, φ (generator g) = x g :=
  ⟨lift hx, lift_generator hx, fun _ h ↦ hom_ext fun g ↦ (h g).trans (lift_generator hx g).symm⟩

/-- The canonical map from the stable Steinberg group to the stable elementary group. -/
noncomputable def toElementary : Steinberg R →* Elementary R :=
  lift elementary_satisfiesRelations

@[simp]
theorem toElementary_generator (g : Generator R) :
    toElementary (generator g) = elementary g :=
  lift_generator elementary_satisfiesRelations g

theorem toElementary_surjective : Function.Surjective (toElementary (R := R)) := by
  intro y
  let image := (toElementary (R := R)).range.map (ElementarySubgroup R).subtype
  have h : ElementarySubgroup R ≤ image := by
    change Subgroup.closure (Set.range transvection) ≤ image
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨elementary g, ⟨generator g, toElementary_generator g⟩, rfl⟩
  obtain ⟨z, ⟨x, hx⟩, hz⟩ := h y.property
  exact ⟨x, hx.trans (Subtype.ext hz)⟩

/-- The classical `K₂` subgroup of the stable Steinberg group. -/
noncomputable def K₂ (R : Type*) [Ring R] : Subgroup (Steinberg R) :=
  (toElementary (R := R)).ker

end ALG02GroupTheory.Extensions.StableSteinberg
