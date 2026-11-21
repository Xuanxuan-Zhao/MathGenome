import MathGenome.Internal.Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure
import MathGenome.Internal.D07.Ch01.DihedralQuaternionModels
import MathGenome.Internal.D07.Ch18.NilpotenceClosure

/-! Computations for the octagon and its product with a cyclic group of order 2.
Finite checks below concern only explicit elements and operations; subgroup
closure and the two central series are handled by their defining theorems. -/
namespace D07.Ch18.NilpotenceExamplesReverseInterlacingFailure

open Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure
open Specs.D07.Ch18.CentralSeries Specs.D07.Ch18.NilpotenceCriteria
open D07.Ch18.NilpotenceCriteria
open DihedralGroup
open scoped commutatorElement

/-- The four even rotations of the octagon. -/
def evenRotations : Subgroup (DihedralGroup 8) where
  carrier := {x | x = r 0 ∨ x = r 2 ∨ x = r 4 ∨ x = r 6}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

/-- The identity and the half turn. -/
def halfTurns : Subgroup (DihedralGroup 8) where
  carrier := {x | x = r 0 ∨ x = r 4}
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

instance : DecidablePred (· ∈ evenRotations) := fun x =>
  inferInstanceAs (Decidable (x = r 0 ∨ x = r 2 ∨ x = r 4 ∨ x = r 6))

instance : DecidablePred (· ∈ halfTurns) := fun x =>
  inferInstanceAs (Decidable (x = r 0 ∨ x = r 4))

lemma evenRotations_eq_zpowers : evenRotations = Subgroup.zpowers (r 2) := by
  apply le_antisymm
  · intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (r 2)) 2
    · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (r 2)) 3
  · exact Subgroup.zpowers_le.mpr (by decide)

lemma halfTurns_eq_zpowers : halfTurns = Subgroup.zpowers (r 4) := by
  apply le_antisymm
  · intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (by decide)

lemma commutator_top : ⁅(⊤ : Subgroup (DihedralGroup 8)), ⊤⁆ = evenRotations := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x _ y _
    exact (by decide : ∀ x y : DihedralGroup 8, ⁅x, y⁆ ∈ evenRotations) x y
  · rw [evenRotations_eq_zpowers]
    apply Subgroup.zpowers_le.mpr
    have h := Subgroup.commutator_mem_commutator
      (Subgroup.mem_top (r (1 : ZMod 8))) (Subgroup.mem_top (sr (0 : ZMod 8)))
    convert h using 1; decide

lemma commutator_even : ⁅evenRotations, (⊤ : Subgroup (DihedralGroup 8))⁆ = halfTurns := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro x hx y _
    exact (by decide : ∀ x : DihedralGroup 8, x ∈ evenRotations →
      ∀ y : DihedralGroup 8, ⁅x, y⁆ ∈ halfTurns) x hx y
  · rw [halfTurns_eq_zpowers]
    apply Subgroup.zpowers_le.mpr
    have h := Subgroup.commutator_mem_commutator
      (show r (2 : ZMod 8) ∈ evenRotations by decide) (Subgroup.mem_top (sr (0 : ZMod 8)))
    convert h using 1; decide

lemma commutator_half : ⁅halfTurns, (⊤ : Subgroup (DihedralGroup 8))⁆ = ⊥ := by
  apply eq_bot_iff.mpr
  apply Subgroup.commutator_le.mpr
  intro x hx y _
  exact (by decide : ∀ x : DihedralGroup 8, x ∈ halfTurns →
    ∀ y : DihedralGroup 8, ⁅x, y⁆ = 1) x hx y

lemma dihedral_lower_two : lowerValue (DihedralGroup 8) 2 = Subgroup.zpowers (r 2) := by
  change ⁅(⊤ : Subgroup (DihedralGroup 8)), ⊤⁆ = _
  rw [commutator_top, evenRotations_eq_zpowers]

lemma dihedral_lower_three : lowerValue (DihedralGroup 8) 3 = Subgroup.zpowers (r 4) := by
  change ⁅⁅(⊤ : Subgroup (DihedralGroup 8)), ⊤⁆, ⊤⁆ = _
  rw [commutator_top, commutator_even, halfTurns_eq_zpowers]

lemma dihedral_lower_four : lowerValue (DihedralGroup 8) 4 = ⊥ := by
  change ⁅⁅⁅(⊤ : Subgroup (DihedralGroup 8)), ⊤⁆, ⊤⁆, ⊤⁆ = ⊥
  rw [commutator_top, commutator_even, commutator_half]

lemma dihedral_hasClass : hasClassValue (DihedralGroup 8) 3 := by
  refine ⟨(classAtMost_iff_lower _ 3).mpr dihedral_lower_four, fun d hd => ?_⟩
  by_contra h
  have hd2 : d ≤ 2 := by omega
  have hle : lowerValue (DihedralGroup 8) 3 ≤ lowerValue (DihedralGroup 8) (d + 1) :=
    CentralSeries.lower_antitone (DihedralGroup 8) hd2
  have hmem : r (4 : ZMod 8) ∈ lowerValue (DihedralGroup 8) 3 := by
    rw [dihedral_lower_three]
    exact Subgroup.mem_zpowers _
  have hbot := (classAtMost_iff_lower _ d).mp hd
  have heq : r (4 : ZMod 8) = 1 := by
    have := hle hmem
    simpa [hbot] using this
  exact (by decide : r (4 : ZMod 8) ≠ 1) heq

universe u v

/-- The source-indexed lower central series respects group isomorphisms. -/
lemma map_lower_value {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (n : ℕ) :
    (lowerValue A (n + 1)).map e.toMonoidHom = lowerValue B (n + 1) := by
  rw [NilpotenceClosure.lower_value_indexing, NilpotenceClosure.lower_value_indexing,
    Subgroup.map_lowerCentralSeries, Subgroup.map_top_of_surjective _ e.surjective]

lemma equiv_hasClass {A : Type u} {B : Type v} [Group A] [Group B]
    (e : A ≃* B) (c : ℕ) (hc : hasClassValue A c) : hasClassValue B c := by
  refine ⟨NilpotenceClosure.surjective_classAtMost A B e.toMonoidHom e.surjective c hc.1,
    fun d hd => hc.2 d ?_⟩
  exact NilpotenceClosure.surjective_classAtMost B A e.symm.toMonoidHom e.symm.surjective d hd

lemma cyclic_two_hasClass : hasClassValue C₂ 1 := by
  apply (class_one_iff_nontrivial_abelian C₂).mpr
  exact ⟨inferInstance, mul_comm⟩

/-- The extra cyclic factor is central in the product, for every group A. -/
lemma extra_factor_central (A : Type u) [Group A] :
    (⊥ : Subgroup A).prod (⊤ : Subgroup C₂) ≤ upperValue (A × C₂) 1 := by
  intro x hx
  rw [Subgroup.mem_prod] at hx
  have hx1 : x.1 = 1 := hx.1
  change x ∈ Subgroup.upperCentralSeries (A × C₂) 1
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro y
  apply Prod.ext
  · simp [hx1]
  · exact mul_comm _ _

lemma product_lower_two (A : Type u) [Group A] :
    lowerValue (A × C₂) 2 = (lowerValue A 2).prod (⊥ : Subgroup C₂) := by
  have hC : lowerValue C₂ 2 = ⊥ := (classAtMost_iff_lower C₂ 1).mp cyclic_two_hasClass.1
  rw [NilpotenceClosure.lower_value_indexing, Subgroup.top_lowerCentralSeries_prod]
  rw [← NilpotenceClosure.lower_value_indexing A 1,
    ← NilpotenceClosure.lower_value_indexing C₂ 1, hC]

lemma reverse_interlacing_fails (A : Type u) [Group A] :
    ¬ upperValue (A × C₂) 1 ≤ lowerValue (A × C₂) 2 := by
  intro h
  have hw : (1, Multiplicative.ofAdd (1 : ZMod 2)) ∈
      (⊥ : Subgroup A).prod (⊤ : Subgroup C₂) := ⟨rfl, Subgroup.mem_top _⟩
  have hmem := h (extra_factor_central A hw)
  rw [product_lower_two] at hmem
  have heq : Multiplicative.ofAdd (1 : ZMod 2) = (1 : C₂) := hmem.2
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : C₂)) heq

/-- The full geometric octagon, including arbitrary center, scale and direction. -/
theorem geometric_counterexample :
    Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure.GeometricCounterexample := by
  intro c a ha
  obtain ⟨hfinite, hcard, e, hr, hs, hrn, hs2, hsrs, _, _, _⟩ :=
    D07.Ch01.DihedralQuaternionModels.dihedral_models 8 c a (by decide) ha
  refine ⟨hfinite, hcard, e, hr, hs, hrn, hs2, hsrs, ?_, ?_, ?_, ?_, ?_,
    extra_factor_central _, ?_, reverse_interlacing_fails _⟩
  · have h := map_lower_value e 1
    rw [dihedral_lower_two, MonoidHom.map_zpowers] at h
    rw [← map_pow, show (r (1 : ZMod 8)) ^ 2 = r 2 by decide]
    exact h.symm
  · have h := map_lower_value e 2
    rw [dihedral_lower_three, MonoidHom.map_zpowers] at h
    rw [← map_pow, show (r (1 : ZMod 8)) ^ 4 = r 4 by decide]
    exact h.symm
  · have h := map_lower_value e 3
    rw [dihedral_lower_four, Subgroup.map_bot] at h
    exact h.symm
  · exact equiv_hasClass e 3 dihedral_hasClass
  · exact NilpotenceClosure.prod_hasClass _ C₂ 3 1
      (equiv_hasClass e 3 dihedral_hasClass) cyclic_two_hasClass
  · rw [product_lower_two]
    have h := map_lower_value e 1
    rw [dihedral_lower_two, MonoidHom.map_zpowers] at h
    congr 1
    rw [← map_pow, show (r (1 : ZMod 8)) ^ 2 = r 2 by decide]
    exact h.symm

end D07.Ch18.NilpotenceExamplesReverseInterlacingFailure
