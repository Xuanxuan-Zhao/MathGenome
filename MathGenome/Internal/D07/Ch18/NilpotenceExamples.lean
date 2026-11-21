import MathGenome.Internal.Specs.D07.Ch18.NilpotenceExamples
import MathGenome.Internal.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
import MathGenome.Internal.D07.Ch18.NilpotenceExamplesSolvableNonnilpotent
import MathGenome.Internal.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure
import Mathlib.GroupTheory.Index
import Lean.Elab.Tactic.Omega

namespace D07.Ch18.NilpotenceExamples

open Specs.D07.Ch18.NilpotenceExamples
open Specs.D07.Ch01.DihedralQuaternionModelsQuaternionMatrices
open Specs.D07.Ch18.CentralSeries Specs.D07.Ch18.NilpotenceCriteria
open D07.Ch18.NilpotenceCriteria
open scoped commutatorElement

lemma quaternion_center (q : QuaternionGroup 2) :
    q ∈ Subgroup.center (QuaternionGroup 2) ↔ q = .a 0 ∨ q = .a 2 := by
  exact (by decide : ∀ q : QuaternionGroup 2,
    q ∈ Subgroup.center (QuaternionGroup 2) ↔ q = .a 0 ∨ q = .a 2) q

lemma quaternion_commutators_central (q r : QuaternionGroup 2) :
    ⁅q, r⁆ ∈ Subgroup.center (QuaternionGroup 2) := by
  exact (by decide : ∀ q r : QuaternionGroup 2,
    ⁅q, r⁆ ∈ Subgroup.center (QuaternionGroup 2)) q r

lemma quaternion_upper_two : upperValue (QuaternionGroup 2) 2 = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro q
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro r
  rw [Subgroup.upperCentralSeries_one]
  exact quaternion_commutators_central q r

lemma quaternion_center_card : Nat.card (Subgroup.center (QuaternionGroup 2)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

lemma quaternion_hasClass : hasClassValue (QuaternionGroup 2) 2 := by
  refine ⟨quaternion_upper_two, fun d hd => ?_⟩
  by_contra h
  have hd1 : d ≤ 1 := by omega
  have hm : (QuaternionGroup.a 1 : QuaternionGroup 2) ∈ upperValue (QuaternionGroup 2) d :=
    hd ▸ Subgroup.mem_top _
  have hc := Subgroup.upperCentralSeries_mono (QuaternionGroup 2) hd1 hm
  rw [Subgroup.upperCentralSeries_one, quaternion_center] at hc
  exact (by decide : ¬ ((QuaternionGroup.a 1 : QuaternionGroup 2) = .a 0 ∨
    (QuaternionGroup.a 1 : QuaternionGroup 2) = .a 2)) hc

lemma quaternion_noncentral_witness (q : QuaternionGroup 2)
    (h0 : q ≠ .a 0) (h2 : q ≠ .a 2) :
    ∃ r : QuaternionGroup 2, (r = .a 1 ∨ r = .xa 0 ∨ r = .xa 3) ∧ q * r ≠ r * q := by
  exact (by decide : ∀ q : QuaternionGroup 2, q ≠ .a 0 → q ≠ .a 2 →
    ∃ r : QuaternionGroup 2, (r = .a 1 ∨ r = .xa 0 ∨ r = .xa 3) ∧ q * r ≠ r * q) q h0 h2

lemma quotient_center_commutative {G : Type*} [Group G]
    (hc : upperValue G 2 = ⊤) :
    ∀ x y : G ⧸ Subgroup.center G, x * y = y * x := by
  intro x y
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction y using QuotientGroup.induction_on with
    | H y =>
      apply (commutatorElement_eq_one_iff_commute.mp ?_).eq
      change ⁅QuotientGroup.mk' (Subgroup.center G) x,
        QuotientGroup.mk' (Subgroup.center G) y⁆ = 1
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hx : x ∈ upperValue G 2 := hc ▸ Subgroup.mem_top x
      have hxy := Subgroup.mem_upperCentralSeries_succ_iff.mp hx y
      rwa [Subgroup.upperCentralSeries_one] at hxy

theorem quaternion_example : QuaternionExample := by
  obtain ⟨H, hH, hcard, hnoncomm, e, he⟩ :=
    D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.quaternion_matrix_model
  have hcenter (q : QuaternionGroup 2) :
      e q ∈ Subgroup.center H ↔ q ∈ Subgroup.center (QuaternionGroup 2) := by
    constructor
    · intro h
      rw [Subgroup.mem_center_iff] at h ⊢
      intro r
      apply e.injective
      simpa only [map_mul] using h (e r)
    · intro h
      rw [Subgroup.mem_center_iff] at h ⊢
      intro r
      obtain ⟨r, rfl⟩ := e.surjective r
      simpa only [map_mul] using congrArg e (h r)
  have hc : hasClassValue H 2 :=
    NilpotenceExamplesReverseInterlacingFailure.equiv_hasClass e 2 quaternion_hasClass
  refine ⟨H, hH, hcard, e, he, hnoncomm, ?_, ?_, ?_,
    quotient_center_commutative hc.1, hc.1, hc,
    (nilpotent_iff_exists_bound H).mpr ⟨2, hc.1⟩⟩
  · intro g
    obtain ⟨q, rfl⟩ := e.surjective g
    rw [hcenter, quaternion_center, he]
    have h0 : modelMatrix q = E ↔ q = .a 0 := by
      rw [← show modelMatrix (.a (0 : ZMod 4)) = E from rfl]
      exact D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.modelMatrix_injective.eq_iff
    have h2 : modelMatrix q = -E ↔ q = .a 2 := by
      rw [← show modelMatrix (.a (2 : ZMod 4)) = -E from rfl]
      exact D07.Ch01.DihedralQuaternionModelsQuaternionMatrices.modelMatrix_injective.eq_iff
    rw [h0, h2]
  · intro g hg0 hg2
    obtain ⟨q, rfl⟩ := e.surjective g
    have h0 : q ≠ .a 0 := by rintro rfl; exact hg0 (he _)
    have h2 : q ≠ .a 2 := by rintro rfl; exact hg2 (he _)
    obtain ⟨r, hr, hqr⟩ := quaternion_noncentral_witness q h0 h2
    refine ⟨e r, ?_, ?_⟩
    · rw [he]
      rcases hr with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · intro h
      apply hqr
      apply e.injective
      simpa only [map_mul] using h
  · have hZ : Nat.card (Subgroup.center H) = 2 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, quaternion_center_card]
    have : Finite H := Finite.of_equiv (QuaternionGroup 2) e.toEquiv
    rw [← Subgroup.index_eq_card, Subgroup.index_eq_card_div, hcard, hZ]

theorem symmetric_example : SymmetricExample :=
  ⟨NilpotenceExamplesSolvableNonnilpotent.derived_subgroup,
    NilpotenceExamplesSolvableNonnilpotent.first_derived_term,
    NilpotenceExamplesSolvableNonnilpotent.second_derived_term,
    NilpotenceExamplesSolvableNonnilpotent.mixed_commutator,
    NilpotenceExamplesSolvableNonnilpotent.lower_central_terms,
    NilpotenceExamplesSolvableNonnilpotent.solvable,
    NilpotenceExamplesSolvableNonnilpotent.not_nilpotent,
    NilpotenceExamplesSolvableNonnilpotent.no_class_bound⟩

theorem reverse_interlacing_example : ReverseInterlacingExample :=
  NilpotenceExamplesReverseInterlacingFailure.geometric_counterexample

theorem symmetric_calculations : SymmetricCalculations := by
  dsimp only [SymmetricCalculations]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  exact (alternatingGroup.isMulCommutative_of_card_le_three (by simp)).is_comm.comm

theorem octagon_calculations : OctagonCalculations := by
  intro c a _ e
  dsimp only
  have hN : Subgroup.zpowers ((e (DihedralGroup.r 1)) ^ 2) =
      commutator (Specs.D07.Ch18.NilpotenceExamplesReverseInterlacingFailure.Octagon c a) := by
    have h := NilpotenceExamplesReverseInterlacingFailure.map_lower_value e 1
    rw [NilpotenceExamplesReverseInterlacingFailure.dihedral_lower_two,
      MonoidHom.map_zpowers] at h
    rw [← map_pow, show (DihedralGroup.r 1 : DihedralGroup 8) ^ 2 = .r 2 by decide]
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_commutatorElement, ← map_pow]
    congr 1
  · rw [← map_pow, ← map_commutatorElement, ← map_pow]
    congr 1
  · rw [← map_pow, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact (by decide : ∀ g : DihedralGroup 8,
      g * DihedralGroup.r 1 ^ 4 = DihedralGroup.r 1 ^ 4 * g) g
  · intro g
    obtain ⟨g, rfl⟩ := e.surjective g
    obtain ⟨b, hb⟩ := (by decide : ∀ g : DihedralGroup 8, ∃ b : Fin 8,
      g = DihedralGroup.r 1 ^ b.val ∨
        g = DihedralGroup.r 1 ^ b.val * DihedralGroup.sr 0) g
    refine ⟨b, ?_⟩
    rcases hb with hb | hb
    · exact Or.inl (by simpa only [map_pow] using congrArg e hb)
    · exact Or.inr (by simpa only [map_mul, map_pow] using congrArg e hb)
  · intro g h hh
    obtain ⟨g, rfl⟩ := e.surjective g
    obtain ⟨h, rfl⟩ := e.surjective h
    have hm : (NilpotenceExamplesReverseInterlacingFailure.evenRotations).map e.toMonoidHom =
        Subgroup.zpowers ((e (DihedralGroup.r 1)) ^ 2) := by
      rw [NilpotenceExamplesReverseInterlacingFailure.evenRotations_eq_zpowers,
        MonoidHom.map_zpowers, ← map_pow,
        show (DihedralGroup.r 1 : DihedralGroup 8) ^ 2 = .r 2 by decide]
      rfl
    rw [← hm] at hh
    have hh' : h ∈ NilpotenceExamplesReverseInterlacingFailure.evenRotations :=
      (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hh
    have hi := (by decide : ∀ g h : DihedralGroup 8,
      h ∈ NilpotenceExamplesReverseInterlacingFailure.evenRotations →
      g * h * g⁻¹ = h ∨ g * h * g⁻¹ = h⁻¹) g h hh'
    rcases hi with hi | hi
    · exact Or.inl (by simpa only [map_mul, map_inv] using congrArg e hi)
    · exact Or.inr (by simpa only [map_mul, map_inv] using congrArg e hi)
  · have hn : (Subgroup.zpowers ((e (DihedralGroup.r 1)) ^ 2)).Normal := by
      rw [hN]
      infer_instance
    refine ⟨hn, ?_⟩
    haveI := hn
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hN.symm.le).is_comm.comm

theorem nilpotence_examples : AllExamples :=
  ⟨quaternion_example, symmetric_example, reverse_interlacing_example,
    symmetric_calculations, octagon_calculations⟩

end D07.Ch18.NilpotenceExamples
