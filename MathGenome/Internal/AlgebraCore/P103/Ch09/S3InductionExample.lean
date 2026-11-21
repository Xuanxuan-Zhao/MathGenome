import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.S3InductionExample
import MathGenome.Internal.AlgebraCore.P103.Ch09.MackeyIrreducibility
import MathGenome.Internal.AlgebraCore.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.P103.Ch08.S3CharacterTable
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace P103.Ch09.S3InductionExample
open Ch08.S3CharacterTableSpecs S3InductionExampleSpecs
open scoped BigOperators

local instance : DecidablePred (· ∈ H) := Equiv.Perm.sign.decidableMemKer

private theorem h_elements : ∀ g : S3, g ∈ H ↔
    g = 1 ∨ g = threeCycle ∨ g = threeCycle⁻¹ := by decide

private theorem outside_conjugates : ∀ s : S3, s ∉ H →
    s⁻¹ * threeCycle * s = threeCycle⁻¹ := by decide

private theorem no_transposition_conjugate :
    ∀ g : S3, IsConj g transposition → ∀ x : S3, x⁻¹ * g * x ∉ H := by
  simp_rw [Equiv.Perm.isConj_iff_cycleType_eq]
  decide

theorem subgroup_structure : subgroupType := by
  refine ⟨?_, ?_, ?_, by decide, by decide, outside_conjugates,
    no_transposition_conjugate⟩
  · apply le_antisymm
    · intro g hg
      rcases (h_elements g).mp hg with rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · exact (Subgroup.closure_le H).mpr (by intro g hg; simp only [Set.mem_singleton_iff] at hg; subst g; exact c.property)
  · rw [Nat.card_eq_fintype_card]; decide
  · exact alternatingGroup.index_eq_two

theorem primitive_root_identities : rootIdentitiesType := by
  intro ζ hζ
  have hp : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hz : ζ ≠ 0 := by intro h; simp [h] at hp
  have hi : ζ⁻¹ = ζ ^ 2 := by
    apply (mul_left_cancel₀ hz)
    simp only [mul_inv_cancel₀ hz]
    simpa [pow_succ, mul_comm] using hp.symm
  have hs : ζ + ζ ^ 2 = -1 := by
    have h := hζ.geom_sum_eq_zero (by decide : 1 < 3)
    norm_num [Finset.sum_range_succ] at h
    linear_combination h
  refine ⟨hi, by rw [hi]; exact hs, ?_⟩
  intro he
  have he' : ζ = ζ ^ 2 := he.trans hi
  have : ζ = 1 := by
    apply (mul_left_cancel₀ hz)
    simpa [pow_two] using he'.symm
  exact hζ.ne_one (by decide) this

private def scalar (ζ : ℂ) (h : H) : ℂ :=
  if (h : S3) = 1 then 1 else if (h : S3) = threeCycle then ζ else ζ ^ 2

private theorem scalar_mul (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (a b : H) :
    scalar ζ (a * b) = scalar ζ a * scalar ζ b := by
  have hc : threeCycle ≠ (1 : S3) := by decide
  have hci : threeCycle⁻¹ ≠ (1 : S3) := by decide
  have hic : threeCycle⁻¹ ≠ threeCycle := by decide
  have hcc : threeCycle * threeCycle = threeCycle⁻¹ := by decide
  have hii : threeCycle⁻¹ * threeCycle⁻¹ = threeCycle := by decide
  have hp : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hp4 : ζ ^ 4 = ζ := by calc
    ζ ^ 4 = ζ ^ 3 * ζ := by ring
    _ = ζ := by rw [hp]; ring
  rcases (h_elements a).mp a.property with ha | ha | ha <;>
    rcases (h_elements b).mp b.property with hb | hb | hb <;>
    simp [scalar, Subgroup.coe_mul, ha, hb, hc, hci, hic, hcc, hii]
  all_goals first
    | exact pow_two ζ
    | simpa [← pow_succ, ← pow_succ', ← pow_add] using hp.symm
    | simpa [← pow_add] using hp4.symm

private def line (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) : Representation ℂ H ℂ where
  toFun h := scalar ζ h • LinearMap.id
  map_one' := by apply LinearMap.ext; intro z; simp [scalar]
  map_mul' a b := by
    apply LinearMap.ext
    intro z
    simp [scalar_mul ζ hζ, mul_smul, mul_comm, mul_left_comm, mul_assoc]

private theorem line_apply (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (h : H) (z : ℂ) :
    line ζ hζ h z = scalar ζ h * z := rfl

private theorem scalar_c (ζ : ℂ) : scalar ζ c = ζ := by
  simp [scalar, c, show threeCycle ≠ (1 : S3) by decide]

private theorem scalar_c_inv (ζ : ℂ) : scalar ζ c⁻¹ = ζ ^ 2 := by
  simp [scalar, c, show threeCycle⁻¹ ≠ (1 : S3) by decide,
    show threeCycle⁻¹ ≠ threeCycle by decide]

private theorem line_irreducible (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) :
    Ch08.Irreducible ℂ H ℂ (line ζ hζ) := by
  refine ⟨inferInstance, fun U => ?_⟩
  rcases eq_bot_or_eq_top U.toSubmodule with h | h
  · left; exact Subrepresentation.toSubmodule_injective h
  · right; exact Subrepresentation.toSubmodule_injective h

private theorem line_distinct (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3)
    (s : S3) (hs : s ∉ H) :
    ¬ Nonempty ((line ζ hζ).Equiv (MackeyIrreducibility.normalTwist H (line ζ hζ) s)) := by
  rintro ⟨e⟩
  have hc : MackeyIrreducibility.normalConjugation H s c = c⁻¹ := by
    apply Subtype.ext
    exact outside_conjugates s hs
  have he := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap c (1 : ℂ)
  change e (line ζ hζ c 1) = line ζ hζ
    (MackeyIrreducibility.normalConjugation H s c) (e 1) at he
  rw [hc, line_apply, line_apply, scalar_c, scalar_c_inv, mul_one] at he
  have hel : e ζ = ζ * e 1 := by simpa using e.map_smul ζ (1 : ℂ)
  rw [hel] at he
  have he1 : e 1 ≠ 0 := by
    intro h
    have : e 1 = e 0 := by simpa only [map_zero] using h
    exact one_ne_zero (e.injective this)
  have hz : ζ = ζ ^ 2 := mul_right_cancel₀ he1 he
  exact (primitive_root_identities ζ hζ).2.2
    (hz.trans (primitive_root_identities ζ hζ).1.symm)

private theorem line_character (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) (h : H) :
    Ch08.CharacterSpecs.characterValue (line ζ hζ) h = scalar ζ h := by
  simp [Ch08.CharacterSpecs.characterValue, line, map_smul]

open private sum_permutations from MathGenome.Internal.AlgebraCore.P103.Ch08.S3CharacterTable

private theorem induced_cycle_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 3) :
    InducedCharacterSpecs.inductionValue H
      (Ch08.CharacterSpecs.characterValue (line ζ hζ)) threeCycle = ζ + ζ⁻¹ := by
  have hm : ∀ x : S3, x⁻¹ * threeCycle * x ∈ H := by decide
  have hconj : ∀ x : S3, x⁻¹ * threeCycle * x =
      if x ∈ H then threeCycle else threeCycle⁻¹ := by decide
  have hc : threeCycle ≠ (1 : S3) := by decide
  have hci : threeCycle⁻¹ ≠ (1 : S3) := by decide
  have hic : threeCycle⁻¹ ≠ threeCycle := by decide
  classical
  unfold InducedCharacterSpecs.inductionValue
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  convert_to (Nat.card H : ℂ)⁻¹ * (∑ x : S3, if x ∈ H then ζ else ζ ^ 2) = ζ + ζ⁻¹
  · congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [dite_eq_left (hm x), line_character]
    unfold scalar
    change (if x⁻¹ * threeCycle * x = 1 then (1 : ℂ) else
      if x⁻¹ * threeCycle * x = threeCycle then ζ else ζ ^ 2) = _
    rw [hconj x]
    by_cases hx : x ∈ H <;> simp [hx, hc, hci, hic]
  rw [sum_permutations, subgroup_structure.2.1, (primitive_root_identities ζ hζ).1]
  norm_num [H, threeCycle, transposition]
  ring

/-- The nontrivial A₃ line induces the standard two-dimensional type. -/
theorem realization : realizationType := by
  intro ζ hζ
  refine ⟨line ζ hζ, ?_, line_irreducible ζ hζ, line_distinct ζ hζ, ?_⟩
  · intro z
    rw [line_apply, scalar_c]
  intro D E
  letI := D.module
  have hirr : Ch08.Irreducible ℂ S3 (Induced H (line ζ hζ)) D.representation :=
    (MackeyIrreducibility.normal_criterion H (line ζ hζ) D).mpr
      ⟨line_irreducible ζ hζ, line_distinct ζ hζ⟩
  obtain ⟨hfd, hformula, hone, hvanish⟩ := induced_character H (line ζ hζ) D E
  letI := hfd
  have he : Ch08.CharacterSpecs.characterValue D.representation 1 = 2 := by
    simpa [subgroup_structure.2.2.1] using hone
  have hc : Ch08.CharacterSpecs.characterValue D.representation threeCycle = ζ + ζ⁻¹ :=
    (hformula threeCycle).trans (induced_cycle_sum ζ hζ)
  have hcm : Ch08.CharacterSpecs.characterValue D.representation threeCycle = -1 :=
    hc.trans (primitive_root_identities ζ hζ).2.1
  have hrow : CharacterRow (Ch08.CharacterSpecs.characterValue D.representation) := by
    refine ⟨he, ?_, ?_⟩
    · intro g hg
      exact hvanish g (no_transposition_conjugate g hg)
    · intro g hg
      obtain ⟨a, ha⟩ := isConj_iff.mp hg
      have h := Ch08.character_conjugate D.representation g a
      rw [ha] at h
      exact h.symm.trans hcm
  have hdim : Module.finrank ℂ (Induced H (line ζ hζ)) = 2 := by
    have hcast : (Module.finrank ℂ (Induced H (line ζ hζ)) : ℂ) = 2 := by
      simpa [Ch08.CharacterSpecs.characterValue] using he
    exact_mod_cast hcast
  have hstandard : Nonempty (standardValue.Equiv D.representation) := by
    rcases Ch08.S3CharacterTable.exhaustive D.representation hirr with ht | hs | hstd
    · obtain ⟨e⟩ := ht
      have h := congrFun (Ch08.RegularMultiplicity.character_of_equiv e) 1
      rw [Ch08.S3CharacterTable.trivial_row.1, he] at h
      norm_num at h
    · obtain ⟨e⟩ := hs
      have h := congrFun (Ch08.RegularMultiplicity.character_of_equiv e) 1
      rw [Ch08.S3CharacterTable.sign_row.1, he] at h
      norm_num at h
    · exact hstd
  exact ⟨hfd, hirr, hdim, hrow, hc, hstandard⟩

end P103.Ch09.S3InductionExample
