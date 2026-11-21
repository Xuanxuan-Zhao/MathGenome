import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.ShiftSpaces
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace D13Unified.Ch17.ShiftSpaces
open Set TopologicalSpace Topology
noncomputable section
abbrev Binary := Specs.D13Unified.Ch17.ShiftSpaces.Binary
abbrev OneSided := Specs.D13Unified.Ch17.ShiftSpaces.OneSided
abbrev TwoSided := Specs.D13Unified.Ch17.ShiftSpaces.TwoSided
abbrev shiftPlus := Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus
abbrev shift := Specs.D13Unified.Ch17.ShiftSpaces.shift
abbrev shiftRight := Specs.D13Unified.Ch17.ShiftSpaces.shiftRight
abbrev distancePlus := Specs.D13Unified.Ch17.ShiftSpaces.distancePlus
abbrev weight := Specs.D13Unified.Ch17.ShiftSpaces.weight
abbrev distance := Specs.D13Unified.Ch17.ShiftSpaces.distance
abbrev cylinder := @Specs.D13Unified.Ch17.ShiftSpaces.cylinder
abbrev prefixCylinder := Specs.D13Unified.Ch17.ShiftSpaces.prefixCylinder

theorem distancePlus_eq : Specs.D13Unified.Ch17.ShiftSpaces.distancePlus_eqStatement := by
  intro s t
  classical
  by_cases h : s = t
  · subst t
    simpa [Specs.D13Unified.Ch17.ShiftSpaces.distancePlus] using PiNat.dist_self s
  · simpa [distancePlus, Specs.D13Unified.Ch17.ShiftSpaces.distancePlus, PiNat.dist, h] using
      PiNat.dist_eq_of_ne h

theorem weight_eq : Specs.D13Unified.Ch17.ShiftSpaces.weight_eqStatement := by
  intro j
  change (1 / 2 : ℝ) ^ (j.natAbs + 2) = _
  rw [show -(j.natAbs : ℤ) - 2 = -((j.natAbs + 2 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast]
  simp only [one_div, inv_pow]

theorem metricPlus_exists : Specs.D13Unified.Ch17.ShiftSpaces.metricPlus_existsStatement := by
  exact ⟨(PiNat.metricSpace (E := fun _ => Binary)), rfl, fun _ _ => rfl⟩

theorem prefixes_basis : Specs.D13Unified.Ch17.ShiftSpaces.prefixes_basisStatement :=
  PiNat.isTopologicalBasis_cylinders (fun _ => Binary)

theorem shiftPlus_continuous : Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus_continuousStatement :=
  continuous_pi fun j => continuous_apply (j + 1)

theorem shiftPlus_surjective : Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus_surjectiveStatement := by
  intro s
  refine ⟨fun j => if j = 0 then 0 else s (j - 1), ?_⟩
  funext j
  simp [Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus]

theorem shiftPlus_not_injective :
    Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus_not_injectiveStatement := by
  intro h
  have heq : shiftPlus (fun _ => 0) = shiftPlus (fun j => if j = 0 then 1 else 0) := by
    funext j
    simp [Specs.D13Unified.Ch17.ShiftSpaces.shiftPlus]
  have hh := congrFun (h heq) 0
  norm_num at hh

theorem shift_continuous : Specs.D13Unified.Ch17.ShiftSpaces.shift_continuousStatement :=
  continuous_pi fun j => continuous_apply (j + 1)

theorem shiftRight_continuous : Specs.D13Unified.Ch17.ShiftSpaces.shiftRight_continuousStatement :=
  continuous_pi fun j => continuous_apply (j - 1)

theorem shift_inverse : Specs.D13Unified.Ch17.ShiftSpaces.shift_inverseStatement := by
  constructor <;> intro s <;> funext j <;>
    simp [Specs.D13Unified.Ch17.ShiftSpaces.shift,
      Specs.D13Unified.Ch17.ShiftSpaces.shiftRight]

theorem shift_homeomorph : Specs.D13Unified.Ch17.ShiftSpaces.shift_homeomorphStatement := by
  exact ⟨{ toFun := shift, invFun := shiftRight, left_inv := shift_inverse.1, right_inv := shift_inverse.2, continuous_toFun := shift_continuous, continuous_invFun := shiftRight_continuous }, rfl, rfl⟩

theorem cylinders_basis : Specs.D13Unified.Ch17.ShiftSpaces.cylinders_basisStatement := by
  intro I
  classical
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro U ⟨s, F, rfl⟩
    change IsOpen ((F : Set I).pi (fun j => {s j}))
    exact isOpen_set_pi F.finite_toSet fun _ _ => isOpen_discrete _
  · intro s U hs hU
    rcases (isTopologicalBasis_pi fun _ : I => isTopologicalBasis_opens).exists_subset_of_mem_open
      hs hU with ⟨V, ⟨W, F, hW, rfl⟩, hsV, hVU⟩
    refine ⟨cylinder s F, ⟨s, F, rfl⟩, (fun _ _ => rfl), ?_⟩
    apply Subset.trans _ hVU
    intro t ht j hj
    rw [ht j hj]
    exact hsV j hj

lemma weight_pos (j : ℤ) : 0 < weight j := by
  unfold weight Specs.D13Unified.Ch17.ShiftSpaces.weight
  positivity

lemma weight_summable : Summable weight := by
  apply summable_int_iff_summable_nat_and_neg.mpr
  have h : Summable (fun n : ℕ => (1 / 2 : ℝ)^n * (1 / 2 : ℝ)^2) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_right _
  constructor <;> simpa [weight, Specs.D13Unified.Ch17.ShiftSpaces.weight, pow_add] using h

lemma symbol_abs_le (a b : Binary) : |(a.val : ℝ) - (b.val : ℝ)| ≤ 1 := by
  fin_cases a <;> fin_cases b <;> norm_num

lemma symbol_abs_of_ne {a b : Binary} (h : a ≠ b) :
    |(a.val : ℝ) - (b.val : ℝ)| = 1 := by
  fin_cases a <;> fin_cases b <;> norm_num at *

lemma distance_summable (s t : TwoSided) :
    Summable (fun j => weight j * |((s j).val : ℝ) - ((t j).val : ℝ)|) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (weight_pos j).le (abs_nonneg _))
    (fun j => ?_) weight_summable
  exact mul_le_of_le_one_right (weight_pos j).le (symbol_abs_le _ _)

lemma distance_self (s : TwoSided) : distance s s = 0 := by
  simp [distance, Specs.D13Unified.Ch17.ShiftSpaces.distance]

lemma distance_comm (s t : TwoSided) : distance s t = distance t s := by
  unfold distance Specs.D13Unified.Ch17.ShiftSpaces.distance
  congr 1
  funext j
  rw [abs_sub_comm]

lemma distance_triangle (s t u : TwoSided) : distance s u ≤ distance s t + distance t u := by
  unfold distance Specs.D13Unified.Ch17.ShiftSpaces.distance
  rw [← (distance_summable s t).tsum_add (distance_summable t u)]
  apply Summable.tsum_le_tsum _ (distance_summable s u)
    ((distance_summable s t).add (distance_summable t u))
  intro j
  simpa only [mul_add] using mul_le_mul_of_nonneg_left
    (abs_sub_le ((s j).val : ℝ) ((t j).val : ℝ) ((u j).val : ℝ)) (weight_pos j).le

lemma coordinate_le_distance (s t : TwoSided) (j : ℤ) :
    weight j * |((s j).val : ℝ) - ((t j).val : ℝ)| ≤ distance s t :=
  (distance_summable s t).le_tsum j (fun k _ => mul_nonneg (weight_pos k).le (abs_nonneg _))

lemma coordinate_eq_of_distance_lt (s t : TwoSided) (j : ℤ)
    (h : distance s t < weight j) : s j = t j := by
  by_contra hne
  have hh := coordinate_le_distance s t j
  rw [symbol_abs_of_ne hne, mul_one] at hh
  exact (not_lt_of_ge hh) h

lemma eq_of_distance_zero (s t : TwoSided) (h : distance s t = 0) : s = t := by
  funext j
  apply coordinate_eq_of_distance_lt s t j
  rw [h]
  exact weight_pos j

lemma distance_continuous_right (s : TwoSided) : Continuous (distance s) := by
  refine continuous_tsum (fun j => ?_) weight_summable (fun j t => ?_)
  · have hval : Continuous (fun a : Binary => (a.val : ℝ)) := continuous_of_discreteTopology
    have hc : Continuous (fun t : TwoSided => ((t j).val : ℝ)) :=
      hval.comp (continuous_apply j)
    exact continuous_const.mul ((continuous_const.sub hc).abs)
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_pos j).le (abs_nonneg _))]
    exact mul_le_of_le_one_right (weight_pos j).le (symbol_abs_le _ _)

lemma finite_weight_lower_bound (F : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ j ∈ F, ε ≤ weight j := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert j F hj ih =>
    rcases ih with ⟨ε, hε, hF⟩
    refine ⟨min ε (weight j), lt_min hε (weight_pos j), ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hF k hk)

lemma isOpen_iff_distance (U : Set TwoSided) :
    IsOpen U ↔ ∀ s ∈ U, ∃ ε > 0, ∀ t, distance s t < ε → t ∈ U := by
  constructor
  · intro hU s hs
    rcases (cylinders_basis ℤ).exists_subset_of_mem_open hs hU with
      ⟨V, ⟨t, F, rfl⟩, hsV, hVU⟩
    rcases finite_weight_lower_bound F with ⟨ε, hε, hF⟩
    refine ⟨ε, hε, fun u hu => hVU ?_⟩
    intro j hj
    exact (coordinate_eq_of_distance_lt s u j (hu.trans_le (hF j hj))).symm.trans (hsV j hj)
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro s hs
    rcases h s hs with ⟨ε, hε, hU⟩
    apply Filter.mem_of_superset
      ((isOpen_Iio.preimage (distance_continuous_right s)).mem_nhds ?_) hU
    change distance s s < ε
    rwa [distance_self]

theorem metric_exists : Specs.D13Unified.Ch17.ShiftSpaces.metric_existsStatement := by
  refine ⟨MetricSpace.ofDistTopology distance distance_self distance_comm distance_triangle
    isOpen_iff_distance eq_of_distance_zero, rfl, fun _ _ => rfl⟩

end
end D13Unified.Ch17.ShiftSpaces
