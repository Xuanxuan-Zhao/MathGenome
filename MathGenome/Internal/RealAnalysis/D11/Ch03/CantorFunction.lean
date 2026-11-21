import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorFunction
import MathGenome.Internal.RealAnalysis.D11.Ch03.CantorSet

noncomputable section
open Set
open D11.Ch03.CantorStaircase

namespace D11.Ch03.CantorFunction

def Gamma : ℝ → ℝ := staircase

/-- Positional expansions respect the order at the first different digit. -/
lemma ofDigits_le_of_first_difference {b : ℕ} (hb : 0 < b)
    (a c : ℕ → Fin b) (n : ℕ) (hprefix : ∀ i < n, a i = c i)
    (hd : (a n : ℕ) + 1 ≤ (c n : ℕ)) : Real.ofDigits a ≤ Real.ofDigits c := by
  have hp : (∑ i ∈ Finset.range n, Real.ofDigitsTerm a i) =
      ∑ i ∈ Finset.range n, Real.ofDigitsTerm c i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Real.ofDigitsTerm, hprefix i (Finset.mem_range.mp hi)]
  have htaila := Real.ofDigits_le_one (fun i => a (i + (n + 1)))
  have htailc := Real.ofDigits_nonneg (fun i => c (i + (n + 1)))
  have hd' : (a n : ℝ) + 1 ≤ (c n : ℝ) := by exact_mod_cast hd
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hpos : 0 < ((b : ℝ) ^ (n + 1))⁻¹ := by positivity
  rw [Real.ofDigits_eq_sum_add_ofDigits a (n + 1),
    Real.ofDigits_eq_sum_add_ofDigits c (n + 1), Finset.sum_range_succ,
    Finset.sum_range_succ, hp]
  simp only [Real.ofDigitsTerm]
  nlinarith [mul_nonneg hpos.le (show 0 ≤ (c n : ℝ) +
    Real.ofDigits (fun i => c (i + (n + 1))) -
    ((a n : ℝ) + Real.ofDigits (fun i => a (i + (n + 1)))) by linarith)]

lemma ofDigits_lt_of_first_difference {b : ℕ} (hb : 0 < b)
    (a c : ℕ → Fin b) (n : ℕ) (hprefix : ∀ i < n, a i = c i)
    (hd : (a n : ℕ) + 1 < (c n : ℕ)) : Real.ofDigits a < Real.ofDigits c := by
  have hp : (∑ i ∈ Finset.range n, Real.ofDigitsTerm a i) =
      ∑ i ∈ Finset.range n, Real.ofDigitsTerm c i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [Real.ofDigitsTerm, hprefix i (Finset.mem_range.mp hi)]
  have htaila := Real.ofDigits_le_one (fun i => a (i + (n + 1)))
  have htailc := Real.ofDigits_nonneg (fun i => c (i + (n + 1)))
  have hd' : (a n : ℝ) + 1 < (c n : ℝ) := by exact_mod_cast hd
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hpos : 0 < ((b : ℝ) ^ (n + 1))⁻¹ := by positivity
  rw [Real.ofDigits_eq_sum_add_ofDigits a (n + 1),
    Real.ofDigits_eq_sum_add_ofDigits c (n + 1), Finset.sum_range_succ,
    Finset.sum_range_succ, hp]
  simp only [Real.ofDigitsTerm]
  nlinarith [mul_pos hpos (show 0 < (c n : ℝ) +
    Real.ofDigits (fun i => c (i + (n + 1))) -
    ((a n : ℝ) + Real.ofDigits (fun i => a (i + (n + 1)))) by linarith)]

lemma digit_order (a c : ℕ → Bool) (h : ternary a ≤ ternary c) : binary a ≤ binary c := by
  classical
  by_cases heq : a = c
  · simp [heq]
  have hex : ∃ n, a n ≠ c n := Function.ne_iff.mp heq
  let n := Nat.find hex
  have hp : ∀ i < n, a i = c i := by
    intro i hi
    exact not_not.mp (Nat.find_min hex hi)
  have hd : a n ≠ c n := Nat.find_spec hex
  cases ha : a n <;> cases hc : c n
  · exact (hd (ha.trans hc.symm)).elim
  · apply ofDigits_le_of_first_difference (by decide : 0 < 2) _ _ n
    · intro i hi
      simp [hp i hi]
    · simp [ha, hc]
  · have hlt : ternary c < ternary a := by
      apply ofDigits_lt_of_first_difference (by decide : 0 < 3) _ _ n
      · intro i hi
        simp [(hp i hi).symm]
      · simp [ha, hc]
    exact (not_lt_of_ge h hlt).elim
  · exact (hd (ha.trans hc.symm)).elim

lemma lowerValues_nonempty (x : ℝ) : (lowerValues x).Nonempty :=
  ⟨0, Or.inl rfl⟩

lemma lowerValues_bddAbove (x : ℝ) : BddAbove (lowerValues x) := by
  refine ⟨1, ?_⟩
  rintro y (rfl | ⟨a, _, rfl⟩)
  · norm_num
  · exact Real.ofDigits_le_one _

lemma Gamma_bounds (x : ℝ) : Gamma x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csSup (lowerValues_bddAbove x) (Or.inl rfl)
  · apply csSup_le (lowerValues_nonempty x)
    rintro y (rfl | ⟨a, _, rfl⟩)
    · norm_num
    · exact Real.ofDigits_le_one _

theorem maps_unit_interval : Specs.D11.Ch03.CantorFunction.maps_unit_interval := by
  intro x _
  exact Gamma_bounds x

theorem monotone : Specs.D11.Ch03.CantorFunction.monotone := by
  intro x y hxy
  apply csSup_le (lowerValues_nonempty x)
  intro z hz
  apply le_csSup (lowerValues_bddAbove y)
  rcases hz with rfl | ⟨a, ha, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, ha.trans hxy, rfl⟩

/-- The extension agrees with the binary digit map on the Cantor set. -/
theorem Gamma_ternary (a : ℕ → Bool) : Gamma (ternary a) = binary a := by
  apply le_antisymm
  · apply csSup_le (lowerValues_nonempty _)
    rintro y (rfl | ⟨c, hc, rfl⟩)
    · exact Real.ofDigits_nonneg _
    · exact digit_order c a hc
  · exact le_csSup (lowerValues_bddAbove _) (Or.inr ⟨a, (show ternary a ≤ ternary a from le_rfl), rfl⟩)

lemma ternary_mem_C (a : ℕ → Bool) : ternary a ∈ CantorSet.C :=
  ofDigits_bool_to_fin_three_mem_cantorSet a

lemma binary_surj (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : ∃ a, binary a = y := by
  obtain ⟨a, _, ha⟩ := Real.ofDigits_SurjOn (by decide : 1 < 2) hy
  refine ⟨fun n => decide (a n = 1), ?_⟩
  convert ha using 1
  unfold binary
  congr 1
  funext n
  have h : a n = 0 ∨ a n = 1 := by omega
  rcases h with h | h <;> simp [h]

theorem cantor_surjective : Specs.D11.Ch03.CantorFunction.cantor_surjective := by
  intro y hy
  obtain ⟨a, ha⟩ := binary_surj y hy
  exact ⟨ternary a, ternary_mem_C a, (Gamma_ternary a).trans ha⟩

theorem surjective : Specs.D11.Ch03.CantorFunction.surjective := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := cantor_surjective hy
  exact ⟨x, CantorSet.C_subset hx, hxy⟩

theorem endpoints : Specs.D11.Ch03.CantorFunction.endpoints := by
  constructor
  · change Gamma 0 = 0
    simpa [ternary, binary, Real.ofDigits, Real.ofDigitsTerm] using
      Gamma_ternary (fun _ => false)
  · have ht : ternary (fun _ => true) = 1 := Real.ofDigits_const_last_eq_one 2
    have hb : binary (fun _ => true) = 1 := Real.ofDigits_const_last_eq_one 1
    change Gamma 1 = 1
    calc
      Gamma 1 = Gamma (ternary (fun _ => true)) := congrArg Gamma ht.symm
      _ = binary (fun _ => true) := Gamma_ternary _
      _ = 1 := hb

/-- Regard the same function as a self-map of the unit interval. -/
def unitMap (x : Icc (0 : ℝ) 1) : Icc (0 : ℝ) 1 := ⟨Gamma x, Gamma_bounds x⟩

lemma unitMap_monotone : Monotone unitMap := by
  intro x y hxy
  exact monotone hxy

lemma unitMap_surjective : Function.Surjective unitMap := by
  intro y
  obtain ⟨x, hx, hxy⟩ := surjective y.property
  refine ⟨⟨x, hx⟩, ?_⟩
  exact Subtype.ext hxy

theorem continuous : Specs.D11.Ch03.CantorFunction.continuous := by
  have hc : Continuous unitMap := unitMap_monotone.continuous_of_surjective unitMap_surjective
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hc)

theorem digit_formula : Specs.D11.Ch03.CantorFunction.digit_formula := by
  intro a
  have ht : (∑' n, (if a n then (2 : ℝ) else 0) / 3 ^ (n + 1)) = ternary a := by
    unfold ternary Real.ofDigits
    apply tsum_congr
    intro n
    cases h : a n <;> simp [Real.ofDigitsTerm, h, div_eq_mul_inv]
  have hb : (∑' n, (if a n then (1 : ℝ) else 0) / 2 ^ (n + 1)) = binary a := by
    unfold binary Real.ofDigits
    apply tsum_congr
    intro n
    cases h : a n <;> simp [Real.ofDigitsTerm, h, div_eq_mul_inv]
  change Gamma _ = _
  rw [ht, hb, Gamma_ternary]

/-- Two ordered arguments with no Cantor point between them have the same value.
Otherwise an intermediate binary value has a Cantor preimage strictly between them. -/
lemma Gamma_eq_of_no_C_between {x y : ℝ} (hxy : x ≤ y)
    (hgap : Disjoint (Ioo x y) CantorSet.C) : Gamma x = Gamma y := by
  by_contra hne
  have hlt : Gamma x < Gamma y := lt_of_le_of_ne (monotone hxy) hne
  let t := (Gamma x + Gamma y) / 2
  have hxt : Gamma x < t := by dsimp [t]; linarith
  have hty : t < Gamma y := by dsimp [t]; linarith
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    have hx := Gamma_bounds x
    have hy := Gamma_bounds y
    constructor <;> linarith [hx.1, hy.2]
  obtain ⟨z, hz, hzt⟩ := cantor_surjective ht
  change Gamma z = t at hzt
  have hxz : x < z := by
    by_contra hn
    have := monotone (le_of_not_gt hn)
    change Gamma z ≤ Gamma x at this
    linarith
  have hzy : z < y := by
    by_contra hn
    have := monotone (le_of_not_gt hn)
    change Gamma y ≤ Gamma z at this
    linarith
  exact Set.disjoint_left.mp hgap ⟨hxz, hzy⟩ hz

lemma constant_on_preconnected {s : Set ℝ}
    (hsub : s ⊆ Icc (0 : ℝ) 1 \ CantorSet.C) (hs : IsPreconnected s)
    {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) : Gamma x = Gamma y := by
  wlog hxy : x ≤ y generalizing x y
  · exact (this hy hx (le_of_not_ge hxy)).symm
  apply Gamma_eq_of_no_C_between hxy
  apply Set.disjoint_left.mpr
  intro z hz hzc
  exact (hsub (hs.Icc_subset hx hy ⟨hz.1.le, hz.2.le⟩)).2 hzc

theorem constant_on_components : Specs.D11.Ch03.CantorFunction.constant_on_components := by
  intro x hx y hy
  apply constant_on_preconnected (connectedComponentIn_subset _ _)
    isPreconnected_connectedComponentIn hy (mem_connectedComponentIn hx)

theorem constant_on_gap_closure : Specs.D11.Ch03.CantorFunction.constant_on_gap_closure := by
  intro a b _ _ hab hgap x hx
  have heq := Gamma_eq_of_no_C_between hab.le hgap
  apply le_antisymm
  · exact (monotone hx.2).trans_eq heq.symm
  · exact monotone hx.1

end D11.Ch03.CantorFunction
