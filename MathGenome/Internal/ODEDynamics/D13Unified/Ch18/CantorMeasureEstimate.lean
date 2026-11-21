import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.CantorMeasureEstimate
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.CantorGeometry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.BernoulliMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace D13Unified.Ch18.CantorMeasureEstimate
open Set MeasureTheory
open scoped ENNReal
open D13Unified.Ch17.CantorGeometry
open D13Unified.Ch17.ShiftSpaces
noncomputable section
abbrev cantorMeasure := Specs.D13Unified.Ch18.CantorMeasureEstimate.cantorMeasure
abbrev exponent := Specs.D13Unified.Ch18.CantorMeasureEstimate.exponent
abbrev intervalConstant := Specs.D13Unified.Ch18.CantorMeasureEstimate.intervalConstant
abbrev meetingWords := Specs.D13Unified.Ch18.CantorMeasureEstimate.meetingWords

lemma coding_measurable : Specs.D13Unified.Ch18.CantorMeasureEstimate.coding_measurableStatement := by
  intro r hr hrh
  exact (coding_continuous r hr hrh).measurable

lemma probability : Specs.D13Unified.Ch18.CantorMeasureEstimate.probabilityStatement := by
  intro r hr hrh
  have : IsProbabilityMeasure D13Unified.Ch19.BernoulliMeasure.bernoulliPlus :=
    D13Unified.Ch19.BernoulliMeasure.probability ℕ
  change IsProbabilityMeasure (Measure.map (coding r) D13Unified.Ch19.BernoulliMeasure.bernoulliPlus)
  infer_instance

lemma supported : Specs.D13Unified.Ch18.CantorMeasureEstimate.supportedStatement := by
  intro r hr hrh
  change Measure.map (coding r) D13Unified.Ch19.BernoulliMeasure.bernoulliPlus _ = _
  rw [Measure.map_apply (coding_measurable r hr hrh) (cantor_compact r hr hrh).isClosed.measurableSet.compl]
  have he : coding r ⁻¹' (cantorSet r)ᶜ = ∅ := by
    ext s
    simp [cantorSet, Specs.D13Unified.Ch17.CantorGeometry.cantorSet]
  rw [he, measure_empty]

lemma cylinder_mass : Specs.D13Unified.Ch18.CantorMeasureEstimate.cylinder_massStatement := by
  intro r hr hrh n w
  change Measure.map (coding r) D13Unified.Ch19.BernoulliMeasure.bernoulliPlus _ = _
  rw [Measure.map_apply (coding_measurable r hr hrh) (show MeasurableSet (levelInterval r w) from measurableSet_Icc)]
  let s : OneSided := fun j => if hj : j < n then w ⟨j,hj⟩ else 0
  have he : coding r ⁻¹' levelInterval r w = cylinder s (Finset.range n) := by
    ext t
    rw [mem_preimage, coding_mem_level_iff r hr hrh]
    constructor
    · intro h j hj
      simpa [s, Finset.mem_range.mp hj] using h ⟨j, Finset.mem_range.mp hj⟩
    · intro h i
      simpa [s, i.isLt] using h i (Finset.mem_range.mpr i.isLt)
  rw [he]
  simpa [D13Unified.Ch19.BernoulliMeasure.bernoulliPlus, Specs.D13Unified.Ch19.BernoulliMeasure.bernoulliPlus] using
    D13Unified.Ch19.BernoulliMeasure.cylinder_mass ℕ s (Finset.range n)

/-- A finite family of separated points in a real interval has bounded cardinality. -/
lemma separated_card {α : Type*} (s : Finset α) (f : α → ℝ)
    {a b g : ℝ} (hg : 0 < g) (hab : a ≤ b)
    (hbnd : ∀ i ∈ s, a ≤ f i ∧ f i ≤ b)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g ≤ |f i - f j|) :
    (s.card : ℝ) * g ≤ b-a+g := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, hmin⟩ := s.exists_min_image f hs
      have hbnd' : ∀ j ∈ s.erase i, f i + g ≤ f j ∧ f j ≤ b := by
        intro j hj
        have hjs := (Finset.mem_erase.mp hj).2
        have hjn := (Finset.mem_erase.mp hj).1
        have hd := hsep j hjs i hi hjn
        rw [abs_of_nonneg (sub_nonneg.mpr (hmin j hjs))] at hd
        exact ⟨by linarith, (hbnd j hjs).2⟩
      by_cases ht : (s.erase i).Nonempty
      · obtain ⟨j,hj⟩ := ht
        have hab' : f i + g ≤ b := (hbnd' j hj).1.trans (hbnd' j hj).2
        have hh := ih (s.erase i) (Finset.erase_ssubset hi) hab' hbnd'
          (fun j hj k hk hne => hsep j (Finset.mem_erase.mp hj).2 k (Finset.mem_erase.mp hk).2 hne)
        have hc : ((s.erase i).card : ℝ) + 1 = s.card := by
          exact_mod_cast Finset.card_erase_add_one hi
        nlinarith [(hbnd i hi).1]
      · have hc : s.card = 1 := by
          have he := Finset.not_nonempty_iff_eq_empty.mp ht
          simpa [he] using (Finset.card_erase_add_one hi).symm
        simp only [hc, Nat.cast_one, one_mul]
        linarith
    · have he := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [he, Finset.card_empty, Nat.cast_zero, zero_mul]
      linarith

lemma meeting_bound : Specs.D13Unified.Ch18.CantorMeasureEstimate.meeting_boundStatement := by
  intro r hr hrh n hn a b hab hu
  classical
  let S := meetingWords r n a b
  have hm : ∀ w ∈ S, (Icc a b ∩ levelInterval r w).Nonempty := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  let x : (Fin n → Binary) → ℝ := fun w =>
    if hw : w ∈ S then (hm w hw).choose else a
  have hx : ∀ w ∈ S, x w ∈ Icc a b ∩ levelInterval r w := by
    intro w hw
    simpa only [x, dite_eq_left hw] using (hm w hw).choose_spec
  have hg : 0 < (1-2*r)*r^(n-1) := mul_pos (by linarith) (pow_pos hr _)
  have hh := separated_card S x hg hab (fun w hw => (hx w hw).1)
    (fun v hv w hw hne => level_gap r hr hrh n hn v w hne _ (hx v hv).2 _ (hx w hw).2)
  have hp := pow_pos hr (n-1)
  have hgap : 0 < 1-2*r := by linarith
  have hdiv : (1-2*r) * (1 / (1-2*r)) = 1 := by field_simp
  change (S.card : ℝ) ≤ 2 + 1 / (1-2*r)
  apply le_of_mul_le_mul_right (a := r^(n-1)) _ hp
  apply le_of_mul_le_mul_right (a := 1-2*r) _ hgap
  nlinarith

lemma interval_mass_le_sum (r : ℝ) (hr : 0 < r) (hrh : r < 1/2)
    (n : ℕ) (a b : ℝ) :
    cantorMeasure r (Icc a b) ≤ (meetingWords r n a b).card * (2 : ℝ≥0∞)^(-(n:ℤ)) := by
  classical
  rw [← measure_inter_conull (s := Icc a b) (supported r hr hrh)]
  calc
    _ ≤ cantorMeasure r (⋃ w ∈ meetingWords r n a b, levelInterval r w) := by
      apply measure_mono
      rintro x ⟨hxJ,hxC⟩
      obtain ⟨w,hw⟩ := mem_iUnion.mp (level_cover r hr hrh n hxC)
      exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨x,hxJ,hw⟩⟩, hw⟩⟩
    _ ≤ ∑ w ∈ meetingWords r n a b, cantorMeasure r (levelInterval r w) :=
      measure_biUnion_finset_le _ _
    _ = _ := by simp_rw [cylinder_mass r hr hrh n]; simp

lemma binary_mass_eq (n : ℕ) :
    (2 : ℝ≥0∞)^(-(n:ℤ)) = ENNReal.ofReal ((1/2 : ℝ)^n) := by
  simp [ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow, ENNReal.ofReal_pow ]

lemma exponent_pos {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) : 0 < exponent r := by
  apply div_pos (Real.log_pos (by norm_num))
  apply Real.log_pos
  exact (one_lt_div hr).mpr (by linarith)

lemma scale_identity {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (n : ℕ) :
    (r^n) ^ exponent r = (1/2 : ℝ)^n := by
  have hlog : Real.log r ≠ 0 := ne_of_lt (Real.log_neg hr (by linarith))
  have he : Real.log r * exponent r = - Real.log 2 := by
    change Real.log r * (Real.log 2 / Real.log (1/r)) = _
    rw [one_div, Real.log_inv]
    field_simp
  rw [← Real.rpow_natCast_mul hr.le, mul_comm (n:ℝ), Real.rpow_mul_natCast hr.le]
  congr 1
  rw [Real.rpow_def_of_pos hr, he, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<2)]
  norm_num

lemma singleton_mass {r : ℝ} (hr : 0 < r) (hrh : r < 1/2) (x : ℝ) :
    cantorMeasure r {x} = 0 := by
  by_cases hx : x ∈ cantorSet r
  · obtain ⟨s,rfl⟩ := hx
    have hb : ∀ n : ℕ, cantorMeasure r {coding r s} ≤ ENNReal.ofReal ((1/2 : ℝ)^n) := by
      intro n
      rw [← binary_mass_eq]
      rw [← cylinder_mass r hr hrh n (fun i => s i)]
      apply measure_mono
      intro y hy
      have hy' : y = coding r s := hy
      subst y
      exact (coding_mem_level_iff r hr hrh n _ _).mpr (fun _ => rfl)
    have ht := ENNReal.tendsto_ofReal
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1))
    exact le_antisymm (by simpa using ge_of_tendsto' ht hb) bot_le
  · exact measure_mono_null (singleton_subset_iff.mpr hx) (supported r hr hrh)

lemma interval_bound_pos {r : ℝ} (hr : 0 < r) (hrh : r < 1/2)
    {a b : ℝ} (hab : a < b) (hu : b-a ≤ 1) :
    cantorMeasure r (Icc a b) ≤ ENNReal.ofReal (intervalConstant r * (b-a)^exponent r) := by
  have hg : 0 < 1-2*r := by linarith
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one (sub_pos.mpr hab) hu hr (by linarith)
  have hc := meeting_bound r hr hrh (n+1) (by omega) a b hab.le (by simpa using hnhi)
  have hpow : (1/2 : ℝ)^(n+1) ≤ (b-a)^exponent r := by
    rw [← scale_identity hr hrh]
    exact Real.rpow_le_rpow (pow_nonneg hr.le _) hnlo.le (exponent_pos hr hrh).le
  calc
    _ ≤ (meetingWords r (n+1) a b).card * (2 : ℝ≥0∞)^(-(((n+1 : ℕ):ℤ))) :=
      interval_mass_le_sum r hr hrh (n+1) a b
    _ = ENNReal.ofReal (((meetingWords r (n+1) a b).card : ℝ) * (1/2 : ℝ)^(n+1)) := by
      rw [binary_mass_eq, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul hc hpow (by positivity) (by
        change 0 ≤ 2 + 1 / (1-2*r)
        positivity))

lemma interval_bound : Specs.D13Unified.Ch18.CantorMeasureEstimate.interval_boundStatement := by
  intro r hr hrh
  have hc : 0 < intervalConstant r := by
    change 0 < 2 + 1 / (1-2*r)
    have hg : 0 < 1-2*r := by linarith
    positivity
  refine ⟨exponent_pos hr hrh, hc, ?_⟩
  intro a b hab hu
  rcases hab.eq_or_lt with he | hlt
  · subst b
    simp [singleton_mass hr hrh, Real.zero_rpow (ne_of_gt (exponent_pos hr hrh))]
  · exact interval_bound_pos hr hrh hlt hu

/-- The closed interval estimate controls every bounded subset, and in
particular every choice of open or closed endpoints for a short interval. -/
lemma bounded_set_bound : Specs.D13Unified.Ch18.CantorMeasureEstimate.bounded_set_boundStatement := by
  intro r hr hrh J hJ hdiam
  by_cases hne : J.Nonempty
  · have hab : sInf J ≤ sSup J := csInf_le_csSup hne hJ.bddBelow hJ.bddAbove
    calc
      _ ≤ cantorMeasure r (Icc (sInf J) (sSup J)) := measure_mono hJ.subset_Icc_sInf_sSup
      _ ≤ _ := by
        rw [Real.diam_eq hJ] at hdiam ⊢
        exact (interval_bound r hr hrh).2.2 _ _ hab hdiam
  · rw [not_nonempty_iff_eq_empty.mp hne, measure_empty]
    exact bot_le

end
end D13Unified.Ch18.CantorMeasureEstimate
