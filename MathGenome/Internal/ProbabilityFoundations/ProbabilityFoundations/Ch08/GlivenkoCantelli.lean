import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.GlivenkoCantelli
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch08.EtemadiStrongLaw
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch01.RealDistributionFunctions
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Glivenko--Cantelli (paper.tex:3041–3069), on the original probability
space, without a completeness or atomlessness hypothesis. A countable family
of generalized-inverse grids gives finite brackets for all real thresholds.
Both strict and closed empirical values are used, so jumps and repeated grid
points cause no loss. Right continuity reduces the real supremum to rationals. -/

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology Classical

namespace ProbabilityFoundations.Ch08

universe u

noncomputable def empiricalDistribution {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, if X k ω ≤ x then (1 : ℝ) else 0) / (n : ℝ)

noncomputable def commonDistribution {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (x : ℝ) : ℝ :=
  (P {ω | X 1 ω ≤ x}).toReal

noncomputable def distributionDeviation {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ⨆ x : ℝ, |empiricalDistribution X n ω x - commonDistribution P X x|

lemma empiricalDistribution_nonneg {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) : 0 ≤ empiricalDistribution X n ω x := by
  unfold empiricalDistribution
  positivity

lemma empiricalDistribution_le_one {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) : empiricalDistribution X n ω x ≤ 1 := by
  cases n with
  | zero => simp [empiricalDistribution]
  | succ n =>
    apply (div_le_one (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    calc
      _ ≤ ∑ _k ∈ Finset.Icc 1 (n + 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        split_ifs <;> norm_num
      _ = (n + 1 : ℕ) := by simp

lemma commonDistribution_eq_law {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : Measurable (X 1)) :
    commonDistribution P X = Ch01.realDistributionFunction (P.map (X 1)) := by
  funext x
  rw [commonDistribution, Ch01.realDistributionFunction, Measure.map_apply hX measurableSet_Iic]
  rfl

lemma commonDistribution_bounds {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (x : ℝ) :
    0 ≤ commonDistribution P X x ∧ commonDistribution P X x ≤ 1 := by
  exact ⟨ENNReal.toReal_nonneg, by
    simpa [commonDistribution, measureReal_def] using (measureReal_le_one (μ := P) (s := {ω | X 1 ω ≤ x}))⟩

lemma distribution_error_bounded {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    BddAbove (range (fun x : ℝ => |empiricalDistribution X n ω x - commonDistribution P X x|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := commonDistribution_bounds P X x
  have h0 := empiricalDistribution_nonneg X n ω x
  have h1 := empiricalDistribution_le_one X n ω x
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma empiricalDistribution_rightContinuous {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) :
    ContinuousWithinAt (empiricalDistribution X n ω) (Ici x) x := by
  unfold empiricalDistribution
  apply ContinuousWithinAt.div_const
  apply tendsto_finsetSum
  intro k hk
  by_cases h : X k ω ≤ x
  · apply (continuousWithinAt_const (b := (1 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp [h.trans hy]
    · simp [h]
  · have hx : x < X k ω := lt_of_not_ge h
    apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hx)] with y hy
      simp [not_le.mpr (mem_Iio.mp hy)]
    · simp [h]

lemma commonDistribution_rightContinuous {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : Measurable (X 1)) (x : ℝ) :
    ContinuousWithinAt (commonDistribution P X) (Ici x) x := by
  rw [commonDistribution_eq_law P X hX]
  exact (Ch01.realDistributionFunction_properties (P.map (X 1))).2.1 x

lemma rightContinuous_ciSup_eq_rat (f : ℝ → ℝ)
    (hf : ∀ x, ContinuousWithinAt f (Ici x) x) (hb : BddAbove (range f)) :
    (⨆ x : ℝ, f x) = ⨆ q : ℚ, f q := by
  have hbq : BddAbove (range (fun q : ℚ => f q)) :=
    hb.mono (by rintro _ ⟨q, rfl⟩; exact ⟨q, rfl⟩)
  apply le_antisymm
  · apply ciSup_le
    intro x
    obtain ⟨q, _, hqx, hq⟩ := Real.exists_seq_rat_strictAnti_tendsto x
    have ht : Tendsto (fun n => f (q n)) atTop (𝓝 (f x)) :=
      (hf x).tendsto.comp (tendsto_nhdsWithin_iff.mpr
        ⟨hq, Eventually.of_forall (fun n => (hqx n).le)⟩)
    exact le_of_tendsto' ht (fun n => le_ciSup hbq (q n))
  · exact ciSup_le (fun q => le_ciSup hb (q : ℝ))

theorem distributionDeviation_eq_rational_sup {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1))) (n : ℕ) (ω : Ω) :
    distributionDeviation P X n ω =
      ⨆ q : ℚ, |empiricalDistribution X n ω (q : ℝ) - commonDistribution P X q| := by
  apply rightContinuous_ciSup_eq_rat
  · intro x
    exact ((empiricalDistribution_rightContinuous X n ω x).sub
      (commonDistribution_rightContinuous P X (hX 0) x)).abs
  · exact distribution_error_bounded P X n ω

lemma empiricalDistribution_measurable {Ω : Type u} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k : ℕ, Measurable (X (k + 1))) (n : ℕ) (x : ℝ) :
    Measurable (fun ω => empiricalDistribution X n ω x) := by
  unfold empiricalDistribution
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro k hk
  have hkpos : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkX : Measurable (X k) := by simpa [Nat.sub_add_cancel hkpos] using hX (k - 1)
  exact Measurable.ite (measurableSet_le hkX measurable_const) measurable_const measurable_const

theorem distributionDeviation_measurable {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1))) (n : ℕ) :
    Measurable (distributionDeviation P X n) := by
  simp_rw [funext (distributionDeviation_eq_rational_sup P X hX n)]
  exact Measurable.iSup (fun q : ℚ =>
    ((empiricalDistribution_measurable X hX n q).sub measurable_const).abs)

/-- The strict empirical distribution is needed at atoms of the common law. -/
noncomputable def empiricalStrictDistribution {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, if X k ω < x then (1 : ℝ) else 0) / (n : ℝ)

lemma empiricalDistribution_mono {Ω : Type u} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Monotone (empiricalDistribution X n ω) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : X k ω ≤ a
  · simp [h, h.trans hab]
  · simp only [ite_eq_right h]
    positivity

lemma empiricalDistribution_le_strict {Ω : Type u} (X : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) {a b : ℝ} (hab : a < b) :
    empiricalDistribution X n ω a ≤ empiricalStrictDistribution X n ω b := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply Finset.sum_le_sum
  intro k hk
  by_cases h : X k ω ≤ a
  · simp [h, h.trans_lt hab]
  · simp only [ite_eq_right h]
    positivity

/-- The generalized inverse is used only at levels strictly between zero and one. -/
noncomputable def cdfQuantile (F : ℝ → ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ F x}

lemma cdfQuantile_spec (F : ℝ → ℝ) (hF : Ch01.IsRealDistributionFunction F)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    (∀ x, cdfQuantile F u ≤ x ↔ u ≤ F x) ∧
      Function.leftLim F (cdfQuantile F u) ≤ u := by
  have hne : Set.Nonempty {x | u ≤ F x} := by
    obtain ⟨x, hx⟩ := ((tendsto_order.mp hF.2.2.2).1 u hu1).exists
    exact ⟨x, hx.le⟩
  have hb : BddBelow {x | u ≤ F x} := by
    obtain ⟨a, ha⟩ := ((tendsto_order.mp hF.2.2.1).2 u hu0).exists
    refine ⟨a, ?_⟩
    intro x hx
    by_contra h
    have hxa : x ≤ a := le_of_lt (lt_of_not_ge h)
    exact (not_le_of_gt ha) (hx.trans (hF.1 hxa))
  have hright : u ≤ F (cdfQuantile F u) := by
    apply ge_of_tendsto ((hF.2.1 (cdfQuantile F u)).mono Ioi_subset_Ici_self).tendsto
    filter_upwards [self_mem_nhdsWithin] with y hy
    obtain ⟨z, hz, hzy⟩ := exists_lt_of_csInf_lt hne (mem_Ioi.mp hy)
    exact hz.trans (hF.1 hzy.le)
  have heq (x : ℝ) : cdfQuantile F u ≤ x ↔ u ≤ F x :=
    ⟨fun hx => hright.trans (hF.1 hx), fun hx => csInf_le hb hx⟩
  refine ⟨heq, ?_⟩
  apply le_of_tendsto (hF.1.tendsto_leftLim (cdfQuantile F u))
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (lt_of_not_ge (fun h => (not_le.mpr (mem_Iio.mp hy)) ((heq y).mpr h))).le

/-- A deterministic bracketing theorem. No continuity of the limit beyond
right continuity is used; the strict upper brackets retain its jumps. -/
lemma uniform_convergence_of_quantile_convergence
    (F : ℝ → ℝ) (hF : Ch01.IsRealDistributionFunction F)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (G H : ℕ → ℝ → ℝ)
    (hG0 : ∀ n x, 0 ≤ G n x) (hG1 : ∀ n x, G n x ≤ 1)
    (hGmono : ∀ n, Monotone (G n))
    (hGH : ∀ n a b, a < b → G n a ≤ H n b)
    (hconv : ∀ m j : ℕ, 0 < j → j < m →
      Tendsto (fun n => G n (cdfQuantile F ((j : ℝ) / m))) atTop
        (𝓝 (F (cdfQuantile F ((j : ℝ) / m)))) ∧
      Tendsto (fun n => H n (cdfQuantile F ((j : ℝ) / m))) atTop
        (𝓝 (Function.leftLim F (cdfQuantile F ((j : ℝ) / m))))) :
    Tendsto (fun n => ⨆ x : ℝ, |G n x - F x|) atTop (𝓝 0) := by
  have hb (n : ℕ) : BddAbove (range (fun x => |G n x - F x|)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact abs_le.mpr ⟨by linarith [hG0 n x, (hFb x).2],
      by linarith [hG1 n x, (hFb x).1]⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_gt (max (3 / ε) 1)
  have hm1 : 1 < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hm0 : 0 < (m : ℝ) := by linarith
  have hm2 : 2 ≤ m := by exact_mod_cast hm1
  have hstep : 1 / (m : ℝ) < ε / 3 := by
    have hmε : 3 / ε < (m : ℝ) := (le_max_left _ _).trans_lt hm
    have hprod := (div_lt_iff₀ hε).mp hmε
    apply (div_lt_iff₀ hm0).mpr
    nlinarith
  have he : 0 < ε / 3 := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.Ico 1 m,
      |G n (cdfQuantile F ((j : ℝ) / m)) - F (cdfQuantile F ((j : ℝ) / m))| < ε / 3 ∧
      |H n (cdfQuantile F ((j : ℝ) / m)) -
        Function.leftLim F (cdfQuantile F ((j : ℝ) / m))| < ε / 3 := by
    apply (Finset.eventually_all _).mpr
    intro j hj
    have hj' := Finset.mem_Ico.mp hj
    have hc := hconv m j (by omega) hj'.2
    simpa only [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hc.1 (ε / 3) he).and
      (Metric.tendsto_nhds.mp hc.2 (ε / 3) he)
  filter_upwards [hev] with n hn
  have hbound (x : ℝ) : |G n x - F x| ≤ ε / 3 + 1 / (m : ℝ) := by
    let j := min ⌊(m : ℝ) * F x⌋₊ (m - 1)
    have hjm : j < m := by dsimp [j]; omega
    have hjfloor : j ≤ ⌊(m : ℝ) * F x⌋₊ := min_le_left _ _
    have hjlow : (j : ℝ) / m ≤ F x := by
      apply (div_le_iff₀ hm0).mpr
      exact (Nat.cast_le.mpr hjfloor).trans (by
        simpa [mul_comm] using Nat.floor_le (mul_nonneg hm0.le (hFb x).1))
    have hjhigh : j + 1 < m → F x < ((j + 1 : ℕ) : ℝ) / m := by
      intro hj
      have hjeq : j = ⌊(m : ℝ) * F x⌋₊ := by dsimp [j] at *; omega
      apply (lt_div_iff₀ hm0).mpr
      have hf := Nat.lt_floor_add_one ((m : ℝ) * F x)
      rw [← hjeq] at hf
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hf
    have hlower : (j : ℝ) / m - ε / 3 ≤ G n x := by
      by_cases hj0 : j = 0
      · simpa [hj0] using (sub_nonpos.mpr he.le).trans (hG0 n x)
      · have hju0 : 0 < (j : ℝ) / m := div_pos (by exact_mod_cast Nat.pos_of_ne_zero hj0) hm0
        have hju1 : (j : ℝ) / m < 1 := (div_lt_one hm0).mpr (by exact_mod_cast hjm)
        have hq := cdfQuantile_spec F hF ((j : ℝ) / m) hju0 hju1
        have hqx := (hq.1 x).mpr hjlow
        have hqF := (hq.1 (cdfQuantile F ((j : ℝ) / m))).mp le_rfl
        have herr := (abs_lt.mp (hn j (Finset.mem_Ico.mpr ⟨by omega, hjm⟩)).1).1
        have hg := hGmono n hqx
        linarith
    have hupper : G n x ≤ ((j + 1 : ℕ) : ℝ) / m + ε / 3 := by
      by_cases hj : j + 1 < m
      · have hju0 : 0 < ((j + 1 : ℕ) : ℝ) / m := div_pos (by positivity) hm0
        have hju1 : ((j + 1 : ℕ) : ℝ) / m < 1 :=
          (div_lt_one hm0).mpr (by exact_mod_cast hj)
        have hq := cdfQuantile_spec F hF (((j + 1 : ℕ) : ℝ) / m) hju0 hju1
        have hxq : x < cdfQuantile F (((j + 1 : ℕ) : ℝ) / m) := by
          apply lt_of_not_ge
          intro h
          exact (not_le_of_gt (hjhigh hj)) ((hq.1 x).mp h)
        have hg := hGH n x _ hxq
        have herr := (abs_lt.mp (hn (j + 1)
          (Finset.mem_Ico.mpr ⟨by omega, hj⟩)).2).2
        linarith [hq.2]
      · have hjeq : j + 1 = m := by omega
        rw [hjeq, div_self hm0.ne']
        linarith [hG1 n x]
    have hFxupper : F x ≤ ((j + 1 : ℕ) : ℝ) / m := by
      by_cases hj : j + 1 < m
      · exact (hjhigh hj).le
      · have hjeq : j + 1 = m := by omega
        simpa [hjeq, hm0.ne'] using (hFb x).2
    have hgrid : ((j + 1 : ℕ) : ℝ) / m = (j : ℝ) / m + 1 / (m : ℝ) := by
      push_cast
      rw [add_div]
    rw [hgrid] at hupper hFxupper
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hsup : (⨆ x : ℝ, |G n x - F x|) ≤ ε / 3 + 1 / (m : ℝ) := ciSup_le hbound
  have hnonneg : 0 ≤ ⨆ x : ℝ, |G n x - F x| :=
    (abs_nonneg _).trans (le_ciSup (hb n) (0 : ℝ))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith

/-- The strong law applied to a Borel event of each observation. -/
lemma empirical_event_strongLaw {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (hindep : Ch02.IndependentRandomElements P (fun k : ℕ => X (k + 1)))
    (hident : ∀ k : ℕ, IdentDistrib (X (k + 1)) (X 1) P P)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, if X k ω ∈ s then (1 : ℝ) else 0) / (n : ℝ))
      atTop (𝓝 ((P (X 1 ⁻¹' s)).toReal)) := by
  classical
  let g : ℝ → ℝ := fun x => if x ∈ s then 1 else 0
  let Y : ℕ → Ω → ℝ := fun k ω => g (X k ω)
  have hg : Measurable g := Measurable.ite hs measurable_const measurable_const
  have hY : ∀ k : ℕ, Measurable (Y (k + 1)) := fun k => hg.comp (hX k)
  have hi := (Ch02.independentRandomElements_iff_iIndepFun P _).mp hindep
  have hYi : Ch02.PairwiseIndependentRandomElements P (fun k : ℕ => Y (k + 1)) := by
    apply (Ch02.pairwiseIndependentRandomElements_iff P _).mpr
    intro i j hij
    exact (hi.indepFun hij).comp hg hg
  have hYident : ∀ k : ℕ, IdentDistrib (Y (k + 1)) (Y 1) P P :=
    fun k => (hident k).comp hg
  have hYeq : Y 1 = (X 1 ⁻¹' s).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : X 1 ω ∈ s <;> simp [Y, g, h, Set.indicator]
  have hmoment : Integrable (fun ω => |Y 1 ω|) P := by
    apply Integrable.abs
    rw [hYeq]
    exact (integrable_const (1 : ℝ)).indicator (hs.preimage (hX 0))
  have hexpect : (∫ ω, Y 1 ω ∂P) = (P (X 1 ⁻¹' s)).toReal := by
    rw [hYeq]
    simpa only [measureReal_def, Pi.one_def, Nat.zero_add] using
      (integral_indicator_one (μ := P) (hs.preimage (hX 0)))
  simpa only [Y, g, hexpect] using etemadi_strong_law P Y hY hYi hYident hmoment

/-- Both sides of every possible jump are controlled by the strong law. -/
lemma empirical_distributions_pointwise {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (hindep : Ch02.IndependentRandomElements P (fun k : ℕ => X (k + 1)))
    (hident : ∀ k : ℕ, IdentDistrib (X (k + 1)) (X 1) P P) (x : ℝ) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => empiricalDistribution X n ω x) atTop (𝓝 (commonDistribution P X x)) ∧
      Tendsto (fun n => empiricalStrictDistribution X n ω x) atTop
        (𝓝 ((P {ω | X 1 ω < x}).toReal)) := by
  simpa only [empiricalDistribution, empiricalStrictDistribution, commonDistribution, mem_Iic,
    mem_Iio, Set.preimage] using
    (empirical_event_strongLaw P X hX hindep hident (Iic x) measurableSet_Iic).and
    (empirical_event_strongLaw P X hX hindep hident (Iio x) measurableSet_Iio)

/-- Glivenko--Cantelli for arbitrary common real laws, including laws with atoms. -/
theorem glivenko_cantelli {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k : ℕ, Measurable (X (k + 1)))
    (hindep : Ch02.IndependentRandomElements P (fun k : ℕ => X (k + 1)))
    (hident : ∀ k : ℕ, IdentDistrib (X (k + 1)) (X 1) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => distributionDeviation P X n ω) atTop (𝓝 0) := by
  let F := commonDistribution P X
  have hF : Ch01.IsRealDistributionFunction F := by
    dsimp [F]
    rw [commonDistribution_eq_law P X (hX 0)]
    exact Ch01.realDistributionFunction_properties (P.map (X 1))
  have hleft (x : ℝ) : (P {ω | X 1 ω < x}).toReal = Function.leftLim F x := by
    have h := (Ch01.realDistributionFunction_leftLimit (P.map (X 1)) x).2
    rw [Measure.map_apply (hX 0) measurableSet_Iio] at h
    rw [show F = Ch01.realDistributionFunction (P.map (X 1)) from
      commonDistribution_eq_law P X (hX 0)]
    exact h
  have ha : ∀ m j : ℕ, ∀ᵐ ω ∂P,
      Tendsto (fun n => empiricalDistribution X n ω (cdfQuantile F ((j : ℝ) / m))) atTop
        (𝓝 (F (cdfQuantile F ((j : ℝ) / m)))) ∧
      Tendsto (fun n => empiricalStrictDistribution X n ω (cdfQuantile F ((j : ℝ) / m))) atTop
        (𝓝 (Function.leftLim F (cdfQuantile F ((j : ℝ) / m)))) := by
    intro m j
    simpa only [hleft] using
      empirical_distributions_pointwise P X hX hindep hident (cdfQuantile F ((j : ℝ) / m))
  have hall := (ae_all_iff.mpr (fun m => ae_all_iff.mpr (ha m)))
  filter_upwards [hall] with ω hω
  exact uniform_convergence_of_quantile_convergence F hF (commonDistribution_bounds P X)
    (fun n => empiricalDistribution X n ω) (fun n => empiricalStrictDistribution X n ω)
    (fun n x => empiricalDistribution_nonneg X n ω x)
    (fun n x => empiricalDistribution_le_one X n ω x)
    (fun n => empiricalDistribution_mono X n ω)
    (fun n _ _ hab => empiricalDistribution_le_strict X n ω hab)
    (fun m j _ _ => hω m j)

end ProbabilityFoundations.Ch08
