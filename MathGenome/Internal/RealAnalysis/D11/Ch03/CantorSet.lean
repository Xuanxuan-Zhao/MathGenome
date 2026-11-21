import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.CantorSet
import MathGenome.Internal.RealAnalysis.D11.Ch03.LebesgueMeasures
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Cardinal ENNReal

namespace D11.Ch03.CantorSet
open CantorConstruction

/-- The fixed middle-thirds Cantor set for subsequent chapters. -/
def C : Set ℝ := _root_.cantorSet

def stage : ℕ → Set ℝ := _root_.preCantorSet

theorem stage_zero : Specs.D11.Ch03.CantorSet.stage_zero := rfl

theorem stage_succ : Specs.D11.Ch03.CantorSet.stage_succ := fun _ => rfl

theorem stage_antitone : Specs.D11.Ch03.CantorSet.stage_antitone := preCantorSet_antitone

theorem C_eq_inter : Specs.D11.Ch03.CantorSet.C_eq_inter := rfl

theorem C_subset : Specs.D11.Ch03.CantorSet.C_subset := cantorSet_subset_unitInterval

/-- Taking a left or right third scales the whole component interval. -/
theorem interval_succ (n : ℕ) (w : Fin (n + 1) → Bool) :
    interval (n + 1) w =
      (fun x : ℝ => ((if w 0 then 2 else 0) + x) / 3) ''
        interval n (fun i => w i.succ) := by
  ext x
  simp only [interval, leftEndpoint, pow_succ, mem_Icc, mem_image]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨3 * x - (if w 0 then 2 else 0), ⟨?_, ?_⟩, ?_⟩ <;> linarith
  · rintro ⟨y, ⟨h₁, h₂⟩, rfl⟩
    constructor <;> linarith

theorem stage_intervals (n : ℕ) :
    preCantorSet n = ⋃ w : Fin n → Bool, interval n w := by
  induction n with
  | zero =>
    ext x
    simp [interval, leftEndpoint]
  | succ n ih =>
    rw [preCantorSet_succ, ih]
    ext x
    simp only [mem_union, mem_image, mem_iUnion]
    constructor
    · rintro (⟨y, ⟨w, hw⟩, rfl⟩ | ⟨y, ⟨w, hw⟩, rfl⟩)
      · refine ⟨Fin.cons false w, ?_⟩
        rw [interval_succ]
        exact ⟨y, hw, by simp⟩
      · refine ⟨Fin.cons true w, ?_⟩
        rw [interval_succ]
        exact ⟨y, hw, by simp⟩
    · rintro ⟨w, hw⟩
      rw [interval_succ] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      cases h : w 0
      · exact Or.inl ⟨y, ⟨_, hy⟩, by simp⟩
      · exact Or.inr ⟨y, ⟨_, hy⟩, by simp⟩

theorem stage_interval_count : Specs.D11.Ch03.CantorSet.stage_interval_count := by
  intro n
  simp

theorem stage_interval_length : Specs.D11.Ch03.CantorSet.stage_interval_length := by
  intro n w
  ring

theorem interval_subset_unit (n : ℕ) (w : Fin n → Bool) :
    interval n w ⊆ Icc 0 1 := by
  intro x hx
  apply preCantorSet_subset_unitInterval (n := n)
  rw [stage_intervals n]
  exact mem_iUnion.mpr ⟨w, hx⟩

theorem stage_disjoint : Specs.D11.Ch03.CantorSet.stage_disjoint := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    exact (hab (Subsingleton.elim a b)).elim
  | succ n ih =>
    intro a b hab
    by_cases hhead : a 0 = b 0
    · have htail : (fun i : Fin n => a i.succ) ≠ (fun i => b i.succ) := by
        intro heq
        apply hab
        funext i
        exact Fin.cases hhead (fun j => congrFun heq j) i
      rw [interval_succ, interval_succ, hhead]
      exact disjoint_image_of_injective (by intro x y h; linarith) (ih htail)
    · rw [interval_succ, interval_succ]
      apply disjoint_image_image
      intro y hy z hz heq
      have hy' := interval_subset_unit n (fun i => a i.succ) hy
      have hz' := interval_subset_unit n (fun i => b i.succ) hz
      cases ha : a 0 <;> cases hb : b 0 <;>
        simp only [ha, hb, Bool.false_eq_true, ite_false, ite_true] at heq hhead
      all_goals first | exact hhead trivial | linarith [hy'.1, hy'.2, hz'.1, hz'.2]

/-- The total length of the retained construction intervals tends to zero. -/
theorem stage_volume_bound (n : ℕ) :
    volume (preCantorSet n) ≤ ENNReal.ofReal (2 / 3 : ℝ) ^ n := by
  rw [stage_intervals n]
  calc
    volume (⋃ w : Fin n → Bool, interval n w) ≤ ∑ w : Fin n → Bool, volume (interval n w) :=
      measure_iUnion_fintype_le _ _
    _ = (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (1 / 3 : ℝ) ^ n := by
      simp [interval, Real.volume_Icc, nsmul_eq_mul, ENNReal.inv_pow]
    _ = ENNReal.ofReal (2 / 3 : ℝ) ^ n := by
      rw [← mul_pow]
      congr 1
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem C_volume_zero : Specs.D11.Ch03.CantorSet.C_volume_zero := by
  apply le_antisymm _ zero_le
  apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.ofReal_lt_one.mpr (by norm_num : (2 / 3 : ℝ) < 1)))
  exact Eventually.of_forall fun n =>
    (measure_mono (iInter_subset _ n)).trans (stage_volume_bound n)

theorem C_nowhere_dense : Specs.D11.Ch03.CantorSet.C_nowhere_dense :=
  IsNowhereDense.of_isClosed_null isClosed_cantorSet C_volume_zero

/-- The Euclidean line identification preserves the standard normalization. -/
theorem linePoint_volume_preserving : MeasurePreserving linePoint volume volume := by
  exact (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _)

theorem C_lebesgue_null : Specs.D11.Ch03.CantorSet.C_lebesgue_null := by
  have hC : MeasurableSet (linePoint '' _root_.cantorSet) := by
    apply IsCompact.measurableSet
    apply isCompact_cantorSet.image
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => continuous_id)
  have hnull : volume (linePoint '' _root_.cantorSet) = 0 := by
    rw [← linePoint_volume_preserving.measure_preimage hC.nullMeasurableSet]
    have hinj : Function.Injective linePoint := by
      intro x y h
      exact congrArg (fun p : Point 1 => p 0) h
    rw [preimage_image_eq _ hinj]
    exact C_volume_zero
  have hfull : MeasurableSet[LebesgueMeasures.lebesgueSpace 1]
      (linePoint '' _root_.cantorSet) := LebesgueMeasures.native_borel_le 1 _ hC
  refine ⟨hfull, ?_⟩
  exact (LebesgueMeasures.lebesgue_apply 1 _ hfull).trans
    ((LebesgueMeasures.native_outer_agreement 1 _).symm.trans hnull)

theorem C_compact : Specs.D11.Ch03.CantorSet.C_compact := isCompact_cantorSet

theorem C_borel : Specs.D11.Ch03.CantorSet.C_borel := isClosed_cantorSet.measurableSet

theorem C_cardinality : Specs.D11.Ch03.CantorSet.C_cardinality := by
  change Cardinal.mk _root_.cantorSet = 𝔠
  rw [Cardinal.mk_congr cantorSetEquivNatToBool, ← Cardinal.power_def,
    Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]

/-- Flipping successively more distant digits converges in the binary product. -/
theorem binary_flip_tendsto (s : ℕ → Bool) :
    Tendsto (fun n => Function.update s n (!(s n))) atTop (𝓝 s) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with n hn
  simp [Function.update_of_ne (ne_of_lt hn)]

theorem C_perfect : Specs.D11.Ch03.CantorSet.C_perfect := by
  refine ⟨isClosed_cantorSet, preperfect_iff_nhds.mpr ?_⟩
  intro x hx U hU
  let e := cantorSetHomeomorphNatToBool.symm
  let s := cantorSetHomeomorphNatToBool ⟨x, hx⟩
  let t := fun n => Function.update s n (!(s n))
  have ht : Tendsto (fun n => (e (t n) : ℝ)) atTop (𝓝 x) := by
    have := (continuous_subtype_val.comp e.continuous).continuousAt.tendsto.comp
      (binary_flip_tendsto s)
    simpa [e, s, t, Function.comp_def] using this
  obtain ⟨n, hn⟩ := (ht.eventually hU).exists
  refine ⟨e (t n), ⟨hn, (e (t n)).property⟩, ?_⟩
  intro heq
  have hs : t n = s := e.injective (by apply Subtype.ext; simpa [e, s] using heq)
  have hd := congrFun hs n
  simp [t] at hd

end D11.Ch03.CantorSet
