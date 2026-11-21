import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.NonconvexOscillations
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.Spaces
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Module.HahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14ReflexiveExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12BoundedSequences
import MathGenome.Internal.FourierSobolev.P102.U4.ACL
import MathGenome.Internal.FourierSobolev.P102.Trace.OrdinaryTrace
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology
namespace VariationalNotes.Sobolev.NonconvexOscillations

/-- Folding the unit interval identifies its endpoints continuously. -/
theorem continuous_tent (n : ℕ) : Continuous (tent n) := by
  have h : Continuous (fun t : ℝ => min t (1 - t)) :=
    continuous_id.min (continuous_const.sub continuous_id)
  have hf : Continuous (fun x : ℝ => min (Int.fract x) (1 - Int.fract x)) :=
    h.continuousOn.comp_fract'' (by norm_num)
  exact (hf.comp (continuous_const.mul continuous_id)).div_const _

/-- All grid endpoints have value zero, including the two boundary endpoints. -/
theorem tent_grid (n k : ℕ) : tent n ((k : ℝ) / n) = 0 := by
  by_cases hn : n = 0
  · simp [tent, hn]
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp [tent, mul_div_cancel₀ _ hn']

/-- The folded fractional part is bounded by distance to every integer. -/
theorem fold_le_dist_int (x : ℝ) (k : ℤ) :
    min (Int.fract x) (1 - Int.fract x) ≤ |x - k| := by
  by_cases h : k ≤ ⌊x⌋
  · have hk : (k : ℝ) ≤ ⌊x⌋ := by exact_mod_cast h
    have hx := Int.floor_le x
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left (Int.fract x) (1 - Int.fract x)).trans (by dsimp only [Int.fract]; linarith)
  · have hk : (⌊x⌋ : ℝ) + 1 ≤ k := by exact_mod_cast (show ⌊x⌋ + 1 ≤ k by omega)
    have hx := Int.lt_floor_add_one x
    rw [abs_of_nonpos (by linarith)]
    exact (min_le_right (Int.fract x) (1 - Int.fract x)).trans (by dsimp only [Int.fract]; linarith)

/-- One of the adjacent integers realizes the folded fractional part. -/
theorem exists_fold_eq_dist_int (x : ℝ) :
    ∃ k : ℤ, min (Int.fract x) (1 - Int.fract x) = |x - k| := by
  by_cases h : Int.fract x ≤ 1 - Int.fract x
  · refine ⟨⌊x⌋, ?_⟩
    rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le x))]
    rfl
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [min_eq_right (le_of_not_ge h), abs_of_nonpos (by
      push_cast; linarith [Int.lt_floor_add_one x])]
    simp only [Int.fract, Int.cast_add, Int.cast_one]
    ring

/-- Folding across integer endpoints retains Lipschitz constant one. -/
theorem lipschitz_fold :
    LipschitzWith 1 (fun x : ℝ => min (Int.fract x) (1 - Int.fract x)) := by
  have h (x y : ℝ) : min (Int.fract x) (1 - Int.fract x) ≤
      |x - y| + min (Int.fract y) (1 - Int.fract y) := by
    obtain ⟨k, hk⟩ := exists_fold_eq_dist_int y
    rw [hk]
    exact (fold_le_dist_int x k).trans (by
      simpa only [sub_add_sub_cancel] using abs_add_le (x - y) (y - k))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_sub_le_iff.mpr ⟨by linarith [h x y], by
    have hh := h y x
    rw [abs_sub_comm y x] at hh
    linarith⟩

/-- The source tents have a uniform Lipschitz constant. -/
theorem lipschitz_tent {n : ℕ} (hn : 0 < n) : LipschitzWith 1 (tent n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := lipschitz_fold.dist_le_mul ((n : ℝ) * x) ((n : ℝ) * y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h ⊢
  unfold tent
  rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  rw [← mul_sub, abs_mul, abs_of_pos hp] at h
  simpa only [mul_comm] using h

private def zeroTent (n : ℕ) (x : ℝ) : ℝ :=
  tent n (max 0 (min x 1))

private def zeroSlope (n : ℕ) (x : ℝ) : ℝ :=
  (Ioo (0 : ℝ) 1).indicator (tentSlope n) x

private theorem zeroTent_eq (n : ℕ) (x : ℝ) :
    zeroTent n x = (Ioo (0 : ℝ) 1).indicator (tent n) x := by
  have h0 : tent n 0 = 0 := by simpa using tent_grid n 0
  have h1 : tent n 1 = 0 := by
    by_cases hn : n = 0
    · simp [tent, hn]
    · simpa [Nat.cast_ne_zero.mpr hn] using tent_grid n n
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · simp [zeroTent, hx, min_eq_left hx.2.le, max_eq_right hx.1.le]
  · by_cases h : x ≤ 0
    · simp [zeroTent, hx, min_eq_left (h.trans zero_le_one), max_eq_left h, h0]
    · have h' : 1 ≤ x := by
        by_contra h'
        exact hx ⟨lt_of_not_ge h, lt_of_not_ge h'⟩
      simp [zeroTent, hx, min_eq_right h', h1]

private theorem lipschitz_zeroTent {n : ℕ} (hn : 0 < n) :
    LipschitzWith 1 (zeroTent n) := by
  change LipschitzWith 1 (fun x => tent n (max 0 (min x 1)))
  simpa only [one_mul, Function.comp_def, id_eq] using (lipschitz_tent hn).comp
    ((LipschitzWith.id.min_const 1).const_max 0)

/-- The height bound is global; in particular it is uniform on [0,1]. -/
theorem tent_bounds {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 ≤ tent n x ∧ tent n x ≤ 1 / (2 * (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h0 := Int.fract_nonneg ((n : ℝ) * x)
  have h1 := Int.fract_lt_one ((n : ℝ) * x)
  have hmin : min (Int.fract ((n : ℝ) * x)) (1 - Int.fract ((n : ℝ) * x)) ≤ 1 / 2 := by
    by_cases h : Int.fract ((n : ℝ) * x) ≤ 1 / 2
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans (by linarith)
  constructor
  · exact div_nonneg (le_min h0 (by linarith)) hn'.le
  · unfold tent
    calc
      _ ≤ (1 / 2 : ℝ) / n := div_le_div_of_nonneg_right hmin hn'.le
      _ = 1 / (2 * (n : ℝ)) := by ring

/-- On the rising half of a cell the fractional-part formula is affine. -/
theorem tent_rising {n : ℕ} (hn : 0 < n) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc ((k : ℝ) / n) (((k : ℝ) + 1 / 2) / n)) :
    tent n x = x - (k : ℝ) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlow : (k : ℝ) ≤ n * x := by simpa only [mul_comm] using (div_le_iff₀ hn').mp hx.1
  have hupp : (n : ℝ) * x ≤ k + 1 / 2 := by simpa only [mul_comm] using (le_div_iff₀ hn').mp hx.2
  have hfloor : Int.floor ((n : ℝ) * x) = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    push_cast
    constructor <;> linarith
  have hmin : (n : ℝ) * x - k ≤ 1 - ((n : ℝ) * x - k) := by linarith
  simp only [tent, Int.fract, hfloor, Int.cast_natCast, min_eq_left hmin]
  field_simp

/-- On the falling half the formula holds also at the right cell endpoint. -/
theorem tent_falling {n : ℕ} (hn : 0 < n) (k : ℕ) {x : ℝ}
    (hx : x ∈ Icc (((k : ℝ) + 1 / 2) / n) (((k : ℝ) + 1) / n)) :
    tent n x = ((k : ℝ) + 1) / n - x := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hlow : (k : ℝ) + 1 / 2 ≤ n * x := by simpa only [mul_comm] using (div_le_iff₀ hn').mp hx.1
  have hupp : (n : ℝ) * x ≤ k + 1 := by simpa only [mul_comm] using (le_div_iff₀ hn').mp hx.2
  by_cases heq : x = ((k : ℝ) + 1) / n
  · subst x
    have hgrid := tent_grid n (k + 1)
    simpa only [Nat.cast_add, Nat.cast_one, sub_self] using hgrid
  · have hlt : (n : ℝ) * x < k + 1 := by
      apply lt_of_le_of_ne hupp
      intro h
      apply heq
      exact (eq_div_iff hn'.ne').mpr (by linarith)
    have hfloor : Int.floor ((n : ℝ) * x) = (k : ℤ) := by
      apply Int.floor_eq_iff.mpr
      push_cast
      constructor <;> linarith
    have hmin : 1 - ((n : ℝ) * x - k) ≤ (n : ℝ) * x - k := by linarith
    simp only [tent, Int.fract, hfloor, Int.cast_natCast, min_eq_right hmin]
    field_simp
    ring

/-- Away from the grid and the tips the derivative is the prescribed sign. -/
theorem hasDerivAt_tent {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : (n : ℝ) * x ≠ (⌊(n : ℝ) * x⌋ : ℤ))
    (hh : Int.fract ((n : ℝ) * x) ≠ 1 / 2) :
    HasDerivAt (tent n) (tentSlope n x) x := by
  have hp : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hf : ∀ᶠ y in 𝓝 x, ⌊(n : ℝ) * y⌋ = ⌊(n : ℝ) * x⌋ := by
    have hc : ContinuousAt (fun y : ℝ => (n : ℝ) * y) x := by fun_prop
    filter_upwards [hc.eventually (Ioo_mem_nhds
      ((Int.floor_le _).lt_of_ne hx.symm) (Int.lt_floor_add_one _))] with y hy
    exact Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
  have hc : ContinuousAt (fun y : ℝ => Int.fract ((n : ℝ) * y)) x :=
    (continuousAt_fract hx).comp (by fun_prop)
  by_cases h : Int.fract ((n : ℝ) * x) < 1 / 2
  · have he : tent n =ᶠ[𝓝 x] fun y => ((n : ℝ) * y - ⌊(n : ℝ) * x⌋) / n := by
      filter_upwards [hf, hc.eventually (gt_mem_nhds h)] with y hy hz
      have hm : Int.fract ((n : ℝ) * y) ≤ 1 - Int.fract ((n : ℝ) * y) := by linarith
      unfold tent
      rw [min_eq_left hm]
      simp only [Int.fract, hy]
    have hd := (((hasDerivAt_id x).const_mul (n : ℝ)).sub_const
      (⌊(n : ℝ) * x⌋ : ℝ)).div_const (n : ℝ)
    rw [tentSlope, if_pos h]
    simpa only [mul_one, div_self hp] using hd.congr_of_eventuallyEq he
  · have hgt : 1 / 2 < Int.fract ((n : ℝ) * x) := lt_of_le_of_ne (le_of_not_gt h) hh.symm
    have he : tent n =ᶠ[𝓝 x] fun y => (1 - ((n : ℝ) * y - ⌊(n : ℝ) * x⌋)) / n := by
      filter_upwards [hf, hc.eventually (lt_mem_nhds hgt)] with y hy hz
      have hm : 1 - Int.fract ((n : ℝ) * y) ≤ Int.fract ((n : ℝ) * y) := by linarith
      unfold tent
      rw [min_eq_right hm]
      simp only [Int.fract, hy]
    have hd := ((((hasDerivAt_id x).const_mul (n : ℝ)).sub_const
      (⌊(n : ℝ) * x⌋ : ℝ)).const_sub 1).div_const (n : ℝ)
    rw [tentSlope, if_neg h]
    simpa only [mul_one, neg_div, div_self hp] using hd.congr_of_eventuallyEq he

/-- The excluded corners form a countable set, so have Lebesgue measure zero. -/
theorem ae_hasDerivAt_tent {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x : ℝ, HasDerivAt (tent n) (tentSlope n x) x := by
  have hp : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  filter_upwards [(Set.countable_range (fun k : ℤ => (k : ℝ) / (2 * n))).ae_notMem volume]
    with x hx
  apply hasDerivAt_tent hn
  · intro he
    apply hx
    refine ⟨2 * ⌊(n : ℝ) * x⌋, ?_⟩
    push_cast
    field_simp
    nlinarith
  · intro he
    apply hx
    refine ⟨2 * ⌊(n : ℝ) * x⌋ + 1, ?_⟩
    dsimp only [Int.fract] at he
    push_cast
    field_simp
    nlinarith

private theorem ae_hasDerivAt_zeroTent {n : ℕ} (hn : 0 < n) :
    ∀ᵐ x : ℝ, HasDerivAt (zeroTent n) (zeroSlope n x) x := by
  filter_upwards [ae_hasDerivAt_tent hn, volume.ae_ne (0 : ℝ), volume.ae_ne (1 : ℝ)] with x hd h0 h1
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [zeroSlope, Set.indicator_of_mem hx]
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [zeroTent_eq, Set.indicator_of_mem hy]
  · rw [zeroSlope, Set.indicator_of_notMem hx]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    have hs : x ∈ (Icc (0 : ℝ) 1)ᶜ := by
      intro h
      exact hx ⟨lt_of_le_of_ne h.1 (Ne.symm h0), lt_of_le_of_ne h.2 h1⟩
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hs] with y hy
    rw [zeroTent_eq, Set.indicator_of_notMem (fun h => hy ⟨h.1.le, h.2.le⟩)]

/-- The explicit tent tends uniformly to zero. -/
theorem tent_uniform :
    TendstoUniformlyOn (fun n => tent (n + 1)) (fun _ => 0) atTop (Icc 0 1) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    convert h.div_const 2 using 1
    · ext n
      push_cast
      field_simp
    · simp
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x _hx
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (tent_bounds (Nat.succ_pos n) x).1]
  exact (tent_bounds (Nat.succ_pos n) x).2.trans_lt hn

theorem geometry : Expected.Geometry := by
  intro n hn
  exact ⟨continuous_tent n, fun k _ => tent_grid n k,
    fun k _ => ⟨fun _ hx => tent_rising hn k hx, fun _ hx => tent_falling hn k hx⟩⟩

theorem uniform_convergence : Expected.UniformConvergence :=
  ⟨fun _ hn x => tent_bounds hn x, tent_uniform⟩


/-- The canonical one-dimensional Euclidean domain has interval volume one. -/
theorem volume_interval : volume (interval : Set (Domain 1)) = 1 := by
  have hpre : (WithLp.toLp 2 : (Fin 1 → ℝ) → Domain 1) ⁻¹' (interval : Set (Domain 1)) =
      Set.univ.pi (fun _ : Fin 1 => Ioo (0 : ℝ) 1) := by
    ext x
    simp only [interval, Set.mem_preimage,
      Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa [hi] using hx
    · intro hx
      exact hx 0
  rw [← (PiLp.volume_preserving_toLp (Fin 1)).measure_preimage
    interval.isOpen.measurableSet.nullMeasurableSet, hpre, volume_pi_pi]
  simp

theorem measure_interval_univ : domainMeasure interval Set.univ = 1 := by
  rw [Measure.restrict_apply_univ, volume_interval]

instance interval_finiteMeasure : IsFiniteMeasure (domainMeasure interval) :=
  ⟨by rw [measure_interval_univ]; exact ENNReal.one_lt_top⟩

/-- Euclidean one-coordinate injection preserves the scalar norm. -/
theorem norm_tentField {n : ℕ} (hn : 0 < n) (x : Domain 1) :
    ‖tentField n x‖ = tent n (x 0) := by
  simp [tentField, EuclideanSpace.single, PiLp.norm_single,
    Real.norm_eq_abs, abs_of_nonneg (tent_bounds hn (x 0)).1]

theorem norm_slopeField (n : ℕ) (x : Domain 1) : ‖slopeField n x‖ = 1 := by
  simp only [slopeField, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
  unfold tentSlope
  split_ifs <;> norm_num

/-- Pointwise continuity gives measurable representatives for every value field. -/
theorem continuous_tentField (n : ℕ) : Continuous (tentField n) := by
  have hc := ((continuous_tent n).comp (EuclideanSpace.proj (0 : Fin 1)).continuous).smul
    (continuous_const (y := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)))
  convert hc using 1
  ext x i
  simp [tentField]

theorem measurable_slopeField (n : ℕ) : Measurable (slopeField n) := by
  have hc : Measurable (fun x : Domain 1 => tentSlope n (x 0)) := by
    unfold tentSlope
    exact measurable_const.ite
      (measurableSet_lt
        ((measurable_const.mul (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable).fract)
        measurable_const) measurable_const
  have hm := hc.smul (measurable_const (a := EuclideanSpace.single ((0, 0) : Fin 1 × Fin 1) (1 : ℝ)))
  have he : slopeField n = fun x : Domain 1 => tentSlope n (x 0) •
      EuclideanSpace.single ((0, 0) : Fin 1 × Fin 1) (1 : ℝ) := by
    ext x i
    simp [slopeField]
  rw [he]
  exact hm

theorem tentField_memLp {n : ℕ} (hn : 0 < n) :
    MemLp (tentField n) four.ennreal (domainMeasure interval) := by
  apply MemLp.of_bound (continuous_tentField n).aestronglyMeasurable
    (1 / (2 * (n : ℝ)))
  exact Eventually.of_forall fun x => by rw [norm_tentField hn]; exact (tent_bounds hn _).2

theorem slopeField_memLp (n : ℕ) :
    MemLp (slopeField n) four.ennreal (domainMeasure interval) := by
  apply MemLp.of_bound (measurable_slopeField n).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => (norm_slopeField n x).le

/-- The zero extension is an actual whole-space Sobolev class, with its
classical a.e. derivative. The ACL converse supplies the distribution identity. -/
private theorem whole_realization {n : ℕ} (hn : 0 < n) :
    ∃ w : P102.U4.Sobolev ℝ (⊤ : Opens (Domain 1)) 1 four.ennreal,
      (P102.U4.sobolevUnderlying w : Domain 1 → ℝ) =ᵐ[volume]
        (fun x => zeroTent n (x 0)) ∧
      (P102.U4.firstWeakDerivative w 0 : Domain 1 → ℝ) =ᵐ[volume]
        (fun x => zeroSlope n (x 0)) := by
  classical
  have htv : MemLp (fun x : Domain 1 => tent n (x 0)) four.ennreal
      (domainMeasure interval) := by
    simpa [tentField, EuclideanSpace.single] using
      (tentField_memLp hn).continuousLinearMap_comp (EuclideanSpace.proj (0 : Fin 1) : Vector 1 →L[ℝ] ℝ)
  have htg : MemLp (fun x : Domain 1 => tentSlope n (x 0)) four.ennreal
      (domainMeasure interval) := by
    simpa [slopeField, EuclideanSpace.single] using
      (slopeField_memLp n).continuousLinearMap_comp
        (EuclideanSpace.proj ((0, 0) : Fin 1 × Fin 1) : Gradient 1 1 →L[ℝ] ℝ)
  have hfv : MemLp (fun x : Domain 1 => zeroTent n (x 0)) four.ennreal volume := by
    have h := (memLp_indicator_iff_restrict interval.isOpen.measurableSet.nullMeasurableSet).mpr htv
    convert h using 1
    ext x
    simp [zeroTent_eq, Set.indicator_apply, interval]
  have hfg : MemLp (fun x : Domain 1 => zeroSlope n (x 0)) four.ennreal volume := by
    have h := (memLp_indicator_iff_restrict interval.isOpen.measurableSet.nullMeasurableSet).mpr htg
    convert h using 1
    ext x
    simp [zeroSlope, Set.indicator_apply, interval]
  let U0 : P102.U4.DomainLp ℝ (⊤ : Opens (Domain 1)) four.ennreal :=
    (show MemLp (fun x : Domain 1 => zeroTent n (x 0)) four.ennreal
      (domainMeasure (⊤ : Opens (Domain 1))) by simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using hfv).toLp _
  let U1 : P102.U4.DomainLp ℝ (⊤ : Opens (Domain 1)) four.ennreal :=
    (show MemLp (fun x : Domain 1 => zeroSlope n (x 0)) four.ennreal
      (domainMeasure (⊤ : Opens (Domain 1))) by simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using hfg).toLp _
  have hU0 : (U0 : Domain 1 → ℝ) =ᵐ[volume] fun x => zeroTent n (x 0) := by
    simpa [U0] using (show (U0 : Domain 1 → ℝ) =ᵐ[domainMeasure (⊤ : Opens (Domain 1))]
      fun x => zeroTent n (x 0) from MemLp.coeFn_toLp _)
  have hU1 : (U1 : Domain 1 → ℝ) =ᵐ[volume] fun x => zeroSlope n (x 0) := by
    simpa [U1] using (show (U1 : Domain 1 → ℝ) =ᵐ[domainMeasure (⊤ : Opens (Domain 1))]
      fun x => zeroSlope n (x 0) from MemLp.coeFn_toLp _)
  have hd : P102.U4.distributionPartial {(0 : Fin 1)}
      (P102.U4.regularDistribution (⊤ : Opens (Domain 1)) U0) =
      P102.U4.regularDistribution (⊤ : Opens (Domain 1)) U1 := by
    apply (P102.U4.acl_dimensionOne ℝ (⊤ : Opens (Domain 1)) U0 U1
      (P102.U4.domainLp_locallyIntegrable ⊤ four.ennreal _)
      (P102.U4.domainLp_locallyIntegrable ⊤ four.ennreal _)).mpr
    refine ⟨fun x => zeroTent n (x 0), ?_, ?_, ?_⟩
    · simpa using hU0
    · change P102.U4.ACL.LocallyAC (zeroTent n) Set.univ
      intro a b _
      exact (lipschitz_zeroTent hn).lipschitzOnWith.absolutelyContinuousOnInterval
    · have hline := P102.Trace.Ordinary.ae_linePoint hU1
      have hder := ae_hasDerivAt_zeroTent hn
      simp only [P102.U4.ACL.fiber, Opens.coe_top, preimage_univ, Measure.restrict_univ]
      filter_upwards [hline, hder] with t ht hdt
      rw [P102.Trace.Ordinary.acl_line_one_eq, ht]
      exact hdt
  have hderivs : P102.U4.HasSobolevDerivatives (⊤ : Opens (Domain 1)) 1 four.ennreal U0 := by
    intro α hα
    by_cases ha : α = 0
    · subst α
      exact ⟨U0, P102.U4.derivative_zero 1 ℝ ⊤ _⟩
    · have hc : α.card = 1 := by
        have hh := Multiset.card_eq_zero.not.mpr ha
        omega
      obtain ⟨j, rfl⟩ := Multiset.card_eq_one.mp hc
      have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      exact ⟨U1, hd⟩
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range (⊤ : Opens (Domain 1))
    1 four.ennreal) U0).mpr hderivs
  have hgrad : U1 = P102.U4.firstWeakDerivative w 0 :=
    P102.U4.sobolev_derivative_unique ⊤ 1 four.ennreal w ⟨{0}, by simp⟩ U1 (by rw [hw]; exact hd)
  exact ⟨w, by simpa only [hw] using hU0, by simpa only [← hgrad] using hU1⟩

/-- Each tent belongs to the prescribed zero-boundary Sobolev space. -/
theorem realization : Expected.Realization := by
  intro n hn
  obtain ⟨w, hwv, hwg⟩ := whole_realization hn
  let r := P102.U4.sobolevRestrict interval w
  have hz : r ∈ P102.U4.sobolevZeroSubmodule ℝ interval 1 four.ennreal := by
    apply P102.Trace.Ordinary.restrict_mem_sobolevZero_of_supported_interval
      (by norm_num [four, Exponent.ennreal]) (show (0 : ℝ) < 1 by norm_num)
      (by rintro _ ⟨t, ht, rfl⟩; exact ht)
    filter_upwards [hwv] with x hx hnot
    rw [hx, zeroTent_eq, Set.indicator_of_notMem (fun h => hnot ⟨h.1.le, h.2.le⟩)]
  let u : W1p interval 1 four := (coordinateEquiv interval four).symm (fun _ : Fin 1 => r)
  have hcoord (i : Fin 1) : coordinateEquiv interval four u i = r := by
    simp only [u, ContinuousLinearEquiv.apply_symm_apply]
  have huv : coordinateLp interval four 0 (value interval 1 four u) =
      P102.U4.sobolevUnderlying r := by
    rw [← toCoordinates_value, ← coordinateEquiv_apply, hcoord]
  have hug : coordinateLp interval four (0, 0) (gradient interval 1 four u) =
      P102.U4.firstWeakDerivative r 0 := by
    rw [← toCoordinates_derivative, ← coordinateEquiv_apply, hcoord]
    rfl
  have hrv : (P102.U4.sobolevUnderlying r : Domain 1 → ℝ) =ᵐ[domainMeasure interval]
      fun x => tent n (x 0) := by
    have hres := (P102.U4.domainLpRestrict_ae interval (P102.U4.sobolevUnderlying w)).trans
      (ae_restrict_of_ae hwv)
    filter_upwards [hres, ae_restrict_mem interval.isOpen.measurableSet] with x hx hxi
    change P102.U4.domainLpRestrict interval (P102.U4.sobolevUnderlying w) x = _
    rw [hx, zeroTent_eq, Set.indicator_of_mem (show x 0 ∈ Ioo (0 : ℝ) 1 from hxi)]
  have hrg : (P102.U4.firstWeakDerivative r 0 : Domain 1 → ℝ) =ᵐ[domainMeasure interval]
      fun x => tentSlope n (x 0) := by
    have hres := (P102.U4.domainLpRestrict_ae interval (P102.U4.firstWeakDerivative w 0)).trans
      (ae_restrict_of_ae hwg)
    filter_upwards [hres, ae_restrict_mem interval.isOpen.measurableSet] with x hx hxi
    change P102.U4.domainLpRestrict interval (P102.U4.firstWeakDerivative w 0) x = _
    rw [hx, zeroSlope, Set.indicator_of_mem (show x 0 ∈ Ioo (0 : ℝ) 1 from hxi)]
  refine ⟨u, ⟨?_, ?_⟩, (zero_mem_iff_coordinates interval four u).mpr (fun i => ?_)⟩
  · filter_upwards [coordinateLp_ae interval four 0 (value interval 1 four u), hrv]
      with x hx hy
    apply PiLp.ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [← hx, huv, hy]
    simp [tentField]
  · filter_upwards [coordinateLp_ae interval four (0, 0) (gradient interval 1 four u), hrg]
      with x hx hy
    apply PiLp.ext
    intro i
    have hi : i = (0, 0) := Subsingleton.elim _ _
    subst i
    rw [← hx, hug, hy]
    simp [slopeField]
  · rw [hcoord]
    exact hz

/-- Any realization of these tents has values converging strongly in L4. -/
theorem values_tendsto_zero (u : ℕ → W1p interval 1 four)
    (hu : ∀ n, RepresentsTent (n + 1) (u n)) :
    Tendsto (fun n => value interval 1 four (u n)) atTop (𝓝 0) := by
  have hbound (n : ℕ) : ‖value interval 1 four (u n)‖ ≤ 1 / (2 * ((n + 1 : ℕ) : ℝ)) := by
    have h := Lp.norm_le_of_ae_bound
      (f := value interval 1 four (u n)) (C := 1 / (2 * ((n + 1 : ℕ) : ℝ))) (by positivity)
      (by filter_upwards [(hu n).1] with x hx
          rw [hx, norm_tentField (Nat.succ_pos n)]
          exact (tent_bounds (Nat.succ_pos n) _).2)
    simpa [measureUnivNNReal, Measure.restrict_apply_univ, volume_interval] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  convert h.div_const 2 using 1
  · ext n
    push_cast
    field_simp
  · simp

/-- Distributional convergence and boundedness identify every weak cluster
point of the gradients. Reflexive subsequence compactness then gives convergence
against the full continuous dual, without a restriction on the test function. -/
theorem gradient_convergence : Expected.GradientConvergence := by
  intro u hu
  let E := P102.U4.DomainLp ℝ interval four.ennreal
  let g : ℕ → E := fun n => coordinateLp interval four (0, 0)
    (gradient interval 1 four (u n))
  have hb (n : ℕ) : ‖g n‖ ≤ 1 := by
    have h := Lp.norm_le_of_ae_bound (f := g n) (C := 1) (by norm_num) (by
      filter_upwards [coordinateLp_ae interval four (0, 0)
        (gradient interval 1 four (u n)), (hu n).2] with x hx hy
      change ‖coordinateLp interval four (0, 0) (gradient interval 1 four (u n)) x‖ ≤ 1
      rw [hx, hy]
      simp only [slopeField, EuclideanSpace.single, WithLp.ofLp_toLp, Pi.single_eq_same]
      unfold tentSlope
      split_ifs <;> norm_num)
    simpa [measureUnivNNReal, Measure.restrict_apply_univ, volume_interval] using h
  have href : ExpandedFA.P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ E :=
    ExpandedFA.P1.C14ReflexiveExamples.measure_lp_reflexive ℝ (Domain 1)
      (domainMeasure interval) 4 (by norm_num)
  have hv := values_tendsto_zero u hu
  have htest (φ : P102.U4.TestSpace ℝ interval) (n : ℕ) :
      P102.U4.lpTestPairing interval four.ennreal φ (g n) =
      -P102.U4.lpTestPairing interval four.ennreal
        (P102.U4.testPartialWord interval [0] φ)
        (coordinateLp interval four 0 (value interval 1 four (u n))) := by
    have h := (P102.U4.distributionPartial_eq_regularLp_iff interval four.ennreal
      {(0 : Fin 1)} _ _).mp (distribution_derivative interval four (u n) 0 0) φ
    simpa [g] using h
  intro ℓ
  let S : E →L[ℝ] GradientLp interval 1 four :=
    (assembleLp interval four).comp
      (ContinuousLinearMap.pi fun _ : Fin 1 × Fin 1 => ContinuousLinearMap.id ℝ E)
  have hS (n : ℕ) : S (g n) = gradient interval 1 four (u n) := by
    apply coordinateLp_ext interval four
    intro i
    have hi : i = (0, 0) := Subsingleton.elim _ _
    subst i
    exact coordinate_assemble interval four (0, 0) _
  let L : E →L[ℝ] ℝ := ℓ.comp S
  have hL : Tendsto (fun n => L (g n)) atTop (𝓝 0) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    have hbounded : Bornology.IsBounded (Set.range (g ∘ ns)) := by
      apply isBounded_iff_forall_norm_le.mpr
      exact ⟨1, by rintro _ ⟨n, rfl⟩; exact hb _⟩
    obtain ⟨k, hk, w, hw⟩ :=
      ExpandedFA.P1.C14WeakSubsequence.reflexive_weak_subsequence ℝ E href (g ∘ ns) hbounded
    have hw0 : w = 0 := by
      apply P102.U4.regularLp_injective interval four.ennreal
      ext φ
      rw [P102.U4.regularLp_pairing interval four.ennreal,
        P102.U4.regularLp_pairing interval four.ennreal, map_zero]
      have ht := ExpandedFA.P1.C12BoundedSequences.weak_evaluation_tendsto ℝ E
        ((g ∘ ns) ∘ k) w hw (P102.U4.lpTestPairing interval four.ennreal φ)
      let A : ValueLp interval 1 four →L[ℝ] ℝ :=
        -(P102.U4.lpTestPairing interval four.ennreal
          (P102.U4.testPartialWord interval [0] φ)).comp (coordinateLp interval four 0)
      have ht0 := ((A.continuous.tendsto 0).comp hv).comp (hns.comp hk.tendsto_atTop)
      have he : (fun n => A (value interval 1 four (u (ns (k n))))) =
          (fun n => P102.U4.lpTestPairing interval four.ennreal φ (g (ns (k n)))) :=
        funext fun n => (htest φ _).symm
      change Tendsto (fun n => A (value interval 1 four (u (ns (k n))))) atTop (𝓝 (A 0)) at ht0
      rw [he, map_zero] at ht0
      exact tendsto_nhds_unique ht ht0
    refine ⟨k, ?_⟩
    have ht := ExpandedFA.P1.C12BoundedSequences.weak_evaluation_tendsto ℝ E
      ((g ∘ ns) ∘ k) w hw L
    simpa [hw0] using ht
  simpa only [L, ContinuousLinearMap.comp_apply, hS] using hL

/-- Every specified slope takes a well value of the quartic, including at corners. -/
theorem integrand_slopeField (n : ℕ) (x : Domain 1) (s : Vector 1) :
    integrand x s (slopeField n x) = 0 := by
  simp [integrand, slopeField, tentSlope]

theorem energy_eq_zero_of_represents {n : ℕ} {u : W1p interval 1 four}
    (hu : RepresentsTent n u) : energy interval 1 four integrand u = 0 := by
  have hz : (fun x => integrand x (value interval 1 four u x)
      (gradient interval 1 four u x)) =ᵐ[domainMeasure interval] fun _ => 0 := by
    filter_upwards [hu.2] with x hx
    rw [hx, integrand_slopeField]
  unfold energy energyOnFields
  have hp : (∫⁻ x, ENNReal.ofReal (integrand x (value interval 1 four u x)
      (gradient interval 1 four u x)) ∂domainMeasure interval) = 0 := by
    calc
      _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂domainMeasure interval :=
        lintegral_congr_ae (hz.mono fun x hx => by simp [hx])
      _ = 0 := by simp
  have hn : (∫⁻ x, ENNReal.ofReal (-integrand x (value interval 1 four u x)
      (gradient interval 1 four u x)) ∂domainMeasure interval) = 0 := by
    calc
      _ = ∫⁻ _x, (0 : ℝ≥0∞) ∂domainMeasure interval :=
        lintegral_congr_ae (hz.mono fun x hx => by simp [hx])
      _ = 0 := by simp
  simp [hp, hn]

/-- The zero class has energy the unit interval's volume, namely one. -/
theorem energy_zero : energy interval 1 four integrand 0 = 1 := by
  unfold energy
  rw [map_zero, map_zero]
  rw [energyOnFields_congr interval integrand
    (Lp.coeFn_zero (Vector 1) four.ennreal (domainMeasure interval))
    (Lp.coeFn_zero (Gradient 1 1) four.ennreal (domainMeasure interval))]
  norm_num [energyOnFields, integrand, Measure.restrict_apply_univ, volume_interval]


/-- The full Sobolev weak convergence follows from its two field convergences.
Hahn--Banach extends a functional on the derivative graph to the ambient Lp
product, where it splits into one functional on each field. -/
theorem weaklyConverges_of_fields (u : ℕ → W1p interval 1 four)
    (hv : Tendsto (fun n => value interval 1 four (u n)) atTop (𝓝 0))
    (hg : GradientWeaklyConverges u) : WeaklyConverges u 0 := by
  intro ℓ
  obtain ⟨L, hL, _hLnorm⟩ := exists_extension_norm_eq
    (weakDerivativeGraph interval 1 four) ℓ
  let T : (ValueLp interval 1 four × GradientLp interval 1 four) →L[ℝ] ℝ :=
    L.comp (WithLp.prodContinuousLinearEquiv four.ennreal ℝ
      (ValueLp interval 1 four) (GradientLp interval 1 four)).symm.toContinuousLinearMap
  let A : ValueLp interval 1 four →L[ℝ] ℝ :=
    T.comp (ContinuousLinearMap.inl ℝ (ValueLp interval 1 four) (GradientLp interval 1 four))
  let B : GradientLp interval 1 four →L[ℝ] ℝ :=
    T.comp (ContinuousLinearMap.inr ℝ (ValueLp interval 1 four) (GradientLp interval 1 four))
  have hsum (w : W1p interval 1 four) :
      ℓ w = A (value interval 1 four w) + B (gradient interval 1 four w) := by
    rw [← hL w]
    change L w.val = T (value interval 1 four w, 0) + T (0, gradient interval 1 four w)
    rw [← map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
    rfl
  have hA := (A.continuous.tendsto 0).comp hv
  have hB := hg B
  have h := hA.add hB
  simpa only [Function.comp_apply, map_zero, add_zero, ← hsum] using h

/-- A sequence with the source fields and convergences contradicts both
sequential lower-semicontinuity inequalities. -/
theorem failure_of_convergences (u : ℕ → W1p interval 1 four)
    (hu : ∀ n, RepresentsTent (n + 1) (u n))
    (hzero : ∀ n, u n ∈ zeroSubmodule interval 1 four)
    (hg : GradientWeaklyConverges u) :
    ¬WeakSequentialLowerSemicontinuity ∧ ¬StrongWeakSequentialLowerSemicontinuity := by
  have hv := values_tendsto_zero u hu
  have hw := weaklyConverges_of_fields u hv hg
  have he : (fun n => energy interval 1 four integrand (u n)) = fun _ => (0 : EReal) :=
    funext fun n => energy_eq_zero_of_represents (hu n)
  have hnot : ¬((1 : EReal) ≤ 0) := by norm_num
  constructor
  · intro h
    have hi := h u 0 hzero (Submodule.zero_mem _) hw
    rw [he, Filter.liminf_const, energy_zero] at hi
    exact hnot hi
  · intro h
    have hi := h u 0 hzero (Submodule.zero_mem _) (by simpa only [map_zero] using hv)
      (fun ℓ => by simpa only [map_zero] using hg ℓ)
    rw [he, Filter.liminf_const, energy_zero] at hi
    exact hnot hi

/-- Assemble the exact sequence from zero-boundary realization and
weak convergence of its explicit gradient fields. -/
theorem counterexample_of_realization_and_gradient
    (hr : Expected.Realization)
    (hg : Expected.GradientConvergence) :
    Expected.Counterexample := by
  choose u hu using fun n => hr (n + 1) (Nat.succ_pos n)
  have hfields : ∀ n, RepresentsTent (n + 1) (u n) := fun n => (hu n).1
  have hzero : ∀ n, u n ∈ zeroSubmodule interval 1 four := fun n => (hu n).2
  have hv := values_tendsto_zero u hfields
  have hwg := hg u hfields
  have hw := weaklyConverges_of_fields u hv hwg
  exact ⟨u, hfields, hzero, hv, hwg, hw,
    fun n => energy_eq_zero_of_represents (hfields n), energy_zero,
    failure_of_convergences u hfields hzero hwg⟩

/-- The exact tents give energies zero along a weakly convergent zero-boundary
Sobolev sequence, while its limit has energy one. -/
theorem counterexample : Expected.Counterexample :=
  counterexample_of_realization_and_gradient realization gradient_convergence


/-- The two wells have zero cost, while their midpoint has cost one. -/
theorem nonconvexity : Expected.Nonconvexity := by
  intro x s h
  let A : Gradient 1 1 := EuclideanSpace.single (0, 0) (1 : ℝ)
  have hi := h.2 (show A ∈ Set.univ from trivial)
    (show -A ∈ Set.univ from trivial)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [A, integrand] at hi

/-- The strong value convergence part, without assuming zero boundary values. -/
theorem value_convergence : Expected.ValueConvergence := values_tendsto_zero

theorem energy_on_tent : Expected.EnergyOnTent := by
  intro n u hu
  exact energy_eq_zero_of_represents hu

theorem energy_at_zero : Expected.EnergyAtZero := energy_zero

end VariationalNotes.Sobolev.NonconvexOscillations
