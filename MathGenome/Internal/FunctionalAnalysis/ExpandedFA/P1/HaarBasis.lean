import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.HaarBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15BasisCriterion
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators unitInterval
universe u
namespace ExpandedFA.P1.HaarBasis
open Spec

/-- All prefixes, including those stopping inside a dyadic level, define
sub-sigma-algebras of the usual Lebesgue measurable structure. -/
theorem prefixSigma_le (N : ℕ) : prefixSigma N ≤ (inferInstance : MeasurableSpace I) := by
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨i, _, _, rfl | rfl⟩ <;> exact measurableSet_dyadicCell _ _

theorem prefixSigma_mono : Monotone prefixSigma := by
  intro m n hmn
  apply MeasurableSpace.generateFrom_mono
  rintro s ⟨i, hi, him, hs⟩
  exact ⟨i, hi, lt_of_lt_of_le him hmn, hs⟩

theorem haar_representatives : Spec.HaarRepresentatives.{u} := by
  intro 𝕜 _ p _ n
  by_cases hn : n = 0
  · subst n
    filter_upwards [Lp.coeFn_const (μ := (volume : Measure I)) (p := p) (1 : 𝕜)] with x hx
    simpa [haarLp, haarFunction, Function.const] using hx
  · have hh := (Lp.coeFn_sub
      (indicatorConstLp (μ := (volume : Measure I)) (s := leftCell n) p (measurableSet_dyadicCell _ _)
        (measure_ne_top _ _) (1 : 𝕜))
      (indicatorConstLp (μ := (volume : Measure I)) (s := rightCell n) p (measurableSet_dyadicCell _ _)
        (measure_ne_top _ _) (1 : 𝕜))).trans
      (indicatorConstLp_coeFn.sub indicatorConstLp_coeFn)
    filter_upwards [hh] with x hx
    simpa [haarLp, haarFunction, hn] using hx

/-- Jensen's bound applied on the actual scalar quotient, valid even at infinity.
This does not yet identify these expectations with the Haar partial sums. -/
theorem prefixExpectation_contraction : Spec.PrefixExpectationContraction.{u} := by
  intro 𝕜 _ p _ N f
  by_cases hN : N = 0
  · simp [prefixExpectation, hN]
  · rw [prefixExpectation, ite_eq_right hN, Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_condExp_le_eLpNorm (m := prefixSigma N) (⇑f) Fact.out)

/-- The geometric disjointness needed for every individual Haar split. -/
theorem dyadicCell_disjoint (l k j : ℕ) (hkj : k ≠ j) :
    Disjoint (dyadicCell l k) (dyadicCell l j) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hpow : (0 : ℝ) < 2 ^ l := by positivity
  have hx' : (k : ℝ) ≤ (x : ℝ) * 2 ^ l ∧ (x : ℝ) * 2 ^ l < k + 1 := by
    simpa only [dyadicCell, Set.mem_preimage, Set.mem_Ico, div_le_iff₀ hpow,
      lt_div_iff₀ hpow] using hx
  have hy' : (j : ℝ) ≤ (x : ℝ) * 2 ^ l ∧ (x : ℝ) * 2 ^ l < j + 1 := by
    simpa only [dyadicCell, Set.mem_preimage, Set.mem_Ico, div_le_iff₀ hpow,
      lt_div_iff₀ hpow] using hy
  rcases lt_or_gt_of_ne hkj with h | h
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    linarith
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    linarith

/-- Each parent interval is exactly the disjoint union of its two children. -/
theorem dyadicCell_split (l k : ℕ) :
    dyadicCell l k = dyadicCell (l + 1) (2 * k) ∪ dyadicCell (l + 1) (2 * k + 1) := by
  ext x
  have hp : (0 : ℝ) < 2 ^ l := by positivity
  simp only [dyadicCell, Set.mem_preimage, Set.mem_Ico, Set.mem_union,
    div_le_iff₀ hp, lt_div_iff₀ hp,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  simp only [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ l * 2),
    lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ l * 2)]
  constructor
  · rintro ⟨ha, hb⟩
    by_cases hm : (x : ℝ) * 2 ^ l * 2 < 2 * k + 1
    · left; constructor <;> nlinarith
    · right; constructor <;> nlinarith
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;> constructor <;> nlinarith

/-- Explicit lengths of all genuine dyadic cells. -/
theorem volume_dyadicCell (l k : ℕ) (hk : k < 2 ^ l) :
    volume (dyadicCell l k) = ENNReal.ofReal (1 / (2 : ℝ) ^ l) := by
  have hp : (0 : ℝ) < 2 ^ l := by positivity
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ l := by exact_mod_cast hk
  have hsub : Set.Ico ((k : ℝ) / 2 ^ l) (((k : ℝ) + 1) / 2 ^ l) ⊆ Set.Icc 0 1 := by
    intro x hx
    refine ⟨le_trans (by positivity) hx.1, hx.2.le.trans ?_⟩
    exact (div_le_one hp).mpr hk'
  have him : Subtype.val '' dyadicCell l k =
      Set.Ico ((k : ℝ) / 2 ^ l) (((k : ℝ) + 1) / 2 ^ l) := by
    apply Set.image_preimage_eq_of_subset
    simpa only [Subtype.range_coe] using hsub
  rw [unitInterval.volume_apply, him, Real.volume_Ico]
  congr 1
  ring

theorem real_volume_dyadicCell (l k : ℕ) (hk : k < 2 ^ l) :
    (volume : Measure I).real (dyadicCell l k) = 1 / (2 : ℝ) ^ l := by
  rw [Measure.real, volume_dyadicCell l k hk, ENNReal.toReal_ofReal (by positivity)]

/-- The logarithmic enumeration really is level-by-level, from left to right. -/
theorem haar_index (l k : ℕ) (hk : k < 2 ^ l) :
    haarLevel (2 ^ l + k) = l ∧ haarPosition (2 ^ l + k) = k := by
  have hl : haarLevel (2 ^ l + k) = l := by
    rw [haarLevel, Nat.log2_eq_log_two]
    apply Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _)
    rw [pow_succ]
    omega
  exact ⟨hl, by simp [haarPosition, hl]⟩

theorem haar_position_lt (n : ℕ) (hn : 0 < n) : haarPosition n < 2 ^ haarLevel n := by
  have hlo : 2 ^ haarLevel n ≤ n := by
    simpa [haarLevel, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn)
  have hhi : n < 2 ^ (haarLevel n + 1) := by
    simpa [haarLevel, Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  rw [pow_succ] at hhi
  unfold haarPosition
  omega

/-- Source test spikes have exactly unit L¹ norm, over either scalar field. -/
theorem endpointSpike_norm (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    ‖endpointSpike 𝕜 N‖ = 1 := by
  rw [endpointSpike, norm_indicatorConstLp (by norm_num) (by norm_num),
    real_volume_dyadicCell N 0 (by positivity)]
  simp only [norm_pow, RCLike.norm_ofNat, ENNReal.toReal_one, div_one, Real.rpow_one]
  field_simp

theorem leftCell_disjoint_rightCell (n : ℕ) : Disjoint (leftCell n) (rightCell n) :=
  dyadicCell_disjoint _ _ _ (by omega)

theorem haarFunction_on_left (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (hn : n ≠ 0)
    (x : I) (hx : x ∈ leftCell n) : haarFunction 𝕜 n x = 1 := by
  have hr : x ∉ rightCell n := Set.disjoint_left.mp (leftCell_disjoint_rightCell n) hx
  simp [haarFunction, hn, Set.indicator_of_mem hx, Set.indicator_of_notMem hr]

theorem haarFunction_on_right (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (hn : n ≠ 0)
    (x : I) (hx : x ∈ rightCell n) : haarFunction 𝕜 n x = -1 := by
  have hl : x ∉ leftCell n := Set.disjoint_left.mp (leftCell_disjoint_rightCell n).symm hx
  simp [haarFunction, hn, Set.indicator_of_mem hx, Set.indicator_of_notMem hl]

theorem haarFunction_norm_le_one (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : I) :
    ‖haarFunction 𝕜 n x‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [haarFunction, hn]
  · by_cases hl : x ∈ leftCell n
    · rw [haarFunction_on_left 𝕜 n hn x hl, norm_one]
    · by_cases hr : x ∈ rightCell n
      · rw [haarFunction_on_right 𝕜 n hn x hr, norm_neg, norm_one]
      · simp [haarFunction, hn, Set.indicator_of_notMem hl, Set.indicator_of_notMem hr]

theorem haarFunction_memLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    MemLp (haarFunction 𝕜 n) p (volume : Measure I) :=
  (memLp_congr_ae (haar_representatives 𝕜 p n)).mp (Lp.memLp _)

theorem haar_nonzero : Spec.HaarNonzero.{u} := by
  intro 𝕜 _ p _ _ n hzero
  have hae : haarFunction 𝕜 n =ᵐ[volume] 0 :=
    (haar_representatives 𝕜 p n).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  by_cases hn : n = 0
  · have hh := hae.exists
    obtain ⟨x, hx⟩ := hh
    simpa [haarFunction, hn] using hx
  · have hk := haar_position_lt n (Nat.pos_of_ne_zero hn)
    have hk' : 2 * haarPosition n < 2 ^ (haarLevel n + 1) := by
      rw [pow_succ]; omega
    have hpos : volume (leftCell n) ≠ 0 := by
      rw [leftCell, volume_dyadicCell _ _ hk']
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    apply hpos
    apply measure_mono_null (t := {x | ¬ haarFunction 𝕜 n x = 0}) ?_ (ae_iff.mp hae)
    intro x hx
    change haarFunction 𝕜 n x ≠ 0
    rw [haarFunction_on_left 𝕜 n hn x hx]
    exact one_ne_zero

/-- The whole level-zero cell differs from the unit interval only at 1. -/
theorem dyadicCell_zero_ae : ∀ᵐ x : I ∂volume, x ∈ dyadicCell 0 0 := by
  filter_upwards [(volume : Measure I).ae_ne (1 : I)] with x hx
  have hx' : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (by
    intro h
    apply hx
    exact Subtype.ext h)
  simpa [dyadicCell] using And.intro x.property.1 hx'

theorem endpointSpike_zero (𝕜 : Type u) [RCLike 𝕜] :
    endpointSpike 𝕜 0 = haarLp 𝕜 1 0 := by
  apply Lp.ext
  have hs := @indicatorConstLp_coeFn I 𝕜 _ 1 volume _ (dyadicCell 0 0)
    (measurableSet_dyadicCell 0 0) (measure_ne_top _ _) ((2 : 𝕜) ^ 0)
  filter_upwards [hs, haar_representatives 𝕜 1 0, dyadicCell_zero_ae] with x hx hy hz
  simp only [pow_zero, Set.indicator_of_mem hz] at hx
  simp only [haarFunction, ite_eq_left rfl] at hy
  simpa only [endpointSpike, pow_zero] using hx.trans hy.symm

/-- Splitting the leftmost cell gives precisely the source's dyadic difference. -/
theorem endpointSpike_succ (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    endpointSpike 𝕜 (N + 1) = endpointSpike 𝕜 N +
      ((2 : 𝕜) ^ N) • haarLp 𝕜 1 (2 ^ N) := by
  have hi : haarLevel (2 ^ N) = N ∧ haarPosition (2 ^ N) = 0 := by
    simpa using haar_index N 0 (by positivity)
  have hn : (2 : ℕ) ^ N ≠ 0 := by positivity
  have hleft : leftCell (2 ^ N) = dyadicCell (N + 1) 0 := by simp [leftCell, hi]
  have hright : rightCell (2 ^ N) = dyadicCell (N + 1) 1 := by simp [rightCell, hi]
  have hs (n : ℕ) : ⇑(endpointSpike 𝕜 n) =ᵐ[volume]
      (dyadicCell n 0).indicator (fun _ => (2 : 𝕜) ^ n) := indicatorConstLp_coeFn
  apply Lp.ext
  filter_upwards [hs (N + 1), hs N, haar_representatives 𝕜 1 (2 ^ N),
    Lp.coeFn_add (endpointSpike 𝕜 N) (((2 : 𝕜) ^ N) • haarLp 𝕜 1 (2 ^ N)),
    Lp.coeFn_smul ((2 : 𝕜) ^ N) (haarLp 𝕜 1 (2 ^ N))] with x hsn hsold hh ha hsm
  simp only [Pi.add_apply, Pi.smul_apply] at ha hsm
  rw [hsn, ha, hsm, hsold, hh]
  simp only [haarFunction, ite_eq_right hn, hleft, hright, smul_eq_mul]
  have hparent : x ∈ dyadicCell N 0 ↔
      x ∈ dyadicCell (N + 1) 0 ∨ x ∈ dyadicCell (N + 1) 1 := by
    rw [dyadicCell_split N 0]; simp
  by_cases hl : x ∈ dyadicCell (N + 1) 0
  · have hr : x ∉ dyadicCell (N + 1) 1 :=
      Set.disjoint_left.mp (dyadicCell_disjoint _ 0 1 (by decide)) hl
    have hp := hparent.mpr (Or.inl hl)
    simp [Set.indicator_of_mem hl, Set.indicator_of_mem hp, Set.indicator_of_notMem hr, pow_succ]
    ring
  · by_cases hr : x ∈ dyadicCell (N + 1) 1
    · have hp := hparent.mpr (Or.inr hr)
      simp [Set.indicator_of_notMem hl, Set.indicator_of_mem hp, Set.indicator_of_mem hr]
    · have hp : x ∉ dyadicCell N 0 := by simpa [hparent, hl, hr]
      simp [Set.indicator_of_notMem hl, Set.indicator_of_notMem hr, Set.indicator_of_notMem hp]

theorem endpointSpike_expansion (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    endpointSpike 𝕜 N = haarLp 𝕜 1 0 +
      ∑ k ∈ Finset.range N, ((2 : 𝕜) ^ k) • haarLp 𝕜 1 (2 ^ k) := by
  induction N with
  | zero => simpa using endpointSpike_zero 𝕜
  | succ N ih => rw [endpointSpike_succ, ih, Finset.sum_range_succ, add_assoc]

/-- The nonconstant Haar functions have mean zero, over both scalar fields. -/
theorem haarFunction_integral (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    (∫ x : I, haarFunction 𝕜 n x) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [haarFunction, hn]
  · have hk := haar_position_lt n (Nat.pos_of_ne_zero hn)
    have hl : 2 * haarPosition n < 2 ^ (haarLevel n + 1) := by
      rw [pow_succ]; omega
    have hr : 2 * haarPosition n + 1 < 2 ^ (haarLevel n + 1) := by
      rw [pow_succ]; omega
    simp only [haarFunction, ite_eq_right hn, leftCell, rightCell]
    rw [integral_sub
      ((integrable_const (μ := (volume : Measure I)) (1 : 𝕜)).indicator (measurableSet_dyadicCell _ _))
      ((integrable_const (μ := (volume : Measure I)) (1 : 𝕜)).indicator (measurableSet_dyadicCell _ _)),
      integral_indicator_const _ (measurableSet_dyadicCell _ _),
      integral_indicator_const _ (measurableSet_dyadicCell _ _)]
    simp only [leftCell, rightCell, real_volume_dyadicCell _ _ hl,
      real_volume_dyadicCell _ _ hr, sub_self]

/-- The integral defining a Fourier-Haar coefficient is well-defined for every
Lp input on this probability space, including p = infinity. -/
theorem haarProduct_integrable {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I)) (n : ℕ) :
    Integrable (fun x => f x * haarFunction 𝕜 n x) volume :=
  ((Lp.memLp f).integrable Fact.out).mul_bdd
    (haarFunction_memLp 𝕜 p n).aestronglyMeasurable
    (Filter.Eventually.of_forall (haarFunction_norm_le_one 𝕜 n))

/-- The probability-space embedding of Lp in L1 has norm at most one. -/
theorem integral_norm_le_lpNorm {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I)) :
    (∫ x, ‖f x‖) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le (f := ⇑f) Fact.out)

/-- An explicit bound, with no coefficient-continuity assumption. -/
theorem haarCoefficient_norm_le {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure I)) (n : ℕ) :
    ‖haarCoefficient f n‖ ≤
      ‖(if n = 0 then 1 else (2 : 𝕜) ^ haarLevel n)‖ * ‖f‖ := by
  rw [haarCoefficient, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∫ x, f x * haarFunction 𝕜 n x‖ ≤ ∫ x, ‖f x * haarFunction 𝕜 n x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ := by
      apply integral_mono (haarProduct_integrable f n).norm
        ((Lp.memLp f).integrable Fact.out).norm
      intro x
      dsimp only
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (haarFunction_norm_le_one 𝕜 n x)
    _ ≤ ‖f‖ := integral_norm_le_lpNorm f

/-- The actual Fourier-Haar coefficients as scalar-linear continuous maps. -/
def haarCoefficientCLM (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (n : ℕ) : Lp 𝕜 p (volume : Measure I) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => haarCoefficient f n
      map_add' := by
        intro f g
        rw [haarCoefficient, haarCoefficient, haarCoefficient, ← mul_add]
        congr 1
        rw [← integral_add (haarProduct_integrable f n) (haarProduct_integrable g n)]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add f g] with x hx
        simp only [Pi.add_apply] at hx
        rw [hx, add_mul]
      map_smul' := by
        intro c f
        simp only [haarCoefficient, RingHom.id_apply, smul_eq_mul]
        have hi : (∫ x, (c • f) x * haarFunction 𝕜 n x) =
            c * ∫ x, f x * haarFunction 𝕜 n x := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_smul c f] with x hx
          simp only [Pi.smul_apply, smul_eq_mul] at hx
          rw [hx, mul_assoc]
        rw [hi]
        ring }
    ‖(if n = 0 then 1 else (2 : 𝕜) ^ haarLevel n)‖
    (fun f => haarCoefficient_norm_le f n)

@[simp] theorem haarCoefficientCLM_apply (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    haarCoefficientCLM 𝕜 p n f = haarCoefficient f n := rfl

theorem haarCoefficient_continuous (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℕ) :
    Continuous (fun f : Lp 𝕜 p (volume : Measure I) => haarCoefficient f n) :=
  (haarCoefficientCLM 𝕜 p n).continuous

/-- Every dyadic child is contained in its parent, including cells outside I. -/
theorem dyadicCell_subset_parent (l k : ℕ) :
    dyadicCell (l + 1) k ⊆ dyadicCell l (k / 2) := by
  have hk : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rw [dyadicCell_split l (k / 2)]
  intro x hx
  rcases hk with hk | hk
  · left; rw [← hk]; exact hx
  · right; rw [← hk]; exact hx

/-- A finer dyadic cell is either contained in a specified coarser cell or
is disjoint from it. No positive-measure hypothesis is needed. -/
theorem dyadicCell_subset_or_disjoint (l m j k : ℕ) (hlm : l ≤ m) :
    dyadicCell m k ⊆ dyadicCell l j ∨ Disjoint (dyadicCell m k) (dyadicCell l j) := by
  induction m generalizing k with
  | zero =>
    have hl : l = 0 := by omega
    subst l
    by_cases h : k = j
    · subst k; exact Or.inl Set.Subset.rfl
    · exact Or.inr (dyadicCell_disjoint 0 k j h)
  | succ m ih =>
    by_cases hl : l = m + 1
    · subst l
      by_cases h : k = j
      · subst k; exact Or.inl Set.Subset.rfl
      · exact Or.inr (dyadicCell_disjoint _ k j h)
    · rcases ih (k := k / 2) (by omega) with h | h
      · exact Or.inl ((dyadicCell_subset_parent m k).trans h)
      · exact Or.inr (h.mono_left (dyadicCell_subset_parent m k))

/-- Outside its parent cell a nonconstant Haar function vanishes. -/
theorem haarFunction_eq_zero_of_notMem (𝕜 : Type u) [RCLike 𝕜]
    {n : ℕ} (hn : n ≠ 0) {x : I}
    (hx : x ∉ dyadicCell (haarLevel n) (haarPosition n)) :
    haarFunction 𝕜 n x = 0 := by
  have hsplit := dyadicCell_split (haarLevel n) (haarPosition n)
  have hl : x ∉ leftCell n := fun h => hx (hsplit ▸ Or.inl h)
  have hr : x ∉ rightCell n := fun h => hx (hsplit ▸ Or.inr h)
  simp [haarFunction, hn, Set.indicator_of_notMem hl, Set.indicator_of_notMem hr]

/-- A Haar function is constant on every cell strictly finer than its level. -/
theorem haarFunction_constant_on_cell (𝕜 : Type u) [RCLike 𝕜]
    (n m k : ℕ) (hnm : haarLevel n + 1 ≤ m) :
    ∃ c : 𝕜, ∀ x ∈ dyadicCell m k, haarFunction 𝕜 n x = c := by
  by_cases hn : n = 0
  · exact ⟨1, fun x _ => by simp [haarFunction, hn]⟩
  rcases dyadicCell_subset_or_disjoint (haarLevel n + 1) m
    (2 * haarPosition n) k hnm with hl | hl
  · exact ⟨1, fun x hx => haarFunction_on_left 𝕜 n hn x (hl hx)⟩
  rcases dyadicCell_subset_or_disjoint (haarLevel n + 1) m
    (2 * haarPosition n + 1) k hnm with hr | hr
  · exact ⟨-1, fun x hx => haarFunction_on_right 𝕜 n hn x (hr hx)⟩
  refine ⟨0, fun x hx => ?_⟩
  have hxl : x ∉ leftCell n := Set.disjoint_left.mp hl hx
  have hxr : x ∉ rightCell n := Set.disjoint_left.mp hr hx
  simp [haarFunction, hn, Set.indicator_of_notMem hxl, Set.indicator_of_notMem hxr]

/-- The cancellation argument for distinct dyadic levels. -/
theorem haarFunction_integral_mul_of_level_lt (𝕜 : Type u) [RCLike 𝕜]
    {i j : ℕ} (hj : j ≠ 0) (hij : haarLevel i < haarLevel j) :
    (∫ x : I, haarFunction 𝕜 i x * haarFunction 𝕜 j x) = 0 := by
  obtain ⟨c, hc⟩ := haarFunction_constant_on_cell 𝕜 i (haarLevel j)
    (haarPosition j) hij
  have heq : (fun x => haarFunction 𝕜 i x * haarFunction 𝕜 j x) =
      (fun x => c * haarFunction 𝕜 j x) := by
    funext x
    by_cases hx : x ∈ dyadicCell (haarLevel j) (haarPosition j)
    · rw [hc x hx]
    · rw [haarFunction_eq_zero_of_notMem 𝕜 hj hx, mul_zero, mul_zero]
  rw [heq, integral_const_mul, haarFunction_integral]
  simp [hj]

/-- The numbering is injective on each level. -/
theorem haarPosition_ne_of_level_eq {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0)
    (hlevel : haarLevel i = haarLevel j) (hij : i ≠ j) :
    haarPosition i ≠ haarPosition j := by
  have hlo (n : ℕ) (hn : n ≠ 0) : 2 ^ haarLevel n ≤ n := by
    simpa [haarLevel, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hn
  have h1 := hlo i hi
  have h2 := hlo j hj
  unfold haarPosition
  rw [hlevel] at h1 ⊢
  omega

/-- Off-diagonal orthogonality, for the genuine unnormalised functions. -/
theorem haarFunction_integral_mul_of_ne (𝕜 : Type u) [RCLike 𝕜]
    {i j : ℕ} (hij : i ≠ j) :
    (∫ x : I, haarFunction 𝕜 i x * haarFunction 𝕜 j x) = 0 := by
  by_cases hi : i = 0
  · subst i
    have h0 : haarFunction 𝕜 0 = fun _ => 1 := rfl
    simp only [h0, one_mul, haarFunction_integral, if_neg (Ne.symm hij)]
  by_cases hj : j = 0
  · subst j
    have h0 : haarFunction 𝕜 0 = fun _ => 1 := rfl
    simp only [h0, mul_one, haarFunction_integral, if_neg hi]
  rcases lt_trichotomy (haarLevel i) (haarLevel j) with hl | hl | hl
  · exact haarFunction_integral_mul_of_level_lt 𝕜 hj hl
  · have hp := haarPosition_ne_of_level_eq hi hj hl hij
    apply integral_eq_zero_of_ae
    apply Filter.Eventually.of_forall
    intro x
    change haarFunction 𝕜 i x * haarFunction 𝕜 j x = 0
    by_cases hx : x ∈ dyadicCell (haarLevel i) (haarPosition i)
    · have hxj : x ∉ dyadicCell (haarLevel j) (haarPosition j) := by
        rw [← hl]
        exact Set.disjoint_left.mp (dyadicCell_disjoint _ _ _ hp) hx
      rw [haarFunction_eq_zero_of_notMem 𝕜 hj hxj, mul_zero]
    · rw [haarFunction_eq_zero_of_notMem 𝕜 hi hx, zero_mul]
  · simpa only [mul_comm] using haarFunction_integral_mul_of_level_lt 𝕜 hi hl

/-- Squaring an unnormalised Haar function gives the indicator of its support. -/
theorem haarFunction_mul_self (𝕜 : Type u) [RCLike 𝕜] {n : ℕ} (hn : n ≠ 0) :
    (fun x => haarFunction 𝕜 n x * haarFunction 𝕜 n x) =
      (dyadicCell (haarLevel n) (haarPosition n)).indicator (fun _ => 1) := by
  funext x
  by_cases hl : x ∈ leftCell n
  · have hp : x ∈ dyadicCell (haarLevel n) (haarPosition n) := by
      rw [dyadicCell_split]; exact Or.inl hl
    rw [haarFunction_on_left 𝕜 n hn x hl, Set.indicator_of_mem hp, one_mul]
  · by_cases hr : x ∈ rightCell n
    · have hp : x ∈ dyadicCell (haarLevel n) (haarPosition n) := by
        rw [dyadicCell_split]; exact Or.inr hr
      rw [haarFunction_on_right 𝕜 n hn x hr, Set.indicator_of_mem hp]
      ring
    · have hp : x ∉ dyadicCell (haarLevel n) (haarPosition n) := by
        rw [dyadicCell_split]; exact fun h => h.elim hl hr
      rw [haarFunction_eq_zero_of_notMem 𝕜 hn hp, Set.indicator_of_notMem hp, mul_zero]

/-- The squared L2 norm is the length of the supporting dyadic interval. -/
theorem haarFunction_integral_mul_self (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) :
    (∫ x : I, haarFunction 𝕜 n x * haarFunction 𝕜 n x) =
      if n = 0 then 1 else ((2 : 𝕜) ^ haarLevel n)⁻¹ := by
  by_cases hn : n = 0
  · subst n; simp [haarFunction]
  · rw [haarFunction_mul_self 𝕜 hn, integral_indicator_const _ (measurableSet_dyadicCell _ _),
      real_volume_dyadicCell _ _ (haar_position_lt n (Nat.pos_of_ne_zero hn)), if_neg hn]
    norm_num [RCLike.real_smul_eq_coe_mul]
    exact congrArg (fun z : 𝕜 => z ^ haarLevel n) (map_ofNat (algebraMap ℝ 𝕜) 2)

/-- Biorthogonality of the explicit integral coefficients, over both fields. -/
theorem haarCoefficient_haarLp (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (i j : ℕ) :
    haarCoefficient (haarLp 𝕜 p j) i = if i = j then 1 else 0 := by
  have heq : (∫ x : I, (haarLp 𝕜 p j) x * haarFunction 𝕜 i x) =
      ∫ x : I, haarFunction 𝕜 j x * haarFunction 𝕜 i x := by
    apply integral_congr_ae
    filter_upwards [haar_representatives 𝕜 p j] with x hx
    rw [hx]
  rw [haarCoefficient, heq]
  by_cases hij : i = j
  · subst j
    rw [haarFunction_integral_mul_self, if_pos rfl]
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
  · rw [haarFunction_integral_mul_of_ne 𝕜 (Ne.symm hij), mul_zero, if_neg hij]

/-- A finite Haar expansion has exactly its prescribed coefficients at every
retained index; all subsequent coefficients vanish. -/
theorem haarCoefficient_partialSum (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ → 𝕜) (N i : ℕ) :
    haarCoefficient (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) a N) i =
      if i < N then a i else 0 := by
  classical
  change haarCoefficientCLM 𝕜 p i _ = _
  simp [C15Basis.Spec.orderedPartialSum, map_sum, map_smul, haarCoefficient_haarLp,
    Finset.sum_ite_eq', Finset.mem_range]

/-- Every norm-convergent ordered expansion has the explicit integral
coefficients. This proves uniqueness without assuming the basis theorem. -/
theorem haar_expansion_unique (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : Lp 𝕜 p (volume : Measure I)}
    {a : ℕ → 𝕜}
    (ha : Tendsto (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) a) atTop (𝓝 f)) :
    a = haarCoefficient f := by
  apply C15BasisCriterion.BasisCriterionProof.unique_expansion
    (haarCoefficientCLM 𝕜 p) _ ha
  intro i j
  classical
  simp only [haarCoefficientCLM_apply, haarCoefficient_haarLp, Pi.single_apply, eq_comm]

/-- The actual partial sums are continuous scalar-linear maps even before
one has proved their uniform contraction estimate. -/
def haarPartialSumCLM (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (N : ℕ) :
    Lp 𝕜 p (volume : Measure I) →L[𝕜] Lp 𝕜 p (volume : Measure I) :=
  ∑ i ∈ Finset.range N, (haarCoefficientCLM 𝕜 p i).smulRight (haarLp 𝕜 p i)

@[simp] theorem haarPartialSumCLM_apply (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    haarPartialSumCLM 𝕜 p N f = haarPartialSum N f := by
  simp [haarPartialSumCLM, haarPartialSum, C15Basis.Spec.orderedPartialSum]

/-- Truncating twice keeps exactly the shorter prefix. -/
theorem haarPartialSum_comp {𝕜 : Type u} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (m N : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    haarPartialSum m (haarPartialSum N f) = haarPartialSum (min m N) f := by
  classical
  change (∑ i ∈ Finset.range m,
    haarCoefficient (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p)
      (haarCoefficient f) N) i • haarLp 𝕜 p i) = _
  simp_rw [haarCoefficient_partialSum]
  simp only [ite_smul, zero_smul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    haarPartialSum, C15Basis.Spec.orderedPartialSum]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  · intro i _; rfl

/-- The leftmost cells are nested as their levels increase. -/
theorem dyadicCell_zero_subset (l m : ℕ) (hlm : l ≤ m) :
    dyadicCell m 0 ⊆ dyadicCell l 0 := by
  induction m with
  | zero =>
    have hl : l = 0 := by omega
    subst l
    exact Set.Subset.rfl
  | succ m ih =>
    by_cases h : l = m + 1
    · subst l; exact Set.Subset.rfl
    · exact (dyadicCell_subset_parent m 0).trans (ih (by omega))

/-- The successive right annuli on the leftmost branch are pairwise disjoint. -/
theorem endpointAnnuli_disjoint : Pairwise (fun i j : ℕ =>
    Disjoint (dyadicCell (i + 1) 1) (dyadicCell (j + 1) 1)) := by
  intro i j hij
  wlog h : i < j generalizing i j
  · exact (this (i := j) (j := i) (Ne.symm hij) (by omega)).symm
  have hj : dyadicCell (j + 1) 1 ⊆ dyadicCell (i + 1) 0 := by
    have hp : dyadicCell (j + 1) 1 ⊆ dyadicCell j 0 := by
      simpa using dyadicCell_subset_parent j 1
    exact hp.trans (dyadicCell_zero_subset _ _ h)
  exact (dyadicCell_disjoint (i + 1) 1 0 (by decide)).mono_right hj

/-- A left-branch Haar function equals +1 before the annulus's level, -1 at
that level, and zero at later levels. -/
theorem haarFunction_on_endpointAnnulus (𝕜 : Type u) [RCLike 𝕜]
    (k j : ℕ) (x : I) (hx : x ∈ dyadicCell (j + 1) 1) :
    haarFunction 𝕜 (2 ^ k) x = if k < j then 1 else if k = j then -1 else 0 := by
  have hi : haarLevel (2 ^ k) = k ∧ haarPosition (2 ^ k) = 0 := by
    simpa using haar_index k 0 (by positivity)
  have hn : (2 : ℕ) ^ k ≠ 0 := by positivity
  by_cases hkj : k < j
  · rw [if_pos hkj]
    apply haarFunction_on_left 𝕜 _ hn x
    simp only [leftCell, hi, mul_zero]
    have hp : x ∈ dyadicCell j 0 := by
      have hp : dyadicCell (j + 1) 1 ⊆ dyadicCell j 0 := by
        simpa using dyadicCell_subset_parent j 1
      exact hp hx
    exact dyadicCell_zero_subset (k + 1) j hkj hp
  · rw [if_neg hkj]
    by_cases h : k = j
    · subst k
      rw [if_pos rfl]
      apply haarFunction_on_right 𝕜 _ hn x
      simpa [rightCell, hi] using hx
    · rw [if_neg h]
      apply haarFunction_eq_zero_of_notMem 𝕜 hn
      simp only [hi]
      have hjk : dyadicCell k 0 ⊆ dyadicCell (j + 1) 0 :=
        dyadicCell_zero_subset _ _ (by omega)
      exact fun hxx => Set.disjoint_left.mp
        (dyadicCell_disjoint (j + 1) 1 0 (by decide)) hx (hjk hxx)

/-- A representative for each finite signed branch polynomial. -/
theorem endpointTransform_ae (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    ⇑(endpointTransform 𝕜 N) =ᵐ[volume] fun x => 1 +
      ∑ k ∈ Finset.range N, (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) *
        haarFunction 𝕜 (2 ^ k) x := by
  have hs : ⇑(∑ k ∈ Finset.range N,
      (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) • haarLp 𝕜 1 (2 ^ k)) =ᵐ[volume]
      fun x => ∑ k ∈ Finset.range N, (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) *
        haarFunction 𝕜 (2 ^ k) x := by
    refine (Lp.coeFn_finsetSum _ _).trans ?_
    have hterm (k : ℕ) :
        ⇑((((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) • haarLp 𝕜 1 (2 ^ k)) =ᵐ[volume]
          fun x => (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) * haarFunction 𝕜 (2 ^ k) x :=
      (Lp.coeFn_smul _ _).trans ((haar_representatives 𝕜 1 (2 ^ k)).fun_comp
        (fun z => (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) * z))
    have hsum := eventuallyEq_sum (s := Finset.range N) (fun k _ => hterm k)
    filter_upwards [hsum] with x hx
    simpa only [Finset.sum_apply] using hx
  exact (Lp.coeFn_add _ _).trans ((haar_representatives 𝕜 1 0).add hs |>.trans
    (Filter.Eventually.of_forall (fun x => by simp [haarFunction])))

/-- The elementary finite geometric sum used by the endpoint example. -/
theorem endpoint_geometric_sum (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) :
    1 + (∑ k ∈ Finset.range j, ((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) -
      (((-1 : 𝕜) ^ (j + 1)) * (2 : 𝕜) ^ j) =
        (2 + 4 * (-2 : 𝕜) ^ j) / 3 := by
  have hg : (∑ k ∈ Finset.range j, ((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) =
      ((-2 : 𝕜) ^ j - 1) / 3 := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ, ih]
      have hpow : (-2 : 𝕜) ^ j = (-1 : 𝕜) ^ j * 2 ^ j := by
        rw [← mul_pow]; congr 1; ring
      rw [pow_succ, pow_succ, hpow]
      field_simp
      ring
  rw [hg]
  have hpow : (-2 : 𝕜) ^ j = (-1 : 𝕜) ^ j * 2 ^ j := by
    rw [← mul_pow]; congr 1; ring
  rw [pow_succ, hpow]
  field_simp
  ring

/-- Exact annular values of the signed endpoint polynomial. -/
theorem endpoint_polynomial_on_annulus (𝕜 : Type u) [RCLike 𝕜]
    (N j : ℕ) (hj : j < N) (x : I) (hx : x ∈ dyadicCell (j + 1) 1) :
    1 + (∑ k ∈ Finset.range N,
      (((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) * haarFunction 𝕜 (2 ^ k) x) =
        (2 + 4 * (-2 : 𝕜) ^ j) / 3 := by
  classical
  have hh (k : ℕ) : haarFunction 𝕜 (2 ^ k) x =
      (if k < j then 1 else 0) - (if k = j then 1 else 0) := by
    rw [haarFunction_on_endpointAnnulus 𝕜 k j x hx]
    by_cases h : k < j
    · simp [h, Nat.ne_of_lt h]
    · by_cases he : k = j <;> simp [h, he]
  simp_rw [hh, mul_sub, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib]
  have hf : (Finset.range N).filter (fun k => k < j) = Finset.range j := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [hf]
  have he : (∑ k ∈ (Finset.range N).filter (fun k => k = j),
      ((-1 : 𝕜) ^ (k + 1)) * (2 : 𝕜) ^ k) =
        ((-1 : 𝕜) ^ (j + 1)) * (2 : 𝕜) ^ j := by
    simp [hj]
  rw [he, ← add_sub_assoc]
  exact endpoint_geometric_sum 𝕜 j

/-- Each annulus contributes at least one third to the L1 norm. -/
theorem endpoint_annular_value_norm (𝕜 : Type u) [RCLike 𝕜] (j : ℕ) :
    (2 : ℝ) ^ (j + 1) / 3 ≤ ‖(2 + 4 * (-2 : 𝕜) ^ j) / 3‖ := by
  have hj : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hn : ‖(4 : 𝕜) * (-2 : 𝕜) ^ j‖ ≤ ‖2 + 4 * (-2 : 𝕜) ^ j‖ + 2 := by
    calc
      ‖(4 : 𝕜) * (-2 : 𝕜) ^ j‖ = ‖(2 + 4 * (-2 : 𝕜) ^ j) + (-2)‖ := by congr 1; ring
      _ ≤ ‖2 + 4 * (-2 : 𝕜) ^ j‖ + ‖(-2 : 𝕜)‖ := norm_add_le _ _
      _ = ‖2 + 4 * (-2 : 𝕜) ^ j‖ + 2 := by simp
  simp only [norm_mul, norm_pow, norm_neg, RCLike.norm_ofNat] at hn
  rw [norm_div, RCLike.norm_ofNat]
  rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3), pow_succ]
  linarith

theorem endpointTransform_annulus_bound (𝕜 : Type u) [RCLike 𝕜]
    (N j : ℕ) (hj : j < N) :
    1 / 3 ≤ ∫ x in dyadicCell (j + 1) 1, ‖endpointTransform 𝕜 N x‖ := by
  have hae : (fun x => ‖endpointTransform 𝕜 N x‖) =ᵐ[volume.restrict (dyadicCell (j + 1) 1)]
      fun _ => ‖(2 + 4 * (-2 : 𝕜) ^ j) / 3‖ := by
    filter_upwards [ae_restrict_of_ae (endpointTransform_ae 𝕜 N),
      ae_restrict_mem (measurableSet_dyadicCell (j + 1) 1)] with x hrep hx
    rw [hrep, endpoint_polynomial_on_annulus 𝕜 N j hj x hx]
  rw [integral_congr_ae hae, integral_const]
  simp only [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  change 1 / 3 ≤ (volume : Measure I).real (dyadicCell (j + 1) 1) *
    ‖(2 + 4 * (-2 : 𝕜) ^ j) / 3‖
  rw [real_volume_dyadicCell _ _ (by
    have : 1 < (2 : ℕ) ^ (j + 1) := one_lt_pow₀ (by decide) (by omega)
    exact this)]
  calc
    1 / 3 = (1 / (2 : ℝ) ^ (j + 1)) * ((2 : ℝ) ^ (j + 1) / 3) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (endpoint_annular_value_norm 𝕜 j) (by positivity)

/-- The finite endpoint witnesses have linearly growing transformed norm. -/
theorem endpointTransform_norm_lower (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    (N : ℝ) / 3 ≤ ‖endpointTransform 𝕜 N‖ := by
  have hint := ((Lp.memLp (endpointTransform 𝕜 N)).integrable (by norm_num)).norm
  have hsum : (N : ℝ) / 3 ≤ ∑ j ∈ Finset.range N,
      ∫ x in dyadicCell (j + 1) 1, ‖endpointTransform 𝕜 N x‖ := by
    calc
      (N : ℝ) / 3 = ∑ _j ∈ Finset.range N, (1 / 3 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j hj => endpointTransform_annulus_bound 𝕜 N j
        (Finset.mem_range.mp hj)
  apply hsum.trans
  rw [← integral_biUnion_finset (Finset.range N)
    (fun j _ => measurableSet_dyadicCell (j + 1) 1)
    (fun i _ j _ hij => endpointAnnuli_disjoint hij)
    (fun j _ => hint.integrableOn), L1.norm_eq_integral_norm]
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall (fun x => norm_nonneg _))

theorem endpoint_witnesses : Spec.EndpointWitnesses.{u} := by
  intro 𝕜 _ N
  refine ⟨endpointSpike_norm 𝕜 N, ?_⟩
  exact (by linarith : ((N : ℝ) - 1) / 3 ≤ (N : ℝ) / 3).trans
    (endpointTransform_norm_lower 𝕜 N)

/-- The finite sign transforms used in the endpoint argument act on the
actual Fourier-Haar coefficients of arbitrary L1 functions. -/
def endpointTransformCLM (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    Lp 𝕜 1 (volume : Measure I) →L[𝕜] Lp 𝕜 1 (volume : Measure I) :=
  (haarCoefficientCLM 𝕜 1 0).smulRight (haarLp 𝕜 1 0) +
    ∑ k ∈ Finset.range N, ((-1 : 𝕜) ^ (k + 1)) •
      (haarCoefficientCLM 𝕜 1 (2 ^ k)).smulRight (haarLp 𝕜 1 (2 ^ k))

@[simp] theorem endpointTransformCLM_apply (𝕜 : Type u) [RCLike 𝕜] (N : ℕ)
    (f : Lp 𝕜 1 (volume : Measure I)) :
    endpointTransformCLM 𝕜 N f = haarCoefficient f 0 • haarLp 𝕜 1 0 +
      ∑ k ∈ Finset.range N, ((-1 : 𝕜) ^ (k + 1)) •
        (haarCoefficient f (2 ^ k) • haarLp 𝕜 1 (2 ^ k)) := by
  simp [endpointTransformCLM]

theorem haarCoefficient_endpointSpike_zero (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    haarCoefficient (endpointSpike 𝕜 N) 0 = 1 := by
  change haarCoefficientCLM 𝕜 1 0 (endpointSpike 𝕜 N) = _
  rw [endpointSpike_expansion, map_add, map_sum]
  simp only [map_smul, haarCoefficientCLM_apply, haarCoefficient_haarLp]
  have hn (k : ℕ) : (0 : ℕ) ≠ 2 ^ k := by positivity
  simp [hn]

theorem haarCoefficient_endpointSpike_branch (𝕜 : Type u) [RCLike 𝕜]
    (N k : ℕ) (hk : k < N) :
    haarCoefficient (endpointSpike 𝕜 N) (2 ^ k) = (2 : 𝕜) ^ k := by
  change haarCoefficientCLM 𝕜 1 (2 ^ k) (endpointSpike 𝕜 N) = _
  rw [endpointSpike_expansion, map_add, map_sum]
  simp only [map_smul, haarCoefficientCLM_apply, haarCoefficient_haarLp]
  have hn : (2 : ℕ) ^ k ≠ 0 := by positivity
  have hinj : Function.Injective (fun j : ℕ => (2 : ℕ) ^ j) :=
    Nat.pow_right_injective (by decide)
  simp [hn, hinj.eq_iff, hk]

/-- The test-polynomial transform is the image of the unit-norm test input,
not an unrelated sequence of vectors. -/
theorem endpointTransformCLM_spike (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) :
    endpointTransformCLM 𝕜 N (endpointSpike 𝕜 N) = endpointTransform 𝕜 N := by
  rw [endpointTransformCLM_apply, haarCoefficient_endpointSpike_zero, one_smul]
  unfold endpointTransform
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [haarCoefficient_endpointSpike_branch 𝕜 N k (Finset.mem_range.mp hk), smul_smul]

/-- Unconditionally summable expansions give bounded values for these
particular finite sign multipliers. -/
theorem endpointTransformCLM_bounded_of_summable (𝕜 : Type u) [RCLike 𝕜]
    (f : Lp 𝕜 1 (volume : Measure I))
    (hf : Summable (fun n => haarCoefficient f n • haarLp 𝕜 1 n)) :
    ∃ C : ℝ, ∀ N, ‖endpointTransformCLM 𝕜 N f‖ ≤ C := by
  classical
  have hb := hf.comp_injective (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))
  have hp := hb.indicator {k | Even (k + 1)}
  have hn := hb.indicator {k | ¬ Even (k + 1)}
  have hs : Summable (fun k => ((-1 : 𝕜) ^ (k + 1)) •
      (haarCoefficient f (2 ^ k) • haarLp 𝕜 1 (2 ^ k))) := by
    convert hp.sub hn using 1
    funext k
    simp only [Set.indicator, Set.mem_setOf_eq, Function.comp_apply]
    rw [neg_one_pow_eq_ite]
    by_cases hk : Even (k + 1) <;>
      simp only [hk, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
        one_smul, neg_one_smul, zero_sub, sub_zero]
  have ht : Tendsto (fun N => endpointTransformCLM 𝕜 N f) atTop
      (𝓝 (haarCoefficient f 0 • haarLp 𝕜 1 0 +
        ∑' k, ((-1 : 𝕜) ^ (k + 1)) •
          (haarCoefficient f (2 ^ k) • haarLp 𝕜 1 (2 ^ k)))) := by
    simpa only [endpointTransformCLM_apply] using
      tendsto_const_nhds.add hs.hasSum.tendsto_sum_nat
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ht).exists_norm_le
  exact ⟨C, fun N => hC _ (Set.mem_range_self N)⟩

/-- The L1 Haar expansion is not unconditionally summable for every input.
The proof uses the finite witnesses and Banach-Steinhaus on actual L1. -/
theorem haar_conditional : Spec.HaarConditional.{u} := by
  intro 𝕜 _
  classical
  by_contra h
  have hall : ∀ f : Lp 𝕜 1 (volume : Measure I),
      Summable (fun n => haarCoefficient f n • haarLp 𝕜 1 n) := not_exists_not.mp h
  obtain ⟨C, hC⟩ := banach_steinhaus (g := endpointTransformCLM 𝕜)
    (fun f => endpointTransformCLM_bounded_of_summable 𝕜 f (hall f))
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * C)
  have hupper : ‖endpointTransform 𝕜 N‖ ≤ C := by
    rw [← endpointTransformCLM_spike]
    exact ((endpointTransformCLM 𝕜 N).le_opNorm (endpointSpike 𝕜 N)).trans
      (by simpa [endpointSpike_norm] using hC N)
  have hlower := endpointTransform_norm_lower 𝕜 N
  linarith

/-- Pairing with a nonconstant Haar function is the difference of the two
set integrals, over both the real and complex scalar fields. -/
theorem integral_mul_haarFunction {𝕜 : Type u} [RCLike 𝕜]
    {g : I → 𝕜} (hg : Integrable g volume) {n : ℕ} (hn : n ≠ 0) :
    (∫ x, g x * haarFunction 𝕜 n x) =
      (∫ x in leftCell n, g x) - ∫ x in rightCell n, g x := by
  have heq : (fun x => g x * haarFunction 𝕜 n x) =
      (fun x => (leftCell n).indicator g x - (rightCell n).indicator g x) := by
    funext x
    by_cases hl : x ∈ leftCell n <;> by_cases hr : x ∈ rightCell n <;>
      simp [haarFunction, hn, Set.indicator, hl, hr, mul_sub]
  simp only [leftCell, rightCell] at heq ⊢
  rw [heq, integral_sub (hg.indicator (measurableSet_dyadicCell _ _))
    (hg.indicator (measurableSet_dyadicCell _ _)),
    integral_indicator (measurableSet_dyadicCell _ _),
    integral_indicator (measurableSet_dyadicCell _ _)]

/-- Zero mean on a parent and zero pairing with its Haar difference imply
zero mean on each child. -/
theorem dyadic_children_integral_zero {𝕜 : Type u} [RCLike 𝕜]
    {g : I → 𝕜} (hg : Integrable g volume) (l k : ℕ) (hk : k < 2 ^ l)
    (hparent : (∫ x in dyadicCell l k, g x) = 0)
    (hhaar : (∫ x, g x * haarFunction 𝕜 (2 ^ l + k) x) = 0) :
    (∫ x in dyadicCell (l + 1) (2 * k), g x) = 0 ∧
      (∫ x in dyadicCell (l + 1) (2 * k + 1), g x) = 0 := by
  have hi := haar_index l k hk
  have hn : 2 ^ l + k ≠ 0 := by positivity
  have hdiff := hhaar
  rw [integral_mul_haarFunction hg hn] at hdiff
  simp only [leftCell, rightCell, hi] at hdiff
  rw [dyadicCell_split, setIntegral_union (dyadicCell_disjoint _ _ _ (by omega))
    (measurableSet_dyadicCell _ _) hg.integrableOn hg.integrableOn] at hparent
  have hleft : (∫ x in dyadicCell (l + 1) (2 * k), g x) = 0 := by
    apply (mul_eq_zero.mp (show (2 : 𝕜) * (∫ x in dyadicCell (l + 1) (2 * k), g x) = 0 from ?_)).resolve_left
      (by exact_mod_cast (by decide : (2 : ℕ) ≠ 0))
    calc
      _ = ((∫ x in dyadicCell (l + 1) (2 * k), g x) +
          ∫ x in dyadicCell (l + 1) (2 * k + 1), g x) +
          ((∫ x in dyadicCell (l + 1) (2 * k), g x) -
          ∫ x in dyadicCell (l + 1) (2 * k + 1), g x) := by ring
      _ = 0 := by rw [hparent, hdiff, add_zero]
  exact ⟨hleft, by simpa only [hleft, zero_add] using hparent⟩

/-- An integrable function orthogonal to a full initial level has zero
integral on each atom of that level's dyadic partition. -/
theorem dyadic_integral_zero_of_haar {𝕜 : Type u} [RCLike 𝕜]
    {g : I → 𝕜} (hg : Integrable g volume) (N : ℕ)
    (hzero : ∀ i < N, (∫ x, g x * haarFunction 𝕜 i x) = 0)
    (l k : ℕ) (hk : k < 2 ^ l) (hl : 2 ^ l ≤ N) :
    (∫ x in dyadicCell l k, g x) = 0 := by
  induction l generalizing k with
  | zero =>
    have hk0 : k = 0 := by simpa using hk
    subst k
    have hm : (∫ x : I, g x) = 0 := by
      have hpos : 0 < N := by simp only [pow_zero] at hl; omega
      simpa [haarFunction] using hzero 0 hpos
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero
      (dyadicCell_zero_ae.mono (fun x hx hnot => (hnot hx).elim)), hm]
  | succ l ih =>
    have hkp : k / 2 < 2 ^ l := by rw [pow_succ] at hk; omega
    have hpl : 2 ^ l ≤ N := by rw [pow_succ] at hl; omega
    have hpi : 2 ^ l + k / 2 < N := by rw [pow_succ] at hl; omega
    have hchildren := dyadic_children_integral_zero hg l (k / 2) hkp
      (ih (k / 2) hkp hpl) (hzero _ hpi)
    have hsplit : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
    rcases hsplit with h | h
    · rw [h]; exact hchildren.1
    · rw [h]; exact hchildren.2

/-- Orthogonality to a prefix controls the two halves of every split in
that prefix, including a prefix that stops partway through a level. -/
theorem prefix_generators_integral_zero {𝕜 : Type u} [RCLike 𝕜]
    {g : I → 𝕜} (hg : Integrable g volume) (N : ℕ)
    (hzero : ∀ i < N, (∫ x, g x * haarFunction 𝕜 i x) = 0)
    (i : ℕ) (hi : 0 < i) (hiN : i < N) :
    (∫ x in leftCell i, g x) = 0 ∧ (∫ x in rightCell i, g x) = 0 := by
  have hp := haar_position_lt i hi
  have hlo : 2 ^ haarLevel i ≤ i := by
    simpa [haarLevel, Nat.log2_eq_log_two] using Nat.pow_log_le_self 2 hi.ne'
  have hindex : 2 ^ haarLevel i + haarPosition i = i := by
    unfold haarPosition
    omega
  have hc := dyadic_children_integral_zero hg (haarLevel i) (haarPosition i) hp
    (dyadic_integral_zero_of_haar hg N hzero _ _ hp (hlo.trans hiN.le))
    (by rw [hindex]; exact hzero i hiN)
  exact hc

/-- Any family of dyadic cells is a pi-system. -/
theorem isPiSystem_of_dyadicCells (C : Set (Set I))
    (hC : ∀ s ∈ C, ∃ l k, s = dyadicCell l k) : IsPiSystem C := by
  intro s hs t ht hst
  obtain ⟨l, j, rfl⟩ := hC s hs
  obtain ⟨m, k, rfl⟩ := hC t ht
  rcases le_total l m with h | h
  · rcases dyadicCell_subset_or_disjoint l m j k h with hsub | hd
    · rwa [Set.inter_eq_right.mpr hsub]
    · obtain ⟨x, hx, hy⟩ := hst
      exact (Set.disjoint_left.mp hd hy hx).elim
  · rcases dyadicCell_subset_or_disjoint m l k j h with hsub | hd
    · rwa [Set.inter_eq_left.mpr hsub]
    · obtain ⟨x, hx, hy⟩ := hst
      exact (Set.disjoint_left.mp hd hx hy).elim

/-- Vanishing on the prefix's generators extends to every measurable set
of the finite prefix sigma algebra by the pi-lambda theorem. -/
theorem prefix_setIntegral_zero_of_haar {𝕜 : Type u} [RCLike 𝕜]
    {g : I → 𝕜} (hg : Integrable g volume) (N : ℕ)
    (hmean : (∫ x, g x) = 0)
    (hzero : ∀ i < N, (∫ x, g x * haarFunction 𝕜 i x) = 0) :
    ∀ s, MeasurableSet[prefixSigma N] s → (∫ x in s, g x) = 0 := by
  have hpi : IsPiSystem {s | ∃ i, 0 < i ∧ i < N ∧ (s = leftCell i ∨ s = rightCell i)} := by
    apply isPiSystem_of_dyadicCells
    rintro s ⟨i, _, _, rfl | rfl⟩
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩
  apply MeasurableSpace.induction_on_inter (C := fun s _ => (∫ x in s, g x) = 0)
    rfl hpi
  · simp
  · rintro s ⟨i, hi, hiN, rfl | rfl⟩
    · exact (prefix_generators_integral_zero hg N hzero i hi hiN).1
    · exact (prefix_generators_integral_zero hg N hzero i hi hiN).2
  · intro t ht hzero
    have he := integral_add_compl (prefixSigma_le N t ht) hg
    simpa only [hzero, hmean, zero_add] using he
  · intro t hdisj ht hzero
    rw [integral_iUnion (fun i => prefixSigma_le N _ (ht i)) hdisj hg.integrableOn]
    simp only [hzero, tsum_zero]

/-- A representative of any finite Haar polynomial. -/
theorem haarSynthesis_ae (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ → 𝕜) (N : ℕ) :
    ⇑(C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) a N) =ᵐ[volume]
      fun x => ∑ i ∈ Finset.range N, a i * haarFunction 𝕜 i x := by
  have hterm (i : ℕ) : ⇑(a i • haarLp 𝕜 p i) =ᵐ[volume]
      fun x => a i * haarFunction 𝕜 i x :=
    (Lp.coeFn_smul _ _).trans ((haar_representatives 𝕜 p i).fun_comp (fun z => a i * z))
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  filter_upwards [eventuallyEq_sum (s := Finset.range N) (fun i _ => hterm i)] with x hx
  simpa only [Finset.sum_apply] using hx

theorem haarFunction_stronglyMeasurable_prefix (𝕜 : Type u) [RCLike 𝕜]
    (N i : ℕ) (hiN : i < N) : StronglyMeasurable[prefixSigma N] (haarFunction 𝕜 i) := by
  by_cases hi : i = 0
  · subst i
    change StronglyMeasurable[prefixSigma N] (fun _ : I => (1 : 𝕜))
    exact stronglyMeasurable_const
  have hl : MeasurableSet[prefixSigma N] (leftCell i) :=
    MeasurableSpace.measurableSet_generateFrom ⟨i, Nat.pos_of_ne_zero hi, hiN, Or.inl rfl⟩
  have hr : MeasurableSet[prefixSigma N] (rightCell i) :=
    MeasurableSpace.measurableSet_generateFrom ⟨i, Nat.pos_of_ne_zero hi, hiN, Or.inr rfl⟩
  have heq : haarFunction 𝕜 i =
      (leftCell i).indicator (fun _ => (1 : 𝕜)) - (rightCell i).indicator (fun _ => (1 : 𝕜)) := by
    funext x; simp [haarFunction, hi]
  rw [heq]
  exact (stronglyMeasurable_const.indicator hl).sub (stronglyMeasurable_const.indicator hr)

/-- The selected representative of a partial sum is a.e. measurable for
exactly the prefix sigma algebra, including incomplete levels. -/
theorem haarPartialSum_aestronglyMeasurable_prefix {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ) (f : Lp 𝕜 p (volume : Measure I)) :
    AEStronglyMeasurable[prefixSigma N] (haarPartialSum N f) volume := by
  have hs : StronglyMeasurable[prefixSigma N]
      (fun x => ∑ i ∈ Finset.range N, haarCoefficient f i * haarFunction 𝕜 i x) := by
    have hh := Finset.stronglyMeasurable_sum (f := fun i x =>
      haarCoefficient f i * haarFunction 𝕜 i x) (Finset.range N) (fun i hi =>
      stronglyMeasurable_const.mul
        (haarFunction_stronglyMeasurable_prefix 𝕜 N i (Finset.mem_range.mp hi)))
    convert hh using 1
    funext x
    simp only [Finset.sum_apply]
  exact hs.aestronglyMeasurable.congr (haarSynthesis_ae 𝕜 p (haarCoefficient f) N).symm

/-- Every retained Haar pairing of the residual is zero. -/
theorem haarPartialSum_residual_pairing {𝕜 : Type u} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (N : ℕ) (f : Lp 𝕜 p (volume : Measure I))
    (i : ℕ) (hi : i < N) :
    (∫ x : I, (f - haarPartialSum N f) x * haarFunction 𝕜 i x) = 0 := by
  have hc : haarCoefficient (f - haarPartialSum N f) i = 0 := by
    change haarCoefficientCLM 𝕜 p i _ = 0
    rw [map_sub, haarCoefficientCLM_apply, haarCoefficientCLM_apply]
    change haarCoefficient f i -
      haarCoefficient (C15Basis.Spec.orderedPartialSum (haarLp 𝕜 p) (haarCoefficient f) N) i = 0
    rw [haarCoefficient_partialSum, if_pos hi, sub_self]
  unfold haarCoefficient at hc
  exact (mul_eq_zero.mp hc).resolve_left (by
    split_ifs
    · exact one_ne_zero
    · exact pow_ne_zero _ (by norm_num))

/-- Identification with genuine conditional expectations, without assuming
the conclusion or restricting prefixes to complete dyadic levels. -/
theorem haar_prefixExpectation : Spec.HaarPrefixExpectation.{u} := by
  intro 𝕜 _ p _ hp N f
  by_cases hN : N = 0
  · simp [haarPartialSum, C15Basis.Spec.orderedPartialSum, prefixExpectation, hN]
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hrint := (Lp.memLp (f - haarPartialSum N f)).integrable Fact.out
  have hzero := haarPartialSum_residual_pairing N f
  have hmean : (∫ x : I, (f - haarPartialSum N f) x) = 0 := by
    simpa [haarFunction] using hzero 0 hpos
  have heq : ⇑(haarPartialSum N f) =ᵐ[volume] volume[⇑f | prefixSigma N] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq (prefixSigma_le N)
      ((Lp.memLp f).integrable Fact.out)
    · intro s hs hfin
      exact ((Lp.memLp (haarPartialSum N f)).integrable Fact.out).integrableOn
    · intro s hs hfin
      have hz := prefix_setIntegral_zero_of_haar hrint N hmean hzero s hs
      rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_sub f (haarPartialSum N f)))] at hz
      simp only [Pi.sub_apply] at hz
      rw [integral_sub ((Lp.memLp f).integrable Fact.out).integrableOn
          ((Lp.memLp (haarPartialSum N f)).integrable Fact.out).integrableOn] at hz
      exact (sub_eq_zero.mp hz).symm
    · exact haarPartialSum_aestronglyMeasurable_prefix N f
  apply Lp.ext
  rw [prefixExpectation, if_neg hN]
  exact heq.trans (MemLp.coeFn_toLp _).symm

theorem haar_contractions : Spec.HaarContractions.{u} := by
  intro 𝕜 _ p _ hp N f
  rw [haar_prefixExpectation 𝕜 p hp N f]
  exact prefixExpectation_contraction 𝕜 p N f

/-- Every cell in a completed positive level belongs to that prefix sigma
algebra. The special case l=0 is avoided because its omitted endpoint is null. -/
theorem dyadicCell_measurable_prefix (N l k : ℕ) (hl : 0 < l)
    (hk : k < 2 ^ l) (hN : 2 ^ l ≤ N) :
    MeasurableSet[prefixSigma N] (dyadicCell l k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  have hkp : k / 2 < 2 ^ m := by rw [pow_succ] at hk; omega
  let i := 2 ^ m + k / 2
  have hi : 0 < i := by dsimp [i]; positivity
  have hiN : i < N := by dsimp [i]; rw [pow_succ] at hN; omega
  have hindex := haar_index m (k / 2) hkp
  apply MeasurableSpace.measurableSet_generateFrom
  refine ⟨i, hi, hiN, ?_⟩
  have hsplit : k = 2 * (k / 2) ∨ k = 2 * (k / 2) + 1 := by omega
  rcases hsplit with h | h
  · left; simp only [leftCell, i, hindex]; exact congrArg (dyadicCell (m + 1)) h
  · right; simp only [rightCell, i, hindex]; exact congrArg (dyadicCell (m + 1)) h

/-- The left endpoint of a genuine dyadic cell, as a point of the actual
closed unit interval. -/
def dyadicSample (l : ℕ) (k : Fin (2 ^ l)) : I :=
  ⟨(k : ℝ) / 2 ^ l, by positivity, by
    apply (div_le_one (by positivity : (0 : ℝ) < 2 ^ l)).mpr
    exact_mod_cast k.isLt.le⟩

def dyadicStepLp (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(I, 𝕜)) (l : ℕ) : Lp 𝕜 p (volume : Measure I) :=
  ∑ k : Fin (2 ^ l), indicatorConstLp (s := dyadicCell l k) p
    (measurableSet_dyadicCell _ _) (measure_ne_top _ _) (f (dyadicSample l k))

theorem dyadicStepLp_ae (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : C(I, 𝕜)) (l : ℕ) :
    ⇑(dyadicStepLp 𝕜 p f l) =ᵐ[volume] fun x => ∑ k : Fin (2 ^ l),
      (dyadicCell l k).indicator (fun _ => f (dyadicSample l k)) x := by
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have hterm (k : Fin (2 ^ l)) :
      ⇑(indicatorConstLp (s := dyadicCell l k) p (measurableSet_dyadicCell _ _)
        (measure_ne_top (volume : Measure I) _) (f (dyadicSample l k))) =ᵐ[volume]
        (dyadicCell l k).indicator (fun _ => f (dyadicSample l k)) := indicatorConstLp_coeFn
  filter_upwards [eventuallyEq_sum (s := Finset.univ) (fun k _ => hterm k)] with x hx
  simpa only [Finset.sum_apply] using hx

theorem dyadicStepLp_fixed (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (f : C(I, 𝕜)) (l : ℕ) (hl : 0 < l) (N : ℕ) (hN : 2 ^ l ≤ N) :
    haarPartialSum N (dyadicStepLp 𝕜 p f l) = dyadicStepLp 𝕜 p f l := by
  have hpos : N ≠ 0 := by
    have hpow : 0 < (2 : ℕ) ^ l := by positivity
    omega
  have hs : StronglyMeasurable[prefixSigma N] (∑ k : Fin (2 ^ l),
      (dyadicCell l k).indicator (fun _ => f (dyadicSample l k))) :=
    Finset.stronglyMeasurable_sum _ fun k _ =>
      stronglyMeasurable_const.indicator (dyadicCell_measurable_prefix N l k hl k.isLt hN)
  have hmeas : AEStronglyMeasurable[prefixSigma N] (dyadicStepLp 𝕜 p f l) volume := by
    have heq : (∑ k : Fin (2 ^ l), (dyadicCell l k).indicator
        (fun _ => f (dyadicSample l k))) =ᵐ[volume] ⇑(dyadicStepLp 𝕜 p f l) := by
      filter_upwards [dyadicStepLp_ae 𝕜 p f l] with x hx
      simpa only [Finset.sum_apply] using hx.symm
    exact hs.aestronglyMeasurable.congr heq
  rw [haar_prefixExpectation 𝕜 p hp, prefixExpectation, if_neg hpos]
  apply Lp.ext
  exact (MemLp.coeFn_toLp _).trans (condExp_of_aestronglyMeasurable' (prefixSigma_le N)
    hmeas ((Lp.memLp _).integrable Fact.out))

/-- Every point except the null endpoint lies in one cell at every level. -/
theorem exists_dyadicCell (l : ℕ) (x : I) (hx : (x : ℝ) < 1) :
    ∃ k : Fin (2 ^ l), x ∈ dyadicCell l k := by
  let k : ℕ := ⌊(x : ℝ) * (2 : ℝ) ^ l⌋₊
  have hnonneg : 0 ≤ (x : ℝ) * 2 ^ l := mul_nonneg x.property.1 (by positivity)
  have hk : k < 2 ^ l := by
    dsimp [k]
    rw [Nat.floor_lt hnonneg, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [show (0 : ℝ) < 2 ^ l by positivity]
  refine ⟨⟨k, hk⟩, ?_⟩
  have hle := Nat.floor_le hnonneg
  have hlt := Nat.lt_floor_add_one ((x : ℝ) * (2 : ℝ) ^ l)
  simp only [dyadicCell, Set.mem_preimage, Set.mem_Ico, Fin.val_mk]
  constructor
  · exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ l)).mpr hle
  · exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ l)).mpr hlt

/-- The mesh size bounds the distance to the sampled left endpoint. -/
theorem dist_dyadicSample_le (l : ℕ) (k : Fin (2 ^ l)) (x : I)
    (hx : x ∈ dyadicCell l k) : dist x (dyadicSample l k) ≤ 1 / (2 : ℝ) ^ l := by
  have hxs : (k : ℝ) / 2 ^ l ≤ (x : ℝ) ∧
      (x : ℝ) < ((k : ℝ) + 1) / 2 ^ l := hx
  rw [Subtype.dist_eq, Real.dist_eq, dyadicSample, abs_of_nonneg (sub_nonneg.mpr hxs.1)]
  have he : ((k : ℝ) + 1) / 2 ^ l = (k : ℝ) / 2 ^ l + 1 / 2 ^ l := by ring
  rw [he] at hxs
  linarith [hxs.2]

/-- Uniform continuity gives arbitrarily accurate dyadic step approximations
in every Lp norm on the probability interval. -/
theorem continuous_dyadic_approximation (𝕜 : Type u) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : C(I, 𝕜)) (ε : ℝ) (hε : 0 < ε) :
    ∃ l : ℕ, 0 < l ∧
      ‖ContinuousMap.toLp p (volume : Measure I) 𝕜 f - dyadicStepLp 𝕜 p f l‖ ≤ ε := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  have hmesh : 1 / (2 : ℝ) ^ (n + 1) < δ := by
    rw [← one_div_pow]
    calc
      (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (by positivity) (by norm_num)
      _ < δ := hn
  refine ⟨n + 1, by omega, ?_⟩
  have hbound : ∀ᵐ x : I ∂volume,
      ‖(ContinuousMap.toLp p (volume : Measure I) 𝕜 f - dyadicStepLp 𝕜 p f (n + 1)) x‖ ≤ ε := by
    filter_upwards [Lp.coeFn_sub (ContinuousMap.toLp p (volume : Measure I) 𝕜 f)
      (dyadicStepLp 𝕜 p f (n + 1)),
      ContinuousMap.coeFn_toLp (p := p) (𝕜 := 𝕜) (volume : Measure I) f,
      dyadicStepLp_ae 𝕜 p f (n + 1), dyadicCell_zero_ae] with x hsub hfun hstep hx
    have hx1 : (x : ℝ) < 1 := by simpa [dyadicCell] using hx.2
    obtain ⟨k, hk⟩ := exists_dyadicCell (n + 1) x hx1
    have hval : (dyadicStepLp 𝕜 p f (n + 1)) x = f (dyadicSample (n + 1) k) := by
      rw [hstep]
      rw [Finset.sum_eq_single k]
      · exact Set.indicator_of_mem hk _
      · intro j _ hj
        have hjk : j.val ≠ k.val := fun h => hj (Fin.ext h)
        exact Set.indicator_of_notMem (Set.disjoint_left.mp
          (dyadicCell_disjoint _ _ _ hjk).symm hk) _
      · simp
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hfun, hval]
    simpa only [dist_eq_norm] using
      (hcont ((dist_dyadicSample_le _ _ x hk).trans_lt hmesh)).le
  have hh := Lp.norm_le_of_ae_bound hε.le hbound
  simpa [measureUnivNNReal, measure_univ] using hh

/-- Convergence holds along all natural-order prefixes, not only the
subsequence of completed dyadic levels. -/
theorem haar_convergence : Spec.HaarConvergence.{u} := by
  intro 𝕜 _ p _ hp f
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd := ContinuousMap.toLp_denseRange 𝕜 (volume : Measure I) 𝕜 hp
  obtain ⟨h, hh⟩ := hd.exists_dist_lt f (by linarith : 0 < ε / 4)
  rw [dist_eq_norm] at hh
  obtain ⟨l, hl, happ⟩ := continuous_dyadic_approximation 𝕜 p h (ε / 4) (by linarith)
  let g := dyadicStepLp 𝕜 p h l
  have hfg : ‖f - g‖ < ε / 2 := by
    have ht := dist_triangle f (ContinuousMap.toLp p (volume : Measure I) 𝕜 h) g
    simp only [dist_eq_norm] at ht
    dsimp [g] at ht ⊢
    linarith
  refine ⟨2 ^ l, fun N hN => ?_⟩
  have hfix : haarPartialSum N g = g := dyadicStepLp_fixed 𝕜 p hp h l hl N hN
  have hlin : haarPartialSum N f - f = haarPartialSum N (f - g) + (g - f) := by
    have hm := map_sub (haarPartialSumCLM 𝕜 p N) f g
    simp only [haarPartialSumCLM_apply, hfix] at hm
    rw [hm]
    abel
  rw [dist_eq_norm, hlin]
  calc
    ‖haarPartialSum N (f - g) + (g - f)‖ ≤ ‖haarPartialSum N (f - g)‖ + ‖g - f‖ :=
      norm_add_le _ _
    _ ≤ 2 * ‖f - g‖ := by
      rw [norm_sub_rev g f]
      linarith [haar_contractions 𝕜 p hp N (f - g)]
    _ < ε := by linarith

/-- The source Haar basis theorem on the real and complex Lebesgue Lp spaces,
with raw uniqueness and no assumed coordinates or projection bounds. -/
theorem haar_basis : Spec.HaarBasis.{u} := by
  intro 𝕜 _ p _ hp
  refine ⟨haar_nonzero 𝕜 p hp, fun f => ⟨haarCoefficient f, haar_convergence 𝕜 p hp f, ?_⟩⟩
  intro a ha
  exact haar_expansion_unique 𝕜 p ha

/-! Public construction names share the canonical independent definitions. -/
abbrev haarFunction := @Spec.haarFunction
abbrev haarLp := @Spec.haarLp
abbrev haarCoefficient := @Spec.haarCoefficient
abbrev haarPartialSum := @Spec.haarPartialSum
abbrev prefixSigma := Spec.prefixSigma
abbrev prefixExpectation := @Spec.prefixExpectation

end ExpandedFA.P1.HaarBasis
