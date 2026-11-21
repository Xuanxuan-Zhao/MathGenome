import MathGenome.Internal.RealAnalysis.D11.Ch13.AveragesMaximalDefinition
import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.RegularShrinking
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 2000000
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace D11.Ch13.RegularShrinking
open D11.Ch03 D11.Ch06 AveragesMaximalDefinition

private theorem native_ball_scaling {n : ℕ} (x z : Point n) (r k : ℝ) (hk : 0 < k) :
    (volume : Measure (Point n)) (Metric.ball x (k * r)) =
      ENNReal.ofReal (k ^ n) * (volume : Measure (Point n)) (Metric.ball z r) := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin,
    Measure.addHaar_ball_center volume z r] using
    Measure.addHaar_ball_mul_of_pos (volume : Measure (Point n)) x hk r

/-- The cube is closed even when its side length is zero or negative. -/
lemma closedCube_isClosed {n : ℕ} (e : Point n ≃ᵢ Point n) (s : ℝ) :
    IsClosed (closedCube e s) := by
  apply e.toHomeomorph.isClosedMap
  simp only [ofPred_forall]
  exact isClosed_iInter (fun j => isClosed_le (EuclideanSpace.proj j).continuous.abs
    continuous_const)

private theorem native_cube_measurable {n : ℕ} (e : Point n ≃ᵢ Point n) (s : ℝ) :
    MeasurableSet (closedCube e s) := (closedCube_isClosed e s).measurableSet

local instance (n : ℕ) [NeZero n] : MeasurableSpace (Point n) := LebesgueMeasures.lebesgueSpace n
variable {n : ℕ} [NeZero n]

private theorem ball_eq_borel (x : Point n) (r : ℝ) :
    LebesgueMeasures.lebesgue n (Metric.ball x r) =
      LebesgueMeasures.borelMeasure n (Metric.ball x r) :=
  (LebesgueMeasures.lebesgue_apply n _ (ball_measurable x r)).trans
    (LebesgueMeasures.native_outer_agreement n _).symm

lemma ball_scaling (x z : Point n) (r k : ℝ) (hk : 0 < k) :
    LebesgueMeasures.lebesgue n (Metric.ball x (k * r)) =
      ENNReal.ofReal (k ^ n) * LebesgueMeasures.lebesgue n (Metric.ball z r) := by
  rw [ball_eq_borel, ball_eq_borel]
  exact native_ball_scaling x z r k hk

lemma ball_real_scaling (x z : Point n) (r k : ℝ) (hk : 0 < k) :
    (LebesgueMeasures.lebesgue n (Metric.ball x (k * r))).toReal =
      k ^ n * (LebesgueMeasures.lebesgue n (Metric.ball z r)).toReal := by
  rw [ball_scaling x z r k hk, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hk.le n)]

lemma subset_centered_ball {x z : Point n} {r : ℝ} (hx : x ∈ Metric.ball z r) :
    Metric.ball z r ⊆ Metric.ball x (2 * r) := by
  intro y hy
  have h := dist_triangle y z x
  have hx' : dist z x < r := by simpa only [Metric.mem_ball, dist_comm] using hx
  have hy' : dist y z < r := hy
  show dist y x < 2 * r
  linarith

lemma integrableOn_subset_ball {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : Point n → 𝕜) (hf : locallyIntegrable f) {E : Set (Point n)}
    {z : Point n} {r : ℝ} (hE : E ⊆ Metric.ball z r) :
    IntegrableOn f E (LebesgueMeasures.lebesgue n) :=
by
  have hb : IntegrableOn f (Metric.ball z r) (LebesgueMeasures.lebesgue n) :=
    ((ScalarIntegral.scalarIntegrable_iff _ _).mp (scalarIntegrable_ball f hf z r)).2
  exact hb.mono_set hE

lemma setMean_formula {𝕜 : Type} [RCLike 𝕜]
    (f : Point n → 𝕜) (E : Set (Point n)) :
    setMean f E = (LebesgueMeasures.lebesgue n E).toReal⁻¹ •
      ∫ y in E, f y ∂(LebesgueMeasures.lebesgue n) := rfl

/-- Pure integral comparison; no differentiation theorem is used. -/
lemma mean_comparison {g : Point n → ℝ} {S T : Set (Point n)} {K : ℝ}
    (hST : S ⊆ T)
    (hg : IntegrableOn g T (LebesgueMeasures.lebesgue n))
    (hgn : ∀ y, 0 ≤ g y)
    (hSp : 0 < (LebesgueMeasures.lebesgue n S).toReal)
    (hTp : 0 < (LebesgueMeasures.lebesgue n T).toReal)
    (hvol : (LebesgueMeasures.lebesgue n T).toReal ≤
      K * (LebesgueMeasures.lebesgue n S).toReal) :
    setMean g S ≤ K * setMean g T := by
  have hi : (∫ y in S, g y ∂(LebesgueMeasures.lebesgue n)) ≤
      ∫ y in T, g y ∂(LebesgueMeasures.lebesgue n) :=
    setIntegral_mono_set hg (Filter.Eventually.of_forall hgn) (Filter.Eventually.of_forall hST)
  have ht : 0 ≤ ∫ y in T, g y ∂(LebesgueMeasures.lebesgue n) :=
    integral_nonneg hgn
  simp only [setMean_formula, smul_eq_mul]
  rw [← div_eq_inv_mul, ← div_eq_inv_mul]
  apply (div_le_iff₀ hSp).mpr
  calc
    _ ≤ (K * (LebesgueMeasures.lebesgue n S).toReal) *
        (∫ y in T, g y ∂(LebesgueMeasures.lebesgue n)) /
        (LebesgueMeasures.lebesgue n T).toReal := by
      apply (le_div_iff₀ hTp).mpr
      nlinarith [mul_le_mul_of_nonneg_left hvol ht,
        mul_le_mul_of_nonneg_right hi hTp.le]
    _ = _ := by ring

lemma mean_sub_const {𝕜 : Type} [RCLike 𝕜]
    (f : Point n → 𝕜) (a : 𝕜) (S : Set (Point n))
    (hf : IntegrableOn f S (LebesgueMeasures.lebesgue n))
    (hS₀ : LebesgueMeasures.lebesgue n S ≠ 0)
    (hStop : LebesgueMeasures.lebesgue n S ≠ ∞) :
    setMean (fun y => f y - a) S = setMean f S - a := by
  have hp : (LebesgueMeasures.lebesgue n S).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hS₀, hStop⟩
  simp only [setMean_formula]
  rw [integral_sub hf (integrableOn_const hStop), integral_const, smul_sub]
  simp only [Measure.restrict_apply_univ, measureReal_def, smul_smul,
    inv_mul_cancel₀ hp, one_smul]

lemma norm_mean_le {𝕜 : Type} [RCLike 𝕜]
    (f : Point n → 𝕜) (S : Set (Point n)) :
    ‖setMean f S‖ ≤ setMean (fun y => ‖f y‖) S := by
  simp only [setMean_formula, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- Regular shrinking at a fixed Lebesgue point, for any indexing filter. -/
theorem regular_shrinking : Specs.D11.Ch13.RegularShrinking.regular_shrinking.{u} := by
  intro n _ 𝕜 _ _ _ f hf x hx ι l E z r c hc hEm hEB hxb hrlim hfrac
  change (∀ i, ENNReal.ofReal c *
    LebesgueMeasures.lebesgue n (Metric.ball (z i) (r i)) ≤
    LebesgueMeasures.lebesgue n (E i)) at hfrac
  change locallyIntegrable f at hf
  change lebesguePoint f hf x at hx
  have hr (i : ι) : 0 < r i := lt_of_le_of_lt dist_nonneg (hxb i)
  have hfin (i : ι) : LebesgueMeasures.lebesgue n (E i) < ∞ :=
    lt_of_le_of_lt (measure_mono (hEB i)) (ball_measure (z i) (r i) (hr i)).2.1
  have hpos (i : ι) : 0 < LebesgueMeasures.lebesgue n (E i) :=
    lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne'
      (ball_measure (z i) (r i) (hr i)).1.ne') (hfrac i)
  have hrealpos (i : ι) : 0 < (LebesgueMeasures.lebesgue n (E i)).toReal :=
    ENNReal.toReal_pos (hpos i).ne' (hfin i).ne
  have hint (i : ι) := integrableOn_subset_ball f hf (hEB i)
  let g : Point n → ℝ := fun y => ‖f y - f x‖
  have hg : locallyIntegrable g :=
    locallyIntegrable_norm _ (locallyIntegrable_sub_const f hf (f x))
  have hEr (i : ι) : E i ⊆ Metric.ball x (2 * r i) :=
    (hEB i).trans (subset_centered_ball (hxb i))
  have hbound (i : ι) : setMean g (E i) ≤ (2 ^ n / c) *
      setMean g (Metric.ball x (2 * r i)) := by
    have hfracR : c * (LebesgueMeasures.lebesgue n (Metric.ball (z i) (r i))).toReal ≤
        (LebesgueMeasures.lebesgue n (E i)).toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le] using
        ENNReal.toReal_mono (hfin i).ne (hfrac i)
    apply mean_comparison (hEr i)
      (integrableOn_subset_ball g hg (Subset.rfl)) (fun _ => norm_nonneg _)
      (hrealpos i) (ball_measure x (2 * r i) (mul_pos (by norm_num) (hr i))).2.2
    calc
      _ = 2 ^ n * (LebesgueMeasures.lebesgue n (Metric.ball (z i) (r i))).toReal :=
        ball_real_scaling x (z i) (r i) 2 (by norm_num)
      _ ≤ 2 ^ n * ((LebesgueMeasures.lebesgue n (E i)).toReal / c) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) n)
        exact (le_div_iff₀ hc).mpr (by nlinarith [hfracR])
      _ = _ := by ring
  have hrlim' : Tendsto (fun i => 2 * r i) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using hrlim.const_mul 2, ?_⟩
    exact Filter.Eventually.of_forall (fun i => mul_pos (by norm_num) (hr i))
  have hball : Tendsto (fun i => setMean g (Metric.ball x (2 * r i))) l (𝓝 0) :=
    hx.comp hrlim'
  have hupper := hball.const_mul (2 ^ n / c)
  simp only [mul_zero] at hupper
  have hosc : Tendsto (fun i => setMean g (E i)) l (𝓝 0) := by
    apply squeeze_zero (fun i => ?_) hbound hupper
    exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg (fun _ => norm_nonneg _))
  refine ⟨fun i => ⟨hpos i, hfin i, hint i⟩, hosc, ?_⟩
  have hdiff : Tendsto (fun i => setMean f (E i) - f x) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_) hosc
    rw [← mean_sub_const f (f x) (E i) (hint i) (hpos i).ne' (hfin i).ne]
    exact norm_mean_le _ _
  simpa only [zero_add, sub_add_cancel] using hdiff.add_const (f x)

lemma closedCube_measurable (e : Point n ≃ᵢ Point n) (s : ℝ) :
    MeasurableSet (closedCube e s) :=
  LebesgueMeasures.native_borel_le n _ (native_cube_measurable e s)

/-- The open inscribed ball is contained in the closed cube. -/
lemma ball_subset_closedCube (e : Point n ≃ᵢ Point n) (s : ℝ) :
    Metric.ball (e 0) (s / 2) ⊆ closedCube e s := by
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have hd : ‖e.symm y‖ < s / 2 := by
    rw [← dist_zero_right, ← e.dist_eq, e.apply_symm_apply]
    exact hy
  intro j
  exact (show |(e.symm y) j| ≤ ‖e.symm y‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e.symm y) j).trans hd.le

/-- A deliberately loose dimensional radius avoids any issue with boundary
points of a circumscribed open ball. -/
lemma closedCube_subset_ball (e : Point n ≃ᵢ Point n) {s : ℝ} (hs : 0 < s) :
    closedCube e s ⊆ Metric.ball (e 0) (((n : ℝ) + 1) * s) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Metric.mem_ball, e.dist_eq, dist_zero_right]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsq : ‖y‖ ^ 2 ≤ (n : ℝ) * (s / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin n, (s / 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_sq).mpr (by simpa only [abs_of_pos (half_pos hs)] using hy j)
      _ = _ := by simp
  have hp : 0 < ((n : ℝ) + 1) * s := mul_pos (by positivity) hs
  have haux : 0 ≤ ((n : ℝ) ^ 2 + n + 1) * s ^ 2 := by positivity
  nlinarith [sq_nonneg (s / 2), sq_nonneg ((n : ℝ) * s), mul_pos hs hs]

/-- A fixed positive fraction of the enclosing ball lies in every cube. -/
lemma closedCube_volume_ratio (e : Point n ≃ᵢ Point n) (s : ℝ) :
    ENNReal.ofReal (((2 * ((n : ℝ) + 1)) ^ n)⁻¹) *
        LebesgueMeasures.lebesgue n (Metric.ball (e 0) (((n : ℝ) + 1) * s)) ≤
      LebesgueMeasures.lebesgue n (closedCube e s) := by
  have hk : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have heq : ((n : ℝ) + 1) * s = (2 * ((n : ℝ) + 1)) * (s / 2) := by ring
  rw [heq, ball_scaling (e 0) (e 0) (s / 2) _ hk, ← mul_assoc]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hk.le n)),
    inv_mul_cancel₀ (pow_pos hk n).ne', ENNReal.ofReal_one, one_mul]
  exact measure_mono (ball_subset_closedCube e s)

/-- Shrinking cubes, allowing arbitrary changing orientations. -/
theorem cubes_shrinking : Specs.D11.Ch13.RegularShrinking.cubes_shrinking.{u} := by
  intro n _ 𝕜 _ _ _ f hf x hx ι l e s hs hxs hslim
  let c : ℝ := ((2 * ((n : ℝ) + 1)) ^ n)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have h := regular_shrinking f hf x hx l (fun i => closedCube (e i) (s i))
    (fun i => e i 0) (fun i => ((n : ℝ) + 1) * s i) c hc
    (fun i => closedCube_measurable (e i) (s i))
    (fun i => closedCube_subset_ball (e i) (hs i))
    (fun i => closedCube_subset_ball (e i) (hs i) (hxs i))
    (by simpa using hslim.const_mul ((n : ℝ) + 1))
    (fun i => closedCube_volume_ratio (e i) (s i))
  exact ⟨fun i => ⟨closedCube_measurable (e i) (s i), h.1 i⟩, h.2⟩

lemma ball_subset_openCube (e : Point n ≃ᵢ Point n) (s : ℝ) :
    Metric.ball (e 0) (s / 2) ⊆ openCube e s := by
  intro y hy
  refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
  have hd : ‖e.symm y‖ < s / 2 := by
    rw [← dist_zero_right, ← e.dist_eq, e.apply_symm_apply]
    exact hy
  intro j
  have hcoord : |(e.symm y) j| ≤ ‖e.symm y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e.symm y) j
  exact hcoord.trans_lt hd

lemma cube_volume_ratio (e : Point n ≃ᵢ Point n) (s : ℝ)
    {Q : Set (Point n)} (hQ : openCube e s ⊆ Q) :
    ENNReal.ofReal (((2 * ((n : ℝ) + 1)) ^ n)⁻¹) *
        LebesgueMeasures.lebesgue n (Metric.ball (e 0) (((n : ℝ) + 1) * s)) ≤
      LebesgueMeasures.lebesgue n Q := by
  have hk : 0 < 2 * ((n : ℝ) + 1) := by positivity
  have heq : ((n : ℝ) + 1) * s = (2 * ((n : ℝ) + 1)) * (s / 2) := by ring
  rw [heq, ball_scaling (e 0) (e 0) (s / 2) _ hk, ← mul_assoc]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hk.le n)),
    inv_mul_cancel₀ (pow_pos hk n).ne', ENNReal.ofReal_one, one_mul]
  exact measure_mono ((ball_subset_openCube e s).trans hQ)

/-- All usual boundary conventions for Euclidean cubes obey the same
regular-shrinking theorem. -/
theorem cube_families_shrinking :
    Specs.D11.Ch13.RegularShrinking.cube_families_shrinking.{u} := by
  intro n _ 𝕜 _ _ _ f hf x hx ι l Q e s hs hQm hinner houter hxQ hslim
  let c : ℝ := ((2 * ((n : ℝ) + 1)) ^ n)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  exact regular_shrinking f hf x hx l Q (fun i => e i 0)
    (fun i => ((n : ℝ) + 1) * s i) c hc hQm
    (fun i => (houter i).trans (closedCube_subset_ball (e i) (hs i)))
    (fun i => closedCube_subset_ball (e i) (hs i) (houter i (hxQ i)))
    (by simpa using hslim.const_mul ((n : ℝ) + 1))
    (fun i => cube_volume_ratio (e i) (s i) (hinner i))

end D11.Ch13.RegularShrinking
