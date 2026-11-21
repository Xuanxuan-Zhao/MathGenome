import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.DeLaValleePoussin
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExpandedFA.PartIV.DeLaValleePoussin

/-- The positive part used in the constructive proof. -/
def hinge (r t : ℝ) : ℝ := max 0 (t - r)

lemma hinge_nonneg (r t : ℝ) : 0 ≤ hinge r t := le_max_left _ _

lemma hinge_monotone (r : ℝ) : Monotone (hinge r) := by
  intro x y h
  exact max_le_max le_rfl (sub_le_sub_right h r)

lemma hinge_convex (r : ℝ) : ConvexOn ℝ univ (hinge r) := by
  exact (convexOn_const 0 convex_univ).sup
    ((convexOn_id convex_univ).add_const (-r))

/-- The series is locally finite when the thresholds dominate their indices. -/
lemma hinge_summable {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) (t : ℝ) :
    Summable (fun n => hinge (R n) t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hn' : N ≤ n := by simpa using hn
  have : t ≤ R n := (le_of_lt hN).trans ((show (N : ℝ) ≤ (n : ℝ) by exact_mod_cast hn').trans (hR n))
  exact max_eq_left (sub_nonpos.mpr this)

/-- The growth function in the manuscript. -/
def hingeSeries (R : ℕ → ℝ) (t : ℝ) : ℝ := ∑' n, hinge (R n) t

lemma hingeSeries_nonneg (R : ℕ → ℝ) (t : ℝ) : 0 ≤ hingeSeries R t :=
  tsum_nonneg (fun _ => hinge_nonneg _ _)

lemma hingeSeries_monotone {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    Monotone (hingeSeries R) := by
  intro x y h
  exact (hinge_summable hR x).tsum_le_tsum (fun n => hinge_monotone _ h)
    (hinge_summable hR y)

lemma hingeSeries_convex {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    ConvexOn ℝ univ (hingeSeries R) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hsum := ((hinge_summable hR x).mul_left a).add
    ((hinge_summable hR y).mul_left b)
  calc
    hingeSeries R (a • x + b • y) ≤ ∑' n, (a * hinge (R n) x + b * hinge (R n) y) :=
      (hinge_summable hR _).tsum_le_tsum
        (fun n => (hinge_convex (R n)).2 (mem_univ x) (mem_univ y) ha hb hab) hsum
    _ = a • hingeSeries R x + b • hingeSeries R y := by
      rw [Summable.tsum_add ((hinge_summable hR x).mul_left a)
        ((hinge_summable hR y).mul_left b), tsum_mul_left, tsum_mul_left]
      rfl

lemma hingeSeries_continuous {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    Continuous (hingeSeries R) :=
  continuousOn_univ.mp ((hingeSeries_convex hR).continuousOn isOpen_univ)

/-- Each finite collection of hinges supplies an eventual linear lower bound. -/
lemma hingeSeries_superlinear {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    Tendsto (fun t => hingeSeries R t / t) atTop atTop := by
  apply tendsto_atTop.2
  intro c
  obtain ⟨N, hN⟩ := exists_nat_gt (c + 1)
  let S := ∑ n ∈ Finset.range N, R n
  apply eventually_atTop.2
  refine ⟨max 1 S, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hSt : S ≤ t := (le_max_right _ _).trans ht
  have hsum : (N : ℝ) * t - S ≤ hingeSeries R t := by
    calc
      (N : ℝ) * t - S = ∑ n ∈ Finset.range N, (t - R n) := by
        simp [S, Finset.sum_sub_distrib, mul_comm]
      _ ≤ ∑ n ∈ Finset.range N, hinge (R n) t :=
        Finset.sum_le_sum (fun n _ => le_max_right 0 _)
      _ ≤ hingeSeries R t :=
        (hinge_summable hR t).sum_le_tsum _ (fun n _ => hinge_nonneg _ _)
  apply (le_div_iff₀ (by linarith : 0 < t)).2
  nlinarith

lemma hingeSeries_growth {R : ℕ → ℝ} (hR : ∀ n : ℕ, (n : ℝ) ≤ R n) :
    DeLaValleePoussinSpec.GrowthFunction (hingeSeries R) :=
  ⟨(hingeSeries_continuous hR).continuousOn, (hingeSeries_monotone hR).monotoneOn _,
    (hingeSeries_convex hR).subset (subset_univ _) (convex_Ici _),
    fun t _ => hingeSeries_nonneg R t, hingeSeries_superlinear hR⟩

variable {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {f : ι → X → E}

/-- The construction uses no positivity of the total mass and no family member. -/
theorem growth_bound_of_uniformIntegrable (h : UniformIntegrable f 1 μ) :
    DeLaValleePoussinSpec.HasGrowthBound μ f := by
  have heps (n : ℕ) : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    exact ENNReal.ofReal_pos.mpr (by positivity)
  choose C hC using fun n : ℕ => h.spec one_ne_zero ENNReal.one_ne_top (heps n)
  let R : ℕ → ℝ := fun n => max (n : ℝ) (C n : ℝ)
  have hR : ∀ n : ℕ, (n : ℝ) ≤ R n := fun n => le_max_left _ _
  have hR0 (n : ℕ) : 0 ≤ R n := (Nat.cast_nonneg n).trans (hR n)
  have htail (i : ι) (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (hinge (R n) ‖f i x‖) ∂μ) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    have hm : NullMeasurableSet {x | C n ≤ ‖f i x‖₊} μ :=
      nullMeasurableSet_le aemeasurable_const (h.aestronglyMeasurable i).nnnorm.aemeasurable
    apply le_trans (b := eLpNorm ({x | C n ≤ ‖f i x‖₊}.indicator (f i)) 1 μ) _ (hC n i)
    rw [eLpNorm_one_eq_lintegral_enorm ((h.aestronglyMeasurable i).indicator₀ hm)]
    apply lintegral_mono
    intro x
    change ENNReal.ofReal (hinge (R n) ‖f i x‖) ≤
      ‖{x | C n ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ
    by_cases hx : C n ≤ ‖f i x‖₊
    · rw [Set.indicator_of_mem (s := {x | C n ≤ ‖f i x‖₊}) hx, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      exact max_le (norm_nonneg _) (sub_le_self _ (hR0 n))
    · rw [Set.indicator_of_notMem (s := {x | C n ≤ ‖f i x‖₊}) hx, enorm_zero]
      have hnorm : ‖f i x‖ ≤ R n := by
        have : ‖f i x‖ < (C n : ℝ) := by exact_mod_cast (lt_of_not_ge hx)
        exact this.le.trans (le_max_right _ _)
      simp [hinge, max_eq_left (sub_nonpos.mpr hnorm)]
  refine ⟨hingeSeries R, hingeSeries_growth hR, 2, ?_⟩
  intro i
  calc
    (∫⁻ x, ENNReal.ofReal (hingeSeries R ‖f i x‖) ∂μ) =
        ∑' n, ∫⁻ x, ENNReal.ofReal (hinge (R n) ‖f i x‖) ∂μ := by
      simp only [hingeSeries,
        ENNReal.ofReal_tsum_of_nonneg (fun n => hinge_nonneg _ _) (hinge_summable hR _)]
      apply lintegral_tsum
      intro n
      exact ((continuous_const.max (continuous_id.sub continuous_const)).comp_aestronglyMeasurable
        (h.aestronglyMeasurable i).norm).aemeasurable.ennreal_ofReal
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ n) :=
      ENNReal.tsum_le_tsum (htail i)
    _ = 2 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two,
        tsum_geometric_two]
      norm_num

/-- Superlinear growth controls all large-value tails. Finiteness of the ambient
measure is used only to turn that tail control into the full L¹ bound. -/
theorem uniformIntegrable_of_growth_bound [IsFiniteMeasure μ]
    (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (h : DeLaValleePoussinSpec.HasGrowthBound μ f) : UniformIntegrable f 1 μ := by
  rcases h with ⟨G, hG, C, hC⟩
  apply uniformIntegrable_of le_rfl ENNReal.one_ne_top hf
  intro η hη
  obtain ⟨ε, hε0, hεη⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hη
  have hε : 0 < (ε : ℝ) := by exact_mod_cast hε0
  let δ : ℝ := (ε : ℝ) / ((C : ℝ) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨r, hr⟩ := eventually_atTop.1 (hG.2.2.2.2.eventually (eventually_ge_atTop δ⁻¹))
  let T : ℝ≥0 := ⟨max 1 r, (zero_le_one.trans (le_max_left _ _))⟩
  refine ⟨T, ?_⟩
  intro i
  have hT (x : X) (hx : T ≤ ‖f i x‖₊) : ‖f i x‖ ≤ δ * G ‖f i x‖ := by
    have hx' : max 1 r ≤ ‖f i x‖ := by exact_mod_cast hx
    have hpos : 0 < ‖f i x‖ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hx')
    have hg : δ⁻¹ * ‖f i x‖ ≤ G ‖f i x‖ :=
      (le_div_iff₀ hpos).mp (hr _ ((le_max_right _ _).trans hx'))
    calc
      ‖f i x‖ = δ * (δ⁻¹ * ‖f i x‖) := by rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
      _ ≤ δ * G ‖f i x‖ := mul_le_mul_of_nonneg_left hg hδ.le
  have hm : NullMeasurableSet {x | T ≤ ‖f i x‖₊} μ :=
    nullMeasurableSet_le aemeasurable_const (hf i).nnnorm.aemeasurable
  rw [eLpNorm_one_eq_lintegral_enorm ((hf i).indicator₀ hm)]
  calc
    (∫⁻ x, ‖{x | T ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ∂μ) ≤
        ∫⁻ x, ENNReal.ofReal (δ * G ‖f i x‖) ∂μ := by
      apply lintegral_mono
      intro x
      change ‖{x | T ≤ ‖f i x‖₊}.indicator (f i) x‖ₑ ≤ ENNReal.ofReal (δ * G ‖f i x‖)
      by_cases hx : T ≤ ‖f i x‖₊
      · rw [Set.indicator_of_mem (s := {x | T ≤ ‖f i x‖₊}) hx, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hT x hx)
      · rw [Set.indicator_of_notMem (s := {x | T ≤ ‖f i x‖₊}) hx, enorm_zero]
        exact bot_le
    _ = ENNReal.ofReal δ * ∫⁻ x, ENNReal.ofReal (G ‖f i x‖) ∂μ := by
      simp_rw [ENNReal.ofReal_mul hδ.le]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal δ * (C : ℝ≥0∞) := by gcongr; exact hC i
    _ ≤ ENNReal.ofReal (ε : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hδ.le]
      apply ENNReal.ofReal_le_ofReal
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (C : ℝ) + 1)).2
      nlinarith
    _ ≤ η := by simpa using hεη.le

/-- De la Vallée–Poussin's criterion, including empty families and zero mass. -/
theorem criterion : DeLaValleePoussinSpec.Criterion := by
  intro X 𝕂 _ _ μ _ F
  constructor
  · rintro ⟨⟨C, hC⟩, hUI⟩
    apply growth_bound_of_uniformIntegrable
    refine ⟨hUI, C, ?_⟩
    intro f
    rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (hC f.1 f.2)
  · intro h
    have hUI := uniformIntegrable_of_growth_bound (fun f : F => Lp.aestronglyMeasurable f.1) h
    obtain ⟨C, hC⟩ := hUI.2
    refine ⟨⟨C, ?_⟩, hUI.1⟩
    intro f hf
    have hCf := hC ⟨f, hf⟩
    rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal] at hCf
    exact (ENNReal.ofReal_le_ofReal_iff C.coe_nonneg).mp hCf

end ExpandedFA.PartIV.DeLaValleePoussin
