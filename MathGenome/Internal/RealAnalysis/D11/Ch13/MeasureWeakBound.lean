import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.MeasureWeakBound
import MathGenome.Internal.RealAnalysis.D11.Ch13.FiniteBallCovering
import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import Mathlib.Topology.Instances.Rat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace D11.Ch13.MeasureWeakBound
open D11.Ch03
open Specs.D11.Ch03.LebesgueMeasures

/-- The centered measure maximal function over all positive real radii. -/
abbrev maximal : Specs.D11.Ch13.MeasureWeakBound.maximal_type :=
  Specs.D11.Ch13.MeasureWeakBound.maximal_value

/-- Lower semicontinuity uses continuity from below on smaller concentric
balls. It does not require the input measure to be absolutely continuous. -/
theorem lowerSemicontinuous_ball_mass {X : Type*} [PseudoMetricSpace X]
    [MeasurableSpace X] (μ : Measure X) (r : ℝ) :
    LowerSemicontinuous (fun x => μ (ball x r)) := by
  intro x a ha
  change a < μ (ball x r) at ha
  let S := {q : ℚ // (q : ℝ) < r}
  have hd : Directed (· ⊆ ·) (fun q : S => ball x (q : ℚ)) := by
    intro q₁ q₂
    rcases le_total q₁.val q₂.val with h | h
    · exact ⟨q₂, ball_subset_ball (by exact_mod_cast h), subset_rfl⟩
    · exact ⟨q₁, subset_rfl, ball_subset_ball (by exact_mod_cast h)⟩
  have hU : (⋃ q : S, ball x (q : ℚ)) = ball x r := by
    ext y
    simp only [mem_iUnion, mem_ball]
    constructor
    · rintro ⟨q, hq⟩
      exact hq.trans q.property
    · intro hy
      obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hy
      exact ⟨⟨q, hq₂⟩, hq₁⟩
  rw [← hU, hd.measure_iUnion] at ha
  obtain ⟨q, hq⟩ := (lt_iSup_iff).mp ha
  have hδ : 0 < r - (q.val : ℝ) := sub_pos.mpr q.property
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply hq.trans_le
  apply measure_mono
  intro z hz
  have hz' := mem_ball.mp hz
  have hy' := mem_ball.mp hy
  rw [mem_ball]
  calc
    dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
    _ < (q.val : ℝ) + (r - (q.val : ℝ)) :=
      add_lt_add hz' (by simpa only [dist_comm] using hy')
    _ = r := by ring

theorem fixed_radius_lowerSemicontinuous :
    Specs.D11.Ch13.MeasureWeakBound.fixed_radius_lowerSemicontinuous := by
  intro d _ μ _ r _
  exact lowerSemicontinuous_ball_mass μ r

/-- Lebesgue ball mass is independent of its center. -/
theorem lebesgue_ball_center (d : ℕ) [NeZero d] (x : Point d) (r : ℝ) :
    lebesgue_value d (ball x r) = lebesgue_value d (ball 0 r) := by
  change LebesgueMeasures.lebesgue d _ = LebesgueMeasures.lebesgue d _
  simp only [EuclideanRegularity.lebesgue_eq_volume]
  exact Measure.addHaar_ball_center volume x r

theorem lebesgue_ball_pos (d : ℕ) [NeZero d] (x : Point d) {r : ℝ} (hr : 0 < r) :
    0 < lebesgue_value d (ball x r) := by
  change 0 < LebesgueMeasures.lebesgue d _
  rw [EuclideanRegularity.lebesgue_eq_volume]
  exact measure_ball_pos volume x hr

theorem lebesgue_ball_ne_top (d : ℕ) [NeZero d] (x : Point d) (r : ℝ) :
    lebesgue_value d (ball x r) ≠ ∞ := by
  change LebesgueMeasures.lebesgue d _ ≠ ∞
  rw [EuclideanRegularity.lebesgue_eq_volume]
  exact measure_ball_ne_top

theorem maximal_lowerSemicontinuous :
    Specs.D11.Ch13.MeasureWeakBound.maximal_lowerSemicontinuous := by
  intro d _ μ _
  apply lowerSemicontinuous_biSup
  intro r hr
  simp_rw [lebesgue_ball_center]
  exact (ENNReal.continuous_div_const _ (lebesgue_ball_pos d 0 hr).ne').comp_lowerSemicontinuous
    (lowerSemicontinuous_ball_mass μ r) (fun a b hab => ENNReal.div_le_div_right hab _)

theorem maximal_measurable : Specs.D11.Ch13.MeasureWeakBound.maximal_measurable := by
  intro d _ μ _
  constructor
  · exact (maximal_lowerSemicontinuous d μ).measurable
  · let : MeasurableSpace (Point d) := LebesgueMeasures.lebesgueSpace d
    let := EuclideanRegularity.opensMeasurable d
    exact (maximal_lowerSemicontinuous d μ).measurable

/-- Compact subsets of a strict maximal level set satisfy the quantitative
estimate by finite disjoint ball selection. -/
theorem compact_weak_bound {d : ℕ} [NeZero d] (μ : Measure (Point d))
    (α : ℝ) (hα : 0 < α) (K : Set (Point d)) (hK : IsCompact K)
    (hKsub : ∀ x ∈ K, ENNReal.ofReal α < maximal d μ x) :
    lebesgue_value d K ≤ (3 : ℝ≥0∞) ^ d * μ univ / ENNReal.ofReal α := by
  classical
  have hw : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      ENNReal.ofReal α < μ (ball x.val r) / lebesgue_value d (ball x.val r) := by
    intro x
    have hx := hKsub x.val x.property
    change ENNReal.ofReal α < ⨆ (r : ℝ) (_ : 0 < r),
      μ (ball x.val r) / lebesgue_value d (ball x.val r) at hx
    obtain ⟨r, hx⟩ := lt_iSup_iff.mp hx
    obtain ⟨hr, hx⟩ := lt_iSup_iff.mp hx
    exact ⟨r, hr, hx⟩
  choose r hr hratio using hw
  have hcover : K ⊆ ⋃ x : K, ball x.val (r x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => ball x.val (r x))
    (fun _ => isOpen_ball) hcover
  obtain ⟨t, hts, htd, _, htm⟩ :=
    FiniteBallCovering.finite_ball_covering d s (fun x : K => x.val) r (fun x _ => hr x)
  have hα0 : ENNReal.ofReal α ≠ 0 := (ENNReal.ofReal_pos.mpr hα).ne'
  have hvol (x : K) : lebesgue_value d (ball x.val (r x)) ≤
      μ (ball x.val (r x)) / ENNReal.ofReal α := by
    apply (ENNReal.le_div_iff_mul_le (.inl hα0) (.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    exact ((ENNReal.lt_div_iff_mul_lt
      (.inl (lebesgue_ball_pos d x.val (hr x)).ne')
      (.inl (lebesgue_ball_ne_top d x.val (r x)))).mp (hratio x)).le
  have hmass : ∑ x ∈ t, μ (ball x.val (r x)) ≤ μ univ := by
    rw [← measure_biUnion_finset htd (fun _ _ => isOpen_ball.measurableSet)]
    exact measure_mono (subset_univ _)
  calc
    lebesgue_value d K ≤ lebesgue_value d (⋃ x ∈ s, ball x.val (r x)) := measure_mono hs
    _ ≤ (3 : ℝ≥0∞) ^ d * ∑ x ∈ t, lebesgue_value d (ball x.val (r x)) := htm
    _ ≤ (3 : ℝ≥0∞) ^ d * ∑ x ∈ t,
        (μ (ball x.val (r x)) / ENNReal.ofReal α) := by
      exact mul_le_mul' (le_refl _) (Finset.sum_le_sum (fun x _ => hvol x))
    _ = (3 : ℝ≥0∞) ^ d * (∑ x ∈ t, μ (ball x.val (r x))) / ENNReal.ofReal α := by
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
    _ ≤ (3 : ℝ≥0∞) ^ d * μ univ / ENNReal.ofReal α := by
      exact ENNReal.div_le_div_right (mul_le_mul' (le_refl _) hmass) _

/-- The finite-measure weak (1,1) estimate, on the completed Lebesgue domain. -/
theorem measure_weak_bound : Specs.D11.Ch13.MeasureWeakBound.measure_weak_bound := by
  intro d _ μ _ α hα
  let E : Set (Point d) := {x | ENNReal.ofReal α < maximal d μ x}
  have hE : IsOpen E := (maximal_lowerSemicontinuous d μ).isOpen_preimage _
  have hEm : MeasurableSet[LebesgueMeasures.lebesgueSpace d] E :=
    LebesgueMeasures.native_borel_le d E hE.measurableSet
  have hinner := EuclideanRegularity.inner_regularity d E hEm
  change lebesgue_value d E ≤ _
  rw [hinner]
  refine iSup_le fun K => iSup_le fun hKE => iSup_le fun hK => ?_
  exact compact_weak_bound μ α hα K hK (fun x hx => hKE hx)

end D11.Ch13.MeasureWeakBound
