import MathGenome.Internal.RealAnalysis.D11.Ch03.TranslationDilation
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch13.FiniteBallCovering
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Metric MeasureTheory
open scoped ENNReal BigOperators Pointwise

namespace D11.Ch13.FiniteBallCovering

/-- An intersecting ball with no greater radius lies in the triple ball. -/
theorem ball_subset_triple_of_inter {X : Type*} [PseudoMetricSpace X]
    {a b : X} {s r : ℝ} (hsr : s ≤ r)
    (h : (ball a s ∩ ball b r).Nonempty) :
    ball a s ⊆ ball b (3 * r) := by
  have hdist := dist_lt_add_of_nonempty_ball_inter_ball h
  apply ball_subset_ball'
  linarith

/-- Finite greedy selection, valid in any pseudometric space. The stronger
per-ball containment records why every discarded ball is covered. -/
theorem finite_ball_selection {X ι : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (c : ι → X) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) :
    ∃ t : Finset ι, t ⊆ s ∧
      (↑t : Set ι).PairwiseDisjoint (fun i => ball (c i) (r i)) ∧
      ∀ i ∈ s, ∃ j ∈ t, ball (c i) (r i) ⊆ ball (c j) (3 * r j) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨∅, by simp⟩
    obtain ⟨a, ha, hmax⟩ := s.exists_max_image r hs
    let q := s.filter (fun i => Disjoint (ball (c i) (r i)) (ball (c a) (r a)))
    have hqs : q ⊆ s := Finset.filter_subset _ _
    have haq : a ∉ q := by
      intro h
      have hd := (Finset.mem_filter.mp h).2
      exact (Metric.nonempty_ball.mpr (hr a ha)).ne_empty (disjoint_self.mp hd)
    have hqss : q ⊂ s := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hqs, by
        intro h
        exact haq (h ▸ ha)⟩
    obtain ⟨t, htq, htd, htc⟩ := ih q hqss (fun i hi => hr i (hqs hi))
    refine ⟨insert a t, ?_, ?_, ?_⟩
    · exact Finset.insert_subset_iff.mpr ⟨ha, htq.trans hqs⟩
    · rw [Finset.coe_insert]
      exact htd.insert (fun b hb _ => ((Finset.mem_filter.mp (htq hb)).2).symm)
    · intro i hi
      by_cases hiq : i ∈ q
      · obtain ⟨j, hj, hc⟩ := htc i hiq
        exact ⟨j, Finset.mem_insert_of_mem hj, hc⟩
      · have hnd : ¬ Disjoint (ball (c i) (r i)) (ball (c a) (r a)) := by
          intro hd
          exact hiq (Finset.mem_filter.mpr ⟨hi, hd⟩)
        exact ⟨a, Finset.mem_insert_self _ _,
          ball_subset_triple_of_inter (hmax i hi)
            (Set.not_disjoint_iff_nonempty_inter.mp hnd)⟩

open D11.Ch03

/-- Translating a dilated origin ball gives the same-center enlarged ball. -/
theorem affine_image_ball_zero {d : ℕ} (c : Point d) (k : ℝ) (hk : k ≠ 0) (r : ℝ) :
    (fun x : Point d => c + k • x) '' ball 0 r = ball c (|k| * r) := by
  calc
    _ = (fun y : Point d => c + y) '' ((fun x : Point d => k • x) '' ball 0 r) := by
      rw [image_image]
    _ = _ := by
      rw [Metric.smul_image_ball hk]
      simp [image_add_left, Real.norm_eq_abs]

/-- The completed Lebesgue measure of a concentric triple-radius ball. -/
theorem lebesgue_ball_triple (d : ℕ) [NeZero d] (c : Point d) (r : ℝ) :
    Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d (ball c (3 * r)) =
      (3 : ℝ≥0∞) ^ d * Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d (ball c r) := by
  have hm : MeasurableSet[Specs.D11.Ch03.LebesgueMeasures.lebesgueSpace_value d]
      (ball (0 : Point d) r) :=
    LebesgueMeasures.native_borel_le d _ isOpen_ball.measurableSet
  have h3 := (TranslationDilation.lebesgue_affine d c 3 (ball 0 r) hm).2
  have h1 := (TranslationDilation.lebesgue_affine d c 1 (ball 0 r) hm).2
  rw [affine_image_ball_zero c 3 (by norm_num) r] at h3
  rw [affine_image_ball_zero c 1 (by norm_num) r] at h1
  norm_num at h1
  have hfactor : ENNReal.ofReal (|(3 : ℝ)| ^ d) = (3 : ℝ≥0∞) ^ d := by
    rw [abs_of_pos (by norm_num : 0 < (3 : ℝ)), ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [hfactor] at h3
  simpa only [abs_of_pos (by norm_num : 0 < (3 : ℝ)), h1] using h3

/-- Finite ball selection with the full quantitative estimate of the paper. -/
theorem finite_ball_covering : Specs.D11.Ch13.FiniteBallCovering.finite_ball_covering := by
  intro d _ ι s c r hr
  obtain ⟨t, hts, htd, htc⟩ := finite_ball_selection s c r hr
  have hcover : (⋃ i ∈ s, ball (c i) (r i)) ⊆ ⋃ j ∈ t, ball (c j) (3 * r j) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨j, hj, hij⟩ := htc i hi
    exact Set.mem_iUnion₂.mpr ⟨j, hj, hij hxi⟩
  refine ⟨t, hts, htd, hcover, ?_⟩
  calc
    _ ≤ Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d
        (⋃ j ∈ t, ball (c j) (3 * r j)) := measure_mono hcover
    _ ≤ ∑ j ∈ t, Specs.D11.Ch03.LebesgueMeasures.lebesgue_value d
        (ball (c j) (3 * r j)) := measure_biUnion_finset_le t _
    _ = _ := by simp_rw [lebesgue_ball_triple]; rw [Finset.mul_sum]

end D11.Ch13.FiniteBallCovering
