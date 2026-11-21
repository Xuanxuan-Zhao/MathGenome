import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.OscillationSets
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.Oscillation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.CompactInterval
import Mathlib.Tactic.Linarith

/-!
# Oscillation superlevel sets on a closed real interval

The first paragraph of the proof of K03.08.oscillation_criterion
(paper.tex:2211–2221). The infimum is the upstream unpunctured oscillation;
we identify its neighborhoods with the displayed relative open intervals.

For closedness, if one neighborhood at x has oscillation below α, every
point y within half its radius has a half-radius neighborhood contained
in it. Oscillation is monotone under inclusion, so the strict sublevel
set is open. Intersecting its closed complement with [a,b] gives E_α.
Finally positive oscillation exceeds 1/(n+1) for some natural n.
-/
namespace SingleVariableAnalysis

open scoped ENNReal

noncomputable def intervalOscillation (f : ℝ → ℝ) (a b x : ℝ) : ℝ≥0∞ :=
  LocalOscillation f (Set.Icc a b) x

noncomputable def oscillationSuperlevel (f : ℝ → ℝ) (a b α : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc a b ∧ ENNReal.ofReal α ≤ intervalOscillation f a b x}

def intervalDiscontinuities (f : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc a b ∧ ¬ ContinuousWithinAt f (Set.Icc a b) x}

/-- The metric balls are exactly the relative intervals in the manuscript. -/
theorem intervalOscillation_formula (f : ℝ → ℝ) (a b x : ℝ) :
    intervalOscillation f a b x =
      ⨅ r : {r : ℝ // 0 < r},
        Oscillation f (Set.Ioo (x - r.val) (x + r.val) ∩ Set.Icc a b) := by
  unfold intervalOscillation LocalOscillation
  congr 1
  funext r
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioo, Real.dist_eq, abs_lt]
  constructor
  · rintro ⟨hy, h₁, h₂⟩
    exact ⟨⟨by linarith, by linarith⟩, hy⟩
  · rintro ⟨⟨h₁, h₂⟩, hy⟩
    exact ⟨hy, by linarith, by linarith⟩

/-- A global bound on values also bounds all relative oscillations. -/
theorem intervalOscillation_bound (f : ℝ → ℝ) (a b M : ℝ)
    (hM : ∀ y ∈ Set.Icc a b, |f y| ≤ M) (x : ℝ) :
    intervalOscillation f a b x ≤ ENNReal.ofReal (2 * M) := by
  apply (iInf_le _ (⟨1, zero_lt_one⟩ : {r : ℝ // 0 < r})).trans
  apply oscillation_le
  intro y hy z hz
  apply ENNReal.ofReal_le_ofReal
  calc
    dist (f y) (f z) = |f y - f z| := Real.dist_eq _ _
    _ ≤ |f y| + |f z| := abs_sub _ _
    _ ≤ 2 * M := by linarith [hM y hy.1, hM z hz.1]

theorem intervalOscillation_finite (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) (x : ℝ) :
    intervalOscillation f a b x ≠ ⊤ := by
  obtain ⟨M, hM⟩ := hf
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (intervalOscillation_bound f a b M hM x)

theorem intervalOscillation_zero_iff_continuous (f : ℝ → ℝ) (a b : ℝ)
    (_hf : ∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M)
    (x : ℝ) (hx : x ∈ Set.Icc a b) :
    intervalOscillation f a b x = 0 ↔ ContinuousWithinAt f (Set.Icc a b) x :=
  localOscillation_zero_iff_continuousWithinAt f (Set.Icc a b) x hx

/-- Oscillation decreases when its set of test pairs is restricted. -/
theorem oscillation_mono {X Y : Type*} [MetricSpace Y] (f : X → Y)
    {A B : Set X} (hAB : A ⊆ B) : Oscillation f A ≤ Oscillation f B := by
  apply oscillation_le
  intro x hx y hy
  exact distance_le_oscillation f B (hAB hx) (hAB hy)

/-- Strict sublevel sets of unpunctured local oscillation are open in the
ambient domain, even when the function is unbounded. -/
theorem isOpen_localOscillation_lt {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (c : ℝ≥0∞) :
    IsOpen {x | LocalOscillation f E x < c} := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  change LocalOscillation f E x < c at hx
  unfold LocalOscillation at hx
  obtain ⟨r, hr⟩ := iInf_lt_iff.mp hx
  refine ⟨r.val / 2, half_pos r.property, ?_⟩
  intro y hy
  apply lt_of_le_of_lt ?_ hr
  apply (iInf_le _ (⟨r.val / 2, half_pos r.property⟩ : {s : ℝ // 0 < s})).trans
  apply oscillation_mono
  intro z hz
  refine ⟨hz.1, ?_⟩
  calc
    dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
    _ < r.val / 2 + r.val / 2 := add_lt_add hz.2 hy
    _ = r.val := add_halves _

theorem oscillationSuperlevel_closed (f : ℝ → ℝ) (a b : ℝ)
    (_hf : ∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M)
    (α : ℝ) (_hα : 0 < α) : IsClosed (oscillationSuperlevel f a b α) := by
  have hclosed : IsClosed {x | ENNReal.ofReal α ≤ LocalOscillation f (Set.Icc a b) x} := by
    simpa only [Set.compl_ofPred, not_lt] using
      (isOpen_localOscillation_lt f (Set.Icc a b) (ENNReal.ofReal α)).isClosed_compl
  exact isClosed_Icc.inter hclosed

theorem oscillationSuperlevel_compact (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M)
    (α : ℝ) (hα : 0 < α) : IsCompact (oscillationSuperlevel f a b α) :=
  (real_closed_interval_compact a b).of_isClosed_subset
    (oscillationSuperlevel_closed f a b hf α hα) (fun _ hx => hx.1)

theorem intervalDiscontinuities_eq_union (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∃ M : ℝ, ∀ y ∈ Set.Icc a b, |f y| ≤ M) :
    intervalDiscontinuities f a b =
      ⋃ n : ℕ, oscillationSuperlevel f a b (1 / ((n : ℝ) + 1)) := by
  ext x
  constructor
  · rintro ⟨hx, hdisc⟩
    have hne : intervalOscillation f a b x ≠ 0 := fun h =>
      hdisc ((intervalOscillation_zero_iff_continuous f a b hf x hx).mp h)
    have hfin := intervalOscillation_finite f a b hf x
    have hpos : 0 < (intervalOscillation f a b x).toReal :=
      ENNReal.toReal_pos hne hfin
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    apply Set.mem_iUnion.mpr
    refine ⟨n, hx, ?_⟩
    calc
      ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤
          ENNReal.ofReal (intervalOscillation f a b x).toReal :=
        ENNReal.ofReal_le_ofReal hn.le
      _ = intervalOscillation f a b x := ENNReal.ofReal_toReal hfin
  · intro hx
    obtain ⟨n, hx, hn⟩ := Set.mem_iUnion.mp hx
    refine ⟨hx, ?_⟩
    intro hc
    have hz := (intervalOscillation_zero_iff_continuous f a b hf x hx).mpr hc
    have hpos : 0 < ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
      ENNReal.ofReal_pos.mpr (one_div_pos.mpr (by positivity))
    rw [hz] at hn
    exact (not_le_of_gt hpos) hn

end SingleVariableAnalysis
