import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorRnFailure
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorMeasureVariation
import Mathlib.MeasureTheory.VectorMeasure.AddContent

/-!
The indicator vector measure on Lebesgue [0,1], over ℝ or ℂ.
Source: paper.tex:20926–20940.

For any finite measure, indicator classes satisfy ‖1_A‖ₑ = μ(A).
Finite additivity and this bound construct a norm-countably-additive vector
measure, and the norm identity gives its exact variation. The dyadic half-sets
are obtained by copying the left half recursively into both halves of [0,1].
Their measures are 1/2 and distinct pairs have intersection measure 1/4,
hence their indicators have L¹ distance 1/2. Compactness would give a
convergent subsequence, contradicting that separation. The accepted compact
range theorem for Bochner densities then rules out a density.
-/

noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal Topology unitInterval symmDiff

namespace ExpandedFA.PartIV.VectorRnFailure
open VectorRnFailureSpec

section FiniteMeasure
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]

/-- Indicator classes for an arbitrary finite measure, totalized at zero
outside the sigma algebra. -/
def indicatorClass (A : Set X) : Lp 𝕜 1 ν :=
  if hA : MeasurableSet A then indicatorConstLp 1 hA (measure_ne_top ν A) (1 : 𝕜) else 0

lemma indicatorClass_enorm (A : Set X) (hA : MeasurableSet A) :
    ‖indicatorClass (𝕜 := 𝕜) ν A‖ₑ = ν A := by
  simp only [indicatorClass, dite_eq_left hA, ← ofReal_norm,
    norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp : (1 : ℝ≥0∞) ≠ ∞)]
  simp [Measure.real, ENNReal.ofReal_toReal (measure_ne_top ν A)]

lemma indicatorClass_bound (A : Set X) : ‖indicatorClass (𝕜 := 𝕜) ν A‖ₑ ≤ ν A := by
  by_cases hA : MeasurableSet A
  · exact (indicatorClass_enorm (𝕜 := 𝕜) ν A hA).le
  · simp [indicatorClass, hA]

lemma indicatorClass_union (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hd : Disjoint A B) :
    indicatorClass (𝕜 := 𝕜) ν (A ∪ B) = indicatorClass (𝕜 := 𝕜) ν A + indicatorClass (𝕜 := 𝕜) ν B := by
  simp only [indicatorClass, dite_eq_left hA, dite_eq_left hB, dite_eq_left (hA.union hB)]
  exact indicatorConstLp_disjoint_union hA hB (measure_ne_top ν A) (measure_ne_top ν B) hd (1 : 𝕜)

def indicatorVectorMeasure : VectorMeasure X (Lp 𝕜 1 ν) :=
  VectorMeasure.of_additive_of_le_measure (indicatorClass (𝕜 := 𝕜) ν) (indicatorClass_bound (𝕜 := 𝕜) ν)
    (indicatorClass_union (𝕜 := 𝕜) ν) (fun A hA => by simp [indicatorClass, hA])

lemma indicatorVectorMeasure_apply (A : Set X) :
    indicatorVectorMeasure (𝕜 := 𝕜) ν A = indicatorClass (𝕜 := 𝕜) ν A := rfl

lemma indicatorVectorMeasure_variation : (indicatorVectorMeasure (𝕜 := 𝕜) ν).variation = ν := by
  apply le_antisymm
  · exact VectorMeasure.variation_le_of_forall_enorm_le
      (fun A _ => indicatorClass_bound (𝕜 := 𝕜) ν A)
  · apply Measure.le_iff.mpr
    intro A hA
    rw [← indicatorClass_enorm (𝕜 := 𝕜) ν A hA]
    exact (indicatorVectorMeasure (𝕜 := 𝕜) ν).enorm_measure_le_variation A

lemma indicatorClass_distance (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    dist (indicatorClass (𝕜 := 𝕜) ν A) (indicatorClass (𝕜 := 𝕜) ν B) = ν.real (A ∆ B) := by
  simp only [indicatorClass, dite_eq_left hA, dite_eq_left hB,
    dist_indicatorConstLp_eq_norm,
    norm_indicatorConstLp (by simp : (1 : ℝ≥0∞) ≠ 0) (by simp : (1 : ℝ≥0∞) ≠ ∞)]
  simp
end FiniteMeasure

/-- The vector measure in the source, with values in actual scalar L¹[0,1]. -/
def indicatorMeasure (𝕜 : Type) [RCLike 𝕜] : IndicatorMeasureType 𝕜 :=
  indicatorVectorMeasure (𝕜 := 𝕜) μ

variable {𝕜 : Type} [RCLike 𝕜]

lemma indicatorMeasure_apply (A : Set Interval) : indicatorMeasure 𝕜 A = IndicatorValue A := rfl

theorem indicator_apply : IndicatorApply := by
  intro 𝕜 _ m hm A hA
  rw [hm A]
  simp only [IndicatorValue, dite_eq_left hA]
  exact indicatorConstLp_coeFn

theorem countable_additivity : CountableAdditivity := by
  intro 𝕜 _ m _ A hA hd
  exact m.m_iUnion hA hd

theorem variation : Variation := by
  intro 𝕜 _ m hm
  have h : m = indicatorMeasure 𝕜 := by
    apply VectorMeasure.ext
    intro A _
    exact hm A
  rw [h]
  exact indicatorVectorMeasure_variation (𝕜 := 𝕜) μ

theorem absolutely_continuous : AbsoluteContinuity := by
  intro 𝕜 _ m hm A hA hnull
  apply enorm_eq_zero.mp
  rw [hm A]
  change ‖indicatorClass (𝕜 := 𝕜) μ A‖ₑ = 0
  rw [indicatorClass_enorm (𝕜 := 𝕜) μ A hA, hnull]

lemma measurable_dyadicCopy (b : ℝ) {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet (DyadicCopy b S) :=
  hS.preimage (by fun_prop)

lemma volume_dyadicCopy (b : ℝ) (S : Set ℝ) :
    volume (DyadicCopy b S) = (1 / 2 : ℝ≥0∞) * volume S := by
  have heq : DyadicCopy b S =
      (fun x : ℝ => 2 * x) ⁻¹' ((fun y : ℝ => y + (-b)) ⁻¹' S) := by
    ext x
    simp [DyadicCopy, sub_eq_add_neg]
  rw [heq, Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0),
    measure_preimage_add_right]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma dyadicCopy_zero_subset {S : Set ℝ} (hS : S ⊆ Ico 0 1) :
    DyadicCopy 0 S ⊆ Ico 0 (1 / 2) := by
  intro x hx
  have hh := hS hx
  simp only [DyadicCopy, mem_preimage, sub_zero] at hx
  change 0 ≤ 2 * x - 0 ∧ 2 * x - 0 < 1 at hh
  constructor <;> linarith

lemma dyadicCopy_one_subset {S : Set ℝ} (hS : S ⊆ Ico 0 1) :
    DyadicCopy 1 S ⊆ Ico (1 / 2) 1 := by
  intro x hx
  have hh := hS hx
  change 0 ≤ 2 * x - 1 ∧ 2 * x - 1 < 1 at hh
  constructor <;> linarith

lemma dyadicCopy_disjoint {S T : Set ℝ} (hS : S ⊆ Ico 0 1) (hT : T ⊆ Ico 0 1) :
    Disjoint (DyadicCopy 0 S) (DyadicCopy 1 T) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h₀ := dyadicCopy_zero_subset hS hx
  have h₁ := dyadicCopy_one_subset hT hy
  exact (not_lt_of_ge h₁.1) h₀.2

lemma realDyadicHalf_subset (n : ℕ) : RealDyadicHalf n ⊆ Ico 0 1 := by
  induction n with
  | zero =>
    intro x hx
    exact ⟨hx.1, hx.2.trans (by norm_num)⟩
  | succ n ih =>
    apply union_subset
    · intro x hx
      have h := dyadicCopy_zero_subset ih hx
      exact ⟨h.1, h.2.trans (by norm_num)⟩
    · intro x hx
      have h := dyadicCopy_one_subset ih hx
      exact ⟨le_trans (by norm_num) h.1, h.2⟩

lemma measurable_realDyadicHalf (n : ℕ) : MeasurableSet (RealDyadicHalf n) := by
  induction n with
  | zero => exact measurableSet_Ico
  | succ n ih => exact (measurable_dyadicCopy 0 ih).union (measurable_dyadicCopy 1 ih)

lemma volume_dyadicCopies {S : Set ℝ} (hS : MeasurableSet S) (hsub : S ⊆ Ico 0 1) :
    volume (DyadicCopy 0 S ∪ DyadicCopy 1 S) = volume S := by
  rw [measure_union (dyadicCopy_disjoint hsub hsub) (measurable_dyadicCopy 1 hS),
    volume_dyadicCopy, volume_dyadicCopy, ← add_mul]
  rw [ENNReal.add_halves]
  simp

lemma volume_realDyadicHalf (n : ℕ) : volume (RealDyadicHalf n) = (1 / 2 : ℝ≥0∞) := by
  induction n with
  | zero => norm_num [RealDyadicHalf, Real.volume_Ico, ENNReal.ofReal_div_of_pos]
  | succ n ih =>
    rw [RealDyadicHalf, volume_dyadicCopies (measurable_realDyadicHalf n)
      (realDyadicHalf_subset n), ih]

lemma realDyadicHalf_inter_zero (n : ℕ) :
    RealDyadicHalf 0 ∩ RealDyadicHalf (n + 1) = DyadicCopy 0 (RealDyadicHalf n) := by
  apply subset_antisymm
  · intro x hx
    rcases hx.2 with h | h
    · exact h
    · have h' := dyadicCopy_one_subset (realDyadicHalf_subset n) h
      exact False.elim ((not_lt_of_ge h'.1) hx.1.2)
  · intro x hx
    exact ⟨dyadicCopy_zero_subset (realDyadicHalf_subset n) hx, Or.inl hx⟩

lemma realDyadicHalf_inter_succ (i j : ℕ) :
    RealDyadicHalf (i + 1) ∩ RealDyadicHalf (j + 1) =
      DyadicCopy 0 (RealDyadicHalf i ∩ RealDyadicHalf j) ∪
        DyadicCopy 1 (RealDyadicHalf i ∩ RealDyadicHalf j) := by
  apply subset_antisymm
  · intro x hx
    rcases hx with ⟨h₀ | h₁, h₂ | h₃⟩
    · exact Or.inl ⟨h₀, h₂⟩
    · exact False.elim (Set.disjoint_left.mp
        (dyadicCopy_disjoint (realDyadicHalf_subset i) (realDyadicHalf_subset j)) h₀ h₃)
    · exact False.elim (Set.disjoint_left.mp
        (dyadicCopy_disjoint (realDyadicHalf_subset j) (realDyadicHalf_subset i)) h₂ h₁)
    · exact Or.inr ⟨h₁, h₃⟩
  · intro x hx
    rcases hx with h | h
    · exact ⟨Or.inl h.1, Or.inl h.2⟩
    · exact ⟨Or.inr h.1, Or.inr h.2⟩

lemma volume_realDyadicHalf_inter (i j : ℕ) (hij : i < j) :
    volume (RealDyadicHalf i ∩ RealDyadicHalf j) = (1 / 4 : ℝ≥0∞) := by
  induction i generalizing j with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hij)
    rw [realDyadicHalf_inter_zero, volume_dyadicCopy, volume_realDyadicHalf]
    simp only [one_div]
    rw [← ENNReal.mul_inv (by simp) (by simp)]
    norm_num
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      rw [realDyadicHalf_inter_succ,
        volume_dyadicCopies ((measurable_realDyadicHalf i).inter (measurable_realDyadicHalf j))
          (inter_subset_left.trans (realDyadicHalf_subset i))]
      exact ih j (Nat.lt_of_succ_lt_succ hij)

lemma measurable_dyadicHalf (n : ℕ) : MeasurableSet (DyadicHalf n) :=
  (measurable_realDyadicHalf n).preimage measurable_subtype_coe

lemma interval_volume_preimage {S : Set ℝ} (hS : S ⊆ Icc 0 1) :
    μ (Subtype.val ⁻¹' S) = volume S := by
  rw [unitInterval.volume_apply]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hS hx⟩, hx, rfl⟩

lemma volume_dyadicHalf (n : ℕ) : μ (DyadicHalf n) = (1 / 2 : ℝ≥0∞) := by
  rw [DyadicHalf, interval_volume_preimage
    ((realDyadicHalf_subset n).trans Ico_subset_Icc_self), volume_realDyadicHalf]

lemma volume_dyadicHalf_inter (i j : ℕ) (hij : i ≠ j) :
    μ (DyadicHalf i ∩ DyadicHalf j) = (1 / 4 : ℝ≥0∞) := by
  change μ ((Subtype.val ⁻¹' RealDyadicHalf i) ∩ (Subtype.val ⁻¹' RealDyadicHalf j)) = _
  rw [← preimage_inter, interval_volume_preimage
    ((inter_subset_left.trans (realDyadicHalf_subset i)).trans Ico_subset_Icc_self)]
  rcases lt_or_gt_of_ne hij with h | h
  · exact volume_realDyadicHalf_inter i j h
  · rw [inter_comm]
    exact volume_realDyadicHalf_inter j i h

lemma real_dyadicHalf (n : ℕ) : μ.real (DyadicHalf n) = (1 / 2 : ℝ) := by
  rw [measureReal_def, volume_dyadicHalf]
  norm_num

lemma real_dyadicHalf_inter (i j : ℕ) (hij : i ≠ j) :
    μ.real (DyadicHalf i ∩ DyadicHalf j) = (1 / 4 : ℝ) := by
  rw [measureReal_def, volume_dyadicHalf_inter i j hij]
  norm_num

lemma real_dyadicHalf_symmDiff (i j : ℕ) (hij : i ≠ j) :
    μ.real (DyadicHalf i ∆ DyadicHalf j) = (1 / 2 : ℝ) := by
  have h₁ := measureReal_inter_add_sdiff (μ := μ) (s := DyadicHalf i)
    (measurable_dyadicHalf j)
  have h₂ := measureReal_inter_add_sdiff (μ := μ) (s := DyadicHalf j)
    (measurable_dyadicHalf i)
  rw [real_dyadicHalf_inter i j hij, real_dyadicHalf] at h₁
  rw [real_dyadicHalf_inter j i hij.symm, real_dyadicHalf] at h₂
  rw [measureReal_symmDiff_eq (measurable_dyadicHalf i) (measurable_dyadicHalf j)]
  linarith

theorem dyadic_separation : DyadicSeparation := by
  intro 𝕜 _
  refine ⟨fun n => ⟨measurable_dyadicHalf n, volume_dyadicHalf n⟩, ?_⟩
  intro i j hij
  change dist (indicatorClass (𝕜 := 𝕜) μ (DyadicHalf i)) (indicatorClass (𝕜 := 𝕜) μ (DyadicHalf j)) = _
  rw [indicatorClass_distance (𝕜 := 𝕜) μ _ _ (measurable_dyadicHalf i) (measurable_dyadicHalf j)]
  exact real_dyadicHalf_symmDiff i j hij

/-- The compact-range obstruction, kept separate from the dyadic arithmetic. -/
theorem not_compact_of_separated_indicators
    (A : ℕ → Set Interval)
    (hsep : ∀ i j, i ≠ j → dist (IndicatorValue (𝕜 := 𝕜) (A i)) (IndicatorValue (A j)) = 1 / 2)
    (m : IndicatorMeasureType 𝕜) (hm : ∀ B, m B = IndicatorValue B) :
    ¬ IsCompact (closure (range m)) := by
  intro hc
  obtain ⟨y, _, φ, hφ, hy⟩ := hc.tendsto_subseq
    (fun n => subset_closure (mem_range_self (A n)))
  have hy' : Tendsto (fun n => m (A (φ (n + 1)))) atTop (𝓝 y) :=
    hy.comp (tendsto_add_atTop_nat 1)
  have hd := hy'.dist hy
  have heq : (fun n => dist (m (A (φ (n + 1)))) (m (A (φ n)))) =
      (fun _ : ℕ => (1 / 2 : ℝ)) := by
    funext n
    rw [hm, hm]
    exact hsep _ _ (ne_of_gt (hφ (Nat.lt_succ_self n)))
  simp only [Function.comp_def] at hd
  rw [heq, dist_self] at hd
  have : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hd
  norm_num at this

/-- Applying the already proved compact-range theorem requires no
Radon–Nikodym property assumption on the Banach range. -/
theorem no_density_of_not_compact
    (m : IndicatorMeasureType 𝕜)
    (hnc : ¬ IsCompact (closure (range m))) :
    ¬ ∃ g : Interval → Y 𝕜, Integrable g μ ∧
      ∀ A, MeasurableSet A → m A = ∫ x in A, g x ∂μ := by
  rintro ⟨g, hg, hmg⟩
  have hmeq : m = μ.withDensityᵥ g := by
    apply VectorMeasure.ext
    intro A hA
    rw [hmg A hA, withDensityᵥ_apply hg hA]
  apply hnc
  rw [hmeq]
  exact densityMeasure_compactRange μ g
    ((ExpandedFA.FunctionSpaces.bochnerIntegrable_identification μ g).mpr hg)

theorem noncompact_range : NoncompactRange := by
  intro 𝕜 _ m hm
  exact not_compact_of_separated_indicators DyadicHalf (dyadic_separation 𝕜).2 m hm

theorem no_bochner_density : NoBochnerDensity := by
  intro 𝕜 _ m hm
  exact no_density_of_not_compact m (noncompact_range 𝕜 m hm)

theorem counterexample : Counterexample := by
  intro 𝕜 _
  exact ⟨indicatorMeasure 𝕜, indicatorMeasure_apply,
    variation 𝕜 _ indicatorMeasure_apply,
    absolutely_continuous 𝕜 _ indicatorMeasure_apply,
    noncompact_range 𝕜 _ indicatorMeasure_apply,
    no_bochner_density 𝕜 _ indicatorMeasure_apply⟩

end ExpandedFA.PartIV.VectorRnFailure
