import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.OneSided
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.BigO
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Big-O and little-o on a fixed common approach

K03.02.big_o, paper.tex:432–437. A filter fixes both the approach and the
common domain. Functions are ambient functions tested only along that filter.
The five real approaches agree with `ApproachEventually`. General filters also
cover finite complex input approaches through `PuncturedDomainFilter`.

The definitions use inequalities, including at zeros of the comparison function.
They specialize to real absolute values and complex moduli. Only the quotient
characterizations impose eventual nonvanishing. The normed-field generality
includes both manuscript scalar types with their existing instances.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
universe u v

/-- The manuscript's five real approaches, restricted to the common domain E. -/
def RealApproachFilter (E : Set ℝ) (q : RealApproach) : Filter ℝ := match q with
  | .punctured a => nhdsWithin a (E \ {a})
  | .right a => nhdsWithin a (E ∩ Set.Ioi a)
  | .left a => nhdsWithin a (E ∩ Set.Iio a)
  | .posInfinity => atTop ⊓ 𝓟 E
  | .negInfinity => atBot ⊓ 𝓟 E

/-- A finite nonnegative real constant bounds the norm ratio by multiplication,
even where g vanishes. -/
def ScalarBigO {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f g : X → K) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ‖f x‖ ≤ C * ‖g x‖

/-- The neighborhood may depend on the positive error coefficient. -/
def ScalarLittleO {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f g : X → K) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ‖f x‖ ≤ ε * ‖g x‖

/-- Eventual boundedness of the quotient means boundedness of its norm. -/
def EventuallyBoundedRatio {X : Type u} {K : Type v} [NormedField K]
    (l : Filter X) (f g : X → K) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, ‖f x / g x‖ ≤ C

/-- A filter's eventual assertions coincide with the explicit source regions.
No nontriviality condition is inserted into this assertion about neighborhoods. -/
theorem approachEventually_filter_iff (E : Set ℝ) (q : RealApproach) (P : ℝ → Prop) :
    ApproachEventually E q P ↔ ∀ᶠ x in RealApproachFilter E q, P x := by
  cases q with
  | punctured a =>
    change (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, (0 < |x - a| ∧ |x - a| < r) → P x) ↔
      {x | P x} ∈ nhdsWithin a (E \ {a})
    rw [Metric.mem_nhdsWithin_iff]
    constructor
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx => h x hx.2.1 ⟨?_, ?_⟩⟩
      · exact abs_pos.mpr (sub_ne_zero.mpr (by simpa using hx.2.2))
      · simpa only [Metric.mem_ball, Real.dist_eq] using hx.1
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx hp => h ⟨?_, hx, ?_⟩⟩
      · simpa only [Metric.mem_ball, Real.dist_eq] using hp.2
      · simpa using sub_ne_zero.mp (abs_pos.mp hp.1)
  | right a =>
    change (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, (a < x ∧ x < a + r) → P x) ↔
      {x | P x} ∈ nhdsWithin a (E ∩ Set.Ioi a)
    rw [Metric.mem_nhdsWithin_iff]
    constructor
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx => h x hx.2.1 ⟨hx.2.2, ?_⟩⟩
      have hd : |x - a| < r := hx.1
      have := (abs_lt.mp hd).2
      linarith
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx hp => h ⟨?_, hx, hp.1⟩⟩
      change |x - a| < r
      rw [abs_of_pos (sub_pos.mpr hp.1)]
      linarith [hp.2]
  | left a =>
    change (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, (a - r < x ∧ x < a) → P x) ↔
      {x | P x} ∈ nhdsWithin a (E ∩ Set.Iio a)
    rw [Metric.mem_nhdsWithin_iff]
    constructor
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx => h x hx.2.1 ⟨?_, hx.2.2⟩⟩
      have hd : |x - a| < r := hx.1
      have := (abs_lt.mp hd).1
      linarith
    · rintro ⟨r, hr, h⟩
      refine ⟨r, hr, fun x hx hp => h ⟨?_, hx, hp.2⟩⟩
      change |x - a| < r
      rw [abs_of_neg (sub_neg.mpr hp.2)]
      linarith [hp.1]
  | posInfinity =>
    change (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, r < x → P x) ↔
      ∀ᶠ x in (atTop : Filter ℝ) ⊓ 𝓟 E, P x
    rw [eventually_inf_principal, eventually_atTop]
    constructor
    · rintro ⟨r, _, h⟩
      exact ⟨r + 1, fun x hx hE => h x hE (by linarith)⟩
    · rintro ⟨r, h⟩
      refine ⟨max 1 r, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx hd => ?_⟩
      exact h x (le_trans (le_max_right _ _) hd.le) hx
  | negInfinity =>
    change (∃ r : ℝ, 0 < r ∧ ∀ x ∈ E, x < -r → P x) ↔
      ∀ᶠ x in (atBot : Filter ℝ) ⊓ 𝓟 E, P x
    rw [eventually_inf_principal, eventually_atBot]
    constructor
    · rintro ⟨r, _, h⟩
      exact ⟨-r - 1, fun x hx hE => h x hE (by linarith)⟩
    · rintro ⟨r, h⟩
      refine ⟨max 1 (-r), lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx hd => ?_⟩
      apply h x _ hx
      have := le_max_right (1 : ℝ) (-r)
      linarith

section Scalar

variable {X : Type u} {K : Type v} [NormedField K]

/-- Check the actual inequalities; a negative library constant can always be
replaced by max C 0 because norms are nonnegative. -/
theorem scalarBigO_iff_isBigO (l : Filter X) (f g : X → K) :
    ScalarBigO l f g ↔ Asymptotics.IsBigO l f g := by
  rw [Asymptotics.isBigO_iff]
  constructor
  · rintro ⟨C, _, h⟩
    exact ⟨C, h⟩
  · rintro ⟨C, h⟩
    refine ⟨max C 0, le_max_right _ _, h.mono fun x hx => ?_⟩
    exact hx.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

theorem scalarLittleO_iff_isLittleO (l : Filter X) (f g : X → K) :
    ScalarLittleO l f g ↔ Asymptotics.IsLittleO l f g := by
  rw [Asymptotics.isLittleO_iff]
  exact ⟨fun h ε hε => h ε hε, fun h ε hε => h hε⟩

/-- Taking ε = 1 gives the big-O bound. -/
theorem scalarLittleO_isBigO (l : Filter X) (f g : X → K)
    (h : ScalarLittleO l f g) : ScalarBigO l f g :=
  ⟨1, zero_le_one, h 1 zero_lt_one⟩

theorem scalarBigO_eventually_zero (l : Filter X) (f g : X → K)
    (h : ScalarBigO l f g) : ∀ᶠ x in l, g x = 0 → f x = 0 := by
  obtain ⟨C, _, hC⟩ := h
  filter_upwards [hC] with x hx hg
  exact norm_le_zero_iff.mp (by simpa [hg] using hx)

theorem scalarLittleO_eventually_zero (l : Filter X) (f g : X → K)
    (h : ScalarLittleO l f g) : ∀ᶠ x in l, g x = 0 → f x = 0 :=
  scalarBigO_eventually_zero l f g (scalarLittleO_isBigO l f g h)

/-- Division by the positive norm of the eventually nonzero denominator is
reversible; no assertion about quotients at zeros is used. -/
theorem scalarBigO_iff_boundedRatio (l : Filter X) (f g : X → K)
    (hg : ∀ᶠ x in l, g x ≠ 0) :
    ScalarBigO l f g ↔ EventuallyBoundedRatio l f g := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h, hg] with x hx hne
    rw [norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr hne)).mpr hx
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h, hg] with x hx hne
    rw [norm_div] at hx
    exact (div_le_iff₀ (norm_pos_iff.mpr hne)).mp hx

/-- Mathlib's converse requires eventual zero compatibility; eventual
nonvanishing supplies precisely that hypothesis. -/
theorem scalarLittleO_iff_ratio_tendsto (l : Filter X) (f g : X → K)
    (hg : ∀ᶠ x in l, g x ≠ 0) :
    ScalarLittleO l f g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) := by
  rw [scalarLittleO_iff_isLittleO]
  exact Asymptotics.isLittleO_iff_tendsto' (hg.mono fun _ hx hzero => (hx hzero).elim)

end Scalar

theorem real_scalarBigO_iff {X : Type u} (l : Filter X) (f g : X → ℝ) :
    ScalarBigO l f g ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in l, |f x| ≤ C * |g x| := by
  simp only [ScalarBigO, Real.norm_eq_abs]

theorem real_scalarLittleO_iff {X : Type u} (l : Filter X) (f g : X → ℝ) :
    ScalarLittleO l f g ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, |f x| ≤ ε * |g x| := by
  simp only [ScalarLittleO, Real.norm_eq_abs]

theorem scalarBigO_approach_iff {K : Type v} [NormedField K]
    (E : Set ℝ) (q : RealApproach) (f g : ℝ → K) :
    ScalarBigO (RealApproachFilter E q) f g ↔
      ∃ C : ℝ, 0 ≤ C ∧ ApproachEventually E q (fun x => ‖f x‖ ≤ C * ‖g x‖) := by
  simp only [ScalarBigO, approachEventually_filter_iff]

theorem scalarLittleO_approach_iff {K : Type v} [NormedField K]
    (E : Set ℝ) (q : RealApproach) (f g : ℝ → K) :
    ScalarLittleO (RealApproachFilter E q) f g ↔
      ∀ ε : ℝ, 0 < ε → ApproachEventually E q (fun x => ‖f x‖ ≤ ε * ‖g x‖) := by
  simp only [ScalarLittleO, approachEventually_filter_iff]

theorem scalarLittleO_ratio_approach_iff {K : Type v} [NormedField K]
    (E : Set ℝ) (q : RealApproach) (f g : ℝ → K)
    (ha : ApproachNontrivial E q) (hg : ApproachEventually E q (fun x => g x ≠ 0)) :
    ScalarLittleO (RealApproachFilter E q) f g ↔
      FiniteApproachLimit (fun x => f x / g x) E q 0 := by
  rw [scalarLittleO_iff_ratio_tendsto _ _ _ ((approachEventually_filter_iff _ _ _).mp hg)]
  simp only [Metric.tendsto_nhds, FiniteApproachLimit, ha, true_and,
    approachEventually_filter_iff]

theorem scalarLittleO_punctured_iff_ratio_limit {K : Type v} [NormedField K]
    (E : Set ℝ) (a : ℝ) (f g : ℝ → K)
    (hg : ApproachEventually E (.punctured a) (fun x => g x ≠ 0)) :
    ScalarLittleO (RealApproachFilter E (.punctured a)) f g ↔
      RelativePuncturedLimit (fun x => f x / g x) E a 0 := by
  rw [scalarLittleO_iff_ratio_tendsto _ _ _ ((approachEventually_filter_iff _ _ _).mp hg),
    relativePuncturedLimit_filter_iff]
  rfl

end SingleVariableAnalysis
