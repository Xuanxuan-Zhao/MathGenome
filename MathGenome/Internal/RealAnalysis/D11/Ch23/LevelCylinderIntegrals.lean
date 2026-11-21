import MathGenome.Internal.RealAnalysis.D11.Ch23.LevelCylinderMeasure
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch23.LevelCylinderIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
universe u
open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace D11.Ch23

section
variable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ)
    (hL : IsElementaryIntegral V L)

include hStone in
/-- The extension agrees with the cylinder pullback on every ring member. -/
theorem levelCylinderMeasure_of_ring (A : Set X) (hA : A ∈ positiveLevelSigmaRing V) :
    levelCylinderMeasure V L A = cylinderMass V L 1 A := by
  classical
  rw [levelCylinderMeasure_apply V hStone L A (sigmaRing_sets_measurable V A hA)]
  change (if A ∈ positiveLevelSigmaRing V then _ else _) = _
  exact ite_eq_left hA

include hV hL in
/-- Exact value on a nonnegative elementary undergraph. -/
theorem nonnegative_undergraph_mass (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) :
    undergraphMeasure V L (undergraph 0 (f : X → ℝ)) = ENNReal.ofReal (L f) := by
  rw [undergraph_measure_exact V hV L hL _ (show undergraph 0 (f : X → ℝ) ∈
    undergraphFamily V from ⟨0, f, rfl⟩)]
  simpa using undergraph_content_of_le V L (0 : V) f hf

/-- A clipped function; the zero threshold needs no constant unit in V. -/
def cappedElement (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (a : ℝ) (ha : 0 ≤ a) : V :=
  ⟨fun x => min ((f : X → ℝ) x) a, by
    rcases ha.eq_or_lt with h | h
    · have he : (fun x => min ((f : X → ℝ) x) a) = 0 := by
        funext x
        simp [← h, min_eq_right (hf x)]
      rw [he]
      exact V.zero_mem
    · exact min_const_mem V hStone f f.property a h⟩

/-- Successive caps are nonnegative strips of height at most d. -/
def stripElement (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (d : ℝ) (hd : 0 < d)
    (k : ℕ) : V :=
  cappedElement V hStone f hf (((k : ℝ) + 1) * d) (by positivity) -
    cappedElement V hStone f hf ((k : ℝ) * d) (by positivity)

lemma stripElement_nonneg (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (k : ℕ) (x : X) :
    0 ≤ (stripElement V hStone f hf d hd k : X → ℝ) x := by
  change 0 ≤ min _ (((k : ℝ) + 1) * d) - min _ ((k : ℝ) * d)
  exact sub_nonneg.mpr (min_le_min_left _ (by linarith))

lemma stripElement_sum (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (N : ℕ) :
    (∑ k ∈ Finset.range N, stripElement V hStone f hf d hd k) =
      cappedElement V hStone f hf ((N : ℝ) * d) (by positivity) := by
  induction N with
  | zero =>
    apply Subtype.ext
    funext x
    simp [cappedElement, min_eq_right (hf x)]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [stripElement, Nat.cast_add, Nat.cast_one]
    abel

include hV hL in
/-- Positive-level cylinders sandwich successive strips pointwise in X × R. -/
lemma strip_mass_lower (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (k : ℕ) :
    ENNReal.ofReal d * cylinderMass V L 1 {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x} ≤
      ENNReal.ofReal (L (stripElement V hStone f hf d hd k)) := by
  rw [← positiveLevel_cylinder_scaling V hV hStone L hL f f.property
    (((k : ℝ) + 1) * d) (by positivity) d hd,
    ← nonnegative_undergraph_mass V hV L hL _ (stripElement_nonneg V hStone f hf d hd k)]
  apply measure_mono
  intro p hp
  change 0 ≤ p.2 ∧ p.2 < _
  refine ⟨hp.2.1, ?_⟩
  change p.2 < min ((f : X → ℝ) p.1) (((k : ℝ) + 1) * d) -
    min ((f : X → ℝ) p.1) ((k : ℝ) * d)
  have hx : ((k : ℝ) + 1) * d < (f : X → ℝ) p.1 := hp.1
  rw [min_eq_right hx.le,
    min_eq_right (show (k : ℝ) * d ≤ (f : X → ℝ) p.1 by nlinarith [hx])]
  nlinarith [hp.2.2]

include hV hL in
lemma strip_mass_upper (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (k : ℕ) :
    ENNReal.ofReal (L (stripElement V hStone f hf d hd (k+1))) ≤
      ENNReal.ofReal d * cylinderMass V L 1 {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x} := by
  rw [← positiveLevel_cylinder_scaling V hV hStone L hL f f.property
    (((k : ℝ) + 1) * d) (by positivity) d hd,
    ← nonnegative_undergraph_mass V hV L hL _ (stripElement_nonneg V hStone f hf d hd (k+1))]
  apply measure_mono
  intro p hp
  change 0 ≤ p.2 ∧ p.2 <
    min ((f : X → ℝ) p.1) ((((k+1 : ℕ) : ℝ) + 1) * d) -
    min ((f : X → ℝ) p.1) (((k+1 : ℕ) : ℝ) * d) at hp
  simp only [Nat.cast_add, Nat.cast_one] at hp
  have hx : ((k : ℝ) + 1) * d < (f : X → ℝ) p.1 := by
    by_contra hx
    have he := le_of_not_gt hx
    rw [min_eq_left (by linarith : (f : X → ℝ) p.1 ≤ ((k : ℝ) + 1 + 1) * d),
      min_eq_left he, sub_self] at hp
    exact not_lt_of_ge hp.1 hp.2
  refine ⟨hx, hp.1, ?_⟩
  rw [min_eq_right hx.le] at hp
  nlinarith [min_le_right ((f : X → ℝ) p.1) (((k : ℝ) + 1 + 1) * d)]

lemma stripElement_sum_shift (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (N : ℕ) :
    (∑ k ∈ Finset.range N, stripElement V hStone f hf d hd (k+1)) =
      cappedElement V hStone f hf (((N : ℝ) + 1) * d) (by positivity) -
        cappedElement V hStone f hf d hd.le := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [stripElement, Nat.cast_add, Nat.cast_one]
    abel

/-- Finite lower level sums use strictly positive thresholds. -/
def lowerLevelStep (f : X → ℝ) (d : ℝ) (N : ℕ) : X → ℝ :=
  fun x => ∑ k ∈ Finset.range N, {x | ((k : ℝ) + 1) * d < f x}.indicator (fun _ => d) x

lemma lowerLevelStep_nonneg (f : X → ℝ) (d : ℝ) (hd : 0 ≤ d) (N : ℕ) (x : X) :
    0 ≤ lowerLevelStep f d N x := by
  apply Finset.sum_nonneg
  intro k _
  exact indicator_nonneg (fun _ _ => hd) x

include hStone in
lemma lowerLevelStep_bounds (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (N : ℕ) (x : X) :
    min ((f : X → ℝ) x) (((N : ℝ) + 1) * d) - min ((f : X → ℝ) x) d ≤
      lowerLevelStep (f : X → ℝ) d N x ∧
    lowerLevelStep (f : X → ℝ) d N x ≤ min ((f : X → ℝ) x) ((N : ℝ) * d) := by
  classical
  have hterm (k : ℕ) :
      (stripElement V hStone f hf d hd (k+1) : X → ℝ) x ≤
        {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x}.indicator (fun _ => d) x ∧
      {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x}.indicator (fun _ => d) x ≤
        (stripElement V hStone f hf d hd k : X → ℝ) x := by
    by_cases hx : ((k : ℝ) + 1) * d < (f : X → ℝ) x
    · simp only [indicator_of_mem (show x ∈ {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x} from hx)]
      constructor
      · change min _ ((((k+1 : ℕ) : ℝ)+1)*d) - min _ (((k+1 : ℕ) : ℝ)*d) ≤ d
        simp only [Nat.cast_add, Nat.cast_one]
        rw [min_eq_right hx.le]
        nlinarith [min_le_right ((f : X → ℝ) x) (((k : ℝ) + 1 + 1) * d)]
      · change d ≤ min _ (((k : ℝ)+1)*d) - min _ ((k : ℝ)*d)
        rw [min_eq_right hx.le, min_eq_right (by linarith : (k : ℝ)*d ≤ (f : X → ℝ) x)]
        linarith
    · simp only [indicator_of_notMem (show x ∉ {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x} from hx)]
      constructor
      · change min _ ((((k+1 : ℕ) : ℝ)+1)*d) - min _ (((k+1 : ℕ) : ℝ)*d) ≤ 0
        simp only [Nat.cast_add, Nat.cast_one]
        rw [min_eq_left (by linarith [le_of_not_gt hx] : (f : X → ℝ) x ≤ ((k : ℝ)+1+1)*d),
          min_eq_left (le_of_not_gt hx), sub_self]
      · exact stripElement_nonneg V hStone f hf d hd k x
  have heval (s : Finset ℕ) (a : ℕ → V) :
      ((∑ k ∈ s, a k : V) : X → ℝ) x = ∑ k ∈ s, (a k : X → ℝ) x := by simp
  constructor
  · have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => (hterm k).1)
    rw [← heval, stripElement_sum_shift V hStone f hf d hd N] at hs
    exact hs
  · have hs := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range N) => (hterm k).2)
    rw [← heval, stripElement_sum V hStone f hf d hd N] at hs
    exact hs

lemma lowerLevelStep_measurable (f : V) (d : ℝ) (hd : 0 < d) (N : ℕ) :
    @Measurable X ℝ (positiveLevelMeasurableSpace V) (borel ℝ)
      (lowerLevelStep (f : X → ℝ) d N) := by
  letI := positiveLevelMeasurableSpace V
  exact Finset.measurable_sum _ (fun k _ => measurable_const.indicator
    (positiveLevel_measurableSet V f f.property (((k : ℝ) + 1) * d) (by positivity)))

include hStone in
lemma lowerLevelStep_lintegral (f : V) (d : ℝ) (hd : 0 < d) (N : ℕ) :
    letI := positiveLevelMeasurableSpace V
    (∫⁻ x, ENNReal.ofReal (lowerLevelStep (f : X → ℝ) d N x) ∂levelCylinderMeasure V L) =
      ∑ k ∈ Finset.range N, ENNReal.ofReal d *
        cylinderMass V L 1 {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x} := by
  classical
  letI := positiveLevelMeasurableSpace V
  have he (x : X) : ENNReal.ofReal (lowerLevelStep (f : X → ℝ) d N x) =
      ∑ k ∈ Finset.range N,
        {x | ((k : ℝ) + 1) * d < (f : X → ℝ) x}.indicator (fun _ => ENNReal.ofReal d) x := by
    rw [lowerLevelStep, ENNReal.ofReal_sum_of_nonneg
      (fun k _ => indicator_nonneg (fun _ _ => hd.le) x)]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hx : ((k : ℝ) + 1) * d < (f : X → ℝ) x <;> simp [hx]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun k _ => measurable_const.indicator
    (positiveLevel_measurableSet V f f.property _ (by positivity)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [lintegral_indicator_const
    (positiveLevel_measurableSet V f f.property _ (by positivity)),
    levelCylinderMeasure_of_ring V hStone L _
      (positiveLevel_mem_sigmaRing V f f.property _ (by positivity))]

include hV hL in
/-- Finite level sums are squeezed by finite sums of elementary strips.
The two sums telescope; no whole-space mass is used. -/
lemma lowerLevelStep_integral_bounds (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x)
    (d : ℝ) (hd : 0 < d) (N : ℕ) :
    letI := positiveLevelMeasurableSpace V
    ENNReal.ofReal (L (cappedElement V hStone f hf (((N : ℝ) + 1) * d) (by positivity) -
      cappedElement V hStone f hf d hd.le)) ≤
      (∫⁻ x, ENNReal.ofReal (lowerLevelStep (f : X → ℝ) d N x) ∂levelCylinderMeasure V L) ∧
    (∫⁻ x, ENNReal.ofReal (lowerLevelStep (f : X → ℝ) d N x) ∂levelCylinderMeasure V L) ≤
      ENNReal.ofReal (L f) := by
  letI := positiveLevelMeasurableSpace V
  rw [lowerLevelStep_lintegral V hStone L f d hd N]
  constructor
  · rw [← stripElement_sum_shift V hStone f hf d hd N, map_sum,
      ENNReal.ofReal_sum_of_nonneg (fun k _ =>
        hL.nonneg _ (stripElement_nonneg V hStone f hf d hd (k+1)))]
    exact Finset.sum_le_sum (fun k _ => strip_mass_upper V hV hStone L hL f hf d hd k)
  · calc
      _ ≤ ∑ k ∈ Finset.range N, ENNReal.ofReal
          (L (stripElement V hStone f hf d hd k)) :=
        Finset.sum_le_sum (fun k _ => strip_mass_lower V hV hStone L hL f hf d hd k)
      _ = ENNReal.ofReal (L (cappedElement V hStone f hf ((N : ℝ) * d) (by positivity))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
          hL.nonneg _ (stripElement_nonneg V hStone f hf d hd k)),
          ← map_sum, stripElement_sum V hStone f hf d hd N]
      _ ≤ ENNReal.ofReal (L f) := ENNReal.ofReal_le_ofReal (hL.mono (fun x => min_le_left _ _))

/-- Elementary lower bounds for the dyadic level sums. -/
def dyadicCapDifference (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (n : ℕ) : V :=
  cappedElement V hStone f hf (n : ℝ) (Nat.cast_nonneg n) -
    cappedElement V hStone f hf ((2 : ℝ)⁻¹ ^ n) (by positivity)

lemma dyadic_mesh (n : ℕ) :
    ((n * 2^n : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ n) = (n : ℝ) := by
  push_cast
  rw [inv_pow, mul_assoc (n : ℝ), mul_inv_cancel₀ (by positivity), mul_one]

lemma dyadicCapDifference_mono (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (x : X) :
    Monotone (fun n => (dyadicCapDifference V hStone f hf n : X → ℝ) x) := by
  intro i j hij
  change min _ (i : ℝ) - min _ ((2 : ℝ)⁻¹ ^ i) ≤
    min _ (j : ℝ) - min _ ((2 : ℝ)⁻¹ ^ j)
  exact sub_le_sub (min_le_min_left _ (by exact_mod_cast hij))
    (min_le_min_left _ (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij))

lemma dyadicCapDifference_tendsto (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (x : X) :
    Tendsto (fun n => (dyadicCapDifference V hStone f hf n : X → ℝ) x) atTop
      (𝓝 ((f : X → ℝ) x)) := by
  have hcap : Tendsto (fun n : ℕ => min ((f : X → ℝ) x) (n : ℝ)) atTop
      (𝓝 ((f : X → ℝ) x)) := by
    apply tendsto_const_nhds.congr'
    have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually (eventually_ge_atTop ((f : X → ℝ) x))] with n hn
    exact (min_eq_left hn).symm
  have hsmall := (tendsto_const_nhds (x := (f : X → ℝ) x)).min
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num))
  have h := hcap.sub hsmall
  simpa [dyadicCapDifference, cappedElement, min_eq_right (hf x)] using h

include hStone in
lemma dyadicStep_bounds (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (n : ℕ) (x : X) :
    (dyadicCapDifference V hStone f hf n : X → ℝ) x ≤
      lowerLevelStep (f : X → ℝ) ((2 : ℝ)⁻¹ ^ n) (n * 2^n) x ∧
    lowerLevelStep (f : X → ℝ) ((2 : ℝ)⁻¹ ^ n) (n * 2^n) x ≤ (f : X → ℝ) x := by
  have hb := lowerLevelStep_bounds V hStone f hf ((2 : ℝ)⁻¹ ^ n) (by positivity) (n * 2^n) x
  constructor
  · apply le_trans ?_ hb.1
    change min _ (n : ℝ) - min _ _ ≤ min _ _ - min _ _
    apply sub_le_sub_right
    apply min_le_min_left
    have he := dyadic_mesh n
    nlinarith [show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity]
  · exact hb.2.trans (min_le_left _ _)

include hV hL in
lemma dyadicStep_integral_bounds (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) (n : ℕ) :
    letI := positiveLevelMeasurableSpace V
    ENNReal.ofReal (L (dyadicCapDifference V hStone f hf n)) ≤
      (∫⁻ x, ENNReal.ofReal (lowerLevelStep (f : X → ℝ) ((2 : ℝ)⁻¹ ^ n) (n * 2^n) x)
        ∂levelCylinderMeasure V L) ∧
    (∫⁻ x, ENNReal.ofReal (lowerLevelStep (f : X → ℝ) ((2 : ℝ)⁻¹ ^ n) (n * 2^n) x)
        ∂levelCylinderMeasure V L) ≤ ENNReal.ofReal (L f) := by
  letI := positiveLevelMeasurableSpace V
  have hb := lowerLevelStep_integral_bounds V hV hStone L hL f hf
    ((2 : ℝ)⁻¹ ^ n) (by positivity) (n * 2^n)
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal (hL.mono (fun x => ?_))) hb.1, hb.2⟩
  change min _ (n : ℝ) - min _ _ ≤ min _ _ - min _ _
  apply sub_le_sub_right
  apply min_le_min_left
  have he := dyadic_mesh n
  nlinarith [show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity]

end

/-- Fatou and the telescoping elementary bounds identify the nonnegative integral.
The dyadic lower steps are exactly the strict-level steps in the manuscript. -/
theorem nonnegative_cylinder_integral : Specs.NonnegativeCylinderIntegral := by
  intro X V hV hStone L hL f hf
  letI := positiveLevelMeasurableSpace V
  refine ⟨nonnegative_undergraph_mass V hV L hL f hf, ?_⟩
  let s : ℕ → X → ℝ := fun n => lowerLevelStep (f : X → ℝ) ((2 : ℝ)⁻¹ ^ n) (n * 2^n)
  have hsm (n : ℕ) : Measurable (s n) := lowerLevelStep_measurable V f _ (by positivity) _
  have hslim (x : X) : Tendsto (fun n => s n x) atTop (𝓝 ((f : X → ℝ) x)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (dyadicCapDifference_tendsto V hStone f hf x) tendsto_const_nhds
      (fun n => (dyadicStep_bounds V hStone f hf n x).1)
      (fun n => (dyadicStep_bounds V hStone f hf n x).2)
  have hsbound (n : ℕ) := dyadicStep_integral_bounds V hV hStone L hL f hf n
  apply le_antisymm
  · calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (s n x)) atTop ∂levelCylinderMeasure V L := by
        apply lintegral_congr
        intro x
        exact ((ENNReal.continuous_ofReal.tendsto _ |>.comp (hslim x)).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (s n x) ∂levelCylinderMeasure V L) atTop :=
        lintegral_liminf_le (fun n => (hsm n).ennreal_ofReal)
      _ ≤ ENNReal.ofReal (L f) :=
        liminf_le_of_frequently_le' (Filter.Frequently.of_forall (fun n => (hsbound n).2))
  · have hconv := (IsElementaryIntegral.monotone_convergence hL f (dyadicCapDifference V hStone f hf)
        (dyadicCapDifference_mono V hStone f hf)
        (dyadicCapDifference_tendsto V hStone f hf)).2
    apply le_of_tendsto' (ENNReal.continuous_ofReal.tendsto _ |>.comp hconv)
    intro n
    exact (hsbound n).1.trans (lintegral_mono (fun x =>
      ENNReal.ofReal_le_ofReal ((dyadicStep_bounds V hStone f hf n x).2)))

/-- Integrability is proved before using any scalar integral identity. -/
theorem nonnegative_cylinder_integrable {X : Type u} (V : Submodule ℝ (X → ℝ))
    (hV : IsVectorLattice V) (hStone : IsStone V) (L : V →ₗ[ℝ] ℝ)
    (hL : IsElementaryIntegral V L) (f : V) (hf : ∀ x, 0 ≤ (f : X → ℝ) x) :
    letI := positiveLevelMeasurableSpace V
    Integrable (f : X → ℝ) (levelCylinderMeasure V L) ∧
      (∫ x, (f : X → ℝ) x ∂levelCylinderMeasure V L) = L f := by
  letI := positiveLevelMeasurableSpace V
  have hm := measurable_of_mem V hV f f.property
  have he := (nonnegative_cylinder_integral V hV hStone L hL f hf).2
  have hi : Integrable (f : X → ℝ) (levelCylinderMeasure V L) := by
    refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_norm _).mpr ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _), he] using
      (ENNReal.ofReal_lt_top : ENNReal.ofReal (L f) < ∞)
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf)
    hm.aestronglyMeasurable, he, ENNReal.toReal_ofReal (hL.nonneg f hf)]

/-- Signed representation by the positive and negative parts in the same V. -/
theorem levelCylinder_integral_representation : Specs.LevelCylinderIntegralRepresentation := by
  intro X V hV hStone L hL f
  letI := positiveLevelMeasurableSpace V
  let p : V := ⟨fun x => max ((f : X → ℝ) x) 0, positivePart_mem V hV f f.property⟩
  let m : V := ⟨fun x => max (-((f : X → ℝ) x)) 0, negativePart_mem V hV f f.property⟩
  have hp := nonnegative_cylinder_integrable V hV hStone L hL p (fun _ => le_max_right _ _)
  have hm := nonnegative_cylinder_integrable V hV hStone L hL m (fun _ => le_max_right _ _)
  have he : f = p - m := by
    apply Subtype.ext
    funext x
    change (f : X → ℝ) x = max ((f : X → ℝ) x) 0 - max (-((f : X → ℝ) x)) 0
    rcases le_total 0 ((f : X → ℝ) x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
      ring
  refine ⟨measurable_of_mem V hV f f.property, ?_, ?_⟩
  · rw [he]
    exact hp.1.sub hm.1
  · have hcoe : (f : X → ℝ) = fun x => (p : X → ℝ) x - (m : X → ℝ) x :=
      congrArg (fun g : V => (g : X → ℝ)) he
    rw [hcoe, integral_sub hp.1 hm.1, hp.2, hm.2, ← map_sub, ← he]

end D11.Ch23
