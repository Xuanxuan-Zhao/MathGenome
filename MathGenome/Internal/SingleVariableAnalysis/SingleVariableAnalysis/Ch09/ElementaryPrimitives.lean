import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.ElementaryDerivatives
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.Tan
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.Primitive
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.IntegerPowers
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
Elementary primitive formulas (K03.09.elementary_primitives).
Differentiate the upstream elementary functions, then apply primitive
uniqueness on each interval. A separate gluing result makes explicit that
constants can be chosen independently on disjoint open components.
-/
noncomputable section
namespace SingleVariableAnalysis.ElementaryPrimitives
open Set
open scoped Topology
open Specs.SingleVariableAnalysis.Ch09.ElementaryPrimitives

/-- Derivatives on a domain give the complete primitive family on each interval. -/
theorem formulaOn_of_hasDerivAt (F f : ℝ → ℝ) (D : Set ℝ)
    (hd : ∀ x ∈ D, HasDerivAt F (f x) x) : formulaOn F f D := by
  refine ⟨hd, ?_⟩
  intro I hI hID
  have hF : ContinuousPrimitiveOn F f I :=
    ⟨fun x hx => (hd x (hID hx)).continuousAt.continuousWithinAt,
      fun x hx => hd x (hID (interior_subset hx))⟩
  refine ⟨hF, fun G => ⟨?_, ?_⟩⟩
  · intro hG
    obtain ⟨c, hc⟩ := real_primitives_differ_by_constant G F f I hI hG hF
    exact ⟨c, fun x hx => by linarith [hc x hx]⟩
  · rintro ⟨c, hc⟩
    have hEq : EqOn G (fun x => F x + c) I := hc
    refine ⟨(hF.1.add continuousOn_const).congr hEq, ?_⟩
    intro x hx
    apply ((hF.2 x hx).add_const c).congr_of_eventuallyEq
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hc y hy

theorem power_primitive : powerPrimitive := by
  intro α hα
  apply formulaOn_of_hasDerivAt
  intro x hx
  have ha : α + 1 ≠ 0 := by exact fun h => hα (by linarith)
  have h := (realPower_hasDerivAt (α + 1) x hx).div_const (α + 1)
  simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ ha] using h

theorem natural_power_primitive : naturalPowerPrimitive := by
  intro n
  apply formulaOn_of_hasDerivAt
  intro x _
  have ha : (n : ℝ) + 1 ≠ 0 := by positivity
  have h := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
    mul_div_cancel_left₀ _ ha] using h

/-- The logarithm of the absolute value, on both sides of zero. -/
theorem log_abs_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => seriesLog |t|) (1 / x) x := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have h := (seriesLog_hasDerivAt (-x) (neg_pos.mpr hn)).comp x
      ((hasDerivAt_id x).neg)
    have hd : HasDerivAt (fun t => seriesLog (-t)) (1 / x) x := by
      convert h using 1 <;> first | rfl | field_simp
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hn] with y hy
    rw [abs_of_neg hy]
  · have hd := seriesLog_hasDerivAt x hp
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hp] with y hy
    change seriesLog |y| = seriesLog y
    rw [abs_of_pos hy]

theorem reciprocal_primitive : reciprocalPrimitive := by
  apply formulaOn_of_hasDerivAt
  exact log_abs_hasDerivAt

theorem exponential_primitive : exponentialPrimitive := by
  intro a ha
  apply formulaOn_of_hasDerivAt
  intro x _
  have h := ((real_expSeries_derivative (a * x)).comp x
    ((hasDerivAt_id x).const_mul a)).div_const a
  convert! h using 1
  simp only [mul_one, mul_div_cancel_right₀ _ ha]

theorem zero_exponential_primitive : zeroExponentialPrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x _
  convert! hasDerivAt_id x using 1
  simp only [zero_mul, expSeries_eq_realExp 0, Real.exp_zero]

theorem sine_primitive : sinePrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x _
  exact (real_sinCosSeries_hasDerivAt x).1

theorem negative_cosine_primitive : negativeCosinePrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x _
  convert! (real_sinCosSeries_hasDerivAt x).2.neg using 1
  simp only [neg_neg]

theorem arctangent_primitive : arctangentPrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x _
  exact TrigInverses.inverse_derivatives.2.2 x

theorem arcsine_primitive : arcsinePrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x hx
  exact TrigInverses.inverse_derivatives.1 x hx

theorem tangent_primitive : tangentPrimitive := by
  apply formulaOn_of_hasDerivAt
  intro x hx
  have hc := (real_sinCosSeries_hasDerivAt x).2
  have h := ((log_abs_hasDerivAt (realSeriesCos x) hx).comp x hc).neg
  convert h using 1 <;> first
  | rfl
  | change realSeriesSin x / realSeriesCos x = -(1 / realSeriesCos x * -realSeriesSin x)
    ring

/-- Complex counterpart of the interval-family argument. -/
theorem complexFormulaOn_of_hasDerivAt (F f : ℝ → ℂ) (D : Set ℝ)
    (hd : ∀ x ∈ D, HasDerivAt F (f x) x) : complexFormulaOn F f D := by
  refine ⟨hd, ?_⟩
  intro I hI hID
  have hF : ContinuousPrimitiveOn F f I :=
    ⟨fun x hx => (hd x (hID hx)).continuousAt.continuousWithinAt,
      fun x hx => hd x (hID (interior_subset hx))⟩
  refine ⟨hF, fun G => ⟨?_, ?_⟩⟩
  · intro hG
    obtain ⟨c, hc⟩ := complex_primitives_differ_by_constant G F f I hI hG hF
    exact ⟨c, fun x hx => (sub_eq_iff_eq_add.mp (hc x hx)).trans (add_comm _ _)⟩
  · rintro ⟨c, hc⟩
    have hEq : EqOn G (fun x => F x + c) I := hc
    refine ⟨(hF.1.add continuousOn_const).congr hEq, ?_⟩
    intro x hx
    apply ((hF.2 x hx).add_const c).congr_of_eventuallyEq
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with y hy
    exact hc y hy

theorem complex_lift : complexLift := by
  intro F f D hF
  apply complexFormulaOn_of_hasDerivAt
  intro x hx
  exact (hF.1 x hx).ofReal_comp

theorem complex_exponential_primitive : complexExponentialPrimitive := by
  intro a ha
  apply complexFormulaOn_of_hasDerivAt
  intro x _
  have he : seriesExp = Complex.exp := funext expSeries_eq_complexExp
  change HasDerivAt (fun t : ℝ => seriesExp (a * (t : ℂ)) / a)
    (seriesExp (a * (x : ℂ))) x
  rw [he]
  have hlin : HasDerivAt (fun t : ℝ => a * (t : ℂ)) a x := by
    convert! Complex.ofRealCLM.hasDerivAt.const_mul a using 1
    simp
  have h := ((Complex.hasDerivAt_exp (a * (x : ℂ))).comp x hlin).div_const a
  convert! h using 1
  simp only [mul_div_cancel_right₀ _ ha]

theorem complex_zero_exponential_primitive : complexZeroExponentialPrimitive := by
  apply complexFormulaOn_of_hasDerivAt
  intro x _
  change HasDerivAt (fun t : ℝ => (t : ℂ)) (seriesExp ((0 : ℂ) * (x : ℂ))) x
  have hcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) x :=
    (hasDerivAt_id x).ofReal_comp
  convert hcast using 1
  rw [zero_mul]
  exact (expSeries_eq_complexExp 0).trans Complex.exp_zero

/-- Gluing arbitrary constant shifts on pairwise disjoint open pieces. -/
theorem primitive_component_gluing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F f : ℝ → E) (D : Set ℝ) (hd : ∀ x ∈ D, HasDerivAt F (f x) x)
    (ι : Type) (I : ι → Set ℝ) (ho : ∀ i, IsOpen (I i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (I i) (I j)) (hsub : ∀ i, I i ⊆ D)
    (c : ι → E) : ∃ G : ℝ → E,
      IsPrimitiveOn G f (⋃ i, I i) ∧ ∀ i, ∀ x ∈ I i, G x = F x + c i := by
  classical
  let G : ℝ → E := fun x =>
    if h : ∃ i, x ∈ I i then F x + c h.choose else F x
  have hEq (i : ι) (x : ℝ) (hx : x ∈ I i) : G x = F x + c i := by
    have he : ∃ j, x ∈ I j := ⟨i, hx⟩
    have hi : he.choose = i := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj he.choose i hne) he.choose_spec hx
    simp only [G, dite_eq_left he, hi]
  refine ⟨G, ?_, hEq⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hx)
  apply ((hd x (hsub i hi)).add_const (c i)).congr_of_eventuallyEq
  filter_upwards [(ho i).mem_nhds hi] with y hy
  exact hEq i y hy

theorem independent_component_constants : independentComponentConstants := by
  intro F f D hF
  exact primitive_component_gluing F f D hF.1

theorem independent_complex_component_constants : independentComplexComponentConstants := by
  intro F f D hF
  exact primitive_component_gluing F f D hF.1

end SingleVariableAnalysis.ElementaryPrimitives
