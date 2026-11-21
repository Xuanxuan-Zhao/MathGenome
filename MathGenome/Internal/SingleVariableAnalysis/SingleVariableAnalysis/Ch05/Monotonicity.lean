import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Monotonicity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch05.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
K03.05.monotonicity. Each forward criterion follows from the upstream real
mean value equality on a segment contained in I. An intermediate point is
interior to I even when I has included endpoints. Necessity uses Mathlib's
nonnegative derivative of a monotone function within a neighborhood. The
last two results verify the manuscript's exact counterexamples.
-/
namespace SingleVariableAnalysis

open Set
open scoped Topology

private theorem monotonicity_secant (f : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hxy : x < y) :
    ∃ c ∈ interior I, f y - f x = deriv f c * (y - x) := by
  have hsub : Icc x y ⊆ I := hI.out hx hy
  have hint : Ioo x y ⊆ interior I := by
    rw [← interior_Icc]
    exact interior_mono hsub
  obtain ⟨c, hc, heq⟩ := lagrange_deriv f x y hxy (hf.mono hsub)
    (fun z hz => hd z (hint hz))
  exact ⟨c, hint hc, heq⟩

theorem nonnegative_derivative_monotone (f : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hs : ∀ x ∈ interior I, 0 ≤ deriv f x) : MonotoneOn f I := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with heq | hlt
  · exact heq ▸ le_rfl
  obtain ⟨c, hc, heq⟩ := monotonicity_secant f I hI hf hd hx hy hlt
  have := mul_nonneg (hs c hc) (sub_nonneg.mpr hxy)
  linarith

theorem positive_derivative_strictMono (f : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hs : ∀ x ∈ interior I, 0 < deriv f x) : StrictMonoOn f I := by
  intro x hx y hy hxy
  obtain ⟨c, hc, heq⟩ := monotonicity_secant f I hI hf hd hx hy hxy
  have := mul_pos (hs c hc) (sub_pos.mpr hxy)
  linarith

theorem nonpositive_derivative_antitone (f : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hs : ∀ x ∈ interior I, deriv f x ≤ 0) : AntitoneOn f I := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with heq | hlt
  · exact heq ▸ le_rfl
  obtain ⟨c, hc, heq⟩ := monotonicity_secant f I hI hf hd hx hy hlt
  have := mul_nonpos_of_nonpos_of_nonneg (hs c hc) (sub_nonneg.mpr hxy)
  linarith

theorem negative_derivative_strictAnti (f : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : ContinuousOn f I)
    (hd : ∀ x ∈ interior I, DifferentiableAt ℝ f x)
    (hs : ∀ x ∈ interior I, deriv f x < 0) : StrictAntiOn f I := by
  intro x hx y hy hxy
  obtain ⟨c, hc, heq⟩ := monotonicity_secant f I hI hf hd hx hy hxy
  have := mul_neg_of_neg_of_pos (hs c hc) (sub_pos.mpr hxy)
  linarith

theorem monotone_derivative_nonnegative (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hf : MonotoneOn f I) (ha : a ∈ interior I) (hd : HasDerivAt f L a) : 0 ≤ L := by
  have h := hf.derivWithin_nonneg (x := a)
  rw [derivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp ha), hd.deriv] at h
  exact h

theorem realIncrement_monotonicity (f d : ℝ → ℝ) (I : Set ℝ)
    (hI : OrdConnected I) (hf : RelativeContinuous f I)
    (hd : ∀ x ∈ interior I, HasRealIncrementDerivativeWithin f (d x) I x) :
    ((∀ x ∈ interior I, 0 ≤ d x) → MonotoneOn f I) ∧
    ((∀ x ∈ interior I, 0 < d x) → StrictMonoOn f I) ∧
    ((∀ x ∈ interior I, d x ≤ 0) → AntitoneOn f I) ∧
    ((∀ x ∈ interior I, d x < 0) → StrictAntiOn f I) := by
  have hder x (hx : x ∈ interior I) : HasDerivAt f (d x) x :=
    (withinDerivative_interior_iff f (d x) I x hx).mp (hd x hx)
  have hdiff x hx := (hder x hx).differentiableAt
  have hcont := relativeContinuous_continuousOn f I hf
  refine ⟨fun hs => nonnegative_derivative_monotone f I hI hcont hdiff ?_,
    fun hs => positive_derivative_strictMono f I hI hcont hdiff ?_,
    fun hs => nonpositive_derivative_antitone f I hI hcont hdiff ?_,
    fun hs => negative_derivative_strictAnti f I hI hcont hdiff ?_⟩ <;>
    intro x hx <;> rw [(hder x hx).deriv] <;> exact hs x hx

theorem realIncrement_monotonicity_necessity (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ)
    (hf : MonotoneOn f I) (ha : a ∈ interior I)
    (hd : HasRealIncrementDerivativeWithin f L I a) : 0 ≤ L :=
  monotone_derivative_nonnegative f I a L hf ha
    ((withinDerivative_interior_iff f L I a ha).mp hd)

theorem monotonicity_cube_counterexample :
    StrictMono (fun x : ℝ => x ^ 3) ∧
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x) ∧
    HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  exact ⟨(by decide : Odd 3).strictMono_pow, hd, by simpa using hd 0⟩

theorem monotonicity_endpoint_counterexample :
    (∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => if t = 0 then 2 else t) 1 x) ∧
    ¬ MonotoneOn (fun t : ℝ => if t = 0 then 2 else t) (Icc 0 1) := by
  constructor
  · intro x hx
    apply (hasDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (ne_of_gt hx.1)] with t ht
    simp [ht]
  · intro h
    have hb := h (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
      (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by norm_num)
    norm_num at hb

end SingleVariableAnalysis
