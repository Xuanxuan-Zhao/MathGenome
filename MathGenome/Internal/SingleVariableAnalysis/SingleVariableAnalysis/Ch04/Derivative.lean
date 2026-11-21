import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.RelativeLimit
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-!
# Derivatives with real increments

Implements K03.04.derivative (paper.tex:637–649). The quotient is multiplied
by the inverse of a real increment, even when the value is complex. Its value
at increment zero is irrelevant to the punctured limit.

For a function on an interval I we use an ambient extension, with increments
restricted by a+h ∈ I. Every interval function has such an extension, and the
congruence theorem proves independence of that choice. At an interior point
this definition is exactly `HasDerivAt` with base field ℝ. The proof works for
any real normed target, in particular the manuscript's ℝ and ℂ.
-/

namespace SingleVariableAnalysis

open scoped Topology
universe u

noncomputable def RealIncrementQuotient {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a h : ℝ) : F :=
  h⁻¹ • (f (a + h) - f a)

def HasRealIncrementDerivative {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a : ℝ) : Prop :=
  RelativePuncturedLimit (RealIncrementQuotient f a) Set.univ 0 L

def HasRealIncrementDerivativeWithin {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) : Prop :=
  RelativePuncturedLimit (RealIncrementQuotient f a) {h : ℝ | a + h ∈ I} 0 L

theorem hasRealIncrementDerivative_iff_hasDerivAt {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔ HasDerivAt f L a := by
  rw [HasRealIncrementDerivative, relativePuncturedLimit_filter_iff,
    PuncturedDomainFilter, ← Set.compl_eq_univ_sdiff]
  exact (hasDerivAt_iff_tendsto_slope_zero (f := f) (f' := L) (x := a)).symm

theorem realDerivative_epsilon_iff (f : ℝ → ℝ) (L a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, 0 < |h| → |h| < δ → |(f (a + h) - f a) / h - L| < ε := by
  simp only [HasRealIncrementDerivative, RelativePuncturedLimit, Real.dist_eq,
    sub_zero, Set.mem_univ, forall_true_left, RealIncrementQuotient,
    smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem complexDerivative_epsilon_iff (f : ℝ → ℂ) (L : ℂ) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, 0 < |h| → |h| < δ →
          ‖(f (a + h) - f a) / (h : ℂ) - L‖ < ε := by
  simp only [HasRealIncrementDerivative, RelativePuncturedLimit, dist_eq_norm,
    Real.norm_eq_abs, sub_zero, Set.mem_univ, forall_true_left,
    RealIncrementQuotient, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

theorem withinDerivative_epsilon_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ) :
    HasRealIncrementDerivativeWithin f L I a ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ h : ℝ, a + h ∈ I → 0 < |h| → |h| < δ →
          ‖RealIncrementQuotient f a h - L‖ < ε := by
  simp only [HasRealIncrementDerivativeWithin, RelativePuncturedLimit,
    dist_eq_norm, Real.norm_eq_abs, sub_zero, Set.mem_ofPred_eq]

theorem withinDerivative_interior_iff {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) :
    HasRealIncrementDerivativeWithin f L I a ↔ HasDerivAt f L a := by
  rw [← hasRealIncrementDerivative_iff_hasDerivAt]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  constructor
  · intro hd ε hε
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    refine ⟨min δ r, lt_min hδ hr, fun h _ hp hlt => ?_⟩
    have hh : a + h ∈ I := hball (by
      simpa only [Metric.mem_ball, Real.dist_eq, add_sub_cancel_left, sub_zero] using
        (lt_of_lt_of_le hlt (min_le_right δ r)))
    exact hb h hh hp (lt_of_lt_of_le hlt (min_le_left δ r))
  · intro hd ε hε
    obtain ⟨δ, hδ, hb⟩ := hd ε hε
    exact ⟨δ, hδ, fun h _ hp hlt => hb h (Set.mem_univ h) hp hlt⟩

theorem withinDerivative_congr {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f g : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ I) (hfg : Set.EqOn f g I) :
    HasRealIncrementDerivativeWithin f L I a ↔
      HasRealIncrementDerivativeWithin g L I a := by
  apply relativePuncturedLimit_congr
  intro h hh _
  simp only [RealIncrementQuotient, hfg hh, hfg ha]

theorem exists_ambientExtension {F : Type u} [NormedAddCommGroup F]
    (I : Set ℝ) (f : I → F) : ∃ g : ℝ → F, ∀ x : I, g x = f x := by
  classical
  refine ⟨fun x => if hx : x ∈ I then f ⟨x, hx⟩ else 0, ?_⟩
  intro x
  simp only [dite_eq_left x.property]

private theorem quotient_re (f : ℝ → ℂ) (a h : ℝ) :
    (RealIncrementQuotient f a h).re =
      RealIncrementQuotient (fun x => (f x).re) a h := by
  simp [RealIncrementQuotient, smul_eq_mul]

private theorem quotient_im (f : ℝ → ℂ) (a h : ℝ) :
    (RealIncrementQuotient f a h).im =
      RealIncrementQuotient (fun x => (f x).im) a h := by
  simp [RealIncrementQuotient, smul_eq_mul]

/-- The forward estimates are |Re z|, |Im z| ≤ ‖z‖. For the converse
use ‖z‖ ≤ |Re z| + |Im z| and a common radius for errors ε/2. -/
theorem complex_incrementDerivative_iff_components (f : ℝ → ℂ) (L : ℂ) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      HasRealIncrementDerivative (fun x => (f x).re) L.re a ∧
      HasRealIncrementDerivative (fun x => (f x).im) L.im a := by
  constructor
  · intro hd
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hd ε hε
      refine ⟨δ, hδ, fun h hh hp hlt => ?_⟩
      have hb' : ‖RealIncrementQuotient f a h - L‖ < ε := by
        simpa only [dist_eq_norm] using hb h hh hp hlt
      simpa only [dist_eq_norm, Real.norm_eq_abs, Complex.sub_re, quotient_re] using
        lt_of_le_of_lt (Complex.abs_re_le_norm (RealIncrementQuotient f a h - L)) hb'
    · intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hd ε hε
      refine ⟨δ, hδ, fun h hh hp hlt => ?_⟩
      have hb' : ‖RealIncrementQuotient f a h - L‖ < ε := by
        simpa only [dist_eq_norm] using hb h hh hp hlt
      simpa only [dist_eq_norm, Real.norm_eq_abs, Complex.sub_im, quotient_im] using
        lt_of_le_of_lt (Complex.abs_im_le_norm (RealIncrementQuotient f a h - L)) hb'
  · rintro ⟨hu, hv⟩ ε hε
    obtain ⟨δu, hδu, hbu⟩ := hu (ε / 2) (half_pos hε)
    obtain ⟨δv, hδv, hbv⟩ := hv (ε / 2) (half_pos hε)
    refine ⟨min δu δv, lt_min hδu hδv, fun h hh hp hlt => ?_⟩
    have hu' := hbu h hh hp (lt_of_lt_of_le hlt (min_le_left _ _))
    have hv' := hbv h hh hp (lt_of_lt_of_le hlt (min_le_right _ _))
    rw [dist_eq_norm]
    calc
      ‖RealIncrementQuotient f a h - L‖ ≤
          |(RealIncrementQuotient f a h - L).re| +
            |(RealIncrementQuotient f a h - L).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ < ε / 2 + ε / 2 := add_lt_add
        (by simpa only [Real.dist_eq, Complex.sub_re, quotient_re] using hu')
        (by simpa only [Real.dist_eq, Complex.sub_im, quotient_im] using hv')
      _ = ε := add_halves ε

theorem complex_hasDerivAt_iff_components (f : ℝ → ℂ) (L : ℂ) (a : ℝ) :
    HasDerivAt f L a ↔ HasDerivAt (fun x => (f x).re) L.re a ∧
      HasDerivAt (fun x => (f x).im) L.im a := by
  simpa only [hasRealIncrementDerivative_iff_hasDerivAt] using
    complex_incrementDerivative_iff_components f L a

theorem complex_differentiableAt_iff_components (f : ℝ → ℂ) (a : ℝ) :
    DifferentiableAt ℝ f a ↔ DifferentiableAt ℝ (fun x => (f x).re) a ∧
      DifferentiableAt ℝ (fun x => (f x).im) a := by
  constructor
  · intro hd
    have hc := (complex_hasDerivAt_iff_components f (deriv f a) a).mp hd.hasDerivAt
    exact ⟨hc.1.differentiableAt, hc.2.differentiableAt⟩
  · rintro ⟨hu, hv⟩
    apply HasDerivAt.differentiableAt (f' :=
      Complex.ofReal (deriv (fun x => (f x).re) a) +
        Complex.ofReal (deriv (fun x => (f x).im) a) * Complex.I)
    apply (complex_hasDerivAt_iff_components _ _ _).mpr
    simpa using And.intro hu.hasDerivAt hv.hasDerivAt

theorem complex_deriv_eq_components (f : ℝ → ℂ) (a : ℝ) (hd : DifferentiableAt ℝ f a) :
    deriv f a = Complex.ofReal (deriv (fun x => (f x).re) a) +
      Complex.ofReal (deriv (fun x => (f x).im) a) * Complex.I := by
  have hc := (complex_hasDerivAt_iff_components f (deriv f a) a).mp hd.hasDerivAt
  rw [hc.1.deriv, hc.2.deriv]
  exact (complex_pair_decomposition (deriv f a)).symm

theorem complex_ofComponents_hasDerivAt_iff (u v : ℝ → ℝ) (u' v' a : ℝ) :
    HasDerivAt (fun x => (u x : ℂ) + (v x : ℂ) * Complex.I)
      ((u' : ℂ) + (v' : ℂ) * Complex.I) a ↔
      HasDerivAt u u' a ∧ HasDerivAt v v' a := by
  simpa using complex_hasDerivAt_iff_components
    (fun x => (u x : ℂ) + (v x : ℂ) * Complex.I)
    ((u' : ℂ) + (v' : ℂ) * Complex.I) a

end SingleVariableAnalysis
