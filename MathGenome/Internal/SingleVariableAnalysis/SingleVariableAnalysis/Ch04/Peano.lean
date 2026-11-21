import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch02.BigO
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Peano
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# First-order Peano approximation

K03.04.peano, paper.tex:660–671. The remainder is the increment minus its
linear part. Mathlib's first-order derivative characterization applies to real
increments in any real normed target, hence in particular to ℝ and ℂ.
The identity forces the canonical remainder to be zero at h = 0; this is why
its little-o statement on the punctured neighborhood extends to the full one.
For a domain I, interiority makes the remainder identity hold near zero.
-/

namespace SingleVariableAnalysis

open Filter
open scoped Topology
universe u

theorem derivative_iff_remainder_littleO {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
        (fun h => f (a + h) - f a - h • L) (fun h : ℝ => h) := by
  rw [hasRealIncrementDerivative_iff_hasDerivAt, hasDerivAt_iff_isLittleO_nhds_zero]
  constructor
  · exact fun h => h.mono nhdsWithin_le_nhds
  · intro h
    have hi := h.insert (by simp)
    have hs : insert (0 : ℝ) ({0} : Set ℝ)ᶜ = Set.univ := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_univ, iff_true]
      exact Classical.em _
    simpa only [hs, nhdsWithin_univ] using hi

theorem derivative_iff_peano {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      ∃ r : ℝ → F, (∀ h : ℝ, f (a + h) = f a + h • L + r h) ∧
        Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h) := by
  rw [derivative_iff_remainder_littleO]
  constructor
  · intro hr
    refine ⟨fun h => f (a + h) - f a - h • L, ?_, hr⟩
    intro h
    dsimp only
    abel
  · rintro ⟨r, heq, hr⟩
    apply hr.congr_left
    intro h
    rw [heq h]
    abel

theorem withinDerivative_interior_iff_peano {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) :
    HasRealIncrementDerivativeWithin f L I a ↔
      ∃ r : ℝ → F, (∀ h : ℝ, a + h ∈ I → f (a + h) = f a + h • L + r h) ∧
        Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h) := by
  rw [withinDerivative_interior_iff f L I a ha,
    ← hasRealIncrementDerivative_iff_hasDerivAt]
  constructor
  · intro hd
    obtain ⟨r, heq, hr⟩ := (derivative_iff_peano f L a).mp hd
    exact ⟨r, fun h _ => heq h, hr⟩
  · rintro ⟨r, heq, hr⟩
    apply (derivative_iff_remainder_littleO f L a).mpr
    have hI : ∀ᶠ h : ℝ in 𝓝 (0 : ℝ), a + h ∈ I := by
      have hc : ContinuousAt (fun h : ℝ => a + h) 0 := continuousAt_const.add continuousAt_id
      exact hc (by simpa only [add_zero] using mem_interior_iff_mem_nhds.mp ha)
    apply hr.congr' _ (Filter.EventuallyEq.rfl)
    filter_upwards [hI.filter_mono nhdsWithin_le_nhds] with h hh
    rw [heq h hh]
    abel

theorem real_derivative_iff_peano (f : ℝ → ℝ) (L a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      ∃ r : ℝ → ℝ, (∀ h : ℝ, f (a + h) = f a + L * h + r h) ∧
        ScalarLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => h) := by
  simpa only [scalarLittleO_iff_isLittleO, smul_eq_mul, mul_comm] using
    derivative_iff_peano f L a

theorem complex_derivative_iff_peano (f : ℝ → ℂ) (L : ℂ) (a : ℝ) :
    HasRealIncrementDerivative f L a ↔
      ∃ r : ℝ → ℂ, (∀ h : ℝ, f (a + h) = f a + L * (h : ℂ) + r h) ∧
        ScalarLittleO (𝓝[≠] (0 : ℝ)) r (fun h : ℝ => (h : ℂ)) := by
  simpa only [ScalarLittleO, Asymptotics.isLittleO_iff, Complex.norm_real,
    Complex.real_smul, mul_comm] using derivative_iff_peano f L a

theorem incrementDerivative_continuousAt {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (a : ℝ)
    (hd : HasRealIncrementDerivative f L a) : ContinuousAt f a :=
  ((hasRealIncrementDerivative_iff_hasDerivAt f L a).mp hd).continuousAt

theorem withinDerivative_interior_continuousAt {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ)
    (ha : a ∈ interior I) (hd : HasRealIncrementDerivativeWithin f L I a) :
    ContinuousAt f a :=
  ((withinDerivative_interior_iff f L I a ha).mp hd).continuousAt

theorem differentiableAt_continuousAt {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ → F) (a : ℝ) (hd : DifferentiableAt ℝ f a) :
    ContinuousAt f a := hd.continuousAt

theorem abs_zero_right_quotient :
    RightRelativeLimit (RealIncrementQuotient (abs : ℝ → ℝ) 0) Set.univ 0 1 := by
  constructor
  · intro δ hδ
    exact ⟨δ / 2, Set.mem_univ _, by simpa [ApproachRegion] using
      (show 0 < δ / 2 ∧ δ / 2 < δ from ⟨half_pos hδ, half_lt_self hδ⟩)⟩
  · intro ε hε
    refine ⟨1, zero_lt_one, fun h _ hh => ?_⟩
    have hp : 0 < h := hh.1
    simpa [RealIncrementQuotient, abs_of_pos hp, inv_mul_cancel₀ hp.ne', Real.dist_eq]
      using hε

theorem abs_zero_left_quotient :
    LeftRelativeLimit (RealIncrementQuotient (abs : ℝ → ℝ) 0) Set.univ 0 (-1) := by
  constructor
  · intro δ hδ
    exact ⟨-δ / 2, Set.mem_univ _, by
      change 0 - δ < -δ / 2 ∧ -δ / 2 < 0
      constructor <;> linarith⟩
  · intro ε hε
    refine ⟨1, zero_lt_one, fun h _ hh => ?_⟩
    have hn : h < 0 := hh.2
    simpa [RealIncrementQuotient, abs_of_neg hn, inv_mul_cancel₀ hn.ne,
      Real.dist_eq] using hε

theorem abs_zero_counterexample :
    ContinuousAt (abs : ℝ → ℝ) 0 ∧
      RightRelativeLimit (RealIncrementQuotient (abs : ℝ → ℝ) 0) Set.univ 0 1 ∧
      LeftRelativeLimit (RealIncrementQuotient (abs : ℝ → ℝ) 0) Set.univ 0 (-1) ∧
      (1 : ℝ) ≠ -1 ∧
      (¬ ∃ L : ℝ, HasRealIncrementDerivative (abs : ℝ → ℝ) L 0) ∧
      ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  refine ⟨continuous_abs.continuousAt, abs_zero_right_quotient, abs_zero_left_quotient,
    by norm_num, ?_, not_differentiableAt_abs_zero⟩
  rintro ⟨L, hL⟩
  exact not_differentiableAt_abs_zero
    (((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hL).differentiableAt)

end SingleVariableAnalysis
