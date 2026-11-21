import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch06.SmoothFlat
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Analyticity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.Uniqueness
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic

/-! The flat function has a convergent Taylor series at every real argument,
but that series represents it only at zero. Coefficient recovery excludes any
other local power series, proving failure of real analyticity at the origin.
-/
noncomputable section
namespace SingleVariableAnalysis
open Filter
open scoped Topology BigOperators

/-- The usual Taylor coefficients at zero of the source's flat function. -/
def flatExponentialTaylorCoefficient (n : ℕ) : ℝ :=
  iteratedDeriv n flatExponential 0 / (n.factorial : ℝ)

@[simp] theorem flatExponential_taylorCoefficient_zero (n : ℕ) :
    flatExponentialTaylorCoefficient n = 0 := by
  have h : iteratedDeriv n flatExponential 0 = 0 :=
    flatExponential_all_derivatives_zero n
  simp [flatExponentialTaylorCoefficient, h]

@[simp] theorem flatExponential_taylorPartialSum_zero (x : ℝ) (N : ℕ) :
    realPowerSeriesPartialSum flatExponentialTaylorCoefficient 0 x N = 0 := by
  simp [realPowerSeriesPartialSum, realPartialSum, realPowerSeriesTerm]

/-- Convergence is ordinary ordered convergence, at every real input. -/
theorem flatExponential_taylorSeries_hasSum_zero (x : ℝ) :
    RealPowerSeriesHasSum flatExponentialTaylorCoefficient 0 x 0 := by
  apply (real_powerSeries_hasSum_iff _ _ _ _).mpr
  intro ε hε
  exact ⟨0, fun N _ => by simpa using hε⟩

theorem flatExponential_taylorSeries_differs (x : ℝ) (hx : x ≠ 0) :
    ¬ RealPowerSeriesHasSum flatExponentialTaylorCoefficient 0 x (flatExponential x) := by
  intro hs
  have he := real_powerSeries_sum_unique _ _ _ _ _
    (flatExponential_taylorSeries_hasSum_zero x) hs
  exact (ne_of_gt (flatExponential_pos x hx)) he.symm

theorem flatExponential_noTaylorNeighborhood :
    Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic.noTaylorNeighborhood := by
  intro r hr
  refine ⟨r / 2, ?_, ?_, ?_⟩
  · rw [abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  · rw [abs_of_pos (by linarith : 0 < r / 2)]
    linarith
  · exact flatExponential_taylorSeries_differs _ (ne_of_gt (by linarith))

/-- A local representing series must have the Taylor coefficients, all zero. -/
theorem flatExponential_noPowerSeriesNeighborhood :
    Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic.noPowerSeriesNeighborhood := by
  rintro ⟨a, r, hr, hs⟩
  have hlocal : ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, |x - 0| < r →
      RealPowerSeriesHasSum a 0 x (flatExponential x) :=
    ⟨r, hr, fun x hx => hs x (by simpa using hx)⟩
  have ha : a = flatExponentialTaylorCoefficient := by
    funext k
    have hd := (real_powerSeries_coefficient_formula a 0 flatExponential hlocal k).1
    have hz : iteratedDeriv k flatExponential 0 = 0 :=
      flatExponential_all_derivatives_zero k
    rw [hz] at hd
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    simpa using (mul_eq_zero.mp hd.symm).resolve_left hk
  have hs' : RealPowerSeriesHasSum flatExponentialTaylorCoefficient 0 (r / 2)
      (flatExponential (r / 2)) := by
    rw [← ha]
    exact hs _ (by rw [abs_of_pos (by linarith : 0 < r / 2)]; linarith)
  exact flatExponential_taylorSeries_differs _ (ne_of_gt (by linarith)) hs'

theorem flatExponential_not_analyticAt :
    Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic.notAnalyticAt := by
  intro h
  have hOn : AnalyticOnNhd ℝ flatExponential {0} := by
    intro c hc
    rcases Set.mem_singleton_iff.mp hc with rfl
    exact h
  obtain ⟨a, r, hr, _, hs⟩ :=
    ((real_analyticOn_iff flatExponential {0}).mpr hOn) 0 (by simp)
  apply flatExponential_noPowerSeriesNeighborhood
  refine ⟨a, r, hr, ?_⟩
  intro x hx
  change RealPowerSeriesHasSum a 0 x (flatExponential x)
  simpa only [zero_add] using hs x hx

/-- Each finite Taylor polynomial has a Peano remainder of the claimed order. -/
theorem flatExponential_taylor_finitePeano :
    Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic.finitePeano := by
  intro n
  change ScalarLittleO (𝓝 (0 : ℝ))
    (fun h => flatExponential h -
      ∑ k ∈ Finset.range (n + 1), flatExponentialTaylorCoefficient k * h ^ k)
    (fun h => h ^ n)
  have hl : ScalarLittleO (𝓝 (0 : ℝ)) flatExponential (fun h => |h| ^ n) :=
    flatExponential_littleO_everyPower n
  intro ε hε
  simpa [Real.norm_eq_abs, abs_pow] using hl ε hε

theorem flatExponential_smooth_not_analytic :
    Specs.SingleVariableAnalysis.Ch06.SmoothNotAnalytic.smoothNotAnalytic :=
  ⟨flatExponential_smooth, flatExponential_not_analyticAt⟩

end SingleVariableAnalysis
