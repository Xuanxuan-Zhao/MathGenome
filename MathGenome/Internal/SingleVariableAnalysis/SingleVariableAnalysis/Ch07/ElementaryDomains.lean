import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.TrigInverses
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.ElementaryDomains

/-!
Real domains and exceptional points (K03.07.elementary_domains).
The domain interfaces restrict the shared constructions. Sine solutions use
their proved periods and principal inverse; distinctness uses the strict
interior arcsine range. The square-root derivative comes from Mathlib's inverse
rule for squaring on (0,∞). At zero we instead rationalize the right quotient,
and combine continuity and strict positivity of sqrt with the reciprocal limit.
-/
noncomputable section
namespace SingleVariableAnalysis.ElementaryDomains
open Set Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch07
open Specs.SingleVariableAnalysis.Ch07.SinCos
open Specs.SingleVariableAnalysis.Ch07.PiPeriod
open Specs.SingleVariableAnalysis.Ch07.TrigInverses
open Specs.SingleVariableAnalysis.Ch07.ElementaryDomains

def logarithm : realPartialType := logarithmValue
def positivePower : positivePowerType := positivePowerValue
def squareRoot : realPartialType := squareRootValue
def arcsine : realPartialType := arcsineValue
def arccosine : realPartialType := arccosineValue
def cosineDenominatorDomain : realDomainType := cosineDenominatorDomainValue
def sineDenominatorDomain : realDomainType := sineDenominatorDomainValue

theorem exact_domains : exactDomains := by
  simp [exactDomains, logarithmValue, positivePowerValue, squareRootValue,
    arcsineValue, arccosineValue]

theorem squareRoot_branch : squareRootBranch := by
  intro x hx
  refine ⟨?_, Real.sqrt_nonneg x, Real.sq_sqrt hx, ?_⟩
  · change squareRootValue x = some (nonnegativeRoot 2 x)
    rw [squareRootValue, ite_eq_left hx, nonnegativeRoot_sqrt x hx]
  · intro y hy hpow
    exact (nonnegativeRoot_unique 2 (by decide) x hx y hy hpow).trans
      (nonnegativeRoot_sqrt x hx)

theorem principal_ranges : principalRanges := by
  refine ⟨?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact TrigInverses.arcsin_inverse.1 hx
    · intro hy
      exact ⟨realSeriesSinValue y, TrigInverses.sine_branch.2.mapsTo hy,
        TrigInverses.arcsin_inverse.2.2 y hy⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact TrigInverses.arccos_inverse.1 hx
    · intro hy
      exact ⟨realSeriesCosValue y, TrigInverses.cosine_branch.2.mapsTo hy,
        TrigInverses.arccos_inverse.2.2 y hy⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact TrigInverses.arctan_inverse.1 x
    · intro hy
      exact ⟨realSeriesSinValue y / realSeriesCosValue y,
        TrigInverses.arctan_inverse.2.2 y hy⟩

theorem reciprocal_domains : reciprocalDomains := by
  have hc : Specs.SingleVariableAnalysis.Ch07.PiPeriod.cosineZeros :=
    PiPeriod.piPeriod_cosine_zeros
  have hs : Specs.SingleVariableAnalysis.Ch07.PiPeriod.sineZeros :=
    PiPeriod.piPeriod_sine_zeros
  have hhalf : firstPositiveCosineZeroValue = analyticPiValue / 2 := by
    unfold analyticPiValue
    ring
  constructor
  · intro x
    change (¬ realSeriesCosValue x = 0) ↔ _
    simpa only [hhalf] using (not_congr (hc x))
  · intro x
    exact not_congr (hs x)

private theorem sine_eq : realSeriesSinValue = Real.sin :=
  funext fun x => (sinCosSeries_eq_real x).1

private theorem pi_eq : analyticPiValue = Real.pi := PiPeriod.analyticPi_eq_pi

theorem sine_translated_solutions : sineTranslatedSolutions := by
  intro x hx k
  have hp : Specs.SingleVariableAnalysis.Ch07.PiPeriod.integerPeriods :=
    PiPeriod.piPeriod_integer_periods
  have hx' : x ∈ Icc (-1 : ℝ) 1 := by
    obtain ⟨hl, hr⟩ := abs_lt.mp hx
    exact ⟨hl.le, hr.le⟩
  have ha := TrigInverses.arcsin_inverse.2.1 x hx'
  rw [(hp k _).1, (hp k _).1]
  refine ⟨ha, ?_⟩
  rw [sine_eq, pi_eq, Real.sin_pi_sub]
  simpa only [sine_eq] using ha

theorem sine_principal_unique : sinePrincipalUnique :=
  TrigInverses.branch_unique_solutions.1

theorem sine_distinct_solutions : sineDistinctSolutions := by
  intro x hx
  have hlt : principalArcsinValue x < analyticPiValue / 2 := by
    rw [pi_eq]
    exact Real.arcsin_lt_pi_div_two.mpr (abs_lt.mp hx).2
  have hne : principalArcsinValue x ≠ analyticPiValue - principalArcsinValue x := by
    intro heq
    linarith
  refine ⟨hne, ?_⟩
  have hs := sine_translated_solutions x hx 0
  simp only [Int.cast_zero, zero_mul, add_zero] at hs
  rintro ⟨y, _, hu⟩
  exact hne ((hu _ hs.1).trans (hu _ hs.2).symm)

theorem squareRoot_derivative : squareRootDerivative := by
  intro x hx
  exact Real.hasDerivAt_sqrt (ne_of_gt hx)

theorem squareRoot_right_quotient : squareRootRightQuotient := by
  intro h hh
  simp only [zero_add, Real.sqrt_zero, sub_zero]
  apply (div_eq_div_iff (ne_of_gt hh) (ne_of_gt (Real.sqrt_pos.mpr hh))).mpr
  simpa only [one_mul, ← pow_two] using Real.sq_sqrt hh.le

theorem squareRoot_right_infinite : squareRootRightInfinite := by
  have hs : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact Real.sqrt_pos.mpr hh
  apply hs.inv_tendsto_nhdsGT_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change (Real.sqrt h)⁻¹ = _
  simpa only [one_div] using (squareRoot_right_quotient h hh).symm

end SingleVariableAnalysis.ElementaryDomains
