import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.FinitePSimpleDensity
import MathGenome.Internal.RealAnalysis.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
Simple functions with finite-measure nonzero support are dense for every
finite exponent 1 ≤ p, on an arbitrary positive measure space.

Mathlib's simple approximation uses dominated convergence on the p-th power
of the error. It gives a simple approximant still in MemLp. For a nonzero
finite exponent, every nonzero level of such a simple function has finite
measure, so their finite union, its support, has finite measure. No global
sigma-finiteness is used. The upstream integral-norm and quotient bridges
then give the original source formulations.
-/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace D11.Ch11.FinitePSimpleDensity

/-- The original integral-norm statement for measurable representatives. -/
theorem raw_simple_density : Specs.D11.Ch11.FinitePSimpleDensity.raw_simple_density := by
  intro X 𝕜 _ _ _ _ μ p hp f hf ε hε
  have hf' := (D11.Ch10.LpDefinition.rawLp_iff_memLp μ p f hp).mp hf
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one hp)
  obtain ⟨s, hdist, hs⟩ := hf'.2.exists_simpleFunc_eLpNorm_sub_lt
    ENNReal.ofReal_ne_top (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨s, (D11.Ch10.LpDefinition.rawLp_iff_memLp μ p s hp).mpr
    ⟨s.measurable, hs⟩, s.measurableSet_support,
    s.measure_support_lt_top_of_memLp hs hp0 ENNReal.ofReal_ne_top, ?_⟩
  rw [D11.Ch10.LpDefinition.powerNorm_eq_eLpNorm μ p (f - (s : X → 𝕜)) hp
    (hf'.1.sub s.measurable)]
  exact hdist

/-- The norm formulation on the ordinary a.e. quotient provided by Mathlib. -/
theorem native_simple_density : Specs.D11.Ch11.FinitePSimpleDensity.native_simple_density := by
  intro X 𝕜 _ _ _ _ μ p hp hpt f ε hε
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp.out)
  obtain ⟨s, hdist, hs⟩ := (Lp.memLp f).exists_simpleFunc_eLpNorm_sub_lt hpt
    (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨s, hs, s.measurableSet_support,
    s.measure_support_lt_top_of_memLp hs hp0 hpt, ?_⟩
  rw [← Lp.toLp_coeFn f (Lp.memLp f), ← MemLp.toLp_sub, Lp.norm_toLp]
  exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hdist) ENNReal.ofReal_ne_top).mpr hdist |>.trans_eq
    (ENNReal.toReal_ofReal hε.le)

/-- Density on the project's literal quotient, with the canonical upstream
normed structures and the representative-compatible linear isometry. -/
theorem finite_p_simple_density : Specs.D11.Ch11.FinitePSimpleDensity.finite_p_simple_density := by
  intro X 𝕜 _ _ _ _ μ p hp hpt
  refine ⟨D11.Ch10.QuotientConstruction.quotientNormedAddCommGroup μ p,
    D11.Ch10.QuotientConstruction.quotientNormedSpace μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p,
    D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf μ p, ?_⟩
  intro f ε hε
  obtain ⟨s, hs, hmeas, hfin, hdist⟩ := native_simple_density μ p hpt
    (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p f) ε hε
  refine ⟨s, hs, hmeas, hfin, ?_⟩
  rw [← (D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv μ p).norm_map,
    map_sub, D11.Ch10.QuotientConstruction.nativeLinearIsometryEquiv_classOf]
  exact hdist

end D11.Ch11.FinitePSimpleDensity
