import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch13.IsolatedZeros
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.IntervalImages
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch13.Identity

/-!
# The real-analytic identity principle on an interval

K03.13.identity, paper.tex:1442–1453. The upstream representation bridges
identify the manuscript's local ordinary power series with `AnalyticOnNhd ℝ`.
In particular a complex-valued function here still has a real argument.

The library identity theorem in `Mathlib.Analysis.Analytic.IsolatedZeros`
combines isolated zeros with analytic uniqueness on a preconnected set.
Its global step, in `Mathlib.Analysis.Analytic.Uniqueness`, proves that the
set of local zeros is open and relatively closed, as in the manuscript.
We supply preconnectedness using the upstream interval theorem and translate
the explicit accumulation hypothesis into closure of distinct agreement points.
-/
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology

namespace AnalyticIdentity

/-- Explicit accumulation supplies the library's punctured closure condition. -/
theorem agreement_mem_closure {F : Type*} (f g : ℝ → F) (E : Set ℝ) (c : ℝ)
    (heq : EqOn f g E)
    (hacc : ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < |x-c| ∧ |x-c| < ε) :
    c ∈ closure ({x | f x = g x} \ {c}) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨x, hx, hpos, hdist⟩ := hacc ε hε
  refine ⟨x, ⟨heq hx, ?_⟩, ?_⟩
  · simpa only [Set.mem_singleton_iff] using sub_ne_zero.mp (abs_pos.mp hpos)
  · simpa only [Real.dist_eq, abs_sub_comm] using hdist

theorem interval_preconnected (I : Set ℝ) (hI : RealInterval I) :
    IsPreconnected I :=
  (relativeConnected_iff_isPreconnected I).mp ((real_connected_iff_interval I).mpr hI)

end AnalyticIdentity

theorem real_analytic_identity_of_accumulation
    (f g : ℝ → ℝ) (I : Set ℝ) (_hIopen : IsOpen I) (hI : RealInterval I)
    (hf : RealAnalyticOn f I) (hg : RealAnalyticOn g I)
    (E : Set ℝ) (_hEI : E ⊆ I) (heq : EqOn f g E)
    (hacc : ∃ c ∈ I, ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < |x-c| ∧ |x-c| < ε) :
    EqOn f g I := by
  obtain ⟨c, hc, hacc⟩ := hacc
  exact ((real_analyticOn_iff f I).mp hf).eqOn_of_preconnected_of_mem_closure
    ((real_analyticOn_iff g I).mp hg) (AnalyticIdentity.interval_preconnected I hI) hc
    (AnalyticIdentity.agreement_mem_closure f g E c heq hacc)

theorem complex_real_analytic_identity_of_accumulation
    (f g : ℝ → ℂ) (I : Set ℝ) (_hIopen : IsOpen I) (hI : RealInterval I)
    (hf : ComplexRealAnalyticOn f I) (hg : ComplexRealAnalyticOn g I)
    (E : Set ℝ) (_hEI : E ⊆ I) (heq : EqOn f g E)
    (hacc : ∃ c ∈ I, ∀ ε : ℝ, 0 < ε → ∃ x ∈ E, 0 < |x-c| ∧ |x-c| < ε) :
    EqOn f g I := by
  obtain ⟨c, hc, hacc⟩ := hacc
  exact ((complex_real_analyticOn_iff f I).mp hf).eqOn_of_preconnected_of_mem_closure
    ((complex_real_analyticOn_iff g I).mp hg) (AnalyticIdentity.interval_preconnected I hI) hc
    (AnalyticIdentity.agreement_mem_closure f g E c heq hacc)

theorem real_analytic_identity_of_open_subinterval
    (f g : ℝ → ℝ) (I : Set ℝ) (_hIopen : IsOpen I) (hI : RealInterval I)
    (hf : RealAnalyticOn f I) (hg : RealAnalyticOn g I)
    (J : Set ℝ) (hJopen : IsOpen J) (_hJ : RealInterval J) (hne : J.Nonempty)
    (hJI : J ⊆ I) (heq : EqOn f g J) : EqOn f g I := by
  obtain ⟨c, hc⟩ := hne
  apply ((real_analyticOn_iff f I).mp hf).eqOn_of_preconnected_of_eventuallyEq
    ((real_analyticOn_iff g I).mp hg) (AnalyticIdentity.interval_preconnected I hI) (hJI hc)
  exact Filter.mem_of_superset (hJopen.mem_nhds hc) heq

theorem complex_real_analytic_identity_of_open_subinterval
    (f g : ℝ → ℂ) (I : Set ℝ) (_hIopen : IsOpen I) (hI : RealInterval I)
    (hf : ComplexRealAnalyticOn f I) (hg : ComplexRealAnalyticOn g I)
    (J : Set ℝ) (hJopen : IsOpen J) (_hJ : RealInterval J) (hne : J.Nonempty)
    (hJI : J ⊆ I) (heq : EqOn f g J) : EqOn f g I := by
  obtain ⟨c, hc⟩ := hne
  apply ((complex_real_analyticOn_iff f I).mp hf).eqOn_of_preconnected_of_eventuallyEq
    ((complex_real_analyticOn_iff g I).mp hg) (AnalyticIdentity.interval_preconnected I hI) (hJI hc)
  exact Filter.mem_of_superset (hJopen.mem_nhds hc) heq

end SingleVariableAnalysis
