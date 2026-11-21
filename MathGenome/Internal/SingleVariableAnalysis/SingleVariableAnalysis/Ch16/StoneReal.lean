import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.StoneReal
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
Real Stone–Weierstrass on compact real sets, K03.16.stone_real.
The proof reuses Mathlib's real Stone–Weierstrass theorem, whose proof uses
strong separation by affine interpolation and two finite compact subcovers
with lattice maxima/minima. Its hypotheses require only a real unital
subalgebra and point separation; no density hypothesis is assumed.
The last two statements expose the sup-norm and pointwise uniform errors.
-/
namespace SingleVariableAnalysis

open scoped Topology

/-- Translate explicit point separation to Mathlib's image-of-functions predicate. -/
theorem real_subalgebra_separatesPoints {K : Set ℝ} (A : Subalgebra ℝ C(K, ℝ))
    (hA : ∀ x y : K, x ≠ y → ∃ u ∈ A, u x ≠ u y) :
    A.SeparatesPoints := by
  intro x y hxy
  obtain ⟨u, hu, hune⟩ := hA x y hxy
  exact ⟨u, ⟨u, hu, rfl⟩, hune⟩

theorem real_stone_weierstrass_closure :
    Specs.SingleVariableAnalysis.Ch16.StoneReal.closureEqTop := by
  intro K _ A hA
  exact ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    A (real_subalgebra_separatesPoints A hA)

theorem real_stone_weierstrass_uniform_closure :
    Specs.SingleVariableAnalysis.Ch16.StoneReal.uniformClosureEqUniv := by
  intro K _ A hA
  rw [← A.topologicalClosure_coe, real_stone_weierstrass_closure K A hA]
  rfl

theorem real_stone_weierstrass_uniform_approximation :
    Specs.SingleVariableAnalysis.Ch16.StoneReal.uniformApproximation := by
  intro K _ A hA f ε hε
  have hf : f ∈ closure (A : Set C(K, ℝ)) := by
    rw [real_stone_weierstrass_uniform_closure K A hA]
    exact Set.mem_univ f
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hfg⟩

theorem real_stone_weierstrass_pointwise_approximation :
    Specs.SingleVariableAnalysis.Ch16.StoneReal.pointwiseApproximation := by
  intro K _ A hA f ε hε
  obtain ⟨g, hg, hfg⟩ := real_stone_weierstrass_uniform_approximation K A hA f ε hε
  refine ⟨g, hg, fun x => ?_⟩
  have hx := (f - g).norm_coe_le_norm x
  exact (show |f x - g x| ≤ ‖f - g‖ by
    simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using hx).trans_lt hfg

end SingleVariableAnalysis
