import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch16.Weierstrass
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch16.Lattice
import Mathlib.Algebra.Order.Module.Basic

/-! K03.16.lattice: the uniform algebra closure and its lattice operations.
Absolute values are constructed from the upstream Bernstein/affine Weierstrass
approximation on [-M,M], followed by polynomial substitution. No separation
hypothesis or Stone–Weierstrass density theorem is used. -/
noncomputable section
open scoped Topology
namespace SingleVariableAnalysis

/-- Polynomial substitution stays inside any real unital subalgebra. -/
theorem polynomial_substitution_mem {K : Set ℝ} (A : Subalgebra ℝ C(K, ℝ))
    (f : C(K, ℝ)) (hf : f ∈ A) (p : Polynomial ℝ) :
    Polynomial.aeval f p ∈ A := by
  rw [← Polynomial.aeval_subalgebra_coe p A ⟨f, hf⟩]
  exact (Polynomial.aeval (⟨f, hf⟩ : A) p).property

theorem real_uniformClosure_algebra :
    Specs.SingleVariableAnalysis.Ch16.Lattice.closureAlgebra := by
  intro K _ A
  exact ⟨A.topologicalClosure, A.topologicalClosure_coe⟩

theorem real_uniformClosure_abs_polynomial_approximation :
    Specs.SingleVariableAnalysis.Ch16.Lattice.absPolynomialApproximation := by
  intro K _ A f hf M hM ε hε
  have hM0 : 0 ≤ M := (norm_nonneg f).trans hM
  by_cases hzero : M = 0
  · subst M
    have hfzero : f = 0 := norm_eq_zero.mp (le_antisymm hM (norm_nonneg f))
    refine ⟨0, ?_, ?_, ?_⟩
    · apply (ContinuousMap.norm_lt_iff _ hε).mpr
      intro t
      have ht : (t : ℝ) = 0 := le_antisymm t.property.2 (by simpa using t.property.1)
      simp [ht, hε]
    · simpa only [map_zero] using
        (show (0 : C(K, ℝ)) ∈ closure (A : Set C(K, ℝ)) from A.topologicalClosure.zero_mem)
    · simp [hfzero, hε]
  · let u : C(Set.Icc (-M) M, ℝ) :=
      ⟨fun t => |(t : ℝ)|, continuous_subtype_val.abs⟩
    obtain ⟨p, hp⟩ := real_weierstrass_approximation (-M) M (by linarith) u ε hε
    refine ⟨p, hp, polynomial_substitution_mem A.topologicalClosure f hf p, ?_⟩
    apply (ContinuousMap.norm_lt_iff _ hε).mpr
    intro x
    have hxn : |f x| ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    have hx : |f x| ≤ M := hxn.trans hM
    let t : Set.Icc (-M) M := ⟨f x, abs_le.mp hx⟩
    have ht := (ContinuousMap.norm_lt_iff _ hε).mp hp t
    change ‖|f x| - p.eval (f x)‖ < ε at ht
    simpa only [ContinuousMap.sub_apply, Polynomial.aeval_continuousMap_apply,
      ContinuousMap.abs_apply, norm_sub_rev] using ht

theorem real_uniformClosure_abs :
    Specs.SingleVariableAnalysis.Ch16.Lattice.closureAbs := by
  intro K _ A f hf
  have h : |f| ∈ closure (closure (A : Set C(K, ℝ))) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨p, _, hp, he⟩ := real_uniformClosure_abs_polynomial_approximation
      K A f hf ‖f‖ le_rfl ε hε
    exact ⟨Polynomial.aeval f p, hp, by simpa only [dist_eq_norm, norm_sub_rev] using he⟩
  simpa only [closure_closure] using h

theorem real_uniformClosure_max_min :
    Specs.SingleVariableAnalysis.Ch16.Lattice.closureMaxMin := by
  intro K _ A f g hf hg
  have habs := real_uniformClosure_abs K A (g - f) (A.topologicalClosure.sub_mem hg hf)
  constructor
  · rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
    exact A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem (A.topologicalClosure.add_mem hf hg) habs) _
  · rw [inf_eq_half_smul_add_sub_abs_sub' ℝ]
    exact A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem (A.topologicalClosure.add_mem hf hg) habs) _

theorem real_uniformClosure_finite_max_min :
    Specs.SingleVariableAnalysis.Ch16.Lattice.closureFiniteMaxMin := by
  intro K _ A ι s hs f hf
  constructor
  · exact Finset.sup'_mem _ (fun u hu v hv => (real_uniformClosure_max_min K A u v hu hv).1)
      s hs f hf
  · exact Finset.inf'_mem _ (fun u hu v hv => (real_uniformClosure_max_min K A u v hu hv).2)
      s hs f hf

end SingleVariableAnalysis
