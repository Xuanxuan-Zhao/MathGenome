import MathGenome.Internal.FourierSobolev.Specs.P102.Approximation.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! Stone–Weierstrass for compact Hausdorff spaces, including the empty space. -/

namespace P102.Approximation

/-- Closure equal to the whole normed space is equivalent to approximation
with every positive uniform error. Applied below to the uniform norm on `C(K, 𝕜)`. -/
theorem closure_eq_univ_iff_norm_approximation
    {E : Type*} [NormedAddCommGroup E] (s : Set E) :
    closure s = Set.univ ↔
      ∀ (f : E) (ε : ℝ), 0 < ε → ∃ a ∈ s, ‖f - a‖ < ε := by
  constructor
  · intro h f ε hε
    have hf : f ∈ closure s := h.symm ▸ Set.mem_univ f
    simpa only [dist_eq_norm] using Metric.mem_closure_iff.mp hf ε hε
  · intro h
    apply Set.eq_univ_of_forall
    intro f
    apply Metric.mem_closure_iff.mpr
    simpa only [dist_eq_norm] using h f

/-- The real form of Theorem 1.11. Constants are part of the subalgebra structure. -/
theorem real_stone_weierstrass : Specs.P102.Approximation.RealStoneWeierstrass := by
  intro K _ _ _ A hsep
  have h : closure (A : Set C(K, ℝ)) = Set.univ := by
    have hA := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
    exact congrArg (fun B : Subalgebra ℝ C(K, ℝ) => (B : Set C(K, ℝ))) hA
  exact ⟨h, (closure_eq_univ_iff_norm_approximation _).mp h⟩

/-- The complex form of Theorem 1.11, with explicit conjugation closure. -/
theorem complex_stone_weierstrass : Specs.P102.Approximation.ComplexStoneWeierstrass := by
  intro K _ _ _ A hsep hconj
  let S : StarSubalgebra ℂ C(K, ℂ) :=
    { A with star_mem' := fun hf => hconj _ hf }
  have hS := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  have h : closure (A : Set C(K, ℂ)) = Set.univ :=
    congrArg (fun B : StarSubalgebra ℂ C(K, ℂ) => (B : Set C(K, ℂ))) hS
  exact ⟨h, (closure_eq_univ_iff_norm_approximation _).mp h⟩

end P102.Approximation
