import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Approximation.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
Stone--Weierstrass on compact Hausdorff spaces, including the empty space.
The real theorem is Mathlib's real Stone--Weierstrass theorem. In the complex
case the explicit conjugation hypothesis equips the given subalgebra with a
star-subalgebra structure having exactly the same carrier, so Mathlib's
complex theorem applies to the original algebra.
-/

namespace ExpandedFA.Approximation.StoneWeierstrass

universe u

theorem real_dense :
    Specs.ExpandedFA.Approximation.StoneWeierstrass.RealDensity.{u} := by
  intro K _ _ _ A hA
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  rw [dense_iff_closure_eq]
  exact congrArg (fun B : Subalgebra ℝ C(K, ℝ) => (B : Set C(K, ℝ))) h

theorem complex_dense :
    Specs.ExpandedFA.Approximation.StoneWeierstrass.ComplexDensity.{u} := by
  intro K _ _ _ A hA hconj
  let S : StarSubalgebra ℂ C(K, ℂ) :=
    { A with star_mem' := fun {f} hf => hconj f hf }
  have hS : S.SeparatesPoints := hA
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  rw [dense_iff_closure_eq]
  exact congrArg (fun B : StarSubalgebra ℂ C(K, ℂ) => (B : Set C(K, ℂ))) h

theorem real_uniform_approximation :
    Specs.ExpandedFA.Approximation.StoneWeierstrass.RealUniformApproximation.{u} := by
  intro K _ _ _ A hA f ε hε
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp (real_dense K A hA f) ε hε
  rw [dist_comm, dist_eq_norm] at hdist
  exact ⟨g, hg, hdist⟩

theorem complex_uniform_approximation :
    Specs.ExpandedFA.Approximation.StoneWeierstrass.ComplexUniformApproximation.{u} := by
  intro K _ _ _ A hA hconj f ε hε
  obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp (complex_dense K A hA hconj f) ε hε
  rw [dist_comm, dist_eq_norm] at hdist
  exact ⟨g, hg, hdist⟩

end ExpandedFA.Approximation.StoneWeierstrass
