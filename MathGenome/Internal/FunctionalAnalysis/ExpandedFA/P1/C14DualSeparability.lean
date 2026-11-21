import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14DualSeparability
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05Norming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
Lemma `fa2:p1:c14:dual-separability`, paper.tex:2800–2822.
A dense sequence of dual functionals supplies countably many detecting
vectors. Their closed linear span has trivial annihilator, hence is the
whole space by the accepted distance-separation theorem. The consequence
uses the continuous, surjective canonical map to the normed bidual.
-/

namespace ExpandedFA.P1.C14DualSeparability

open TopologicalSpace

universe u v

/-- A single vector detects the norm of a functional up to a factor of two
against every functional vanishing at that vector. No norm attainment is
required. -/
private theorem exists_norm_detecting_vector {𝕜 : Type u} {X : Type v}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (f : X →L[𝕜] 𝕜) :
    ∃ x : X, ∀ g : X →L[𝕜] 𝕜, g x = 0 → ‖f‖ ≤ 2 * ‖f - g‖ := by
  by_cases hf : f = 0
  · exact ⟨0, fun g _ => by simp [hf]⟩
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hnot : ¬ ∀ x : X, ‖f x‖ ≤ (‖f‖ / 2) * ‖x‖ := by
    intro h
    have := f.opNorm_le_bound (by positivity) h
    linarith
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hxpos : 0 < ‖x‖ := by
    by_contra h
    have hxzero : x = 0 := norm_eq_zero.mp (le_antisymm (not_lt.mp h) (norm_nonneg x))
    simp [hxzero] at hx
  refine ⟨x, fun g hg => ?_⟩
  have hbound := (f - g).le_opNorm x
  simp only [sub_apply, hg, sub_zero] at hbound
  nlinarith

/-- Closed subspaces with trivial continuous annihilator are the whole
space, using the accepted distance-separating functional theorem. -/
private theorem eq_top_of_trivial_annihilator {𝕜 : Type u} {X : Type v}
    [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 X) (hM : IsClosed (M : Set X))
    (h : ∀ f : X →L[𝕜] 𝕜, (∀ x ∈ M, f x = 0) → f = 0) : M = ⊤ := by
  apply top_unique
  intro x _
  by_contra hx
  have hxcl : x ∉ closure (M : Set X) := by simpa [hM.closure_eq] using hx
  obtain ⟨f, hf, hfn, _, _⟩ := C05Norming.distance_norming_functional 𝕜 X M x hxcl
  have hfzero : f = 0 := h f hf
  simpa [hfzero] using hfn

theorem space_separable_of_dual_separable :
    Spec.SpaceSeparableOfDualSeparable.{u, v} := by
  classical
  intro 𝕜 X _ _ _ hsep
  let := hsep
  obtain ⟨f, hf⟩ := exists_dense_seq (X →L[𝕜] 𝕜)
  choose x hx using fun n => exists_norm_detecting_vector (f n)
  let M := (Submodule.span 𝕜 (Set.range x)).topologicalClosure
  have hM : M = ⊤ := by
    apply eq_top_of_trivial_annihilator M (Submodule.isClosed_topologicalClosure _)
    intro g hg
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := hf.exists_dist_lt g (by positivity : 0 < ε / 3)
    have hgn : g (x n) = 0 := hg _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n)))
    have hfn := hx n g hgn
    have htri := norm_add_le (g - f n) (f n)
    rw [sub_add_cancel] at htri
    rw [dist_eq_norm] at hn
    rw [norm_sub_rev (f n) g] at hfn
    linarith
  have hsepM : IsSeparable (M : Set X) :=
    ((Set.countable_range x).isSeparable.span (R := 𝕜)).closure
  rw [hM, Submodule.top_coe] at hsepM
  exact isSeparable_univ_iff.mp hsepM

theorem dual_separable_of_separable_reflexive :
    Spec.DualSeparableOfSeparableReflexive.{u, v} := by
  intro 𝕜 X _ _ _ _ hsep href
  let := hsep
  have hsurj : Function.Surjective (C04CanonicalMap.canonicalEvaluation 𝕜 X) := href
  have hbidual : SeparableSpace ((X →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    hsurj.denseRange.separableSpace (C04CanonicalMap.canonicalEvaluation 𝕜 X).continuous
  exact space_separable_of_dual_separable 𝕜 (X →L[𝕜] 𝕜) hbidual

end ExpandedFA.P1.C14DualSeparability
