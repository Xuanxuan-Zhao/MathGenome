import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DiscontinuousAlgebraicFunctional
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C03BoundedCriterion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Dual
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-! The algebraic-dual counterexample of paper.tex, lines 770–780.

An infinite Hamel basis supplies a countable independent family, which is
normalized to unit norm. Extend the normalized family to a new Hamel basis,
and use finite basis expansions to prescribe its scalar values. The resulting
map has arbitrarily large values at unit vectors; the boundedness criterion
therefore excludes continuity. All choices here are purely algebraic.
-/

namespace ExpandedFA.P1.DiscontinuousAlgebraicFunctional

open Module

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An infinite-dimensional normed space contains a countable independent
family of unit vectors. No ambient completeness is needed. -/
theorem exists_independent_unit_sequence (hE : ¬ FiniteDimensional 𝕜 E) :
    ∃ u : ℕ → E, LinearIndependent 𝕜 u ∧ ∀ n, ‖u n‖ = 1 := by
  classical
  let b := Basis.ofVectorSpace 𝕜 E
  let : Infinite (Basis.ofVectorSpaceIndex 𝕜 E) :=
    not_finite_iff_infinite.mp (fun h => hE (by
      let := h
      exact b.finiteDimensional_of_finite))
  let i := Infinite.natEmbedding (Basis.ofVectorSpaceIndex 𝕜 E)
  let v : ℕ → E := fun n => b (i n)
  have hv : LinearIndependent 𝕜 v := b.linearIndependent.comp i i.injective
  have hn (n : ℕ) : (‖v n‖ : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hv.ne_zero n))
  let w : ℕ → 𝕜ˣ := fun n => (Units.mk0 (‖v n‖ : 𝕜) (hn n))⁻¹
  refine ⟨w • v, hv.units_smul w, ?_⟩
  intro n
  change ‖(w n : 𝕜) • v n‖ = 1
  simpa [w] using norm_smul_inv_norm (𝕜 := 𝕜) (hv.ne_zero n)

/-- Prescribe arbitrary values on an independent sequence, and zero on the
remaining vectors of an explicitly provided extending Hamel basis. -/
theorem exists_basis_functional {u : ℕ → E} (hu : LinearIndependent 𝕜 u)
    (a : ℕ → 𝕜) :
    ∃ (B : Set E) (b : Basis B 𝕜 E) (f : C04Dual.AlgebraicDual 𝕜 E),
      (∀ x : B, b x = (x : E)) ∧
      Set.range u ⊆ B ∧
      (∀ n, f (u n) = a n) ∧
      (∀ x ∈ B, x ∉ Set.range u → f x = 0) := by
  classical
  let B := hu.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Basis B 𝕜 E := Basis.extend hu.linearIndepOn_id
  have hsub : Set.range u ⊆ B := hu.linearIndepOn_id.subset_extend _
  let values : E → 𝕜 := Function.extend u a (fun _ => 0)
  let f : E →ₗ[𝕜] 𝕜 := b.constr 𝕜 (fun x : B => values x)
  have hb (x : B) : b x = (x : E) := Basis.extend_apply_self _ x
  have hf (x : B) : f (x : E) = values x := by
    calc
      f (x : E) = f (b x) := congrArg f (hb x).symm
      _ = values x := b.constr_basis 𝕜 (fun y : B => values y) x
  refine ⟨B, b, f, hb, hsub, ?_, ?_⟩
  · intro n
    exact (hf ⟨u n, hsub (Set.mem_range_self n)⟩).trans
      (hu.injective.extend_apply a (fun _ => 0) n)
  · intro x hx hnot
    exact (hf ⟨x, hx⟩).trans (Function.extend_apply' a (fun _ => 0) x hnot)

/-- The full algebraic-dual example, including the Hamel basis and its unused
vectors' zero values, unboundedness on the unit sphere, and discontinuity. -/
theorem discontinuous_algebraic_functional : Spec.DiscontinuousAlgebraicFunctional := by
  intro 𝕜 E _ _ _ hE
  obtain ⟨u, hu, hunit⟩ := exists_independent_unit_sequence hE
  obtain ⟨B, b, f, hb, hsub, hf, hzero⟩ := exists_basis_functional hu
    (fun n => (n : 𝕜))
  have hlarge (C : ℝ) : ∃ n, C < ‖f (u n)‖ := by
    obtain ⟨n, hn⟩ := exists_nat_gt C
    refine ⟨n, ?_⟩
    rw [hf, RCLike.norm_natCast]
    exact hn
  have hunbounded : ¬ Bornology.IsBounded (f '' Metric.sphere (0 : E) 1) := by
    intro hbound
    obtain ⟨C, _, hC⟩ := hbound.exists_pos_norm_le
    obtain ⟨n, hn⟩ := hlarge C
    exact hn.not_ge (hC _ (Set.mem_image_of_mem f (by
      simpa only [Metric.mem_sphere, dist_zero_right] using hunit n)))
  have hdiscontinuous : ¬ Continuous f := by
    intro hc
    obtain ⟨C, _, hC⟩ := (C03BoundedCriterion.continuous_iff_norm_bound f).mp hc
    obtain ⟨n, hn⟩ := hlarge C
    exact hn.not_ge (by simpa only [hunit n, mul_one] using hC (u n))
  refine ⟨u, B, b, f, hu, hunit, hb, hsub, hf, hzero, hlarge,
    hunbounded, hdiscontinuous, ?_⟩
  rintro ⟨g, hg⟩
  apply hdiscontinuous
  rw [← hg]
  exact g.continuous

end ExpandedFA.P1.DiscontinuousAlgebraicFunctional
