import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.ValueSensitivity
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch04.PerturbationAlgebra
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
universe u v
namespace VariationalNotes.Ch04
open VariationalNotes.ConvexAnalysis

/-- Weak duality turns an objective value p into a dual maximum; the accepted
attainment equivalence then gives precisely the global supporting inequality. -/
theorem value_sensitivity_bound : Specs.value_sensitivity_bound.{u,v} := by
  intro X Y _ _ _ _ _ _ Φ p hbot hp y hy
  have hd : Specs.perturbationDualValue Φ = (p : EReal) := by
    apply le_antisymm (perturbation_dual_bound Φ p hp).2.2.1
    exact hy ▸ le_iSup (Specs.perturbationDualObjective Φ) y
  exact (perturbation_attainment Φ p hbot hp y).2.mp
    ((perturbation_attainment Φ p hbot hp y).1.mp ⟨hy, hd⟩)

/-- On each ray, the derivative at its origin lies below the unit secant. -/
theorem convex_derivative_support {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Y → ℝ) (D : Y →L[ℝ] ℝ) (hc : ConvexOn ℝ Set.univ f)
    (hD : HasFDerivAt f D 0) (u : Y) : f 0 + D u ≤ f u := by
  have hray : ConvexOn ℝ Set.univ (fun t : ℝ => f (t • u)) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    simpa only [smul_eq_mul, add_smul, mul_smul] using
      hc.2 (Set.mem_univ (a • u)) (Set.mem_univ (b • u)) hs ht hst
  have hder : HasDerivAt (fun t : ℝ => f (t • u)) (D u) 0 := by
    simpa only [Function.comp_def, id_eq, zero_smul, one_smul] using
      hD.comp_hasDerivAt_of_eq 0 ((hasDerivAt_id (0 : ℝ)).smul_const u) (zero_smul ℝ u).symm
  have h := hray.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hder
  simp only [slope_def_field, zero_smul, one_smul, sub_zero, div_one] at h
  linarith

theorem finite_convex_subdifferential : Specs.finite_convex_subdifferential.{v} := by
  intro Y _ _ f D hc hD
  have hs := convex_derivative_support f D hc hD
  refine ⟨?_, hs⟩
  apply Set.ext
  intro y
  rw [Set.mem_singleton_iff]
  change y ∈ subdifferential (fun u => (f u : WithTop ℝ)) 0 ↔ y = D
  rw [mem_subdifferential_iff (f := fun u => (f u : WithTop ℝ)) (x := (0 : Y)) rfl]
  simp only [sub_zero, WithTop.coe_le_coe]
  constructor
  · intro hy
    have hmin : IsLocalMin (fun u => f u - y u) 0 := by
      apply Filter.Eventually.of_forall
      intro u
      change f 0 - y 0 ≤ f u - y u
      simp only [map_zero, sub_zero]
      linarith [hy u]
    have heq : D - y = 0 := hmin.hasFDerivAt_eq_zero (hD.sub y.hasFDerivAt)
    exact (sub_eq_zero.mp heq).symm
  · rintro rfl
    exact hs

theorem value_sensitivity_differentiable : Specs.value_sensitivity_differentiable.{u,v} := by
  intro X Y _ _ _ _ _ Φ hΦ f hf D hD
  have hbot : ∀ u, Specs.marginal Φ u ≠ ⊥ := by
    intro u
    rw [hf u]
    exact EReal.coe_ne_bot _
  have hrep : Specs.marginalFunction Φ = fun u => (f u : WithTop ℝ) := by
    funext u
    change (Specs.marginal Φ u).unbotD ⊤ = _
    rw [hf u]
    rfl
  have hc : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ s t hs ht hst
    have h := marginal_convex_finite Φ hΦ a b (f a) (f b) (hf a) (hf b) s t hs ht hst
    rw [hf] at h
    exact EReal.coe_le_coe_iff.mp h
  have hsingle : subdifferential (fun u => (f u : WithTop ℝ)) 0 = {D} :=
    (finite_convex_subdifferential f D hc hD).1
  have hmem : D ∈ ConvexAnalysis.Specs.subdifferential (Specs.marginalFunction Φ) 0 := by
    rw [hrep]
    change D ∈ subdifferential (fun u => (f u : WithTop ℝ)) 0
    rw [hsingle]
    exact Set.mem_singleton D
  have hatt := (perturbation_attainment Φ (f 0) hbot (hf 0) D).1.mpr hmem
  refine ⟨?_, ?_, hatt.1, hatt.2, ?_⟩
  · rw [hrep]
    exact hsingle
  · exact (perturbation_attainment Φ (f 0) hbot (hf 0) D).2.mp hmem
  · intro y
    constructor
    · intro hy
      have hymem := (perturbation_attainment Φ (f 0) hbot (hf 0) y).1.mp ⟨hy, hatt.2⟩
      rw [hrep] at hymem
      change y ∈ subdifferential (fun u => (f u : WithTop ℝ)) 0 at hymem
      rw [hsingle] at hymem
      exact Set.mem_singleton_iff.mp hymem
    · rintro rfl
      exact hatt.1

end VariationalNotes.Ch04
