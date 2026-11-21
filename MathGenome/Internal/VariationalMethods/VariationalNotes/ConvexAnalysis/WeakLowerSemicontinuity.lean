import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.WeakLowerSemicontinuity
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ExtendedFunctions
import Mathlib.Analysis.LocallyConvex.WeakSpace

noncomputable section
open Set
universe u
namespace VariationalNotes.ConvexAnalysis

/-- Norm and weak closures agree on convex sets; hence norm-closed
convex sets are weakly closed. -/
theorem normClosed_convex_isWeaklyClosed :
    Specs.normClosed_convex_isWeaklyClosed.{u} := by
  intro X _ _ C hclosed hconvex
  have h := hconvex.toWeakSpace_closure ℝ
  rw [hclosed.closure_eq] at h
  rw [h]
  exact isClosed_closure

/-- Epigraph convexity implies convexity of every real sublevel. -/
theorem IsConvex.convex_sublevel {X : Type u} [AddCommGroup X] [Module ℝ X]
    {f : X → WithTop ℝ} (hf : IsConvex f) (a : ℝ) :
    Convex ℝ (sublevel f a) := by
  intro x hx y hy b c hb hc hbc
  have h := hf (show (x, a) ∈ Specs.epigraph f from hx)
    (show (y, a) ∈ Specs.epigraph f from hy) hb hc hbc
  change f (b • x + c • y) ≤ ((b * a + c * a : ℝ) : WithTop ℝ) at h
  change f (b • x + c • y) ≤ (a : WithTop ℝ)
  simpa only [← add_mul, hbc, one_mul] using h

/-- Apply weak closedness to the closed convex real sublevels. -/
theorem convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous :
    Specs.convex_normLowerSemicontinuous_isWeaklyLowerSemicontinuous.{u} := by
  intro X _ _ f hconvex hlsc
  apply (lowerSemicontinuous_iff_closed_sublevels _).mpr
  intro a
  have hclosed := (lowerSemicontinuous_iff_closed_sublevels f).mp hlsc a
  have hweak := normClosed_convex_isWeaklyClosed (Specs.sublevel f a) hclosed
    (IsConvex.convex_sublevel hconvex a)
  have heq : Specs.sublevel
      (fun x : WeakSpace ℝ X => f ((toWeakSpace ℝ X).symm x)) a =
      (toWeakSpace ℝ X) '' (Specs.sublevel f a) := by
    ext x
    constructor
    · intro hx
      exact ⟨(toWeakSpace ℝ X).symm x, hx, (toWeakSpace ℝ X).apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [Specs.sublevel, Set.mem_ofPred_eq, LinearEquiv.symm_apply_apply] using hy
  rw [heq]
  exact hweak

end VariationalNotes.ConvexAnalysis
