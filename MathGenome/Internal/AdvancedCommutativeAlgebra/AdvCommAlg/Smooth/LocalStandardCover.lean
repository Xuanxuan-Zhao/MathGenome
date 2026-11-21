import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.LocalStandardCover
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! Local standard presentations and a finite principal cover (SM-05).
SM-03 identifies the canonical standard smoothness predicate used here
with the source's finite Jacobian presentations. -/

namespace AdvCommAlg.Smooth

universe u v

/-- Standard smoothness near every prime, over an arbitrary commutative base. -/
theorem exists_notMem_standardSmooth :
    Specs.AdvCommAlg.Smooth.LocalStandardCover.localStandard.{u,v} := by
  intro A B _ _ _ hs q _
  letI : Algebra.Smooth A B := hs
  exact Algebra.IsSmoothAt.exists_notMem_isStandardSmooth A q

/-- Finitely many principal standard smooth neighbourhoods generate the
unit ideal; for the zero ring we explicitly choose the empty family. -/
theorem exists_finite_standardSmooth_cover :
    Specs.AdvCommAlg.Smooth.LocalStandardCover.finiteStandardCover.{u,v} := by
  intro A B _ _ _ hs
  classical
  by_cases hB : Subsingleton B
  · letI := hB
    refine ⟨∅, ?_, by simp⟩
    simp [Subsingleton.elim (⊥ : Ideal B) ⊤]
  · letI : Algebra.Smooth A B := hs
    obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth A B
    obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
    exact ⟨t, ht, fun g hg => hstd g (hts hg)⟩

end AdvCommAlg.Smooth
