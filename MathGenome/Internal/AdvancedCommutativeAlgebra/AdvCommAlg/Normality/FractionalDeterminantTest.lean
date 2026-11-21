import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.FractionalDeterminantTest
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
The determinant test for fractional multiplication (paper.tex, SN-05).
Mathlib's stable-submodule theorem applies to the fraction field acting on
itself: this action is torsion free, and the given submodule is nonzero and
finitely generated. Its proof uses integrality of endomorphisms of a finite
module, hence supplies the required monic equation.
-/

namespace AdvCommAlg.Normality

theorem fractional_determinant_test
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Submodule A K) (hL : L ≠ ⊥) (hLfg : L.FG)
    (u : K) (hu : ∀ v ∈ L, u * v ∈ L) : IsIntegral A u := by
  exact isIntegral_of_smul_mem_submodule L hL hLfg u hu

theorem fractional_determinant_test_monic
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Submodule A K) (hL : L ≠ ⊥) (hLfg : L.FG)
    (u : K) (hu : ∀ v ∈ L, u * v ∈ L) :
    ∃ p : Polynomial A, p.Monic ∧ p.eval₂ (algebraMap A K) u = 0 := by
  exact fractional_determinant_test A K L hL hLfg u hu

end AdvCommAlg.Normality
