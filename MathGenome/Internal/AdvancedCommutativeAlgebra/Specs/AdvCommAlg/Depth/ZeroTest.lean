import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic

/-! Independent statements for paper.tex:2636–2658 (DP-01).
`Submodule.torsionBySet R M I` is the annihilator submodule `0 :_M I`:
its elements are exactly those killed by every scalar in `I`. For the
maximal ideal this is the socle. Grade and depth use the upstream
regular-length definitions, including the `IM = M` convention. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth.Specs

def grade_zero_iff_exists_associatedPrimeType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I • (⊤ : Submodule R M) ≠ ⊤ →
      (gradeValue I M = 0 ↔ ∃ p ∈ associatedPrimes R M, I ≤ p)

def grade_zero_iff_annihilator_ne_botType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    I • (⊤ : Submodule R M) ≠ ⊤ →
      (gradeValue I M = 0 ↔ Submodule.torsionBySet R M (I : Set R) ≠ ⊥)

def depth_zero_iff_socle_ne_botType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    depthValue R M = 0 ↔
      Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R) ≠ ⊥

end AdvCommAlg.Depth.Specs
