import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.KrullDimension.Module

/-! Independent statements for paper.tex:2660–2688, DP-02.
Dimensions use the canonical support dimension in `WithBot ℕ∞`.  Nonzero
finite modules are explicit in the local statements; no global finite
Krull-dimension assumption is imposed on a Noetherian ring. -/

universe u v
open scoped Pointwise
namespace AdvCommAlg.Depth.Specs

def supportDim_quotSMulTop_add_oneType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ IsLocalRing.maximalIdeal R →
    Function.Injective (fun m : M => x • m) →
    Module.supportDim R (QuotSMulTop x M) + 1 = Module.supportDim R M

def regular_length_le_supportDimType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : List R), RingTheory.Sequence.IsRegular M x →
    (x.length : WithBot ℕ∞) ≤ Module.supportDim R M

def depth_le_supportDimType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M],
    (depthValue R M : WithBot ℕ∞) ≤ Module.supportDim R M

def regular_lengths_boundedType : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R), I • (⊤ : Submodule R M) ≠ ⊤ →
    ∃ n : ℕ, ∀ x : List R, RingTheory.Sequence.IsRegular M x →
      (∀ a ∈ x, a ∈ I) → x.length ≤ n

end AdvCommAlg.Depth.Specs
