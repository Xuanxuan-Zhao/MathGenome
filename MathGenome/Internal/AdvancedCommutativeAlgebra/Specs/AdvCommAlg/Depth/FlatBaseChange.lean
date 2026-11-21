import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Independent specifications for the flat assertions of DP-08,
`paper.tex:2886–2893,2900–2906`. The extended ideal is `Ideal.map`,
and the tensor product carries its canonical left `S`-module structure.
No nonzero, local, or proper-ideal hypotheses are imposed. -/

universe u
open scoped TensorProduct
namespace AdvCommAlg.Depth.Specs

def grade_le_flatBaseChangeType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    gradeValue I M ≤ gradeValue (I.map (algebraMap R S)) (S ⊗[R] M)

def grade_eq_faithfullyFlatBaseChangeType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.FaithfullyFlat R S]
    (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
    gradeValue I M = gradeValue (I.map (algebraMap R S)) (S ⊗[R] M)

end AdvCommAlg.Depth.Specs
