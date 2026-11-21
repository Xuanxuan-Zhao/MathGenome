import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions

/-! The Ext vanishing assertion of GC-11, paper.tex:4742–4774.
The canonical module is arbitrary, and the maximal Cohen–Macaulay predicate
includes the zero module. Vanishing means that the actual categorical Ext
abelian group is a subsingleton. -/

universe u
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Gorenstein.Specs

def maximalCohenMacaulay_ext_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    IsCanonicalModuleValue R W →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      CohenMacaulay.Specs.MaximalCohenMacaulayValue R M →
      ∀ i : ℕ, 0 < i → Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R W) i)

end AdvCommAlg.Gorenstein.Specs
