import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Noetherian.Defs

/-! Independent statement of the finite-module stage of GC-02, paper.tex:4410–4452.
The coefficient module may be zero; the ring is nonzero, Noetherian and local.
`R ⧸ maximalIdeal R` is the residue field. `Shrink` places it in the module
category universe; `[Small R]` is only the corresponding universe condition.
`Subsingleton (Ext ...)` expresses vanishing of the additive Ext group.
-/
universe u v
open CategoryTheory CategoryTheory.Abelian
namespace AdvCommAlg.Gorenstein.FiniteExtDetection.Specs

def finite_ext_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    [Small.{v} R] (N : ModuleCat.{v} R) [Module.Finite R N] (n : ℕ),
    (∀ i : ℕ, n < i →
      Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ IsLocalRing.maximalIdeal R))) N i)) →
    ∀ (M : ModuleCat.{v} R) [Module.Finite R M] (i : ℕ), n < i →
      Subsingleton (Ext M N i)

end AdvCommAlg.Gorenstein.FiniteExtDetection.Specs
