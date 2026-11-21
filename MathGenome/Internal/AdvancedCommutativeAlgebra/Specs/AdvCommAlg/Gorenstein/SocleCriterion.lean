import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Artinian.Defs

/-! GC-05, second assertion (paper.tex:4518–4556).
The socle carries the canonical action of R/m defined in DP-05; no
coefficient field in R is chosen. Self-injectivity means injectivity of
the regular R-module. Artinianity is the only finiteness hypothesis. -/
universe u
namespace AdvCommAlg.Gorenstein.SocleCriterionSpec

noncomputable def selfInjective_iff_socle_finrank_one : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R],
    Module.Injective R R ↔
      Module.finrank (IsLocalRing.ResidueField R) (Specs.socleValue R R) = 1

end AdvCommAlg.Gorenstein.SocleCriterionSpec
