import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! Independent specification for the maximal Cohen–Macaulay assertion of
CM-12, paper.tex:3662–3664 and 3685–3696. Finiteness and nonzeroness are
hypotheses; there is no hypothesis on projective dimension or on dimension.
Since M is finite, `Module.Free R M` says precisely that M is finite free.
-/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def maximalCohenMacaulay_iff_freeType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M],
    MaximalCohenMacaulayValue R M ↔ Module.Free R M

end AdvCommAlg.CohenMacaulay.Specs
