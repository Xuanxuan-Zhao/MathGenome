import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Definitions
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.KrullDimension.Basic

/-! The sharp localization inequality in DP-10, paper.tex:2983–2988,
3007–3017. Depth uses the source's regular-length definition. The
localization is the actual prime localization of the module; no support
hypothesis is imposed. Krull dimension has its canonical `WithBot ℕ∞`
value, so the depths are coerced to that same type. -/

universe u v
namespace AdvCommAlg.Depth.Specs

def depth_le_localized_depth_add_dimType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (p : Ideal R) [p.IsPrime],
    (depthValue R M : WithBot ℕ∞) ≤
      (depthValue (Localization.AtPrime p) (LocalizedModule.AtPrime p M) : WithBot ℕ∞) +
        ringKrullDim (R ⧸ p)

end AdvCommAlg.Depth.Specs
