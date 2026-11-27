import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierConnecting
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Instances.ZMod

namespace Specs.GaloisFormalization.GH.RationalArtinSchreier

open GaloisFormalization.GH.Model (continuousCocycles continuousClass)
open ArtinSchreierCoefficients (Quotient primeFieldAction primeFieldInclusion quotientMap wp)
open ArtinSchreierConnecting (Characters PrimeCohomology charactersModule primeCohomologyModule)
open KrullLayers (AbsoluteGaloisGroup)

universe u v

/-- The indeterminate of the rational-function field over a finite field has
nonzero image in the quotient by the Artin–Schreier map. -/
def VariableClassNonzero : Prop :=
  ∀ (p : ℕ) (k₀ : Type u) [Field k₀] [Finite k₀] [Fact p.Prime] [CharP k₀ p],
    quotientMap p (RatFunc k₀) RatFunc.X ≠ 0

/-- Under the Artin–Schreier connecting isomorphism, the indeterminate defines
a nonzero class in continuous first cohomology with trivial coefficients. -/
def VariableCohomologyClassNonzero : Prop :=
  ∀ (p : ℕ) (k₀ : Type u) (S : Type v)
    [Field k₀] [Finite k₀] [Fact p.Prime] [CharP k₀ p]
    [Field S] [Algebra (RatFunc k₀) S] [IsSepClosure (RatFunc k₀) S],
    let k := RatFunc k₀
    let G := AbsoluteGaloisGroup k S
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : DistribMulAction G (ZMod p) := primeFieldAction G p
    letI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
    letI : Module (ZMod p) (PrimeCohomology p G) := primeCohomologyModule p G
    letI : Module (ZMod p) (Characters p G) := charactersModule p G
    ∃ (connect : Quotient p k ≃ₗ[ZMod p] PrimeCohomology p G)
      (toCharacter : PrimeCohomology p G ≃ₗ[ZMod p] Characters p G),
      (∀ (c : continuousCocycles G (ZMod p) 1) (g : G),
        (toCharacter.toFun (continuousClass G (ZMod p) 1 c)) (Additive.ofMul g) =
          c.val.val ![g]) ∧
      (∀ (a : k) (α : S), wp p S α = algebraMap k S a → ∀ g : G,
        primeFieldInclusion p S
          ((toCharacter.toFun (connect.toFun (quotientMap p k a))) (Additive.ofMul g)) =
            g • α - α) ∧
      connect.toFun (quotientMap p k RatFunc.X) ≠ 0

end Specs.GaloisFormalization.GH.RationalArtinSchreier
