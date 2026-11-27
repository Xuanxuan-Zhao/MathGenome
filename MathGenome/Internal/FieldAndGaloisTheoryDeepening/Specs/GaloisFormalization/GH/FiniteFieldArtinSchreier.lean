import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierConnecting
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.FiniteFrobenius
import Mathlib.FieldTheory.Finite.Trace

namespace Specs.GaloisFormalization.GH.FiniteFieldArtinSchreier

open ArtinSchreierCoefficients (Quotient primeFieldAction primeFieldInclusion quotientMap wp)
open ArtinSchreierConnecting (Characters PrimeCohomology charactersModule primeCohomologyModule)
open FiniteFrobenius (arithmeticFrobenius)
open KrullLayers (AbsoluteGaloisGroup)
open GaloisFormalization.GH.Model (continuousCocycles continuousClass)

universe u v

noncomputable section

attribute [local instance] ZMod.algebra

/-- The trace identifies the Artin–Schreier quotient with the additive prime field. -/
def TraceQuotient : Prop :=
  ∀ (p : ℕ) (k : Type u) [Field k] [Finite k] [Fact p.Prime] [CharP k p],
    ∃ e : ArtinSchreierCoefficients.Quotient p k ≃ₗ[ZMod p] ZMod p,
      ∀ a : k, e (quotientMap p k a) = Algebra.trace (ZMod p) k a

/-- For a field of cardinality (p^r), the absolute trace sums the first (r)
prime-field Frobenius conjugates. -/
def TraceFormula : Prop :=
  ∀ (p : ℕ) (k : Type u) [Field k] [Fintype k] [Fact p.Prime] [CharP k p],
    let r := Module.finrank (ZMod p) k
    Fintype.card k = p ^ r ∧
      ∀ a : k, algebraMap (ZMod p) k (Algebra.trace (ZMod p) k a) =
        ∑ i ∈ Finset.range r, a ^ (p ^ i)

/-- The Artin–Schreier connecting isomorphism of GH09 evaluates on arithmetic
Frobenius as the trace. The two formulas from GH09 specify the character being evaluated. -/
def CharacterAtFrobenius : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Fintype k] [Field S] [Algebra k S]
    [Fact p.Prime] [CharP k p] [IsSepClosure k S]
    [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)],
    let G := AbsoluteGaloisGroup k S
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : DistribMulAction G (ZMod p) := primeFieldAction G p
    letI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
    letI : Module (ZMod p) (PrimeCohomology p G) := primeCohomologyModule p G
    letI : Module (ZMod p) (Characters p G) := charactersModule p G
    ∃ (connect : ArtinSchreierCoefficients.Quotient p k ≃ₗ[ZMod p] PrimeCohomology p G)
      (toCharacter : PrimeCohomology p G ≃ₗ[ZMod p] Characters p G),
      (∀ (c : continuousCocycles G (ZMod p) 1) (g : G),
        (toCharacter.toFun (continuousClass G (ZMod p) 1 c)) (Additive.ofMul g) = c.val.val ![g]) ∧
      (∀ (a : k) (α : S), wp p S α = algebraMap k S a → ∀ g : G,
        primeFieldInclusion p S
          ((toCharacter.toFun (connect.toFun (quotientMap p k a))) (Additive.ofMul g)) =
            g • α - α) ∧
      ∀ a : k, (toCharacter.toFun (connect.toFun (quotientMap p k a)))
        (Additive.ofMul (arithmeticFrobenius k S)) = Algebra.trace (ZMod p) k a

end

end Specs.GaloisFormalization.GH.FiniteFieldArtinSchreier
