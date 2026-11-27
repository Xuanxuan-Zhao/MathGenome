import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierCoefficients
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.Cochains
import Mathlib.Algebra.Module.ZMod
import Mathlib.Topology.Algebra.ContinuousMonoidHom

namespace Specs.GaloisFormalization.GH.ArtinSchreierConnecting

open GaloisFormalization.GH.Model
open ArtinSchreierCoefficients (primeFieldAction primeFieldInclusion wp quotientMap)
open KrullLayers (AbsoluteGaloisGroup)

universe u v

noncomputable section

private theorem nsmul_primeField (p : ℕ) (x : ZMod p) : p • x = 0 := by
  rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]

section PrimeFieldCoefficients

variable (p : ℕ) (G : Type v) [Group G] [TopologicalSpace G]
  [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]

/-- Continuous homomorphisms from the multiplicatively written group to the
additive group of the discrete prime field. -/
abbrev Characters := Additive G →ₜ+ ZMod p

local instance : DistribMulAction G (ZMod p) := primeFieldAction G p

local instance : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩

variable [IsTopologicalGroup G]

/-- First continuous cohomology with the trivial prime-field action. -/
abbrev PrimeCohomology := ContinuousH G (ZMod p) 1

/-- The prime-field scalar structure on characters, induced by pointwise addition. -/
abbrev charactersModule : Module (ZMod p) (Characters p G) :=
  AddCommGroup.zmodModule fun f => by
    ext g
    exact (ContinuousAddMonoidHom.nsmul_apply f p g).trans (nsmul_primeField p (f g))

/-- The prime-field scalar structure on cohomology, induced by pointwise addition of cochains. -/
abbrev primeCohomologyModule : Module (ZMod p) (PrimeCohomology p G) :=
  AddCommGroup.zmodModule fun h => by
    obtain ⟨c, rfl⟩ := (continuousCoboundaries G (ZMod p) 1).mkQ_surjective h
    change p • continuousClass G (ZMod p) 1 c = 0
    rw [← map_nsmul]
    have hc : p • c = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      funext g
      exact nsmul_primeField p (c.val.val g)
    rw [hc, map_zero]

end PrimeFieldCoefficients

/-- The Artin–Schreier connecting isomorphism and the degree-one character comparison. -/
def ConnectingIsomorphism : Prop :=
  ∀ (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
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
      ∀ (a : k) (α : S), wp p S α = algebraMap k S a → ∀ g : G,
        primeFieldInclusion p S
          ((toCharacter.toFun (connect.toFun (quotientMap p k a))) (Additive.ofMul g)) = g • α - α

end

end Specs.GaloisFormalization.GH.ArtinSchreierConnecting
