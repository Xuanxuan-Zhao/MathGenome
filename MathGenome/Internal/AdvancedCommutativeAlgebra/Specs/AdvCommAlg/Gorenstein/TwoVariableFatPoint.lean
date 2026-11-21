import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.InjectiveEnvelope
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.HopkinsLevitzki

/-! GC-14, second example (paper.tex:4855–4860). The ring is the actual
polynomial quotient by the square of the ideal of the two variables. -/
noncomputable section
universe u
namespace AdvCommAlg.Gorenstein.TwoVariableFatPoint

abbrev PolynomialRing (k : Type u) [Field k] := MvPolynomial (Fin 2) k
abbrev variableIdeal (k : Type u) [Field k] : Ideal (PolynomialRing k) :=
  MvPolynomial.idealOfVars (Fin 2) k
abbrev Ring (k : Type u) [Field k] := PolynomialRing k ⧸ variableIdeal k ^ 2
noncomputable def coordinate (k : Type u) [Field k] (i : Fin 2) : Ring k :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

namespace Spec

def structureType : Prop := ∀ (k : Type u) [Field k],
  IsArtinianRing (Ring k) ∧ IsLocalRing (Ring k)

def geometryType : Prop := ∀ (k : Type u) [Field k]
    [IsArtinianRing (Ring k)] [IsLocalRing (Ring k)],
  ringKrullDim (Ring k) = 0 ∧
    CohenMacaulay.Specs.LocalCohenMacaulayValue (Ring k) (Ring k)

/-- The residue field is k, and the actual classes of x,y are a basis of
its socle for the canonical descended residue-field action. -/
def socleType : Prop := ∀ (k : Type u) [Field k]
    [IsArtinianRing (Ring k)] [IsLocalRing (Ring k)],
  (∃ e : IsLocalRing.ResidueField (Ring k) ≃+* k,
    ∀ a : k, e (IsLocalRing.residue (Ring k) (algebraMap k (Ring k) a)) = a) ∧
  (∃ b : Module.Basis (Fin 2) (IsLocalRing.ResidueField (Ring k))
      (Specs.socleValue (Ring k) (Ring k)),
    ∀ i, (b i).val = coordinate k i) ∧
  Module.finrank (IsLocalRing.ResidueField (Ring k))
    (Specs.socleValue (Ring k) (Ring k)) = 2

def notGorensteinType : Prop := ∀ (k : Type u) [Field k]
    [IsArtinianRing (Ring k)] [IsLocalRing (Ring k)],
  ¬ Specs.LocalGorensteinValue (Ring k)

/-- Every displayed injective envelope is finite, canonical (including MCM
and type one), and has injective dimension exactly zero. Existence is included. -/
def canonicalType : Prop := ∀ (k : Type u) [Field k]
    [IsArtinianRing (Ring k)] [IsLocalRing (Ring k)],
  Nonempty (InjectiveEnvelope (Ring k) (IsLocalRing.ResidueField (Ring k))) ∧
  ∀ (E : Type u) [AddCommGroup E] [Module (Ring k) E]
    (ι : IsLocalRing.ResidueField (Ring k) →ₗ[Ring k] E),
    IsInjectiveEnvelope ι → ∃ hfin : Module.Finite (Ring k) E,
      @Specs.IsCanonicalModuleValue (Ring k) _ _ _ E _ _ hfin ∧
      CategoryTheory.injectiveDimension (ModuleCat.of (Ring k) E) = 0

end Spec
end AdvCommAlg.Gorenstein.TwoVariableFatPoint
