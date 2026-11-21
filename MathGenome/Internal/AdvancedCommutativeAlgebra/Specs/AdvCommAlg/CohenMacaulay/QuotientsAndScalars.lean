import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.RegularQuotient
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! CM-05, paper.tex:3336–3354. Algebra structures encode the ring map and
scalar towers encode restriction of the same module action. Surjectivity
between local rings implies that the map is local. Dimension and depth
comparison include the zero module (dimension bottom, depth infinity).
The singleton list generates the principal ideal (x). -/
universe u
namespace AdvCommAlg.CohenMacaulay.Specs

def dimension_of_surjectiveType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (L : Type u) [AddCommGroup L] [Module R L] [Module S L]
    [IsScalarTower R S L] [Module.Finite S L],
    Function.Surjective (algebraMap R S) → dimensionValue R L = dimensionValue S L

def depth_of_surjectiveType : Prop :=
  ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (L : Type u) [AddCommGroup L] [Module R L] [Module S L]
    [IsScalarTower R S L] [Module.Finite S L] [IsLocalRing R] [IsLocalRing S],
    Function.Surjective (algebraMap R S) →
      Depth.Specs.depthValue R L = Depth.Specs.depthValue S L

def localCohenMacaulay_quotient_regularType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R), x ∈ IsLocalRing.maximalIdeal R →
    Function.Injective (fun m : M => x • m) →
    (LocalCohenMacaulayValue R M ↔ LocalCohenMacaulayValue R (QuotSMulTop x M))

def localCohenMacaulay_quotient_regular_scalarsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R),
    Function.Injective (fun m : M => x • m) →
    letI := Depth.regularQuotientLocalRing [x] (by simpa using hx)
    (LocalCohenMacaulayValue R M ↔
      LocalCohenMacaulayValue (R ⧸ Ideal.ofList [x])
        (M ⧸ (Ideal.ofList [x] • (⊤ : Submodule R M))))

end AdvCommAlg.CohenMacaulay.Specs
