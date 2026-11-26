import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CechDualizingComplexModel
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CohenMacaulayLocalCohomology
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalQuotient

noncomputable section

open CategoryTheory Opposite
open IsLocalRing (maximalIdeal)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (matlisBidualEvaluationValue matlisDualValue residueFieldEnvelopeValue)

namespace Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration

open CechDualizingComplexModel (cechDual)
open RegularCoverDualizingModel (Complex ShiftedRingResolution dualizingComplex)

universe u w

variable {R : Type u} [CommRing R]

def CanonicalModuleType :=
  ∀ {R : Type u} [CommRing R], Complex R → ℕ → ModuleCat.{u} R

/-- The canonical module obtained from a model of the normalized dualizing complex. -/
def canonicalModule (D : Complex R) (d : ℕ) : ModuleCat.{u} R :=
  D.homology (-(d : ℤ))

/-- Finiteness, the two Matlis dual identifications, uniqueness among finite
modules, and the criterion for the dualizing object to be a shifted module. -/
def CanonicalModuleProperties [IsLocalRing R] [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (E : residueFieldEnvelopeValue R) (D : Complex R) (d : ℕ) : Prop :=
  let ω := canonicalModule D d
  let H := (IdealTorsion.localCohomology (maximalIdeal R) (d : ℤ)).obj (ModuleCat.of R R)
  let dual := matlisDualValue E
  Module.Finite R ω ∧
    (∃ (e : ω ≅ dual.obj (op H)) (b : H ≅ dual.obj (op ω)),
      b.hom = (matlisBidualEvaluationValue E).app H ≫ dual.map e.hom.op) ∧
    (∀ (M : ModuleCat.{u} R) [Module.Finite R M],
      Nonempty (dual.obj (op M) ≅ H) → Nonempty (M ≅ ω)) ∧
    (AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R R ↔
      Nonempty (DerivedCategory.Q.obj D ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj ω)⟦(d : ℤ)⟧))

/-- For every complete Noetherian local ring, the dualized Čech model gives
the canonical module and concentration criterion. -/
def CanonicalModuleAndConcentrationType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (d : ℕ), ringKrullDim R = (d : WithBot ℕ∞) →
    ∀ (E : residueFieldEnvelopeValue R) (rs : List R),
      Ideal.span {r | r ∈ rs} = maximalIdeal R →
      CanonicalModuleProperties E (cechDual E rs) d

/-- The same conclusions for every model built using a complete regular local cover. -/
def CanonicalModuleForCoverType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n d : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
      ringKrullDim R = (d : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (E : residueFieldEnvelopeValue R),
      CanonicalModuleProperties E (dualizingComplex f J.complex) d

/-- In the Cohen–Macaulay case, the cover model gives the canonical module of
GC-10. Its Ext module has the action induced by multiplication on the first
argument, as specified by CanonicalQuotient.omega. -/
def CanonicalModuleExtType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n d : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
      ringKrullDim R = (d : WithBot ℕ∞) →
      AdvCommAlg.CohenMacaulay.LocalCohenMacaulay R R →
    ∀ J : ShiftedRingResolution S n,
      letI := f.toAlgebra
      let W := AdvCommAlg.Gorenstein.CanonicalQuotient.omega S R n d
      d ≤ n ∧ Nonempty (canonicalModule (dualizingComplex f J.complex) d ≅ W) ∧
      ∃ hfin : Module.Finite R W,
        letI := hfin
        AdvCommAlg.Gorenstein.Specs.IsCanonicalModuleValue R W

end Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
