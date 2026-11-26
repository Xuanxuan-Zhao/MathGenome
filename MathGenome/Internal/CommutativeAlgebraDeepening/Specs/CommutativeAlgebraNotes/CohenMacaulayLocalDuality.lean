import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CanonicalModuleAndConcentration
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalDualityAfterCompletion
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionOfFiniteExt

noncomputable section

open CategoryTheory Opposite
open IsLocalRing (maximalIdeal)
open AdvCommAlg.CohenMacaulay (LocalCohenMacaulay)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs
  (matlisDualValue matlisBidualEvaluationValue residueFieldEnvelopeValue)
open _root_.CommutativeAlgebraNotes.CompletionOfFiniteExt (signedExt complete completionMap extPush)

namespace Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality

open CompleteLocalDuality (finiteModules)
open IdealTorsion (localCohomology)
open RegularCoverDualizingModel (ShiftedRingResolution dualizingComplex)
open CanonicalModuleAndConcentration (canonicalModule)
open CompletionOfTorsionModules (Completion IsPowerTorsion)
open LocalCohomologyCompletion (adicCompletionFunctor completedAction)
open LocalDualityAfterCompletion (restrictedHullDual)

universe u v w

/-- Ext with a fixed second argument, with the shared zero convention in negative degrees. -/
def extInto {R : Type u} [CommRing R] (W : ModuleCat.{u} R) (j : ℤ) :
    (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  signedExt R j ⋙ (evaluation _ _).obj W

/-- The second comparison is the actual bidual evaluation followed by the dual of
the inverse first comparison. The map `c` accounts for restriction of scalars. -/
def evaluationCompatible {B : Type u} [CommRing B] [IsLocalRing B]
    {C : Type v} [Category.{w} C] (E : residueFieldEnvelopeValue B)
    {H : C ⥤ ModuleCat.{u} B} {F T : Cᵒᵖ ⥤ ModuleCat.{u} B}
    (c : F ≅ H.op ⋙ matlisDualValue E) (a : F ≅ T) : Prop :=
  ∃ b : H ≅ T.rightOp ⋙ matlisDualValue E, ∀ X,
    b.hom.app X = (matlisBidualEvaluationValue E).app (H.obj X) ≫
      (matlisDualValue E).map ((a.inv.app (op X) ≫ c.hom.app (op X)).op)

/-- The regular cover and bounded injective resolution used to model the
normalized dualizing complex. -/
def HasRegularCoverModel (R : Type u) [CommRing R] : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (_ : IsRegularLocalRing S),
    IsAdicComplete (maximalIdeal S) S ∧
      ∃ f : S →+* R, IsLocalHom f ∧ Function.Surjective f ∧
        ∃ n : ℕ, ringKrullDim S = (n : WithBot ℕ∞) ∧
          Nonempty (ShiftedRingResolution S n)

/-- Cohen–Macaulay local duality for every regular-cover model of the normalized
dualizing complex of a complete Noetherian local ring. -/
def CompleteCohenMacaulayLocalDualityType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → LocalCohenMacaulay R R →
    HasRegularCoverModel R ∧
    ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
      (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (E : residueFieldEnvelopeValue R) (i : ℤ),
      let H := (finiteModules R).ι ⋙ localCohomology (maximalIdeal R) i
      let W := canonicalModule (dualizingComplex f J.complex) d
      let T := (finiteModules R).ι.op ⋙ extInto W ((d : ℤ) - i)
      ∃ a : H.op ⋙ matlisDualValue E ≅ T, evaluationCompatible E (Iso.refl _) a

section Completion

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

attribute [local instance] MatlisHullUnderCompletion.restrictedHullModule
  MatlisHullUnderCompletion.restrictedHullScalarTower

/-- An original-linear functional on a power-torsion module extends uniquely to
a completed-linear functional with the same values. -/
def completedCohomologyDualIso (E : residueFieldEnvelopeValue (Completion R))
    (G : ModuleCat.{u} R ⥤ ModuleCat.{u} R) (h : ∀ X, IsPowerTorsion R (G.obj X)) :
    ((finiteModules R).ι ⋙ G).op ⋙ restrictedHullDual E ≅
      ((finiteModules R).ι ⋙ completedAction G h).op ⋙ matlisDualValue E :=
  NatIso.ofComponents (fun X =>
    (MatlisHullUnderCompletion.completedMatlisDualEquiv E (h X.unop.obj)).toModuleIso)
    (fun _ => ModuleCat.hom_ext (LinearMap.ext fun _ => LinearMap.ext fun _ => rfl))

end Completion

/-- Both comparisons after completion and the completed-Ext formula for any
finite coefficient module whose completion is identified with the canonical module. -/
def CohenMacaulayLocalDualityAfterCompletionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (d : ℕ),
    ringKrullDim R = (d : WithBot ℕ∞) → LocalCohenMacaulay R R →
    HasRegularCoverModel (Completion R) ∧
    ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
      (f : S →+* Completion R) [IsLocalHom f], Function.Surjective f →
    ∀ {n : ℕ}, ringKrullDim S = (n : WithBot ℕ∞) →
    ∀ (J : ShiftedRingResolution S n) (E : residueFieldEnvelopeValue (Completion R)) (i : ℤ),
      let G := localCohomology (maximalIdeal R) i
      let W := canonicalModule (dualizingComplex f J.complex) d
      let K := (finiteModules R).ι ⋙ adicCompletionFunctor R
      let F := ((finiteModules R).ι ⋙ G).op ⋙ restrictedHullDual E
      let j := (d : ℤ) - i
      let T := K.op ⋙ extInto W j
      ∃ (h : ∀ X, IsPowerTorsion R (G.obj X)) (a : F ≅ T),
        evaluationCompatible E (completedCohomologyDualIso E G h) a ∧
        ∀ (ω : ModuleCat.{u} R) [Module.Finite R ω] (e : (adicCompletionFunctor R).obj ω ≅ W),
          ∃ b : F ≅ (finiteModules R).ι.op ⋙ extInto ω j ⋙ complete R,
            ∀ X : (finiteModules R).FullSubcategory,
              letI : Module.Finite R X.obj := X.property
              b.hom.app (op X) ≫ ModuleCat.ofHom (completionMap R X.obj ω j) ≫
                extPush (K.obj X) e.hom j = a.hom.app (op X)

end Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality
