import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CompleteLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality

/-! The Cohen–Macaulay form of local duality for the normalized object of U19. -/

namespace Specs.DerivedFormalization.CohenMacaulayLocalDuality

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalRing (maximalIdeal)
open AdvCommAlg.CohenMacaulay (LocalCohenMacaulay)
open Cochains (derivedStalkValue derivedCohomologyValue)
open DerivedHomModels (Models)
open DerivedCoinduction (Coinduction)
open NormalizedRegularCoverDuality (normalizedObjectValue)
open CompleteLocalDuality (derivedHomFromModule)
open _root_.Specs.CommutativeAlgebraNotes.CompleteLocalDuality (finiteModules)
open _root_.Specs.CommutativeAlgebraNotes.CohenMacaulayLocalDuality (extInto)
open _root_.Specs.CommutativeAlgebraNotes.IdealTorsion (localCohomology)
open _root_.CommutativeAlgebraNotes.MatlisDualFunctorSpecs (matlisDualValue residueFieldEnvelopeValue)

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- For each regular cover of a complete Cohen–Macaulay local ring, the canonical
module is the top local cohomology dual and the sole cohomology of the normalized
object. The shift comparison and local duality identify the same derived Hom
with signed Ext, naturally on finite modules. -/
def CohenMacaulayLocalDualityType : Prop :=
  ∀ {S R : Type u} [CommRing S] [CommRing R] [IsRegularLocalRing S]
    [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal S) S] [IsAdicComplete (maximalIdeal R) R]
    (f : S →+* R) [IsLocalHom f], Function.Surjective f →
    ∀ (d e : ℕ), ringKrullDim S = (d : WithBot ℕ∞) →
      ringKrullDim R = (e : WithBot ℕ∞) → LocalCohenMacaulay R R →
    ∀ (G : Coinduction.{u} f) (HR : Models.{u,u} R) (E : residueFieldEnvelopeValue R),
      let D := normalizedObjectValue f G d
      let ω := (derivedCohomologyValue R (-(e : ℤ))).obj D
      let dual := matlisDualValue E
      let top := (localCohomology (maximalIdeal R) (e : ℤ)).obj (ModuleCat.of R R)
      Module.Finite R ω ∧ Nontrivial ω ∧
      Nonempty (ω ≅ dual.obj (op top)) ∧ Nonempty (top ≅ dual.obj (op ω)) ∧
      (∀ (W : ModuleCat.{u} R) [Module.Finite R W],
        Nonempty (dual.obj (op W) ≅ top) → Nonempty (W ≅ ω)) ∧
      (∀ i : ℤ, i ≠ -(e : ℤ) → IsZero ((derivedCohomologyValue R i).obj D)) ∧
      Nonempty (D ≅ ((derivedStalkValue R).obj ω)⟦(e : ℤ)⟧) ∧
      ∀ q : ℤ,
        let H := (finiteModules R).ι.op ⋙ derivedHomFromModule HR D ⋙
          derivedCohomologyValue R (-q)
        let B := (finiteModules R).ι.op ⋙ (localCohomology (maximalIdeal R) q).op ⋙ dual
        let T := (finiteModules R).ι.op ⋙ extInto ω ((e : ℤ) - q)
        Nonempty (B ≅ H) ∧ Nonempty (H ≅ T) ∧ Nonempty (B ≅ T) ∧
          ((e : ℤ) - q < 0 → ∀ X, IsZero (B.obj X) ∧ IsZero (H.obj X) ∧ IsZero (T.obj X))

end

end Specs.DerivedFormalization.CohenMacaulayLocalDuality
