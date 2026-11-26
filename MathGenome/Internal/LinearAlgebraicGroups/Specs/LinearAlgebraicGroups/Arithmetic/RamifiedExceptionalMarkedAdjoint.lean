import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle restriction)

namespace LinearAlgebraicGroups.Specs.RamifiedExceptionalMarkedAdjoint

open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open CentralIsogenies (IsCentralIsogeny)
open ExceptionalAffineBruhat (ExceptionalNumbering RamifiedReference)
open ExceptionalAffineRootSystems (e6Partner exceptionalCartan)
open ExceptionalIwahoriImageComparison (MarkedCentralCover)
open ExceptionalLocalRootCoordinates (ramificationIndex)
open GeometricRadicals (IsSemisimple)
open IntegralSemisimpleModel (Model)
open Pinning (AttachedDatum BasedRootDatum PinnedGroup)
open QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction)
attribute [local instance] QuasiSplitInnerForms.basedAutTopology QuasiSplitInnerForms.basedAutDiscrete
attribute [local instance] QuasiSplitInnerForms.fieldGalTopology
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected)

universe u

/-- The Cartan diagram is E₆ in the numbering used by the affine comparison. -/
def HasE6Diagram (D : BasedRootDatum.{u}) : Prop :=
  ∃ b : Fin 6 ≃ D.base.support,
    ∀ i j, D.datum.pairing (b i) (b j) = exceptionalCartan 6 i j

/-- Naturality of the point comparison under every change of test algebra. -/
def NaturalPointComparison {F : Type u} [Field F] {G H : GroupScheme F}
    (e : G ≅ H) : Prop :=
  ∀ {R R' : TestAlgebra F} (f : R ⟶ R') (g : GroupPoints G R),
    (((groupPointsFunctor F).obj H).map f).hom
        ((((groupPointsFunctor F).mapIso e).hom.app R).hom g) =
      ((((groupPointsFunctor F).mapIso e).hom.app R').hom)
        ((((groupPointsFunctor F).obj G).map f).hom g)

/-- Both marked references for the inflated ramified diagram action, with the
adjoint comparison over the base field and its action on all test algebras. -/
def MarkedReference : Prop :=
  ∀ (F S : Type u) [Field F] [Field S] [Algebra F S] [IsSepClosure F S]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l Q),
    IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G → HasE6Diagram D.toBased →
    ∀ (L : FiniteGaloisIntermediateField F S) [ValuativeRel L] [TopologicalSpace L]
      [IsNonarchimedeanLocalField L] [ValuativeExtension F L],
      Module.finrank F L = 2 → 1 < ramificationIndex F L →
      ∀ (ω : Gal(L/F) →* Aut D.toBased), ω ≠ 1 →
      ∀ (outer : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased)),
        (∀ g, outer g = ω (restriction L g)) →
      ∀ (V : PinnedRepresentative (S := S) E outer),
      ∃ (Dsc Dad : BasedRootDatum.{u}) (M : Model Dsc) (M' : Model Dad)
        (c : MarkedCentralCover M M') (b : Fin 6 ≃ Dsc.base.support)
        (b' : Fin 6 ≃ Dad.base.support)
        (R : RamifiedReference F L M) (R' : RamifiedReference F L M')
        (j : R.descent.group.val ≅ V.model.val.val),
        ExceptionalNumbering Dsc 6 b ∧ ExceptionalNumbering Dad 6 b' ∧
        Dsc.datum.corootSpan ℤ = ⊤ ∧ Dad.datum.rootSpan ℤ = ⊤ ∧
        (∀ (σ : Gal(L/F)), σ ≠ 1 →
          (∀ i, (R.diagram σ).val.indexEquiv (b i) = b (e6Partner i)) ∧
          (∀ i, (R'.diagram σ).val.indexEquiv (b' i) = b' (e6Partner i)) ∧
          (∀ i, c.rootEquiv ((R.diagram σ).val.indexEquiv i) =
            (R'.diagram σ).val.indexEquiv (c.rootEquiv i))) ∧
        NaturalPointComparison j ∧
        ∀ (φ : R.descent.group.val ⟶ R'.descent.group.val), IsCentralIsogeny φ →
          ∀ Q' : AdjointQuotient V.model.val,
            ∃ e : R'.descent.group.val ≅ Q'.quotient.val,
              φ ≫ e.hom = j.hom ≫ Q'.projection ∧ NaturalPointComparison e

end LinearAlgebraicGroups.Specs.RamifiedExceptionalMarkedAdjoint
