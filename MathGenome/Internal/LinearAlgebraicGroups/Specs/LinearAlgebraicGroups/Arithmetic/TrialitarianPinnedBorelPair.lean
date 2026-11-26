import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitOrbitLevis
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianPinnedBorelPair

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open DatumAndWeyl (Identification)
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open GeometricBorelConjugacy (IsQuasiSplit subgroupOfSubgroup)
open GeometricRadicals (IsSemisimple)
open OrderedRootProducts (RootSubgroupFamily)
open Pinning (AttachedDatum PinnedGroup Pinning SplitBorelPair)
open QuasiSplitFixedWeyl (IsLargestSplitSubtorus IsScalarAction)
open QuasiSplitInnerForms (outerHom)
open QuasiSplitOrbitLevis
  (IsAmbientPinnedAction MultiplicativeComparison PreservesUnits SplitPairOver simplePermutation)
open QuasiSplitPinnedPairModel (BorelPair)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open RelativeFormComparison (IsInduced fieldTest transportedAut)
open RootGroups (AdditiveLine rootPoint)
open SchemeDerivedGroup (IsSubgroupOf)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Forget the preservation of the simple system in a based datum action. -/
def underlyingAction {K : Type u} [Field K] {P : SplitBorelPair K}
    (D : AttachedDatum P) {Γ : Type*} [Group Γ] (ω : Γ →* Aut D.toBased) :
    letI := D.comm
    Γ →* D.datum.rootDatum.Aut := by
  letI := D.comm
  exact
    { toFun := fun σ => (ω σ).asIso.hom.val
      map_one' := by rw [map_one]; rfl
      map_mul' := fun σ τ => by rw [map_mul]; rfl }

/-- The actual Borel pair of the quasi-split form, with pinning over a finite
Galois layer and simple-root labels compared to the prescribed split reference. -/
def Statement : Prop :=
  ∀ {F Fsep : Type u} [Field F] [Field Fsep] [Algebra F Fsep] [IsSepClosure F Fsep]
    (G : AffineAlgebraicGroup F),
    IsSemisimple G → GeometricallySimplyConnected G → IsQuasiSplit G →
    ∀ {A₀ : AdditiveLine F} {P₀ : PinnedGroup A₀} {D₀ : AttachedDatum P₀.pair}
      {l : Aut D₀.toBased ≃* Aut P₀} {Q : AdjointQuotient P₀.pair.G}
      (E : SplitSequence P₀ D₀ l Q)
      (f : (groupBaseChange F Fsep).obj P₀.pair.G.val ≅ (groupBaseChange F Fsep).obj G.val)
      (i : relativePoints P₀.pair.G.val (fieldTest F Fsep) ≅
        relativePoints G.val (fieldTest F Fsep)),
      IsInduced F Fsep f i →
      ∃ (K : FiniteGaloisIntermediateField F Fsep) (M : BorelPair G)
        (S : ClosedSubgroup M.torus.group),
        IsLargestSplitSubtorus S ∧
        IsMaximalSplitTorus (subgroupOfSubgroup M.torus S) ∧
        RepresentsSubgroup M.torus
          (fun _ g => Centralizes (subgroupOfSubgroup M.torus S).inclusion g) ∧
        IsMinimalParabolic G M.positive ∧
        IsSubgroupOf (subgroupOfSubgroup M.torus S) M.positive ∧
        ∃ (P : SplitPairOver (K := K) G M.torus M.positive) (D : AttachedDatum P.pair),
          letI := D.comm
          ∃ (_ : Identification D.datum)
            (A : AdditiveLine K) (U : RootSubgroupFamily P.pair.T) (p : Pinning A P.pair U)
            (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
            (m : MultiplicativeComparison F K) (ω : Gal(K/F) →* Aut D.toBased)
            (j : D₀.toBased.base.support ≃ D.toBased.base.support),
            (∀ (R : TestAlgebra K) (v : R),
              baseChangePoint F K A₀.group.X R (rootPoint a.inv R v) =
                rootPoint (𝟙 A₀.group) ((restrictTestAlgebra F K).obj R) v) ∧
            PreservesUnits m ∧
            IsAmbientPinnedAction D p a m ω ∧
            IsScalarAction M.torus P.torusClosed D.comm D.datum m (underlyingAction D ω) ∧
            (∀ x y, D.toBased.datum.pairing (j y).val (j x).val =
              D₀.toBased.datum.pairing y.val x.val) ∧
            ∀ (σ : Gal(Fsep/F)) (x : D₀.toBased.base.support),
              simplePermutation D (ω (restriction K σ)) (j x) =
                j (simplePermutation D₀ (outerHom E (transportedAut F Fsep i σ)) x)

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianPinnedBorelPair
