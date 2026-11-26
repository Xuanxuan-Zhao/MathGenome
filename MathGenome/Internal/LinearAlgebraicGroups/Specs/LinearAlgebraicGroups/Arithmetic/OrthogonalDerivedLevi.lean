import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitInducedWeilProduct
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

open AlgebraicGeometry CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.OrthogonalDerivedLevi

open AutomorphismSequence (AdjointQuotient SplitSequence relativePoints)
open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)
open GeometricBorelConjugacy (IsQuasiSplit)
open GeometricRadicals (IsReductive IsSemisimple IsTorus)
open Pinning (AttachedDatum PinnedGroup)
open QuasiSplitInducedWeilProduct (ProductDescent)
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (IsInduced fieldTest transportedAut)
open RootGroups (AdditiveLine)
open SchemeDerivedGroup (IsDerivedSubgroup)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open StandardGroups (specialLinearPoints)
open StandardParabolicLevi (HasFace)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Descent.Forms (IsScalarExtensionComparison spectrumIso)

/-- A standard face of orthogonal simple roots in a simply connected
group gives a product of embedded split rank-one groups after the
comparison, with the corresponding semilinear action on its factors. -/
def DerivedFactors : Prop :=
  ∀ (F K I : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Finite I] [MulAction Gal(K/F) I]
    {A : AdditiveLine F} (P : PinnedGroup A) (D : AttachedDatum P.pair)
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    (seq : SplitSequence P D l Q), IsSemisimple P.pair.G → GeometricallySimplyConnected P.pair.G →
    ∀ (G : AffineAlgebraicGroup F) (c : Cocharacter G.val) (M : LimitDecomposition c),
      IsReductive (closedSubgroupAlgebraicGroup M.centralizer) →
      ∀ (d₀ : Cocharacter P.pair.T.group) (M₀ : LimitDecomposition (d₀ ≫ P.pair.T.inclusion))
        (a : (groupBaseChange F K).obj P.pair.G.val ≅ (groupBaseChange F K).obj G.val)
        (p : (groupBaseChange F K).obj M₀.parabolic.group ≅
          (groupBaseChange F K).obj M.parabolic.group)
        (b : (groupBaseChange F K).obj M₀.centralizer.group ≅
          (groupBaseChange F K).obj M.centralizer.group)
        (iK : relativePoints P.pair.G.val (fieldTest F K) ≅ relativePoints G.val (fieldTest F K)),
        IsInduced F K a iK →
        (groupBaseChange F K).map M₀.parabolic.inclusion ≫ a.hom =
          p.hom ≫ (groupBaseChange F K).map M.parabolic.inclusion →
        (groupBaseChange F K).map M₀.centralizer.inclusion ≫ a.hom =
          b.hom ≫ (groupBaseChange F K).map M.centralizer.inclusion →
        ∀ r : I ↪ D.toBased.I, Set.range r ⊆ D.toBased.base.support →
          (letI := D.comm; HasFace D.base (Set.range r) d₀) →
          (∀ i j, i ≠ j → D.toBased.datum.pairing (r i) (r j) = 0) →
          (∀ (σ : Gal(K/F)) i,
            (outerHom seq (transportedAut F K iK σ)).asIso.hom.val.indexEquiv (r i) =
              r (σ • i)) →
          let L := closedSubgroupAlgebraicGroup M.centralizer
          ∃ (H : ClosedSubgroup L.val) (X : ProductDescent (F := F) (K := K) (I := I))
            (j : specGroup X.descent.coordinate ≅ H.group)
            (t : ∀ B : HopfAlgebraCategory F,
              specGroup (extendedHopf K B) ≅ (groupBaseChange F K).obj (specGroup B)),
            IsDerivedSubgroup H ∧ IsScalarExtensionComparison t ∧
            (∀ i, Nonempty ((groupPointsFunctor K).obj (specGroup (X.factor i)) ≅
              specialLinearPoints K (ULift.{u} (Fin 2)))) ∧
            (IsEmpty I → IsTorus L.val) ∧
            (∀ (E : Type u) [Field E] [Algebra F E],
              IsQuasiSplit (baseChangedAlgebraicGroup E L) →
                IsQuasiSplit (baseChangedAlgebraicGroup E (closedSubgroupAlgebraicGroup H))) ∧
            let γ := (groupBaseChange F K).mapIso j.symm ≪≫
              (t X.descent.coordinate).symm ≪≫ spectrumIso X.descent.comparison
            ∀ i, ∃ f : (groupBaseChange F K).obj (P.roots (r i)).val.group ⟶
                (groupBaseChange F K).obj H.group,
              f ≫ (groupBaseChange F K).map (H.inclusion ≫ M.centralizer.inclusion) =
                (groupBaseChange F K).map (P.roots (r i)).val.inclusion ≫ a.hom ∧
              (∀ j', j' ≠ i → f ≫ γ.hom ≫ specGroupMap (X.projection j') = 0) ∧
              IsClosedImmersion (f ≫ γ.hom ≫ specGroupMap (X.projection i)).hom.hom.left

end LinearAlgebraicGroups.Specs.Arithmetic.OrthogonalDerivedLevi
