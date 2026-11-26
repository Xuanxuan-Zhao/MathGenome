import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelPositivity
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.BorelPairs

open GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive IsSplitTorus)
open GeometricBorelConjugacy (ConjugatesSubgroups IsBorel IsKBorel subgroupOfSubgroup)
open BorelProper (ContainsGeometricBorel)
open AbstractPairing (Datum)
open BorelPositivity (BorelCorrespondence RadicalDecomposition WeylAction)
open OrderedRootProducts (RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

/-- Over the algebraic closure a Borel pair exists, and rational points
conjugate both Borel subgroups and pairs of a Borel and a maximal torus in it. -/
def GeometricConjugacy : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    let Gbar := GeometricGroup G
    (∃ B : ClosedSubgroup Gbar.val, IsBorel B ∧
      ∃ T : ClosedSubgroup B.group, IsMaximalTorus T) ∧
    ∀ (B₁ B₂ : ClosedSubgroup Gbar.val), IsBorel B₁ → IsBorel B₂ →
      (∃ g : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶ Gbar.val.X,
        ConjugatesSubgroups g B₁ B₂) ∧
      ∀ (T₁ : ClosedSubgroup B₁.group) (T₂ : ClosedSubgroup B₂.group),
        IsMaximalTorus T₁ → IsMaximalTorus T₂ →
        ∃ g : 𝟙_ (SchemeOver (AlgebraicClosure k)) ⟶ Gbar.val.X,
          ConjugatesSubgroups g B₁ B₂ ∧
          ConjugatesSubgroups g (subgroupOfSubgroup B₁ T₁) (subgroupOfSubgroup B₂ T₂)

/-- The right fppf quotient exists, and it is proper precisely when the
geometric subgroup contains a Borel. -/
def PropernessCriterion : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    ∀ (P : ClosedSubgroup G.val), Smooth P.group.X.hom →
      Nonempty (QuotientEmbedding.Presentation P) ∧
      ∀ Q : QuotientEmbedding.Presentation P,
        IsProper Q.scheme.hom ↔ ContainsGeometricBorel P

/-- Borels through a split maximal torus correspond to the positive systems
of the actual roots. The identified scheme Weyl group acts simply transitively,
and the Borel splits over the torus with the ordered root product as radical. -/
def SplitBorels : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ D : Datum T,
          Nonempty (DatumAndWeyl.Identification D) ∧
          BorelCorrespondence T ∧ WeylAction D ∧ Nonempty (RootSubgroupFamily T) ∧
          ∀ B : ClosedSubgroup G.val, IsKBorel B → IsSubgroupOf T B →
            RadicalDecomposition T B

/-- A pinning consists of equivariant additive coordinates on the simple root
subgroups of the specified split Borel pair. -/
def pinning {k : Type u} [Field k] (A : AdditiveLine k) (P : Pinning.SplitBorelPair k)
    (U : RootSubgroupFamily P.T) : Type u :=
  ∀ α : Pinning.SimpleRoot P, Pinning.RootCoordinate A P.T (U α.val).val α.val.val

/-- Differentiation gives the equivalent choices of nonzero simple root vectors.
Changes of coordinates are exactly the corresponding unit scalings. -/
def PinningAndRootVectors : Prop :=
  Pinning.AdditiveLineExists.{u} ∧ Pinning.PinningsExist.{u} ∧
    Pinning.PinningVectors.{u} ∧ Pinning.CoordinateChanges.{u}

/-- A connected reductive group is quasi-split if it has a Borel over its
ground field. -/
def isQuasiSplit {k : Type u} [Field k] (G : AffineAlgebraicGroup k) : Prop :=
  IsReductive G ∧ ∃ B : ClosedSubgroup G.val, IsKBorel B

end

end LinearAlgebraicGroups.Specs.BorelPairs
