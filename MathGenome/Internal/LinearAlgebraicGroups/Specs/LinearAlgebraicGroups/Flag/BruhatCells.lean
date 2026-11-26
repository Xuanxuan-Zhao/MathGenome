import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SimpleRoots

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.BruhatCells

open AbstractPairing (Datum)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (Cell IsConjugateIntersection IsRepresentative OrderedParametrization)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open OrderedRootProducts (RootSubgroupFamily)
open QuotientEmbedding (Presentation)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleRoots (IsBaseFor evaluate wordLength)
open Unipotent (closedSubgroupAlgebraicGroup)

/-- Affine space over the ground field as the product of `n` copies of
`Spec k[t]` over `Spec k`. -/
noncomputable def affineSpace (k : Type u) [Field k] (n : ℕ) : SchemeOver k :=
  OrderedRootProducts.product
    (fun _ : PUnit.{u + 1} ↦ (testSpec k).obj (.op (CommAlgCat.of k (Polynomial k))))
    (List.replicate n PUnit.unit)

/-- The split Bruhat stratification of the group and its right flag quotient.
The cells record the locally closed embeddings, the scheme multiplication
parametrizations, the pullback along the quotient, and the double coset formula
on test schemes, in particular on ground-field points. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (I : Identification D) (U : RootSubgroupFamily T)
        (Bneg : ClosedSubgroup G.val) (Rpos : ClosedSubgroup B.group)
        (Rneg : ClosedSubgroup Bneg.group) (c : Cocharacter T.group) (b : D.rootDatum.Base),
        IsKBorel Bneg ∧ IsSubgroupOf T Bneg ∧
        subgroupRoots T Bneg = (subgroupRoots T B)ᶜ ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup B) Rpos ∧
        IsUnipotentRadical (closedSubgroupAlgebraicGroup Bneg) Rneg ∧
        IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
        IsBaseFor D.rootDatum (evaluate D c) b ∧
        (∀ w, ∃ n, IsRepresentative I w n) ∧ Nonempty (Presentation B) ∧
        ∀ Q : Presentation B,
          ∃ a : ModObj G.val.X Q.scheme,
            lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
              μ[G.val.X] ≫ Q.projection ∧
            ∀ n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X),
              (∀ w, IsRepresentative I w (n w)) →
              let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
              ∃ (A : D.rootDatum.weylGroup → ClosedSubgroup G.val)
                (C : ∀ w, Cell (T := T) Q a (g w) (A w)),
                (∀ w,
                  IsConjugateIntersection (subgroupOfSubgroup B Rpos)
                    (subgroupOfSubgroup Bneg Rneg) (A w) (g w) ∧
                  OrderedParametrization U
                    (subgroupRoots T B ∩ (D.rootDatum.weylGroupToPerm w '' subgroupRoots T Bneg))
                    (A w) ∧
                  Nonempty ((C w).orbit ≅ affineSpace k (wordLength D.rootDatum b w))) ∧
                (∀ w v, w ≠ v →
                  Disjoint (Set.range (C w).orbitInclusion.left)
                    (Set.range (C v).orbitInclusion.left) ∧
                  Disjoint (Set.range (C w).doubleOrbitInclusion.left)
                    (Set.range (C v).doubleOrbitInclusion.left)) ∧
                (⋃ w, Set.range (C w).doubleOrbitInclusion.left) = Set.univ ∧
                (⋃ w, Set.range (C w).orbitInclusion.left) = Set.univ

end LinearAlgebraicGroups.Specs.BruhatCells
