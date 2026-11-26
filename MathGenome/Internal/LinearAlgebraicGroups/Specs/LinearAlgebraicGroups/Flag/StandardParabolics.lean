import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.StandardParabolics

open AbstractPairing (Datum Root)
open BorelProper (IsParabolic)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsBorel IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal SameSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleRoots (IsBaseFor evaluate)
open StandardParabolicLevi (StandardParabolic parabolicWeylGroup)

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- A subset of the simple roots of the chosen base. -/
abbrev SimpleSubset {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (b : D.rootDatum.Base) :=
  {I : Set (Root T) // I ⊆ (b.support : Set (Root T))}

/-- The Weyl indices of a subgroup containing the chosen Borel are tested on
representatives in the actual torus normalizer. -/
def HasWeylIndices {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    {D : Datum T} (W : Identification D) (P : ClosedSubgroup G.val)
    (S : Set D.rootDatum.weylGroup) : Prop :=
  ∀ (w : D.rootDatum.weylGroup) (n : 𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X),
    IsRepresentative W w n →
      (n ≫ W.normalizer.inclusion.hom.hom ∈ SubgroupSections P (𝟙_ (SchemeOver k)) ↔
        w ∈ S)

/-- The parabolics through the chosen Borel are the standard parabolics.
The family retains the common-kernel torus, the dynamic Levi, the
semidirect decomposition and the ordered radical parametrization. -/
def StandardParabolicClassification : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (W : Identification D) (U : RootSubgroupFamily T)
          (c : Cocharacter T.group) (b : D.rootDatum.Base),
          IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
          IsBaseFor D.rootDatum (evaluate D c) b ∧
          (∀ w, ∃ n, IsRepresentative W w n) ∧
          ∃ P : (I : SimpleSubset b) → StandardParabolic B D b U I.val,
            (∀ I, HasWeylIndices W (P I).limitGroups.parabolic (parabolicWeylGroup D I.val)) ∧
            ∀ H : ClosedSubgroup G.val, IsParabolic G H → IsSubgroupOf B H →
              (∃! I : SimpleSubset b, HasWeylIndices W H (parabolicWeylGroup D I.val)) ∧
              ∀ I : SimpleSubset b, HasWeylIndices W H (parabolicWeylGroup D I.val) ↔
                SameSubgroup H (P I).limitGroups.parabolic

/-- Over an algebraically closed field, every smooth closed subgroup containing
a Borel represents its own normalizer functor on all test schemes. -/
def GeometricParabolicNormalizer : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ P : ClosedSubgroup G.val, Smooth P.group.X.hom →
      (∃ B : ClosedSubgroup G.val, IsBorel B ∧ IsSubgroupOf B P) →
      RepresentsSubgroup P (fun _ g ↦ Normalizes P.inclusion g)

/-- The same scheme-theoretic normalizer equality holds for a parabolic defined
over an arbitrary ground field. -/
def GroundFieldParabolicNormalizer : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    IsParabolic G P → RepresentsSubgroup P (fun _ g ↦ Normalizes P.inclusion g)

end LinearAlgebraicGroups.Specs.StandardParabolics
