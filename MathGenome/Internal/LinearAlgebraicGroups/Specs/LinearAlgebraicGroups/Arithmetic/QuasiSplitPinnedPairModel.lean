import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitPinnedPairModel

open AdjointBorelCohomology (PinnedTwist extendedCharacterValue)
open AdjointCocharacters (coordinateHopf coordinateHopfIso coordinateHopfMap)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open GeometricRadicals (IsSemisimple IsTorus IsUnipotentRadical)
open Pinning (AttachedDatum PinnedGroup transportCharacter)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (AdditiveLine)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open Unipotent (closedSubgroupAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)
open LinearAlgebraicGroups.Descent (SemilinearAction)
open LinearAlgebraicGroups.Descent.Forms (spectrumIso IsScalarExtensionComparison)

noncomputable section

variable {k : Type u} [Field k]

/-- The two opposite rational Borels, their common geometrically maximal torus,
and their actual unipotent radicals as closed subgroup schemes. -/
structure BorelPair (G : AffineAlgebraicGroup k) where
  positive : ClosedSubgroup G.val
  negative : ClosedSubgroup G.val
  torus : ClosedSubgroup G.val
  positiveRadical : ClosedSubgroup positive.group
  negativeRadical : ClosedSubgroup negative.group
  positiveBorel : IsKBorel positive
  negativeBorel : IsKBorel negative
  isTorus : IsTorus torus.group
  maximal : IsGeometricallyMaximal torus
  intersection : IsSchemeIntersection {positive, negative} torus
  positiveUnipotentRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup positive)
    positiveRadical
  negativeUnipotentRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup negative)
    negativeRadical

/-- The distinguished closed subgroup inclusions into the ambient group. -/
inductive Marking
  | positive | negative | torus | positiveRadical | negativeRadical

def BorelPair.subgroup {G : AffineAlgebraicGroup k} (M : BorelPair G) :
    Marking → ClosedSubgroup G.val
  | .positive => M.positive
  | .negative => M.negative
  | .torus => M.torus
  | .positiveRadical => subgroupOfSubgroup M.positive M.positiveRadical
  | .negativeRadical => subgroupOfSubgroup M.negative M.negativeRadical

variable {K : Type u} [Field K] [Algebra k K]

/-- An isomorphism of scalar-extended groups with its squares on every mark. -/
structure MarkedComparison {G H : AffineAlgebraicGroup k} (M : BorelPair G) (N : BorelPair H) where
  groupIso : (groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val
  subgroupIso : ∀ m, (groupBaseChange k K).obj (M.subgroup m).group ≅
    (groupBaseChange k K).obj (N.subgroup m).group
  commutes : ∀ m, (groupBaseChange k K).map (M.subgroup m).inclusion ≫ groupIso.hom =
    (subgroupIso m).hom ≫ (groupBaseChange k K).map (N.subgroup m).inclusion

/-- Coordinate maps of the five marked inclusions in the common splitting field. -/
abbrev extendedInclusion {G : AffineAlgebraicGroup k} (M : BorelPair G) (m : Marking) :=
  extendedHopfMap K (coordinateHopfMap
    (G := closedSubgroupAlgebraicGroup (M.subgroup m)) (H := G) (M.subgroup m).inclusion)

/-- The comparison is obtained from the indicated coordinate isomorphism by
inverse pullback and the canonical scalar-extension identifications. -/
def MatchesCoordinateComparison {G H : AffineAlgebraicGroup k}
    {M : BorelPair G} {N : BorelPair H} (e : MarkedComparison (K := K) M N)
    (i : extendedHopf K (coordinateHopf G) ≅ extendedHopf K (coordinateHopf H)) : Prop :=
  ∃ (t : ∀ A : HopfAlgebraCategory k,
      specGroup (extendedHopf K A) ≅ (groupBaseChange k K).obj (specGroup A)),
    IsScalarExtensionComparison t ∧
    e.groupIso = ((groupBaseChange k K).mapIso (coordinateHopfIso G)).symm ≪≫
      (t (coordinateHopf G)).symm ≪≫ spectrumIso i ≪≫ t (coordinateHopf H) ≪≫
      (groupBaseChange k K).mapIso (coordinateHopfIso H)

def MarkedComparisonOfHopf : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H : AffineAlgebraicGroup k} (M : BorelPair G) (N : BorelPair H)
    (i : extendedHopf K (coordinateHopf G) ≅ extendedHopf K (coordinateHopf H))
    (d : ∀ m, extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup (M.subgroup m))) ≅
      extendedHopf K (coordinateHopf (closedSubgroupAlgebraicGroup (N.subgroup m)))),
    (∀ m, i.hom ≫ extendedInclusion (K := K) N m =
      extendedInclusion (K := K) M m ≫ (d m).hom) →
    ∃ e : MarkedComparison (K := K) M N, MatchesCoordinateComparison e i

/-- The weight and coweight maps of a based automorphism are the maps from
the restriction of its pinned lift to the pinned torus. -/
def IsBasedLift {A : AdditiveLine k} {P : PinnedGroup A} (D : AttachedDatum P.pair)
    (lift : Aut D.toBased ≃* Aut P) : Prop :=
  ∀ a : Aut D.toBased,
    let t := (lift a).asIso.hom.torus
    (∀ χ : CharacterDescent.Character P.pair.T.group,
      a.asIso.hom.val.weightEquiv (Additive.ofMul χ) = Additive.ofMul (transportCharacter t χ)) ∧
    (∀ c : CharacterDescent.Cocharacter P.pair.T.group,
      a.asIso.hom.val.coweightEquiv (Additive.ofMul c) = Additive.ofMul (c ≫ t.inv))

/-- The comparison on the specified torus carries its coefficient Galois
action on characters to the weight action of the actual based datum. -/
def IsTransportedBasedAction {A : AdditiveLine k} {P : PinnedGroup A}
    {D : AttachedDatum P.pair} {lift : Aut D.toBased ≃* Aut P}
    {G : AffineAlgebraicGroup k} {B T : ClosedSubgroup G.val}
    (twist : PinnedTwist K D lift B T) : Prop :=
  let T₀ := closedSubgroupAlgebraicGroup P.pair.T
  let C := coordinateHopf (closedSubgroupAlgebraicGroup T)
  ∃ e : CharacterDescent.Character T₀.val ≃* CharacterDescent.GeometricCharacters K C,
    (∀ χ, (e χ).val = twist.torusIso.hom.hom (extendedCharacterValue K T₀ χ)) ∧
    ∀ (σ : Gal(K/k)) χ,
      (SemilinearAction.scalarExtension (K := K) C).act σ (e χ).val =
        (e (Additive.toMul ((twist.outer σ).asIso.hom.val.weightEquiv (Additive.ofMul χ)))).val

/-- A split model over one field, with the full coroot lattice, is realized
by scalar extension of a split pinned model over the ground field. -/
def GroundFieldModel : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (Q : Pinning.SplitBorelPair K) (E : AttachedDatum Q),
    corootLattice E = ⊤ →
    ∃ (A : AdditiveLine k) (P : PinnedGroup A) (D : AttachedDatum P.pair),
      IsSemisimple P.pair.G ∧ corootLattice D = ⊤ ∧
      Nonempty ((groupBaseChange k K).obj P.pair.G.val ≅ Q.G.val)

/-- An actual geometrically simply connected form forces the coroot lattice
of a split pair over an algebraic splitting field to be the full lattice. -/
def CorootLatticeAfterSplitting : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (G : AffineAlgebraicGroup k), IsSemisimple G → GeometricallySimplyConnected G →
    ∀ (Q : Pinning.SplitBorelPair K) (D : AttachedDatum Q),
      Nonempty ((groupBaseChange k K).obj G.val ≅ Q.G.val) → corootLattice D = ⊤

/-- The torus in the given pair becomes split over a finite Galois layer
inside the chosen separable closure. -/
def FiniteTorusSplitting : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (T : AffineAlgebraicGroup k), IsTorus T.val →
    ∃ L : FiniteGaloisIntermediateField k S,
      GeometricRadicals.IsSplitTorus ((groupBaseChange k L).obj T.val)

/-- Once the specified torus splits, it is a split geometrically maximal
torus in the scalar extension and admits a split Borel pair there. -/
def SplitPairOverField : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k), GeometricRadicals.IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsTorus T.group → IsGeometricallyMaximal T →
      GeometricRadicals.IsSplitTorus ((groupBaseChange k K).obj T.group) →
      ∃ Q : Pinning.SplitBorelPair K, Q.G = Unipotent.baseChangedAlgebraicGroup K G

local instance (D : Pinning.BasedRootDatum.{u}) : TopologicalSpace (Aut D) := ⊥

local instance {S : Type u} [Field S] [Algebra k S] :
    TopologicalSpace (Gal(S/k)) := krullTopology k S

/-- The quasi-split member of the outer fibre of the split model is
isomorphic over the ground field to the given quasi-split form. -/
def PinnedModelOfForm : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    {A : AdditiveLine k} (P : PinnedGroup A)
    (H : LinearAlgebraicGroups.Descent.Forms.SchemeModels S P.pair.G),
    GeometricBorelConjugacy.IsQuasiSplit H.val →
    ∃ (D : AttachedDatum P.pair) (lift : Aut D.toBased ≃* Aut P)
      (Q : AutomorphismSequence.AdjointQuotient P.pair.G)
      (E : AutomorphismSequence.SplitSequence P D lift Q)
      (ω : LinearAlgebraicGroups.Descent.NonabelianCohomology.Cocycle
        (QuasiSplitInnerForms.trivialOuterAction (k := k) (S := S) D.toBased))
      (W : QuasiSplitInnerForms.PinnedRepresentative (S := S) E ω),
      IsBasedLift D lift ∧ Nonempty (W.model.val.val ≅ H.val.val)

/-- The finite pinned descent model before comparing the rational marks. -/
def UnmarkedModel : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G → BorelPair G →
    ∃ (A : AdditiveLine k) (P : PinnedGroup A)
      (D : AttachedDatum P.pair) (lift : Aut D.toBased ≃* Aut P)
      (Q : AutomorphismSequence.AdjointQuotient P.pair.G)
      (E : AutomorphismSequence.SplitSequence P D lift Q)
      (ω : LinearAlgebraicGroups.Descent.NonabelianCohomology.Cocycle
        (QuasiSplitInnerForms.trivialOuterAction (k := k) (S := SeparableClosure k) D.toBased))
      (W : QuasiSplitInnerForms.PinnedRepresentative (S := SeparableClosure k) E ω),
      IsSemisimple P.pair.G ∧ corootLattice D = ⊤ ∧
      IsBasedLift D lift ∧ Nonempty (W.model.val.val ≅ G.val)

/-- The finite pinned comparison on the actual positive rational Borel
and common torus. The opposite Borel and radicals are additional marks
in the full assertion. -/
def PositivePinnedComparison : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G → ∀ M : BorelPair G,
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
      (_ : IsGalois k K) (A : AdditiveLine k) (P : PinnedGroup A)
      (D : AttachedDatum P.pair) (lift : Aut D.toBased ≃* Aut P)
      (_ : PinnedTwist K D lift M.positive M.torus),
      IsSemisimple P.pair.G ∧ corootLattice D = ⊤ ∧ IsBasedLift D lift

/-- The split positive Borel and torus of a pinning extend to an opposite
pair with its two scheme-theoretic unipotent radicals. -/
def SplitOppositePair : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A),
    ∃ M : BorelPair P.pair.G, M.positive = P.pair.B ∧ M.torus = P.pair.T

/-- Over a field splitting the specified Borel torus, the base change of
the actual unipotent radical is the unipotent radical. -/
def BorelRadicalBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k), GeometricRadicals.IsReductive G →
    ∀ (B : ClosedSubgroup G.val), IsKBorel B →
    ∀ (T : ClosedSubgroup B.group), IsGeometricallyMaximal (subgroupOfSubgroup B T) →
      GeometricRadicals.IsSplitTorus ((groupBaseChange k K).obj T.group) →
    ∀ (U : ClosedSubgroup B.group), IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U →
      ∃ c : IsClosedImmersion ((groupBaseChange k K).map U.inclusion).hom.hom.left,
        IsUnipotentRadical (Unipotent.baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup B))
          (GeometricRadicals.baseChangedSubgroup K U c)

def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k),
    IsSemisimple G → GeometricallySimplyConnected G → ∀ M : BorelPair G,
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
      (_ : IsGalois k K) (A : AdditiveLine k) (P : PinnedGroup A)
      (D : AttachedDatum P.pair) (lift : Aut D.toBased ≃* Aut P)
      (twist : PinnedTwist K D lift M.positive M.torus) (S : BorelPair P.pair.G),
      S.positive = P.pair.B ∧ S.torus = P.pair.T ∧
      IsSemisimple P.pair.G ∧ corootLattice D = ⊤ ∧ IsBasedLift D lift ∧
      GeometricRadicals.IsSplitTorus ((groupBaseChange k K).obj M.torus.group) ∧
      IsTransportedBasedAction twist ∧
      ∃ cmp : MarkedComparison (K := K) S M,
        MatchesCoordinateComparison cmp twist.groupIso

end

end LinearAlgebraicGroups.Specs.QuasiSplitPinnedPairModel
