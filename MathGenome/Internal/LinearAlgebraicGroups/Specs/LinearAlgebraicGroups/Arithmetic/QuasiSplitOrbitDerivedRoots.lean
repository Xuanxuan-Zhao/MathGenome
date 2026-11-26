import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.CentralDerived
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitOrbitDerivedRoots

open AbstractPairing (Root Datum)
open CharacterDescent (Character Cocharacter)
open GeometricBorelConjugacy (subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus)
open Pinning (AttachedDatum SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open RootGroups (IsRootSubgroup)
open StandardParabolicLevi (IsCommonKernelTorus leviRoots)
open SubtorusCentralizer (IsCentralizer)
open SchemeDerivedGroup (IsDerivedSubgroup)
open Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section
variable {k : Type u} [Field k] {P : SplitBorelPair k}

/-- The split standard Levi and its derived group with the intersection
of the derived group and the specified ambient maximal torus. -/
structure SplitFace (D : AttachedDatum P) (I : Set (Root P.T)) where
  simple : letI := D.comm; I ⊆ D.base.support
  kernelTorus : ClosedSubgroup P.T.group
  kernel : IsCommonKernelTorus I kernelTorus
  levi : ClosedSubgroup P.G.val
  centralizer : IsCentralizer (subgroupOfSubgroup P.T kernelTorus) levi
  reductive : IsReductive (closedSubgroupAlgebraicGroup levi)
  leviTorus : ClosedSubgroup levi.group
  torusIso : P.T.group ≅ leviTorus.group
  torusInclusion : torusIso.hom ≫ leviTorus.inclusion ≫ levi.inclusion = P.T.inclusion
  leviTorusMaximal : IsGeometricallyMaximal leviTorus
  leviRoots_eq : letI := D.comm
    CharacterPairing.absoluteRoots leviTorus =
      (fun α : Root P.T => torusIso.inv ≫ α.val) '' leviRoots D.datum I
  derived : ClosedSubgroup levi.group
  isDerived : IsDerivedSubgroup derived
  torus : ClosedSubgroup derived.group
  toAmbientTorus : torus.group ⟶ P.T.group
  intersection : IsPullback toAmbientTorus torus.inclusion P.T.inclusion
    (derived.inclusion ≫ levi.inclusion)
  torusSplit : IsSplitTorus torus.group
  torusMaximal : IsGeometricallyMaximal torus

abbrev SplitFace.group {D : AttachedDatum P} {I : Set (Root P.T)} (S : SplitFace D I) :
    AffineAlgebraicGroup k :=
  closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup S.levi) S.derived

abbrev SplitFace.inclusion {D : AttachedDatum P} {I : Set (Root P.T)} (S : SplitFace D I) :
    S.group.val ⟶ P.G.val :=
  S.derived.inclusion ≫ S.levi.inclusion

/-- Every ambient face coroot lifts to the given scheme intersection. -/
def FaceCorootFactors : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ α ∈ leviRoots D.datum I, ∃ c : Cocharacter S.torus.group,
      c ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot α).toMul

/-- Every ambient root subgroup of the face factors through the actual
derived Levi. -/
def FaceRootSubgroupsFactor : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ α ∈ leviRoots D.datum I, ∀ U : ClosedSubgroup P.G.val,
      IsRootSubgroup P.T U α.val →
      ∃ j : U.group ⟶ S.group.val, j ≫ S.inclusion = U.inclusion

/-- Restriction distinguishes the ambient roots in the face. -/
def FaceRootRestrictionInjective : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    Set.InjOn (fun α : Root P.T => S.toAmbientTorus ≫ α.val) (leviRoots D.datum I)

/-- Restriction of an ambient face root gives an actual root of the derived
group and identifies its root subgroup via the given embedding. -/
def FaceRootRestrictions : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ α ∈ leviRoots D.datum I,
      let β := S.toAmbientTorus ≫ α.val
      β ∈ CharacterPairing.absoluteRoots S.torus ∧
      ∀ U : ClosedSubgroup P.G.val, IsRootSubgroup P.T U α.val →
        ∃ V : ClosedSubgroup S.group.val, IsRootSubgroup S.torus V β ∧
          ∃ e : V.group ≅ U.group, e.hom ≫ U.inclusion = V.inclusion ≫ S.inclusion

/-- There are no additional roots of the actual derived group. -/
def FaceRootRestrictionSurjective : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    Set.SurjOn (fun α : Root P.T => S.toAmbientTorus ≫ α.val) (leviRoots D.datum I)
      (CharacterPairing.absoluteRoots S.torus)

/-- The lifts are the coroots attached by the rank-one construction in
the actual derived group. -/
def FaceAttachedCoroots : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ α ∈ leviRoots D.datum I, ∀ (hβ : S.toAmbientTorus ≫ α.val ∈
        CharacterPairing.absoluteRoots S.torus) (c : Cocharacter S.torus.group),
      AbstractPairing.IsAttachedCoroot (G := S.group) S.torus ⟨S.toAmbientTorus ≫ α.val, hβ⟩ c →
      c ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot α).toMul

/-- The exact integral image in the ambient coroot lattice implies
geometric simple connectedness of the actual derived Levi. -/
def SplitDerivedSimplyConnected : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    (∀ y : D.toBased.Y, (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
      y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)) →
    SimplyConnectedLattice.GeometricallySimplyConnected S.group

/-- An actual marked additive coordinate on a face root subgroup transports
over the same additive line to the derived root subgroup. -/
def FacePinCoordinates : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ α ∈ leviRoots D.datum I, ∀ (U : ClosedSubgroup P.G.val) (A : RootGroups.AdditiveLine k),
      IsRootSubgroup P.T U α.val → ∀ x : Pinning.RootCoordinate A P.T U α.val,
      ∃ (V : ClosedSubgroup S.group.val) (y : Pinning.RootCoordinate A S.torus V
          (S.toAmbientTorus ≫ α.val)),
        IsRootSubgroup S.torus V (S.toAmbientTorus ≫ α.val) ∧
        y.val.hom ≫ V.inclusion ≫ S.inclusion = x.val.hom ≫ U.inclusion

/-- The signs on the derived group are induced by the actual scheme
intersections with the corresponding ambient Borels. -/
def FaceBorelRoots : Prop :=
  ∀ {k : Type u} [Field k] {P : SplitBorelPair k} (D : AttachedDatum P)
    (I : Set (Root P.T)) (S : SplitFace D I),
    letI := D.comm
    ∀ (B : ClosedSubgroup P.G.val) (B' : ClosedSubgroup S.group.val)
      (j : B'.group ⟶ B.group), IsPullback j B'.inclusion B.inclusion S.inclusion →
      ∀ α ∈ leviRoots D.datum I, ∀ (hβ : S.toAmbientTorus ≫ α.val ∈
        CharacterPairing.absoluteRoots S.torus),
        (⟨S.toAmbientTorus ≫ α.val, hβ⟩ : Root (G := S.group) S.torus) ∈
          BorelsAndChambers.subgroupRoots S.torus B' ↔
        α ∈ BorelsAndChambers.subgroupRoots P.T B

section Descent

open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsTorus)
open Pinning (PinnedGroup SimpleRoot IsSimple)
open RootGroups (AdditiveLine)
open SchemeDerivedGroup (IsSubgroupOf)
open SimplyConnectedLattice (GeometricallySimplyConnected)

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {P : SplitBorelPair K} {D : AttachedDatum P} {I : Set (Root P.T)}

/-- An actual rational Levi and its derived-group intersection, with
specified comparisons to the split standard Levi and its embedded groups. -/
structure RationalFace (F : Type u) [Field F] [Algebra F K] (S : SplitFace D I) where
  ambient : AffineAlgebraicGroup F
  ambientReductive : IsReductive ambient
  ambientTorus : ClosedSubgroup ambient.val
  ambientTorusIsTorus : IsTorus ambientTorus.group
  ambientTorusMaximal : IsGeometricallyMaximal ambientTorus
  positive : ClosedSubgroup ambient.val
  negative : ClosedSubgroup ambient.val
  positiveBorel : IsKBorel positive
  negativeBorel : IsKBorel negative
  positiveTorus : ambientTorus.group ⟶ positive.group
  negativeTorus : ambientTorus.group ⟶ negative.group
  opposite : IsPullback positiveTorus negativeTorus positive.inclusion negative.inclusion
  positiveTorusSquare : positiveTorus ≫ positive.inclusion = ambientTorus.inclusion
  levi : ClosedSubgroup ambient.val
  leviReductive : IsReductive (closedSubgroupAlgebraicGroup levi)
  derived : ClosedSubgroup levi.group
  isDerived : IsDerivedSubgroup derived
  torus : ClosedSubgroup derived.group
  toAmbientTorus : torus.group ⟶ ambientTorus.group
  intersection : IsPullback toAmbientTorus torus.inclusion ambientTorus.inclusion
    (derived.inclusion ≫ levi.inclusion)
  torusIsTorus : IsTorus torus.group
  torusMaximal : IsGeometricallyMaximal torus
  groupComparison : (groupBaseChange F K).obj ambient.val ≅ P.G.val
  ambientTorusComparison : (groupBaseChange F K).obj ambientTorus.group ≅ P.T.group
  ambientTorusSquare : ambientTorusComparison.hom ≫ P.T.inclusion =
    (groupBaseChange F K).map ambientTorus.inclusion ≫ groupComparison.hom
  positiveComparison : (groupBaseChange F K).obj positive.group ≅ P.B.group
  positiveSquare : positiveComparison.hom ≫ P.B.inclusion =
    (groupBaseChange F K).map positive.inclusion ≫ groupComparison.hom
  leviComparison : (groupBaseChange F K).obj levi.group ≅ S.levi.group
  leviSquare : leviComparison.hom ≫ S.levi.inclusion =
    (groupBaseChange F K).map levi.inclusion ≫ groupComparison.hom
  derivedComparison : (groupBaseChange F K).obj derived.group ≅ S.group.val
  derivedSquare : derivedComparison.hom ≫ S.derived.inclusion =
    (groupBaseChange F K).map derived.inclusion ≫ leviComparison.hom
  torusComparison : (groupBaseChange F K).obj torus.group ≅ S.torus.group
  torusSquare : torusComparison.hom ≫ S.torus.inclusion =
    (groupBaseChange F K).map torus.inclusion ≫ derivedComparison.hom
  torusMapSquare : torusComparison.hom ≫ S.toAmbientTorus =
    (groupBaseChange F K).map toAmbientTorus ≫ ambientTorusComparison.hom
  integralImage : letI := D.comm
    ∀ y : D.toBased.Y,
      (∃ c : Cocharacter S.torus.group, c ≫ S.toAmbientTorus = y.toMul) ↔
        y ∈ Submodule.span ℤ (D.datum.rootDatum.coroot '' I)

abbrev RationalFace.group {S : SplitFace D I} (R : RationalFace F S) : AffineAlgebraicGroup F :=
  closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup R.levi) R.derived

abbrev RationalFace.inclusion {S : SplitFace D I} (R : RationalFace F S) :
    R.group.val ⟶ R.ambient.val := R.derived.inclusion ≫ R.levi.inclusion

/-- The actual rational derived Levi is geometrically simply connected. -/
def RationalDerivedSimplyConnected : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {P : SplitBorelPair K} (D : AttachedDatum P) (I : Set (Root P.T)) (S : SplitFace D I)
    (R : RationalFace F S), GeometricallySimplyConnected R.group

/-- Pullback along a field automorphism on the scalar extension of a group
defined over the ground field. -/
def coefficientAction (σ : Gal(K/F)) (X : GroupScheme F) :
    pullback X.X.hom (fieldSpecMap F K) ⟶ pullback X.X.hom (fieldSpecMap F K) :=
  pullback.lift (pullback.fst X.X.hom (fieldSpecMap F K))
    (pullback.snd X.X.hom (fieldSpecMap F K) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
      have h : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ fieldSpecMap F K =
          fieldSpecMap F K := by
        rw [← Spec.map_comp]
        congr 1
        ext x
        exact σ.commutes x
      rw [Category.assoc, h, pullback.condition])

/-- The coefficient action expressed on the specified split scheme. -/
def comparedAction (σ : Gal(K/F)) {X : GroupScheme F} {Y : GroupScheme K}
    (e : (groupBaseChange F K).obj X ≅ Y) : Y.X.left ⟶ Y.X.left :=
  e.inv.hom.hom.left ≫ coefficientAction σ X ≫ e.hom.hom.hom.left

abbrev multiplicativeLine (k : Type u) [Field k] : GroupScheme k :=
  specGroup (DiagonalizableGroups.groupAlgebra k DiagonalizableGroups.IntegerCharacters)

abbrev diagramRoot (ω : Gal(K/F) →* Aut D.toBased) (σ : Gal(K/F)) (α : Root P.T) :
    Root P.T :=
  (ω σ).asIso.hom.val.indexEquiv α

def diagramSimple (ω : Gal(K/F) →* Aut D.toBased) (σ : Gal(K/F)) (α : SimpleRoot P) :
    SimpleRoot P := by
  letI := D.comm
  refine ⟨diagramRoot ω σ α.val, (D.simple_iff _).mp ?_⟩
  have h : diagramRoot ω σ α.val ∈
      (ω σ).asIso.hom.val.indexEquiv '' (D.toBased.base.support : Set D.toBased.I) :=
    ⟨α.val, (D.simple_iff _).mpr α.property, rfl⟩
  rw [(ω σ).asIso.hom.property] at h
  exact h

/-- Compatibility of the stated diagram action and pinning with the actual
coefficient action of the rational group. -/
structure ActualPinnedAction {S : SplitFace D I} (R : RationalFace F S)
    (A₀ : AdditiveLine F) (A : AdditiveLine K)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : (groupBaseChange F K).obj (multiplicativeLine F) ≅ multiplicativeLine K)
    (U : OrderedRootProducts.RootSubgroupFamily P.T) (p : Pinning.Pinning A P U)
    (ω : Gal(K/F) →* Aut D.toBased) : Prop where
  stable : ∀ (σ : Gal(K/F)) (α : Root P.T), diagramRoot ω σ α ∈ I ↔ α ∈ I
  characters : ∀ (σ : Gal(K/F)) (α : Root P.T),
    comparedAction σ⁻¹ R.ambientTorusComparison ≫ (diagramRoot ω σ α).val.hom.hom.left =
      α.val.hom.hom.left ≫ comparedAction σ⁻¹ m
  cocharacters : letI := D.comm
    ∀ (σ : Gal(K/F)) (α : Root P.T),
      comparedAction σ⁻¹ m ≫ (D.datum.rootDatum.coroot (diagramRoot ω σ α)).toMul.hom.hom.left =
        (D.datum.rootDatum.coroot α).toMul.hom.hom.left ≫ comparedAction σ⁻¹ R.ambientTorusComparison
  pinning : ∀ (σ : Gal(K/F)) (α : SimpleRoot P),
    let β := diagramSimple ω σ α
    comparedAction σ⁻¹ a ≫
      ((p β).val.hom ≫ (U β.val).val.inclusion).hom.hom.left =
      ((p α).val.hom ≫ (U α.val).val.inclusion).hom.hom.left ≫
        comparedAction σ⁻¹ R.groupComparison

/-- The actual coefficient action on the derived group respects the
restricted root characters and lifted coroots. It also respects any two
marked maps whose ambient images are the prescribed coordinates. -/
def RationalRootMarkAction : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {A₀ : AdditiveLine F} {A : AdditiveLine K} (Q : PinnedGroup A)
    (D : AttachedDatum Q.pair) (I : Set (Root Q.pair.T)) (S : SplitFace D I)
    (R : RationalFace F S)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : (groupBaseChange F K).obj (multiplicativeLine F) ≅ multiplicativeLine K)
    (ω : Gal(K/F) →* Aut D.toBased),
    ActualPinnedAction R A₀ A a m Q.roots Q.pin ω →
    letI := D.comm
    ∀ (σ : Gal(K/F)) (α : Root Q.pair.T),
      let β := diagramRoot ω σ α
      (comparedAction σ⁻¹ R.torusComparison ≫ (S.toAmbientTorus ≫ β.val).hom.hom.left =
        (S.toAmbientTorus ≫ α.val).hom.hom.left ≫ comparedAction σ⁻¹ m) ∧
      (∀ (c d : Cocharacter S.torus.group),
        c ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot α).toMul →
        d ≫ S.toAmbientTorus = (D.datum.rootDatum.coroot β).toMul →
        comparedAction σ⁻¹ m ≫ d.hom.hom.left =
          c.hom.hom.left ≫ comparedAction σ⁻¹ R.torusComparison) ∧
      ∀ (i : SimpleRoot Q.pair) (x y : A.group ⟶ S.group.val),
        i.val = α →
        x ≫ S.inclusion = (Q.pin i).val.hom ≫ (Q.roots i.val).val.inclusion →
        y ≫ S.inclusion =
          (Q.pin (diagramSimple ω σ i)).val.hom ≫ (Q.roots (diagramSimple ω σ i).val).val.inclusion →
        comparedAction σ⁻¹ a ≫ y.hom.hom.left =
          x.hom.hom.left ≫ comparedAction σ⁻¹ R.derivedComparison

/-- An actual rational Borel of the derived group and its comparison to a
Borel through the specified split maximal torus. -/
structure InducedBorel {S : SplitFace D I} (R : RationalFace F S)
    (B : ClosedSubgroup R.ambient.val) where
  rational : ClosedSubgroup R.group.val
  toAmbient : rational.group ⟶ B.group
  intersection : IsPullback toAmbient rational.inclusion B.inclusion R.inclusion
  isKBorel : IsKBorel rational
  split : ClosedSubgroup S.group.val
  splitBorel : IsKBorel split
  containsTorus : IsSubgroupOf S.torus split
  comparison : (groupBaseChange F K).obj rational.group ≅ split.group
  square : comparison.hom ≫ split.inclusion =
    (groupBaseChange F K).map rational.inclusion ≫ R.derivedComparison.hom

def InducedBorel.pair {S : SplitFace D I} {R : RationalFace F S}
    {B : ClosedSubgroup R.ambient.val} (Q : InducedBorel R B)
    (h : IsReductive S.group) : SplitBorelPair K where
  G := S.group
  reductive := h
  T := S.torus
  split := S.torusSplit
  maximal := S.torusMaximal
  B := Q.split
  borel := Q.splitBorel
  containsTorus := Q.containsTorus

/-- The pinned coordinate as a map into the split group. -/
abbrev pinnedRootMap {P : SplitBorelPair K} {A : AdditiveLine K}
    {U : OrderedRootProducts.RootSubgroupFamily P.T}
    (p : Pinning.Pinning A P U) (j : SimpleRoot P) : A.group ⟶ P.G.val :=
  (p j).val.hom ≫ (U j.val).val.inclusion

/-- Comparison of the derived standard Levi and the stable split face for the
given rational inclusions, Borels, and pinned action. -/
def RationalDerivedRootComparison : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {A₀ : AdditiveLine F} {A : AdditiveLine K} (Q : PinnedGroup A)
    (D : AttachedDatum Q.pair) (I : Set (Root Q.pair.T)) (S : SplitFace D I)
    (R : RationalFace F S)
    (a : (groupBaseChange F K).obj A₀.group ≅ A.group)
    (m : (groupBaseChange F K).obj (multiplicativeLine F) ≅ multiplicativeLine K)
    (ω : Gal(K/F) →* Aut D.toBased),
    ActualPinnedAction R A₀ A a m Q.roots Q.pin ω →
    letI := D.comm
    ∃ (h : IsReductive S.group) (Bp : InducedBorel R R.positive)
      (Bn : InducedBorel R R.negative)
      (E : AttachedDatum (Bp.pair h)) (En : AttachedDatum (Bn.pair h))
      (e : ↥(leviRoots D.datum I) ≃ Root (G := S.group) S.torus),
      letI := E.comm
      letI := En.comm
      (∃ (ip : R.torus.group ⟶ Bp.rational.group) (in' : R.torus.group ⟶ Bn.rational.group),
        IsPullback ip in' Bp.rational.inclusion Bn.rational.inclusion ∧
        ip ≫ Bp.rational.inclusion = R.torus.inclusion) ∧
      GeometricallySimplyConnected R.group ∧
      (∀ (σ : Gal(K/F)) (α : ↥(leviRoots D.datum I)),
        diagramRoot ω σ α.val ∈ leviRoots D.datum I) ∧
      (∀ α, (e α).val = S.toAmbientTorus ≫ α.val.val ∧
        (E.datum.rootDatum.coroot (e α)).toMul ≫ S.toAmbientTorus =
          (D.datum.rootDatum.coroot α.val).toMul ∧
        ((e α) ∈ E.base.support ↔ α.val ∈ I) ∧
        ((e α) ∈ En.base.support ↔ ∃ δ ∈ I, α.val.val = δ.val⁻¹) ∧
        ∀ U : ClosedSubgroup Q.pair.G.val, IsRootSubgroup Q.pair.T U α.val.val →
          ∃ V : ClosedSubgroup S.group.val, IsRootSubgroup S.torus V (e α).val ∧
            ∃ r : V.group ≅ U.group, r.hom ≫ U.inclusion = V.inclusion ≫ S.inclusion) ∧
      ∃ (U : OrderedRootProducts.RootSubgroupFamily (Bp.pair h).T)
        (p : Pinning.Pinning A (Bp.pair h) U),
        (∀ (α : ↥(leviRoots D.datum I)) (i : SimpleRoot Q.pair)
            (j : SimpleRoot (Bp.pair h)), i.val = α.val → j.val = e α →
          pinnedRootMap p j ≫ S.inclusion = pinnedRootMap Q.pin i) ∧
        (∀ (σ : Gal(K/F)) (α α' : ↥(leviRoots D.datum I)),
          α'.val = diagramRoot ω σ α.val →
          comparedAction σ⁻¹ R.torusComparison ≫ (e α').val.hom.hom.left =
            (e α).val.hom.hom.left ≫ comparedAction σ⁻¹ m ∧
          comparedAction σ⁻¹ m ≫ (E.datum.rootDatum.coroot (e α')).toMul.hom.hom.left =
            (E.datum.rootDatum.coroot (e α)).toMul.hom.hom.left ≫
              comparedAction σ⁻¹ R.torusComparison ∧
          ∀ (i : SimpleRoot Q.pair) (j j' : SimpleRoot (Bp.pair h)),
            i.val = α.val → j.val = e α → j'.val = e α' →
            comparedAction σ⁻¹ a ≫ (pinnedRootMap p j').hom.hom.left =
              (pinnedRootMap p j).hom.hom.left ≫
                comparedAction σ⁻¹ R.derivedComparison)

end Descent

end
end LinearAlgebraicGroups.Specs.QuasiSplitOrbitDerivedRoots
