import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.UnitaryRankOne
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.QuasiSplitOrbitAmbientWords

open AbstractPairing (Datum Root)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (subgroupRoots)
open CharacterDescent (Cocharacter)
open GeometricBorelConjugacy (IsKBorel subgroupOfSubgroup)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open OrderedRootProducts (RootSubgroupFamily)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)
open Unipotent (baseChangedAlgebraicGroup closedSubgroupAlgebraicGroup)
open UnitaryRankOne

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev SL₂ (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R
abbrev SL₃ (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 3) R

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

abbrev rationalAlgebra (F : Type u) [Field F] : TestAlgebra F := CommAlgCat.of F F

abbrev RationalPoints (G : GroupScheme F) := GroupPoints G (rationalAlgebra F)

abbrev onPoints {G H : GroupScheme F} (f : G ⟶ H) (R : TestAlgebra F) :
    GroupPoints G R →* GroupPoints H R := ((groupPointsFunctor F).map f).app R |>.hom

abbrev onRational {G H : GroupScheme F} (f : G ⟶ H) : RationalPoints G →* RationalPoints H :=
  onPoints f (rationalAlgebra F)

def groundPointIso (F : Type u) [Field F] :
    𝟙_ (SchemeOver F) ≅ (testSpec F).obj (op (rationalAlgebra F)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of F))) (by
    change (𝟙 (Spec (CommRingCat.of F))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id _)

def extendPoint (G : GroupScheme F) (p : RationalPoints G) :
    RationalPoints ((groupBaseChange F K).obj G) :=
  (groundPointIso K).inv ≫
    scalarExtendedRationalPoint K ((groundPointIso F).hom ≫ p)

/-- The two actual rational Borels and their radicals are indexed by the sign.
The positive Borel has index true. -/
structure BorelRadical (G : AffineAlgebraicGroup F) where
  borel : ClosedSubgroup G.val
  isBorel : IsKBorel borel
  radical : ClosedSubgroup borel.group
  isRadical : IsUnipotentRadical (closedSubgroupAlgebraicGroup borel) radical

abbrev BorelRadical.inAmbient {G : AffineAlgebraicGroup F} (B : BorelRadical G) :
    ClosedSubgroup G.val := subgroupOfSubgroup B.borel B.radical

/-- Ground-field scheme data for an embedded derived Levi, with the torus
given by the scheme intersection and the two Borels induced from the ambient pair. -/
structure OrbitLevi (F : Type u) [Field F] where
  G : AffineAlgebraicGroup F
  reductive : IsReductive G
  T : ClosedSubgroup G.val
  maximal : IsGeometricallyMaximal T
  B : Bool → BorelRadical G
  ambientTorus : ∀ s, IsSubgroupOf T (B s).borel
  L : ClosedSubgroup G.val
  deriv : ClosedSubgroup L.group
  isDerived : IsDerivedSubgroup deriv
  S : ClosedSubgroup deriv.group
  torusMap : S.group ⟶ T.group
  intersection : IsPullback torusMap.hom.hom S.inclusion.hom.hom T.inclusion.hom.hom
    (deriv.inclusion ≫ L.inclusion).hom.hom
  Hpair : Bool → BorelRadical (closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup (G := G) L) deriv)
  induced : ∀ (s : Bool) (Y : SchemeOver F) (p : Y ⟶ deriv.group.X),
    p ∈ SubgroupSections (Hpair s).borel Y ↔
      p ≫ (deriv.inclusion ≫ L.inclusion).hom.hom ∈ SubgroupSections (B s).borel Y

abbrev OrbitLevi.H (O : OrbitLevi F) : GroupScheme F := O.deriv.group

abbrev OrbitLevi.inclusion (O : OrbitLevi F) : O.H ⟶ O.G.val :=
  O.deriv.inclusion ≫ O.L.inclusion

abbrev OrbitLevi.radical (O : OrbitLevi F) (s : Bool) : ClosedSubgroup O.G.val :=
  (O.B s).inAmbient

abbrev OrbitLevi.derivedRadical (O : OrbitLevi F) (s : Bool) : ClosedSubgroup O.G.val :=
  subgroupOfSubgroup (subgroupOfSubgroup O.L O.deriv) (O.Hpair s).inAmbient

def OrbitLevi.derivedGenerated (O : OrbitLevi F) : Subgroup (RationalPoints O.H) :=
  Subgroup.closure {p | ∃ s, p ∈ (onRational (O.Hpair s).inAmbient.inclusion).range}

def OrbitLevi.generated (O : OrbitLevi F) : Subgroup (RationalPoints O.G.val) :=
  Subgroup.closure {p | ∃ s, p ∈ (onRational (O.radical s).inclusion).range}

/-- The split Borels and radicals are the scalar extensions of the specified
rational closed subgroups, through the same inclusions. -/
structure SplitRadical (K : Type u) [Field K] [Algebra F K] {G : AffineAlgebraicGroup F}
    (B : BorelRadical G) where
  borelClosed : IsClosedImmersion ((groupBaseChange F K).map B.borel.inclusion).hom.hom.left
  radicalClosed : IsClosedImmersion ((groupBaseChange F K).map B.radical.inclusion).hom.hom.left
  isBorel : IsKBorel (scalarExtendedSubgroup K B.borel borelClosed)
  isRadical : IsUnipotentRadical
    (closedSubgroupAlgebraicGroup (G := baseChangedAlgebraicGroup K G)
      (scalarExtendedSubgroup K B.borel borelClosed))
    (scalarExtendedSubgroup K B.radical radicalClosed)

abbrev SplitRadical.borel {G : AffineAlgebraicGroup F} {B : BorelRadical G}
    (A : SplitRadical K B) := scalarExtendedSubgroup K B.borel A.borelClosed

abbrev SplitRadical.radical {G : AffineAlgebraicGroup F} {B : BorelRadical G}
    (A : SplitRadical K B) := scalarExtendedSubgroup K B.radical A.radicalClosed

/-- The split datum and quotient use the ambient torus. Root comparisons
identify the actual closed subgroup inclusions after scalar extension. -/
structure SplitOrbit (O : OrbitLevi F) (K : Type u) [Field K] [Algebra F K] where
  reductive : IsReductive (baseChangedAlgebraicGroup K O.G)
  hReductive : IsReductive (baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup (G := O.G) O.L) O.deriv))
  tClosed : IsClosedImmersion ((groupBaseChange F K).map O.T.inclusion).hom.hom.left
  sClosed : IsClosedImmersion ((groupBaseChange F K).map O.S.inclusion).hom.hom.left
  tSplit : IsSplitTorus ((groupBaseChange F K).obj O.T.group)
  sSplit : IsSplitTorus ((groupBaseChange F K).obj O.S.group)
  tMax : IsGeometricallyMaximal (scalarExtendedSubgroup K O.T tClosed)
  sMax : IsGeometricallyMaximal (scalarExtendedSubgroup K O.S sClosed)
  ambient : ∀ s, SplitRadical K (O.B s)
  derived : ∀ s, SplitRadical K (O.Hpair s)
  tInBorel : ∀ s, IsSubgroupOf (scalarExtendedSubgroup K O.T tClosed) (ambient s).borel
  sInBorel : ∀ s, IsSubgroupOf (scalarExtendedSubgroup K O.S sClosed) (derived s).borel
  comm : IsCommMonObj (scalarExtendedSubgroup K O.T tClosed).group.X
  D : @Datum K _ (baseChangedAlgebraicGroup K O.G) (scalarExtendedSubgroup K O.T tClosed) comm
  W : @DatumAndWeyl.Identification K _ (baseChangedAlgebraicGroup K O.G)
    (scalarExtendedSubgroup K O.T tClosed) comm D
  positive : Additive (CharacterDescent.Character ((groupBaseChange F K).obj O.T.group)) →ₗ[ℤ] ℤ
  base : D.rootDatum.Base
  based : SimpleRoots.IsBaseFor D.rootDatum positive base
  positive_eq : SimpleRoots.positive D.rootDatum positive =
    subgroupRoots (scalarExtendedSubgroup K O.T tClosed) (ambient true).borel
  negative_eq : {i | positive (D.rootDatum.root i) < 0} =
    subgroupRoots (scalarExtendedSubgroup K O.T tClosed) (ambient false).borel
  face : Set (Root (G := baseChangedAlgebraicGroup K O.G) (scalarExtendedSubgroup K O.T tClosed))
  isFace : face ⊆ base.support
  rootGroups : RootSubgroupFamily (G := baseChangedAlgebraicGroup K O.G)
    (scalarExtendedSubgroup K O.T tClosed)
  derivedRootGroups : RootSubgroupFamily
    (G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup (G := O.G) O.L) O.deriv))
    (scalarExtendedSubgroup K O.S sClosed)
  rootIndex : Root (G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup (G := O.G) O.L) O.deriv)) (scalarExtendedSubgroup K O.S sClosed) ≃
    StandardParabolicLevi.leviRoots D face
  rootSigns : ∀ (s : Bool) (i : Root (G := baseChangedAlgebraicGroup K (closedSubgroupAlgebraicGroup
    (G := closedSubgroupAlgebraicGroup (G := O.G) O.L) O.deriv)) (scalarExtendedSubgroup K O.S sClosed)),
    i ∈ subgroupRoots (scalarExtendedSubgroup K O.S sClosed) (derived s).borel ↔
      (rootIndex i).val ∈ subgroupRoots (scalarExtendedSubgroup K O.T tClosed) (ambient s).borel
  rootMatch : ∀ i, ∃ e : (derivedRootGroups i).val.group ≅ (rootGroups (rootIndex i).val).val.group,
    e.hom ≫ (rootGroups (rootIndex i).val).val.inclusion =
      (derivedRootGroups i).val.inclusion ≫ (groupBaseChange F K).map O.inclusion
  corootLift : face → Cocharacter ((groupBaseChange F K).obj O.S.group)
  corootMatch : ∀ i : face,
    corootLift i ≫ (groupBaseChange F K).map O.torusMap =
      Additive.toMul (D.rootDatum.coroot i.val)

abbrev OrbitLevi.derivedGroup (O : OrbitLevi F) : AffineAlgebraicGroup F :=
  closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup (G := O.G) O.L) O.deriv

abbrev SplitOrbit.T {O : OrbitLevi F} (A : SplitOrbit O K) :
    ClosedSubgroup (baseChangedAlgebraicGroup K O.G).val :=
  scalarExtendedSubgroup K O.T A.tClosed

abbrev SplitOrbit.S {O : OrbitLevi F} (A : SplitOrbit O K) :
    ClosedSubgroup (baseChangedAlgebraicGroup K O.derivedGroup).val :=
  scalarExtendedSubgroup K O.S A.sClosed

abbrev SplitOrbit.rootDatum {O : OrbitLevi F} (A : SplitOrbit O K) :=
  @Datum.rootDatum K _ (baseChangedAlgebraicGroup K O.G) A.T A.comm A.D

/-- The longest element of the face Weyl subgroup is characterized by sending
every positive root of the face subsystem to a negative root. -/
def IsFaceLongest {O : OrbitLevi F} (A : SplitOrbit O K)
    (w : letI : IsCommMonObj A.T.group.X := A.comm; A.rootDatum.weylGroup) : Prop :=
  letI : IsCommMonObj A.T.group.X := A.comm
  w ∈ StandardParabolicLevi.parabolicWeylGroup A.D A.face ∧
  ∀ i ∈ StandardParabolicLevi.leviRoots A.D A.face, 0 < A.positive (A.rootDatum.root i) →
    A.positive (w.val.weightEquiv (A.rootDatum.root i)) < 0

/-- The rank-one words generate the torus points in the derived group and in
the ambient group. The derived group also supplies the rational normalizer
representative whose scalar extension has the given ambient quotient label. -/
def AmbientConclusion (O : OrbitLevi F) (A : SplitOrbit O K) : Prop :=
  letI : IsCommMonObj A.T.group.X := A.comm
  (∀ s, IsSubgroupOf (O.derivedRadical s) (O.radical s)) ∧
  (∀ t : RationalPoints O.S.group,
    onRational O.S.inclusion t ∈ O.derivedGenerated ∧
    onRational (O.torusMap ≫ O.T.inclusion) t ∈ O.generated) ∧
  ∃ (x : RationalPoints O.H) (w : A.rootDatum.weylGroup)
    (n : RationalPoints A.W.normalizer.group),
    let g := onRational O.inclusion x
    x ∈ O.derivedGenerated ∧ g ∈ O.generated ∧
    Normalizes O.T.inclusion g ∧ IsFaceLongest A w ∧
    onRational A.W.normalizer.inclusion n = extendPoint (K := K) O.G.val g ∧
    onRational A.W.quotient n =
      toUnit _ ≫ A.W.image.constantGroup.sectionPoint (A.W.labelEquiv w)

open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- Evaluate the split markings on the splitting field. The standard upper and
lower transvections parametrize the two actual absolute root subgroups there.
The product `splitWord t * splitWord (-1)` is the standard diagonal
`diag(t, t⁻¹)`, whose marked image is the attached ambient coroot at `t`. -/
structure RootBlockMark {O : OrbitLevi F} (A : SplitOrbit O K) (i : A.face)
    (block : SL₂ K →* RationalPoints ((groupBaseChange F K).obj O.G.val)) : Prop where
  opposite : ∃ j : Root (G := baseChangedAlgebraicGroup K O.G) (scalarExtendedSubgroup K O.T A.tClosed),
    j.val = i.val.val⁻¹ ∧
    (∀ p : RationalPoints (A.rootGroups i.val).val.group,
      ∃ a : K, block (splitUpper a) = onRational (A.rootGroups i.val).val.inclusion p) ∧
    (∀ p : RationalPoints (A.rootGroups j).val.group,
      ∃ a : K, block (splitLower a) = onRational (A.rootGroups j).val.inclusion p)
  coroot : letI : IsCommMonObj A.T.group.X := A.comm
    ∀ t : Kˣ,
    block (splitWord t * splitWord (-1)) =
      cocharacterPoint (Additive.toMul (A.rootDatum.coroot i.val))
        (rationalAlgebra K) t ≫ ((groupBaseChange F K).map O.T.inclusion).hom.hom

/-- The two rank-one blocks of SL₃ are inserted in coordinates (0,1) and (1,2). -/
def adjacentBlock (R : Type u) [CommRing R] (i : Fin 2) : SL₂ R →* SL₃ R := by
  let b (x : SL₂ R) : Matrix (Fin 3) (Fin 3) R :=
    if i = 0 then !![x.val 0 0, x.val 0 1, 0; x.val 1 0, x.val 1 1, 0; 0, 0, 1]
    else !![1, 0, 0; 0, x.val 0 0, x.val 0 1; 0, x.val 1 0, x.val 1 1]
  have h (x : SL₂ R) : (b x).det = 1 := by
    have hx := x.prop
    rw [Matrix.det_fin_two] at hx
    by_cases hi : i = 0 <;> simp [b, hi, Matrix.det_fin_three, hx]
  refine { toFun := fun x ↦ ⟨b x, h x⟩, map_one' := ?_, map_mul' := ?_ }
  · apply Subtype.ext
    change b 1 = 1
    ext a c
    fin_cases a <;> fin_cases c <;> by_cases hi : i = 0 <;> simp [b, hi]
  · intro x y
    apply Subtype.ext
    change b (x * y) = b x * b y
    have hm : (x * y).val = x.val * y.val := rfl
    ext a c
    fin_cases a <;> fin_cases c <;>
      by_cases hi : i = 0 <;>
      simp [b, hi, hm, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

def orthogonalBlock (K : Type u) [Field K] (I : Type u) (i : I) :
    SL₂ K →* (I → SL₂ K) := by
  classical
  refine { toFun := fun x ↦ Pi.mulSingle (M := fun _ : I ↦ SL₂ K) i x, map_one' := ?_, map_mul' := ?_ }
  · exact Pi.mulSingle_one i
  · intro a b
    funext j
    change Pi.mulSingle (M := fun _ : I ↦ SL₂ K) i (a * b) j =
      Pi.mulSingle (M := fun _ : I ↦ SL₂ K) i a j * Pi.mulSingle (M := fun _ : I ↦ SL₂ K) i b j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]

/-- Evaluate the marked Weil restriction isomorphism at the ground and
splitting fields. For an embedding `e`, the split factor comes from the
projection of the scalar algebra sending `a ⊗ b` to `a * e b`.
The torus, the two radicals and the single-factor root blocks inherit their
markings from the corresponding scheme inclusions. -/
structure OrthogonalModel {O : OrbitLevi F} (A : SplitOrbit O K)
    (E : Type u) [Field E] [Algebra F E] where
  indices : (E →ₐ[F] K) ≃ A.face
  pairings : letI : IsCommMonObj A.T.group.X := A.comm
    ∀ i j : A.face, i ≠ j → A.rootDatum.pairing i.val j.val = 0
  ground : RationalPoints O.H ≃* SL₂ E
  split : RationalPoints ((groupBaseChange F K).obj O.H) ≃* ((E →ₐ[F] K) → SL₂ K)
  scalar : ∀ g e, split (extendPoint (K := K) O.H g) e =
    Matrix.SpecialLinearGroup.map e.toRingHom (ground g)
  torus : ∀ t : RationalPoints O.S.group,
    ∃ b : Eˣ, (ground (onRational O.S.inclusion t)).val =
      Matrix.diagonal ![(b : E), (↑b⁻¹ : E)]
  upper : ∀ x : E, ground.symm (splitUpper x) ∈
    (onRational (O.Hpair true).inAmbient.inclusion).range
  lower : ∀ x : E, ground.symm (splitLower x) ∈
    (onRational (O.Hpair false).inAmbient.inclusion).range
  blocks : ∀ i : E →ₐ[F] K,
    RootBlockMark A (indices i)
      ((onRational ((groupBaseChange F K).map O.inclusion)).comp
        (split.symm.toMonoidHom.comp (orthogonalBlock K _ i)))

/-- Evaluate the marked special unitary isomorphism for the antidiagonal
Hermitian form with entries 1. The chosen embedding gives the projection to
one factor of the split quadratic scalar algebra. The Hermitian equations
determine the second factor from the first. In the first factor the two
marked simple roots use the consecutive coordinate blocks of `SL₃`. -/
structure AdjacentModel {O : OrbitLevi F} (A : SplitOrbit O K)
    (E : Type u) [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] where
  embedding : E →ₐ[F] K
  indices : Fin 2 ≃ A.face
  pairings : letI : IsCommMonObj A.T.group.X := A.comm
    ∀ i j : Fin 2, i ≠ j →
    A.rootDatum.pairing (indices i).val (indices j).val = -1
  matrices : Subgroup (SL₃ E)
  isUnitary : ∀ g : SL₃ E, g ∈ matrices ↔ PreservesForm (quadraticConjugation F E) 1 g.val
  ground : RationalPoints O.H ≃* matrices
  split : RationalPoints ((groupBaseChange F K).obj O.H) ≃* SL₃ K
  scalar : ∀ g, split (extendPoint (K := K) O.H g) =
    Matrix.SpecialLinearGroup.map embedding.toRingHom (ground g).val
  torus : ∀ t : RationalPoints O.S.group,
    ∃ d : Fin 3 → E, (ground (onRational O.S.inclusion t)).val.val = Matrix.diagonal d
  upper : ∀ g : matrices,
    (∃ a b, g.val.val = UnitaryRankOne.upper (quadraticConjugation F E) 1 a b) →
    ground.symm g ∈ (onRational (O.Hpair true).inAmbient.inclusion).range
  lower : ∀ g : matrices,
    (∃ a b, g.val.val = UnitaryRankOne.lower (quadraticConjugation F E) 1 a b) →
    ground.symm g ∈ (onRational (O.Hpair false).inAmbient.inclusion).range
  blocks : ∀ i : Fin 2, RootBlockMark A (indices i)
    ((onRational ((groupBaseChange F K).map O.inclusion)).comp
      (split.symm.toMonoidHom.comp (adjacentBlock K i)))

def RadicalInclusions : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    (O : OrbitLevi F) (_A : SplitOrbit O K), ∀ s,
      IsSubgroupOf (O.derivedRadical s) (O.radical s)

def OrthogonalWords : Prop :=
  ∀ {F K E : Type u} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    [Infinite F] [FiniteDimensional F K] [IsGalois F K]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (O : OrbitLevi F) (A : SplitOrbit O K), OrthogonalModel A E → AmbientConclusion O A

def AdjacentWords : Prop :=
  ∀ {F K E : Type u} [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E]
    [Infinite F] [FiniteDimensional F K] [IsGalois F K]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (O : OrbitLevi F) (A : SplitOrbit O K), AdjacentModel A E → AmbientConclusion O A

end

end LinearAlgebraicGroups.Specs.QuasiSplitOrbitAmbientWords
