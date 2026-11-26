import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralSmoothness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinWeights

namespace LinearAlgebraicGroups.Albert.SplitFrameTorusSpecification

open AlgebraicGeometry CategoryTheory Opposite
open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open LinearAlgebraicGroups.Specs.SpinWeights
open SplitSpinSpecification TrialitySpecification IntegralSmoothnessSpecification
open ShortDirectionSpecification (IntegralPresentation)
open FrameSpecification (frameAxis)
open scoped CategoryTheory.MonObj MonoidAlgebra

noncomputable section

abbrev ScalarTest := CommAlgCat.{0} ℤ
abbrev scalarSpec := algSpec (CommRingCat.of ℤ)
abbrev IntegralGroup := SpinSpecification.GroupScheme ℤ
abbrev ScalarPoints (G : IntegralGroup) := SpinSpecification.SchemePoints G

abbrev CharacterGroup := Multiplicative CharacterExponents
abbrev LaurentRing := MonoidAlgebra ℤ CharacterGroup

/-- The split torus with the free character coordinates `(u,a₁,a₂,a₃)`. -/
abbrev diagonalTorus : IntegralGroup :=
  (hopfSpec (CommRingCat.of ℤ)).obj (op (CommHopfAlgCat.of ℤ LaurentRing))

def vectorWeight : PairIndex 4 → CharacterExponents :=
  Sum.elim epsilon (fun i => -epsilon i)

abbrev WedgeIndex (p : Bool) := {I : Finset (Fin 4) // I.card % 2 = p.toNat}

def halfSpinBlock (p : Bool) : Fin 3 := if p then 2 else 0

/-- The integral spin lift, marked by its vector action and by its scalar
on every wedge including the empty wedge. -/
def IsDiagonalCliffordLift
    (l : ∀ S : ScalarTest, DiagonalPoints S →* (ScalarClifford 4 S)ˣ) : Prop :=
    (∀ S, Function.Injective (l S)) ∧
    (∀ {S T : ScalarTest} (f : S ⟶ T) (t : DiagonalPoints S),
      l T (mapDiagonal f.hom.toRingHom t) =
        Units.map (SpinSpecification.coefficientMap (integralForm 4) S f.hom).toMonoidHom (l S t)) ∧
    ∀ S : ScalarTest, ∃ E : ScalarClifford 4 S ≃ₐ[S] Module.End S (ExteriorSpace S),
      IsExteriorModel E ∧ ∀ t : DiagonalPoints S,
        l S t ∈ SpinSpecification.spinUnits (integralForm 4) S ∧
        HasActionMatrix 4 (l S t) (middle (diagonalBlock t)) ∧
        ∀ I : Finset (Fin 4),
          E (l S t) ((Pi.basisFun S (Fin 4)).ExteriorAlgebra I) =
            (Additive.toMul (evaluate t (exteriorWeight I)) : Sˣ).val •
              (Pi.basisFun S (Fin 4)).ExteriorAlgebra I

def CliffordLift : Prop := ∃ l, IsDiagonalCliffordLift l

def monomial (x : CharacterExponents) : LaurentRing :=
  MonoidAlgebra.of ℤ CharacterGroup (Multiplicative.ofAdd x)

def TorusCoordinates : Prop :=
  ∃ d : ∀ S : ScalarTest, ScalarPoints diagonalTorus S ≃* DiagonalPoints S,
    (∀ {S T : ScalarTest} (f : S ⟶ T) (t : ScalarPoints diagonalTorus S),
      d T (scalarSpec.map f.op ≫ t) = mapDiagonal f.hom.toRingHom (d S t)) ∧
    ∀ (S : ScalarTest) (f : LaurentRing →ₐ[ℤ] S) (x : CharacterExponents),
      (Additive.toMul (evaluate (d S (scalarSpec.map (CommAlgCat.ofHom f).op)) x) : Sˣ).val =
        f (monomial x)

/-- A genuine marking of the torus inside the same represented Albert group. -/
structure FrameTorus {P : IntegralPresentation} (G : SplitGroup P) where
  inclusion : diagonalTorus ⟶ G.group
  closed : IsClosedImmersion inclusion.hom.hom.left
  points : ∀ S : ScalarTest, ScalarPoints diagonalTorus S ≃* DiagonalPoints S
  natural : ∀ {S T : ScalarTest} (f : S ⟶ T) (t : ScalarPoints diagonalTorus S),
    points T (scalarSpec.map f.op ≫ t) = mapDiagonal f.hom.toRingHom (points S t)
  characters : ∀ (S : ScalarTest) (f : LaurentRing →ₐ[ℤ] S) (x : CharacterExponents),
    (Additive.toMul (evaluate (points S (scalarSpec.map (CommAlgCat.ofHom f).op)) x) : Sˣ).val =
      f (monomial x)
  vectorBasis : ∀ S : ScalarTest, Module.Basis (PairIndex 4) S (Composition.Zorn S)
  halfBasis : ∀ (S : ScalarTest) (p : Bool), Module.Basis (WedgeIndex p) S (Composition.Zorn S)
  vectorNatural : ∀ {S T : ScalarTest} (f : S ⟶ T) (j : PairIndex 4),
    Composition.ZornSpecification.mapCoordinates f.hom.toRingHom (vectorBasis S j) = vectorBasis T j
  halfNatural : ∀ {S T : ScalarTest} (f : S ⟶ T) (p : Bool) (j : WedgeIndex p),
    Composition.ZornSpecification.mapCoordinates f.hom.toRingHom (halfBasis S p j) = halfBasis T p j
  blockAction : ∀ (S : ScalarTest) (t : ScalarPoints diagonalTorus S),
    ∃ h : relatedTriples (R := S),
      (∀ x, G.action S (t ≫ inclusion.hom.hom) x = (x.1, fun i => h.val i (x.2 i))) ∧
      (∀ j, h.val 1 (vectorBasis S j) =
        (Additive.toMul (evaluate (points S t) (vectorWeight j)) : Sˣ).val • vectorBasis S j) ∧
      ∀ p i, h.val (halfSpinBlock p) (halfBasis S p i) =
        (Additive.toMul (evaluate (points S t) (exteriorWeight i.val)) : Sˣ).val • halfBasis S p i

def FrameTorus.Centralizes {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    {S : ScalarTest} (g : ScalarPoints G.group S) : Prop :=
  ∀ (A : ScalarTest) (f : S ⟶ A) (t : ScalarPoints diagonalTorus A),
    let gA := scalarSpec.map f.op ≫ g
    let tA := t ≫ T.inclusion.hom.hom
    gA * tA = tA * gA

/-- The torus factors through the spin scheme representing the ordered frame
stabilizer. The factor sends its coordinate point to the normalized lift. -/
def FrameTorus.InOrderedStabilizer {P : IntegralPresentation} {G : SplitGroup P}
    (T : FrameTorus G) : Prop :=
  ∃ (H : IntegralGroup) (j : H ⟶ G.group) (i : diagonalTorus ⟶ H)
    (ρ : ∀ S : ScalarTest, ScalarPoints H S →* (ScalarClifford 4 S)ˣ)
    (l : ∀ S : ScalarTest, DiagonalPoints S →* (ScalarClifford 4 S)ˣ),
    i ≫ j = T.inclusion ∧
    SpinSpecification.IsSpinPointRepresentation (integralForm 4) H ρ ∧
    (∀ S : ScalarTest,
      Function.Injective (fun p : ScalarPoints H S => p ≫ j.hom.hom) ∧
      Set.range (fun p : ScalarPoints H S => p ≫ j.hom.hom) =
        {g | ∀ a, G.action S g (frameAxis a) = frameAxis a}) ∧
    IsDiagonalCliffordLift l ∧
    ∀ (S : ScalarTest) (t : ScalarPoints diagonalTorus S),
      ρ S (t ≫ i.hom.hom) = l S (T.points S t)

abbrev FrameTorus.fibre {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G)
    (k : Type) [Field k] : ClosedSubgroup (geometricFiber G k) :=
  ⟨_, ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).mapGrp).map T.inclusion, by
    open CategoryTheory.Limits in
    let f := Spec.map (CommRingCat.ofHom (algebraMap ℤ k))
    let i := T.inclusion.hom.hom
    let b := ((Over.pullback f).map i).left
    change IsClosedImmersion b
    have top : IsPullback (pullback.fst diagonalTorus.X.hom f) (pullback.snd diagonalTorus.X.hom f)
        (i.left ≫ G.group.X.hom) f := by
      rw [Over.w i]
      exact IsPullback.of_hasPullback _ _
    have h₁ : b ≫ pullback.fst G.group.X.hom f = pullback.fst diagonalTorus.X.hom f ≫ i.left :=
      pullback.lift_fst _ _ _
    have h₂ : b ≫ pullback.snd G.group.X.hom f = pullback.snd diagonalTorus.X.hom f :=
      pullback.lift_snd _ _ _
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_bot (h₂.symm ▸ top) h₁.symm (IsPullback.of_hasPullback _ _)) T.closed⟩

def Statement : Prop :=
  ∀ (P : IntegralPresentation) (G : SplitGroup P), ∃ T : FrameTorus G,
    T.InOrderedStabilizer ∧
    (∀ (S : ScalarTest) (g : ScalarPoints G.group S), T.Centralizes g →
      ∀ i, G.action S g (frameAxis i) = frameAxis i) ∧
    (∀ (S : ScalarTest) (g : ScalarPoints G.group S),
      T.Centralizes g ↔ ∃ t : ScalarPoints diagonalTorus S, t ≫ T.inclusion.hom.hom = g) ∧
    ∀ (k : Type) [Field k], LinearAlgebraicGroups.Specs.RankOneFlag.IsGeometricallyMaximal (T.fibre k)

end

end LinearAlgebraicGroups.Albert.SplitFrameTorusSpecification
