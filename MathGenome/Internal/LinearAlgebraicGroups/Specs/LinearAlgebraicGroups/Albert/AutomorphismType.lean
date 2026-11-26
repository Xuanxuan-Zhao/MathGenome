import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitAlbertAdjointWeights
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AlbertAutomorphismDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRecognition
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SchemeCentre

namespace LinearAlgebraicGroups.Albert.AutomorphismTypeSpecification

open LinearAlgebraicGroups.Specs
open SpinWeights (CharacterExponents VectorExponents coordinate epsilon halfSum
  exteriorWeight)
open scoped BigOperators

/-- The two nonzero signs, with both choices independent on each long root. -/
def rootSign (negative : Bool) : ℤ := if negative then -1 else 1

abbrev LongIndex := {ij : Fin 4 × Fin 4 // ij.1 < ij.2} × Bool × Bool
abbrev VectorIndex := Fin 4 × Bool
abbrev HalfIndex := Finset (Fin 4)
abbrev RootIndex := LongIndex ⊕ (VectorIndex ⊕ HalfIndex)

/-- The roots in the diagonal Spin₈ character lattice, with the half-spin
weights marked by the corresponding wedge subsets. -/
def rootCharacter : RootIndex → CharacterExponents
  | .inl (ij, s, t) => rootSign s • epsilon ij.val.1 + rootSign t • epsilon ij.val.2
  | .inr (.inl (i, s)) => rootSign s • epsilon i
  | .inr (.inr I) => exteriorWeight I

/-- Twice the Euclidean coordinates of a character. In the free coordinates
of the spin torus the character of the scalar is minus the half-sum. -/
def doubledCoordinates (x : CharacterExponents) : VectorExponents :=
  Fin.cons (-x.1) (fun i => 2 * x.2 i - x.1)

/-- Coroots in the four vector coordinates. The short vector roots are
doubled, and the half-sums give the four independent signs. -/
def vectorCoroot : RootIndex → VectorExponents
  | .inl (ij, s, t) => rootSign s • coordinate ij.val.1 + rootSign t • coordinate ij.val.2
  | .inr (.inl (i, s)) => (2 * rootSign s) • coordinate i
  | .inr (.inr I) => fun i => if i ∈ I then 1 else -1

/-- A cocharacter in the coordinates dual to the scalar and three
independent diagonal entries of the spin torus. -/
def corootCoordinates (r : RootIndex) : CharacterExponents :=
  (-(∑ i, vectorCoroot r i) / 2, fun i => vectorCoroot r i.succ)

def coordinatePairing (x y : CharacterExponents) : ℤ :=
  x.1 * y.1 + ∑ i, x.2 i * y.2 i

def simpleIndex : Fin 4 → RootIndex :=
  ![.inl (⟨(1, 2), by decide⟩, false, true),
    .inl (⟨(2, 3), by decide⟩, false, true),
    .inr (.inl (3, false)), .inr (.inr {0})]

/-- The transpose convention is avoided by indexing the rows by roots
and the columns by coroots. -/
def cartanMatrix : Fin 4 → Fin 4 → ℤ :=
  ![![2, -1, 0, 0], ![-1, 2, -2, 0], ![0, -1, 2, -1], ![0, 0, -1, 2]]

def RootLatticeCalculation : Prop :=
  Fintype.card LongIndex = 24 ∧ Fintype.card VectorIndex = 8 ∧ Fintype.card HalfIndex = 16 ∧
  Function.Injective rootCharacter ∧ (∀ r, rootCharacter r ≠ 0) ∧
  Set.range (fun r : LongIndex => rootCharacter (.inl r)) = SpinWeights.rootCharacters ∧
  Submodule.span ℤ (Set.range rootCharacter) = ⊤

def CorootCalculation : Prop :=
  Function.Injective corootCoordinates ∧
  (∀ r, coordinatePairing (rootCharacter r) (corootCoordinates r) = 2) ∧
  (∀ i j, coordinatePairing (rootCharacter (simpleIndex i)) (corootCoordinates (simpleIndex j)) =
    cartanMatrix i j) ∧
  ∀ (x : CharacterExponents) r,
    2 * coordinatePairing x (corootCoordinates r) =
      ∑ j, doubledCoordinates x j * vectorCoroot r j

/-- The rank-one reflection on characters determines its integral coroot
by its action on the finite spanning root set. -/
def ReflectionRecovery : Prop :=
  ∀ (r : RootIndex) (f : Module.Dual ℤ CharacterExponents),
    f (rootCharacter r) = 2 →
    Set.MapsTo (Module.preReflection (rootCharacter r) f)
      (Set.range rootCharacter) (Set.range rootCharacter) →
    ∀ x, f x = coordinatePairing x (corootCoordinates r)

/-- Integral based data realizing the explicit roots, coroots and simple
system on the full character and cocharacter lattices. -/
structure DatumCoordinates (D : Pinning.BasedRootDatum.{0}) where
  characters : D.X ≃ₗ[ℤ] CharacterExponents
  cocharacters : D.Y ≃ₗ[ℤ] CharacterExponents
  roots : D.I ≃ RootIndex
  root_eq : ∀ i, characters (D.datum.root i) = rootCharacter (roots i)
  coroot_eq : ∀ i, cocharacters (D.datum.coroot i) = corootCoordinates (roots i)
  pair_eq : ∀ x y, D.datum.toLinearMap x y = coordinatePairing (characters x) (cocharacters y)
  simple_eq : ∀ i, i ∈ D.base.support ↔ roots i ∈ Set.range simpleIndex

def IntegralDatumExists : Prop := ∃ D : Pinning.BasedRootDatum.{0}, Nonempty (DatumCoordinates D)


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj TensorProduct
open TrialitySpecification (Model)
open IntegralSmoothnessSpecification (SplitGroup algebraicFiber geometricFiber)
open ShortDirectionSpecification (IntegralPresentation)
open SpinWeights (DiagonalPoints mapDiagonal evaluate)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue absoluteRoots pairing)
open GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)

noncomputable section

abbrev groupChange := @AutomorphismDescentSpecification.groupChange
abbrev IsCenterless := @AutomorphismDescentSpecification.IsCenterless
abbrev FrameTorus := @SplitFrameTorusSpecification.FrameTorus

/-- The absolute weights and the actual integral coroots on the same
calibrated torus in every geometric fibre. -/
def FibreRoots {P : IntegralPresentation} {G : SplitGroup P} (T : FrameTorus G) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k],
    let Tₖ := T.fibre k
    IsSplitTorus Tₖ.group ∧ IsGeometricallyMaximal Tₖ ∧
    ∃ C : SplitAlbertAdjointWeightsSpecification.FibreCalibration T k,
      Set.BijOn (fun χ : Character Tₖ.group => C.characters (Additive.ofMul χ))
        (absoluteRoots Tₖ) (Set.range rootCharacter) ∧
      ∃ h : IsCommMonObj Tₖ.group.X, letI := h
      ∃ (E : AbstractPairing.Datum (G := algebraicFiber G k) Tₖ)
        (Y : Additive (Cocharacter Tₖ.group) ≃ₗ[ℤ] CharacterExponents),
        (∀ χ ψ, pairing Tₖ.group χ ψ =
          coordinatePairing (C.characters (Additive.ofMul χ)) (Y (Additive.ofMul ψ))) ∧
        ∀ α : AbstractPairing.Root (G := algebraicFiber G k) Tₖ,
          ∃ r : RootIndex, C.characters (Additive.ofMul α.val) = rootCharacter r ∧
            Y (E.rootDatum.coroot α) = corootCoordinates r

/-- The base-change functor sends the Chevalley model over the integral
classification's copy of the integers to the requested base. -/
abbrev chevalleyChange (R : Type) [CommRing R] :=
  letI : Algebra IntegralSemisimpleModel.Integers.{0} R :=
    IntegralSemisimpleModel.integerAlgebra R
  groupChange IntegralSemisimpleModel.Integers.{0} R

/-- The split Albert automorphism group with its torus and the integral
comparison to the Chevalley model of the explicit based datum. -/
structure IntegralSplitIdentification where
  datum : Pinning.BasedRootDatum.{0}
  datumCoordinates : DatumCoordinates datum
  chevalley : IntegralSemisimpleModel.Model datum
  presentation : IntegralPresentation
  split : SplitGroup presentation
  torus : FrameTorus split
  inOrderedStabilizer : torus.InOrderedStabilizer
  comparison : split.group ≅ (chevalleyChange ℤ).obj chevalley.group
  torusComparison : SplitFrameTorusSpecification.diagonalTorus ≅ (chevalleyChange ℤ).obj (IntegralSemisimpleModel.splitTorus datum)
  compatible : torus.inclusion ≫ comparison.hom =
    torusComparison.hom ≫ (chevalleyChange ℤ).map chevalley.torus
  smooth : SmoothOfRelativeDimension 52 split.group.X.hom
  connected : GeometricallyConnected split.group.X.hom
  fibreRoots : FibreRoots torus
  adjointSemisimple : ∀ (k : Type) [Field k] [IsAlgClosed k],
    IsSemisimple (algebraicFiber split k) ∧ IsCenterless (geometricFiber split k)

section Forms

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

abbrev RepresentsAutomorphisms := @AutomorphismDescentSpecification.RepresentsAutomorphisms

/-- Forms split by the faithfully flat cover in the definition of Albert
algebra. The geometric fibre is the specified Chevalley group of type F₄. -/
def AlbertForms (D : Pinning.BasedRootDatum.{0}) (C : IntegralSemisimpleModel.Model D) : Prop :=
  ∀ {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    (J : SplitSpecification.ParaQuadratic R M), SplitSpecification.IsAlbert J →
    ∃ G : SpinSpecification.GroupScheme R,
      IsAffine G.X.left ∧ LocallyOfFinitePresentation G.X.hom ∧
      RepresentsAutomorphisms J G ∧ Smooth G.X.hom ∧ GeometricallyConnected G.X.hom ∧
      IsCenterless G ∧
      (∀ (S : Type) [CommRing S] [Algebra R S],
        RepresentsAutomorphisms (J.baseChange S) ((groupChange R S).obj G)) ∧
      (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K],
        ∃ H : AffineAlgebraicGroup K, IsSemisimple H ∧
          Nonempty (((groupChange R K).obj G) ≅ H.val) ∧
          Nonempty (H.val ≅ (chevalleyChange K).obj C.group)) ∧
      (SplitSpecification.IsSplitModel J .octonion →
        Nonempty (G ≅ (chevalleyChange R).obj C.group))

end Forms

/-- NA13-C04.09 for the split algebra over the integers and all its
faithfully flat forms over arbitrary commutative base rings. -/
def Statement : Prop :=
  ∃ S : IntegralSplitIdentification, AlbertForms S.datum S.chevalley

end
end LinearAlgebraicGroups.Albert.AutomorphismTypeSpecification
