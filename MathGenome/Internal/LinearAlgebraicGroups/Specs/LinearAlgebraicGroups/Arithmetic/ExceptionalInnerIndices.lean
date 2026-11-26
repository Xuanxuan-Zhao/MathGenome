import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerAlcoveSymmetries
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerWeylDirections

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerIndices

open ExceptionalInnerWeylDirections (reflectWord)
open ExceptionalInnerAlcoveSymmetries (e6Highest e7Highest e6Rotate e7Reverse invariantDirections)

universe u

def e6Word : List (Fin 6) := [0, 2, 3, 5, 4, 3, 1, 2, 3]
def e7Word : List (Fin 7) := [6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5]

/-- The orbit numbers are constant on each cycle of the marked affine diagram. -/
def e6Orbit : Fin 7 → Fin 3 := ![0, 0, 1, 1, 2, 1, 0]
def e7Orbit : Fin 8 → Fin 5 := ![0, 1, 2, 3, 4, 3, 1, 0]

def e6Black : Set (Fin 6) := {0, 2, 4, 5}
def e7Black : Set (Fin 7) := {1, 4, 6}

def VanishingNodes {n : ℕ} (D : Set (Fin n → ℚ)) : Set (Fin n) :=
  {i | ∀ r ∈ D, r i = 0}

/-- The finite calculation on the extended E₆ diagram, with either
nonidentity rotation as generator. -/
def E6IndexCalculation : Prop :=
  Function.Surjective e6Orbit ∧
  (∀ i j, e6Orbit i = e6Orbit j ↔
    ∃ k : Fin 3, (e6Rotate ^ (k : ℕ)) i = j) ∧
  (∀ r ∈ invariantDirections e6Highest e6Rotate,
    ∃ a b : ℚ, r = ![-2*a-b, a, a, b, a, -2*a-b]) ∧
  (∀ a b : ℚ, ![-2*a-b, a, a, b, a, -2*a-b] ∈ invariantDirections e6Highest e6Rotate ∧
    reflectWord e6Word ![-2*a-b, a, a, b, a, -2*a-b] = ![0, b, 0, a, 0, 0]) ∧
  VanishingNodes (reflectWord e6Word '' invariantDirections e6Highest e6Rotate) = e6Black

/-- The finite calculation on the extended E₇ diagram. -/
def E7IndexCalculation : Prop :=
  Function.Surjective e7Orbit ∧
  (∀ i j, e7Orbit i = e7Orbit j ↔
    ∃ k : Fin 2, (e7Reverse ^ (k : ℕ)) i = j) ∧
  (∀ r ∈ invariantDirections e7Highest e7Reverse,
    ∃ a b c d : ℚ, r = ![a, d, b, c, b, a, -2*a-3*b-2*c-d]) ∧
  (∀ a b c d : ℚ,
    ![a, d, b, c, b, a, -2*a-3*b-2*c-d] ∈ invariantDirections e7Highest e7Reverse ∧
    reflectWord e7Word ![a, d, b, c, b, a, -2*a-3*b-2*c-d] = ![d, 0, c, b, 0, a, 0]) ∧
  VanishingNodes (reflectWord e7Word '' invariantDirections e7Highest e7Reverse) = e7Black

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

open ExceptionalAffineRootSystems (ApartmentRoots simpleRootValues)
open ExceptionalAffineBruhat (ExceptionalNumbering IsUnramifiedLocalExtension SplitLevel)
open ExceptionalAffineBuilding (SplitBuildingLevel lengthZeroNormalizer typeChange)
open ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open ExceptionalInnerStandardTorusDescent (markedCharacter IsMarkedTrivialization)
open ExceptionalTwistedTraceComparison (PointCocycle Twist)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open ExceptionalMarkedRootDescent (MarkedFibre)
open IntegralSemisimpleModel (Model fibre integerAlgebra forgetFibrePoint)
open Pinning (BasedRootDatum)
open AutomorphismSequence (AdjointQuotient)
open RelativeFormComparison (IsInduced)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open GeometricRadicals (IsMaximalTorus)
open SchemeDerivedGroup (IsSubgroupOf)

attribute [local instance] integerAlgebra

/-- A split torus of the indicated dimension over its own ground field. -/
def IsSplitOfRank {F : Type u} [Field F] (S : GroupScheme F) (r : ℕ) : Prop :=
  Nonempty (S ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val)

noncomputable section

/-- The descended standard torus contains a maximal split torus of rank `r`.
A change of Borel by a marked normalizer point makes the absolute simple
roots adapted to a minimal rational parabolic. A node is black exactly
when its character restricts trivially to the base change of the split torus. -/
def HasInnerIndex {F K : Type u} [Field F] [Field K] [Algebra F K]
    {H : AffineAlgebraicGroup F} {D : BasedRootDatum.{u}} {M : Model D}
    {n : ℕ} (b : Fin n ≃ D.base.support) (r : ℕ) (black : Set (Fin n))
    (C : MarkedFibre M K)
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
    (normalizer : Set (ExceptionalAffineBruhat.FieldPoints M K)) : Prop :=
  let P := C.realization.pinned.pair
  (∀ (S' : ClosedSubgroup H.val) (r' : ℕ), IsSplitOfRank S'.group r' → r' ≤ r) ∧
  ∃ (U S : ClosedSubgroup H.val) (uK : (groupBaseChange F K).obj U.group ≅ P.T.group),
    IsMaximalTorus U ∧ IsMaximalSplitTorus S ∧ IsSplitOfRank S.group r ∧ IsSubgroupOf S U ∧
    uK.hom ≫ P.T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion ∧
    ∃ (g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X) (J : ClosedSubgroup H.val)
      (sK : (groupBaseChange F K).obj S.group ⟶ P.T.group)
      (jK : P.B.group ⟶ (groupBaseChange F K).obj J.group),
      markedGroundPoint C g ∈ normalizer ∧ IsMinimalParabolic H J ∧ IsSubgroupOf S J ∧
      let gs : ((groupBaseChange F K).obj S.group).X ⟶ P.G.val.X := toUnit _ ≫ g
      let gb : P.B.group.X ⟶ P.G.val.X := toUnit _ ≫ g
      (sK ≫ P.T.inclusion).hom.hom =
        gs * (((groupBaseChange F K).map S.inclusion) ≫ f.inv).hom.hom * gs⁻¹ ∧
      (jK ≫ (groupBaseChange F K).map J.inclusion ≫ f.inv).hom.hom =
        gb⁻¹ * P.B.inclusion.hom.hom * gb ∧
      ∀ i, i ∈ black ↔ (sK ≫ markedCharacter C (b i)).hom.hom = 1

/-- The split rank and Tits index of an actual inner form presented by a
nontrivial length-zero Frobenius representative at a finite unramified level.
The wall labels identify vertices by their opposite walls. -/
def InnerIndex (n r : ℕ) (highest : Fin n → ℤ)
    (permutations : Set (Equiv.Perm (Fin (n + 1)))) (black : Set (Fin n)) : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      (c : MarkedCentralCover M M') (b : Fin n ≃ D.base.support) (b' : Fin n ≃ E.base.support),
      ExceptionalNumbering D n b → ExceptionalNumbering E n b' →
      D.datum.corootSpan ℤ = ⊤ → E.datum.rootSpan ℤ = ⊤ →
      ∀ {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
        {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
        (Y : SplitLevel K c p p' e) (_B : SplitBuildingLevel Y),
        let A := ApartmentRoots.split E.datum ℚ
        (∀ i, E.base.IsPos i → 0 < A.root i p' ∧ A.root i p' < 1) →
        ∀ (G : AffineAlgebraicGroup F) (Q : AdjointQuotient G)
          (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group),
          Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map →
          ∀ (a : PointCocycle (S := K) Q.quotient.val) (T : Twist a) (σ : Gal(K/F)),
            IsArithmeticFrobenius σ →
            let t := forgetFibrePoint M'.group (CommAlgCat.of F K) (a.val σ ≫ iQ.hom.hom.hom)
            t ∈ lengthZeroNormalizer Y.ad →
            typeChange Y.typeQuotient t ≠ 1 →
            (∃ l : Fin (n + 1) ≃ A.SimpleWall p',
              (∀ i x, A.wallValue (l i).val x =
                Fin.cases (1 - ∑ j, (highest j : ℚ) * simpleRootValues E.datum E.base b' ℚ x j)
                  (simpleRootValues E.datum E.base b' ℚ x) i) ∧
              (∃ τ ∈ permutations, ∀ i,
                Y.typeQuotient.wallPerm (typeChange Y.typeQuotient t) (l i) = l (τ i))) ∧
            ∃ (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj T.group.val)
              (f : Y.sc_fibre.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj T.group.val),
              IsInduced F K j T.trivialization ∧ IsMarkedTrivialization Y.sc_fibre iG j f ∧
              HasInnerIndex b r black Y.sc_fibre f Y.sc.N

/-- The extended diagram computations and the two nonsplit inner exceptional
Tits indices over a nonarchimedean local field in any characteristic. -/
def ExceptionalInnerTitsIndices : Prop :=
  E6IndexCalculation ∧ E7IndexCalculation ∧
  InnerIndex.{u} 6 2 e6Highest {e6Rotate, e6Rotate.symm} e6Black ∧
  InnerIndex.{u} 7 4 e7Highest {e7Reverse} e7Black

end
end LinearAlgebraicGroups.Specs.ExceptionalInnerIndices
