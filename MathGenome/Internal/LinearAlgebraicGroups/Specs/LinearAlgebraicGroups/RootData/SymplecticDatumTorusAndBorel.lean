import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.BorelsAndChambers

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix

universe u

namespace LinearAlgebraicGroups.Specs.SymplecticDatumTorusAndBorel

open SymplecticMatrixStructure
open StandardGroups (multiplicativePowerPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue pairing adjointWeightVectors absoluteRoots)
open AdjointRepresentation (GroupPoints)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open GeometricRadicals (IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open GeometricBorelConjugacy (IsKBorel)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint)

noncomputable section

abbrev MatrixAlgebra (I R : Type*) := Matrix (Indices I) (Indices I) R

/-- The coordinate vectors in the character and cocharacter lattices. -/
def coordinate {n : ℕ} (i : Fin n) : Fin n → ℤ := Pi.single i 1

/-- Signs refer to the two members of each hyperbolic basis pair. -/
def sign (s : Bool) : ℤ := if s then 1 else -1

inductive RootLabel (n : ℕ) where
  | long (i : Fin n) (s : Bool)
  | short (i j : Fin n) (ordered : i < j) (s t : Bool)

def rootVector {n : ℕ} : RootLabel n → (Fin n → ℤ)
  | .long i s => (2 * sign s) • coordinate i
  | .short i j _ s t => sign s • coordinate i + sign t • coordinate j

def simpleLabel {n : ℕ} (i : Fin (n + 1)) : RootLabel (n + 1) :=
  if h : i.val < n then .short i ⟨i.val + 1, by omega⟩ (by change i.val < i.val + 1; omega) true false
  else .long i true

abbrev HyperbolicIndex (n : ℕ) := ULift.{u} (Fin n)

def signedIndex {n : ℕ} (i : Fin n) (s : Bool) : Indices (HyperbolicIndex.{u} n) :=
  if s then Sum.inl ⟨i⟩ else Sum.inr ⟨i⟩

/-- Matrix of the tangent vector obtained from the upper elementary
matrix in the rank-one plane or the plane with its paired dual. -/
def elementaryDirection {n : ℕ} (R : Type u) [CommRing R] :
    RootLabel n → MatrixAlgebra (HyperbolicIndex.{u} n) R
  | .long i s => Matrix.single (signedIndex i s) (signedIndex i (!s)) 1
  | .short i j _ s t =>
    Matrix.single (signedIndex i s) (signedIndex j (!t)) 1 +
    Matrix.single (signedIndex j t) (signedIndex i (!s)) ((sign s * sign t : ℤ) : R)

/-- The exponent of the torus on a single hyperbolic basis vector. -/
def indexWeight {n : ℕ} : Indices (HyperbolicIndex.{u} n) → (Fin n → ℤ)
  | .inl i => coordinate i.down
  | .inr i => -coordinate i.down

abbrev LaurentCoordinates (k : Type u) [Semiring k] (n : ℕ) := AddMonoidAlgebra k (Fin n → ℤ)

def universalTorusUnits (k : Type u) [Field k] (n : ℕ) :
    HyperbolicIndex.{u} n → (LaurentCoordinates k n)ˣ :=
  fun i => (AddMonoidAlgebra.of k (Fin n → ℤ)).toHomUnits
    (Multiplicative.ofAdd (coordinate i.down))

/-- A weight is detected on the universal torus point. The inverse on the
right of the conjugation uses the reciprocal diagonal units. -/
def MatrixHasWeight {k : Type u} [Field k] {n : ℕ} (x : Fin n → ℤ)
    (X : MatrixAlgebra (HyperbolicIndex.{u} n) k) : Prop :=
  let T := universalTorusUnits k n
  let M := X.map (algebraMap k (LaurentCoordinates k n))
  SymplecticMatrixStructure.hyperbolicDiagonal T * M *
    SymplecticMatrixStructure.hyperbolicDiagonal (fun i => (T i)⁻¹) =
      AddMonoidAlgebra.single x (1 : k) • M

/-- The weights of the nonzero matrix entries determine the torus weight
of the whole endomorphism, over any base field. -/
def MatrixWeightEntries : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (x : Fin n → ℤ)
    (X : MatrixAlgebra (HyperbolicIndex.{u} n) k),
    MatrixHasWeight x X ↔ ∀ i j, X i j ≠ 0 → x = indexWeight i - indexWeight j

/-- The nonzero weights in the actual matrix model for the symplectic Lie
algebra. Every listed weight has a nonzero elementary tangent vector. -/
def MatrixLieWeights : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    (∀ x : Fin n → ℤ, x ≠ 0 →
      ((∃ X : SymplecticMatrixStructure.symplecticLieSubspace k (HyperbolicIndex.{u} n),
        X.val ≠ 0 ∧ MatrixHasWeight x X.val) ↔ ∃ a : RootLabel n, x = rootVector a)) ∧
    ∀ a : RootLabel n,
      elementaryDirection k a ∈ SymplecticMatrixStructure.symplecticLieSubspace k
        (HyperbolicIndex.{u} n) ∧
      elementaryDirection k a ≠ 0 ∧ MatrixHasWeight (rootVector a) (elementaryDirection k a)


/-- The two lattices with their evaluations in the designated torus coordinates. -/
structure LatticeCoordinates {k : Type u} [Field k] {T : GroupScheme k} {n : ℕ}
    (d : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (HyperbolicIndex.{u} n)) where
  comm : IsCommMonObj T.X
  X : Additive (Character T) ≃ₗ[ℤ] (Fin n → ℤ)
  Y : letI := comm; Additive (Cocharacter T) ≃ₗ[ℤ] (Fin n → ℤ)
  characterEvaluation : ∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} n → Rˣ)
    (χ : Character T), characterValue χ R (d.inv.app R t) =
      (↑(∏ i : Fin n, t ⟨i⟩ ^ X (Additive.ofMul χ) i) : R)
  cocharacterEvaluation : letI := comm
    ∀ (R : TestAlgebra k) (z : Rˣ) (y : Cocharacter T) (i : Fin n),
      (d.hom.app R (cocharacterPoint y R z) : HyperbolicIndex.{u} n → Rˣ) ⟨i⟩ =
        z ^ Y (Additive.ofMul y) i
  compositionPairing : letI := comm
    ∀ (χ : Character T) (y : Cocharacter T), pairing T χ y =
      ∑ i : Fin n, X (Additive.ofMul χ) i * Y (Additive.ofMul y) i

/-- The regular cocharacter has coordinates (n,…,1) in rank n. -/
def descending (n : ℕ) (i : Fin n) : ℤ := (n : ℤ) - i.val

/-- A positive root of a Borel is simple when it is indecomposable among
the positive roots, with addition in the character lattice. -/
def IsSimpleRoot {k : Type u} [Field k] {G : GroupScheme k}
    (T B : ClosedSubgroup G) (α : ↥(absoluteRoots T)) : Prop :=
  α ∈ subgroupRoots T B ∧
    ¬ ∃ (beta gamma : ↥(absoluteRoots T)), beta ∈ subgroupRoots T B ∧ gamma ∈ subgroupRoots T B ∧
      α.val = beta.val * gamma.val

/-- The actual diagonal torus, its marked lattices, its absolute roots with
their tangent vectors, and its Borel with the type C simple system. -/
def TorusAndBorel : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (G : AffineAlgebraicGroup k)
    (c : (groupPointsFunctor k).obj G.val ≅
      symplecticPoints k (HyperbolicIndex.{u} (n + 1))),
    ∃ (T : ClosedSubgroup G.val)
      (d : (groupPointsFunctor k).obj T.group ≅
        multiplicativePowerPoints k (HyperbolicIndex.{u} (n + 1)))
      (L : LatticeCoordinates d)
      (e : Lie k G.val ≃+ symplecticLieSubspace k (HyperbolicIndex.{u} (n + 1)))
      (label : RootLabel (n + 1) ≃ ↥(absoluteRoots T))
      (y : Cocharacter T.group) (D : LimitDecomposition (y ≫ T.inclusion)),
      letI := L.comm
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
      (∀ (R : TestAlgebra k) (t : HyperbolicIndex.{u} (n + 1) → Rˣ),
        (show PointGroup _ R from c.hom.app R
          (((groupPointsFunctor k).map T.inclusion).app R (d.inv.app R t))).val =
          hyperbolicDiagonal t) ∧
      (∀ p i j, (e p).val i j =
        ((show PointGroup _ (DualNumber k) from
          c.hom.app (CommAlgCat.of k (DualNumber k)) p.toMul.val).val i j).snd) ∧
      (∀ χ v, v ∈ adjointWeightVectors T χ ↔ MatrixHasWeight (L.X (Additive.ofMul χ)) (e v).val) ∧
      (∀ a, L.X (Additive.ofMul (label a).val) = rootVector a ∧
        ∃ v ∈ adjointWeightVectors T (label a).val, v ≠ 0 ∧ (e v).val = elementaryDirection k a) ∧
      (∀ i, L.Y (Additive.ofMul y) i = descending (n + 1) i) ∧
      IsRegular T y ∧ IsKBorel D.parabolic ∧ IsSubgroupOf T D.parabolic ∧
      subgroupRoots T D.parabolic = positiveRoots T y ∧
      (∀ a, IsSimpleRoot T D.parabolic (label a) ↔ ∃ i, a = simpleLabel i)

end
end LinearAlgebraicGroups.Specs.SymplecticDatumTorusAndBorel
