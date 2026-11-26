import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieLeftExact
import Mathlib.Algebra.Polynomial.Laurent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin

open AlgebraicGeometry CategoryTheory
open scoped BigOperators MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SpecialLinearDatum

open GeometricRadicals (IsSemisimple IsSplitTorus IsReductive)
open RankOneFlag (IsGeometricallyMaximal)
open GeneralLinearStructure (SpecialMatrixPoints)
open CharacterDescent (Character Cocharacter)
open StandardGroups
open Unipotent (Index)

open CharacterPairing (characterValue pairing adjointWeightVectors)
open GeometricBorelConjugacy (IsKBorel)
open SchemeDerivedGroup (IsSubgroupOf)
open RootGroups (AdditiveLine rootPoint)
open AbstractPairing (Root)
open BorelsAndChambers (subgroupRoots)
open Pinning (SplitBorelPair AttachedDatum IsSimple SimpleRoot RootCoordinate Pinning)
open OrderedRootProducts (RootSubgroupFamily)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition cocharacterPoint)

noncomputable section

/-- The sum of the diagonal exponents. -/
def sumExponents (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] ℤ :=
  ∑ i : Fin n, LinearMap.proj i

/-- The exponents of diagonal determinant-one cocharacters. -/
abbrev CocharacterLattice (n : ℕ) := LinearMap.ker (sumExponents n)

/-- Integer monomials modulo the determinant character. -/
abbrev CharacterLattice (n : ℕ) :=
  (Fin n → ℤ) ⧸ Submodule.span ℤ ({(1 : Fin n → ℤ)} : Set (Fin n → ℤ))

def coordinate (n : ℕ) (i : Fin n) : Fin n → ℤ := Pi.single i 1

def root (n : ℕ) (i j : Fin n) : CharacterLattice n :=
  (Submodule.span ℤ ({(1 : Fin n → ℤ)} : Set (Fin n → ℤ))).mkQ
    (coordinate n i - coordinate n j)

def coroot (n : ℕ) (i j : Fin n) : CocharacterLattice n :=
  ⟨coordinate n i - coordinate n j, by
    simp [sumExponents, coordinate, LinearMap.sum_apply, Finset.sum_sub_distrib]⟩

def simpleCoroot (r : ℕ) (i : Fin r) : CocharacterLattice (r + 1) :=
  coroot (r + 1) i.castSucc i.succ

/-- The dot product before imposing the determinant relation. -/
def exponentDot (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] CocharacterLattice n →ₗ[ℤ] ℤ where
  toFun x :=
    { toFun := fun y => ∑ i, x i * y.val i
      map_add' y z := by simp [mul_add, Finset.sum_add_distrib]
      map_smul' a y := by
        change (∑ i, x i * (a * y.val i)) = a * ∑ i, x i * y.val i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ac_rfl }
  map_add' x z := by
    ext y
    change (∑ i, (x i + z i) * y.val i) = (∑ i, x i * y.val i) + (∑ i, z i * y.val i)
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext y
    change (∑ i, (a * x i) * y.val i) = a * ∑ i, x i * y.val i
    simp only [mul_assoc, Finset.mul_sum]

/-- The dot product, descended along the determinant relation. -/
def dotPairing (n : ℕ) : CharacterLattice n →ₗ[ℤ] CocharacterLattice n →ₗ[ℤ] ℤ := by
  refine Submodule.liftQ _ (exponentDot n) (Submodule.span_le.mpr ?_)
  intro v hv
  obtain rfl : v = 1 := hv
  change exponentDot n 1 = 0
  ext y
  change (∑ i : Fin n, (1 : ℤ) * y.val i) = 0
  have hy : sumExponents n y.val = 0 := y.2
  simpa [sumExponents, LinearMap.sum_apply] using hy

/-- The canonical special linear group is semisimple in every positive matrix size. -/
def Semisimple : Prop :=
  ∀ (k : Type u) [Field k] (r : ℕ) (S : AffineAlgebraicGroup k),
    SpecialMatrixPoints S (r + 1) → IsSemisimple S

/-- The size-one scheme represents the trivial group on all test rings. -/
def RankOneTrivial : Prop :=
  ∀ (k : Type u) [Field k] (S : AffineAlgebraicGroup k),
    SpecialMatrixPoints S 1 → Nonempty (S.val ≅ Grp.trivial (SchemeOver k))

/-- Adjacent differences are an integral basis of the determinant-one exponents. -/
def SimpleCorootBasis : Prop :=
  ∀ r : ℕ, ∃ b : Module.Basis (Fin r) ℤ (CocharacterLattice (r + 1)),
    ∀ i, b i = simpleCoroot r i

/-- Cartan pairings of the adjacent roots and coroots in their natural order. -/
def SimpleCartanPairings : Prop :=
  ∀ (r : ℕ) (i j : Fin r),
    dotPairing (r + 1) (root (r + 1) i.castSucc i.succ) (simpleCoroot r j) =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

/-- The first diagonal entry is determined by the other entries and the determinant. -/
def determinantOneUnits {R : Type u} [CommRing R] {r : ℕ}
    (a : Index.{u} r → Rˣ) : Index.{u} (r + 1) → Rˣ :=
  fun i => Fin.cons (α := fun _ => Rˣ) (∏ j : Index.{u} r, a j)⁻¹ (fun j => a ⟨j⟩) i.down

/-- A split torus embedded by putting in the missing first diagonal entry.
The range condition specifies the diagonal subgroup on all test algebras. -/
structure DiagonalTorus {k : Type u} [Field k] {r : ℕ}
    {S : AffineAlgebraicGroup k} (s : SpecialMatrixPoints S (r + 1)) where
  subgroup : ClosedSubgroup S.val
  pointsIso : (groupPointsFunctor k).obj subgroup.group ≅ multiplicativePowerPoints k (Index.{u} r)
  split : IsSplitTorus subgroup.group
  matrix : ∀ (R : TestAlgebra k) (x : Points subgroup.group.X R),
    (s.hom.app R (x ≫ subgroup.inclusion.hom.hom)).val =
      Matrix.diagonal (fun i => (determinantOneUnits (pointsIso.hom.app R x) i : R))
  range : ∀ (R : TestAlgebra k) (x : Points S.val.X R),
    x ∈ SubgroupSections subgroup ((testSpec k).obj (Opposite.op R)) ↔
      ∀ i j, i ≠ j → (s.hom.app R x).val i j = 0

/-- The split diagonal subgroup of the actual matrix functor is geometrically maximal. -/
def SplitDiagonalTorus : Prop :=
  ∀ (k : Type u) [Field k] (r : ℕ) (S : AffineAlgebraicGroup k)
    (s : SpecialMatrixPoints S (r + 1)),
    ∃ T : DiagonalTorus s, IsGeometricallyMaximal T.subgroup

/-- Diagonal entries of the normalized two-coordinate rank-one word. -/
def coordinatePairUnits {R : Type u} [CommRing R] {idx : Type*} [DecidableEq idx]
    (i j : idx) (a : Rˣ) (l : idx) : Rˣ :=
  if l = i then a else if l = j then a⁻¹ else 1

/-- The rank-one word in the two standard matrix transvections. -/
def transvectionWord {R : Type u} [CommRing R] {idx : Type*} [Fintype idx] [DecidableEq idx]
    {i j : idx} (hij : i ≠ j) (a : Rˣ) : Matrix.SpecialLinearGroup idx R :=
  Matrix.SpecialLinearGroup.transvection hij (a : R) *
    Matrix.SpecialLinearGroup.transvection hij.symm (-(↑a⁻¹ : R)) *
    Matrix.SpecialLinearGroup.transvection hij (a : R)

/-- The normalized word has diagonal entries (t,t^{-1}) in the chosen positions,
over arbitrary test rings, including characteristic two and nonreduced rings. -/
def NormalizedWord : Prop :=
  ∀ (R idx : Type u) [CommRing R] [Fintype idx] [DecidableEq idx]
    (i j : idx) (hij : i ≠ j) (a : Rˣ),
    (transvectionWord hij a * (transvectionWord hij 1)⁻¹).val =
      Matrix.diagonal (fun l => (coordinatePairUnits i j a l : R))

/-- The two integral lattices in size one are zero. -/
def SizeOneLattices : Prop :=
  Subsingleton (CharacterLattice 1) ∧ Subsingleton (CocharacterLattice 1)

/-- The ordered indices of the off-diagonal matrix units. -/
abbrev RootIndices (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The strictly decreasing exponents (r,r-2,ldots,-r). -/
def decreasingVector (r : ℕ) : Fin (r + 1) → ℤ :=
  fun i => (r : ℤ) - 2 * (i.val : ℤ)

/-- Simplicity is indecomposability among the positive differences. -/
def AdjacentPositiveRoots : Prop :=
  ∀ (r : ℕ) (i j : Fin (r + 1)), i < j →
    ((∀ a b c d : Fin (r + 1), a < b → c < d →
      root (r + 1) i j ≠ root (r + 1) a b + root (r + 1) c d) ↔
      ∃ p : Fin r, i = p.castSucc ∧ j = p.succ)

/-- The rank-one generators with the first diagonal entry as parameter. -/
def SizeTwoLattices : Prop :=
  ∃ (x : CharacterLattice 2 ≃ₗ[ℤ] ℤ) (y : CocharacterLattice 2 ≃ₗ[ℤ] ℤ),
    x ((Submodule.span ℤ ({(1 : Fin 2 → ℤ)} : Set (Fin 2 → ℤ))).mkQ (coordinate 2 0)) = 1 ∧
    y (coroot 2 0 1) = 1 ∧ x (root 2 0 1) = 2 ∧
    ∀ a b, dotPairing 2 a b = x a * y b

variable {k : Type u} [Field k] {r : ℕ} {S : AffineAlgebraicGroup k}
  {s : SpecialMatrixPoints S (r + 1)}

/-- The integral identifications of the two actual lattices, with the pointwise
monomial and diagonal power formulas and the resulting composition pairing. -/
structure LatticeIdentification (T : DiagonalTorus s) where
  comm : IsCommMonObj T.subgroup.group.X
  characters : Additive (Character T.subgroup.group) ≃ₗ[ℤ] CharacterLattice (r + 1)
  cocharacters : letI := comm
    Additive (Cocharacter T.subgroup.group) ≃ₗ[ℤ] CocharacterLattice (r + 1)
  characterValue_eq : ∀ (a : Fin (r + 1) → ℤ) (R : TestAlgebra k)
    (t : Points T.subgroup.group.X R),
    characterValue (Additive.toMul (characters.symm
      ((Submodule.span ℤ ({(1 : Fin (r + 1) → ℤ)} : Set (Fin (r + 1) → ℤ))).mkQ a))) R t =
      ↑(∏ i : Fin (r + 1), determinantOneUnits (T.pointsIso.hom.app R t) ⟨i⟩ ^ a i)
  cocharacterPoint_eq : ∀ (y : CocharacterLattice (r + 1)) (R : TestAlgebra k) (t : Rˣ),
    letI := comm
    (s.hom.app R
      (cocharacterPoint (Additive.toMul (cocharacters.symm y)) R t ≫
        T.subgroup.inclusion.hom.hom)).val =
      Matrix.diagonal (fun i => (↑(t ^ y.val i.down) : R))
  pairing_eq : ∀ (χ : Character T.subgroup.group) (c : Cocharacter T.subgroup.group),
    letI := comm
    pairing T.subgroup.group χ c =
      dotPairing (r + 1) (characters (Additive.ofMul χ)) (cocharacters (Additive.ofMul c))

/-- The actual roots are precisely the off-diagonal weights. -/
structure RootIdentification (T : DiagonalTorus s) (L : LatticeIdentification T) where
  indices : RootIndices (r + 1) ≃ Root T.subgroup
  character_eq : ∀ p, L.characters (Additive.ofMul (indices p).val) = root (r + 1) p.val.1 p.val.2
  weight_eq : ∀ (p : RootIndices (r + 1)) (v : Lie k S.val),
    v ∈ adjointWeightVectors T.subgroup (indices p).val ↔
      ∃ a : k, slTangentCoefficient s v = Matrix.single ⟨p.val.1⟩ ⟨p.val.2⟩ a

/-- The actual upper triangular Borel is the limit parabolic of the decreasing direction. -/
structure UpperTriangularBorel (T : DiagonalTorus s) (L : LatticeIdentification T)
    (M : RootIdentification T L) where
  reductive : IsReductive S
  maximal : IsGeometricallyMaximal T.subgroup
  exponents : CocharacterLattice (r + 1)
  exponent_eq : exponents.val = decreasingVector r
  limits : LimitDecomposition (letI := L.comm
    Additive.toMul (L.cocharacters.symm exponents) ≫ T.subgroup.inclusion)
  isBorel : IsKBorel limits.parabolic
  containsTorus : IsSubgroupOf T.subgroup limits.parabolic
  matrix : ∀ (R : TestAlgebra k) (g : Points S.val.X R),
    g ∈ SubgroupSections limits.parabolic ((testSpec k).obj (Opposite.op R)) ↔
      (s.hom.app R g).val.IsUpperTriangular
  positive_iff : ∀ p, M.indices p ∈ subgroupRoots T.subgroup limits.parabolic ↔ p.val.1 < p.val.2

/-- The Borel pair uses the identical ambient group and torus. -/
abbrev UpperTriangularBorel.pair {T : DiagonalTorus s} {L : LatticeIdentification T}
    {M : RootIdentification T L} (B : UpperTriangularBorel T L M) : SplitBorelPair k :=
  ⟨S, B.reductive, T.subgroup, T.split, B.maximal, B.limits.parabolic, B.isBorel, B.containsTorus⟩

/-- Both the full root datum and its base agree with the displayed matrix lattices. -/
def IsMatrixBasedDatum {T : DiagonalTorus s} {L : LatticeIdentification T}
    {M : RootIdentification T L} (B : UpperTriangularBorel T L M)
    (D : AttachedDatum B.pair) : Prop :=
  letI := D.comm
  (∀ p : RootIndices (r + 1),
    L.cocharacters (D.datum.rootDatum.coroot (M.indices p)) = coroot (r + 1) p.val.1 p.val.2) ∧
  ∀ p : RootIndices (r + 1), M.indices p ∈ D.base.support ↔
    ∃ i : Fin r, p.val.1 = i.castSucc ∧ p.val.2 = i.succ

/-- The standard transvections are coordinates of the actual root subgroups,
and their restriction to the simple roots is a pinning of the specified pair. -/
def HasTransvectionPinning {T : DiagonalTorus s} {L : LatticeIdentification T}
    {M : RootIdentification T L} (B : UpperTriangularBorel T L M) : Prop :=
  ∃ (A : AdditiveLine k) (U : RootSubgroupFamily T.subgroup)
    (x : ∀ α : Root T.subgroup, RootCoordinate A T.subgroup (U α).val α.val),
    (∀ (p : RootIndices (r + 1)) (R : TestAlgebra k) (a : R),
      (s.hom.app R (rootPoint ((x (M.indices p)).val.hom ≫ (U (M.indices p)).val.inclusion) R a)).val =
        1 + Matrix.single ⟨p.val.1⟩ ⟨p.val.2⟩ a) ∧
    ∃ pin : Pinning A B.pair U, ∀ α, pin α = x α.val

/-- The pinned datum and geometric simple connectedness of the determinant-one group.
The root index is empty in size one. -/
def MatrixPinnedDatum : Prop :=
  ∀ (k : Type u) [Field k] (r : ℕ) (S : AffineAlgebraicGroup k)
    (s : SpecialMatrixPoints S (r + 1)),
    ∃ (T : DiagonalTorus s) (L : LatticeIdentification T) (M : RootIdentification T L)
      (B : UpperTriangularBorel T L M) (D : AttachedDatum B.pair),
      IsMatrixBasedDatum B D ∧ HasTransvectionPinning B ∧ GeometricallySimplyConnected S


end

end LinearAlgebraicGroups.Specs.SpecialLinearDatum
