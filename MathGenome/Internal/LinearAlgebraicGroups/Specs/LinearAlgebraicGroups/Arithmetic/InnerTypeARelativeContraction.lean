import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeReflections
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Transvection

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct BigOperators Matrix

universe u

namespace LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction

open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

variable {F B R : Type*} [Field F] [Ring B] [Algebra F B] [CommRing R] [Algebra F R]

/-- Central scalar diagonal in the test-algebra points of the matrix algebra. -/
noncomputable def scalarDiagonal {m : ℕ} (t : Fin m → R) :
    R ⊗[F] Matrix (Fin m) (Fin m) B :=
  ∑ i, t i ⊗ₜ[F] Matrix.single i i (1 : B)

/-- The additive matrix block, in the original algebra before identifying a splitting. -/
noncomputable def blockEntry {m : ℕ} (i j : Fin m) :
    R ⊗[F] B →ₗ[F] R ⊗[F] Matrix (Fin m) (Fin m) B :=
  TensorProduct.map LinearMap.id (Matrix.singleLinearMap F i j)

/-- The original block coordinate, with its values in the extended division
algebra. -/
noncomputable def blockProjection {m : ℕ} (i j : Fin m) :
    R ⊗[F] Matrix (Fin m) (Fin m) B →ₗ[F] R ⊗[F] B :=
  TensorProduct.map LinearMap.id (Matrix.entryLinearMap F B i j)

/-- Left and right multiplication by central scalar diagonals acts entrywise.
For a tuple of units and its inverse this gives the actual character ratio on
each block over any test algebra. -/
def DiagonalAction : Prop :=
  ∀ {F B R : Type*} [Field F] [Ring B] [Algebra F B] [CommRing R] [Algebra F R]
    {m : ℕ} (t u : Fin m → R) (x : R ⊗[F] Matrix (Fin m) (Fin m) B) (i j : Fin m),
    blockProjection i j (scalarDiagonal t * x * scalarDiagonal u) =
      (t i * u j) • blockProjection i j x

/-- A single off-diagonal block gives an additive one-parameter block group inside
the norm-one functor, with its parameter recovered uniquely. -/
def BlockTransvections : Prop :=
  ∀ {F B R : Type*} [Field F] [DivisionRing B] [Algebra F B] [CommRing R] [Algebra F R]
    (_hB : isCentralSimple F B) {m : ℕ} (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (i j : Fin m) (_hij : i ≠ j),
    Function.Injective (fun x : R ⊗[F] B => 1 + blockEntry i j x) ∧
    (∀ x : R ⊗[F] B, normAt hA b (1 + blockEntry i j x) = 1) ∧
    ∀ x y : R ⊗[F] B,
      (1 + blockEntry i j x) * (1 + blockEntry i j y) = 1 + blockEntry i j (x + y)

/-- A cocharacter of the standard diagonal torus, expressed by integral powers
of the diagonal coordinates whose sum is zero. -/
abbrev DiagonalCocharacter (m : ℕ) :=
  {a : Fin m → ℤ // ∑ i, a i = 0}

/-- The ratio of the two diagonal coordinates, in the integral character pairing. -/
def blockCharacter {m : ℕ} (i j : Fin m) (a : DiagonalCocharacter m) : ℤ :=
  a.val i - a.val j

/-- Distinct ordered pairs give distinct nonzero rays. The equality tested here
allows any positive rational proportionality by clearing denominators. -/
def DiagonalRootRays : Prop :=
  ∀ {m : ℕ} {i j k l : Fin m}, i ≠ j → k ≠ l →
    (∃ a, blockCharacter i j a ≠ 0) ∧
    ∀ p q : ℤ, 0 < p → 0 < q →
      (∀ a, p * blockCharacter i j a = q * blockCharacter k l a) →
      i = k ∧ j = l ∧ p = q

/-- Under a given splitting of the division algebra, the matrix splitting has
ordered pairs of block and within-block indices. The original norm is its
determinant. The parameterized block is the product of the indicated absolute
root matrices. -/
def BlockSplitting : Prop :=
  ∀ {F B K R : Type*} [Field F] [DivisionRing B] [Algebra F B] [Field K] [Algebra F K]
    [CommRing R] [Algebra F R] [Algebra K R] [IsScalarTower F K R]
    {d m : ℕ} (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)),
    ∃ (E : R ⊗[F] B ≃ₐ[R] Matrix (Fin d) (Fin d) R)
      (D : R ⊗[F] Matrix (Fin m) (Fin m) B ≃ₐ[R] Matrix (Fin m × Fin d) (Fin m × Fin d) R),
      (∀ (r : R) (x : B), E (r ⊗ₜ[F] x) = r • (e (1 ⊗ₜ[F] x)).map (algebraMap K R)) ∧
      (∀ x, normAt hA b x = (D x).det) ∧
      (∀ t, D (scalarDiagonal (F := F) (B := B) t) = Matrix.diagonal (fun p => t p.1)) ∧
      ∀ (i j : Fin m) (x : R ⊗[F] B), i ≠ j →
        ∃ l : List (Fin d × Fin d), l.Nodup ∧ l.toFinset = Finset.univ ∧
          D (1 + blockEntry i j x) =
            (l.map (fun p => Matrix.transvection (i, p.1) (j, p.2) (E x p.1 p.2))).prod

/-- A model of the F05 norm-one functor, with its multiplication and change of
coefficients specified on the original tensor algebra. -/
structure NormOnePoints {F B : Type u} [Field F] [Ring B] [Algebra F B]
    {m : ℕ} (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) where
  point : ∀ R : LinearAlgebraicGroups.TestAlgebra F,
    ((LinearAlgebraicGroups.groupPointsFunctor F).obj H.val).obj R ≃ {x : R ⊗[F] Matrix (Fin m) (Fin m) B // normAt hA b x = 1}
  one : ∀ R, (point R 1).val = 1
  mul : ∀ R (x y : ((LinearAlgebraicGroups.groupPointsFunctor F).obj H.val).obj R), (point R (x * y)).val = (point R x).val * (point R y).val
  natural : ∀ {R T : LinearAlgebraicGroups.TestAlgebra F} (f : R ⟶ T) (x : ((LinearAlgebraicGroups.groupPointsFunctor F).obj H.val).obj R),
    (point T (LinearAlgebraicGroups.mapPoints f x)).val =
      Algebra.TensorProduct.map f.hom (AlgHom.id F _) (point R x).val

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots characterValue pairing)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open Relative.RelativeReflections (RootCentralizer)
open LinearAlgebraicGroups.CocharacterDynamics (HasLimit cocharacterPoint)

variable {m : ℕ} {F₀ B₀ : Type u} [Field F₀] [Ring B₀] [Algebra F₀ B₀]

/-- The determinant-one scalar tuples, with their ordinary pointwise product. -/
def diagonalTuples (m : ℕ) (R : Type u) [CommRing R] : Subgroup (Fin m → Rˣ) :=
  (show (Fin m → Rˣ) →* Rˣ from
    { toFun := fun t => ∏ i, t i
      map_one' := by simp
      map_mul' := fun t v => Finset.prod_mul_distrib }).ker

/-- The specified scalar diagonal is a presentation on all test algebras. -/
structure ScalarDiagonalModel
    {hA : isCentralSimple F₀ (Matrix (Fin m) (Fin m) B₀)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F₀ (Matrix (Fin m) (Fin m) B₀)}
    {H : AffineAlgebraicGroup F₀} (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val) where
  tuple : ∀ R : TestAlgebra F₀, GroupPoints S.group R ≃* diagonalTuples m R
  natural : ∀ {R T : TestAlgebra F₀} (f : R ⟶ T) (t : GroupPoints S.group R) (i : Fin m),
    (tuple T (mapPoints f t)).val i = Units.map f.hom.toMonoidHom ((tuple R t).val i)
  diagonal : ∀ (R : TestAlgebra F₀) (t : GroupPoints S.group R),
    (P.point R (t ≫ S.inclusion.hom.hom)).val =
      scalarDiagonal fun i => ((tuple R t).val i : R)

/-- A character is the indicated ratio on the entire test-algebra functor. -/
def IsBlockCharacter
    {hA : isCentralSimple F₀ (Matrix (Fin m) (Fin m) B₀)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F₀ (Matrix (Fin m) (Fin m) B₀)}
    {H : AffineAlgebraicGroup F₀} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (D : ScalarDiagonalModel P S) (i j : Fin m) (a : Character S.group) : Prop :=
  ∀ (R : TestAlgebra F₀) (t : GroupPoints S.group R),
    characterValue a R t = (((D.tuple R t).val i / (D.tuple R t).val j : Rˣ) : R)

/-- The roots are exactly the off-diagonal ratios, with the rank-zero case
included by the empty range of unequal pairs. -/
def RelativeRootCalculation : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (_hB : isCentralSimple F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val),
    IsMaximalSplitTorus S → ∀ D : ScalarDiagonalModel P S,
    ∀ a : Character S.group,
      a ∈ relativeRoots S ↔ ∃ i j : Fin m, i ≠ j ∧ IsBlockCharacter D i j a

/-- Centralization of the full character kernel, tested after every map out
of the base algebra of the point. -/
def CentralizesCharacterKernel {F : Type u} [Field F] {G : GroupScheme F}
    (S : ClosedSubgroup G) (a : Character S.group) {R : TestAlgebra F}
    (g : GroupPoints G R) : Prop :=
  ∀ (T : TestAlgebra F) (f : R ⟶ T) (t : GroupPoints S.group T),
    characterValue a T t = 1 →
    Commute (show GroupPoints G T from mapPoints f g)
      (show GroupPoints G T from t ≫ S.inclusion.hom.hom)

/-- Contraction inside the full kernel centralizer, expressed directly as a
condition on the functor of points. -/
def FullKernelContraction : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (_hB : isCentralSimple F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val),
    IsMaximalSplitTorus S → ∀ (D : ScalarDiagonalModel P S) (i j : Fin m), i ≠ j →
    ∀ (a : relativeRoots S), IsBlockCharacter D i j a.val →
    ∀ (c : Cocharacter S.group), 0 < pairing S.group a.val c →
    ∀ (R : TestAlgebra F) (g : GroupPoints H.val R),
      (CentralizesCharacterKernel S a.val g ∧ HasLimit (c ≫ S.inclusion) g 1) ↔
      ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x

/-- The positive contracting group in the identity component of the full
kernel centralizer is the additive block. The cocharacter may be any
cocharacter with strictly positive pairing with the ratio. -/
def RelativeContraction : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (_hB : isCentralSimple F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val),
    IsMaximalSplitTorus S → ∀ (D : ScalarDiagonalModel P S) (i j : Fin m), i ≠ j →
    ∀ (a : relativeRoots S), IsBlockCharacter D i j a.val →
    ∀ (C : RootCentralizer S a) (c : Cocharacter S.group), 0 < pairing S.group a.val c →
    ∀ (R : TestAlgebra F) (g : GroupPoints H.val R),
      ((∃ q : GroupPoints C.component.group R,
        q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom = g) ∧
        HasLimit (c ≫ S.inclusion) g 1) ↔
      ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x

/-- The same contracting group, with the polynomial limit taken in the
identity component of the full kernel centralizer. -/
def ComponentContraction : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (_hB : isCentralSimple F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val),
    IsMaximalSplitTorus S → ∀ (D : ScalarDiagonalModel P S) (i j : Fin m), i ≠ j →
    ∀ (a : relativeRoots S), IsBlockCharacter D i j a.val →
    ∀ (C : RootCentralizer S a) (c : Cocharacter S.group), 0 < pairing S.group a.val c →
    ∀ (R : TestAlgebra F) (g : GroupPoints H.val R),
      (∃ q : GroupPoints C.component.group R,
        q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom = g ∧
        HasLimit (c ≫ C.torusIso.hom ≫ C.torus.inclusion) q 1) ↔
      ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x

/-- The norm-one point model obtained from F05 with its coordinate evaluations. -/
def F05NormOnePoints : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)),
    let A := LinearAlgebraicGroups.Descent.InnerTypeA.Specification.NormOneCoordinates hA b
    ∃ h : StandardGroups.HopfOperations F A,
      let H := @StandardGroups.spectrum F _ A _ h.hopf inferInstance
      ∃ P : NormOnePoints hA b H,
        ∀ (R : TestAlgebra F) (f : A →ₐ[F] R) (g : GroupPoints H.val R),
          (show Points H.val.X R from g).left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ l, (b.baseChange R).repr (P.point R g).val l =
            f (Ideal.Quotient.mk
              (LinearAlgebraicGroups.Descent.InnerTypeA.Specification.normOneIdeal hA b)
              (MvPolynomial.X l))

/-- The block splitting identifies the F05 group after scalar extension with
the split special linear group, naturally on test algebras. In these
coordinates the original torus repeats its scalar in each block. -/
def BlockSplitPoints : Prop :=
  ∀ {F B K : Type u} [Field F] [DivisionRing B] [Algebra F B] [Field K] [Algebra F K]
    {m d : ℕ} (e : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H),
    let κ := ULift.{u} (Fin m × Fin d)
    let H_K := Unipotent.baseChangedAlgebraicGroup K H
    ∃ M : (groupPointsFunctor K).obj H_K.val ≅ StandardGroups.specialLinearPoints K κ,
      ∀ (S : ClosedSubgroup H.val) (D : ScalarDiagonalModel P S) (R : TestAlgebra K)
        (t : GroupPoints ((groupBaseChange F K).obj S.group) R),
        (show Matrix.SpecialLinearGroup κ R from
          M.hom.app R (t ≫ ((groupBaseChange F K).map S.inclusion).hom.hom)).val =
          Matrix.diagonal (fun p => ((D.tuple (restrictTestAlgebraObj F K R)
            (baseChangePoint F K S.group.X R t)).val p.down.1 : R))

/-- The actual block characters and integral diagonal cocharacters realizing
their pairing. The construction includes the positive exponent 2 for each ray. -/
def RelativeRootPairing : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B] {m : ℕ}
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val)
    (D : ScalarDiagonalModel P S),
    ∃ (α : Fin m → Fin m → Character S.group) (c : DiagonalCocharacter m → Cocharacter S.group),
      (∀ i j, IsBlockCharacter D i j (α i j)) ∧
      (∀ w (R : TestAlgebra F) (t : Rˣ) i, (D.tuple R (cocharacterPoint (c w) R t)).val i =
        t ^ w.val i) ∧
      (∀ i j w, pairing S.group (α i j) (c w) = blockCharacter i j w) ∧
      ∀ i j, i ≠ j → ∃ w, pairing S.group (α i j) (c w) = 2

/-- The actual absolute root characters of the split special linear model,
with respect to its full determinant-one diagonal torus. The rows may be
indexed by pairs by choosing the corresponding enumeration. -/
def SplitAbsoluteRootCalculation : Prop :=
  ∀ {K : Type u} [Field K] {κ : Type u} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    {N : ℕ} (e : κ ≃ Fin N) (G : AffineAlgebraicGroup K)
    (P : (groupPointsFunctor K).obj G.val ≅ StandardGroups.specialLinearPoints K κ)
    (T : ClosedSubgroup G.val) (t : ∀ R : TestAlgebra K, GroupPoints T.group R ≃* diagonalTuples N R),
    GeometricRadicals.IsSplitTorus T.group →
    (∀ {R S : TestAlgebra K} (f : R ⟶ S) (x : GroupPoints T.group R) i,
      (t S (mapPoints f x)).val i = Units.map f.hom.toMonoidHom ((t R x).val i)) →
    (∀ (R : TestAlgebra K) (x : GroupPoints T.group R),
      (show Matrix.SpecialLinearGroup κ R from P.hom.app R (x ≫ T.inclusion.hom.hom)).val =
        Matrix.diagonal (fun p => ((t R x).val (e p) : R))) →
    ∃ α : κ → κ → Character T.group,
      (∀ p q (R : TestAlgebra K) (x : GroupPoints T.group R),
        characterValue (α p q) R x = (((t R x).val (e p) / (t R x).val (e q) : Rˣ) : R)) ∧
      ∀ a : Character T.group, a ∈ absoluteRoots T ↔ ∃ p q, p ≠ q ∧ a = α p q

/-- In the split special linear coordinates of BlockSplitting, the root at
(p,q) has character the quotient of diagonal coordinates p and q. Its pullback
along the block-scalar diagonal depends on their first coordinates. Testing
powers on all test algebras identifies precisely the absolute roots on each
positive relative ray. -/
def SplitAbsoluteRootRestrictions : Prop :=
  ∀ (F : Type u) [Field F] {m d : ℕ} (p q : Fin m × Fin d), p ≠ q →
    ((∀ (R : TestAlgebra F) (t : diagonalTuples m R), t.val p.1 / t.val q.1 = 1) ↔ p.1 = q.1) ∧
    ∀ (i j : Fin m), i ≠ j → ∀ (a b : ℤ), 0 < a → 0 < b →
      ((∀ (R : TestAlgebra F) (t : diagonalTuples m R),
          (t.val p.1 / t.val q.1) ^ a = (t.val i / t.val j) ^ b) ↔
        p.1 = i ∧ q.1 = j ∧ a = b)

end LinearAlgebraicGroups.Specs.InnerTypeARelativeContraction
