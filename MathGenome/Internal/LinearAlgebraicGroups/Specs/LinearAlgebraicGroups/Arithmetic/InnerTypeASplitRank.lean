import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeATorusWeightProjections
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeARelativeContraction
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Matrix.Transvection

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct BigOperators Matrix

universe u

namespace LinearAlgebraicGroups.Specs.InnerTypeASplitRank

open InnerTypeATorusWeightProjections (PointRepresentation)
open InnerTypeARelativeContraction (NormOnePoints ScalarDiagonalModel IsBlockCharacter
  CentralizesCharacterKernel diagonalTuples)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots characterValue pairing)
open GeometricRadicals (IsSplitTorus)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (relativeRoots)
open Relative.RelativeReflections (RootCentralizer)
open LinearAlgebraicGroups.CocharacterDynamics (HasLimit)
open Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open _root_.Specs.RM03.CSA (isCentralSimple isCentralDivision degree)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

open InnerTypeARelativeContraction
  (scalarDiagonal blockEntry blockProjection DiagonalCocharacter blockCharacter)
open LinearAlgebraicGroups.Arithmetic.InnerTypeAClosedDiagonal.Specification (determinantOneTuple)

/-- Left and right multiplication by central scalar diagonals acts entrywise.
For a tuple of units and its inverse this gives the actual character ratio on
each block over any test algebra. -/
def DiagonalAction : Prop :=
  ∀ {F B R : Type*} [Field F] [Ring B] [Algebra F B] [CommRing R] [Algebra F R]
    {m : ℕ} (t u : Fin m → R) (x : R ⊗[F] Matrix (Fin m) (Fin m) B) (i j : Fin m),
    blockProjection i j (scalarDiagonal t * x * scalarDiagonal u) =
      (t i * u j) • blockProjection i j x

/-- The F05 polynomial on a scalar diagonal is the product of the scalars, raised
to the degree of the division algebra. This holds on arbitrary test algebras. -/
def DiagonalNorm : Prop :=
  ∀ {F B R : Type*} [Field F] [DivisionRing B] [Algebra F B] [CommRing R] [Algebra F R]
    (_hB : isCentralSimple F B) {m : ℕ} (_hm : 0 < m)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (t : Fin m → R),
    normAt hA b (scalarDiagonal (F := F) (B := B) t) = (∏ i, t i) ^ degree F B

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

/-- The diagonal split torus of rank n, at all test algebras. -/
def CentralDiagonal : Prop :=
  ∀ {F B R : Type*} [Field F] [DivisionRing B] [Algebra F B] [CommRing R] [Algebra F R]
    (_hB : isCentralSimple F B) (n : ℕ)
    (hA : isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin (n + 1)) (Fin (n + 1)) B)),
    let D := fun t : Fin n → Rˣ =>
      scalarDiagonal (F := F) (B := B) (fun i => (↑(determinantOneTuple t i) : R))
    D 1 = 1 ∧ Function.Injective D ∧ (∀ t u, D (t * u) = D t * D u) ∧
    (∀ t, normAt hA b (D t) = 1) ∧
    ∀ a : Fin (n + 1) → Rˣ, (∏ i, a i) = 1 ↔ ∃ t, determinantOneTuple t = a

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

/-- Once the weights on the division-module basis detect all cocharacters, the
norm-one relation bounds the rank. A weight occurs once per basis vector in
its weight space. -/
def DiagonalRankBound : Prop :=
  ∀ {F B : Type*} [Field F] [DivisionRing B] [Algebra F B]
    (_hB : isCentralSimple F B) {m r : ℕ} (_hm : 0 < m)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type*} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (w : Fin m → Fin r → ℤ),
    (∀ c : Fin r → ℤ, (∀ i, ∑ j, w i j * c j = 0) → c = 0) →
    normAt hA b
      (scalarDiagonal (F := F) (B := B)
        (fun i => MonoidAlgebra.of F (Multiplicative (Fin r → ℤ)) (Multiplicative.ofAdd (w i)))) = 1 →
    r ≤ m - 1

/-- A finite family of mutually orthogonal matrix projections gives a
basis of the right division module adapted to their images. -/
def ProjectionBasis : Prop := by
  classical
  exact ∀ {D W : Type*} [DivisionRing D] [Fintype W] {m : ℕ}
    (P : W → Matrix (Fin m) (Fin m) D),
    (∑ a, P a) = 1 →
    (∀ a b, P a * P b = if a = b then P a else 0) →
    ∃ (v : Module.Basis (Fin m) Dᵐᵒᵖ (Fin m → D)) (label : Fin m → W),
      ∀ a i, P a *ᵥ v i = if a = label i then v i else 0

/-- The norm polynomial is defined for every positive-size matrix algebra
over the central division algebra in the rank statement. -/
def CentralSimpleMatrix : Prop :=
  ∀ {F B : Type*} [Field F] [Ring B] [Algebra F B] {m : ℕ},
    0 < m → isCentralSimple F B → isCentralSimple F (Matrix (Fin m) (Fin m) B)

/-- The weight space in the right division module, written as a left module
over the opposite division ring. -/
def weightSpace {B : Type*} [DivisionRing B] {m : ℕ}
    (P : Matrix (Fin m) (Fin m) B) : Submodule Bᵐᵒᵖ (Fin m → B) :=
  LinearMap.range (Matrix.mulVecBilin B Bᵐᵒᵖ P)

/-- The matrix representation obtained by evaluating a split torus embedding
on character-valued points. -/
noncomputable def splitTorusAction {F B J : Type u} [Field F] [DivisionRing B]
    [Algebra F B] [Fintype J] {m : ℕ}
    {hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} (P : NormOnePoints hA b H)
    (T : ClosedSubgroup H.val)
    (a : (groupPointsFunctor F).obj T.group ≅
      DiagonalizableGroups.characterValuedPoints F (Multiplicative (J → ℤ))) :
    PointRepresentation F (Multiplicative (J → ℤ)) (Matrix (Fin m) (Fin m) B) :=
  fun R =>
    (show ((groupPointsFunctor F).obj H.val).obj R →* (R ⊗[F] Matrix (Fin m) (Fin m) B) from
      { toFun := fun x => (P.point R x).val
        map_one' := P.one R
        map_mul' := P.mul R }).comp
      ((((groupPointsFunctor F).map T.inclusion).app R).hom.comp (a.inv.app R).hom)

/-- The weights of an arbitrary split torus of the norm-one group are the
support of its matrix coefficient expansion on all test algebras. They
generate the character lattice. Their right-division-module dimensions give
the exponents of the norm character, which is trivial. -/
def SplitTorusWeights : Prop := by
  classical
  exact ∀ {F B J : Type u} [Field F] [DivisionRing B] [Algebra F B] [Fintype J]
    {m : ℕ} (hm : 0 < m) (_hB : isCentralDivision F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H)
    (T : ClosedSubgroup H.val),
    Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup F J).val) →
    ∃ a : (groupPointsFunctor F).obj T.group ≅
        DiagonalizableGroups.characterValuedPoints F (Multiplicative (J → ℤ)),
      let ρ := splitTorusAction P T a
      let M := Multiplicative (J → ℤ)
      ∃ Q : M →₀ Matrix (Fin m) (Fin m) B,
        (∀ a b, Q a * Q b = if a = b then Q a else 0) ∧
        (∑ a ∈ Q.support, Q a) = 1 ∧
        (∀ (R : TestAlgebra F) (t : M →* Rˣ),
          ρ R t = ∑ a ∈ Q.support, ((t a : R) ⊗ₜ[F] Q a)) ∧
        Subgroup.closure (↑Q.support : Set M) = ⊤ ∧
        let W := ↥Q.support
        let multiplicity := fun a : W => Module.finrank Bᵐᵒᵖ (weightSpace (Q a.val))
        Submodule.span ℚ (Set.range (fun (a : W) (j : J) => (a.val.toAdd j : ℚ))) = ⊤ ∧
        DirectSum.IsInternal (fun a : W => weightSpace (Q a.val)) ∧
        (∀ (a : W) (x : Fin m → B), x ∈ weightSpace (Q a.val) ↔
          ∀ c : W, Q c.val *ᵥ x = if c = a then x else 0) ∧
        (∀ a, 0 < multiplicity a) ∧
        (∑ a, multiplicity a) = m ∧
        (∃ (v : Module.Basis (Fin m) Bᵐᵒᵖ (Fin m → B)) (label : Fin m → W),
          (∀ a i, Q a.val *ᵥ v i = if a = label i then v i else 0) ∧
          ∀ a, Nat.card {i // label i = a} = multiplicity a) ∧
        (∀ (R : TestAlgebra F) (t : M →* Rˣ),
          normAt hA b (ρ R t) =
            ∏ a : W, (t a.val : R) ^ (degree F B * multiplicity a)) ∧
        (∏ a : W, a.val ^ (degree F B * multiplicity a)) = 1 ∧
        Fintype.card J ≤ Q.support.card - 1 ∧ Q.support.card ≤ m

/-- The full character-kernel centralizer and its actual identity component
exist. Its points contracted along the root ray are exactly the block points. -/
def BlockIdentityComponent {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} {hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (_D : ScalarDiagonalModel P S) (i j : Fin m) (a : relativeRoots S) : Prop :=
  ∃ (K : ClosedSubgroup S.group) (Z : ClosedSubgroup H.val) (Z₀ : ClosedSubgroup Z.group),
    IsSchemeKernel a.val K ∧
    RepresentsSubgroup Z (fun _ g => Centralizes (K.inclusion ≫ S.inclusion) g) ∧
    IsOpenImmersion Z₀.inclusion.hom.hom.left ∧
    Set.range Z₀.inclusion.hom.hom.left = connectedComponent ((MonObj.one (X := Z.group.X)).left (IsLocalRing.closedPoint F)) ∧
    ∀ (c : Cocharacter S.group), 0 < pairing S.group a.val c →
      ∀ (R : TestAlgebra F) (g : GroupPoints H.val R),
        ((∃ q : GroupPoints Z₀.group R, q ≫ Z₀.inclusion.hom.hom ≫ Z.inclusion.hom.hom = g) ∧
          HasLimit (c ≫ S.inclusion) g 1) ↔
        ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x

/-- The relative roots of the standard diagonal and the contracting group
along each positive ray. The kernel condition is tested after arbitrary
change of test algebra, including when the character kernel is nonsmooth. -/
def RelativeBlockDescription {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} {hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (D : ScalarDiagonalModel P S) : Prop :=
  ∃ (α : Fin m → Fin m → Character S.group)
    (ha : ∀ i j, i ≠ j → α i j ∈ relativeRoots S),
    (∀ i j, IsBlockCharacter D i j (α i j)) ∧
    (∀ a : Character S.group, a ∈ relativeRoots S ↔ ∃ i j, i ≠ j ∧ a = α i j) ∧
    (∀ i j, i ≠ j → ∃ c, pairing S.group (α i j) c = 2) ∧
    (∀ i j (hij : i ≠ j), BlockIdentityComponent D i j ⟨α i j, ha i j hij⟩) ∧
    ∀ i j (hij : i ≠ j) (c : Cocharacter S.group), 0 < pairing S.group (α i j) c →
    ∀ (R : TestAlgebra F) (g : GroupPoints H.val R),
      ((CentralizesCharacterKernel S (α i j) g ∧ HasLimit (c ≫ S.inclusion) g 1) ↔
        ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x) ∧
      ∀ (C : RootCentralizer S ⟨α i j, ha i j hij⟩),
        (∃ q : GroupPoints C.component.group R,
          q ≫ C.component.inclusion.hom.hom ≫ C.centralizer.inclusion.hom.hom = g ∧
          HasLimit (c ≫ C.torusIso.hom ≫ C.torus.inclusion) q 1) ↔
        ∃! x : R ⊗[F] B, (P.point R g).val = 1 + blockEntry i j x

/-- In the split matrix group the full diagonal torus contains the extended
scalar diagonal. Restricting the absolute root for (p,q) gives the ratio of
their block coordinates. Testing powers on all test algebras gives exactly
the absolute roots on each positive relative ray. The original block
transvection is the product of the corresponding entry transvections in
these same coordinates. -/
def AbsoluteBlockRoots {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} {hA : isCentralSimple F (Matrix (Fin m) (Fin m) B)}
    {ι : Type u} [Fintype ι] {b : Module.Basis ι F (Matrix (Fin m) (Fin m) B)}
    {H : AffineAlgebraicGroup F} {P : NormOnePoints hA b H} {S : ClosedSubgroup H.val}
    (D : ScalarDiagonalModel P S) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra F K] {d : ℕ}
    (s : K ⊗[F] B ≃ₐ[K] Matrix (Fin d) (Fin d) K),
    let G := Unipotent.baseChangedAlgebraicGroup K H
    let S_K := (groupBaseChange F K).obj S.group
    let κ := ULift.{u} (Fin m × Fin d)
    ∃ (M : (groupPointsFunctor K).obj G.val ≅ StandardGroups.specialLinearPoints K κ)
      (T : ClosedSubgroup G.val) (j : S_K ⟶ T.group)
      (t : ∀ R : TestAlgebra K, GroupPoints T.group R ≃* diagonalTuples (m * d) R)
      (e : κ ≃ Fin (m * d)) (β : κ → κ → Character T.group),
      IsSplitTorus T.group ∧ j ≫ T.inclusion = (groupBaseChange F K).map S.inclusion ∧
      (∀ (R : TestAlgebra K) (x : GroupPoints T.group R),
        (show Matrix.SpecialLinearGroup κ R from M.hom.app R (x ≫ T.inclusion.hom.hom)).val =
          Matrix.diagonal (fun p => ((t R x).val (e p) : R))) ∧
      (∀ p q (R : TestAlgebra K) (x : GroupPoints T.group R),
        characterValue (β p q) R x = (((t R x).val (e p) / (t R x).val (e q) : Rˣ) : R)) ∧
      (∀ a : Character T.group, a ∈ absoluteRoots T ↔ ∃ p q, p ≠ q ∧ a = β p q) ∧
      (∀ p q (R : TestAlgebra K) (x : GroupPoints S_K R),
        let z := D.tuple (restrictTestAlgebraObj F K R) (baseChangePoint F K S.group.X R x)
        characterValue (j ≫ β p q) R x = ((z.val p.down.1 / z.val q.down.1 : Rˣ) : R)) ∧
      (∀ (R : TestAlgebra K) (z : diagonalTuples m R), ∃ x : GroupPoints S_K R,
        D.tuple (restrictTestAlgebraObj F K R) (baseChangePoint F K S.group.X R x) = z) ∧
      (∀ (R : TestAlgebra K),
        let R_F := restrictTestAlgebraObj F K R
        ∃ C : R_F ⊗[F] B ≃ₐ[R] Matrix (Fin d) (Fin d) R,
          (∀ (r : R_F) (x : B),
            C (r ⊗ₜ[F] x) = r • (s (1 ⊗ₜ[F] x)).map (algebraMap K R)) ∧
          ∀ (i j : Fin m), i ≠ j → ∀ (x : R_F ⊗[F] B),
            ∃ l : List (Fin d × Fin d), l.Nodup ∧ l.toFinset = Finset.univ ∧
              ∀ (g : GroupPoints G.val R),
                (P.point R_F (baseChangePoint F K H.val.X R g)).val = 1 + blockEntry i j x ↔
                  (show Matrix.SpecialLinearGroup κ R from M.hom.app R g).val =
                    (l.map (fun p => Matrix.transvection (⟨i, p.1⟩ : κ)
                      (⟨j, p.2⟩ : κ) (C x p.1 p.2))).prod) ∧
      ∀ p q : κ, p ≠ q →
        ((∀ (R : TestAlgebra K) (z : diagonalTuples m R), z.val p.down.1 / z.val q.down.1 = 1) ↔
          p.down.1 = q.down.1) ∧
        ∀ i j : Fin m, i ≠ j → ∀ a b : ℤ, 0 < a → 0 < b →
          ((∀ (R : TestAlgebra K) (z : diagonalTuples m R),
            (z.val p.down.1 / z.val q.down.1) ^ a = (z.val i / z.val j) ^ b) ↔
            p.down.1 = i ∧ q.down.1 = j ∧ a = b)

/-- The split rank of the F05 model is n for matrix size n + 1. Its
maximal split subgroup is the standard product-one diagonal, with its
description on every test algebra. The coordinate evaluation fixes the
identification with the F05 norm-one scheme. -/
def SplitRank : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    (n : ℕ) (_hB : isCentralDivision F B)
    (hA : isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin (n + 1)) (Fin (n + 1)) B)),
    let A := NormOneCoordinates hA b
    ∃ h : StandardGroups.HopfOperations F A,
      let H := @StandardGroups.spectrum F _ A _ h.hopf inferInstance
      ∃ (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val),
        (∀ (R : TestAlgebra F) (f : A →ₐ[F] R) (g : Points H.val.X R),
          g.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ l, (b.baseChange R).repr (P.point R g).val l =
            f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X l))) ∧
        Nonempty (S.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin n))).val) ∧
        IsMaximalSplitTorus S ∧
        (∃ D : ScalarDiagonalModel P S, RelativeBlockDescription D) ∧
        ∀ (r : ℕ) (T : ClosedSubgroup H.val),
          Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val) →
          r ≤ n

/-- The absolute-root description is available for every F05-compatible
point model and every determinant-one scalar diagonal in it. -/
def SplitAbsoluteBlocks : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    {m : ℕ} (_hm : 0 < m) (_hB : isCentralDivision F B)
    (hA : isCentralSimple F (Matrix (Fin m) (Fin m) B))
    {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin m) (Fin m) B))
    (H : AffineAlgebraicGroup F) (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val)
    (D : ScalarDiagonalModel P S), AbsoluteBlockRoots D

/-- The rank and root descriptions hold for the same closed diagonal in the
F05 group for every positive matrix size. The rank is the largest exponent
of a split multiplicative power embedding as a closed subgroup. -/
def SplitRankAndRoots : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    (n : ℕ) (_hB : isCentralDivision F B),
    ∃ hA : isCentralSimple F (Matrix (Fin (n + 1)) (Fin (n + 1)) B),
    ∀ {ι : Type u} [Fintype ι] (b : Module.Basis ι F (Matrix (Fin (n + 1)) (Fin (n + 1)) B)),
    let A := NormOneCoordinates hA b
    ∃ h : StandardGroups.HopfOperations F A,
      let H := @StandardGroups.spectrum F _ A _ h.hopf inferInstance
      ∃ (P : NormOnePoints hA b H) (S : ClosedSubgroup H.val) (D : ScalarDiagonalModel P S),
        (∀ (R : TestAlgebra F) (f : A →ₐ[F] R) (g : Points H.val.X R),
          g.left = Spec.map (CommRingCat.ofHom f.toRingHom) →
          ∀ l, (b.baseChange R).repr (P.point R g).val l =
            f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X l))) ∧
        Nonempty (S.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin n))).val) ∧
        IsMaximalSplitTorus S ∧ RelativeBlockDescription D ∧ AbsoluteBlockRoots D ∧
        ∀ (r : ℕ) (T : ClosedSubgroup H.val),
          Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val) →
          r ≤ n

end LinearAlgebraicGroups.Specs.InnerTypeASplitRank
