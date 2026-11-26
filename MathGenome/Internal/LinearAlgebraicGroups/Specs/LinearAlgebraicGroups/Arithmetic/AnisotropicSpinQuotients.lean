import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.KummerObstructions
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor

open AlgebraicGeometry CategoryTheory Filter
open scoped RestrictedProduct

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSpinQuotients

open LinearAlgebraicGroups.Arithmetic
open AdelicGroups
open IntegralModels (MatrixRealization RationalPoints)


/-- The point map of the given group-scheme morphism over a test algebra. -/
noncomputable abbrev pointMap.{u} {K : Type u} [Field K] {G H : AffineAlgebraicGroup K}
    (f : G.val ⟶ H.val) (i : MatrixRealization G) (j : MatrixRealization H)
    (L : Type u) [CommRing L] [Algebra K L] : PointsIn i L →* PointsIn j L :=
  (((groupPointsFunctor K).map f).app (CommAlgCat.of K L)).hom

/-- Finite morphisms have compact inverse images on the full restricted products
of points, in the topologies from the given closed matrix realizations. -/
def FiniteAdelicMorphism.{u,v} : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    {G H : AffineAlgebraicGroup K} (f : G.val ⟶ H.val),
    IsFinite f.hom.hom.left →
    ∀ (i : MatrixRealization G) (j : MatrixRealization H),
    ∃ F : Adeles D i ∅ →* Adeles D j ∅,
      (∀ (x : Adeles D i ∅) (w : Outside D ∅),
        F x w = pointMap f i j (D.Completion w.val) (x w)) ∧
      Continuous F ∧ ∀ C : Set (Adeles D j ∅), IsCompact C → IsCompact (F ⁻¹' C)

/-- A compact set in the full restricted product satisfies a common finite
exception set for the integrality of all its members. -/
def CompactAlmostEverywhereIntegral.{u,v} : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    {H : AffineAlgebraicGroup K} (j : MatrixRealization H)
    (C : Set (Adeles D j ∅)), IsCompact C →
    ∃ S : Set D.Place, S.Finite ∧
      ∀ c ∈ C, ∀ (w : Outside D ∅), w.val ∉ S → c w ∈ localSubgroup D j w.val

/-- Cocompactness transfers to a covering group if the compact representative
set is met using only finitely many obstruction classes. Triviality of the
obstruction is equivalent to lifting a rational point. -/
def CompactOfCoverReduction.{u} : Prop :=
  ∀ {G H P Q E : Type u} [Group G] [Group H] [Group P] [Group Q] [Group E]
    [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup G] [IsTopologicalGroup H]
    (F : G →* H) (f : P →* Q) (dG : P →* G) (dH : Q →* H)
    (ν : Q →* E) (C : Set H) (A : Set E),
    (∀ p, F (dG p) = dH (f p)) →
    (∀ q, ν q = 1 ↔ q ∈ f.range) →
    IsCompact C → A.Finite →
    (∀ B : Set H, IsCompact B → IsCompact (F ⁻¹' B)) →
    (∀ g : G, ∃ q : Q, F g * dH q ∈ C ∧ ν q ∈ A) →
    CompactSpace (G ⧸ dG.range)

/-- The square-class correction for a finite spin cover. The local obstruction
is compatible with localization, kills the local image of the cover, and
comes from a unit on integral points at almost every finite place. -/
def CompactOfSquareClassReduction.{u,v} : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    {G H : AffineAlgebraicGroup K} (f : G.val ⟶ H.val)
    (i : MatrixRealization G) (j : MatrixRealization H)
    (dG : RationalPoints G →* Adeles D i ∅) (dH : RationalPoints H →* Adeles D j ∅),
    (∀ (g : RationalPoints G) (w : Outside D ∅), dG g w = localPoint D i w.val g) →
    (∀ (h : RationalPoints H) (w : Outside D ∅), dH h w = localPoint D j w.val h) →
    IsFinite f.hom.hom.left →
    ∀ (ν : RationalPoints H →* Kummer.Classes K 2)
      (νw : ∀ w : D.FinitePlace, LocalPoints D j (.inl w) →*
        Kummer.Classes (D.FiniteCompletion w) 2),
    (∀ h, ν h = 1 ↔ h ∈ (pointMap f i j K).range) →
    (∀ w h, νw w (localPoint D j (.inl w) h) =
      Kummer.map (D.embedding (.inl w)) 2 (ν h)) →
    (∀ w x, νw w (pointMap f i j (D.Completion (.inl w)) x) = 1) →
    (∀ᶠ w in Filter.cofinite, ∀ x ∈ integralPoints D j w,
      νw w x ∈ (Kummer.map (D.integers w).subtype 2).range) →
    ∀ C : Set (Adeles D j ∅), IsCompact C →
      (∀ x : Adeles D i ∅, ∃ h : RationalPoints H, ∃ c ∈ C,
        ∀ w : Outside D ∅,
          c w = pointMap f i j (D.Completion w.val) (x w) * dH h w) →
      CompactSpace (Adeles D i ∅ ⧸ dG.range)


section QuadraticModels

open Albert.SpinSpecification (IsSpinPointRepresentation ScalarClifford)
open Unipotent (Index)
open scoped TensorProduct CategoryTheory.MonObj

/-- Over a field the polar form is either nondegenerate or, in characteristic
two, has a single radical line on which the quadratic form is nonzero. -/
def RegularModel {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (r : Option V) : Prop :=
  match r with
  | none => LinearMap.ker q.polarBilin = ⊥
  | some x => (2 : K) = 0 ∧ q x ≠ 0 ∧ LinearMap.ker q.polarBilin = K ∙ x

/-- A closed realization of the orthogonal target on the original quadratic
space. In the radical case this is the stabilizer of the marked vector. Over
number fields the oriented volume is part of the defining tensors. -/
def IsOrthogonalRealization.{u} {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (r : Option V) (oriented : Bool)
    {O : AffineAlgebraicGroup K} (j : MatrixRealization O)
    (b : Module.Basis (Index.{u} j.size) K V) : Prop :=
  ∀ (L : Type u) [CommRing L] [Algebra K L]
    (m : Matrix.GeneralLinearGroup (Index.{u} j.size) L),
    m ∈ (asMatrix j L).range ↔
    let Q := Albert.CliffordSpecification.coefficientForm L q b
    let a := (Matrix.GeneralLinearGroup.toLin' (b.baseChange L) m).toLinearEquiv
    (∀ x, Q (a x) = Q x) ∧
      (∀ x, r = some x → a (1 ⊗ₜ[K] x) = 1 ⊗ₜ[K] x) ∧
      (oriented = true → m.det = 1)

/-- The orthogonal reduction for the regular anisotropic quadratic model.
The representatives are in the established restricted product at all places. -/
def OrthogonalCompactRepresentatives.{u,v} : Prop :=
  ∀ {K V : Type u} [Field K] [AddCommGroup V] [Module K V]
    (D : GlobalFieldData.{u,v} K) (q : QuadraticForm K V) (r : Option V),
    RegularModel q r → (∀ x, q x = 0 → x = 0) →
    ∀ {O : AffineAlgebraicGroup K} (j : MatrixRealization O)
      (b : Module.Basis (Index.{u} j.size) K V),
    5 ≤ j.size →
    IsOrthogonalRealization q r (by cases D with | number _ => exact true | function _ _ => exact false) j b →
    ∃ C : Set (Adeles D j ∅), IsCompact C ∧ ∀ x : Adeles D j ∅,
      ∃ d : RationalPoints O, ∃ c ∈ C,
        ∀ w : Outside D ∅, c w = x w * localPoint D j w.val d

/-- Compactness of the full adelic quotient of the intrinsic spin model.
The identification gives its Clifford points on every commutative test
algebra, including those detecting the scalar kernel in characteristic two. -/
def AnisotropicSpinCompactnessOver.{u,v} {K : Type u} [Field K]
    (D : GlobalFieldData.{u,v} K) : Prop :=
  ∀ {V : Type u} [AddCommGroup V] [Module K V]
    (q : QuadraticForm K V) (r : Option V),
    RegularModel q r → (∀ x, q x = 0 → x = 0) →
    ∀ (n : ℕ) (_b : Module.Basis (Index.{u} n) K V), 5 ≤ n →
    ∀ (G : AffineAlgebraicGroup K)
      (e : ∀ L : CommAlgCat.{u} K,
        Albert.SpinSpecification.SchemePoints G.val L →* (ScalarClifford q L)ˣ),
    IsSpinPointRepresentation q G.val e →
    ∀ (i : MatrixRealization G)
      (d : RationalPoints G →* Adeles D i ∅),
    (∀ (g : RationalPoints G) (w : Outside D ∅), d g w = localPoint D i w.val g) →
    CompactSpace (Adeles D i ∅ ⧸ d.range)

/-- The assertion over both forms of global field. -/
def AnisotropicSpinCompactness.{u,v} : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K), AnisotropicSpinCompactnessOver D

/-- The global function-field case, with the same dimension and regularity
conditions and the full adelic topology. -/
def FunctionFieldSpinCompactness.{u,v} : Prop :=
  ∀ {K : Type u} [Field K] {F : Type v} [Field F] [Finite F] [Algebra F K]
    (t : SeparatingParameter F K), AnisotropicSpinCompactnessOver (.function F t)

end QuadraticModels

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSpinQuotients
