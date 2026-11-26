import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SplitSpin
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeometricRadicals
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Fintype.WithTopBot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.Algebra.Polynomial.Laurent

open CliffordAlgebra Module

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinCharTwoStabilizer

universe u v w i j

section Hyperplane

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {I : Type i} [LinearOrder I]

/-- A basis of the ambient space adapted to the inclusion of a hyperplane.
The extra basis vector is indexed by `⊤`. -/
structure AdaptedBasis (q : QuadraticForm R V) (Q : QuadraticForm R W)
    (J : q →qᵢ Q) (b : Basis I R V) (d : Basis (WithTop I) R W) (r : V) : Prop where
  coe_basis : ∀ a : I, d (a : WithTop I) = J (b a)
  polar_coord : Q.polarBilin (J r) = d.coord ⊤

/-- The inclusion identifies the intrinsic Clifford algebra of the hyperplane
with the full centralizer of the distinguished vector. The preceding basis
conditions hold for the hyperplane orthogonal to (e_0+f_0) in the split
even space and the extra vector (f_0). -/
def CliffordCentralizer : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W] {I : Type i} [LinearOrder I] [Fintype I]
    (q : QuadraticForm R V) (Q : QuadraticForm R W) (J : q →qᵢ Q)
    (b : Basis I R V) (d : Basis (WithTop I) R W) (r : V),
    (2 : R) = 0 → AdaptedBasis q Q J b d r →
    Function.Injective (CliffordAlgebra.map J) ∧
    ∀ a : CliffordAlgebra Q,
      Commute (ι Q (J r)) a ↔ ∃ x : CliffordAlgebra q, CliffordAlgebra.map J x = a

/-- Intrinsic even Clifford spin points, as in the scalar-extended normalizer
after identifying the base-changed Clifford algebra. -/
def IsIntrinsicSpin (q : QuadraticForm R V) (a : (CliffordAlgebra q)ˣ) : Prop :=
  (a : CliffordAlgebra q) ∈ evenOdd q 0 ∧ reverse (a : CliffordAlgebra q) * a = 1 ∧
    Set.MapsTo (fun x : CliffordAlgebra q => (a : CliffordAlgebra q) * x * ↑a⁻¹)
      (LinearMap.range (ι q)) (LinearMap.range (ι q)) ∧
    Set.MapsTo (fun x : CliffordAlgebra q => (↑a⁻¹ : CliffordAlgebra q) * x * a)
      (LinearMap.range (ι q)) (LinearMap.range (ι q))

/-- The actual conjugation on Clifford vectors of the hyperplane is intertwined
by the homomorphism induced by the inclusion. -/
def IntrinsicSpinComparison : Prop :=
  ∀ {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W] {I : Type i} [LinearOrder I] [Fintype I]
    (q : QuadraticForm R V) (Q : QuadraticForm R W) (J : q →qᵢ Q)
    (b : Basis I R V) (d : Basis (WithTop I) R W) (r : V) (j : I),
    (2 : R) = 0 → AdaptedBasis q Q J b d r →
    (∀ a : WithTop I, a ≠ (j : WithTop I) → ∃ v : V, Q.polarBilin (J v) = d.coord a) →
    ∃ e : {a : (CliffordAlgebra q)ˣ // IsIntrinsicSpin q a} ≃
        {a : (CliffordAlgebra Q)ˣ // IsIntrinsicSpin Q a ∧ Commute (ι Q (J r)) a.val},
      (∀ a, (e a).val = Units.map (CliffordAlgebra.map J).toMonoidHom a.val) ∧
      ∀ (a : {a : (CliffordAlgebra q)ˣ // IsIntrinsicSpin q a}) (v : V),
        CliffordAlgebra.map J (a.val.val * ι q v * ↑(a.val⁻¹)) =
        (e a).val.val * ι Q (J v) * ↑((e a).val⁻¹)

end Hyperplane

section SplitModel

noncomputable section

open Albert.SplitSpinSpecification

abbrev OddIndex (n : ℕ) := WithTop (Lex (PairIndex n))
abbrev AmbientIndex (n : ℕ) := WithTop (OddIndex n)
abbrev OddModule (R : Type u) (n : ℕ) := OddIndex n → R
abbrev AmbientModule (R : Type u) (n : ℕ) := AmbientIndex n → R
abbrev OddMatrixIndex (n : ℕ) := ULift.{u} (OddIndex n)

def oddBasis (R : Type u) [CommRing R] (n : ℕ) : Basis (OddMatrixIndex.{u} n) R (OddModule R n) :=
  (Pi.basisFun R (OddIndex n)).reindex Equiv.ulift.symm

/-- The matrix action in the basis of the marked hyperplane. -/
def oddMatrixAction {R : Type u} [CommRing R] {n : ℕ} :
    Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R ≃*
      (OddModule R n ≃ₗ[R] OddModule R n) :=
  (Matrix.GeneralLinearGroup.toLin' (oddBasis R n)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (OddModule R n))

def eIndex {n : ℕ} (i : Fin n) : AmbientIndex n :=
  ((toLex (Sum.inl i) : Lex (PairIndex n)) : OddIndex n)

def fIndex {n : ℕ} (i : Fin n) : AmbientIndex n :=
  ((toLex (Sum.inr i) : Lex (PairIndex n)) : OddIndex n)

def rIndex (n : ℕ) : AmbientIndex n := ((⊤ : OddIndex n) : AmbientIndex n)

/-- The coordinates at `rIndex` and `⊤` correspond to `e₀+f₀` and `f₀`. -/
def ambientForm (R : Type u) [CommRing R] (n : ℕ) : QuadraticForm R (AmbientModule R n) :=
  let term (l m : AmbientModule R n →ₗ[R] R) :=
    LinearMap.BilinMap.toQuadraticMap ((LinearMap.mul R R).compl₁₂ l m)
  let p (i : AmbientIndex n) : AmbientModule R n →ₗ[R] R := LinearMap.proj i
  (∑ i : Fin n, term (p (eIndex i)) (p (fIndex i))) +
    term (p (rIndex n)) (p (rIndex n) + p ⊤)

/-- Extend an odd vector by a zero coefficient on the extra `f₀`. -/
def extendOdd (R : Type u) [CommRing R] (n : ℕ) : OddModule R n →ₗ[R] AmbientModule R n :=
  LinearMap.pi fun i => WithTop.recTopCoe (0 : OddModule R n →ₗ[R] R) LinearMap.proj i

def oddForm (R : Type u) [CommRing R] (n : ℕ) : QuadraticForm R (OddModule R n) :=
  (ambientForm R n).comp (extendOdd R n)

def inclusion (R : Type u) [CommRing R] (n : ℕ) : oddForm R n →qᵢ ambientForm R n where
  toLinearMap := extendOdd R n
  map_app' _ := rfl

abbrev radicalVector (R : Type u) [CommRing R] (n : ℕ) : OddModule R n :=
  Pi.single ⊤ 1

/-- Invertible matrices preserving the odd quadratic form and fixing the
specified radical vector. The equations test the full quadratic form. -/
def MarkedIsometries (R : Type u) [CommRing R] (n : ℕ) :
    Subgroup (Matrix.GeneralLinearGroup (OddMatrixIndex.{u} n) R) where
  carrier := {g | (∀ x, oddForm R n (oddMatrixAction g x) = oddForm R n x) ∧
    oddMatrixAction g (radicalVector R n) = radicalVector R n}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (_ ∧ _) at hg hh ⊢
    rw [map_mul]
    exact ⟨fun x => (hg.1 _).trans (hh.1 x), (congrArg (oddMatrixAction g) hh.2).trans hg.2⟩
  inv_mem' := by
    intro g hg
    change (_ ∧ _) at hg ⊢
    rw [map_inv]
    refine ⟨fun x => ?_, ?_⟩
    · have h := hg.1 ((oddMatrixAction g).symm x)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    · exact ((oddMatrixAction g).injective (by simp [hg.2]))

/-- The diagonal hyperbolic action with the marked line fixed. -/
def diagonalOddVector {R : Type u} [CommRing R] {n : ℕ}
    (t : Fin n → Rˣ) (x : OddModule R n) : OddModule R n :=
  WithTop.recTopCoe (x ⊤) fun j =>
    (ofLex j).elim (fun i => (t i : R) * x (↑(toLex (Sum.inl i) : Lex (PairIndex n))))
      (fun i => (↑(t i)⁻¹ : R) * x (↑(toLex (Sum.inr i) : Lex (PairIndex n))))

/-- The entire fibre over each diagonal point is given by the scalar norm
equation, over every characteristic-two test ring. -/
def DiagonalNormEquation : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), (2 : R) = 0 →
    let Q := ambientForm R n
    let J := inclusion R n
    let r := radicalVector R n
    ∀ t : Fin n → Rˣ, ∃ b : (CliffordAlgebra Q)ˣ,
      b.val ∈ evenOdd Q 0 ∧ reverse b.val * b.val = algebraMap R _ (∏ i, (t i : R)) ∧
      (∀ a : (CliffordAlgebra Q)ˣ,
        IsIntrinsicSpin Q a ∧ Commute (ι Q (J r)) a.val ∧
          (∀ x, a.val * ι Q (J x) * ↑a⁻¹ = ι Q (J (diagonalOddVector t x))) ↔
        ∃! u : Rˣ, (u : R) ^ 2 * (∏ i, (t i : R)) = 1 ∧
          a = Units.map (algebraMap R (CliffordAlgebra Q)).toMonoidHom u * b)

/-- The standard type-B coroots in the cocharacter coordinates of the
diagonal torus of the marked isometry group. -/
def typeBCoroots (n : ℕ) : Set (Fin n → ℤ) :=
  let e (i : Fin n) : Fin n → ℤ := Pi.single i 1
  {v | (∃ i, v = (2 : ℤ) • e i ∨ v = -((2 : ℤ) • e i)) ∨
    ∃ i j, i ≠ j ∧
      (v = e i - e j ∨ v = e i + e j ∨ v = -(e i + e j))}

/-- A diagonal exponent vector lifts at the universal Laurent parameter
precisely when it belongs to the type-B coroot lattice. -/
def LaurentDiagonalLifting : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    ∀ m : Fin n → ℤ, ∀ t : Fin n → (LaurentPolynomial k)ˣ,
      (∀ i, (t i : LaurentPolynomial k) = LaurentPolynomial.T (m i)) →
      let R := LaurentPolynomial k
      let Q := ambientForm R n
      let J := inclusion R n
      let r := radicalVector R n
      (∃ a : (CliffordAlgebra Q)ˣ, IsIntrinsicSpin Q a ∧
        Commute (ι Q (J r)) a.val ∧ ∀ x, a.val * ι Q (J x) * ↑a⁻¹ =
          ι Q (J (diagonalOddVector t x))) ↔ m ∈ Submodule.span ℤ (typeBCoroots n)

/-- The ambient coordinates are those of the specified split hyperbolic form,
and the marked odd form is its restriction to the orthogonal hyperplane. -/
def SplitHyperplane : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), (2 : R) = 0 →
    (∃ e : AmbientModule R n ≃ₗ[R] (PairIndex (n + 1) → R),
      (∀ x, ambientForm R n x = hyperbolicNorm (e x)) ∧
      ∀ (a : OddModule R n), e (inclusion R n a) (Sum.inl 0) = a ⊤ ∧
        e (inclusion R n a) (Sum.inr 0) = a ⊤) ∧
    AdaptedBasis (oddForm R n) (ambientForm R n) (inclusion R n)
      (Pi.basisFun R (OddIndex n)) (Pi.basisFun R (AmbientIndex n)) (radicalVector R n) ∧
    (∀ a : AmbientIndex n, a ≠ rIndex n →
      ∃ v : OddModule R n, (ambientForm R n).polarBilin (inclusion R n v) =
        (Pi.basisFun R (AmbientIndex n)).coord a) ∧
    (oddForm R n) (radicalVector R n) = 1 ∧
    LinearMap.ker (oddForm R n).polarBilin = R ∙ radicalVector R n

/-- The all-test-ring Clifford comparison for the actual split odd form and
the split even stabilizer, using the marked vector (e₀+f₀). -/
def SplitSpinPoints : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), (2 : R) = 0 →
    let q := oddForm R n
    let Q := ambientForm R n
    let J := inclusion R n
    ∃ e : {a : (CliffordAlgebra q)ˣ // IsIntrinsicSpin q a} ≃
        {a : (CliffordAlgebra Q)ˣ //
          IsIntrinsicSpin Q a ∧ Commute (ι Q (J (radicalVector R n))) a.val},
      (∀ a, (e a).val = Units.map (CliffordAlgebra.map J).toMonoidHom a.val) ∧
      ∀ (a : {a : (CliffordAlgebra q)ˣ // IsIntrinsicSpin q a}) (v : OddModule R n),
        CliffordAlgebra.map J (a.val.val * ι q v * ↑(a.val⁻¹)) =
          (e a).val.val * ι Q (J v) * ↑((e a).val⁻¹)

end

end SplitModel

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct CategoryTheory.MonObj

/-- The represented affine scheme-theoretic stabilizer, characterized on every
test algebra by fixing the marked Clifford vector under conjugation. -/
def SchemeStabilizer : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    let Q := ambientForm k n
    let r := inclusion k n (radicalVector k n)
    ∃ (G H : Albert.SpinSpecification.GroupScheme k) (i : H ⟶ G)
        (e : ∀ S, Albert.SpinSpecification.SchemePoints G S →*
          (Albert.SpinSpecification.ScalarClifford Q S)ˣ),
      Albert.SpinSpecification.IsSpinPointRepresentation Q G e ∧
      IsAffine H.X.left ∧ LocallyOfFinitePresentation H.X.hom ∧
      IsClosedImmersion i.hom.hom.left ∧
      ∀ (S : CommAlgCat k) (a : Albert.SpinSpecification.SchemePoints G S),
        Commute (Albert.SpinSpecification.vectors Q S (1 ⊗ₜ[k] r)) (e S a).val ↔
          ∃! p : Albert.SpinSpecification.SchemePoints H S, p ≫ i.hom.hom = a

/-- The split even spin group and the stabilizer of the marked vector are smooth. -/
def SmoothSchemeStabilizer : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    let Q := ambientForm k n
    let r := inclusion k n (radicalVector k n)
    ∃ (G H : Albert.SpinSpecification.GroupScheme k) (i : H ⟶ G)
        (e : ∀ S, Albert.SpinSpecification.SchemePoints G S →*
          (Albert.SpinSpecification.ScalarClifford Q S)ˣ),
      Albert.SpinSpecification.IsSpinPointRepresentation Q G e ∧
      IsAffine G.X.left ∧ IsAffine H.X.left ∧ Smooth G.X.hom ∧ Smooth H.X.hom ∧
      IsClosedImmersion i.hom.hom.left ∧
      ∀ (S : CommAlgCat k) (a : Albert.SpinSpecification.SchemePoints G S),
        Commute (Albert.SpinSpecification.vectors Q S (1 ⊗ₜ[k] r)) (e S a).val ↔
          ∃! p : Albert.SpinSpecification.SchemePoints H S, p ≫ i.hom.hom = a

/-- The affine scheme of marked odd isometries, with its point action over
arbitrary commutative algebras. -/
def MarkedIsometryScheme : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 →
    ∃ (O : Albert.SpinSpecification.GroupScheme k)
      (e : ∀ S : CommAlgCat k, Albert.SpinSpecification.SchemePoints O S ≃* MarkedIsometries S n),
      IsAffine O.X.left ∧ LocallyOfFinitePresentation O.X.hom ∧
      ∀ {S T : CommAlgCat k} (f : S ⟶ T) (p : Albert.SpinSpecification.SchemePoints O S),
        (e T ((algSpec (CommRingCat.of k)).map f.op ≫ p)).val =
          Matrix.GeneralLinearGroup.map f.hom.toRingHom (e S p).val

noncomputable section

open Albert.SpinSpecification
open scoped TensorProduct

/-- The multiplicative group with its Laurent coordinate `T`. -/
abbrev laurentMultiplicativeGroup (k : Type u) [Field k] : GroupScheme k :=
  (StandardGroups.spectrum k (LaurentPolynomial k)).val

/-- Reductivity of an affine group scheme, including its finite type condition. -/
def IsReductiveGroupScheme {k : Type u} [Field k] (G : GroupScheme k) : Prop :=
  ∃ h : IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom,
    GeometricRadicals.IsReductive (⟨G, h⟩ : AffineAlgebraicGroup k)

/-- The actual cocharacter of the marked isometry group with diagonal exponents
`m`, evaluated over the Laurent coordinate ring. -/
def HasDiagonalExponents {k : Type u} [Field k] {n : ℕ} {O : GroupScheme k}
    (eO : ∀ S : CommAlgCat k, SchemePoints O S ≃* MarkedIsometries S n)
    (χ : laurentMultiplicativeGroup k ⟶ O) (m : Fin n → ℤ) : Prop :=
  let S := CommAlgCat.of k (LaurentPolynomial k)
  ∃ t : Fin n → (LaurentPolynomial k)ˣ,
    (∀ i, (t i : LaurentPolynomial k) = LaurentPolynomial.T (m i)) ∧
    ∀ x : OddModule (LaurentPolynomial k) n,
      oddMatrixAction (eO S χ.hom.hom).val x = diagonalOddVector t x

/-- The kernel square and the central scalar inclusion of the group scheme μ₂. -/
def HasScalarRestrictionKernel {k : Type u} [Field k] {n : ℕ}
    {G H O : GroupScheme k} (i : H ⟶ G) (f : H ⟶ O)
    (e : ∀ S, SchemePoints G S →* (ScalarClifford (ambientForm k n) S)ˣ) : Prop :=
  ∃ (M : GroupScheme k) (hM : M.X = muTwoUnderlying k)
      (N : ClosedSubgroup H) (j : M ≅ N.group),
    IsSchemeKernel f N ∧ Centralizes (𝟙 H) N.inclusion.hom.hom ∧
    ∀ (S : CommAlgCat k) (a : muTwoCoordinateRing k →ₐ[k] S),
      (e S ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom a).op ≫
        eqToHom hM.symm ≫ j.hom.hom.hom ≫ N.inclusion.hom.hom ≫ i.hom.hom)).val =
        algebraMap S _ (a (AdjoinRoot.root (muTwoPolynomial k)))

/-- The full preimage of the diagonal action, with a choice of Clifford lifts
compatible with changes of test algebra. The scalar parameter and the
stabilizer point uniquely determine each other on every diagonal fibre. -/
def HasDiagonalRestrictionFibre {k : Type u} [Field k] {n : ℕ}
    {G H O : GroupScheme k} (i : H ⟶ G) (f : H ⟶ O)
    (e : ∀ S, SchemePoints G S →* (ScalarClifford (ambientForm k n) S)ˣ)
    (eO : ∀ S : CommAlgCat k, SchemePoints O S ≃* MarkedIsometries S n) : Prop :=
  let Q := ambientForm k n
  ∃ (E : ∀ S : CommAlgCat k, ScalarClifford Q S ≃ₐ[S] CliffordAlgebra (ambientForm S n))
      (b : ∀ S : CommAlgCat k, (Fin n → Sˣ) → (CliffordAlgebra (ambientForm S n))ˣ),
    (∀ {S T : CommAlgCat k} (a : S ⟶ T) (t : Fin n → Sˣ),
      Units.map (coefficientMap Q S a.hom).toMonoidHom (Units.map (E S).symm.toMonoidHom (b S t)) =
        Units.map (E T).symm.toMonoidHom (b T (fun j => Units.map a.hom.toMonoidHom (t j)))) ∧
    ∀ S : CommAlgCat k,
      let Qs := ambientForm S n
      (∀ x : S ⊗[k] AmbientModule k n,
        E S (vectors Q S x) =
          CliffordAlgebra.ι Qs (((Pi.basisFun k (AmbientIndex n)).baseChange S).equivFun x)) ∧
      ∀ t : Fin n → Sˣ,
        (b S t).val ∈ evenOdd Qs 0 ∧
        reverse (b S t).val * (b S t).val = algebraMap S _ (∏ j, (t j : S)) ∧
        let a (p : SchemePoints H S) := Units.map (E S).toMonoidHom (e S (p ≫ i.hom.hom))
        let isDiagonal (p : SchemePoints H S) :=
          ∀ x, oddMatrixAction (eO S (p ≫ f.hom.hom)).val x = diagonalOddVector t x
        let normEquation (u : Sˣ) := (u : S) ^ 2 * (∏ j, (t j : S)) = 1
        (∀ p : SchemePoints H S, isDiagonal p ↔
          ∃! u : Sˣ, normEquation u ∧ a p =
            Units.map (algebraMap S (CliffordAlgebra Qs)).toMonoidHom u * b S t) ∧
        (∀ u : Sˣ, normEquation u →
          ∃! p : SchemePoints H S,
            a p = Units.map (algebraMap S (CliffordAlgebra Qs)).toMonoidHom u * b S t ∧ isDiagonal p)

/-- The finite faithfully flat restriction of the smooth stabilizer, with
the specified vector action and its central scalar scheme kernel. Reductivity
and the diagonal cocharacter calculation apply to this same restriction. -/
def SplitRestrictionCover : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    let Q := ambientForm k n
    let J := inclusion k n
    let r := J (radicalVector k n)
    ∃ (G H O : GroupScheme k) (i : H ⟶ G) (f : H ⟶ O)
      (e : ∀ S, SchemePoints G S →* (ScalarClifford Q S)ˣ)
      (eO : ∀ S : CommAlgCat k, SchemePoints O S ≃* MarkedIsometries S n),
      IsSpinPointRepresentation Q G e ∧ IsClosedImmersion i.hom.hom.left ∧
      IsAffine H.X.left ∧ Smooth H.X.hom ∧ IsAffine O.X.left ∧ Smooth O.X.hom ∧
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      UniversallyInjective f.hom.hom.left ∧
      (GeometricallyConnected O.X.hom → GeometricallyConnected H.X.hom) ∧
      (IsReductiveGroupScheme O → IsReductiveGroupScheme H) ∧
      HasScalarRestrictionKernel (n := n) i f e ∧ HasDiagonalRestrictionFibre i f e eO ∧
      (∀ m : Fin n → ℤ, ∃ χ : laurentMultiplicativeGroup k ⟶ O, HasDiagonalExponents eO χ m) ∧
      (∀ (χ : laurentMultiplicativeGroup k ⟶ O) (m : Fin n → ℤ),
        HasDiagonalExponents eO χ m →
        ((∃ c : laurentMultiplicativeGroup k ⟶ H, c ≫ f = χ) ↔
          m ∈ Submodule.span ℤ (typeBCoroots n))) ∧
      (∀ {S T : CommAlgCat k} (a : S ⟶ T) (p : SchemePoints O S),
        (eO T ((algSpec (CommRingCat.of k)).map a.op ≫ p)).val =
          Matrix.GeneralLinearGroup.map a.hom.toRingHom (eO S p).val) ∧
      ∀ S : CommAlgCat k,
        (∀ a : SchemePoints G S, Commute (vectors Q S (1 ⊗ₜ[k] r)) (e S a).val ↔
          ∃! p : SchemePoints H S, p ≫ i.hom.hom = a) ∧
        (∀ (p : SchemePoints H S) (x : S ⊗[k] OddModule k n),
          let v := ((Pi.basisFun k (OddIndex n)).baseChange S).equivFun
          vectors Q S (J.toLinearMap.baseChange S
            (v.symm (oddMatrixAction (eO S (p ≫ f.hom.hom)).val (v x)))) =
              conjugate Q S (e S (p ≫ i.hom.hom)) (vectors Q S (J.toLinearMap.baseChange S x))) ∧
        (∀ p : SchemePoints H S, p ≫ f.hom.hom = 1 ↔
          ∃! t : muTwoCoordinateRing k →ₐ[k] S, (e S (p ≫ i.hom.hom)).val =
            algebraMap S _ (t (AdjoinRoot.root (muTwoPolynomial k)))) ∧
        (∀ p q : SchemePoints H S, p ≫ f.hom.hom = 1 → Commute p q)

end

/-- Geometric surjectivity of restriction to the actual marked odd isometries. -/
def GeometricRestriction : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ), (2 : K) = 0 →
    ∀ g : OddModule K n ≃ₗ[K] OddModule K n,
      (∀ x, oddForm K n (g x) = oddForm K n x) → g (radicalVector K n) = radicalVector K n →
      ∃ a : (CliffordAlgebra (ambientForm K n))ˣ,
        IsIntrinsicSpin (ambientForm K n) a ∧
        Commute (CliffordAlgebra.ι (ambientForm K n) (inclusion K n (radicalVector K n))) a.val ∧
        ∀ x, a.val * CliffordAlgebra.ι (ambientForm K n) (inclusion K n x) * ↑a⁻¹ =
          CliffordAlgebra.ι (ambientForm K n) (inclusion K n (g x))

/-- The kernel is the central scalar group of square roots of unity on every test ring. -/
def ScalarRestrictionKernel : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), (2 : R) = 0 →
    let Q := ambientForm R n
    let J := inclusion R n
    ∀ a : (CliffordAlgebra Q)ˣ, IsIntrinsicSpin Q a →
      Commute (CliffordAlgebra.ι Q (J (radicalVector R n))) a.val →
      ((∀ x : OddModule R n, Commute a.val (CliffordAlgebra.ι Q (J x))) ↔
        ∃! t : rootsOfUnity 2 R, a.val = algebraMap R _ (t.val : R)) ∧
      (∀ t : rootsOfUnity 2 R, Commute (algebraMap R (CliffordAlgebra Q) (t.val : R)) a.val)

/-- The coefficientwise Clifford inclusion gives the comparison for the
represented spin functor over all base algebras. -/
def TensorSpinComparison : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 →
    let q := oddForm k n
    let Q := ambientForm k n
    let J := inclusion k n
    let r := radicalVector k n
    ∀ (S : Type u) [CommRing S] [Algebra k S],
      let j : Albert.SpinSpecification.ScalarClifford q S →ₐ[S]
          Albert.SpinSpecification.ScalarClifford Q S :=
        Algebra.TensorProduct.map (AlgHom.id S S) (CliffordAlgebra.map J)
      Function.Injective j ∧
      (∀ a : (Albert.SpinSpecification.ScalarClifford q S)ˣ,
        a ∈ Albert.SpinSpecification.spinUnits q S ↔
          Units.map j.toMonoidHom a ∈ Albert.SpinSpecification.spinUnits Q S ∧
          Commute (Albert.SpinSpecification.vectors Q S (1 ⊗ₜ[k] J r)) (j a.val)) ∧
      (∀ a : (Albert.SpinSpecification.ScalarClifford Q S)ˣ,
        a ∈ Albert.SpinSpecification.spinUnits Q S →
        Commute (Albert.SpinSpecification.vectors Q S (1 ⊗ₜ[k] J r)) a.val →
        ∃! b : (Albert.SpinSpecification.ScalarClifford q S)ˣ,
          b ∈ Albert.SpinSpecification.spinUnits q S ∧ Units.map j.toMonoidHom b = a) ∧
      (∀ x : S ⊗[k] OddModule k n,
        j (Albert.SpinSpecification.vectors q S x) =
          Albert.SpinSpecification.vectors Q S (J.toLinearMap.baseChange S x)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra k T] (f : S →ₐ[k] T) (x : Albert.SpinSpecification.ScalarClifford q S),
        Albert.SpinSpecification.coefficientMap Q S f (j x) =
          Algebra.TensorProduct.map (AlgHom.id T T) (CliffordAlgebra.map J)
            (Albert.SpinSpecification.coefficientMap q S f x)

/-- The differential of the split even spin orbit at the marked vector fills
the tangent hyperplane to the norm-one quadric. This form allows arbitrary
square-zero test ideals and identifies the infinitesimal Clifford implementer. -/
def SquareZeroOrbitLifting : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ), (2 : R) = 0 → 0 < n →
    let Q := ambientForm R n
    let r := inclusion R n (radicalVector R n)
    ∀ (I : Ideal R), I ^ 2 = ⊥ →
    ∀ v : AmbientModule R n, (∀ i, v i ∈ I) → Q.polarBilin r v = 0 →
      ∃ a : (CliffordAlgebra Q)ˣ,
        IsIntrinsicSpin Q a ∧
        a.val - 1 ∈ I • (⊤ : Submodule R (CliffordAlgebra Q)) ∧
        a.val * CliffordAlgebra.ι Q r * ↑a⁻¹ = CliffordAlgebra.ι Q (r + v)

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinCharTwoStabilizer
