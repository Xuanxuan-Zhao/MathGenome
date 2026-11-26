import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LatticeCompletionDecomposition
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalLatticeIntersection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LaurentLatticeReduction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RealLatticeReduction
import Mathlib.Algebra.Module.Lattice
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.Group.Matrix

open scoped BigOperators LaurentSeries PowerSeries Pointwise Polynomial RatFunc RestrictedProduct
  TensorProduct
open IsDedekindDomain
open scoped NumberField

namespace LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

noncomputable section

/-- The column basis of an invertible matrix. -/
def columnBasis {k N : Type*} [Field k] [Fintype N] [DecidableEq N]
    (M : Matrix.GeneralLinearGroup N k) : Module.Basis N k (N → k) :=
  (Pi.basisFun k N).map (Matrix.GeneralLinearGroup.toLin M).toLinearEquiv

/-- The vectors with integral coefficients in the indicated basis matrix. The map
can be the distinguished or a finite completion embedding of the coefficient ring. -/
def basisVectors {R k N : Type*} [CommRing R] [Field k] [Fintype N] [DecidableEq N]
    (f : R →+* k) (M : Matrix.GeneralLinearGroup N k) : Set (N → k) :=
  Set.range fun z : N → R => M.val.mulVec (f ∘ z)

/-- The integral span of the columns of a matrix. -/
def matrixLattice {R k N : Type*} [CommRing R] [Field k] [Algebra R k]
    [Fintype N] [DecidableEq N] (M : Matrix.GeneralLinearGroup N k) :
    Submodule R (N → k) :=
  Submodule.span R (Set.range (columnBasis M))

/-- The basis matrix of the rational intersection in reference coordinates. -/
def IsBasisMatrix (R : Type*) {k V N : Type*} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup V] [Module k V] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k V) (L : Set V) (M : Matrix.GeneralLinearGroup N k) : Prop :=
  b.equivFun '' L = basisVectors (algebraMap R k) M

/-- The finite matrix adeles of the base field in the chosen reference basis. -/
abbrev FiniteBasisAdeles (R k N : Type*) [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N] :=
  Πʳ p : HeightOneSpectrum R, [Matrix.GeneralLinearGroup N (p.adicCompletion k),
    ↑(Matrix.GeneralLinearGroup.map (n := N) (p.adicCompletionIntegers k).subtype).range]

/-- The full base matrix adeles, with the single distinguished completion
separated from the restricted product of the finite completions. -/
abbrev BasisAdeles (R k B N : Type*) [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Field B] [Fintype N] [DecidableEq N] :=
  FiniteBasisAdeles R k N × Matrix.GeneralLinearGroup N B

/-- A basis is integral with integral inverse at every base finite place
after applying the given local operators. -/
def FiniteBasisIntegral {R k N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N]
    (G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k))
    (M : Matrix.GeneralLinearGroup N k) : Prop :=
  ∀ p, G p * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M ∈
    (Matrix.GeneralLinearGroup.map (p.adicCompletionIntegers k).subtype).range

/-- The integral finite components form a point in the actual restricted product. -/
def finiteBasisRepresentative {R k N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N]
    (G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k))
    (M : Matrix.GeneralLinearGroup N k) (h : FiniteBasisIntegral G M) :
    FiniteBasisAdeles R k N :=
  ⟨fun p => G p * Matrix.GeneralLinearGroup.map (algebraMap k (p.adicCompletion k)) M,
    Filter.Eventually.of_forall h⟩

open LatticeCompletionDecompositionSpec in
/-- This base local matrix acts by the original matrices on all the actual
completions above the base place. -/
def FiniteMatrixAction {R A k K I N : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Field k] [Field K] [Algebra k K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K))
    (g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K))
    (p : HeightOneSpectrum R) (G : Matrix.GeneralLinearGroup N (p.adicCompletion k)) : Prop :=
  let J := p.asIdeal.primesOver A
  let B := p.adicCompletion k
  let C (j : J) := (primeAbove p j).adicCompletion K
  ∃ a : ∀ j : J, Algebra B (C j),
    letI := a
    ∃ E : (N → B) ≃L[B] (∀ j : J, I → C j),
      (∀ (x : I → K) (j : J),
        E (embedCoordinates (algebraMap k B) (b.equivFun x)) j =
          embedCoordinates (algebraMap K (C j)) x) ∧
      (∀ x j, E (G.val.mulVec x) j = (g (primeAbove p j)).val.mulVec (E x j))

/-- Integral values on the completed finite reference lattices. -/
def IntegralOnReference {A K I J : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K] (L₀ : Submodule A (I → K))
    (p : J → MvPolynomial I K) : Prop :=
  ∀ b (v : HeightOneSpectrum A) y, y ∈ completedLattice v L₀ →
    (p b).eval₂ (algebraMap K (v.adicCompletion K)) y ∈ v.adicCompletionIntegers K

/-- The local matrices preserve the listed polynomials over their own fields. -/
def PreservesPolynomials {I J P K : Type*} [Field K] [Fintype I] [DecidableEq I]
    {L : J → Type*} [∀ j, Field (L j)] (e : ∀ j, K →+* L j) (p : P → MvPolynomial I K)
    (g : ∀ j, Matrix.GeneralLinearGroup I (L j)) : Prop :=
  ∀ b j y, (p b).eval₂ (e j) ((g j).val.mulVec y) = (p b).eval₂ (e j) y

/-- The completed real matrix lattice is full, discrete and of covolume one in
reference coordinates. -/
def RealCovolumeOne {n : ℕ} (H : Matrix.GeneralLinearGroup (Fin n) ℝ) : Prop :=
  let L := matrixLattice (R := ℤ) H
  ∃ (h : DiscreteTopology L) (_hFull : IsZLattice ℝ L),
    letI := h
    ZLattice.covolume L = 1

open MeasureTheory LaurentLattice in
/-- Unit covolume of the Laurent coordinate lattice for the measure normalized
on the reference polynomial lattice. -/
def LaurentCovolumeOne {F : Type*} [Field F] {n : ℕ} [MeasurableSpace F⸨X⸩]
    (μ : Measure (Fin n → F⸨X⸩)) (H : SquareGL n F⸨X⸩) : Prop :=
  DiscreteTopology (latticeVector H).range ∧
    addCovolume (latticeVector H).range (Fin n → F⸨X⸩) μ = 1

end

end LinearAlgebraicGroups.Arithmetic.AdelicLatticeBounds

namespace LinearAlgebraicGroups.Specs.AdelicLatticeBounds

open Arithmetic.AdelicLatticeBounds

/-- A homogeneous polynomial is bounded by the coefficient sum times the corresponding
power of a bound on the input coordinates. -/
def homogeneousEvaluationBound : Prop :=
  ∀ {I K L : Type*} [Field K] [Field L] (a : AbsoluteValue L ℝ) (e : K →+* L)
    (p : MvPolynomial I K) (d : ℕ), p.IsHomogeneous d →
    ∀ (y : I → L) (r : ℝ), 0 ≤ r → (∀ i, a (y i) ≤ r) →
      a (p.eval₂ e y) ≤ (∑ m ∈ p.support, a (e (p.coeff m))) * r ^ d

/-- A finite weighted product of local absolute values has a single homogeneous bound
for each polynomial. The weight is two at a complex place in the number-field application. -/
def homogeneousProductBound : Prop :=
  ∀ {I J K : Type*} [Fintype J] [Field K] {L : J → Type*} [∀ j, Field (L j)]
    (a : ∀ j, AbsoluteValue (L j) ℝ) (e : ∀ j, K →+* L j) (w : J → ℕ)
    (p : MvPolynomial I K) (d : ℕ), p.IsHomogeneous d →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : ∀ j, I → L j) (r : ℝ), 0 ≤ r →
      (∀ j i, a j (y j i) ≤ r) →
      (∏ j, (a j (p.eval₂ (e j) (y j))) ^ w j) ≤
        C * r ^ (d * ∑ j, w j)

/-- Pull back integrality on a reference set by a local change preserving the evaluations. -/
def invariantValuesIntegral : Prop :=
  ∀ {I J A K : Type*} [Field K] {L : J → Type*} [∀ j, Field (L j)]
    (e : ∀ j, K →+* L j) (O : ∀ j, Subring (L j)) (B : ∀ j, Set (I → L j))
    (p : A → MvPolynomial I K) (g : ∀ j, (I → L j) → (I → L j)),
    (∀ a j y, y ∈ B j → (p a).eval₂ (e j) y ∈ O j) →
    (∀ a j y, (p a).eval₂ (e j) (g j y) = (p a).eval₂ (e j) y) →
    ∀ x : I → K, (∀ j, g j (e j ∘ x) ∈ B j) →
    ∀ a j, e j ((p a).eval x) ∈ O j

/-- Once the global norm estimate is supplied, the polynomial argument gives a lower bound
uniform also in the transformations and rational vectors to which the estimate applies. -/
def invariantPolynomialLowerBound : Prop :=
  ∀ {I J A K X : Type*} [Fintype J] [Fintype A] [Field K]
    {L : J → Type*} [∀ j, Field (L j)]
    (a : ∀ j, AbsoluteValue (L j) ℝ) (e : ∀ j, K →+* L j) (w : J → ℕ),
    0 < ∑ j, w j →
    ∀ (p : A → MvPolynomial I K) (d : A → ℕ),
    (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) →
    ∀ (x : X → I → K) (y : X → ∀ j, I → L j),
    (∀ b z j, (p b).eval₂ (e j) (y z j) = e j ((p b).eval (x z))) →
    (∀ z, ∃ b, 1 ≤ ∏ j, (a j (e j ((p b).eval (x z)))) ^ w j) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ z (r : ℝ), 0 ≤ r →
      (∀ j i, a j (y z j i) ≤ r) → ε ≤ r

/-- A submodule between nonzero reciprocal dilates of a lattice over a PID is itself
a full finite free lattice. -/
def fullFreeOfSandwich : Prop :=
  ∀ {R k V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field k] [Algebra R k] [IsFractionRing R k]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower R k V]
    (L₀ L : Submodule R V) [Submodule.IsLattice k L₀] (u : kˣ),
    (u • L₀ : Submodule R V) ≤ L → L ≤ (u⁻¹ • L₀ : Submodule R V) →
    Submodule.IsLattice k L ∧ Module.Free R L

/-- A full lattice over a finite integer-ring extension remains a lattice over
the base PID, even if the original lattice is not free over the integer ring. -/
def restrictLatticeScalars : Prop :=
  ∀ {R A k K V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra R k] [IsFractionRing R k]
    [Algebra A K] [IsFractionRing A K] [Algebra k K] [FiniteDimensional k K]
    [AddCommGroup V] [Module R V] [Module A V] [Module k V] [Module K V]
    [IsScalarTower R A V] [IsScalarTower R k V] [IsScalarTower A K V]
    [IsScalarTower k K V] [FiniteDimensional K V]
    (L : Submodule A V) [Submodule.IsLattice K L],
    Submodule.IsLattice k (L.restrictScalars R) ∧ Module.Free R (L.restrictScalars R)

open Arithmetic in
/-- The recovered number-field intersection is full and free over the base integers. -/
def numberIntersectionOverBase : Prop :=
  ∀ {K I : Type*} [Field K] [NumberField K] [Finite I]
    (L₀ : Submodule (𝓞 K) (I → K)) [Submodule.IsLattice K L₀]
    (P : ∀ v : NumberFinitePlace K,
      Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K))
    [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
    {v | P v ≠ completedLattice v L₀}.Finite →
      LatticeIntersectionConclusion (B := ℤ) L₀ P ∧
      Submodule.IsLattice ℚ (L₀.restrictScalars ℤ) ∧
      Submodule.IsLattice ℚ ((rationalLatticeIntersection P).restrictScalars ℤ) ∧
      Module.Free ℤ ((rationalLatticeIntersection P).restrictScalars ℤ)

open Arithmetic in
/-- The recovered function-field intersection is full and free over the
polynomial ring of the chosen separating parameter. -/
def functionIntersectionOverBase : Prop :=
  ∀ {F K I : Type*} [Field F] [Finite F] [Field K] [Algebra F K] [Finite I]
    (t : SeparatingParameter F K)
    (L₀ : Submodule t.integerRing (I → K)) [Submodule.IsLattice K L₀]
    (P : ∀ v : HeightOneSpectrum t.integerRing,
      Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K))
    [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
    {v | P v ≠ completedLattice v L₀}.Finite →
      letI := t.polynomialAlgebra
      letI := t.rationalAlgebra
      LatticeIntersectionConclusion (B := F[X]) L₀ P ∧
      Submodule.IsLattice F⟮X⟯ (L₀.restrictScalars F[X]) ∧
      Submodule.IsLattice F⟮X⟯ ((rationalLatticeIntersection P).restrictScalars F[X]) ∧
      Module.Free F[X] ((rationalLatticeIntersection P).restrictScalars F[X])

/-- In a number field the distinguished absolute values of a nonzero element integral at
every finite place have product at least one, counting both complex embeddings. -/
def numberDistinguishedNormBound : Prop :=
  ∀ {K : Type*} [Field K] [NumberField K] (x : K), x ≠ 0 →
    (∀ v : Arithmetic.NumberFinitePlace K, algebraMap K (v.adicCompletion K) x ∈
      v.adicCompletionIntegers K) →
    1 ≤ ∏ v : NumberField.InfinitePlace K, v x ^ v.mult

/-- In a number field, local invariance and finite-place integrality yield a uniform
positive lower bound at the product of all archimedean completions. -/
def numberInvariantPolynomialLowerBound : Prop :=
  ∀ {K I A X : Type*} [Field K] [NumberField K] [Fintype A]
    (p : A → MvPolynomial I K) (d : A → ℕ)
    (x : X → I → K)
    (y : X → ∀ w : NumberField.InfinitePlace K, I → w.Completion),
    (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) →
    (∀ b z w, (p b).eval₂ (algebraMap K w.Completion) (y z w) =
      algebraMap K w.Completion ((p b).eval (x z))) →
    (∀ z, ∃ b, (p b).eval (x z) ≠ 0 ∧
      ∀ v : Arithmetic.NumberFinitePlace K,
        algebraMap K (v.adicCompletion K) ((p b).eval (x z)) ∈ v.adicCompletionIntegers K) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ z (r : ℝ), 0 ≤ r → (∀ w i, ‖y z w i‖ ≤ r) → ε ≤ r

open Classical in
/-- In a function field the field norm of a nonzero element integral away from the
chosen infinity has nonnegative pole degree at the infinity of the rational subfield. -/
def functionDistinguishedNormBound : Prop :=
  ∀ {F K : Type*} [Field F] [Field K] [Finite F] [Algebra F K]
    (t : Arithmetic.SeparatingParameter F K) (x : K), x ≠ 0 →
    (∀ v : Arithmetic.FunctionPlace K, t.element ∈ v.1 → v.embedding x ∈ v.integers) →
    letI := t.rationalAlgebra
    1 ≤ RatFunc.inftyValuation F (Algebra.norm F⟮X⟯ x)

open Classical Arithmetic.LatticeCompletionDecompositionSpec in
/-- The function-field norm bound in the original completed factors, with
the relative degree at each place above the chosen infinity. -/
def functionDistinguishedProductBound : Prop :=
  ∀ {F K : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    (t : Arithmetic.SeparatingParameter F K),
    let P := {v : Arithmetic.FunctionPlace K // t.element ∉ v.val}
    let B := infinityField F
    letI := t.rationalAlgebra
    letI := (infinityEmbedding F).toAlgebra
    letI := infinityNormedField F
    ∀ (idx : Fintype P) (a : ∀ w : P, Algebra B w.val.Completion),
      letI := idx
      letI := a
      ∀ (fd : ∀ w : P, FiniteDimensional B w.val.Completion),
        letI := fd
        ∀ (e : B ⊗[F⟮X⟯] K ≃ₐ[B] (∀ w : P, w.val.Completion)),
          (∀ (x : K) (w : P), e (1 ⊗ₜ[F⟮X⟯] x) w = w.val.embedding x) →
          ∀ x : K, x ≠ 0 →
            (∀ v : Arithmetic.FunctionPlace K, t.element ∈ v.val → v.embedding x ∈ v.integers) →
            1 ≤ ∏ w : P, (spectralNorm B w.val.Completion (w.val.embedding x) : ℝ) ^
              Module.finrank B w.val.Completion

open Classical Arithmetic.LatticeCompletionDecompositionSpec in
/-- Uniform separation in the product of all completions above the chosen infinity,
using the absolute values extending the normalized base absolute value. -/
def functionInvariantPolynomialLowerBound : Prop :=
  ∀ {F K I A : Type*} [Field F] [Field K] [Finite F] [Algebra F K] [Fintype A]
    (t : Arithmetic.SeparatingParameter F K)
    (p : A → MvPolynomial I K) (d : A → ℕ),
    (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) →
    let P := {v : Arithmetic.FunctionPlace K // t.element ∉ v.val}
    let B := infinityField F
    letI := t.rationalAlgebra
    letI := (infinityEmbedding F).toAlgebra
    letI := infinityNormedField F
    ∃ (idx : Fintype P) (a : ∀ w : P, Algebra B w.val.Completion),
      letI := idx
      letI := a
      ∃ (fd : ∀ w : P, FiniteDimensional B w.val.Completion)
        (e : B ⊗[F⟮X⟯] K ≃ₐ[B] (∀ w : P, w.val.Completion)),
        (∀ r x w, e (r ⊗ₜ[F⟮X⟯] x) w =
          algebraMap B w.val.Completion r * w.val.embedding x) ∧
        (∀ w : P, Continuous (algebraMap B w.val.Completion)) ∧
        letI := fd
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (x : I → K) (y : ∀ w : P, I → w.val.Completion),
            (∀ b w, (p b).eval₂ w.val.embedding (y w) = w.val.embedding ((p b).eval x)) →
            (∃ b, (p b).eval x ≠ 0 ∧ ∀ v : Arithmetic.FunctionPlace K,
              t.element ∈ v.val → v.embedding ((p b).eval x) ∈ v.integers) →
            ∀ r : ℝ, 0 ≤ r →
              (∀ w i, (spectralNorm B w.val.Completion (y w i) : ℝ) ≤ r) → ε ≤ r

/-- The determinant of a rational basis with everywhere integral invertible finite
components after determinant-one changes is the image of an integral unit. -/
def determinantUnitOfLocal : Prop :=
  ∀ {R K I : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Fintype I] [DecidableEq I]
    (M : Matrix.GeneralLinearGroup I K)
    (g : ∀ v : HeightOneSpectrum R, Matrix.GeneralLinearGroup I (v.adicCompletion K)),
    (∀ v, (g v).det = 1) →
    (∀ v, g v * Matrix.GeneralLinearGroup.map (algebraMap K (v.adicCompletion K)) M ∈
      (Matrix.GeneralLinearGroup.map (v.adicCompletionIntegers K).subtype).range) →
    ∃ u : Rˣ, Units.map (algebraMap R K) u = M.det

/-- The integral general linear group is the stabilizer of the standard
coordinate lattice for the embedded valuation ring (or any embedded subring). -/
def integralMatrixIffPreservesBox : Prop :=
  ∀ {I L : Type*} [Fintype I] [DecidableEq I] [CommRing L] (O : Subring L)
    (m : Matrix.GeneralLinearGroup I L),
    m ∈ (Matrix.GeneralLinearGroup.map O.subtype).range ↔
      m.val.mulVec '' {x | ∀ i, x i ∈ O} = {x | ∀ i, x i ∈ O}

/-- In base coordinates, the product of determinant-one local operators again
has determinant one. The coordinates may be any linear identification of the
scalar-restricted space with the product of local spaces. -/
def determinantOneProductMatrix : Prop :=
  ∀ {B J I N : Type*} [Field B] [Fintype J] [Fintype I] [DecidableEq I]
    [Fintype N] [DecidableEq N] {C : J → Type*}
    [∀ j, Field (C j)] [∀ j, Algebra B (C j)] [∀ j, FiniteDimensional B (C j)]
    (E : (N → B) ≃ₗ[B] (∀ j, I → C j))
    (g : ∀ j, Matrix.GeneralLinearGroup I (C j)),
    (∀ j, (g j).det = 1) →
    ∃ G : Matrix.GeneralLinearGroup N B, G.det = 1 ∧
      ∀ x j, E (G.val.mulVec x) j = (g j).val.mulVec (E x j)

open Arithmetic in
/-- Realize the completion comparison in the coordinates of any base-field
basis. The comparison carries the rational diagonal to the original embeddings. -/
def coordinateCompletionComparison : Prop :=
  ∀ {k K B J I N : Type*} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [NontriviallyNormedField B] [CompleteSpace B] [Algebra k B] [Fintype J] [Fintype I]
    [Fintype N] {C : J → Type*} [∀ j, Field (C j)] [∀ j, Algebra B (C j)]
    [∀ j, Algebra K (C j)] [∀ j, FiniteDimensional B (C j)]
    [∀ j, TopologicalSpace (C j)] [∀ j, T2Space (C j)] [∀ j, IsTopologicalRing (C j)],
    (∀ j, Continuous (algebraMap B (C j))) →
    ∀ (e : B ⊗[k] K ≃ₐ[B] (∀ j, C j)),
    (∀ (x : K) (j : J), e (1 ⊗ₜ[k] x) j = algebraMap K (C j) x) →
    ∀ (b : Module.Basis N k (I → K)),
    ∃ E : (N → B) ≃L[B] (∀ j, I → C j),
      ∀ (x : I → K) (j : J),
        E (embedCoordinates (algebraMap k B) (b.equivFun x)) j =
          embedCoordinates (algebraMap K (C j)) x

open Arithmetic in
/-- The completion of a free lattice in coordinates is the image of the
standard local integer box under the scalar extension of its basis matrix. -/
def completedBasisLattice : Prop :=
  ∀ {R k N : Type*} [CommRing R] [IsDedekindDomain R] [Field k]
    [Algebra R k] [IsFractionRing R k] [Fintype N] [DecidableEq N]
    (M : Matrix.GeneralLinearGroup N k) (v : HeightOneSpectrum R),
    (completedLattice v (matrixLattice (R := R) M) : Set (N → v.adicCompletion k)) =
      (Matrix.GeneralLinearGroup.map (algebraMap k (v.adicCompletion k)) M).val.mulVec ''
        {x | ∀ i, x i ∈ v.adicCompletionIntegers k}

open Arithmetic Arithmetic.LatticeCompletionDecompositionSpec in
/-- In base-field coordinates the local closure of a lattice factors into the
completions at the primes above the base prime, compatibly for all lattices. -/
def finiteCoordinateLatticeComparison : Prop :=
  ∀ {R A k K I N : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K] [Fintype I] [Fintype N]
    (p : HeightOneSpectrum R) (b : Module.Basis N k (I → K)),
    let J := p.asIdeal.primesOver A
    let B := p.adicCompletion k
    let C (j : J) := (primeAbove p j).adicCompletion K
    ∃ a : ∀ j : J, Algebra B (C j),
      letI := a
      ∃ (_d : ∀ j : J, FiniteDimensional B (C j))
        (E : (N → B) ≃L[B] (∀ j : J, I → C j)),
        (∀ (x : I → K) (j : J),
          E (embedCoordinates (algebraMap k B) (b.equivFun x)) j =
            embedCoordinates (algebraMap K (C j)) x) ∧
        ∀ (L : Submodule A (I → K)) [Submodule.IsLattice K L],
          E '' closure (Set.range fun x : L =>
            embedCoordinates (algebraMap k B) (b.equivFun (x : I → K))) =
              Set.pi Set.univ (fun j : J =>
                (completedLattice (primeAbove p j) L : Set (I → C j)))

/-- Any integral lattice over the base PID has a reference basis whose rational
extension gives the standard integral coordinates. Every other full lattice is
represented in these coordinates by an invertible rational basis matrix. -/
def latticeBasisCoordinates : Prop :=
  ∀ {R k V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Field k] [Algebra R k] [IsFractionRing R k]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower R k V] [FiniteDimensional k V]
    (L₀ : Submodule R V) [Submodule.IsLattice k L₀],
    let N := Fin (Module.finrank k V)
    ∃ b : Module.Basis N k V, IsBasisMatrix R b (L₀ : Set V) 1 ∧
      ∀ (L : Submodule R V) [Submodule.IsLattice k L],
        ∃ M : Matrix.GeneralLinearGroup N k, IsBasisMatrix R b (L : Set V) M

open Arithmetic in
/-- If determinant-one local operators carry a full lattice onto the reference
lattice at every finite place, its rational basis can be normalized to
determinant one and gives integral bases at every finite place of the base. -/
def normalizeFiniteBasis : Prop :=
  ∀ {R A k K I N : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K]
    [Fintype I] [DecidableEq I] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k (I → K))
    (L₀ L : Submodule A (I → K)) [Submodule.IsLattice K L₀] [Submodule.IsLattice K L]
    (M : Matrix.GeneralLinearGroup N k),
    IsBasisMatrix R b (L₀ : Set (I → K)) 1 →
    IsBasisMatrix R b (L : Set (I → K)) M →
    ∀ (g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K)),
      (∀ v, (g v).det = 1) →
      (∀ v, (g v).val.mulVec '' (completedLattice v L : Set (I → v.adicCompletion K)) =
        (completedLattice v L₀ : Set (I → v.adicCompletion K))) →
      ∃ (G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k))
        (M' : Matrix.GeneralLinearGroup N k),
        (∀ p, (G p).det = 1 ∧ FiniteMatrixAction b g p (G p)) ∧
        IsBasisMatrix R b (L : Set (I → K)) M' ∧ M'.det = 1 ∧ FiniteBasisIntegral G M'

open Arithmetic in
/-- A fixed reference basis serves all rational intersections. It describes their
full free base lattices, their prescribed completions, and determinant-normalized
bases when the prescribed lattices come from determinant-one changes. -/
def baseLatticeModel : Prop :=
  ∀ {R A k K I : Type*} [CommRing R] [IsDedekindDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [IsDedekindDomain A] [Algebra R A] [Module.IsTorsionFree R A]
    [Algebra.IsIntegral R A] [Module.Finite R A]
    [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Algebra.IsSeparable k K]
    [Algebra R k] [IsFractionRing R k] [Algebra A K] [IsFractionRing A K] [Algebra R K]
    [IsScalarTower R A K] [IsScalarTower R k K] [Fintype I] [DecidableEq I]
    (L₀ : Submodule A (I → K)) [Submodule.IsLattice K L₀],
    let N := Fin (Module.finrank k (I → K))
    ∃ b : Module.Basis N k (I → K), IsBasisMatrix R b (L₀ : Set (I → K)) 1 ∧
      ∀ (P : ∀ v : HeightOneSpectrum A,
          Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K))
        [∀ v, Submodule.IsLattice (v.adicCompletion K) (P v)],
        {v | P v ≠ completedLattice v L₀}.Finite →
        let L := rationalLatticeIntersection P
        LatticeIntersectionConclusion (B := R) L₀ P ∧
          Submodule.IsLattice k (L.restrictScalars R) ∧ Module.Free R (L.restrictScalars R) ∧
          (∃ M : Matrix.GeneralLinearGroup N k, IsBasisMatrix R b (L : Set (I → K)) M) ∧
          ∀ (g : ∀ v : HeightOneSpectrum A, Matrix.GeneralLinearGroup I (v.adicCompletion K)),
            (∀ v, (g v).det = 1) →
            (∀ v, (g v).val.mulVec '' (P v : Set (I → v.adicCompletion K)) =
              (completedLattice v L₀ : Set (I → v.adicCompletion K))) →
            ∃ (G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k))
              (M : Matrix.GeneralLinearGroup N k),
              (∀ p, (G p).det = 1 ∧ FiniteMatrixAction b g p (G p)) ∧
              IsBasisMatrix R b (L : Set (I → K)) M ∧ M.det = 1 ∧ FiniteBasisIntegral G M

/-- A basis with unit determinant can be changed to determinant one by an integral
change of columns. Even in dimension zero the resulting determinant is one. -/
def determinantOneBasisCorrection : Prop :=
  ∀ {R K I : Type*} [CommRing R] [Field K] [Algebra R K] [Fintype I] [DecidableEq I]
    (M : Matrix.GeneralLinearGroup I K) (u : Rˣ),
    Units.map (algebraMap R K) u = M.det →
    ∃ B : Matrix.GeneralLinearGroup I R,
      (M * Matrix.GeneralLinearGroup.map (algebraMap R K) B).det = 1

/-- A box with compact coordinates is compact in the restricted product if the box imposes
the defining local conditions outside a finite set. -/
def compactRestrictedProductBox : Prop :=
  ∀ {J : Type*} {L : J → Type*} [∀ j, TopologicalSpace (L j)]
    (U C : ∀ j, Set (L j)),
    (∀ j, IsCompact (C j)) → (∀ᶠ j in Filter.cofinite, C j ⊆ U j) →
    IsCompact {x : Πʳ j, [L j, U j] | ∀ j, x j ∈ C j}

/-- Compact conditions on the basis and its inverse give a compact adelic matrix set.
At the finite places one can take both conditions to be integrality. -/
def compactAdelicBasisBox : Prop :=
  ∀ {J I : Type*} {L : J → Type*} [∀ j, Field (L j)] [∀ j, TopologicalSpace (L j)]
    [∀ j, T1Space (L j)] [∀ j, IsTopologicalRing (L j)] [Fintype I] [DecidableEq I]
    (U : ∀ j, Set (Matrix.GeneralLinearGroup I (L j))) (B : ∀ j, Set (L j)),
    (∀ j, IsCompact (B j)) →
    (∀ᶠ j in Filter.cofinite, ∀ m : Matrix.GeneralLinearGroup I (L j),
      (∀ s t, m.val s t ∈ B j) → (∀ s t, m⁻¹.val s t ∈ B j) → m ∈ U j) →
    IsCompact {x : Πʳ j, [Matrix.GeneralLinearGroup I (L j), U j] |
      ∀ j s t, (x j).val s t ∈ B j ∧ (x j)⁻¹.val s t ∈ B j}

open Classical Arithmetic.LatticeCompletionDecompositionSpec in
/-- The same normalized infinity completion in Laurent-series coordinates. -/
def functionInfinityLaurent : Prop :=
  ∀ (F : Type*) [Field F] [Finite F],
    letI := infinityNormedField F
    ∃ (e : infinityField F ≃+* F⸨X⸩) (h : infinityField F ≃ₜ F⸨X⸩),
      (⇑e = ⇑h) ∧
      (∀ p : F[X], e (infinityEmbedding F (algebraMap F[X] F⟮X⟯ p)) =
        Arithmetic.LaurentLattice.polynomialEmbedding F p) ∧
      ∀ x, Arithmetic.LaurentLattice.absoluteValue F (e x) = ‖x‖

/-- In real coordinates any full basis lattice is discrete and its Haar
covolume is the absolute determinant. The identity is the reference lattice. -/
def realMatrixCovolume : Prop :=
  ∀ (n : ℕ) (H : Matrix.GeneralLinearGroup (Fin n) ℝ),
    let L := matrixLattice (R := ℤ) H
    ∃ (h : DiscreteTopology L) (_hFull : IsZLattice ℝ L),
      letI := h
      ZLattice.covolume L = |H.val.det|

/-- The product of the full integral finite box and a compact entry box at the
distinguished place gives compact adelic representatives. -/
def compactIntegralAdelicBasisBox : Prop :=
  ∀ {R k B N : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
    [Field k] [Algebra R k] [IsFractionRing R k] [Field B] [TopologicalSpace B]
    [T1Space B] [IsTopologicalRing B] [Fintype N] [DecidableEq N]
    (D : Set B), IsCompact D →
    ∃ C : Set (BasisAdeles R k B N), IsCompact C ∧
      ∀ (G : ∀ p : HeightOneSpectrum R, Matrix.GeneralLinearGroup N (p.adicCompletion k))
        (M : Matrix.GeneralLinearGroup N k) (h : FiniteBasisIntegral G M)
        (H : Matrix.GeneralLinearGroup N B),
        (∀ i j, H.val i j ∈ D ∧ H⁻¹.val i j ∈ D) →
        (finiteBasisRepresentative G M h, H) ∈ C

open Arithmetic Arithmetic.RealLatticeReduction in
/-- Uniform adelic reduction in the rational base coordinates. The input
integral finite components, and the rational lattice itself, are preserved by
the integral column change. -/
def boundedRealAdelicBasis : Prop :=
  ∀ (n : ℕ) (ε : ℝ), 0 < ε →
    let N := Fin n
    ∃ (B : ℝ) (C : Set (BasisAdeles ℤ ℚ ℝ N)), 0 < B ∧ IsCompact C ∧
      ∀ (G : ∀ p : HeightOneSpectrum ℤ, Matrix.GeneralLinearGroup N (p.adicCompletion ℚ))
        (GInf : Matrix.GeneralLinearGroup N ℝ) (M : Matrix.GeneralLinearGroup N ℚ),
        GInf.det = 1 → M.det = 1 → FiniteBasisIntegral G M →
        let H₀ := GInf * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M
        (∀ x ∈ basisVectors (Int.castRingHom ℝ) H₀, x ≠ 0 → ε ≤ euclideanLength x) →
        ∃ (M' : Matrix.GeneralLinearGroup N ℚ) (h : FiniteBasisIntegral G M'),
          let H := GInf * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M'
          M'.det = 1 ∧ basisVectors (algebraMap ℤ ℚ) M' = basisVectors (algebraMap ℤ ℚ) M ∧
          entriesBounded B H.val ∧ entriesBounded B H⁻¹.val ∧
          (finiteBasisRepresentative G M' h, H) ∈ C

open Arithmetic Arithmetic.LaurentLattice in
/-- Ordered valuation bases with determinant-one normalization and finite
integrality, under the actual polynomial embedding for the specified Laurent field.
This assertion has no lower-bound hypothesis. -/
def orderedFunctionAdelicBasis : Prop :=
  ∀ {F : Type*} [Field F] [Finite F] (n : ℕ) (f : F⟮X⟯ →+* F⸨X⸩),
    f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F →
    ∀ (G : ∀ p : HeightOneSpectrum F[X], SquareGL n (p.adicCompletion F⟮X⟯))
      (GInf : SquareGL n F⸨X⸩) (M : SquareGL n F⟮X⟯),
      GInf.det = 1 → M.det = 1 → FiniteBasisIntegral G M →
      ∃ (M' : SquareGL n F⟮X⟯) (k : SquareGL n F⟦X⟧) (a : Fin n → ℤ),
        M'.det = 1 ∧ FiniteBasisIntegral G M' ∧
          basisVectors (algebraMap F[X] F⟮X⟯) M' = basisVectors (algebraMap F[X] F⟮X⟯) M ∧
          Monotone a ∧ (∑ i, a i) = 0 ∧ k.val.det = 1 ∧
          (GInf * Matrix.GeneralLinearGroup.map f M').val =
            k.val.map (HahnSeries.ofPowerSeries ℤ F) * Matrix.diagonal (polePower F ∘ a)

open Arithmetic Arithmetic.LaurentLattice in
/-- With a lower bound on lengths the ordered exponents, the matrix and its
inverse have uniform bounds. Finite integrality and determinant one are retained. -/
def boundedFunctionAdelicBasis : Prop :=
  ∀ {F : Type*} [Field F] [Finite F] (n : ℕ) (f : F⟮X⟯ →+* F⸨X⸩),
    f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F →
    ∀ ε : ℝ, 0 < ε →
      ∃ (B : ℕ) (C : Set (BasisAdeles F[X] F⟮X⟯ F⸨X⸩ (Fin n))), IsCompact C ∧
        ∀ (G : ∀ p : HeightOneSpectrum F[X], SquareGL n (p.adicCompletion F⟮X⟯))
          (GInf : SquareGL n F⸨X⸩) (M : SquareGL n F⟮X⟯),
          GInf.det = 1 → M.det = 1 → FiniteBasisIntegral G M →
          let H₀ := GInf * Matrix.GeneralLinearGroup.map f M
          (∀ x ∈ basisVectors (polynomialEmbedding F) H₀, x ≠ 0 → ε ≤ length F x) →
          ∃ (M' : SquareGL n F⟮X⟯) (h : FiniteBasisIntegral G M')
            (k : SquareGL n F⟦X⟧) (a : Fin n → ℤ),
            let H := GInf * Matrix.GeneralLinearGroup.map f M'
            M'.det = 1 ∧
              basisVectors (algebraMap F[X] F⟮X⟯) M' = basisVectors (algebraMap F[X] F⟮X⟯) M ∧
              Monotone a ∧ (∑ i, a i) = 0 ∧ k.val.det = 1 ∧
              H.val = k.val.map (HahnSeries.ofPowerSeries ℤ F) * Matrix.diagonal (polePower F ∘ a) ∧
              (∀ i, |a i| ≤ (B : ℤ)) ∧
              (∀ i j, absoluteValue F (H.val i j) ≤ (Nat.card F : ℝ) ^ B ∧
                absoluteValue F (H⁻¹.val i j) ≤ (Nat.card F : ℝ) ^ B) ∧
              (finiteBasisRepresentative G M' h, H) ∈ C

open Arithmetic in
/-- The matrix lattice is exactly the image of the actual rational intersection
under the distinguished diagonal embedding and distinguished operator. -/
def distinguishedLatticeImage : Prop :=
  ∀ {R k B V N : Type*} [CommRing R] [Field k] [Field B] [Algebra R k]
    [AddCommGroup V] [Module k V] [Fintype N] [DecidableEq N]
    (b : Module.Basis N k V) (L : Set V) (M : Matrix.GeneralLinearGroup N k),
    IsBasisMatrix R b L M →
    ∀ (f : k →+* B) (G : Matrix.GeneralLinearGroup N B),
      Set.range (fun x : L => G.val.mulVec (embedCoordinates f (b.equivFun (x : V)))) =
        basisVectors (f.comp (algebraMap R k)) (G * Matrix.GeneralLinearGroup.map f M)

open Arithmetic Arithmetic.RealLatticeReduction in
/-- Uniform compact basis representatives for the number-field rational
intersections. The archimedean operator is the product of the given local
operators on the original real and complex factors. -/
def numberAdelicLatticeBounds : Prop :=
  ∀ {K I P : Type*} [Field K] [NumberField K] [Fintype I] [DecidableEq I] [Fintype P]
    (L₀ : Submodule (𝓞 K) (I → K)) [Submodule.IsLattice K L₀]
    (p : P → MvPolynomial I K) (d : P → ℕ),
    (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) → IntegralOnReference L₀ p →
    let N := Fin (Module.finrank ℚ (I → K))
    ∃ (b : Module.Basis N ℚ (I → K)) (a : ∀ w : NumberField.InfinitePlace K, Algebra ℝ w.Completion),
      letI := a
      ∃ E : (N → ℝ) ≃L[ℝ] (∀ w : NumberField.InfinitePlace K, I → w.Completion),
        IsBasisMatrix ℤ b (L₀ : Set (I → K)) 1 ∧
        (∀ x w, E (embedCoordinates (algebraMap ℚ ℝ) (b.equivFun x)) w =
          embedCoordinates (algebraMap K w.Completion) x) ∧
        ∃ (ε B : ℝ) (C : Set (BasisAdeles ℤ ℚ ℝ N)), 0 < ε ∧ 0 < B ∧ IsCompact C ∧
          ∀ (Q : ∀ v : NumberFinitePlace K,
              Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K))
            [∀ v, Submodule.IsLattice (v.adicCompletion K) (Q v)],
            {v | Q v ≠ completedLattice v L₀}.Finite →
            let L := rationalLatticeIntersection Q
            let LInf := Set.range (fun x : L => embedCoordinates (algebraMap ℚ ℝ) (b.equivFun (x : I → K)))
            LatticeIntersectionConclusion (B := ℤ) L₀ Q ∧
            DiscreteTopology LInf ∧ Submodule.span ℝ LInf = ⊤ ∧
            ∀ (g : ∀ v : NumberFinitePlace K, Matrix.GeneralLinearGroup I (v.adicCompletion K))
              (gInf : ∀ w : NumberField.InfinitePlace K, Matrix.GeneralLinearGroup I w.Completion),
              (∀ v, (g v).det = 1) →
              (∀ v, (g v).val.mulVec '' (Q v : Set (I → v.adicCompletion K)) =
                (completedLattice v L₀ : Set (I → v.adicCompletion K))) →
              (∀ w, (gInf w).det = 1) →
              PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g →
              PreservesPolynomials (fun w => algebraMap K w.Completion) p gInf →
              (∀ x ∈ L, x ≠ 0 → ∃ b, (p b).eval x ≠ 0) →
              ∃ (G : ∀ q : HeightOneSpectrum ℤ, Matrix.GeneralLinearGroup N (q.adicCompletion ℚ))
                (GInf : Matrix.GeneralLinearGroup N ℝ) (M : Matrix.GeneralLinearGroup N ℚ)
                (h : FiniteBasisIntegral G M),
                let H := GInf * Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M
                (∀ q, (G q).det = 1 ∧ FiniteMatrixAction b g q (G q)) ∧
                GInf.det = 1 ∧ (∀ z w, E (GInf.val.mulVec z) w = (gInf w).val.mulVec (E z w)) ∧
                IsBasisMatrix ℤ b (L : Set (I → K)) M ∧ M.det = 1 ∧
                RealCovolumeOne (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) M) ∧
                RealCovolumeOne H ∧
                (∀ z ∈ basisVectors (Int.castRingHom ℝ) H, z ≠ 0 → ε ≤ euclideanLength z) ∧
                entriesBounded B H.val ∧ entriesBounded B H⁻¹.val ∧
                (finiteBasisRepresentative G M h, H) ∈ C

open Classical Arithmetic Arithmetic.LaurentLattice
  Arithmetic.LatticeCompletionDecompositionSpec MeasureTheory in
/-- The rational intersection over the polynomial base admits a
determinant-one ordered basis for every choice of the local changes. The
invariant polynomials give a uniform positive lower bound and a uniform
compact adelic set. The infinity action is the original product action
on every place above the pole of the parameter. -/
def functionAdelicLatticeBounds : Prop :=
  ∀ {F K I P : Type*} [Field F] [Finite F] [Field K] [Algebra F K]
    [Fintype I] [DecidableEq I] [Fintype P] (t : SeparatingParameter F K)
    (L₀ : Submodule t.integerRing (I → K)) [Submodule.IsLattice K L₀]
    (p : P → MvPolynomial I K) (d : P → ℕ),
    (∀ b, 0 < d b ∧ (p b).IsHomogeneous (d b)) → IntegralOnReference L₀ p →
    letI := t.rationalAlgebra
    letI := parameterIntegerRing_torsionFree t
    let N := Fin (Module.finrank F⟮X⟯ (I → K))
    let B := infinityField F
    let J := {w : FunctionPlace K // t.element ∉ w.val}
    letI (w : J) : Field w.val.Completion := inferInstance
    letI : MeasurableSpace F⸨X⸩ := borel _
    ∃ (b : Module.Basis N F⟮X⟯ (I → K)) (a : ∀ w : J, Algebra B w.val.Completion),
      letI := a
      ∃ (E : (N → B) ≃L[B] (∀ w : J, I → w.val.Completion))
        (e : B ≃+* F⸨X⸩) (h : B ≃ₜ F⸨X⸩),
        let f := e.toRingHom.comp (infinityEmbedding F)
        IsBasisMatrix F[X] b (L₀ : Set (I → K)) 1 ∧
        (∀ x w, E (embedCoordinates (infinityEmbedding F) (b.equivFun x)) w =
          embedCoordinates w.val.embedding x) ∧ (⇑e = ⇑h) ∧
        f.comp (algebraMap F[X] F⟮X⟯) = polynomialEmbedding F ∧
        ∃ μ : Measure (N → F⸨X⸩), μ.IsAddHaarMeasure ∧ μ (standardDomain F _) = 1 ∧
          ∃ (ε : ℝ) (D : ℕ) (C : Set (BasisAdeles F[X] F⟮X⟯ F⸨X⸩ N)), 0 < ε ∧ IsCompact C ∧
            ∀ (Q : ∀ v : HeightOneSpectrum t.integerRing,
                Submodule (v.adicCompletionIntegers K) (I → v.adicCompletion K))
              [∀ v, Submodule.IsLattice (v.adicCompletion K) (Q v)],
              {v | Q v ≠ completedLattice v L₀}.Finite →
              let L := rationalLatticeIntersection Q
              let LInf := Set.range (fun x : L => embedCoordinates f (b.equivFun (x : I → K)))
              LatticeIntersectionConclusion (B := F[X]) L₀ Q ∧
              DiscreteTopology LInf ∧ Submodule.span F⸨X⸩ LInf = ⊤ ∧
              ∀ (g : ∀ v : HeightOneSpectrum t.integerRing,
                  Matrix.GeneralLinearGroup I (v.adicCompletion K))
                (gInf : ∀ w : J, Matrix.GeneralLinearGroup I w.val.Completion),
                (∀ v, (g v).det = 1) →
                (∀ v, (g v).val.mulVec '' (Q v : Set (I → v.adicCompletion K)) =
                  (completedLattice v L₀ : Set (I → v.adicCompletion K))) →
                (∀ w, (gInf w).det = 1) →
                ∃ (G : ∀ q : HeightOneSpectrum F[X], Matrix.GeneralLinearGroup N (q.adicCompletion F⟮X⟯))
                  (GInf : Matrix.GeneralLinearGroup N B) (M : Matrix.GeneralLinearGroup N F⟮X⟯)
                  (hI : FiniteBasisIntegral G M) (k : Matrix.GeneralLinearGroup N F⟦X⟧) (s : N → ℤ),
                  let H := Matrix.GeneralLinearGroup.map e.toRingHom GInf * Matrix.GeneralLinearGroup.map f M
                  (∀ q, (G q).det = 1 ∧ FiniteMatrixAction b g q (G q)) ∧
                  GInf.det = 1 ∧ (∀ z w, E (GInf.val.mulVec z) w = (gInf w).val.mulVec (E z w)) ∧
                  IsBasisMatrix F[X] b (L : Set (I → K)) M ∧ M.det = 1 ∧
                  LaurentCovolumeOne μ (Matrix.GeneralLinearGroup.map f M) ∧ LaurentCovolumeOne μ H ∧
                  Monotone s ∧ (∑ i, s i) = 0 ∧ k.val.det = 1 ∧
                  H.val = k.val.map (HahnSeries.ofPowerSeries ℤ F) * Matrix.diagonal (polePower F ∘ s) ∧
                  (PreservesPolynomials (fun v => algebraMap K (v.adicCompletion K)) p g →
                    PreservesPolynomials (fun w => w.val.embedding) p gInf →
                    (∀ x ∈ L, x ≠ 0 → ∃ j, (p j).eval x ≠ 0) →
                    (∀ z ∈ basisVectors (polynomialEmbedding F) H, z ≠ 0 → ε ≤ length F z) ∧
                    (∀ i, |s i| ≤ (D : ℤ)) ∧
                    (∀ i j, absoluteValue F (H.val i j) ≤ (Nat.card F : ℝ) ^ D ∧
                      absoluteValue F (H⁻¹.val i j) ≤ (Nat.card F : ℝ) ^ D) ∧
                    (finiteBasisRepresentative G M hI, H) ∈ C)

end LinearAlgebraicGroups.Specs.AdelicLatticeBounds
