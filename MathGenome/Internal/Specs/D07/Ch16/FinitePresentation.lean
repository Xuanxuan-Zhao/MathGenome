import MathGenome.Internal.Specs.D07.Ch16.FinitePresentationFiniteRelationsCounterexample
import MathGenome.Internal.Specs.D07.Ch16.PidSubmodulesFinite
import MathGenome.Internal.Specs.D07.Ch16.QuotientsIsomorphism
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Independent statements for K07.16.finite_presentation, paper.tex:3091–3122.
General presentations use arbitrary associative unital rings and unital LEFT
modules, including the zero ring, empty matrices, and zero modules.

A matrix has its relation vectors as columns. For a left module over a
noncommutative ring, coefficients multiply entries on the LEFT: the induced
map is x ↦ ∑ j, x j • column j. This is the unique left-linear map sending
the standard vectors to those columns. Over a commutative ring this agrees
with the usual column-vector matrix action. No commutativity is imposed on
the general finite-presentation statements; it is imposed for PID results.
-/

universe u v
noncomputable section
namespace Specs.D07.Ch16.FinitePresentation

/-- The actual linear map determined by the finite list of relation columns. -/
def matrixMap {R : Type u} [Ring R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : (Fin m → R) →ₗ[R] (Fin n → R) :=
  (Module.Basis.constr (Pi.basisFun R (Fin m)) ℕ) (fun j i => A i j)

/-- The definition in the paper, for all rings and all left modules. -/
def FinitePresentationCriterion : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M ↔
      ∃ (n : ℕ) (π : (Fin n → R) →ₗ[R] M),
        Function.Surjective π ∧ (LinearMap.ker π).FG

/-- The columns are precisely the generator images, and generate the image. -/
def MatrixColumns : Prop :=
  ∀ (R : Type u) [Ring R] (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
    (∀ (x : Fin m → R) (i : Fin n), matrixMap A x i = ∑ j, x j * A i j) ∧
    (∀ j, matrixMap A (Pi.single j 1) = fun i => A i j) ∧
    LinearMap.range (matrixMap A) = Submodule.span R (Set.range (fun j i => A i j))

/-- On commutative rings the relation map is exactly the canonical matrix map. -/
def MatrixMapAgreement : Prop :=
  ∀ (R : Type u) [CommRing R] (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
    matrixMap A = A.mulVecLin

/-- Each specified finite presentation gives a finite relation matrix and the
first-isomorphism equivalence, with its formula on the given generators. -/
def PresentationMatrix : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (π : (Fin n → R) →ₗ[R] M),
    Function.Surjective π → (LinearMap.ker π).FG →
    ∃ (m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      LinearMap.range (matrixMap A) = LinearMap.ker π ∧
      ∃ e : M ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range (matrixMap A)),
        ∀ x, e (π x) = (LinearMap.range (matrixMap A)).mkQ x

/-- Conversely a finite matrix presents its cokernel, with finitely many
relations (not merely finitely many generators of the quotient). -/
def CokernelPresentation : Prop :=
  ∀ (R : Type u) [Ring R] (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
    let N := LinearMap.range (matrixMap A)
    Function.Surjective N.mkQ ∧ LinearMap.ker N.mkQ = N ∧ N.FG ∧
      Module.FinitePresentation R ((Fin n → R) ⧸ N)

/-- Finite matrix cokernels are exactly the finitely presented modules. -/
def MatrixCriterion : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    Module.FinitePresentation R M ↔
      ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
        Nonempty (M ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range (matrixMap A)))

/-- The kernel of every chosen finite free cover over a PID is finite free. -/
def PidKernelFree : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
      Module.Free R (LinearMap.ker π) ∧ Module.Finite R (LinearMap.ker π)

/-- A finitely generated PID-module has a finite presentation and therefore
a finite matrix cokernel description. -/
def PidPresentation : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M],
    Module.FinitePresentation R M ∧
      ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
        Nonempty (M ≃ₗ[R] ((Fin n → R) ⧸ LinearMap.range (matrixMap A)))

/-- The cyclic module in the source is finitely generated, but no finite
free cover has finitely generated kernel. The stronger obstruction and
residue algebra identification are supplied by the counterexample goal. -/
def FiniteGenerationInsufficient : Prop :=
  ∀ (k : Type u) [Field k],
    let R := FinitePresentationFiniteRelationsCounterexample.PolynomialRing k
    let I := FinitePresentationFiniteRelationsCounterexample.variablesIdeal k
    Module.Finite R (R ⧸ I) ∧ ¬ Module.FinitePresentation R (R ⧸ I) ∧
      ∀ (n : ℕ) (π : (Fin n → R) →ₗ[R] (R ⧸ I)),
        Function.Surjective π → ¬ (LinearMap.ker π).FG

end Specs.D07.Ch16.FinitePresentation
