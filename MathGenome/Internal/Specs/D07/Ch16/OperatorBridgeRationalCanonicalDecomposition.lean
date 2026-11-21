import MathGenome.Internal.Specs.D07.Ch16.OperatorBridgePolynomialModuleCorrespondence
import MathGenome.Internal.Specs.D05.M10.InvariantFactors
import MathGenome.Internal.Specs.D05.M10.JordanExistence
import Mathlib.Algebra.Module.Torsion.Basic

/-! Independent statements for paper.tex:3338–3380. Finite products are finite
external direct sums. The polynomial action is the actual evaluation action,
not an assumed annihilator certificate. All fields, including finite fields,
and empty block families are allowed. -/
noncomputable section
universe u v w
namespace Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
open Polynomial Module
open scoped BigOperators

abbrev Cyclic {F : Type u} [Field F] (f : F[X]) := F[X] ⧸ Ideal.span {f}

/-- Monicity, exclusion of constant factors, and the ascending divisibility order. -/
def Normalized {F : Type u} [Field F] {s : ℕ} (f : Fin s → F[X]) : Prop :=
  (∀ i, (f i).Monic) ∧ (∀ i, 0 < (f i).natDegree) ∧
    (∀ i j, i ≤ j → f i ∣ f j)

/-- An actual polynomial-linear equivalence of the evaluated module. -/
def HasFactors {F : Type u} [Field F] {V : Type v} [AddCommGroup V]
    [Module F V] (T : Module.End F V) {s : ℕ} (f : Fin s → F[X]) : Prop :=
  Nonempty (Module.AEval' T ≃ₗ[F[X]] (∀ i, Cyclic (f i)))

abbrev companion {F : Type u} [Field F] (f : F[X]) :=
  Specs.D05.M10.Companion.companionMatrix_value F f

/-- The synonym really carries the same evaluation action as the source. -/
def EvaluationAction : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    (T : Module.End F V) (p : F[X]) (x : V),
    (Module.AEval'.of T).symm (p • Module.AEval'.of T x) = aeval T p x

def FiniteTorsion : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    Module.Finite F[X] (Module.AEval' T) ∧ Module.IsTorsion F[X] (Module.AEval' T)

def RationalDecomposition : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V),
    ∃ (s : ℕ) (f : Fin s → F[X]), Normalized f ∧ HasFactors T f

/-- The prescribed residue power bases, and hence the companion convention,
are retained; irreducibility of f is not required. -/
def CompanionQuotient : Prop :=
  ∀ (F : Type u) [Field F] (f : F[X]) (hf : f.Monic), 0 < f.natDegree →
    ∃ b : Basis (Fin f.natDegree) F (AdjoinRoot f),
      (∀ i, b i = AdjoinRoot.mk f (X ^ i.val)) ∧
      LinearMap.toMatrix b b (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) =
        companion f ∧
      (∀ p : F[X], aeval (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) p = 0 ↔ f ∣ p) ∧
      (letI := hf.finite_adjoinRoot
       (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)).charpoly = f ∧
       minpoly F (Algebra.lmul F (AdjoinRoot f) (AdjoinRoot.root f)) = f)

/-- Every normalized quotient representation, not just one chosen witness,
gives the stated blocks, dimension, characteristic and minimal polynomials. -/
def BlockFormulas : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (s : ℕ) (f : Fin s → F[X]),
    Normalized f → HasFactors T f →
    (∃ b : Basis (Σ i, Fin (f i).natDegree) F V,
      LinearMap.toMatrix b b T = Matrix.blockDiagonal' (fun i => companion (f i))) ∧
    (∑ i, (f i).natDegree) = finrank F V ∧
    T.charpoly = ∏ i, f i ∧
    (s = 0 ↔ finrank F V = 0) ∧
    (∀ h : 0 < s, minpoly F T = f ⟨s - 1, Nat.sub_lt h (by decide)⟩)

def FactorUniqueness : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (s t : ℕ)
    (f : Fin s → F[X]) (g : Fin t → F[X]),
    Normalized f → Normalized g → HasFactors T f → HasFactors T g →
    List.ofFn f = List.ofFn g

/-- Same invariant factors if and only if the operators are intertwined by
an invertible map over F, also when their ambient types differ. -/
def SimilarityClassification : Prop :=
  ∀ (F : Type u) [Field F]
    (V : Type v) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (W : Type w) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (T : Module.End F V) (S : Module.End F W)
    (s t : ℕ) (f : Fin s → F[X]) (g : Fin t → F[X]),
    Normalized f → Normalized g → HasFactors T f → HasFactors S g →
    ((∃ e : V ≃ₗ[F] W, ∀ x, e (T x) = S (e x)) ↔ List.ofFn f = List.ofFn g)

def ZeroSpace : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V), finrank F V = 0 →
    T.charpoly = 1 ∧ minpoly F T = 1 ∧
      ∃ f : Fin 0 → F[X], Normalized f ∧ HasFactors T f

/-- Reversed powers of X-λ, in the actual quotient by (X-λ)^e.
The multiplication operator is λI plus the superdiagonal shift. -/
def JordanQuotient : Prop :=
  ∀ (F : Type u) [Field F] (lam : F) (e : ℕ), 0 < e →
    ∃ b : Basis (Fin e) F (AdjoinRoot ((X - C lam) ^ e)),
      (∀ j, b j = AdjoinRoot.mk _ ((X - C lam) ^ (e - 1 - j.val))) ∧
      (∀ j, j.val = 0 →
        AdjoinRoot.root _ * b j = lam • b j) ∧
      (∀ j k, j.val = k.val + 1 →
        AdjoinRoot.root _ * b j = lam • b j + b k)

/-- Splitting is assumed only here. The primary summands are literal
quotients by powers of linear factors, and their X-action gives Jordan form. -/
def SplitPrimaryJordan : Prop :=
  ∀ (F : Type u) [Field F] (V : Type v) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (T : Module.End F V) (s : ℕ) (f : Fin s → F[X]),
    Normalized f → HasFactors T f → (∀ i, (f i).Splits) →
    ∃ (r : ℕ) (e : Fin r → ℕ) (lam : Fin r → F),
      (∀ i, 0 < e i) ∧ HasFactors T (fun i => (X - C (lam i)) ^ e i) ∧
      ∃ b : Basis (Σ i, Fin (e i)) F V,
        LinearMap.toMatrix b b T = Specs.D05.M10.JordanExistence.jordanMatrix e lam ∧
        (∑ i, e i) = finrank F V

/-- The finite-dimensional hypothesis is substantive even for algebraic T. -/
def InfiniteAlgebraicExample : Prop :=
  ∀ (F : Type u) [Field F],
    ¬ FiniteDimensional F F[X] ∧ aeval (0 : Module.End F F[X]) (X : F[X]) = 0

end Specs.D07.Ch16.OperatorBridgeRationalCanonicalDecomposition
