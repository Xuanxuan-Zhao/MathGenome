import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
Interfaces for HA-A07, notes/002/advanced-homological-algebra.tex:3227–3256.
The coefficient ring may have zero divisors or be the zero ring. The variable
type and the rank of the free module are unrestricted.

`FullExactness` records the original symmetric/exterior obligation. The
finite-list results below are supporting obligations, not substitutes for it.
-/

noncomputable section
open scoped TensorProduct
universe u v w

namespace AdvancedHomologicalAlgebra.SymmetricKoszul

variable {R : Type u} [CommRing R] {I : Type v}

/-- Variables in a subset, considered inside the polynomial ring on ALL variables. -/
def variableIdeal (s : Set I) : Ideal (MvPolynomial I R) :=
  Ideal.span (MvPolynomial.X '' s)

/-- Evaluation kills exactly the selected variables and retains the others. -/
def killVariables (s : Set I) :
    MvPolynomial I R →ₐ[R] MvPolynomial {i : I // i ∉ s} R := by
  classical
  exact MvPolynomial.aeval fun i =>
    if h : i ∈ s then 0 else MvPolynomial.X ⟨i, h⟩

def variableList (l : List I) : List (MvPolynomial I R) := l.map MvPolynomial.X

/-- Canonical augmentation for a finite subset, still over all variables. -/
def finiteAugmentation (l : List I) :
    (⋀[MvPolynomial I R]^0 (Fin (variableList (R := R) l).length → MvPolynomial I R))
      →ₗ[MvPolynomial I R] (MvPolynomial I R ⧸ variableIdeal {i | i ∈ l}) :=
  (variableIdeal {i | i ∈ l}).mkQ.comp
    (exteriorPower.zeroEquiv (MvPolynomial I R) _).toLinearMap

/-- The universal polynomial linear form, on a direct sum with arbitrary index type. -/
def polynomialForm : (I →₀ MvPolynomial I R) →ₗ[MvPolynomial I R] MvPolynomial I R :=
  Finsupp.linearCombination (MvPolynomial I R) MvPolynomial.X

/-- The degree-zero augmentation of the coordinate Koszul complex. -/
def polynomialAugmentation : (⋀[MvPolynomial I R]^0 (I →₀ MvPolynomial I R)) →ₗ[R] R :=
  (MvPolynomial.aeval (fun _ : I => (0 : R))).toLinearMap.comp
    ((exteriorPower.zeroEquiv (MvPolynomial I R) _).toLinearMap.restrictScalars R)

variable (R) (M : Type w) [AddCommGroup M] [Module R M]

/-- The terms in the source, before choosing coordinates or changing scalars. -/
abbrev Term (n : ℕ) := SymmetricAlgebra R M ⊗[R] (⋀[R]^n M)

/-- Exterior degree zero identifies the degree-zero term with the symmetric algebra. -/
def zeroTermEquiv : Term R M 0 ≃ₗ[R] SymmetricAlgebra R M :=
  (TensorProduct.congr (LinearEquiv.refl R _) (exteriorPower.zeroEquiv R M)).trans
    (TensorProduct.rid R _)

/-- The source augmentation: evaluate all symmetric generators at zero. -/
def augmentation : Term R M 0 →ₗ[R] R :=
  (SymmetricAlgebra.lift (0 : M →ₗ[R] R)).toLinearMap.comp
    (zeroTermEquiv R M).toLinearMap

variable {R M}

/-- Total weight a in degree n is polynomial degree a-n and exterior degree n.
Using n + degree = a also makes the space zero when a < n. -/
def weightSpace (b : Module.Basis I R M) (a n : ℕ) : Submodule R (Term R M n) :=
  Submodule.span R {z | ∃ (m : I →₀ ℕ) (w : ⋀[R]^n M),
    n + m.degree = a ∧ z = b.symmetricAlgebra m ⊗ₜ[R] w}

end AdvancedHomologicalAlgebra.SymmetricKoszul

namespace Specs.AdvancedHomologicalAlgebra.SymmetricKoszul
open _root_.AdvancedHomologicalAlgebra.SymmetricKoszul
open _root_.AdvCommAlg.Koszul

def QuotientIdentification : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (s : Set I),
    ∃ e : (MvPolynomial I R ⧸ variableIdeal s) ≃ₐ[R]
        MvPolynomial {i : I // i ∉ s} R,
      ∀ p, e (Ideal.Quotient.mk _ p) = killVariables s p

def VariableRegularity : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (s : Set I) (i : I), i ∉ s →
    IsSMulRegular (MvPolynomial I R ⧸ variableIdeal s) (MvPolynomial.X (R := R) i)

def FiniteWeakRegularity : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (l : List I), l.Nodup →
    RingTheory.Sequence.IsWeaklyRegular (MvPolynomial I R) (variableList (R := R) l)

/-- Positive-degree exactness for a finite subset over the whole polynomial ring. -/
def FiniteExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (l : List I), l.Nodup →
    ∀ n : ℕ, 0 < n → (listComplex (R := MvPolynomial I R) (variableList l)).ExactAt n

def FiniteAugmentedExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (l : List I),
    LinearMap.range (differential (listForm (variableList (R := R) l)) 0) =
      LinearMap.ker (finiteAugmentation l) ∧
    Function.Surjective (finiteAugmentation (R := R) l)

def FiniteDeletionFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (l : List I) (n : ℕ)
    (x : Fin (n+1) → (Fin (variableList (R := R) l).length → MvPolynomial I R)),
    differential (listForm (variableList l)) n
      (exteriorPower.ιMulti (MvPolynomial I R) (n+1) x) =
      ∑ i : Fin (n+1), (-1 : MvPolynomial I R)^i.val •
        (listForm (variableList l) (x i) •
          exteriorPower.ιMulti (MvPolynomial I R) n (x ∘ i.succAbove))

def FiniteZeroHomology : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v) (l : List I),
    Nonempty (homology (MvPolynomial I R) (variableList (R := R) l) 0 ≃ₗ[MvPolynomial I R]
      (MvPolynomial I R ⧸ variableIdeal {i | i ∈ l}))

def AllVariablesQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v),
    ∃ e : (MvPolynomial I R ⧸ variableIdeal (Set.univ : Set I)) ≃ₐ[R] R,
      ∀ p, e (Ideal.Quotient.mk _ p) = MvPolynomial.constantCoeff p

/-- Exactness of the arbitrary-rank coordinate complex, with its actual augmentation. -/
def ArbitraryRankExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type v),
    (∀ (n : ℕ) (z : ⋀[MvPolynomial I R]^(n+1) (I →₀ MvPolynomial I R)),
      differential (polynomialForm (R := R) (I := I)) n z = 0 →
      ∃ y, differential (polynomialForm (R := R) (I := I)) (n+1) y = z) ∧
    (∀ z : ⋀[MvPolynomial I R]^0 (I →₀ MvPolynomial I R),
      polynomialAugmentation z = 0 → ∃ y, differential (polynomialForm (R := R) (I := I)) 0 y = z) ∧
    (∀ z, polynomialAugmentation (differential (polynomialForm (R := R) (I := I)) 0 z) = 0) ∧
    Function.Surjective (polynomialAugmentation (R := R) (I := I))

/-- Augmented exactness on the original tensor terms, before recording weights.
An explicit basis is quantified without imposing a cardinality bound. -/
def UnweightedExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (I : Type v) (b : Module.Basis I R M),
    ∃ d : ∀ n : ℕ, Term R M (n+1) →ₗ[SymmetricAlgebra R M] Term R M n,
      (∀ (n : ℕ) (p : SymmetricAlgebra R M) (x : Fin (n+1) → M),
        d n (p ⊗ₜ[R] exteriorPower.ιMulti R (n+1) x) =
          ∑ i : Fin (n+1), (-1 : R)^i.val •
            ((p * SymmetricAlgebra.ι R M (x i)) ⊗ₜ[R]
              exteriorPower.ιMulti R n (x ∘ i.succAbove))) ∧
      (∀ n, (d n).comp (d (n+1)) = 0) ∧
      (∀ z, augmentation R M (d 0 z) = 0) ∧
      Function.Surjective (augmentation R M) ∧
      (∀ (n : ℕ) (z : Term R M (n+1)),
        d n z = 0 → ∃ y, d (n+1) y = z) ∧
      (∀ z : Term R M 0, augmentation R M z = 0 → ∃ y, d 0 y = z) ∧
      (Nonempty ((Term R M 0 ⧸ LinearMap.range ((d 0).restrictScalars R)) ≃ₗ[R] R))

/-- The complete target, including the signed differential, augmentation, H₀,
and exactness in every total weight, for free modules of arbitrary rank. -/
def FullExactness : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    (I : Type v) (b : Module.Basis I R M),
    ∃ d : ∀ n : ℕ, Term R M (n+1) →ₗ[SymmetricAlgebra R M] Term R M n,
      (∀ (n : ℕ) (p : SymmetricAlgebra R M) (x : Fin (n+1) → M),
        d n (p ⊗ₜ[R] exteriorPower.ιMulti R (n+1) x) =
          ∑ i : Fin (n+1), (-1 : R)^i.val •
            ((p * SymmetricAlgebra.ι R M (x i)) ⊗ₜ[R]
              exteriorPower.ιMulti R n (x ∘ i.succAbove))) ∧
      (∀ n, (d n).comp (d (n+1)) = 0) ∧
      (∀ z, augmentation R M (d 0 z) = 0) ∧
      Function.Surjective (augmentation R M) ∧
      (∀ (n : ℕ) (z : Term R M (n+1)),
        d n z = 0 → ∃ y, d (n+1) y = z) ∧
      (∀ z : Term R M 0, augmentation R M z = 0 → ∃ y, d 0 y = z) ∧
      (Nonempty ((Term R M 0 ⧸ LinearMap.range ((d 0).restrictScalars R)) ≃ₗ[R] R)) ∧
      (∀ (a n : ℕ) (z : Term R M (n+1)), z ∈ weightSpace b a (n+1) →
        d n z ∈ weightSpace b a n) ∧
      (∀ (a n : ℕ) (z : Term R M (n+1)), z ∈ weightSpace b a (n+1) →
        d n z = 0 → ∃ y ∈ weightSpace b a (n+2), d (n+1) y = z) ∧
      (∀ (a : ℕ) (z : Term R M 0), z ∈ weightSpace b a 0 →
        augmentation R M z = 0 → ∃ y ∈ weightSpace b a 1, d 0 y = z) ∧
      (∀ r : R, ∃ z ∈ weightSpace b 0 0, augmentation R M z = r) ∧
      (∀ (a : ℕ) (z : Term R M 0), 0 < a → z ∈ weightSpace b a 0 →
        augmentation R M z = 0)

end Specs.AdvancedHomologicalAlgebra.SymmetricKoszul
