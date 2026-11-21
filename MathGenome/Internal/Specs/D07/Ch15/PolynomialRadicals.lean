import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
K07.15.polynomial_radicals, paper.tex:4379–4390.
The closure Ω is fixed by its algebra structure; all roots, not merely one
root, are required. Nonzero constants and repeated/inseparable factors are
allowed. No characteristic or separability assumption occurs.

A finite tower means finitely many radical adjunctions, using exactly the
upstream radical predicates. Its final field has finite degree by the
upstream ExtensionFinite theorem. Splitting fields are arbitrary models S.
The final statement permits the radical extension to be presented in a
different algebraic overfield, and compares it with the fixed closure.
-/

universe u v w t
namespace Specs.D07.Ch15.PolynomialRadicals
open Specs.D07.Ch15.RadicalDefinition

/-- Solvability is defined for nonzero polynomials and requires every root. -/
def PolynomialSolvableType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω], Polynomial K → Prop

def polynomialSolvableValue : PolynomialSolvableType.{u, v} :=
  fun K Ω _ _ _ _ _ f => f ≠ 0 ∧
    ∀ x : Ω, Polynomial.aeval x f = 0 → solvableByRadicalsValue K Ω x

/-- All roots lie in the final field of one finite radical tower. -/
def CommonTowerType : Type (max u v + 1) :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω], Polynomial K → Prop

def commonTowerValue : CommonTowerType.{u, v} :=
  fun K Ω _ _ _ _ f =>
    ∃ (r : ℕ) (T : Fin (r + 1) → IntermediateField K Ω),
      radicalTowerValue K Ω r T ∧
        ∀ x : Ω, Polynomial.aeval x f = 0 → x ∈ T (Fin.last r)

/-- A splitting-field model embeds into a finite radical extension in Ω. -/
def RadicalEmbeddingType : Type (max u v w + 1) :=
  ∀ (K : Type u) (Ω : Type v) (S : Type w) [Field K] [Field Ω] [Field S]
    [Algebra K Ω] [Algebra K S] [Algebra.IsAlgebraic K Ω], Prop

def radicalEmbeddingValue : RadicalEmbeddingType.{u, v, w} :=
  fun K Ω S _ _ _ _ _ _ =>
    ∃ E : IntermediateField K Ω, radicalExtensionValue K Ω E ∧
      Nonempty (S →ₐ[K] E)

def SolvableIffCommonTower : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (f : Polynomial K), f ≠ 0 →
      (polynomialSolvableValue K Ω f ↔ commonTowerValue K Ω f)

def SolvableIffSplittingFieldEmbedding : Prop :=
  ∀ (K : Type u) (Ω : Type v) (S : Type w) [Field K] [Field Ω] [Field S]
    [Algebra K Ω] [Algebra K S] [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω]
    (f : Polynomial K) [Polynomial.IsSplittingField K S f], f ≠ 0 →
      (polynomialSolvableValue K Ω f ↔ radicalEmbeddingValue K Ω S)

/-- Representation independence: the proposed radical extension may be in
any algebraic overfield Ω', with its specified K-action. -/
def SolvableOfEmbeddingInOverfield : Prop :=
  ∀ (K : Type u) (Ω : Type v) (S : Type w) (Ω' : Type t)
    [Field K] [Field Ω] [Field S] [Field Ω'] [Algebra K Ω] [Algebra K S]
    [Algebra K Ω'] [Algebra.IsAlgebraic K Ω] [Algebra.IsAlgebraic K Ω']
    [IsAlgClosed Ω] (f : Polynomial K) [Polynomial.IsSplittingField K S f],
    f ≠ 0 → ∀ E : IntermediateField K Ω', radicalExtensionValue K Ω' E →
      Nonempty (S →ₐ[K] E) → polynomialSolvableValue K Ω f

end Specs.D07.Ch15.PolynomialRadicals
