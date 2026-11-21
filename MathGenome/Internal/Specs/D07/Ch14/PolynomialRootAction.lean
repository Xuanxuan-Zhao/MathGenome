import MathGenome.Internal.Specs.D07.Ch14.SplittingCriterion
import Mathlib.Algebra.Group.End
import Mathlib.Data.Fintype.EquivFin
import Mathlib.FieldTheory.Separable

/-!
Independent specification of K07.14.polynomial_root_action, paper.tex:4240–4248.
The extension is any realization of the splitting field, with its specified
base embedding. Its automorphisms compose as functions and act on the left.
The roots are actual elements of L, not formal roots or roots with multiplicity.
No finiteness, normality, characteristic, or closedness premise is added.
-/

universe u v

namespace Specs.D07.Ch14.PolynomialRootAction

open Polynomial

def RootPermutationType : Type (max u v + 1) :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), (L ≃ₐ[K] L) →* Equiv.Perm (f.rootSet L)

/-- Restrict each base-fixing automorphism to the actual set of roots.
Its inverse restricts the inverse automorphism, so this construction also
specifies the action when the polynomial does not split. -/
def rootPermutationValue : RootPermutationType.{u, v} :=
  fun K L _ _ _ f =>
    { toFun := fun σ =>
        { toFun := fun a => ⟨σ a, rootSet_mapsTo σ.toAlgHom a.property⟩
          invFun := fun a => ⟨σ.symm a, rootSet_mapsTo σ.symm.toAlgHom a.property⟩
          left_inv := fun a => Subtype.ext (σ.symm_apply_apply a)
          right_inv := fun a => Subtype.ext (σ.apply_symm_apply a) }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }

def RootPermutationApply : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (σ : L ≃ₐ[K] L) (a : f.rootSet L),
    (rootPermutationValue K L f σ a).val = σ a.val

/-- Separability counts distinct roots, and splitting supplies all of them. -/
def RootCount : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), 0 < f.natDegree → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f →
    Fintype.card (f.rootSet L) = f.natDegree

/-- Faithfulness is injectivity of the natural permutation representation. -/
def RootActionFaithful : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), 0 < f.natDegree → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f →
    Function.Injective (rootPermutationValue K L f)

/-- Any numbering gives the embedding in S_n, with its actual root action. -/
def EmbeddingAfterNumbering : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (n : ℕ), 0 < f.natDegree → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = n →
    ∀ b : Fin n ≃ f.rootSet L,
      ∃ ρ : (L ≃ₐ[K] L) →* Equiv.Perm (Fin n),
        Function.Injective ρ ∧
        ∀ (σ : L ≃ₐ[K] L) (i : Fin n), (b (ρ σ i)).val = σ (b i).val

/-- The numbering exists; it is not an additional hypothesis. -/
def NumberedEmbedding : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K) (n : ℕ), 0 < f.natDegree → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = n →
    ∃ b : Fin n ≃ f.rootSet L,
      ∃ ρ : (L ≃ₐ[K] L) →* Equiv.Perm (Fin n),
        Function.Injective ρ ∧
        ∀ (σ : L ≃ₐ[K] L) (i : Fin n), (b (ρ σ i)).val = σ (b i).val

/-- Every ordered pair of roots is connected by a splitting-field
automorphism when f is irreducible. -/
def RootActionTransitive : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), 0 < f.natDegree → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → Irreducible f →
    ∀ a b : f.rootSet L,
      ∃ σ : L ≃ₐ[K] L, rootPermutationValue K L f σ a = b

end Specs.D07.Ch14.PolynomialRootAction
