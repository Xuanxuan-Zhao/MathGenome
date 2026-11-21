import MathGenome.Internal.Specs.D07.Ch01.GroupDefinition
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Topology.MetricSpace.Isometry

/-!
Independent specification of `K07.01.matrix_transformation_examples`
(paper.tex:358–363). Matrices have arbitrary finite index types, including
the empty type. Fields have no characteristic restriction. Permutations act
by composition in the source's order. The obstruction for endomorphisms
concerns their existing composition monoid, not an unrelated multiplication.
-/

namespace Specs.D07.Ch01.MatrixTransformationExamples

universe u v w

def MatrixAssociativity : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F]
    (A B C : Matrix ι ι F), (A * B) * C = A * (B * C)

/-- GL contains exactly the matrices with a two-sided matrix inverse. -/
def GLMembership : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F]
    (A : Matrix ι ι F),
    (∃ g : Matrix.GeneralLinearGroup ι F, (g : Matrix ι ι F) = A) ↔
      ∃ B : Matrix ι ι F, A * B = 1 ∧ B * A = 1

/-- All group laws, inherited matrix operations, and inverse closure. -/
def GLGroupOperations : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F],
    GroupDefinition.groupAxiomsValue (Matrix.GeneralLinearGroup ι F) (· * ·) 1 Inv.inv ∧
    ((1 : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = 1 ∧
    (∀ A B : Matrix.GeneralLinearGroup ι F,
      ((A * B : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
        (A : Matrix ι ι F) * (B : Matrix ι ι F)) ∧
    (∀ A : Matrix.GeneralLinearGroup ι F,
      ((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) = (A : Matrix ι ι F)⁻¹) ∧
    (∀ A : Matrix.GeneralLinearGroup ι F,
      IsUnit (((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F))) ∧
    (∀ A B : Matrix.GeneralLinearGroup ι F,
      (((A * B)⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
        (B : Matrix ι ι F)⁻¹ * (A : Matrix ι ι F)⁻¹)

def DeterminantLaws : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F],
    Matrix.det (1 : Matrix ι ι F) = 1 ∧
    (∀ A B : Matrix ι ι F, (A * B).det = A.det * B.det) ∧
    (∀ A : Matrix.GeneralLinearGroup ι F,
      (((A⁻¹ : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)).det =
        ((A : Matrix ι ι F).det)⁻¹)

/-- The determinant-one conditions on matrices supply all closure properties. -/
def DeterminantOneClosure : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F],
    Matrix.det (1 : Matrix ι ι F) = 1 ∧
    (∀ A B : Matrix ι ι F, A.det = 1 → B.det = 1 → (A * B).det = 1) ∧
    (∀ A : Matrix ι ι F, A.det = 1 → A⁻¹.det = 1) ∧
    (∀ A : Matrix ι ι F, A.det = 1 → IsUnit A)

/-- SL is a subgroup of GL, with the same underlying determinant-one matrices.
The multiplicative equivalence explicitly preserves the underlying matrices. -/
def SpecialLinearSubgroup : Prop :=
  ∀ (ι : Type u) (F : Type v) [Fintype ι] [DecidableEq ι] [Field F],
    ∃ H : Subgroup (Matrix.GeneralLinearGroup ι F),
      (∀ A : Matrix.GeneralLinearGroup ι F,
        A ∈ H ↔ (A : Matrix ι ι F).det = 1) ∧
      ∃ e : Matrix.SpecialLinearGroup ι F ≃* H,
        ∀ A : Matrix.SpecialLinearGroup ι F,
          (((e A : H) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
            (A : Matrix ι ι F)

/-- Uniformly in every field, including characteristic two, GL is nonabelian
in every dimension at least two. -/
def GLNoncommutative : Prop :=
  ∀ (F : Type v) [Field F] (n : ℕ), 2 ≤ n →
    ∃ A B : Matrix.GeneralLinearGroup (Fin n) F, A * B ≠ B * A

/-- Bijections are precisely the underlying functions of permutations. -/
def PermutationMembership : Prop :=
  ∀ (X : Type u) (f : X → X),
    Function.Bijective f ↔ ∃ e : Equiv.Perm X, (e : X → X) = f

def PermutationGroupOperations : Prop :=
  ∀ (X : Type u),
    GroupDefinition.groupAxiomsValue (Equiv.Perm X) (· * ·) 1 Inv.inv ∧
    (∀ x : X, (1 : Equiv.Perm X) x = x) ∧
    (∀ f g : Equiv.Perm X, ∀ x : X, (f * g) x = f (g x)) ∧
    (∀ f : Equiv.Perm X, f⁻¹ = f.symm)

/-- On an empty carrier there is exactly one endomap, and exactly one
bijection; that bijection is its own identity and inverse. -/
def EmptyPermutation : Prop :=
  ∀ (X : Type u) [IsEmpty X],
    (∃! f : X → X, Function.Bijective f) ∧
    (∀ e : Equiv.Perm X, e = 1 ∧ e⁻¹ = e)

/-- Any family of bijective isometries with the stated closures is a subgroup
of the bijections, acting by the very same maps on the metric space. -/
def IsometryFamilySubgroup : Prop :=
  ∀ (X : Type u) [PseudoEMetricSpace X] (s : Set (Equiv.Perm X)),
    (∀ f ∈ s, Isometry (f : X → X)) →
    (1 : Equiv.Perm X) ∈ s →
    (∀ f ∈ s, ∀ g ∈ s, f * g ∈ s) →
    (∀ f ∈ s, f⁻¹ ∈ s) →
    ∃ H : Subgroup (Equiv.Perm X), (H : Set (Equiv.Perm X)) = s ∧
      ∀ f : H, Isometry ((f : Equiv.Perm X) : X → X)

def EndomorphismMonoid : Prop :=
  ∀ (F : Type v) (V : Type w) [Field F] [AddCommGroup V] [Module F V],
    (∀ f g h : Module.End F V, (f * g) * h = f * (g * h)) ∧
    (∀ f : Module.End F V, 1 * f = f ∧ f * 1 = f) ∧
    (∀ f g : Module.End F V, ∀ x : V, (f * g) x = f (g x)) ∧
    (∀ x : V, (1 : Module.End F V) x = x)

/-- The zero endomorphism has no inverse on a nonzero vector space. -/
def ZeroEndomorphismNotInvertible : Prop :=
  ∀ (F : Type v) (V : Type w) [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V], ¬ ∃ f : Module.End F V, (0 : Module.End F V) * f = 1

/-- No group structure extends the existing composition monoid. -/
def NoEndomorphismGroup : Prop :=
  ∀ (F : Type v) (V : Type w) [Field F] [AddCommGroup V] [Module F V]
    [Nontrivial V],
    ¬ ∃ g : Group (Module.End F V),
      g.toMonoid = (inferInstance : Monoid (Module.End F V))

end Specs.D07.Ch01.MatrixTransformationExamples
