import MathGenome.Internal.Specs.D05.M12.Orthonormal
import Mathlib.Order.Interval.Finset.Fin

/-!
K05.12.gram_schmidt, paper.tex:1967–1979.
A finite list is indexed by `Fin n`, including `n = 0`. These are the actual
normalized recursive formulas, using the shared first-slot-linear convention.
The totalized operation at a zero residual is not asserted to be normalization;
the independent-input theorem proves that this case never occurs. For dependent
input, the separate output family retains only indices with nonzero residuals.
No dimension or completeness condition is imposed on the ambient space.
-/

noncomputable section

namespace D05

/-- The paper's normalized recursion, with strictly earlier indices only. -/
def gramSchmidtVectors {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] {n : ℕ} (v : Fin n → V) (j : Fin n) : V :=
  normalizeVector (F := F)
    (v j - ∑ i : Finset.Iio j,
      firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i) • gramSchmidtVectors (F := F) v i)
termination_by j.val
decreasing_by exact (Finset.mem_Iio.mp i.2 : (i : Fin n) < j)

/-- The residual before the normalization at position `j`. -/
def gramSchmidtResidual {F V : Type*} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] {n : ℕ} (v : Fin n → V) (j : Fin n) : V :=
  v j - ∑ i ∈ Finset.Iio j,
    firstInner (F := F) (v j) (gramSchmidtVectors (F := F) v i) • gramSchmidtVectors (F := F) v i

end D05

namespace Specs.D05.M12.GramSchmidt

universe u v

def family_type : Type (max (u + 1) (v + 1)) :=
  {F : Type u} → {V : Type v} → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → {n : ℕ} → (Fin n → V) → Fin n → V

def vectors_value : family_type.{u, v} := @_root_.D05.gramSchmidtVectors

def residual_value : family_type.{u, v} := @_root_.D05.gramSchmidtResidual

/-- Display both equations together, including the real normalization factor. -/
def recurrence : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V) (j : Fin n),
    _root_.D05.gramSchmidtResidual (F := F) v j =
      v j - ∑ i ∈ Finset.Iio j,
        _root_.D05.firstInner (F := F) (v j) (_root_.D05.gramSchmidtVectors (F := F) v i) •
          _root_.D05.gramSchmidtVectors (F := F) v i ∧
    _root_.D05.gramSchmidtVectors (F := F) v j =
      (((‖_root_.D05.gramSchmidtResidual (F := F) v j‖⁻¹ : ℝ) : F) •
        _root_.D05.gramSchmidtResidual (F := F) v j)

def residual_ne_zero : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v → ∀ j,
      _root_.D05.gramSchmidtResidual (F := F) v j ≠ 0

def denominators_pos : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v → ∀ j,
      0 < ‖_root_.D05.gramSchmidtResidual (F := F) v j‖

def orthonormal : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v →
      _root_.D05.orthonormalFamily (F := F) (_root_.D05.gramSchmidtVectors (F := F) v)

/-- Initial segments of every length, including zero and the full list. -/
def initial_spans : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v → ∀ k : ℕ, k ≤ n →
      Submodule.span F (_root_.D05.gramSchmidtVectors (F := F) v '' {i | i.val < k}) =
        Submodule.span F (v '' {i | i.val < k})

/-- The manuscript's conclusion with its three simultaneous assertions. -/
def gram_schmidt : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V), LinearIndependent F v →
      (∀ j, 0 < ‖_root_.D05.gramSchmidtResidual (F := F) v j‖) ∧
      _root_.D05.orthonormalFamily (F := F) (_root_.D05.gramSchmidtVectors (F := F) v) ∧
      (∀ k : ℕ, k ≤ n →
        Submodule.span F (_root_.D05.gramSchmidtVectors (F := F) v '' {i | i.val < k}) =
          Submodule.span F (v '' {i | i.val < k}))

/-- For dependent input skip zero residuals; every retained denominator is positive,
and the retained family is an orthonormal basis of the input span (as a family
in the ambient space, via independence and span equality). -/
def omit_zero_residuals : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    {n : ℕ} (v : Fin n → V),
    (∀ j : {j // _root_.D05.gramSchmidtResidual (F := F) v j ≠ 0},
      0 < ‖_root_.D05.gramSchmidtResidual (F := F) v j‖) ∧
    _root_.D05.orthonormalFamily (F := F)
      (fun j : {j // _root_.D05.gramSchmidtResidual (F := F) v j ≠ 0} =>
        _root_.D05.gramSchmidtVectors (F := F) v j) ∧
    Submodule.span F (Set.range
      (fun j : {j // _root_.D05.gramSchmidtResidual (F := F) v j ≠ 0} =>
        _root_.D05.gramSchmidtVectors (F := F) v j)) =
      Submodule.span F (Set.range v)

end Specs.D05.M12.GramSchmidt
