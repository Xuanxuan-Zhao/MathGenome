import MathGenome.Internal.Specs.D05.M11.Alternating
import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.Foundations.PermutationSign
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Basic.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! Independent statements for paper.tex:1817–1831, K05.11.pfaffian.
The covectors below are the actual ordered dual coordinate basis. Products and
powers are in the accepted square-relation exterior algebra. The signed formula
is used to construct the scalar; `wedge_normalization` and
`normalization_unique` prove its equivalence with the paper's definition.
No invertibility or nondegeneracy of the skew matrix is required. -/

noncomputable section
namespace Specs.D05.M11.Pfaffian

open scoped BigOperators

abbrev Covectors (n : ℕ) := Module.Dual ℝ (Fin n → ℝ)

def coordinateBasis (n : ℕ) : Module.Basis (Fin n) ℝ (Covectors n) :=
  (Pi.basisFun ℝ (Fin n)).dualBasis

/-- The positions (2j,2j+1), with indices starting at zero. -/
def pairIndex (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

abbrev omega_type := {m : ℕ} → Matrix (Fin (2*m)) (Fin (2*m)) ℝ →
  ExteriorAlgebra ℝ (Covectors (2*m))

def omega_value : omega_type := fun {m} A =>
  ∑ i, ∑ j ∈ Finset.Ioi i,
    A i j • (ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) i) *
      ExteriorAlgebra.ι ℝ (coordinateBasis (2*m) j))

abbrev volume_type := (m : ℕ) → ExteriorAlgebra ℝ (Covectors (2*m))

def volume_value : volume_type := fun m =>
  ExteriorAlgebra.ιMulti ℝ (2*m) (coordinateBasis (2*m))

abbrev pfaffian_type := {m : ℕ} → Matrix (Fin (2*m)) (Fin (2*m)) ℝ → ℝ

def pfaffian_value : pfaffian_type := fun {m} A =>
  (2^m * (Nat.factorial m : ℝ))⁻¹ *
    ∑ σ : Equiv.Perm (Fin (2*m)), (D05.Foundations.permutationSign σ : ℝ) *
      ∏ j : Fin m, A (σ (pairIndex m (j, 0))) (σ (pairIndex m (j, 1)))

def wedge_normalization : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    (Nat.factorial m : ℝ)⁻¹ • omega_value A ^ m = pfaffian_value A • volume_value m

def normalization_unique : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    ∃! p : ℝ, (Nat.factorial m : ℝ)⁻¹ • omega_value A ^ m = p • volume_value m

def empty_pfaffian : Prop :=
  ∀ A : Matrix (Fin (2*0)) (Fin (2*0)) ℝ, pfaffian_value A = 1

def empty_normalization : Prop :=
  ∀ A : Matrix (Fin (2*0)) (Fin (2*0)) ℝ,
    omega_value A ^ 0 = 1 ∧ volume_value 0 = 1

def permutation_formula : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin (2*m)) (Fin (2*m)) ℝ),
    (∀ i j, A i j = -A j i) →
    pfaffian_value A = (1 / (2^m * (Nat.factorial m : ℝ))) *
      ∑ σ : Equiv.Perm (Fin (2*m)), (D05.Foundations.permutationSign σ : ℝ) *
        ∏ j : Fin m, A (σ (pairIndex m (j, 0))) (σ (pairIndex m (j, 1)))

end Specs.D05.M11.Pfaffian
