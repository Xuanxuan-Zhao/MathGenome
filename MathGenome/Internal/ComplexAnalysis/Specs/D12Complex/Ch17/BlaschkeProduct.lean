import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.HolomorphicProducts

/-! Independent statements for the sufficiency assertion of D12.17.06,
paper.tex:3059–3089. `none` is an identity factor, so a finite list is represented
by its entries followed by `none`, and the empty list by the constant `none`.
The natural index retains the displayed order. Repeated `some a` entries count
multiplicity. Summability itself suffices; no extra separation hypothesis is
needed. The theorem also proves finiteness of the set of occurrences at each
interior point. All norms and all convergence below are ordinary complex ones. -/
noncomputable section
open Set Filter Metric
open scoped Topology ComplexConjugate
namespace Specs.D12Complex.Ch17.BlaschkeProduct
open _root_.D12Complex

def factor_type := ℂ → ℂ → ℂ
def factor_value : factor_type := fun a z => (‖a‖ : ℂ) / a * ((a - z) / (1 - conj a * z))

def factors_type := (ℕ → Option ℂ) → ℕ → ℂ → ℂ
def factors_value : factors_type := fun a n z => (a n).elim 1 (fun w => factor_value w z)

def product_type := (ℕ → Option ℂ) → ℕ → ℂ → ℂ
def product_value : product_type := fun a m z => z ^ m * ∏' n, factors_value a n z

def partialProduct_type := (ℕ → Option ℂ) → ℕ → ℕ → ℂ → ℂ
def partialProduct_value : partialProduct_type := fun a m N z =>
  z ^ m * ∏ n ∈ Finset.range N, factors_value a n z

def Admissible_type := (ℕ → Option ℂ) → Prop
def Admissible_value : Admissible_type := fun a =>
  (∀ n w, a n = some w → w ≠ 0 ∧ ‖w‖ < 1) ∧
  Summable (fun n => (a n).elim 0 (fun w => 1 - ‖w‖))

def factor_estimate_type : Prop :=
  ∀ (a z : ℂ) (r : ℝ), a ≠ 0 → ‖a‖ < 1 → ‖z‖ ≤ r → r < 1 →
    ‖1 - factor_value a z‖ ≤ (1 - ‖a‖) * (1 + r) / (1 - r)

def factor_bound_type : Prop :=
  ∀ a z : ℂ, a ≠ 0 → ‖a‖ < 1 → ‖z‖ < 1 → ‖factor_value a z‖ ≤ 1

def blaschke_product_type : Prop :=
  ∀ a : ℕ → Option ℂ, Admissible_value a → ∀ m : ℕ,
    TendstoLocallyUniformlyOn (partialProduct_value a m) (product_value a m)
      atTop (ball (0 : ℂ) 1) ∧
    HolomorphicOn (ball (0 : ℂ) 1) (product_value a m) ∧
    (∀ z ∈ ball (0 : ℂ) 1, ‖product_value a m z‖ ≤ 1) ∧
    (∀ z ∈ ball (0 : ℂ) 1,
      (product_value a m z = 0 ↔ (z = 0 ∧ 0 < m) ∨ ∃ n, a n = some z)) ∧
    (∀ z ∈ ball (0 : ℂ) 1, {n : ℕ | a n = some z}.Finite ∧
      analyticOrderAt (product_value a m) z =
        (if z = 0 then (m : ℕ∞) else 0) +
        ∑' n, (if a n = some z then (1 : ℕ∞) else 0)) ∧
    analyticOrderAt (product_value a m) 0 = (m : ℕ∞)

/-- The quantitative estimate supplies the normal product criterion on every compact subset. -/
def normal_product_condition_type : Prop :=
  ∀ a : ℕ → Option ℂ, Admissible_value a →
    Specs.D12Complex.Ch16.HolomorphicProducts.NormalProductCondition_value
      (ball (0 : ℂ) 1) (factors_value a)

/-- Every padded finite sequence of nonzero disk points satisfies the hypotheses. -/
def finite_admissible_type : Prop :=
  ∀ (a : ℕ → Option ℂ) (N : ℕ), (∀ n, N ≤ n → a n = none) →
    (∀ n w, a n = some w → w ≠ 0 ∧ ‖w‖ < 1) → Admissible_value a

/-- A finite sequence uses its original prefix and then identity factors. -/
def finite_product_type : Prop :=
  ∀ (a : ℕ → Option ℂ) (N m : ℕ), (∀ n, N ≤ n → a n = none) →
    ∀ z : ℂ, product_value a m z = partialProduct_value a m N z

/-- In particular the empty product is exactly z^m, including m=0. -/
def empty_product_type : Prop :=
  ∀ m : ℕ, product_value (fun _ => none) m = fun z => z ^ m

end Specs.D12Complex.Ch17.BlaschkeProduct
