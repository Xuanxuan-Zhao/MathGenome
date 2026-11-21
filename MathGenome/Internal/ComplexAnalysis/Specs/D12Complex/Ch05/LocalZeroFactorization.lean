import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Analysis.Analytic.Order

/-! Independent interface for paper.tex:1289–1305 (D12.05.03).
All equalities of germs mean actual equality on some neighborhood. The
extended order takes value ∞ for the zero germ, never an arbitrary natural.
Only expected values and proposition types are declared here; the actual
definitions and proofs belong to the implementation module.
-/
noncomputable section
open Filter
open scoped Topology

namespace Specs.D12Complex.Ch05.LocalZeroFactorization
open _root_.D12Complex

def HolomorphicNear_type := (ℂ → ℂ) → ℂ → Prop
def HolomorphicNear_value : HolomorphicNear_type :=
  fun f a => ∃ U : Set ℂ, a ∈ U ∧ HolomorphicOn U f

def ZeroGerm_type := (ℂ → ℂ) → ℂ → Prop
def ZeroGerm_value : ZeroGerm_type := fun f a => ∀ᶠ z in 𝓝 a, f z = 0

def HasFiniteOrder_type := (ℂ → ℂ) → ℂ → ℕ → Prop
def HasFiniteOrder_value : HasFiniteOrder_type := fun f a m =>
  ∃ g : ℂ → ℂ, HolomorphicNear_value g a ∧ g a ≠ 0 ∧
    ∀ᶠ z in 𝓝 a, f z = (z - a)^m * g z

def order_type := (ℂ → ℂ) → ℂ → ℕ∞
def order_value : order_type := fun f a => analyticOrderAt f a

def holomorphicNear_iff_analyticAt_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear_value f a ↔ AnalyticAt ℂ f a

def order_eq_top_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), order_value f a = ⊤ ↔ ZeroGerm_value f a

def order_eq_nat_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear_value f a → ∀ m : ℕ,
    order_value f a = (m : ℕ∞) ↔ HasFiniteOrder_value f a m

/-- The alternatives are exclusive; only the integer, not the total function
representing the unit away from the point, is uniquely quantified. -/
def local_zero_factorization_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear_value f a →
    (ZeroGerm_value f a ∧ ¬ ∃ m : ℕ, HasFiniteOrder_value f a m) ∨
    (¬ ZeroGerm_value f a ∧ ∃! m : ℕ, HasFiniteOrder_value f a m)

/-- For a fixed power the remaining factor is unique as a germ. -/
def factor_unique_type : Prop :=
  ∀ (f g h : ℂ → ℂ) (a : ℂ) (m : ℕ),
    HolomorphicNear_value g a → HolomorphicNear_value h a →
    (∀ᶠ z in 𝓝 a, f z = (z - a)^m * g z) →
    (∀ᶠ z in 𝓝 a, f z = (z - a)^m * h z) → g =ᶠ[𝓝 a] h

def finiteOrder_zero_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), HasFiniteOrder_value f a m →
    (f a = 0 ↔ 0 < m)

/-- This also states local nonvanishing when m=0. -/
def finiteOrder_isolated_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ) (m : ℕ), HasFiniteOrder_value f a m →
    ∀ᶠ z in 𝓝[≠] a, f z ≠ 0

def order_eq_zero_iff_type : Prop :=
  ∀ (f : ℂ → ℂ) (a : ℂ), HolomorphicNear_value f a →
    (order_value f a = 0 ↔ f a ≠ 0)

def finiteOrder_mul_type : Prop :=
  ∀ (f g : ℂ → ℂ) (a : ℂ) (m n : ℕ),
    HasFiniteOrder_value f a m → HasFiniteOrder_value g a n →
    HasFiniteOrder_value (f * g) a (m + n) ∧ order_value (f * g) a = ((m + n : ℕ) : ℕ∞)

/-- Extended addition also covers zero germs without assigning them finite orders. -/
def order_mul_type : Prop :=
  ∀ (f g : ℂ → ℂ) (a : ℂ), HolomorphicNear_value f a → HolomorphicNear_value g a →
    order_value (f * g) a = order_value f a + order_value g a

end Specs.D12Complex.Ch05.LocalZeroFactorization
