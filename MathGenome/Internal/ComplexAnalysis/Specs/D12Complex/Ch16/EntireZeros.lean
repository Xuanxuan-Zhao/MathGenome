import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.CanonicalFactors
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.HolomorphicProducts
import Mathlib.Topology.LocallyFinsupp

/-! Independent statements of the entire prescribed-zero theorem, D12.16.03.
A divisor is a natural-valued multiplicity function with locally finite support.
Zero multiplicity means absence; natural values exclude infinite multiplicities.
-/
noncomputable section
open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch16.EntireZeros
open _root_.D12Complex

def Occurrences_type := (ℂ → ℕ) → Type
def Occurrences_value : Occurrences_type := fun d =>
  Σ z : {z : ℂ // z ≠ 0 ∧ d z ≠ 0}, Fin (d z)
def Realizes_type := (ℂ → ℕ) → (ℂ → ℂ) → Prop
def Realizes_value : Realizes_type := fun d f =>
  HolomorphicOn univ f ∧ (∃ z, f z ≠ 0) ∧
    (∀ z, analyticOrderAt f z = (d z : ℕ∞)) ∧ ∀ z, f z = 0 ↔ d z ≠ 0
def canonicalProduct_type := (ℕ → ℂ) → ℕ → ℂ → ℂ
def canonicalProduct_value : canonicalProduct_type := fun a m z =>
  z ^ m * ∏' n, CanonicalFactors.factor_value n (z / a n)

/-- Any enumeration of all multiplicity slots escapes every bounded disk. -/
def enumerate_divisor_type : Prop :=
  ∀ d : ℂ → ℕ, LocallyFiniteSupport d →
    {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Infinite →
    ∃ e : ℕ ≃ Occurrences_value d,
      Tendsto (fun n => ‖(e n).1.1‖) atTop atTop ∧
      ∀ z : ℂ, z ≠ 0 →
        (∑' n, (if (e n).1.1 = z then 1 else 0 : ℕ∞)) = (d z : ℕ∞)

/-- The explicit source product, for any repeated nonzero sequence escaping
bounded disks. Its order formula counts repetitions, including none at zero. -/
def canonical_product_type : Prop :=
  ∀ (a : ℕ → ℂ) (m : ℕ), (∀ n, a n ≠ 0) →
    Tendsto (fun n => ‖a n‖) atTop atTop →
    TendstoLocallyUniformlyOn
      (fun N z => z ^ m * ∏ n ∈ Finset.range N, CanonicalFactors.factor_value n (z / a n))
      (canonicalProduct_value a m) atTop univ ∧
    HolomorphicOn univ (canonicalProduct_value a m) ∧
    (∃ z, canonicalProduct_value a m z ≠ 0) ∧
    (∀ z, analyticOrderAt (canonicalProduct_value a m) z =
      (if z = 0 then (m : ℕ∞) else 0) +
        ∑' n, (if a n = z then 1 else 0 : ℕ∞)) ∧
    ∀ z, canonicalProduct_value a m z = 0 ↔ (z = 0 ∧ m ≠ 0) ∨ ∃ n, a n = z

/-- A finite divisor is realized by the corresponding finite polynomial product. -/
def finite_divisor_type : Prop :=
  ∀ (d : ℂ → ℕ) (s : Finset ℂ), (∀ z, d z ≠ 0 → z ∈ s) →
    Realizes_value d (fun z => ∏ c ∈ s, (z - c) ^ d c)

/-- The empty divisor has precisely the source's normalized witness one. -/
def empty_divisor_type : Prop := Realizes_value (fun _ => 0) (fun _ => 1)

/-- No enumeration or convergence certificate is assumed in this existence result. -/
def entire_prescribed_zeros_type : Prop :=
  ∀ d : ℂ → ℕ, LocallyFiniteSupport d → ∃ f : ℂ → ℂ, Realizes_value d f

/-- The enumerated source product realizes the original divisor, including its
independently prescribed center multiplicity. -/
def infinite_divisor_product_type : Prop :=
  ∀ d : ℂ → ℕ, LocallyFiniteSupport d →
    {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Infinite →
    ∃ e : ℕ ≃ Occurrences_value d,
      Tendsto (fun n => ‖(e n).1.1‖) atTop atTop ∧
      Realizes_value d (canonicalProduct_value (fun n => (e n).1.1) (d 0))

end Specs.D12Complex.Ch16.EntireZeros
