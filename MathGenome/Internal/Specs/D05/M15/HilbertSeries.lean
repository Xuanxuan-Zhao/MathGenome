import MathGenome.Internal.Specs.D05.M15.ExteriorBasis
import MathGenome.Internal.Specs.D05.M15.SymmetricBasis
import MathGenome.Internal.Specs.D05.M15.TensorAlgebra
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! Independent statements for the complete K05.15.hilbert_series entry.
All series are formal series over ℤ. Dimensions refer to the upstream quotient
powers, with no characteristic restrictions. -/
noncomputable section
namespace Specs.D05.M15.HilbertSeries
universe u v w
open scoped TensorProduct DirectSum

/-- A formal dimension series; `mk` specifies every coefficient, without an
analytic convergence assertion. -/
def dimensionSeries (K : Type u) [Field K] (M : ℕ → Type v)
    [∀ p, AddCommGroup (M p)] [∀ p, Module K (M p)] : PowerSeries ℤ :=
  PowerSeries.mk (fun p => (Module.finrank K (M p) : ℤ))

def exterior_series : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (fun p => ↥(Exterior.homogeneousPart_value K V p)) =
    (1 + PowerSeries.X) ^ Module.finrank K V

def symmetric_series : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (Symmetric.symmetricPower K V) =
    (PowerSeries.mk (fun _ => (1 : ℤ))) ^ Module.finrank K V

def symmetric_inverse : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (Symmetric.symmetricPower K V) *
    (1 - PowerSeries.X) ^ Module.finrank K V = 1

def symmetric_product : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (Symmetric.symmetricPower K V) =
    ∏ _ : Fin (Module.finrank K V), PowerSeries.mk (fun _ => (1 : ℤ))

def geometric_inverse : Prop :=
  (PowerSeries.mk (fun _ => (1 : ℤ))) * (1 - PowerSeries.X) = 1

def zero_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V], Module.finrank K V = 0 →
    dimensionSeries K (fun p => ↥(Exterior.homogeneousPart_value K V p)) = 1 ∧
    dimensionSeries K (Symmetric.symmetricPower K V) = 1

def tensor_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ),
  Module.finrank K (TensorPower K p V) = Module.finrank K V ^ p

def tensor_series : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (fun p => TensorPower K p V) =
    PowerSeries.mk (fun p => (Module.finrank K V : ℤ) ^ p)

def tensor_inverse : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
  dimensionSeries K (fun p => TensorPower K p V) *
    (1 - PowerSeries.C (Module.finrank K V : ℤ) * PowerSeries.X) = 1

/-- The degree k of the graded tensor product is the finite sum over a+b=k.
The subtype is finite, so this remains an algebraic direct sum. -/
abbrev tensorGrade (K : Type u) [Field K] (U : ℕ → Type v) (W : ℕ → Type w)
    [∀ p, AddCommGroup (U p)] [∀ p, Module K (U p)]
    [∀ p, AddCommGroup (W p)] [∀ p, Module K (W p)] (k : ℕ) :=
  ⨁ ab : {ab : ℕ × ℕ // ab ∈ Finset.antidiagonal k}, U ab.val.1 ⊗[K] W ab.val.2

def tensor_product_series : Prop :=
  ∀ {K : Type u} [Field K] (U : ℕ → Type v) (W : ℕ → Type w)
    [∀ p, AddCommGroup (U p)] [∀ p, Module K (U p)]
    [∀ p, AddCommGroup (W p)] [∀ p, Module K (W p)]
    [∀ p, FiniteDimensional K (U p)] [∀ p, FiniteDimensional K (W p)],
  dimensionSeries K (tensorGrade K U W) = dimensionSeries K U * dimensionSeries K W

/-- Any finite indexing set can be ordered to write its increasing wedges. -/
abbrev basisIndexOrder (I : Type*) [Fintype I] : LinearOrder I :=
  LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective

/-- Increasing wedges of total weight k, in the actual exterior algebra. -/
def weightedExteriorPart {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ) :
    Submodule K (_root_.ExteriorAlgebra K V) :=
  letI := basisIndexOrder I
  Submodule.span K (Set.range (fun s : {s : Finset I // ∑ i ∈ s, d i = k} =>
    b.ExteriorAlgebra s.val))

/-- Ordinary monomials of the specified total weight, in the actual symmetric
algebra. `symmetricAlgebra` transports the formal monomial basis by the canonical
polynomial isomorphism; it is not an assumed dimension certificate. -/
def weightedSymmetricPart {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ) :
    Submodule K (_root_.SymmetricAlgebra K V) :=
  Submodule.span K (Set.range (fun a : {a : I → ℕ // ∑ i, d i * a i = k} =>
    b.symmetricAlgebra (Finsupp.equivFunOnFinite.symm a.val)))

/-- Bridge from the transported polynomial basis to actual ordinary products
of generators in the original quotient algebra. -/
def weighted_symmetric_part_monomials : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ),
    weightedSymmetricPart b d k =
      Submodule.span K (Set.range (fun a : {a : I → ℕ // ∑ i, d i * a i = k} =>
        ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a.val i))

/-- The series 1+t^d+t^(2d)+⋯ when d>0, specified coefficientwise. -/
def weightedGeometric (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun k => if d ∣ k then 1 else 0)

def positive_weight_finiteness : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V)
    (d : I → ℕ), (∀ i, 0 < d i) → ∀ k,
    FiniteDimensional K (weightedExteriorPart b d k) ∧
    FiniteDimensional K (weightedSymmetricPart b d k)

/-- Block weights on the direct sum of the given spaces. The basis of the sum
is made from the bases of its components, with index (j,i); hence every
component of dimension n_j supplies n_j generators of weight d_j. -/
def weighted_exterior_series : Prop :=
  ∀ {K : Type u} [Field K] (r : ℕ) (W : Fin r → Type v)
    [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    [∀ j, FiniteDimensional K (W j)] (d : Fin r → ℕ),
    (∀ j, 0 < d j) →
    dimensionSeries K (fun k => ↥(weightedExteriorPart
      (DFinsupp.basis (fun j => Module.finBasis K (W j))) (fun i => d i.1) k)) =
      ∏ j, (1 + PowerSeries.X ^ d j) ^ Module.finrank K (W j)

def weighted_symmetric_series : Prop :=
  ∀ {K : Type u} [Field K] (r : ℕ) (W : Fin r → Type v)
    [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    [∀ j, FiniteDimensional K (W j)] (d : Fin r → ℕ),
    (∀ j, 0 < d j) →
    dimensionSeries K (fun k => ↥(weightedSymmetricPart
      (DFinsupp.basis (fun j => Module.finBasis K (W j))) (fun i => d i.1) k)) =
      ∏ j, weightedGeometric (d j) ^ Module.finrank K (W j)

/-- This supplies the meaning of each negative power in the source product
∏ (1-t^d_j)^(-n_j) entirely inside formal integer power series. -/
def weighted_geometric_inverse : Prop :=
  ∀ d : ℕ, 0 < d → weightedGeometric d * (1 - PowerSeries.X ^ d) = 1

def weighted_symmetric_inverse : Prop :=
  ∀ {K : Type u} [Field K] (r : ℕ) (W : Fin r → Type v)
    [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    [∀ j, FiniteDimensional K (W j)] (d : Fin r → ℕ),
    (∀ j, 0 < d j) →
    dimensionSeries K (fun k => ↥(weightedSymmetricPart
      (DFinsupp.basis (fun j => Module.finBasis K (W j))) (fun i => d i.1) k)) *
      (∏ j, (1 - PowerSeries.X ^ d j) ^ Module.finrank K (W j)) = 1

end Specs.D05.M15.HilbertSeries
