import MathGenome.Internal.Specs.D05.M15.HilbertSeries

/-!
Independent statements for K05.15.hilbert_series, paper.tex:3210.

We reuse the canonical tensor powers, dimension series, graded tensor product,
and weighted subspaces from the prerequisite Specs. In particular the weighted
subspaces lie in the exterior and symmetric quotient algebras themselves.
For block weights the underlying vector space is the external direct sum of
the given finite-dimensional spaces, with its concatenated component basis.
All series have integer coefficients and every assertion includes degree zero,
zero-dimensional factors, and the empty family. No characteristic assumption
is imposed. The inverse identities express the paper's negative powers inside
the formal power-series ring, without analytic evaluation.
-/

noncomputable section
namespace Specs.D05.M15.HilbertSeries.Weighted
universe u v w
open scoped TensorProduct DirectSum

/-- Finiteness as well as the dimension of every tensor power. -/
def tensor_dimension : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (p : ℕ),
    FiniteDimensional K (TensorPower K p V) ∧
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

/-- The genuine direct-sum degree k is finite dimensional and its dimension
is the finite Cauchy sum. No finiteness of the entire graded spaces is assumed. -/
def tensor_grade_dimension : Prop :=
  ∀ {K : Type u} [Field K] (U : ℕ → Type v) (W : ℕ → Type w)
    [∀ p, AddCommGroup (U p)] [∀ p, Module K (U p)]
    [∀ p, AddCommGroup (W p)] [∀ p, Module K (W p)]
    [∀ p, FiniteDimensional K (U p)] [∀ p, FiniteDimensional K (W p)] (k : ℕ),
    FiniteDimensional K (tensorGrade K U W k) ∧
      Module.finrank K (tensorGrade K U W k) =
        ∑ ab ∈ Finset.antidiagonal k,
          Module.finrank K (U ab.1) * Module.finrank K (W ab.2)

def tensor_product_series : Prop :=
  ∀ {K : Type u} [Field K] (U : ℕ → Type v) (W : ℕ → Type w)
    [∀ p, AddCommGroup (U p)] [∀ p, Module K (U p)]
    [∀ p, AddCommGroup (W p)] [∀ p, Module K (W p)]
    [∀ p, FiniteDimensional K (U p)] [∀ p, FiniteDimensional K (W p)],
    dimensionSeries K (tensorGrade K U W) = dimensionSeries K U * dimensionSeries K W

/-- A positive weight bounds every exponent, so only finitely many monomials
can have a specified weight. -/
def weighted_exponents_finite : Prop :=
  ∀ {I : Type u} [Fintype I] (d : I → ℕ), (∀ i, 0 < d i) → ∀ k : ℕ,
    Finite {a : I → ℕ // ∑ i, d i * a i = k}

/-- The polynomial-coordinate description is the ordinary product of the
original symmetric-algebra generators. -/
def weighted_symmetric_part_monomials : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V) (d : I → ℕ) (k : ℕ),
    weightedSymmetricPart b d k =
      Submodule.span K (Set.range (fun a : {a : I → ℕ // ∑ i, d i * a i = k} =>
        ∏ i, (_root_.SymmetricAlgebra.ι K V (b i)) ^ a.val i))

def positive_weight_finiteness : Prop :=
  ∀ {K : Type u} {V : Type v} {I : Type w} [Field K] [AddCommGroup V]
    [Module K V] [Fintype I] (b : Module.Basis I K V)
    (d : I → ℕ), (∀ i, 0 < d i) → ∀ k,
    FiniteDimensional K (weightedExteriorPart b d k) ∧
    FiniteDimensional K (weightedSymmetricPart b d k)

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

/-- This identity supplies each factor (1-X^d)^(-1). -/
def weighted_geometric_inverse : Prop :=
  ∀ d : ℕ, 0 < d → weightedGeometric d * (1 - PowerSeries.X ^ d) = 1

/-- Consequently the symmetric series is the inverse of the stated finite
product, i.e. the product of the negative powers in the manuscript. -/
def weighted_symmetric_inverse : Prop :=
  ∀ {K : Type u} [Field K] (r : ℕ) (W : Fin r → Type v)
    [∀ j, AddCommGroup (W j)] [∀ j, Module K (W j)]
    [∀ j, FiniteDimensional K (W j)] (d : Fin r → ℕ),
    (∀ j, 0 < d j) →
    dimensionSeries K (fun k => ↥(weightedSymmetricPart
      (DFinsupp.basis (fun j => Module.finBasis K (W j))) (fun i => d i.1) k)) *
      (∏ j, (1 - PowerSeries.X ^ d j) ^ Module.finrank K (W j)) = 1

end Specs.D05.M15.HilbertSeries.Weighted
