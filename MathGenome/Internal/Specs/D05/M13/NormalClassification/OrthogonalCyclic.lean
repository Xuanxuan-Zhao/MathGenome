import MathGenome.Internal.Specs.D05.M13.NormalClassification.CyclicLayers
import MathGenome.Internal.Specs.D05.M13.ComplexSpectral
import MathGenome.Internal.Specs.D05.M10.InvariantFactors
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! K05.13.normal_classification, paper.tex:2353–2377. The powers span actual
cyclic subspaces. Invariant factors are the shared determinantal-divisor list.
Squarefreeness means no repeated irreducible factor over the stated base field;
it does not assert that a real annihilator splits into linear factors.
No orthonormality of a power basis or unitary companion form is asserted. -/
noncomputable section
namespace Specs.D05.M13.NormalClassification.OrthogonalCyclic
open Polynomial
open CyclicLayers

variable {F V : Type*} [RCLike F] [NormedAddCommGroup V]
  [InnerProductSpace F V] [FiniteDimensional F V]

/-- The full finite orthogonal cyclic decomposition, ordered by decreasing
rather than increasing divisibility. Empty index types are permitted. -/
structure Decomposition (T : Module.End F V) (r : ℕ) (w : Fin r → V)
    (d : Fin r → F[X]) : Prop where
  monic : ∀ i, (d i).Monic
  nonconstant : ∀ i, 0 < (d i).natDegree
  annihilator : ∀ i, Specs.D05.M10.Cyclic.vectorAnnihilator_value F V T (w i) = d i
  orthogonal : Pairwise fun i j =>
    (Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w i)).IsOrtho
      (Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w j))
  spanning : (⨆ i, Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w i)) = ⊤
  descending : ∀ i j, i ≤ j → d j ∣ d i
  squarefree : ∀ i, Squarefree (d i)
  factorization : ∀ i, ∃ P : Finset F[X],
    (∀ q ∈ P, q.Monic ∧ Irreducible q) ∧ d i = ∏ q ∈ P, q
  invariant_factors : Specs.D05.M10.InvariantFactors.factors T = (List.ofFn d).reverse

/-- The real theorem uses irreducible quadratics as well as linear factors. -/
def real_decomposition : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (T : Module.End ℝ V), _root_.D05.normalOperator T →
    ∃ r w d, Decomposition T r w d

def complex_decomposition : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V), _root_.D05.normalOperator T →
    ∃ r w d, Decomposition T r w d

/-- Group all occurrences of the same irreducible label, and assemble the
proved algebraic layers into an orthogonal cyclic decomposition. -/
def assemble_layers : Prop :=
  ∀ {F V ι : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Fintype ι] (T : Module.End F V)
    (H : ι → Submodule F V) (p : ι → F[X]),
    (∀ i, Block T (H i) (p i)) → (Pairwise fun i j => (H i).IsOrtho (H j)) →
    (⨆ i, H i) = ⊤ → ∃ r w d, Decomposition T r w d

/-- Identification for any full orthogonal family of cyclic spaces; the
power bases need not be orthonormal. This is an algebraic module assertion. -/
def cyclic_factors : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (T : Module.End F V) {r : ℕ}
    (w : Fin r → V) (d : Fin r → F[X]),
    (∀ i, (d i).Monic) → (∀ i, 0 < (d i).natDegree) →
    (∀ i, Specs.D05.M10.Cyclic.vectorAnnihilator_value F V T (w i) = d i) →
    (Pairwise fun i j =>
      (Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w i)).IsOrtho
        (Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w j))) →
    (⨆ i, Specs.D05.M10.Cyclic.cyclicSpace_value F V T (w i)) = ⊤ →
    (∀ i j, i ≤ j → d j ∣ d i) →
    Specs.D05.M10.InvariantFactors.factors T = (List.ofFn d).reverse

/-- The primary space is the actual kernel of a positive power of p(T).
Normality makes all these kernels equal and their orthogonal projections
polynomials in T. This also covers a zero primary space and a zero ambient
space; no nonzero-space assumption is introduced. -/
def primary_projections : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (T : Module.End F V), _root_.D05.normalOperator T →
    ∀ p : F[X], p.Monic → Irreducible p → ∀ k : ℕ, 0 < k →
      LinearMap.ker (aeval T (p ^ k)) = LinearMap.ker (aeval T p) ∧
      ∃ e : F[X], aeval T e =
        (LinearMap.ker (aeval T (p ^ k))).starProjection.toLinearMap

/-- The decomposition of the zero space is literally empty. -/
def zero_decomposition : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] [Subsingleton V] (T : Module.End F V),
    Decomposition T 0 Fin.elim0 Fin.elim0

end Specs.D05.M13.NormalClassification.OrthogonalCyclic
