import MathGenome.Internal.Specs.D05.M02.Basis
import MathGenome.Internal.Specs.D05.M15.TensorExistence
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
Independent statements for K05.15.tensor_basis, paper.tex:2721–2730.
The tensor space is the same algebraic `TensorProduct` used upstream. The
product index type retains every pair of basis indices, without finiteness
or nonemptiness assumptions. All expansions and relations have finite support.
Only `finite_dimension` assumes finite-dimensional factors. No characteristic
restriction is imposed, and a zero factor is allowed throughout.
-/
namespace Specs.D05.M15.TensorBasis

open scoped TensorProduct

/-- The specified elementary tensors themselves form a basis. -/
def tensor_basis : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V) (f : Module.Basis J K W),
    ∃ B : Module.Basis (I × J) K (V ⊗[K] W),
      ∀ p, B p = e p.1 ⊗ₜ[K] f p.2

/-- The independent-and-spanning formulation of the same indexed family. -/
def independent_and_span : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V) (f : Module.Basis J K W),
    LinearIndependent K (fun p : I × J => e p.1 ⊗ₜ[K] f p.2) ∧
      Submodule.span K (Set.range (fun p : I × J => e p.1 ⊗ₜ[K] f p.2)) = ⊤

/-- Every tensor has exactly one finite-support expansion in the product basis. -/
def unique_expansion : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V) (f : Module.Basis J K W)
    (z : V ⊗[K] W),
    ∃! a : (I × J) →₀ K,
      (∑ p ∈ a.support, a p • (e p.1 ⊗ₜ[K] f p.2)) = z

/-- Products of coordinate functionals linearize and extract a chosen
coefficient from every finite expansion. This uses algebraic coordinates
also when the bases are infinite. -/
def coordinate_functionals : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : Module.Basis I K V) (f : Module.Basis J K W)
    (i : I) (j : J),
    ∃ L : (V ⊗[K] W) →ₗ[K] K,
      (∀ v w, L (v ⊗ₜ[K] w) = e.repr v i * f.repr w j) ∧
      (∀ a : (I × J) →₀ K,
        L (∑ p ∈ a.support, a p • (e p.1 ⊗ₜ[K] f p.2)) = a (i, j))

/-- The product is finite dimensional, with the product of the dimensions.
The conjunction prevents a bare `finrank` equality from hiding infinitude. -/
def finite_dimension : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W],
    FiniteDimensional K (V ⊗[K] W) ∧
      Module.finrank K (V ⊗[K] W) = Module.finrank K V * Module.finrank K W

/-- Zero left factor, with no dimension restriction on the other factor. -/
def zero_left : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Subsingleton V],
    ∀ z : V ⊗[K] W, z = 0

/-- Zero right factor, with no dimension restriction on the other factor. -/
def zero_right : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Subsingleton W],
    ∀ z : V ⊗[K] W, z = 0

end Specs.D05.M15.TensorBasis
