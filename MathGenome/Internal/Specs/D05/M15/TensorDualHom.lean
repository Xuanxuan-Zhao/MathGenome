import MathGenome.Internal.Specs.D05.M03.BasisExtension
import MathGenome.Internal.Specs.D05.M07.DualBasis
import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import Mathlib.LinearAlgebra.Contraction

/-!
Independent statements for K05.15.tensor_dual_hom, paper.tex:2800–2809.
The canonical map is defined for arbitrary algebraic vector spaces. Only the
isomorphism onto all linear maps requires a finite-dimensional domain; the
codomain has no finiteness hypothesis. Finite bases may have an empty index type.
The definitions below are shared interfaces for subsequent finite-rank results.
-/

namespace Specs.D05.M15.TensorDualHom

open scoped TensorProduct

/-- The bilinear rank-one assignment, linearized on the algebraic tensor product.
There is deliberately no finite-dimensional instance in this definition. -/
abbrev phi (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :
    (Module.Dual K V ⊗[K] W) →ₗ[K] (V →ₗ[K] W) :=
  dualTensorHom K V W

/-- Type and prescribed value of the canonical map. -/
def phi_type :=
  (K V W : Type*) → [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] →
    (Module.Dual K V ⊗[K] W) →ₗ[K] (V →ₗ[K] W)

def phi_value : phi_type := fun K V W _ _ _ _ _ => phi K V W

/-- The paper's explicit inverse sum for a specified finite basis. -/
noncomputable def psi {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] (b : Module.Basis I K V) :
    (V →ₗ[K] W) →ₗ[K] (Module.Dual K V ⊗[K] W) :=
  ∑ i, (TensorProduct.mk K (Module.Dual K V) W (b.coord i)).comp
    (LinearMap.applyₗ (R := K) (b i))

def psi_type :=
  {K V W I : Type*} → [Field K] → [AddCommGroup V] → [Module K V] →
    [AddCommGroup W] → [Module K W] → [Fintype I] →
    Module.Basis I K V → (V →ₗ[K] W) →ₗ[K] (Module.Dual K V ⊗[K] W)

noncomputable def psi_value : psi_type := @psi

/-- The elementary tensor has the specified rank-one action in every dimension. -/
def phi_tmul : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : Module.Dual K V) (w : W) (v : V),
    phi K V W (f ⊗ₜ[K] w) v = f v • w

/-- The assignment is bilinear and induces precisely this canonical map. -/
def bilinear_assignment : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∃ b : Module.Dual K V →ₗ[K] W →ₗ[K] (V →ₗ[K] W),
      (∀ f w v, b f w v = f v • w) ∧ TensorProduct.lift b = phi K V W

/-- No choice of a basis can alter the map with this elementary action. -/
def phi_unique : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (L : (Module.Dual K V ⊗[K] W) →ₗ[K] (V →ₗ[K] W)),
    (∀ f w v, L (f ⊗ₜ[K] w) v = f v • w) → L = phi K V W

/-- The inverse construction is exactly the finite sum in the manuscript. -/
def psi_apply : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I]
    (b : Module.Basis I K V) (T : V →ₗ[K] W),
    psi b T = ∑ i, b.coord i ⊗ₜ[K] T (b i)

/-- The vector-coordinate expansion proves the first inverse identity. -/
def phi_psi : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I]
    (b : Module.Basis I K V) (T : V →ₗ[K] W), phi K V W (psi b T) = T

/-- The dual-coordinate expansion and tensor spanning prove the second identity. -/
def psi_phi : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I]
    (b : Module.Basis I K V) (t : Module.Dual K V ⊗[K] W),
    psi b (phi K V W t) = t

/-- Isomorphism onto all Hom, for finite-dimensional V and arbitrary W. -/
def finite_dimensional_equivalence : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V],
    ∃ E : (Module.Dual K V ⊗[K] W) ≃ₗ[K] (V →ₗ[K] W),
      E.toLinearMap = phi K V W

/-- Every equivalence whose forward map is Phi has the stated inverse formula. -/
def inverse_formula : Prop :=
  ∀ {K V W I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I]
    (b : Module.Basis I K V)
    (E : (Module.Dual K V ⊗[K] W) ≃ₗ[K] (V →ₗ[K] W)),
    E.toLinearMap = phi K V W → ∀ T : V →ₗ[K] W,
      E.symm T = ∑ i, b.coord i ⊗ₜ[K] T (b i)

/-- In particular, changing the finite basis leaves the inverse map unchanged. -/
def basis_independent : Prop :=
  ∀ {K V W I J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype I] [Fintype J]
    (b : Module.Basis I K V) (c : Module.Basis J K V),
    psi (W := W) b = psi (W := W) c

/-- In arbitrary dimension every tensor still gives a map of finite rank. -/
def finite_rank : Prop :=
  ∀ {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (t : Module.Dual K V ⊗[K] W),
    FiniteDimensional K (LinearMap.range (phi K V W t))

/-- Hence infinite-dimensional endomorphism spaces cannot all be represented:
the identity itself is absent. -/
def identity_not_in_range : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V],
    ¬ FiniteDimensional K V →
      (LinearMap.id : V →ₗ[K] V) ∉ LinearMap.range (phi K V V)

end Specs.D05.M15.TensorDualHom
