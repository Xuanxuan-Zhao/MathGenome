import MathGenome.Internal.Specs.D07.Ch17.Characters
import MathGenome.Internal.Specs.D07.Ch17.IrreducibleDefinition
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
K07.21.dual_tensor, paper.tex:6188–6224.
The constructions use the algebraic dual and the ordinary tensor product, with
the upstream endomorphism-valued representation and trace character. We state
the field-independent results: in particular they apply to every finite group
over ℂ as required by the chapter. Only character and duality assertions impose
finite dimension. No nonzero-space assumption is imposed on the constructions.
-/
namespace Specs.D07.Ch21.DualTensor

universe u v w x t z
noncomputable section
open scoped TensorProduct

def DualRepresentationType : Type (max u v w + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V],
    Representation K G V → Representation K G (Module.Dual K V)

abbrev dualRepresentationValue : DualRepresentationType.{u,v,w} :=
  fun _ _ _ _ _ _ _ ρ => ρ.dual

def TensorRepresentationType : Type (max u v w x + 1) :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    Representation K G V → Representation K G W → Representation K G (V ⊗[K] W)

abbrev tensorRepresentationValue : TensorRepresentationType.{u,v,w,x} :=
  fun _ _ _ _ _ _ _ _ _ _ ρ σ => ρ.tprod σ

def DualLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V),
    (∀ g (φ : Module.Dual K V) v, ρ.dual g φ v = φ (ρ g⁻¹ v)) ∧
    ρ.dual 1 = 1 ∧
    (∀ g h, ρ.dual (g * h) = ρ.dual g * ρ.dual h) ∧
    (∀ g, ρ.dual g * ρ.dual g⁻¹ = 1 ∧ ρ.dual g⁻¹ * ρ.dual g = 1)

def DualMatrix : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (ι : Type t)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (ρ : Representation K G V) (g : G),
    LinearMap.toMatrix b.dualBasis b.dualBasis (ρ.dual g) =
      (LinearMap.toMatrix b b (ρ g⁻¹)).transpose

def DualCharacter : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (g : G),
    Ch17.Characters.characterValue K G (Module.Dual K V) ρ.dual g =
      Ch17.Characters.characterValue K G V ρ g⁻¹

/-- The actual evaluation identification, including equivariance. -/
def BidualEquivalence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V),
    ∃ e : ρ.Equiv ρ.dual.dual, ∀ v (φ : Module.Dual K V), e v φ = φ v

/-- The annihilator used in the irreducibility argument is invariant, has the
complementary dimension, and is proper nonzero for proper nonzero U. -/
def AnnihilatorLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) (U : Subrepresentation ρ.dual),
    (∀ g v, v ∈ U.toSubmodule.dualCoannihilator →
      ρ g v ∈ U.toSubmodule.dualCoannihilator) ∧
    Module.finrank K U.toSubmodule +
      Module.finrank K U.toSubmodule.dualCoannihilator = Module.finrank K V ∧
    (U ≠ ⊥ → U ≠ ⊤ →
      U.toSubmodule.dualCoannihilator ≠ ⊥ ∧ U.toSubmodule.dualCoannihilator ≠ ⊤)

def DualIrreducible : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V),
    Representation.IsIrreducible ρ.dual ↔ Representation.IsIrreducible ρ

def DualZero : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] [Subsingleton V]
    (ρ : Representation K G V),
    Subsingleton (Module.Dual K V) ∧
      ¬ Representation.IsIrreducible ρ ∧ ¬ Representation.IsIrreducible ρ.dual

def TensorLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    (∀ g v w, (ρ.tprod σ) g (v ⊗ₜ[K] w) = ρ g v ⊗ₜ[K] σ g w) ∧
    (ρ.tprod σ) 1 = 1 ∧
    (∀ g h, (ρ.tprod σ) (g * h) = (ρ.tprod σ) g * (ρ.tprod σ) h) ∧
    (∀ g, (ρ.tprod σ) g * (ρ.tprod σ) g⁻¹ = 1 ∧
      (ρ.tprod σ) g⁻¹ * (ρ.tprod σ) g = 1)

/-- Full product-basis entries, hence in particular the diagonal formula. -/
def TensorMatrix : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x) (ι : Type t) (κ : Type z)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι K V) (c : Module.Basis κ K W)
    (ρ : Representation K G V) (σ : Representation K G W) (g : G) (i j : ι × κ),
    LinearMap.toMatrix (b.tensorProduct c) (b.tensorProduct c) ((ρ.tprod σ) g) i j =
      LinearMap.toMatrix b b (ρ g) i.1 j.1 * LinearMap.toMatrix c c (σ g) i.2 j.2

def TensorCharacter : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W) (g : G),
    Ch17.Characters.characterValue K G (V ⊗[K] W) (ρ.tprod σ) g =
      Ch17.Characters.characterValue K G V ρ g * Ch17.Characters.characterValue K G W σ g

def TensorZero : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    (Subsingleton V ∨ Subsingleton W) →
      Subsingleton (V ⊗[K] W) ∧ ∀ g,
        Ch17.Characters.characterValue K G (V ⊗[K] W) (ρ.tprod σ) g = 0 ∧
        Ch17.Characters.characterValue K G V ρ g * Ch17.Characters.characterValue K G W σ g = 0

end
end Specs.D07.Ch21.DualTensor
