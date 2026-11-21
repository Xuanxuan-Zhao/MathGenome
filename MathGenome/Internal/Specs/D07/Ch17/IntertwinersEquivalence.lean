import MathGenome.Internal.Specs.D07.Ch17.Definition
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
Independent specification of K07.17.intertwiners_equivalence,
paper.tex:4661–4685. Representations use the upstream endomorphism formulation,
which is equivalent there to the source's automorphism formulation. No finiteness
of the group, algebraic closedness or characteristic restrictions are imposed.
Only statements about matrices choose finite bases; empty index types are allowed.
The conjugating matrix is quantified before the group element.
-/
namespace Specs.D07.Ch17.IntertwinersEquivalence

universe u v w x y t z

/-- The pointwise library predicate is exactly the displayed equality of linear maps. -/
def IntertwinerCharacterization : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ T ↔ ∀ g, T.comp (ρ g) = (σ g).comp T

/-- The zero linear map intertwines. -/
def IntertwinersZero : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    ρ.IsIntertwiningMap σ 0

/-- Intertwiners are closed under addition. -/
def IntertwinersAdd : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (S T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ S → ρ.IsIntertwiningMap σ T →
    ρ.IsIntertwiningMap σ (S + T)

/-- Intertwiners are closed under every scalar multiplication. -/
def IntertwinersSmul : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W) (a : K),
    ρ.IsIntertwiningMap σ T → ρ.IsIntertwiningMap σ (a • T)

/-- Identity linear maps intertwine. -/
def IntertwinerIdentity : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V]
    (ρ : Representation K G V), ρ.IsIntertwiningMap ρ LinearMap.id

/-- Composition of two intertwiners intertwines. -/
def IntertwinerComposition : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x) (U : Type y)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    [Module K V] [Module K W] [Module K U]
    (ρ : Representation K G V) (σ : Representation K G W) (τ : Representation K G U)
    (S : W →ₗ[K] U) (T : V →ₗ[K] W),
    σ.IsIntertwiningMap τ S → ρ.IsIntertwiningMap σ T →
    ρ.IsIntertwiningMap τ (S.comp T)

/-- The inverse of an invertible intertwiner intertwines in the reverse direction. -/
def IntertwinerInverse : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W) (e : V ≃ₗ[K] W),
    ρ.IsIntertwiningMap σ e.toLinearMap →
    σ.IsIntertwiningMap ρ e.symm.toLinearMap

/-- Bundled representation equivalence is precisely existence of a bijective intertwiner. -/
def BijectiveIntertwinerEquivalence : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    Nonempty (ρ.Equiv σ) ↔
      ∃ T : V →ₗ[K] W, ρ.IsIntertwiningMap σ T ∧ Function.Bijective T

/-- Reflexivity, symmetry and transitivity hold even across different carrier spaces. -/
def EquivalenceLaws : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x) (U : Type y)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    [Module K V] [Module K W] [Module K U]
    (ρ : Representation K G V) (σ : Representation K G W) (τ : Representation K G U),
    Nonempty (ρ.Equiv ρ) ∧
    (Nonempty (ρ.Equiv σ) → Nonempty (σ.Equiv ρ)) ∧
    (Nonempty (ρ.Equiv σ) → Nonempty (σ.Equiv τ) → Nonempty (ρ.Equiv τ))

/-- On a fixed carrier, invertible intertwiners give an equivalence relation. -/
def EquivalenceRelation : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V],
    Equivalence (fun ρ σ : Representation K G V => Nonempty (ρ.Equiv σ))

/-- Equality of linear maps is equivalent to equality of their coordinate matrices. -/
def MatrixEquality : Prop :=
  ∀ (K : Type u) (V : Type w) (W : Type x)
    [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (ι : Type t) (κ : Type z) [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι K V) (c : Module.Basis κ K W) (S T : V →ₗ[K] W),
    S = T ↔ LinearMap.toMatrix b c S = LinearMap.toMatrix b c T

/-- With arbitrary finite bases, intertwining is equivalent to PA_g = B_gP. -/
def MatrixIntertwining : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ι : Type t) (κ : Type z) [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (b : Module.Basis ι K V) (c : Module.Basis κ K W)
    (ρ : Representation K G V) (σ : Representation K G W) (T : V →ₗ[K] W),
    ρ.IsIntertwiningMap σ T ↔ ∀ g,
      LinearMap.toMatrix b c T * LinearMap.toMatrix b b (ρ g) =
        LinearMap.toMatrix c c (σ g) * LinearMap.toMatrix b c T

/-- For equal finite basis sizes, T is bijective exactly when its matrix is a unit. -/
def MatrixInvertibility : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ι : Type t) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (c : Module.Basis ι K W)
    (T : V →ₗ[K] W),
    Function.Bijective T ↔ IsUnit (LinearMap.toMatrix b c T)

/-- For a fixed linear isomorphism, intertwining is exactly simultaneous conjugation by its matrix. -/
def MatrixConjugacy : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ι : Type t) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (c : Module.Basis ι K W)
    (ρ : Representation K G V) (σ : Representation K G W) (e : V ≃ₗ[K] W),
    ρ.IsIntertwiningMap σ e.toLinearMap ↔ ∀ g,
      LinearMap.toMatrix c c (σ g) =
        LinearMap.toMatrix b c e.toLinearMap * LinearMap.toMatrix b b (ρ g) *
          LinearMap.toMatrix c b e.symm.toLinearMap

/-- One common invertible matrix for all group elements is equivalent to representation equivalence, in both directions. -/
def SimultaneousConjugacy : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    (ι : Type t) [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (c : Module.Basis ι K W)
    (ρ : Representation K G V) (σ : Representation K G W),
    Nonempty (ρ.Equiv σ) ↔ ∃ P : Matrix.GeneralLinearGroup ι K, ∀ g,
      LinearMap.toMatrix c c (σ g) =
        (P : Matrix ι ι K) * LinearMap.toMatrix b b (ρ g) *
          (↑(P⁻¹) : Matrix ι ι K)

/-- Representations on finite dimensional spaces of different dimensions cannot be equivalent. -/
def DifferentDimensions : Prop :=
  ∀ (K : Type u) (G : Type v) (V : Type w) (W : Type x)
    [Field K] [Group G] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (ρ : Representation K G V) (σ : Representation K G W),
    Module.finrank K V ≠ Module.finrank K W → ¬ Nonempty (ρ.Equiv σ)

end Specs.D07.Ch17.IntertwinersEquivalence
