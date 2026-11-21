import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.Nilradical
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.JordanDerivations
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.StdBasis

/-!
LA-I09-Step, notes/005/lie-algebras-and-representations.tex:4362–4471.
This file gives the independent interface for the full enlargement step
and its auxiliary statements.
The nilradical is the upstream sum of internally nilpotent ideals.
-/

noncomputable section
universe u v w uS uT uB
namespace Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep

open Module

variable {k : Type u} [Field k] [CharZero k]
variable {A : Type v} [LieRing A] [LieAlgebra k A] [FiniteDimensional k A]

/-- In a solvable algebra every derivation has image in the actual nilradical. -/
def derivation_image_type : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CharZero k]
    [LieRing A] [LieAlgebra k A] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable A] (D : LieDerivation k A A) (x : A),
    D x ∈ Nilradical.nilradical_value k A

/-- A normalized functional on A/nilrad(A), pulled back to A, is a character. -/
def normalized_character_type : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CharZero k]
    [LieRing A] [LieAlgebra k A] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable A] (d : A),
    d ∉ Nilradical.nilradical_value k A →
    ∃ χ : A →ₗ[k] k, χ d = 1 ∧
      (∀ x ∈ Nilradical.nilradical_value k A, χ x = 0) ∧
      (∀ x y : A, χ ⁅x, y⁆ = 0) ∧
      (∀ (D : LieDerivation k A A) (x : A), χ (D x) = 0)

/-- Nilpotent-adjoint vectors in a solvable algebra generate a nilpotent
subalgebra. This will be applied to nilrad(A) and the new vector y in A'. -/
def nilpotent_span_type : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CharZero k]
    [LieRing A] [LieAlgebra k A] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable A] (P : Submodule k A) (y : A)
    (M : LieSubalgebra k A),
    (∀ x ∈ P, IsNilpotent (LieAlgebra.ad k A x)) →
    IsNilpotent (LieAlgebra.ad k A y) →
    M.toSubmodule ≤ P ⊔ Submodule.span k {y} → LieRing.IsNilpotent M

/-- A nilpotent ideal and one additional nilpotent-adjoint direction.
Here the span is equality, so this also proves the actual sum is nilpotent. -/
def nilpotent_ideal_plus_line_type : Prop :=
  ∀ (k : Type u) (A : Type v) [Field k] [CharZero k]
    [LieRing A] [LieAlgebra k A] [FiniteDimensional k A]
    [LieAlgebra.IsSolvable A] (I : LieIdeal k A) (y : A)
    (M : LieSubalgebra k A),
    LieRing.IsNilpotent I → IsNilpotent (LieAlgebra.ad k A y) →
    M.toSubmodule = I.toSubmodule ⊔ Submodule.span k {y} → LieRing.IsNilpotent M

/-- The numerical part of the decreasing measure, with the extra direction
required to be outside the old nilradical subspace. -/
def quotient_dimension_drop_type : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) (W : Type w)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (P : Submodule k V) (Q R : Submodule k W) (y : W),
    Module.finrank k W = Module.finrank k V →
    Module.finrank k Q = Module.finrank k P →
    y ∉ Q → Q ⊔ Submodule.span k {y} ≤ R →
    Module.finrank k (W ⧸ R) < Module.finrank k (V ⧸ P)

/-- Linear graph of x ↦ -χ(x)α, the underlying subspace of a'. -/
def tiltedGraphMap {k V H : Type*} [Field k]
    [AddCommGroup V] [Module k V] [AddCommGroup H] [Module k H]
    (χ : V →ₗ[k] k) (α : H) : V →ₗ[k] V × H :=
  (LinearMap.id : V →ₗ[k] V).prod (-(χ.smulRight α))

def graph_complement_type : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) (H : Type w)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup H] [Module k H] (χ : V →ₗ[k] k) (α : H) (d : V),
    χ d = 1 →
    (tiltedGraphMap χ α).range =
      (LinearMap.ker χ).map (LinearMap.inl k V H) ⊔ Submodule.span k {(d, -α)} ∧
    IsCompl (tiltedGraphMap χ α).range (LinearMap.inr k V H).range ∧
    Module.finrank k (tiltedGraphMap χ α).range = Module.finrank k V

/-- The tilted graph is an ideal when the character kills brackets and all
acting derivations and the chosen external vector is central. -/
def graph_ideal_type : Prop :=
  ∀ (k : Type u) [Field k] (A : Type v) (H : Type w)
    [LieRing A] [LieAlgebra k A] [LieRing H] [LieAlgebra k H]
    (θ : H →ₗ⁅k⁆ LieDerivation k A A) (χ : A →ₗ[k] k) (α : H),
    (∀ h : H, ⁅h, α⁆ = 0) →
    (∀ x y : A, χ ⁅x, y⁆ = 0) →
    (∀ (h : H) (x : A), χ (θ h x) = 0) →
    ∃ I : LieIdeal k (A ⋊⁅θ⁆ H), ∀ z : A ⋊⁅θ⁆ H,
      z ∈ I ↔ z.right = -(χ z.left • α)

section ComplexStep

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoined central abelian algebra, with its standard coordinate basis. -/
abbrev Torus (m : ℕ) := Fin m → ℂ

/-- Integer weights relative to a specified basis of the acting abelian algebra.
The eigenbasis of the acted-on space may be chosen; it includes the zero-space case. -/
def HasIntegerWeights {ι : Type*} {T V : Type*}
    [AddCommGroup T] [Module ℂ T] [AddCommGroup V] [Module ℂ V]
    (b : Basis ι ℂ T) (ρ : T →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∃ n : ℕ, ∃ c : Basis (Fin n) ℂ V, ∃ w : Fin n → ι → ℤ,
    ∀ i j, ρ (b j) (c i) = (w i j : ℂ) • c i

variable {S T : Type*} [LieRing S] [LieAlgebra ℂ S]
  [LieRing T] [LieAlgebra ℂ T]
variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]

def centerAction (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B) :
    T →ₗ[ℂ] Module.End ℂ B :=
  ((LieDerivation.toLinearMapLieHom ℂ B).comp θ).toLinearMap.comp
    (LinearMap.inr ℂ S T)

def enlargedCenterAction {U : Type*} [LieRing U] [LieAlgebra ℂ U]
    (θ : ((S × T) × U) →ₗ⁅ℂ⁆ LieDerivation ℂ B B) :
    (T × U) →ₗ[ℂ] Module.End ℂ B :=
  ((LieDerivation.toLinearMapLieHom ℂ B).comp θ).toLinearMap.comp
    ((LinearMap.inr ℂ S T).prodMap (LinearMap.id : U →ₗ[ℂ] U))

/-- The subgroup generated by the actual eigenvalues, not a supplied lattice. -/
def eigenvalueGroup {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : Module.End ℂ V) : AddSubgroup ℂ :=
  AddSubgroup.closure {β : ℂ | D.HasEigenvalue β}

def eigenvalue_lattice_type : Prop :=
  ∀ (B : Type v) [AddCommGroup B] [Module ℂ B] [FiniteDimensional ℂ B]
    (D : Module.End ℂ B),
    ∃ m : ℕ, Nonempty (Basis (Fin m) ℤ (eigenvalueGroup D))

/-- The integer-coordinate construction on all generalized eigenspaces.
Commutation with the full centralizer is needed for adjoining the torus to k. -/
structure IntegralTorusData (D : LieDerivation ℂ B B) where
  rank : ℕ
  basis : Basis (Fin rank) ℤ (eigenvalueGroup D.toLinearMap)
  action : Torus rank →ₗ⁅ℂ⁆ LieDerivation ℂ B B
  on_generalized_eigenspace :
    ∀ (β : ℂ) (hβ : β ∈ eigenvalueGroup D.toLinearMap) (x : B),
      x ∈ Module.End.maxGenEigenspace D.toLinearMap β →
      ∀ j, action (Pi.single j 1) x = (basis.repr ⟨β, hβ⟩ j : ℂ) • x
  centralizer : ∀ E : LieDerivation ℂ B B,
    Commute D.toLinearMap E.toLinearMap → ∀ z, ⁅E, action z⁆ = 0
  kills_kernel : ∀ x : B, D x = 0 → ∀ z, action z x = 0
  jordan : ∃ N : Module.End ℂ B,
    _root_.LieAlgebrasAndRepresentations.IsJordanDecomposition D.toLinearMap
      (action (fun j => (basis j : ℂ))).toLinearMap N

def torusElement {D : LieDerivation ℂ B B} (t : IntegralTorusData D) : Torus t.rank :=
  fun j => (t.basis j : ℂ)

def tiltedVector {m : ℕ}
    (Θ : ((S × T) × Torus m) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    (d : B) (α : Torus m) : B ⋊⁅Θ⁆ ((S × T) × Torus m) :=
  ⟨d, (0, -α)⟩

/-- Full witness for the source's step. All spectral, ideal, embedding,
splitting, nilpotence, integral-weight, and strict-dimension conclusions are
outputs. No certificate for any of them is included among the hypotheses. -/
structure StepData (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    {r : ℕ} (bT : Basis (Fin r) ℂ T) where
  d : B
  fixed : ∀ x : S × T, θ x d = 0
  outside_nilradical : d ∉ Nilradical.nilradical_value ℂ B
  character : B →ₗ[ℂ] ℂ
  character_d : character d = 1
  character_nilradical : ∀ x ∈ Nilradical.nilradical_value ℂ B, character x = 0
  character_bracket : ∀ x y : B, character ⁅x, y⁆ = 0
  torus : IntegralTorusData (LieDerivation.ad ℂ B d)
  extendedAction : ((S × T) × Torus torus.rank) →ₗ⁅ℂ⁆ LieDerivation ℂ B B
  extends_old : ∀ x : S × T, extendedAction (x, 0) = θ x
  extends_torus : ∀ z, extendedAction (0, z) = torus.action z
  replacement : LieIdeal ℂ (B ⋊⁅extendedAction⁆ ((S × T) × Torus torus.rank))
  replacement_space : replacement.toSubmodule =
    (LinearMap.ker character).map (LieAlgebra.SemiDirectSum.inl extendedAction).toLinearMap ⊔
      Submodule.span ℂ {tiltedVector extendedAction d (torusElement torus)}
  replacement_solvable : LieAlgebra.IsSolvable replacement
  complement : IsCompl replacement.toSubmodule
    (LieAlgebra.SemiDirectSum.inr extendedAction).range.toSubmodule
  newAction : ((S × T) × Torus torus.rank) →ₗ⁅ℂ⁆ LieDerivation ℂ replacement replacement
  splitting :
    (replacement ⋊⁅newAction⁆ ((S × T) × Torus torus.rank)) ≃ₗ⁅ℂ⁆
      (B ⋊⁅extendedAction⁆ ((S × T) × Torus torus.rank))
  splitting_apply : ∀ (x : replacement) (h : (S × T) × Torus torus.rank),
    splitting ⟨x, h⟩ = (x : B ⋊⁅extendedAction⁆ ((S × T) × Torus torus.rank)) +
      LieAlgebra.SemiDirectSum.inr extendedAction h
  oldEmbedding : (B ⋊⁅θ⁆ (S × T)) →ₗ⁅ℂ⁆
    (B ⋊⁅extendedAction⁆ ((S × T) × Torus torus.rank))
  oldEmbedding_apply : ∀ x, oldEmbedding x = ⟨x.left, (x.right, 0)⟩
  oldEmbedding_injective : Function.Injective oldEmbedding
  nilpotentSum : LieIdeal ℂ replacement
  nilpotentSum_space : nilpotentSum.toSubmodule.map replacement.incl.toLinearMap =
    (Nilradical.nilradical_value ℂ B).toSubmodule.map
      (LieAlgebra.SemiDirectSum.inl extendedAction).toLinearMap ⊔
      Submodule.span ℂ {tiltedVector extendedAction d (torusElement torus)}
  nilpotentSum_nilpotent : LieRing.IsNilpotent nilpotentSum
  nilpotentSum_direct : Disjoint
    ((Nilradical.nilradical_value ℂ B).toSubmodule.map
      (LieAlgebra.SemiDirectSum.inl extendedAction).toLinearMap)
    (Submodule.span ℂ {tiltedVector extendedAction d (torusElement torus)})
  integer_weights : HasIntegerWeights (bT.prod (Pi.basisFun ℂ (Fin torus.rank)))
    (enlargedCenterAction newAction)
  dimension_drop :
    Module.finrank ℂ (replacement ⧸ Nilradical.nilradical_value ℂ replacement) <
      Module.finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B)

/-- The unchanged original obligation, in external direct-product coordinates
for the given k=s⊕t. Semisimplicity is the upstream radical-zero definition. -/
def enlargement_step_type : Prop :=
  ∀ (S : Type uS) (T : Type uT) (B : Type uB)
    [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
    [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
    [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B] [LieAlgebra.IsSolvable B]
    (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    (r : ℕ) (bT : Basis (Fin r) ℂ T),
    SolvableRadical.IsSemisimple_value ℂ S →
    HasIntegerWeights bT (centerAction θ) →
    0 < Module.finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B) →
    Nonempty (StepData θ bT)

/-- The fixed vector required at every positive stage, under exactly the
semisimple-factor and diagonal-center hypotheses of the step. -/
def fixed_vector_type : Prop :=
  ∀ (S : Type uS) (T : Type uT) (B : Type uB)
    [LieRing S] [LieAlgebra ℂ S] [FiniteDimensional ℂ S]
    [LieRing T] [LieAlgebra ℂ T] [FiniteDimensional ℂ T] [IsLieAbelian T]
    [LieRing B] [LieAlgebra ℂ B] [FiniteDimensional ℂ B] [LieAlgebra.IsSolvable B]
    (θ : (S × T) →ₗ⁅ℂ⁆ LieDerivation ℂ B B)
    (r : ℕ) (bT : Basis (Fin r) ℂ T),
    SolvableRadical.IsSemisimple_value ℂ S →
    HasIntegerWeights bT (centerAction θ) →
    0 < Module.finrank ℂ (B ⧸ Nilradical.nilradical_value ℂ B) →
    ∃ d : B, (∀ x : S × T, θ x d = 0) ∧
      d ∉ Nilradical.nilradical_value ℂ B

end ComplexStep

end Specs.LieAlgebrasAndRepresentations.DiagonalEnlargementStep
