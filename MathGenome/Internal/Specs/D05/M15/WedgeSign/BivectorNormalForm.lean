import MathGenome.Internal.Specs.D05.M15.ExteriorPairing
import MathGenome.Internal.Specs.D05.M11.SymplecticBlocks
import MathGenome.Internal.Specs.D05.M07.Biddual
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The bivector stage of K05.15.wedge_sign, paper.tex:2937–2955.
All exterior powers are the canonical square-relation quotients. No restriction
on characteristic is imposed, and the empty normal form is allowed. -/
noncomputable section
namespace Specs.D05.M15.WedgeSign.BivectorNormalForm
open Module
open scoped BigOperators
universe u v w

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The elementary degree-two wedge, in the accepted exterior power. -/
abbrev wedge (u v : V) : ⋀[K]^2 V := exteriorPower.ιMulti K 2 ![u, v]

/-- Wedge as a bilinear map. These are the inherited quotient operations. -/
def wedgeBilin : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
  LinearMap.mk₂ K wedge
    (by intros; apply Subtype.ext; simp [wedge, ExteriorAlgebra.ιMulti_succ_apply, add_mul])
    (by intros; apply Subtype.ext; simp [wedge, ExteriorAlgebra.ιMulti_succ_apply])
    (by intros; apply Subtype.ext; simp [wedge, ExteriorAlgebra.ιMulti_succ_apply, mul_add])
    (by intros; apply Subtype.ext; simp [wedge, ExteriorAlgebra.ιMulti_succ_apply])

/-- B_z(phi,psi) is precisely evaluation of phi wedge psi on z. -/
def form (z : ⋀[K]^2 V) : LinearMap.BilinForm K (Dual K V) :=
  (wedgeBilin (K := K) (V := Dual K V)).compr₂
    ((ExteriorPairing.pairing_value K V 2).flip z)

/-- The matrix in the dual of the original basis; indices follow form slots. -/
def matrix {I : Type w} [Finite I] (b : Basis I K V) (z : ⋀[K]^2 V) : Matrix I I K :=
  fun i j => form z (b.coord i) (b.coord j)

/-- Construction bridge to the accepted determinant exterior pairing. -/
def form_evaluation : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (z : ⋀[K]^2 V) (phi psi : Dual K V),
    form z phi psi = ExteriorPairing.pairing_value K V 2 (wedge phi psi) z

def elementary : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (u v : V) (phi psi : Dual K V),
    form (wedge u v) phi psi = phi u * psi v - phi v * psi u

def alternating : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (z : ⋀[K]^2 V), (form z).IsAlt

/-- For arbitrary coefficients in an increasing basis expansion, recover exactly
Z_ij = z_ij above the diagonal, -z_ji below, and zero on the diagonal. -/
def matrix_entries : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Basis (Fin n) K V) (a : Fin n → Fin n → K),
    let z := ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), a i j • wedge (b i) (b j)
    ∀ i j, matrix b z i j = if i < j then a i j else if j < i then -a j i else 0

def matrix_rank : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {I : Type w} [Fintype I] (b : Basis I K V) (z : ⋀[K]^2 V),
    (matrix b z).rank = Module.finrank K (LinearMap.range (form z))

/-- Simultaneous factor independence, the actual bivector equality, and rank.
The family indexed by Fin r × Fin 2 retains all 2r factor occurrences. -/
def normal_form : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (z : ⋀[K]^2 V),
    ∃ (r : ℕ) (u v : Fin r → V),
      LinearIndependent K (fun ij : Fin r × Fin 2 => if ij.2 = 0 then u ij.1 else v ij.1) ∧
      z = ∑ i, wedge (u i) (v i) ∧
      Module.finrank K (LinearMap.range (form z)) = 2 * r ∧
      (∀ {n : ℕ} (b : Basis (Fin n) K V), (matrix b z).rank = 2 * r)

/-- In particular the nonzero decomposable case has rank TWO. -/
def nonzero_decomposable_rank : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (u v : V), wedge (K := K) u v ≠ 0 →
      Module.finrank K (LinearMap.range (form (wedge (K := K) u v))) = 2

end Specs.D05.M15.WedgeSign.BivectorNormalForm
