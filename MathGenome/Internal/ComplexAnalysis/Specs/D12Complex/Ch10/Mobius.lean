import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.SphereHolomorphic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Defs

/-! Möbius maps on the canonical sphere, paper.tex:2331–2337.
Matrices act on the homogeneous column [x:y], with finite z = [z:1]
and infinity = [1:0]. No holomorphy or group laws are assumed here. -/
noncomputable section
namespace D12Complex.Mobius

abbrev Coefficients := Matrix (Fin 2) (Fin 2) ℂ

def Regular (M : Coefficients) : Prop := M.det ≠ 0

/-- Homogeneous coordinate [x:y]; only nonzero pairs represent points. -/
def spherePair (x y : ℂ) : RiemannSphere :=
  if y = 0 then sphereInfty else sphereFinite (x / y)

/-- The fractional linear transformation, including its pole and infinity. -/
def mobiusMap (M : Coefficients) : RiemannSphere → RiemannSphere :=
  fun p => OnePoint.elim p (spherePair (M 0 0) (M 1 0))
    (fun z => spherePair (M 0 0 * z + M 0 1) (M 1 0 * z + M 1 1))

/-- The adjugate represents the inverse sphere map without dividing the matrix. -/
def inverseCoefficients (M : Coefficients) : Coefficients :=
  !![M 1 1, -M 0 1; -M 1 0, M 0 0]

/-- The full meaning of a sphere biholomorphism with its specified inverse. -/
def SphereBiholomorphicPair (F G : RiemannSphere → RiemannSphere) : Prop :=
  SphereHolomorphicOn Set.univ F ∧ SphereHolomorphicOn Set.univ G ∧
    Function.LeftInverse G F ∧ Function.RightInverse G F

end D12Complex.Mobius

namespace Specs.D12Complex.Ch10.Mobius
open _root_.D12Complex _root_.D12Complex.Mobius

def Regular_type := Coefficients → Prop
def Regular_value : Regular_type := fun M => M.det ≠ 0

def spherePair_type := ℂ → ℂ → RiemannSphere
def spherePair_value : spherePair_type :=
  fun x y => if y = 0 then sphereInfty else sphereFinite (x / y)

def mobiusMap_type := Coefficients → RiemannSphere → RiemannSphere
def mobiusMap_value : mobiusMap_type := fun M p =>
  OnePoint.elim p (spherePair (M 0 0) (M 1 0))
    (fun z => spherePair (M 0 0 * z + M 0 1) (M 1 0 * z + M 1 1))

def inverseCoefficients_type := Coefficients → Coefficients
def inverseCoefficients_value : inverseCoefficients_type :=
  fun M => !![M 1 1, -M 0 1; -M 1 0, M 0 0]

def SphereBiholomorphicPair_type :=
  (RiemannSphere → RiemannSphere) → (RiemannSphere → RiemannSphere) → Prop
def SphereBiholomorphicPair_value : SphereBiholomorphicPair_type := fun F G =>
  SphereHolomorphicOn Set.univ F ∧ SphereHolomorphicOn Set.univ G ∧
    Function.LeftInverse G F ∧ Function.RightInverse G F

def mobiusMap_finite_type : Prop :=
  ∀ (M : Coefficients) (z : ℂ), M 1 0 * z + M 1 1 ≠ 0 →
    mobiusMap M (sphereFinite z) =
      sphereFinite ((M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1))

def mobiusMap_pole_type : Prop :=
  ∀ M : Coefficients, Regular M → M 1 0 ≠ 0 →
    mobiusMap M (sphereFinite (-M 1 1 / M 1 0)) = sphereInfty

def mobiusMap_infty_type : Prop :=
  ∀ M : Coefficients,
    (M 1 0 ≠ 0 → mobiusMap M sphereInfty = sphereFinite (M 0 0 / M 1 0)) ∧
    (M 1 0 = 0 → mobiusMap M sphereInfty = sphereInfty)

def mobiusMap_one_type : Prop := mobiusMap 1 = id

def regular_mul_type : Prop :=
  ∀ M N : Coefficients, Regular M → Regular N → Regular (M * N)

def regular_inverseCoefficients_type : Prop :=
  ∀ M : Coefficients, Regular M → Regular (inverseCoefficients M)

def mobiusMap_mul_type : Prop :=
  ∀ M N : Coefficients, Regular M → Regular N →
    mobiusMap (M * N) = mobiusMap M ∘ mobiusMap N

def mobiusMap_inverse_type : Prop :=
  ∀ M : Coefficients, Regular M →
    Function.LeftInverse (mobiusMap (inverseCoefficients M)) (mobiusMap M) ∧
    Function.RightInverse (mobiusMap (inverseCoefficients M)) (mobiusMap M)

def mobiusMap_eq_iff_type : Prop :=
  ∀ M N : Coefficients, Regular M → Regular N →
    (mobiusMap M = mobiusMap N ↔ ∃ k : ℂ, k ≠ 0 ∧ M = k • N)

def mobiusMap_holomorphic_type : Prop :=
  ∀ M : Coefficients, Regular M → SphereHolomorphicOn Set.univ (mobiusMap M)

def mobiusMap_biholomorphic_type : Prop :=
  ∀ M : Coefficients, Regular M →
    SphereBiholomorphicPair (mobiusMap M) (mobiusMap (inverseCoefficients M))

/-- The sphere permutations represented by invertible matrices form a group
under composition, with exactly the stated matrix representatives. -/
def mobiusMap_group_type : Prop :=
  ∃ G : Subgroup (Equiv.Perm RiemannSphere), ∀ e : Equiv.Perm RiemannSphere,
    e ∈ G ↔ ∃ M : Coefficients, Regular M ∧ ∀ p, e p = mobiusMap M p

def mobiusMap_bijective_type : Prop :=
  ∀ M : Coefficients, Regular M → Function.Bijective (mobiusMap M)

end Specs.D12Complex.Ch10.Mobius
