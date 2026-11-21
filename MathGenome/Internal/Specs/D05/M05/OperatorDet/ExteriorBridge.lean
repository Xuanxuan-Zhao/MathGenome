import MathGenome.Internal.Specs.D05.M15.DeterminantLine

/-!
The top-exterior comparison in K05.05.operator_det, paper.tex:899–903.
The exterior power is the canonical homogeneous submodule of the exterior
algebra quotient, and its map applies the operator to each wedge factor.
The coefficient is the previously defined column Leibniz determinant.
The vector-space assertions are over every field, including characteristic
two, in every finite dimension, including zero. A specified finite basis
already supplies the dimension hypothesis.
-/

noncomputable section
namespace Specs.D05.M05.OperatorDet.ExteriorBridge

universe u v
open Specs.D05.M15.DeterminantLine
open Specs.D05.M15.WedgeSign
open Specs.D05.M04.MatrixOfMap

/-- The ordered full wedge is a basis of the actual top exterior power. -/
def top_wedge_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V),
    ∃ B : Module.Basis (Fin 1) K (⋀[K]^n V), B 0 = volume b

/-- The induced map on the full wedge has the explicit signed-sum coefficient. -/
def leibniz_wedge_action : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    powerMap_value n T (volume b) =
      (∑ σ : Equiv.Perm (Fin n), (D05.Foundations.permutationSign σ : K) *
        ∏ j, matrixOfMap_value b b T (σ j) j) • volume b

/-- This is precisely the determinant of the basis matrix, with column
coordinates, rather than a separately chosen scalar. -/
def basis_wedge_action : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    powerMap_value n T (volume b) = detInBasis_value b T • volume b

/-- Equality on the whole top exterior power, for any specified finite basis. -/
def top_power_in_basis : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) (T : Module.End K V),
    powerMap_value n T = detInBasis_value b T • LinearMap.id

/-- The scalar is the already defined, basis-independent operator determinant. -/
def top_power_operator_det : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    powerMap_value (Module.finrank K V) T = operatorDet_value T • LinearMap.id

/-- In dimension zero the scalar is one and the empty volume is the unit;
the canonical identification of degree zero with K intertwines the induced
map with the identity of K. -/
def zero_dimensional_bridge : Prop :=
  ∀ {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin 0) K V) (T : Module.End K V),
    detInBasis_value b T = 1 ∧
    ((volume b : ⋀[K]^0 V) : _root_.ExteriorAlgebra K V) = 1 ∧
    ∀ a : K, exteriorPower.zeroEquiv K V
      (powerMap_value 0 T ((exteriorPower.zeroEquiv K V).symm a)) = a

end Specs.D05.M05.OperatorDet.ExteriorBridge
