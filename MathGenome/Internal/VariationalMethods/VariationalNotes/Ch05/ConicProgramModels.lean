import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolarsBipolar
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ConicProgramModels

noncomputable section
universe u v
namespace VariationalNotes.Ch05.ConicProgramModels

def innerPositiveDual {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (K : Set X) : Set X :=
  Specs.innerPositiveDual K

def primalFeasible {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) : Set X :=
  Specs.primalFeasible K A b

def dualFeasible {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (c : X) : Set Y :=
  Specs.dualFeasible K A c

def primalValue {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X) : EReal :=
  Specs.primalValue K A b c

def dualValue {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    {Y : Type v} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (A : X →ₗ[ℝ] Y) (b : Y) (c : X) : EReal :=
  Specs.dualValue K A b c

theorem mem_innerPositiveDual : Specs.mem_innerPositiveDual := by
  intro X _ _ K s
  rfl

theorem gap_identity : Specs.gap_identity := by
  intro X _ _ _ Y _ _ _ K A b c x y hx
  rw [inner_sub_left, LinearMap.adjoint_inner_left, hx.2, real_inner_comm y b]

theorem gap_nonneg : Specs.gap_nonneg := by
  intro X _ _ _ Y _ _ _ K A b c x y hx hy
  exact hy x hx.1

theorem weak_duality : Specs.weak_duality := by
  intro X _ _ _ Y _ _ _ K A b c x y hx hy
  have h := gap_nonneg K A b c x y hx hy
  rw [← gap_identity K A b c x y hx] at h
  exact sub_nonneg.mp h

theorem zero_gap_iff : Specs.zero_gap_iff := by
  intro X _ _ _ Y _ _ _ K A b c x y hx _hy
  rw [gap_identity K A b c x y hx]

theorem equal_objectives_iff : Specs.equal_objectives_iff := by
  intro X _ _ _ Y _ _ _ K A b c x y hx hy
  rw [← sub_eq_zero, zero_gap_iff K A b c x y hx hy]

theorem value_weak_duality : Specs.value_weak_duality := by
  intro X _ _ _ Y _ _ _ K A b c
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  exact_mod_cast weak_duality K A b c x y hx hy

end VariationalNotes.Ch05.ConicProgramModels
