import Mathlib.Algebra.Field.Opposite
import Mathlib.RingTheory.SimpleModule.Basic

/-!
The scalar and operator conventions of RM03-C03.01 and the annihilator
identification used in RM03-C03.02. A right module over the opposite
endomorphism ring is written as a left module over the endomorphism ring.
-/

universe u v

namespace RM03.Specs.Density

-- The signatures quantify over the ring and module universes independently.
set_option linter.checkUnivs false

def RightScalarsType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M], Type v

abbrev RightScalarsValue : RightScalarsType :=
  fun R M _ _ _ ↦ (Module.End R M)ᵐᵒᵖ

def rightScalarsDivisionRingType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M], DivisionRing (RightScalarsValue R M)

noncomputable def rightScalarsDivisionRingValue : rightScalarsDivisionRingType := by
  classical
  intro R M _ _ _ _
  exact MulOpposite.instDivisionRing (α := Module.End R M)

def rightScalarsDivisionRing_toRingType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [IsSimpleModule R M],
    (rightScalarsDivisionRingValue R M).toRing = (inferInstance : Ring (RightScalarsValue R M))

def evaluationModuleType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    Module (Module.End R M) M

def evaluationModuleValue : evaluationModuleType :=
  fun _ _ _ _ _ ↦ Module.End.applyModule

def rightSMulType :=
  ∀ (R : Type u) {M : Type v} [Ring R] [AddCommGroup M] [Module R M],
    M → RightScalarsValue R M → M

def rightSMulValue : rightSMulType :=
  fun _ _ _ _ _ m d ↦ (MulOpposite.unop d) m

def rightSMul_opType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    (m : M) (f : Module.End R M), rightSMulValue R m (MulOpposite.op f) = f m

def rightSMul_mulType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    (m : M) (d e : RightScalarsValue R M),
    rightSMulValue R (rightSMulValue R m d) e = rightSMulValue R m (d * e)

def RightEndType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M], Type v

abbrev RightEndValue : RightEndType :=
  fun R M _ _ _ ↦ Module.End (Module.End R M) M

def actionType :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    R →+* RightEndValue R M

def actionValue : actionType := fun _ _ _ _ _ ↦
  { toFun := fun r ↦
      { toFun := fun m ↦ r • m
        map_add' := smul_add r
        map_smul' := fun f m ↦ (f.map_smul r m).symm }
    map_one' := LinearMap.ext (one_smul _)
    map_mul' := fun r s ↦ LinearMap.ext (mul_smul r s)
    map_zero' := LinearMap.ext (zero_smul _)
    map_add' := fun r s ↦ LinearMap.ext (add_smul r s) }

def action_applyType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M] (r : R) (m : M),
    actionValue R M r m = r • m

/-- Mathlib's module annihilator is two-sided and has membership
`r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0`. -/
def action_kerType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    RingHom.ker (actionValue R M) = Module.annihilator R M

end RM03.Specs.Density
