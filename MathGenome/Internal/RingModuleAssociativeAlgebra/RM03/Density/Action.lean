import Mathlib.Algebra.Field.Opposite
import Mathlib.RingTheory.SimpleModule.Basic

universe u v

namespace RM03.Density

variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]

/-- Scalars acting on the right by evaluation. Endomorphisms multiply by composition. -/
abbrev RightScalars := (Module.End R M)ᵐᵒᵖ

/-- Schur's lemma equips the opposite endomorphism ring with division. -/
@[instance_reducible]
noncomputable def rightScalarsDivisionRing [IsSimpleModule R M] :
    DivisionRing (RightScalars R M) := by
  classical
  infer_instance

theorem rightScalarsDivisionRing_toRing [IsSimpleModule R M] :
    (rightScalarsDivisionRing R M).toRing = (inferInstance : Ring (RightScalars R M)) :=
  rfl

/-- The left module over the endomorphism ring that represents the right scalar action. -/
abbrev evaluationModule : Module (Module.End R M) M :=
  Module.End.applyModule

variable {M} in
/-- Right scalar multiplication is evaluation by the underlying endomorphism. -/
def rightSMul (m : M) (d : RightScalars R M) : M :=
  MulOpposite.unop d • m

@[simp] theorem rightSMul_op (m : M) (f : Module.End R M) :
    rightSMul R m (MulOpposite.op f) = f m :=
  rfl

theorem rightSMul_mul (m : M) (d e : RightScalars R M) :
    rightSMul R (rightSMul R m d) e = rightSMul R m (d * e) :=
  rfl

/-- The ring of right-linear endomorphisms, written over the endomorphism ring on the left. -/
abbrev RightEnd := Module.End (Module.End R M) M

/-- The original scalar action as a unital map into the ring of right-linear endomorphisms. -/
def action : R →+* RightEnd R M :=
  Module.toModuleEnd (Module.End R M) (S := R) M

@[simp] theorem action_apply (r : R) (m : M) : action R M r m = r • m :=
  rfl

theorem action_ker : RingHom.ker (action R M) = Module.annihilator R M := by
  apply Ideal.ext
  intro r
  simp only [RingHom.mem_ker, Module.mem_annihilator, LinearMap.ext_iff,
    action_apply, LinearMap.zero_apply]

end RM03.Density
