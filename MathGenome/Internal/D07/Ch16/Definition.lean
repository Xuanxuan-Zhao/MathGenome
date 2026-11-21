import MathGenome.Internal.Specs.D07.Ch16.Definition

/-!
# Unital left modules

K07.16.definition, paper.tex:2927–2943. The scalar ring may be
noncommutative or the zero ring, and the module may be zero. There is no
multiplication on the vectors. The two zero-action identities needed by
Mathlib's `Module` are derived below from the four source axioms, rather
than included in `ModuleLaws`.
-/

universe u v

namespace D07.Ch16.Definition

open Specs.D07.Ch16.Definition

private theorem zero_smul_from_laws {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [SMul R M] (h : ModuleLaws R M) (m : M) :
    (0 : R) • m = 0 := by
  apply add_left_cancel (a := (0 : R) • m)
  calc
    (0 : R) • m + (0 : R) • m = ((0 : R) + 0) • m := (h.add_smul 0 0 m).symm
    _ = (0 : R) • m + 0 := by rw [add_zero, add_zero]

private theorem smul_zero_from_laws {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [SMul R M] (h : ModuleLaws R M) (r : R) :
    r • (0 : M) = 0 := by
  apply add_left_cancel (a := r • (0 : M))
  calc
    r • (0 : M) + r • (0 : M) = r • ((0 : M) + 0) := (h.smul_add r 0 0).symm
    _ = r • (0 : M) + 0 := by rw [add_zero, add_zero]

/-- The four source axioms produce exactly a module with the given action. -/
theorem moduleCharacterization : ModuleCharacterization.{u, v} := by
  intro R _ M _ s
  let : SMul R M := s
  constructor
  · intro h
    refine ⟨{ s with
      one_smul := h.one_smul
      mul_smul := h.mul_smul
      add_smul := h.add_smul
      smul_add := h.smul_add
      zero_smul := zero_smul_from_laws h
      smul_zero := smul_zero_from_laws h }, rfl⟩
  · rintro ⟨a, ha⟩
    cases ha
    let : Module R M := a
    exact {
      one_smul := _root_.one_smul R
      mul_smul := SemigroupAction.mul_smul
      add_smul := _root_.add_smul
      smul_add := _root_.smul_add }

theorem zeroSmul : ZeroSmul.{u, v} := by
  intro R _ M _ _ m
  exact _root_.zero_smul R m

theorem smulZero : SmulZero.{u, v} := by
  intro R _ M _ _ r
  exact _root_.smul_zero r

theorem negSmul : NegSmul.{u, v} := by
  intro R _ M _ _ r m
  exact _root_.neg_smul r m

theorem smulNeg : SmulNeg.{u, v} := by
  intro R _ M _ _ r m
  exact _root_.smul_neg r m

/-- Specializing the scalar ring to a field gives vector spaces. -/
theorem vectorSpaceCharacterization : VectorSpaceCharacterization.{u, v} := by
  intro K _ V _ s
  exact moduleCharacterization K V s

theorem integerModuleExistence : IntegerModuleExistence.{v} := by
  intro M _
  exact ⟨AddCommGroup.toIntModule M, fun _ _ => rfl⟩

/-- Even an independently supplied integer action is forced to be `zsmul`. -/
theorem integerModuleAction : IntegerModuleAction.{v} := by
  intro M _ a z m
  exact int_smul_eq_zsmul a z m

theorem regularModule : RegularModule.{u} := by
  intro R _
  exact ⟨Semiring.toModule, fun _ _ => rfl⟩

/-- Closure under left multiplication is exactly the additional closure
condition making an additive subgroup a submodule of the regular module. -/
theorem leftIdealCharacterization : LeftIdealCharacterization.{u} := by
  intro R _ I
  constructor
  · intro h
    refine ⟨{
      carrier := I
      zero_mem' := I.zero_mem
      add_mem' := fun hx hy => I.add_mem hx hy
      smul_mem' := fun r x hx => h r x hx }, ?_⟩
    exact SetLike.coe_injective rfl
  · rintro ⟨N, rfl⟩ r x hx
    exact N.smul_mem r hx

end D07.Ch16.Definition
