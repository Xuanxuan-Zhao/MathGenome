import Mathlib.Algebra.Module.Injective

/-! Injective envelopes, paper.tex 361–408. Rings are unital and may be
noncommutative or zero. Right modules are left modules over the opposite ring.
An extension is represented by a linear injection, rather than a literal subset.
All ambient universes used in maximality contain the ring universe. -/
namespace P103.Specs.Ch02.InjectiveEnvelope

universe u v w z

/-- Every nonzero submodule has nonzero intersection with `S`. -/
def Essential {R : Type u} {E : Type w} [Ring R] [AddCommGroup E]
    [Module R E] (S : Submodule R E) : Prop :=
  ∀ U : Submodule R E, U ≠ ⊥ → U ⊓ S ≠ ⊥

def EssentialExtension {R : Type u} {M : Type v} {E : Type w}
    [Ring R] [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E) : Prop := Function.Injective i ∧ Essential (LinearMap.range i)

def IsEnvelope {R : Type u} {M : Type v} {E : Type w}
    [Ring R] [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E) : Prop := Module.Injective R E ∧ EssentialExtension i

/-- There is no proper further essential extension over the given copy of `M`. -/
def MaximalEssential {R : Type u} {M : Type v} {E : Type w}
    [Ring R] [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E) : Prop := EssentialExtension i ∧
  ∀ (F : Type (max u w)) [AddCommGroup F] [Module R F] (j : E →ₗ[R] F),
    Function.Injective j → EssentialExtension (j.comp i) → Function.Surjective j

/-- Minimal among injective submodules that contain the given copy of `M`. -/
def MinimalInjective {R : Type u} {M : Type v} {E : Type w}
    [Ring R] [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E) : Prop := Function.Injective i ∧ Module.Injective R E ∧
  ∀ S : Submodule R E, LinearMap.range i ≤ S → Module.Injective R S → S = ⊤

def existsEnvelopeType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M],
    ∃ (E : Type (max u v)) (_ : AddCommGroup E) (_ : Module R E)
      (i : M →ₗ[R] E), IsEnvelope i

/-- Maximality also holds for further extensions in arbitrary universes. -/
def noProperExtensionType : Prop :=
  ∀ (R : Type u) (M : Type v) (E : Type (max u w)) (F : Type z) [Ring R]
    [AddCommGroup M] [AddCommGroup E] [AddCommGroup F]
    [Module R M] [Module R E] [Module R F]
    (i : M →ₗ[R] E) (j : E →ₗ[R] F), IsEnvelope i →
      Function.Injective j → EssentialExtension (j.comp i) → Function.Surjective j

def envelope_iff_maximalType : Prop :=
  ∀ (R : Type u) (M : Type v) (E : Type (max u w)) [Ring R]
    [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E), IsEnvelope i ↔ MaximalEssential i

def envelope_iff_minimalType : Prop :=
  ∀ (R : Type u) (M : Type v) (E : Type (max u w)) [Ring R]
    [AddCommGroup M] [AddCommGroup E] [Module R M] [Module R E]
    (i : M →ₗ[R] E), IsEnvelope i ↔ MinimalInjective i

def uniqueType : Prop :=
  ∀ (R : Type u) (M : Type v) (E : Type (max u w)) (F : Type (max u z))
    [Ring R] [AddCommGroup M] [AddCommGroup E] [AddCommGroup F]
    [Module R M] [Module R E] [Module R F]
    (i : M →ₗ[R] E) (j : M →ₗ[R] F), IsEnvelope i → IsEnvelope j →
      ∃ e : E ≃ₗ[R] F, e.toLinearMap.comp i = j

def rightExistsEnvelopeType : Prop :=
  ∀ (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module Rᵐᵒᵖ M],
    ∃ (E : Type (max u v)) (_ : AddCommGroup E) (_ : Module Rᵐᵒᵖ E)
      (i : M →ₗ[Rᵐᵒᵖ] E), IsEnvelope i

end P103.Specs.Ch02.InjectiveEnvelope
