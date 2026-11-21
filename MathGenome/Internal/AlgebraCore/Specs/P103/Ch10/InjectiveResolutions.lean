import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Exact.Basic

/-!
The injective part of paper.tex, Theorem ALG-10-C02-R01 (2435–2471).
An ordinary resolution starts in degree zero; its complex omits the module
and augmentation. Rings are associative and unital, with the zero ring allowed.
Right modules are obtained by substituting the opposite ring. The ring and
module can lie in different universes; resolution terms lie in their maximum.
-/
namespace P103.Specs.Ch10.InjectiveResolutions

open CategoryTheory P103.Specs.Ch10.Complexes
noncomputable section
universe u v

/-- An augmented exact nonnegative cochain complex of injective modules.
There is no finiteness or nonzero assumption. -/
structure Resolution (R : Type u) [Ring R] (A : Type v)
    [AddCommGroup A] [Module R A] where
  complex : CochainComplex (ModuleCat.{max u v} R) ℕ
  injectiveTerm : ∀ n, Module.Injective R (complex.X n)
  η : A →ₗ[R] complex.X 0
  injective_η : Function.Injective η
  exact_zero : Function.Exact η (complex.d 0 1).hom
  exact_succ : ∀ n, Function.Exact (complex.d n (n + 1)).hom
    (complex.d (n + 1) (n + 2)).hom

variable {R : Type u} [Ring R] {A B : Type v}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- The augmentation viewed as a map to the degree-zero cycles. -/
def Resolution.augmentationCycles (I : Resolution R A) : A →ₗ[R] cycles I.complex 0 :=
  I.η.codRestrict (cycles I.complex 0) (by
    intro a
    change (I.complex.d 0 ((ComplexShape.up ℕ).next 0)).hom (I.η a) = 0
    rw [CochainComplex.next]
    exact I.exact_zero.apply_apply_eq_zero a)

/-- The canonical identification sends a to the class of η(a). -/
def Resolution.augmentationClass (I : Resolution R A) :
    A →ₗ[R] Homology I.complex 0 :=
  (homologyClass I.complex 0).comp I.augmentationCycles

/-- Existence is an obligation, not an assumed resolution certificate. -/
def existsResolutionType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A],
    Nonempty (Resolution R A)

def homologyZeroType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (I : Resolution R A),
    ∃ e : A ≃ₗ[R] Homology I.complex 0, e.toLinearMap = I.augmentationClass

def positiveHomologyType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (I : Resolution R A) (n : ℕ), Subsingleton (Homology I.complex (n + 1))

/-- Naturality for every map of augmented resolutions over a module map.
No choice of comparison map is assumed to exist in this statement. -/
def homologyZeroNaturalityType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (I : Resolution R A) (J : Resolution R B)
    (u : A →ₗ[R] B) (f : I.complex ⟶ J.complex),
    (f.f 0).hom.comp I.η = J.η.comp u →
    (homologyMap f 0).comp I.augmentationClass = J.augmentationClass.comp u

def rightResolutionType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    Nonempty (Resolution Rᵐᵒᵖ A)

end
end P103.Specs.Ch10.InjectiveResolutions
