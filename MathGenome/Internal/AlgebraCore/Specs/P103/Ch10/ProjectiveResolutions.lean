import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.Complexes
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Isomorphisms

/-! Ordinary resolutions, paper.tex 2435–2455. The augmented sequence is
exact; `complex` deletes the module and the augmentation. Rings may be
noncommutative or zero. There is no finiteness condition. Using the opposite
ring gives precisely the right-module convention of the source. -/
namespace P103.Specs.Ch10.ProjectiveResolutions

open P103.Specs.Ch10.Complexes
universe u v
variable (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The nonnegative complex with its exact augmentation to `A`. The universe
of the terms accommodates free modules on the underlying set of `A`. -/
structure Resolution where
  complex : ChainComplex (ModuleCat.{max u v} R) ℕ
  ε : complex.X 0 →ₗ[R] A
  surjective : Function.Surjective ε
  exact_zero : LinearMap.range (complex.d 1 0).hom = LinearMap.ker ε
  exact_succ : ∀ n : ℕ, LinearMap.range (complex.d (n + 2) (n + 1)).hom =
    LinearMap.ker (complex.d (n + 1) n).hom

variable {R A}

def Resolution.IsFree (Q : Resolution R A) : Prop :=
  ∀ n, Module.Free R (Q.complex.X n)

def Resolution.IsProjective (Q : Resolution R A) : Prop :=
  ∀ n, Module.Projective R (Q.complex.X n)

/-- The identification is specified on every cycle representative by the
augmentation, so it is canonical rather than an arbitrary module isomorphism. -/
def Resolution.HasH0 (Q : Resolution R A) : Prop :=
  ∃ e : Homology Q.complex 0 ≃ₗ[R] A,
    ∀ z : cycles Q.complex 0, e (homologyClass Q.complex 0 z) = Q.ε z.val

def exists_free_resolutionType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A],
    ∃ Q : Resolution R A, Q.IsFree

def free_is_projectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (Q : Resolution R A), Q.IsFree → Q.IsProjective

def exists_projective_resolutionType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A],
    ∃ Q : Resolution R A, Q.IsProjective

def homology_zeroType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (Q : Resolution R A), Q.HasH0

def homology_succType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A]
    (Q : Resolution R A) (n : ℕ), Subsingleton (Homology Q.complex (n + 1))

/-- Naturality with respect to any map of augmented complexes. -/
def homology_zero_naturalType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : Type v) [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B] (Q : Resolution R A) (T : Resolution R B)
    (f : A →ₗ[R] B) (g : Q.complex ⟶ T.complex)
    (_h : T.ε.comp (g.f 0).hom = f.comp Q.ε)
    (eQ : Homology Q.complex 0 ≃ₗ[R] A) (eT : Homology T.complex 0 ≃ₗ[R] B)
    (_hQ : ∀ z, eQ (homologyClass Q.complex 0 z) = Q.ε z.val)
    (_hT : ∀ z, eT (homologyClass T.complex 0 z) = T.ε z.val),
    eT.toLinearMap.comp (homologyMap g 0) = f.comp eQ.toLinearMap

def right_resolutionType : Prop :=
  ∀ (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    ∃ Q : Resolution Rᵐᵒᵖ A, Q.IsFree ∧ Q.IsProjective ∧ Q.HasH0 ∧
      ∀ n : ℕ, Subsingleton (Homology Q.complex (n + 1))

end P103.Specs.Ch10.ProjectiveResolutions
