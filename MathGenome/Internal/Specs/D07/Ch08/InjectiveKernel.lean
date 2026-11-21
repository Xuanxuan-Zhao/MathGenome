import Mathlib.RingTheory.Ideal.Maps

/-!
Independent specification for K07.08.injective_kernel, paper.tex:1325–1335.
The rings are associative and unital, with neither commutativity nor
nontriviality assumed. `RingHom.ker` is the zero fibre, and `⊥` is the
zero ideal, whose only element is zero.
-/

universe u v

namespace Specs.D07.Ch08.InjectiveKernel

/-- A ring homomorphism is injective exactly when its kernel is zero. -/
def InjectiveIffKernelZero : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    Function.Injective f ↔ RingHom.ker f = ⊥

end Specs.D07.Ch08.InjectiveKernel
