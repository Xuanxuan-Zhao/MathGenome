import MathGenome.Internal.Specs.D07.Ch01.IsomorphismDefinition
import MathGenome.Internal.Specs.D07.Ch01.KernelImage
import Mathlib.SetTheory.Cardinal.Finite

/-!
Independent specification of `K07.01.injective_kernel`
(paper.tex:335–344, chapters/M07.01.tex:120–129).

The first two statements use the kernel and image carriers from the upstream
specification, so `{1}` and the whole target are literal sets. All groups are
arbitrary and may lie in different universes. Only the final finite-group
statements assume finiteness and equality of orders. Trivial groups are allowed.
The bundled conclusion retains the specified forward homomorphism.
-/

namespace Specs.D07.Ch01.InjectiveKernel

universe u v

def InjectiveIffKernelSingleton : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    Function.Injective f ↔ (f.ker : Set G) = {1}

def SurjectiveIffImageUniv : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] (f : G →* H),
    Function.Surjective f ↔ (f.range : Set H) = Set.univ

def IsomorphismOfFiniteInjective : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H), Nat.card G = Nat.card H → Function.Injective f →
      IsomorphismDefinition.isomorphismPredicateValue G H f

def IsomorphismOfFiniteSurjective : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H), Nat.card G = Nat.card H → Function.Surjective f →
      IsomorphismDefinition.isomorphismPredicateValue G H f

def FiniteIsomorphismBundled : Prop :=
  ∀ (G : Type u) (H : Type v) [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H), Nat.card G = Nat.card H →
      (Function.Injective f ∨ Function.Surjective f) →
        ∃ e : G ≃* H, e.toMonoidHom = f

end Specs.D07.Ch01.InjectiveKernel
