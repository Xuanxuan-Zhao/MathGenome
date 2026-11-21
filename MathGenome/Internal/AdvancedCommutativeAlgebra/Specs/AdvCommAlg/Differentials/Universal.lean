import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Derivations
import Mathlib.RingTheory.Kaehler.Basic

/-! Independent specifications for paper.tex, KD-02, including its concluding
uniqueness assertion. Rings may be zero. Coefficient actions are compatible. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w z

noncomputable section

def omegaType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], Type v

def omegaValue : omegaType.{u,v} :=
  fun A B _ _ _ => KaehlerDifferential A B

def universalDerivationType := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B], Derivation A B (KaehlerDifferential A B)

def universalDerivationValue : universalDerivationType.{u,v} :=
  fun A B _ _ _ => KaehlerDifferential.D A B

def universalEquivType := ∀ (A : Type u) (B : Type v) (M : Type w)
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
  [Module B M] [Module A M] [IsScalarTower A B M],
  (KaehlerDifferential A B →ₗ[B] M) ≃ₗ[B] Derivation A B M

def universalEquivValue : universalEquivType.{u,v,w} :=
  fun A B M _ _ _ _ _ _ _ => KaehlerDifferential.linearMapEquivDerivation A B

def universalEquivApply : Prop := ∀ (A : Type u) (B : Type v) (M : Type w)
  [CommRing A] [CommRing B] [Algebra A B] [AddCommGroup M]
  [Module B M] [Module A M] [IsScalarTower A B M]
  (f : KaehlerDifferential A B →ₗ[B] M),
  universalEquivValue A B M f = f.compDer (KaehlerDifferential.D A B)

def universalNaturality : Prop :=
  ∀ (A : Type u) (B : Type v) (M : Type w) (N : Type z)
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  (g : M →ₗ[B] N) (f : KaehlerDifferential A B →ₗ[B] M),
  universalEquivValue A B N (g.comp f) = g.compDer (universalEquivValue A B M f)

def differentialsSpan : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  Submodule.span B (Set.range (KaehlerDifferential.D A B)) = ⊤

/-- The relation submodule exactly as displayed in the paper, with [b] = single b 1. -/
def differentialRelations (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] : Submodule B (B →₀ B) :=
  Submodule.span B
    ((Set.range (fun p : B × B =>
        Finsupp.single (p.1 + p.2) 1 - Finsupp.single p.1 1 - Finsupp.single p.2 1) ∪
      Set.range (fun p : B × B =>
        Finsupp.single (p.1 * p.2) 1 - p.1 • Finsupp.single p.2 1 -
          p.2 • Finsupp.single p.1 1)) ∪
      Set.range (fun a : A => Finsupp.single (algebraMap A B a) 1))

def relationKernel : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  differentialRelations A B =
    LinearMap.ker (Finsupp.linearCombination B (KaehlerDifferential.D A B))

def relationModel : Prop := ∀ (A : Type u) (B : Type v)
  [CommRing A] [CommRing B] [Algebra A B],
  ∃ e : ((B →₀ B) ⧸ differentialRelations A B) ≃ₗ[B] KaehlerDifferential A B,
    ∀ b : B, e ((differentialRelations A B).mkQ (Finsupp.single b 1)) =
      KaehlerDifferential.D A B b

/-- Universality in the two coefficient modules suffices to compare any two
universal pairs. These are precisely the four specializations of their usual
universal properties used by the uniqueness argument; no size restriction or
finite generation assumption on either pair is imposed. -/
def uniqueUniversalPair : Prop :=
  ∀ (A : Type u) (B : Type v) (U : Type w) (V : Type z)
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup U] [Module B U] [Module A U] [IsScalarTower A B U]
  [AddCommGroup V] [Module B V] [Module A V] [IsScalarTower A B V]
  (δ : Derivation A B U) (ε : Derivation A B V),
  Function.Bijective (fun f : U →ₗ[B] U => f.compDer δ) →
  Function.Bijective (fun f : U →ₗ[B] V => f.compDer δ) →
  Function.Bijective (fun f : V →ₗ[B] U => f.compDer ε) →
  Function.Bijective (fun f : V →ₗ[B] V => f.compDer ε) →
  ∃! e : U ≃ₗ[B] V, e.toLinearMap.compDer δ = ε

end
end Specs.AdvCommAlg.Differentials
