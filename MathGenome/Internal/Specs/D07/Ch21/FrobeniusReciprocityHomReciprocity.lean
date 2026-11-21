import MathGenome.Internal.Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

/-!
Frobenius reciprocity for the actual ordinary tensor quotient in
paper.tex:6574–6600. The Hom spaces are spaces of complex-linear intertwiners.
There is no finite-dimensionality or nonzero-space assumption.

`IsInducedAction` identifies the action on the shared quotient by its values on
all generators. `ReciprocityFormulas` prescribes both directions of the linear
equivalence. Naturality is stated for arbitrary intertwiners in both variables,
using the induced map `[g,v] ↦ [g,a(v)]`; the preceding specification constructs
that map uniquely. Thus the naturality statement applies to the constructed
equivalences rather than to a separately assumed adjunction.
-/
namespace Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity

universe u v v' w w'
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge

variable {G : Type u} [Group G] {H : Subgroup G}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
  {W : Type w} [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ G W}

/-- The quotient's left action, characterized on its spanning generators. -/
def IsInducedAction (σ : Representation ℂ G (NotesInd H ρ)) : Prop :=
  ∀ k g v, σ k (notesMk H ρ g v) = notesMk H ρ (k * g) v

/-- The two maps are exactly those in the source, including their scalar linearity
(which is part of the type of `e`). -/
def ReciprocityFormulas {σ : Representation ℂ G (NotesInd H ρ)}
    (e : IntertwiningMap σ τ ≃ₗ[ℂ] IntertwiningMap ρ (τ.comp H.subtype)) : Prop :=
  (∀ T v, e T v = T (notesMk H ρ 1 v)) ∧
  (∀ A g v, e.symm A (notesMk H ρ g v) = τ g (A v))

/-- Existence on the constructed quotient, with its descended raw tensor action.
The same action works for every target representation. -/
def HomReciprocity : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V),
    ∃ σ : Representation ℂ G (NotesInd H ρ),
      (∀ k x, σ k ((relations H ρ).mkQ x) =
        (relations H ρ).mkQ (tensorAction (V := V) k x)) ∧
      IsInducedAction σ ∧
      ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
        ∃ e : IntertwiningMap σ τ ≃ₗ[ℂ] IntertwiningMap ρ (τ.comp H.subtype),
          ReciprocityFormulas e

/-- The result is independent of how the quotient's left action was obtained. -/
def AnyInducedAction : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (σ : Representation ℂ G (NotesInd H ρ)), IsInducedAction σ →
    ∀ (W : Type w) [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W),
      ∃ e : IntertwiningMap σ τ ≃ₗ[ℂ] IntertwiningMap ρ (τ.comp H.subtype),
        ReciprocityFormulas e

/-- Descent and equivariance of induction on a morphism, with uniqueness. -/
def InducedMorphism : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) (V' : Type v') [AddCommGroup V] [AddCommGroup V']
    [Module ℂ V] [Module ℂ V']
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H V')
    (σ : Representation ℂ G (NotesInd H ρ))
    (σ' : Representation ℂ G (NotesInd H ρ')),
    IsInducedAction σ → IsInducedAction σ' →
    ∀ a : IntertwiningMap ρ ρ',
      ∃! i : IntertwiningMap σ σ',
        ∀ g v, i (notesMk H ρ g v) = notesMk H ρ' g (a v)

/-- Simultaneous contravariant naturality in V and covariant naturality in W.
Equality is pointwise equality of H-intertwiners. Either variable may be fixed
by choosing an identity map, and every vector space here may be zero. -/
def Naturality : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G)
    (V : Type v) (V' : Type v') (W : Type w) (W' : Type w')
    [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W] [AddCommGroup W']
    [Module ℂ V] [Module ℂ V'] [Module ℂ W] [Module ℂ W']
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H V')
    (τ : Representation ℂ G W) (τ' : Representation ℂ G W')
    (σ : Representation ℂ G (NotesInd H ρ))
    (σ' : Representation ℂ G (NotesInd H ρ'))
    (a : IntertwiningMap ρ' ρ) (b : IntertwiningMap τ τ')
    (i : IntertwiningMap σ' σ),
    (∀ g v, i (notesMk H ρ' g v) = notesMk H ρ g (a v)) →
    ∀ (e : IntertwiningMap σ τ ≃ₗ[ℂ] IntertwiningMap ρ (τ.comp H.subtype))
      (e' : IntertwiningMap σ' τ' ≃ₗ[ℂ] IntertwiningMap ρ' (τ'.comp H.subtype)),
      ReciprocityFormulas e → ReciprocityFormulas e' →
      ∀ (T : IntertwiningMap σ τ) v,
        e' ((b.comp T).comp i) v = b (e T (a v))

end
end Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity
