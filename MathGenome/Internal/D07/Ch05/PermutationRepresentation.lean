import MathGenome.Internal.D07.Ch01.InjectiveKernel
import MathGenome.Internal.D07.Ch02.PermutationConvention
import MathGenome.Internal.D07.Ch05.ActionDefinition
import MathGenome.Internal.Specs.D07.Ch05.PermutationRepresentation

/-!
Actions as permutation representations (`K07.05.permutation_representation`).
No finiteness, inhabitedness of the acted-on type, or faithfulness is assumed.
-/

namespace D07.Ch05.PermutationRepresentation

universe u v

def actionToHom (G : Type u) (X : Type v) [Group G] (a : MulAction G X) :
    G →* Equiv.Perm X :=
  @MulAction.toPermHom G X _ a

def homToAction (G : Type u) (X : Type v) [Group G] (ρ : G →* Equiv.Perm X) :
    MulAction G X :=
  MulAction.compHom X ρ

theorem actionToHom_apply (G : Type u) (X : Type v) [Group G]
    (a : MulAction G X) (g : G) (x : X) :
    actionToHom G X a g x = a.smul g x := rfl

theorem homToAction_apply (G : Type u) (X : Type v) [Group G]
    (ρ : G →* Equiv.Perm X) (g : G) (x : X) :
    (homToAction G X ρ).smul g x = ρ g x := rfl

theorem homToAction_actionToHom (G : Type u) (X : Type v) [Group G]
    (a : MulAction G X) : homToAction G X (actionToHom G X a) = a := by
  apply MulAction.ext
  rfl

theorem actionToHom_homToAction (G : Type u) (X : Type v) [Group G]
    (ρ : G →* Equiv.Perm X) : actionToHom G X (homToAction G X ρ) = ρ := by
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro x
  rfl

theorem actions_homs_equiv (G : Type u) (X : Type v) [Group G] :
    ∃ e : MulAction G X ≃ (G →* Equiv.Perm X),
      (∀ a : MulAction G X, e a = actionToHom G X a) ∧
      (∀ ρ : G →* Equiv.Perm X, e.symm ρ = homToAction G X ρ) := by
  exact ⟨{ toFun := actionToHom G X
           invFun := homToAction G X
           left_inv := homToAction_actionToHom G X
           right_inv := actionToHom_homToAction G X },
    fun _ => rfl, fun _ => rfl⟩

theorem kernel_iff_fixes (G : Type u) (X : Type v) [Group G]
    [a : MulAction G X] (g : G) :
    g ∈ (actionToHom G X a).ker ↔ ∀ x : X, g • x = x := by
  change actionToHom G X a g = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun σ : Equiv.Perm X => σ x) h
  · intro h
    exact Equiv.ext h

theorem faithful_iff_injective (G : Type u) (X : Type v) [Group G]
    [a : MulAction G X] :
    ActionDefinition.IsFaithful G X ↔ Function.Injective (actionToHom G X a) := by
  constructor
  · intro h g k hgk
    apply h g k
    exact funext (fun x => congrArg (fun σ : Equiv.Perm X => σ x) hgk)
  · intro h g k hgk
    apply h
    exact Equiv.ext (congrFun hgk)

theorem empty_representation_trivial (G : Type u) (X : Type v) [Group G]
    [a : MulAction G X] (h : IsEmpty X) : actionToHom G X a = 1 := by
  apply MonoidHom.ext
  intro g
  apply Equiv.ext
  intro x
  exact (h.false x).elim

theorem empty_faithful_iff_trivial (G : Type u) (X : Type v) [Group G]
    [MulAction G X] (h : IsEmpty X) :
    ActionDefinition.IsFaithful G X ↔ Subsingleton G := by
  constructor
  · intro hf
    refine ⟨fun g k => hf g k ?_⟩
    exact funext (fun x => (h.false x).elim)
  · intro hs g k _
    exact hs.elim g k

end D07.Ch05.PermutationRepresentation
