import MathGenome.Internal.D07.Ch01.ElementaryGroupLaws
import MathGenome.Internal.Specs.D07.Ch05.ActionDefinition

/-!
# Left group actions

`K07.05.action_definition`: action axioms, inverse acting maps, and the
faithful/free/transitive predicates, with the source's empty-set convention.
-/

namespace D07.Ch05.ActionDefinition

universe u v

/-- A left group action is the usual `MulAction`, without additional conditions. -/
abbrev ActionStructure (G : Type u) (X : Type v) [Group G] := MulAction G X

def actionAxioms (G : Type u) (X : Type v) [Group G] (act : G → X → X) : Prop :=
  (∀ x : X, act (1 : G) x = x) ∧
  (∀ (g h : G) (x : X), act (g * h) x = act g (act h x))

def IsFaithful (G : Type u) (X : Type v) [Group G] [MulAction G X] : Prop :=
  ∀ g h : G, (fun x : X => g • x) = (fun x : X => h • x) → g = h

def IsFree (G : Type u) (X : Type v) [Group G] [MulAction G X] : Prop :=
  ∀ (g : G) (x : X), g • x = x → g = 1

def IsTransitive (G : Type u) (X : Type v) [Group G] [MulAction G X] : Prop :=
  Nonempty X ∧ ∀ x y : X, ∃ g : G, g • x = y

theorem action_laws (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    actionAxioms G X (fun g x => g • x) :=
  ⟨one_smul G, mul_smul⟩

theorem axioms_realized (G : Type u) (X : Type v) [Group G] (act : G → X → X)
    (h : actionAxioms G X act) : ∃ a : MulAction G X, a.smul = act := by
  exact ⟨{ smul := act, one_smul := h.1, mul_smul := h.2 }, rfl⟩

theorem inverse_action (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G) :
    (∀ x : X, g⁻¹ • (g • x) = x) ∧ (∀ x : X, g • (g⁻¹ • x) = x) :=
  ⟨inv_smul_smul g, smul_inv_smul g⟩

theorem acting_maps_bijective (G : Type u) (X : Type v)
    [Group G] [MulAction G X] (g : G) : Function.Bijective (fun x : X => g • x) := by
  constructor
  · intro x y h
    calc
      x = g⁻¹ • (g • x) := (inv_smul_smul g x).symm
      _ = g⁻¹ • (g • y) := congrArg (fun z : X => g⁻¹ • z) h
      _ = y := inv_smul_smul g y
  · intro x
    exact ⟨g⁻¹ • x, smul_inv_smul g x⟩

theorem faithful_iff_faithfulSMul (G : Type u) (X : Type v)
    [Group G] [MulAction G X] : IsFaithful G X ↔ FaithfulSMul G X := by
  constructor
  · intro h
    exact ⟨fun {g k} hk => h g k (funext hk)⟩
  · intro h g k hk
    exact h.eq_of_smul_eq_smul (congrFun hk)

theorem transitive_iff_nonempty_pretransitive (G : Type u) (X : Type v)
    [Group G] [MulAction G X] :
    IsTransitive G X ↔ Nonempty X ∧ MulAction.IsPretransitive G X := by
  exact ⟨fun h => ⟨h.1, ⟨h.2⟩⟩, fun h => ⟨h.1, h.2.exists_smul_eq⟩⟩

theorem empty_action_allowed (G : Type u) (X : Type v) [Group G]
    (h : IsEmpty X) : Nonempty (MulAction G X) := by
  exact ⟨{ smul := fun _ x => h.false x |>.elim
           one_smul := fun x => h.false x |>.elim
           mul_smul := fun _ _ x => h.false x |>.elim }⟩

theorem empty_not_transitive (G : Type u) (X : Type v) [Group G] [MulAction G X]
    (h : IsEmpty X) : ¬ IsTransitive G X := by
  intro ht
  exact ht.1.elim h.false

theorem singleton_counterexample (G : Type u) [Group G] [Nontrivial G] :
    ∃ a : MulAction G PUnit.{v + 1},
      (∀ (g : G) (x : PUnit.{v + 1}), a.smul g x = x) ∧
      @IsTransitive G PUnit _ a ∧
      ¬ @IsFaithful G PUnit _ a ∧ ¬ @IsFree G PUnit _ a := by
  let a : MulAction G PUnit.{v + 1} :=
    { smul := fun _ x => x, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl }
  letI := a
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨a, fun _ _ => rfl, ⟨⟨PUnit.unit⟩, ?_⟩, ?_, ?_⟩
  · intro x y
    exact ⟨1, Subsingleton.elim _ _⟩
  · intro h
    exact hg (h g 1 rfl)
  · intro h
    exact hg (h g PUnit.unit rfl)

end D07.Ch05.ActionDefinition
