import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Completion

/-! Cofinal restriction and the completion of a finite group, GR02-C05.04. -/

namespace Specs.ALG02GroupTheory.Profinite

universe u

variable {G : Type u} [Group G]

/-- The compatible tuples on a subset of the finite-index normal subgroups. -/
def restrictedTuples (D : Set (FiniteIndexNormalSubgroup G)) :
    Subgroup (∀ d : D, finiteQuotient d.1) where
  carrier := { x | ∀ ⦃d e : D⦄ (h : d.1 ≤ e.1), transitionValue h (x d) = x e }
  one_mem' := by
    intro d e h
    exact map_one (transitionValue h)
  mul_mem' := by
    intro x y hx hy d e h
    exact (map_mul (transitionValue h) (x d) (y d)).trans
      (congrArg₂ (· * ·) (hx h) (hy h))
  inv_mem' := by
    intro x hx d e h
    exact (map_inv (transitionValue h) (x d)).trans (congrArg Inv.inv (hx h))

/-- The restriction of the inverse-limit construction uses the product subspace topology. -/
abbrev RestrictedCompletion (D : Set (FiniteIndexNormalSubgroup G)) :=
  ↥(restrictedTuples D)

def RestrictedCompletionType :=
  ∀ {G : Type u} [Group G], Set (FiniteIndexNormalSubgroup G) → Type u

def RestrictCoordinatesType :=
  ∀ {G : Type u} [Group G] (D : Set (FiniteIndexNormalSubgroup G)),
    completionValue G →ₜ* RestrictedCompletion D

/-- The actual restriction of a tuple to the coordinates in `D`. -/
def restrictCoordinatesValue : RestrictCoordinatesType := by
  intro G _ D
  refine
    { toFun := fun x => ⟨fun d => projectionValue d.1 x, ?_⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      continuous_toFun := ?_ }
  · intro d e h
    exact x.2 h.hom
  · exact continuous_induced_rng.mpr
      (continuous_pi fun d => (projectionValue d.1).continuous_toFun)

def CofinalRestriction : Prop :=
  ∀ {G : Type u} [Group G] (D : Set (FiniteIndexNormalSubgroup G)),
    (∀ N : FiniteIndexNormalSubgroup G, ∃ d : D, d.1 ≤ N) →
    ∃ e : completionValue G ≃ₜ* RestrictedCompletion D,
      (e : completionValue G → RestrictedCompletion D) = restrictCoordinatesValue D ∧
      ∀ (x : RestrictedCompletion D) (N : FiniteIndexNormalSubgroup G)
        (d : D) (h : d.1 ≤ N), projectionValue N (e.symm x) = transitionValue h (x.1 d)

def FiniteCompletion : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G],
    ∃ e : G ≃ₜ* completionValue G,
      (e : G → completionValue G) = etaValue G ∧
      ∀ x : completionValue G, e.symm x = QuotientGroup.quotientBot
        (projectionValue (FiniteIndexNormalSubgroup.ofSubgroup ⊥) x)

end Specs.ALG02GroupTheory.Profinite
