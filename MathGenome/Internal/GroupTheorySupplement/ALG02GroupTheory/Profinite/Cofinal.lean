import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Completion
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Profinite.Cofinal

/-! Restricting a profinite completion to a cofinal family of quotients. -/

namespace ALG02GroupTheory.Profinite

universe u

variable {G : Type u} [Group G]

/-- Compatible tuples on `D` with their product subspace topology. -/
abbrev RestrictedCompletion (D : Set (FiniteIndexNormalSubgroup G)) :=
  Specs.ALG02GroupTheory.Profinite.RestrictedCompletion D

/-- Restrict a point of the completion to its coordinates in `D`. -/
def restrictCoordinates (D : Set (FiniteIndexNormalSubgroup G)) :
    Completion G →ₜ* RestrictedCompletion D where
  toFun x := ⟨fun d => projection d.1 x, fun _ _ h => projection_compatible h x⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  continuous_toFun := continuous_induced_rng.mpr
    (continuous_pi fun d => (projection d.1).continuous_toFun)

private theorem transition_trans {L M N : FiniteIndexNormalSubgroup G}
    (hLM : L ≤ M) (hMN : M ≤ N) (x : finiteQuotient L) :
    transition hMN (transition hLM x) = transition (hLM.trans hMN) x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

private theorem transition_self {N : FiniteIndexNormalSubgroup G} (x : finiteQuotient N) :
    transition le_rfl x = x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

local instance (N : FiniteIndexNormalSubgroup G) : DiscreteTopology (finiteQuotient N) :=
  ⟨rfl⟩

private def continuousTransition {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N) :
    finiteQuotient M →ₜ* finiteQuotient N where
  toMonoidHom := transition h
  continuous_toFun := continuous_of_discreteTopology

/-- Cofinal restriction is a topological group isomorphism. The inverse can use any
index in the family contained in the subgroup at the desired coordinate. -/
theorem cofinal_restriction (D : Set (FiniteIndexNormalSubgroup G))
    (hD : ∀ N : FiniteIndexNormalSubgroup G, ∃ d : D, d.1 ≤ N) :
    ∃ e : Completion G ≃ₜ* RestrictedCompletion D,
      (e : Completion G → RestrictedCompletion D) = restrictCoordinates D ∧
      ∀ (x : RestrictedCompletion D) (N : FiniteIndexNormalSubgroup G)
        (d : D) (h : d.1 ≤ N), projection N (e.symm x) = transition h (x.1 d) := by
  classical
  have existsBelow := hD
  choose d hd using existsBelow
  let coordinate (x : RestrictedCompletion D) (N : FiniteIndexNormalSubgroup G) :
      finiteQuotient N := transition (hd N) (x.1 (d N))
  have coordinate_eq (x : RestrictedCompletion D) (N : FiniteIndexNormalSubgroup G)
      (e : D) (he : e.1 ≤ N) : coordinate x N = transition he (x.1 e) := by
    obtain ⟨k, hk⟩ := hD ((d N).1 ⊓ e.1)
    have hk₁ : k.1 ≤ (d N).1 := hk.trans inf_le_left
    have hk₂ : k.1 ≤ e.1 := hk.trans inf_le_right
    have hx₁ : transition hk₁ (x.1 k) = x.1 (d N) := x.2 hk₁
    have hx₂ : transition hk₂ (x.1 k) = x.1 e := x.2 hk₂
    change transition (hd N) (x.1 (d N)) = transition he (x.1 e)
    rw [← hx₁, ← hx₂, transition_trans, transition_trans]
  have coordinate_compatible (x : RestrictedCompletion D)
      {M N : FiniteIndexNormalSubgroup G} (h : M ≤ N) :
      transition h (coordinate x M) = coordinate x N :=
    (transition_trans (hd M) h (x.1 (d M))).trans
      (coordinate_eq x N (d M) ((hd M).trans h)).symm
  let extend (x : RestrictedCompletion D) : Completion G :=
    (toCompatibleTuples G).symm ⟨coordinate x, fun _ _ h => coordinate_compatible x h⟩
  have continuous_extend : Continuous extend := by
    refine (toCompatibleTuples G).continuous_invFun.comp
      (continuous_induced_rng.mpr (continuous_pi fun N => ?_))
    have h := (continuous_apply (d N)).comp
      (continuous_subtype_val :
        Continuous (fun x : RestrictedCompletion D => x.1))
    exact (continuousTransition (hd N)).continuous_toFun.comp h
  let e : Completion G ≃ₜ* RestrictedCompletion D :=
    { toFun := restrictCoordinates D
      invFun := extend
      left_inv := by
        intro x
        apply Subtype.ext
        funext N
        change transition (hd N) (projection (d N).1 x) = projection N x
        exact projection_compatible (hd N) x
      right_inv := by
        intro x
        apply Subtype.ext
        funext i
        change coordinate x i.1 = x.1 i
        exact (coordinate_eq x i.1 i le_rfl).trans (transition_self (x.1 i))
      map_mul' := map_mul (restrictCoordinates D)
      continuous_toFun := (restrictCoordinates D).continuous_toFun
      continuous_invFun := continuous_extend }
  exact ⟨e, rfl, coordinate_eq⟩

/-- For a finite discrete group the canonical map is an isomorphism, with inverse
obtained from the coordinate at the trivial subgroup. -/
theorem finite_completion (G : Type u) [Group G] [Finite G]
    [TopologicalSpace G] [DiscreteTopology G] :
    ∃ e : G ≃ₜ* Completion G,
      (e : G → Completion G) = eta G ∧
      ∀ x : Completion G, e.symm x = QuotientGroup.quotientBot
        (projection (FiniteIndexNormalSubgroup.ofSubgroup ⊥) x) := by
  let B : FiniteIndexNormalSubgroup G := FiniteIndexNormalSubgroup.ofSubgroup ⊥
  let inverse (x : Completion G) : G := QuotientGroup.quotientBot (projection B x)
  let e : G ≃ₜ* Completion G :=
    { toFun := eta G
      invFun := inverse
      left_inv := by
        intro g
        change QuotientGroup.quotientBot (projection B (eta G g)) = g
        rw [projection_eta]
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        funext N
        change projection N (eta G (inverse x)) = projection N x
        have hBN : B ≤ N := (bot_le : (⊥ : Subgroup G) ≤ N.toSubgroup)
        rw [projection_eta, ← projection_compatible hBN x]
        change QuotientGroup.mk (QuotientGroup.quotientBot (projection B x)) =
          transition hBN (projection B x)
        obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (projection B x)
        rw [← hg]
        rfl
      map_mul' := map_mul (eta G)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := (continuous_of_discreteTopology :
        Continuous (fun q : finiteQuotient B => QuotientGroup.quotientBot q)).comp
          (projection B).continuous_toFun }
  exact ⟨e, rfl, fun _ => rfl⟩

end ALG02GroupTheory.Profinite
