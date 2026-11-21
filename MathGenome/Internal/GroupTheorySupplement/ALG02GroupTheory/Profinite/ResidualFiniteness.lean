import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Profinite.Topology

/-! Residual finiteness and simultaneous separation by a finite quotient. -/

namespace ALG02GroupTheory.Profinite

universe u

theorem residuallyFinite_iff_finiteQuotient (G : Type u) [Group G] :
    Group.ResiduallyFinite G ↔
      ∀ g : G, g ≠ 1 →
        ∃ N : FiniteIndexNormalSubgroup G, QuotientGroup.mk' N.toSubgroup g ≠ 1 := by
  rw [Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup]
  exact forall_congr' fun g => imp_congr_right fun _ => exists_congr fun N =>
    not_congr (QuotientGroup.eq_one_iff (N := N.toSubgroup) g).symm

theorem residuallyFinite_iff_finiteHom (G : Type u) [Group G] :
    Group.ResiduallyFinite G ↔
      ∀ g : G, g ≠ 1 →
        ∃ (H : Type u) (_ : Group H) (_ : Finite H) (f : G →* H), f g ≠ 1 := by
  refine ⟨?_, Group.residuallyFinite_of_forall_exists_finite_monoidHom⟩
  intro h g hg
  obtain ⟨N, hN⟩ := (residuallyFinite_iff_finiteQuotient G).mp h g hg
  exact ⟨G ⧸ N.toSubgroup, inferInstance, inferInstance, QuotientGroup.mk' N.toSubgroup, hN⟩

theorem residuallyFinite_iff_eta_injective (G : Type u) [Group G] :
    Group.ResiduallyFinite G ↔ Function.Injective (eta G) := by
  rw [Group.residuallyFinite_def, ← ker_eta G, MonoidHom.ker_eq_bot_iff]

/-- Intersect the finite-index normal subgroups that separate the distinct pairs in `S`. -/
theorem exists_finiteQuotient_injOn (G : Type u) [Group G] (hG : Group.ResiduallyFinite G)
    (S : Set G) (hS : S.Finite) :
    ∃ N : FiniteIndexNormalSubgroup G, Set.InjOn (QuotientGroup.mk' N.toSubgroup) S := by
  classical
  let _ : Group.ResiduallyFinite G := hG
  let _ : Fintype S := hS.fintype
  let P := {p : S × S // p.1 ≠ p.2}
  choose N hN using fun p : P =>
    Group.exists_finiteIndexNormalSubgroup_of_residuallyFinite
      (p.val.1 : G) (p.val.2 : G) (Subtype.val_injective.ne p.property)
  refine ⟨finiteIntersection N, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let p : P := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
  apply hN p
  simpa only [QuotientGroup.mk'_apply, transition_mk] using
    congrArg (transition (finiteIntersection_le N p)) hxy

/-- The trivial quotient suffices for the empty set and every singleton. -/
theorem injOn_trivialQuotient_of_subsingleton (G : Type u) [Group G] (S : Set G)
    (hS : S.Subsingleton) : Set.InjOn (QuotientGroup.mk' (topIndex G).toSubgroup) S :=
  fun _ hx _ hy _ => hS hx hy

end ALG02GroupTheory.Profinite
