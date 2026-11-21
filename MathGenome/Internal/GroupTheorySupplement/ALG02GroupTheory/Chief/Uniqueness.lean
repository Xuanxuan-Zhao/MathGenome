import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.EquivariantSecondIso
import Mathlib.Order.JordanHolder
import Mathlib.Order.Sublattice

/-! Equivariant Jordan–Hölder uniqueness for chief factors. -/

namespace ALG02GroupTheory.Chief

universe u

private def normalSubgroups (G : Type u) [Group G] : Sublattice (Subgroup G) where
  carrier := {K | K.Normal}
  supClosed' := by
    intro K hK L hL
    exact @Subgroup.sup_normal G _ K L hK hL
  infClosed' := by
    intro K hK L hL
    exact @Subgroup.normal_inf_normal G _ K L hK hL

variable {G : Type u} [Group G]

local instance (K : normalSubgroups G) : (K : Subgroup G).Normal := K.property

local instance : JordanHolderLattice (normalSubgroups G) where
  IsMaximal K L := AmbientCovBy (K : Subgroup G) (L : Subgroup G)
  lt_of_isMaximal h := h.1
  sup_eq_of_isMaximal {K L N} hK hL hne := by
    apply Subtype.ext
    exact (ambient_diamond _ _ _ hK hL (fun h => hne (Subtype.ext h))).1
  isMaximal_inf_left_of_isMaximal_sup {K L} hK hL := by
    have hne : (K : Subgroup G) ≠ (L : Subgroup G) := by
      intro h
      apply hK.1.ne
      change (K : Subgroup G) = (K : Subgroup G) ⊔ (L : Subgroup G)
      rw [← h, sup_idem]
    exact (ambient_diamond _ _ _ hK hL hne).2.1

private def intervalEquiv (p q : normalSubgroups G × normalSubgroups G) : Prop :=
  Nonempty (GEquiv G (Factor (p.1 : Subgroup G) (p.2 : Subgroup G))
    (Factor (q.1 : Subgroup G) (q.2 : Subgroup G)))

private theorem intervalEquiv_symm {p q : normalSubgroups G × normalSubgroups G} :
    intervalEquiv p q → intervalEquiv q p := by
  rintro ⟨e⟩
  refine ⟨⟨e.1.symm, fun g z => e.1.injective ?_⟩⟩
  rw [e.1.apply_symm_apply, e.2, e.1.apply_symm_apply]

private theorem intervalEquiv_of_iso {p q : normalSubgroups G × normalSubgroups G}
    (h : JordanHolderLattice.Iso p q) : intervalEquiv p q := by
  refine JordanHolderLattice.Iso.rel intervalEquiv ?_ intervalEquiv_symm ?_ ?_ h
  · intro p
    exact ⟨⟨MulEquiv.refl _, fun _ _ => rfl⟩⟩
  · rintro p q r ⟨e⟩ ⟨f⟩
    refine ⟨⟨e.1.trans f.1, fun g z => ?_⟩⟩
    change f.1 (e.1 (g • z)) = g • f.1 (e.1 z)
    rw [e.2, f.2]
  · intro K L _
    obtain ⟨e, _⟩ := equivariant_second_iso (K : Subgroup G) (L : Subgroup G)
      (↑(K ⊓ L)) (↑(K ⊔ L)) rfl rfl
    exact intervalEquiv_symm (p := (K ⊓ L, L)) (q := (K, K ⊔ L)) ⟨e⟩

variable [Finite G]

private def toCompositionSeries (s : ChiefSeries G) : CompositionSeries (normalSubgroups G) where
  length := s.length
  toFun i := ⟨s.term i, s.normal i⟩
  step i := s.step i

/-- Chief series of a finite group have equal lengths and a bijective matching
of their factors by isomorphisms that preserve ambient conjugation. -/
theorem chief_series_uniqueness (s t : ChiefSeries G) :
    s.length = t.length ∧
      ∃ e : Fin s.length ≃ Fin t.length, ∀ i : Fin s.length,
        Nonempty (GEquiv G (chiefFactor s i) (chiefFactor t (e i))) := by
  have hfirst : (toCompositionSeries s).head = (toCompositionSeries t).head :=
    Subtype.ext (s.first_eq_bot.trans t.first_eq_bot.symm)
  have hlast : (toCompositionSeries s).last = (toCompositionSeries t).last :=
    Subtype.ext (s.last_eq_top.trans t.last_eq_top.symm)
  obtain ⟨e, he⟩ := CompositionSeries.jordan_holder _ _ hfirst hlast
  change Fin s.length ≃ Fin t.length at e
  refine ⟨by simpa only [Fintype.card_fin] using Fintype.card_congr e, e, ?_⟩
  intro i
  exact intervalEquiv_of_iso (he i)

end ALG02GroupTheory.Chief
