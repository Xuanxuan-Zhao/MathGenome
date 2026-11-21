import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Chief.SolvableFactors

/-! Solvability characterized by elementary abelian chief factors. -/

namespace ALG02GroupTheory.Chief

universe u

theorem solvable_iff_chiefSeries_elementary_abelian (G : Type u) [Group G] [Finite G] :
    Group.IsSolvable G ↔
      ∃ s : ChiefSeries G, ∀ i : Fin s.length,
        ∃ p : ℕ, p.Prime ∧ IsMulCommutative (chiefFactor s i) ∧
          Monoid.exponent (chiefFactor s i) = p := by
  constructor
  · intro hSolvable
    let _ := hSolvable
    obtain ⟨s⟩ := chiefSeries_exists G
    exact ⟨s, solvable_chiefFactor_elementary_abelian s⟩
  · rintro ⟨s, hFactors⟩
    have hTerms : ∀ i : Fin (s.length + 1), Group.IsSolvable (s.term i) := by
      refine Fin.induction (motive := fun i => Group.IsSolvable (s.term i)) ?_ ?_
      · rw [s.first_eq_bot]
        infer_instance
      · intro i hLower
        let _ := hLower
        let _ := s.normal i.castSucc
        let e := Subgroup.subgroupOfEquivOfLe (s.step i).1.le
        let _ : Group.IsSolvable ((s.term i.castSucc).subgroupOf (s.term i.succ)) :=
          Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
        obtain ⟨_, _, hComm, _⟩ := hFactors i
        let _ : Group.IsSolvable (Factor (s.term i.castSucc) (s.term i.succ)) :=
          Group.isSolvable_of_comm hComm.is_comm.comm
        exact Group.isSolvable_of_subgroup_quotient
          ((s.term i.castSucc).subgroupOf (s.term i.succ))
    let _ : Group.IsSolvable (⊤ : Subgroup G) := s.last_eq_top ▸ hTerms (Fin.last s.length)
    let topEquiv := Subgroup.topEquiv (G := G)
    exact Group.isSolvable_of_surjective (f := topEquiv.toMonoidHom) topEquiv.surjective

end ALG02GroupTheory.Chief
