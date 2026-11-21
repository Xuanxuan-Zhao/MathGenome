import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ForwardPresentations
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FlatLattice

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

theorem flatCharacterization (M : _root_.Matroid α) (F : Set α) :
    M.IsFlat F ↔ F ⊆ M.E ∧ M.closure F = F := by
  exact ⟨fun h => ⟨h.subset_ground, h.closure⟩,
    fun h => M.isFlat_iff_closure_eq.mpr h.2⟩

theorem flatFinite (M : _root_.Matroid α) [M.Finite] : Finite (Flat M) := by
  have := M.ground_finite.powerset.to_subtype
  exact Finite.of_injective
    (fun F : Flat M => (⟨F.1, F.2.subset_ground⟩ : ↥(𝒫 M.E)))
    (fun _ _ h => Subtype.ext (congrArg (fun S : ↥(𝒫 M.E) => S.1) h))

theorem flatMeet (M : _root_.Matroid α) (F G : Flat M) :
    (F ⊓ G).1 = F.1 ∩ G.1 := by
  apply Set.Subset.antisymm
  · exact subset_inter inf_le_left inf_le_right
  · have hclosed : M.IsFlat (F.1 ∩ G.1) := by
      apply M.isFlat_iff_closure_eq.mpr
      apply Set.Subset.antisymm
      · exact subset_inter
          ((M.closure_subset_closure inter_subset_left).trans_eq F.2.closure)
          ((M.closure_subset_closure inter_subset_right).trans_eq G.2.closure)
      · exact M.subset_closure _ (inter_subset_left.trans F.2.subset_ground)
    exact (show (⟨F.1 ∩ G.1, hclosed⟩ : Flat M) ≤ F ⊓ G from
      le_inf inter_subset_left inter_subset_right)

theorem flatJoin (M : _root_.Matroid α) (F G : Flat M) :
    (F ⊔ G).1 = M.closure (F.1 ∪ G.1) := rfl

theorem flatBottom (M : _root_.Matroid α) :
    (⊥ : Flat M).1 = M.closure ∅ := rfl

/-- Closure preserves the canonical integer rank. -/
theorem rankClosure (M : _root_.Matroid α) [M.Finite] (A : Set α) :
    rank M (M.closure A) = rank M A := by
  simp only [rank, M.eRk_closure_eq]

/-- Rank strictly increases under proper inclusion of finite flats. -/
theorem flatRankStrict (M : _root_.Matroid α) [M.Finite] {F G : Flat M}
    (h : F < G) : rank M F.1 < rank M G.1 := by
  have hFG : F.1 ⊂ G.1 := h
  obtain ⟨e, heG, heF⟩ := Set.exists_of_ssubset hFG
  have hm := rankMonotone M F.1 G.1 h.le G.2.subset_ground
  apply lt_of_le_of_ne hm
  intro hr
  have hi := rankMonotone M (insert e F.1) G.1
    (insert_subset heG h.le) G.2.subset_ground
  have hlo := (rankIncrements M F.1 F.2.subset_ground e
    (G.2.subset_ground heG)).1
  have hecl := (closureRank M F.1 F.2.subset_ground e
    (G.2.subset_ground heG)).mpr (by linarith)
  rw [F.2.closure] at hecl
  exact heF hecl

/-- Adjoining one element outside a flat increases rank by exactly one. -/
theorem flatInsertRank (M : _root_.Matroid α) [M.Finite] (F : Flat M)
    {e : α} (he : e ∈ M.E) (heF : e ∉ F.1) :
    rank M (M.closure (insert e F.1)) = rank M F.1 + 1 := by
  rw [rankClosure]
  have hi := rankIncrements M F.1 F.2.subset_ground e he
  have hn : rank M (insert e F.1) ≠ rank M F.1 := by
    intro hr
    have h := (closureRank M F.1 F.2.subset_ground e he).mpr hr
    rw [F.2.closure] at h
    exact heF h
  omega

theorem flatCoverRank (M : _root_.Matroid α) [M.Finite] (F G : Flat M) :
    F ⋖ G ↔ F < G ∧ rank M G.1 - rank M F.1 = 1 := by
  constructor
  · intro h
    have hFG : F.1 ⊂ G.1 := h.lt
    obtain ⟨e, heG, heF⟩ := Set.exists_of_ssubset hFG
    let H := flatClosure M (insert e F.1)
    have hFH : F ≤ H := by
      exact (subset_insert e F.1).trans
        (M.subset_closure _ (insert_subset (G.2.subset_ground heG) F.2.subset_ground))
    have heH : e ∈ H.1 := M.mem_closure_of_mem' (mem_insert e F.1)
      (G.2.subset_ground heG)
    have hne : H ≠ F := by
      intro heq
      exact heF (heq ▸ heH)
    have hHG : H ≤ G := by
      exact (M.closure_subset_closure (insert_subset heG h.le)).trans_eq G.2.closure
    have heq : H = G := (h.eq_or_eq hFH hHG).resolve_left hne
    have hr := flatInsertRank M F (G.2.subset_ground heG) heF
    change rank M H.1 = rank M F.1 + 1 at hr
    rw [heq] at hr
    exact ⟨h.lt, by omega⟩
  · rintro ⟨hFG, hr⟩
    refine ⟨hFG, ?_⟩
    intro H hFH hHG
    have h1 := flatRankStrict M hFH
    have h2 := flatRankStrict M hHG
    omega

/-- The closure of a nonloop singleton covers the loop flat. -/
theorem nonloopFlatAtom (M : _root_.Matroid α) [M.Finite] {e : α}
    (he : M.IsNonloop e) : IsAtom (flatClosure M {e}) := by
  apply bot_covBy_iff.mp
  apply (flatCoverRank M ⊥ (flatClosure M {e})).mpr
  constructor
  · apply bot_lt_iff_ne_bot.mpr
    intro h
    have hem : e ∈ (flatClosure M {e}).1 :=
      M.mem_closure_of_mem' (mem_singleton e) he.mem_ground
    rw [h, flatBottom] at hem
    exact he.not_isLoop hem
  · change rank M (M.closure {e}) - rank M (⊥ : Flat M).1 = 1
    rw [rankClosure, flatBottom, rankClosure, rankEmpty]
    have hr := ((rankRecovery M {e}).mpr he.indep).2
    simpa using hr

theorem flatAtom (M : _root_.Matroid α) [M.Finite] (F : Flat M) :
    IsAtom F ↔ ∃ e, M.IsNonloop e ∧ F = flatClosure M {e} := by
  constructor
  · intro hF
    have hs : (⊥ : Flat M).1 ⊂ F.1 := hF.bot_lt
    obtain ⟨e, heF, hebot⟩ := Set.exists_of_ssubset hs
    have he : M.IsNonloop e := by
      refine ⟨?_, F.2.subset_ground heF⟩
      change e ∉ M.closure ∅
      simpa only [flatBottom] using hebot
    have hle : flatClosure M {e} ≤ F := by
      exact (M.closure_subset_closure (singleton_subset_iff.mpr heF)).trans_eq F.2.closure
    exact ⟨e, he, ((hF.le_iff_eq (nonloopFlatAtom M he).ne_bot).mp hle).symm⟩
  · rintro ⟨e, he, rfl⟩
    exact nonloopFlatAtom M he

theorem flatJoinNonloops (M : _root_.Matroid α) [M.Finite] (F : Flat M) :
    sSup {A : Flat M | ∃ e ∈ F.1, M.IsNonloop e ∧ A = flatClosure M {e}} = F := by
  let S : Set (Flat M) := {A | ∃ e ∈ F.1, M.IsNonloop e ∧ A = flatClosure M {e}}
  change sSup S = F
  apply le_antisymm
  · apply sSup_le
    rintro A ⟨e, heF, _, rfl⟩
    exact (M.closure_subset_closure (singleton_subset_iff.mpr heF)).trans_eq F.2.closure
  · intro e heF
    by_cases he : M.IsLoop e
    · exact he.mem_of_isFlat (sSup S).2
    · have hn := M.isNonloop_of_not_isLoop (F.2.subset_ground heF) he
      have hmem : flatClosure M {e} ∈ S := ⟨e, heF, hn, rfl⟩
      exact (show (flatClosure M {e}).1 ⊆ (sSup S).1 from le_sSup hmem)
        (M.mem_closure_of_mem' (mem_singleton e) hn.mem_ground)

theorem flatAtomistic (M : _root_.Matroid α) [M.Finite] (F : Flat M) :
    sSup {A : Flat M | IsAtom A ∧ A ≤ F} = F := by
  apply le_antisymm
  · exact sSup_le fun A h => h.2
  · calc
      F = sSup {A : Flat M | ∃ e ∈ F.1, M.IsNonloop e ∧ A = flatClosure M {e}} :=
        (flatJoinNonloops M F).symm
      _ ≤ sSup {A : Flat M | IsAtom A ∧ A ≤ F} := by
        apply sSup_le
        rintro A ⟨e, heF, he, rfl⟩
        apply le_sSup
        exact ⟨nonloopFlatAtom M he,
          (M.closure_subset_closure (singleton_subset_iff.mpr heF)).trans_eq F.2.closure⟩

theorem flatSemimodular (M : _root_.Matroid α) [M.Finite] (F G : Flat M)
    (h : (F ⊓ G) ⋖ F) : G ⋖ (F ⊔ G) := by
  have hr := ((flatCoverRank M (F ⊓ G) F).mp h).2
  have hs := rankSubmodular M F.1 G.1 F.2.subset_ground G.2.subset_ground
  rw [← flatMeet M F G] at hs
  have hj : rank M (F ⊔ G).1 = rank M (F.1 ∪ G.1) := by
    rw [flatJoin, rankClosure]
  have hlt : G < F ⊔ G := by
    apply lt_of_le_of_ne le_sup_right
    intro heq
    have hFG : F ≤ G := heq ▸ (show F ≤ F ⊔ G from le_sup_left)
    have heq' : F ⊓ G = F := inf_eq_left.mpr hFG
    exact h.lt.ne heq'
  have hstrict := flatRankStrict M hlt
  apply (flatCoverRank M G (F ⊔ G)).mpr
  exact ⟨hlt, by omega⟩

theorem flatGeometric (M : _root_.Matroid α) [M.Finite] :
    GeometricLattice (Flat M) :=
  ⟨flatFinite M, flatAtomistic M, flatSemimodular M⟩

end FiniteCombinatorics.Matroid
