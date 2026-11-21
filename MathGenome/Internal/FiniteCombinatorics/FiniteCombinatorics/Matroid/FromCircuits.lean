import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FromCircuits
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α} {C : Set (Set α)}

private lemma circuit_contains_inserted {I D : Set α} {x : α}
    (hI : CircuitIndependent E C I) (hD : D ∈ C) (hDI : D ⊆ insert x I) : x ∈ D := by
  by_contra hx
  exact hI.2 D hD (by intro z hz; exact (hDI hz).resolve_left (by aesop))

private lemma circuit_unique (hC : CircuitPresentation E C) {I D F : Set α} {x : α}
    (hI : CircuitIndependent E C I) (hD : D ∈ C) (hF : F ∈ C)
    (hDI : D ⊆ insert x I) (hFI : F ⊆ insert x I) : D = F := by
  by_contra hne
  obtain ⟨K, hK, hKI⟩ := hC.2.2 D hD F hF hne x
    ⟨circuit_contains_inserted hI hD hDI, circuit_contains_inserted hI hF hFI⟩
  exact hI.2 K hK (by
    intro z hz
    have h := hKI hz
    exact (h.1.elim (fun hz => hDI hz) (fun hz => hFI hz)).resolve_left (by simpa using h.2))

private lemma circuit_swap (hC : CircuitPresentation E C) {I D : Set α} {x y : α}
    (hI : CircuitIndependent E C I) (hxE : x ∈ E) (hD : D ∈ C)
    (hDI : D ⊆ insert x I) (hyD : y ∈ D) (hyx : y ≠ x) :
    CircuitIndependent E C (insert x (I \ {y})) := by
  refine ⟨by intro z hz; rcases hz with rfl | hz; exact hxE; exact hI.1 hz.1, ?_⟩
  intro F hF hFK
  have hFD := circuit_unique hC hI hF hD
    (hFK.trans (by intro z hz; aesop)) hDI
  subst F
  have := hFK hyD
  aesop

/-- Saturation is maximality expressed through one-element extensions. -/
private def Saturated (E : Set α) (C : Set (Set α)) (A I : Set α) : Prop :=
  I ⊆ A ∧ CircuitIndependent E C I ∧
    ∀ x ∈ A \ I, ¬ CircuitIndependent E C (insert x I)

private lemma exists_circuit_of_not_indep {I : Set α}
    (hIE : I ⊆ E) (hI : ¬ CircuitIndependent E C I) : ∃ D ∈ C, D ⊆ I := by
  classical
  by_contra h
  exact hI ⟨hIE, fun D hD hDI => h ⟨D, hD, hDI⟩⟩

private lemma saturated_swap (hC : CircuitPresentation E C) {A I D : Set α} {x y : α}
    (hAE : A ⊆ E) (hI : Saturated E C A I) (hx : x ∈ A \ I)
    (hD : D ∈ C) (hDI : D ⊆ insert x I) (hyD : y ∈ D) (hyx : y ≠ x) :
    Saturated E C A (insert x (I \ {y})) := by
  classical
  have hyI : y ∈ I := (hDI hyD).resolve_left hyx
  have hxD := circuit_contains_inserted hI.2.1 hD hDI
  refine ⟨by intro z hz; rcases hz with rfl | hz; exact hx.1; exact hI.1 hz.1,
    circuit_swap hC hI.2.1 (hAE hx.1) hD hDI hyD hyx, ?_⟩
  intro z hz hKz
  by_cases hzy : z = y
  · subst z
    exact hKz.2 D hD (by
      intro a ha
      by_cases hay : a = y
      · exact Or.inl hay
      · exact Or.inr ((hDI ha).imp_right (fun h => ⟨h, by simpa using hay⟩)))
  have hzI : z ∉ I := by intro hzI; exact hz.2 (Or.inr ⟨hzI, by simpa using hzy⟩)
  have hzx : z ≠ x := by intro h; subst z; exact hz.2 (mem_insert _ _)
  obtain ⟨F, hF, hFI⟩ := exists_circuit_of_not_indep
    (insert_subset (hAE hz.1) hI.2.1.1) (hI.2.2 z ⟨hz.1, hzI⟩)
  by_cases hyF : y ∈ F
  · have hDF : D ≠ F := by
      intro heq
      have := hFI (heq ▸ hxD)
      exact this.elim (fun h => hzx h.symm) hx.2
    obtain ⟨G, hG, hGF⟩ := hC.2.2 D hD F hF hDF y ⟨hyD, hyF⟩
    exact hKz.2 G hG (by
      intro a ha
      have h := hGF ha
      have ha' : a ∈ insert x I ∨ a ∈ insert z I := h.1.imp (fun ha => hDI ha) (fun ha => hFI ha)
      rcases ha' with (rfl | ha') | (rfl | ha')
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨ha', h.2⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨ha', h.2⟩))
  · exact hKz.2 F hF (by intro a ha; have := hFI ha; aesop)

/-- Exchange toward `J`, preserving saturation and cardinality. Each step strictly
reduces `J \ I`; when `J ⊆ I`, the desired cardinal bound is immediate. -/
private lemma saturated_card_le (hC : CircuitPresentation E C) (hE : E.Finite)
    {A I J : Set α} (hAE : A ⊆ E) (hI : Saturated E C A I)
    (hJ : CircuitIndependent E C J) (hJA : J ⊆ A) : J.ncard ≤ I.ncard := by
  classical
  suffices ∀ n, ∀ I : Set α, (J \ I).ncard = n → Saturated E C A I →
      J.ncard ≤ I.ncard from this _ I rfl hI
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I hn hI
    by_cases hJI : J ⊆ I
    · exact ncard_le_ncard hJI (hE.subset hI.2.1.1)
    obtain ⟨x, hxJ, hxI⟩ := not_subset.mp hJI
    obtain ⟨D, hD, hDI⟩ := exists_circuit_of_not_indep
      (insert_subset (hJ.1 hxJ) hI.2.1.1) (hI.2.2 x ⟨hJA hxJ, hxI⟩)
    obtain ⟨y, hyD, hyJ⟩ := not_subset.mp (hJ.2 D hD)
    have hyx : y ≠ x := by rintro rfl; exact hyJ hxJ
    have hyI : y ∈ I := (hDI hyD).resolve_left hyx
    have hK := saturated_swap hC hAE hI ⟨hJA hxJ, hxI⟩ hD hDI hyD hyx
    have hdiff : J \ insert x (I \ {y}) = (J \ I) \ {x} := by
      ext a
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨haJ, haK⟩
        exact ⟨⟨haJ, fun haI => haK (Or.inr ⟨haI, fun hay => hyJ (hay ▸ haJ)⟩)⟩,
          fun hax => haK (Or.inl hax)⟩
      · rintro ⟨⟨haJ, haI⟩, hax⟩
        exact ⟨haJ, fun h => h.elim hax (fun h => haI h.1)⟩
    have hlt : (J \ insert x (I \ {y})).ncard < n := by
      rw [hdiff, ← hn]
      exact ncard_sdiff_singleton_lt_of_mem ⟨hxJ, hxI⟩ (hE.subset hJ.1).sdiff
    have hle := ih _ hlt _ rfl hK
    rwa [ncard_exchange hxI hyI] at hle

/-- Circuit elimination implies augmentation, including the empty-family case. -/
theorem circuitAugmentation : Expected.circuitAugmentation.{u} := by
  intro α E hE C hC
  change CircuitPresentation E C at hC
  intro I J hI hJ hcard
  change CircuitIndependent E C I at hI
  change CircuitIndependent E C J at hJ
  classical
  by_contra h
  have hno : ∀ x ∈ J \ I, ¬ CircuitIndependent E C (insert x I) := by
    intro x hx hi
    exact h ⟨x, hx, hi⟩
  have hsat : Saturated E C (I ∪ J) I := by
    refine ⟨subset_union_left, hI, ?_⟩
    intro x hx
    exact hno x ⟨hx.1.resolve_left hx.2, hx.2⟩
  exact (not_le_of_gt hcard) (saturated_card_le hC hE (union_subset hI.1 hJ.1)
    hsat hJ subset_union_right)

/-- The circuit axioms construct a finite matroid and recover the designated circuits. -/
theorem matroidFromCircuits : Expected.matroidFromCircuits.{u} := by
  intro α E hE C hC
  let S := circuitSystem E hE C hC
  have haug : Augmentation S := circuitAugmentation E hE C hC
  let M := ofAugmentation S haug
  have hME : M.E = E := rfl
  have hMI : ∀ I, M.Indep I ↔ CircuitIndependent E C I := fun I => Iff.rfl
  change CircuitPresentation E C at hC
  refine ⟨M, hME, inferInstance, hMI, ?_⟩
  intro D
  constructor
  · intro hD
    obtain ⟨F, hF, hFD⟩ := exists_circuit_of_not_indep
      (hME ▸ hD.subset_ground) (fun hi => hD.not_indep ((hMI D).mpr hi))
    have hFn : ¬ M.Indep F := by
      intro hFi
      exact ((hMI F).mp hFi).2 F hF Subset.rfl
    have heq := hD.eq_of_not_indep_subset hFn hFD
    exact heq ▸ hF
  · intro hD
    rw [_root_.Matroid.isCircuit_iff]
    refine ⟨⟨?_, by rw [hME]; exact (hC.1 D hD).1⟩, ?_⟩
    · intro hi
      exact ((hMI D).mp hi).2 D hD Subset.rfl
    · intro F hF hFD
      obtain ⟨K, hK, hKF⟩ := exists_circuit_of_not_indep
        (hME ▸ hF.subset_ground) (fun hi => hF.not_indep ((hMI F).mpr hi))
      have hKD : K = D := hC.2.1 K hK D hD (hKF.trans hFD)
      exact Subset.antisymm hFD (hKD ▸ hKF)

end FiniteCombinatorics.Matroid
