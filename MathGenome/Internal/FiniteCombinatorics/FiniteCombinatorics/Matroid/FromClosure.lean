import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.FromClosure

namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u} {E : Set α} {c : Set α → Set α}

namespace ClosurePresentation

lemma independent_subset (hc : ClosurePresentation E c) {I J : Set α}
    (hJ : ClosureIndependent E c J) (hIJ : I ⊆ J) : ClosureIndependent E c I := by
  refine ⟨hIJ.trans hJ.1, fun e he h => hJ.2 e (hIJ he) ?_⟩
  exact hc.2.2.1 _ (sdiff_subset.trans (hIJ.trans hJ.1)) _
    (sdiff_subset.trans hJ.1) (sdiff_subset_sdiff_left hIJ) h

lemma independent_insert (hc : ClosurePresentation E c) {I : Set α}
    (hI : ClosureIndependent E c I) {x : α} (hxE : x ∈ E) (hx : x ∉ c I) :
    ClosureIndependent E c (insert x I) := by
  have hxI : x ∉ I := fun h => hx (hc.2.1 I hI.1 h)
  refine ⟨insert_subset hxE hI.1, ?_⟩
  intro y hy hycl
  rcases hy with rfl | hyI
  · apply hx
    exact hc.2.2.1 _ (sdiff_subset.trans (insert_subset hxE hI.1)) _ hI.1
      (by simp [hxI]) hycl
  · have hyx : y ≠ x := fun h => hxI (h ▸ hyI)
    have hdel : (insert x I) \ {y} = insert x (I \ {y}) := by
      ext z
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff]
      constructor <;> aesop
    rw [hdel] at hycl
    have hx' := hc.2.2.2.2 (I \ {y}) (sdiff_subset.trans hI.1) x hxE y (hI.1 hyI)
      ⟨hycl, hI.2 y hyI⟩
    apply hx
    simpa [insert_sdiff_singleton, insert_eq_of_mem hyI] using hx'

lemma closure_mono_of_subset_closure (hc : ClosurePresentation E c)
    {A B : Set α} (hA : A ⊆ E) (hB : B ⊆ E) (hAB : A ⊆ c B) : c A ⊆ c B := by
  have h := hc.2.2.1 A hA (c B) (hc.1 B hB) hAB
  rwa [hc.2.2.2.1 B hB] at h

/-- A maximal independent set spans E. This uses only the extension test. -/
lemma maximal_spans (hc : ClosurePresentation E c) {B : Set α}
    (hB : Maximal (ClosureIndependent E c) B) : E ⊆ c B := by
  intro x hxE
  by_contra hx
  have hi := hc.independent_insert hB.1 hxE hx
  have hsub := hB.2 hi (subset_insert x B)
  exact hx (hc.2.1 B hB.1.1 (hsub (mem_insert x B)))

/-- Conversely, a spanning independent set is maximal. -/
lemma maximal_of_spans (hc : ClosurePresentation E c) {I : Set α}
    (hI : ClosureIndependent E c I) (hspan : E ⊆ c I) :
    Maximal (ClosureIndependent E c) I := by
  refine ⟨hI, ?_⟩
  intro J hJ hIJ y hyJ
  by_contra hyI
  exact hJ.2 y hyJ (hc.2.2.1 I hI.1 (J \ {y}) (sdiff_subset.trans hJ.1)
    (by intro z hz; exact ⟨hIJ hz, fun h => hyI (h ▸ hz)⟩) (hspan (hJ.1 hyJ)))

lemma maximal_augmentation (hc : ClosurePresentation E c) {I B : Set α}
    (hI : ClosureIndependent E c I) (hnot : ¬ Maximal (ClosureIndependent E c) I)
    (hB : Maximal (ClosureIndependent E c) B) :
    ∃ x ∈ B \ I, ClosureIndependent E c (insert x I) := by
  classical
  have hBI : ¬ B ⊆ c I := by
    intro h
    exact hnot (hc.maximal_of_spans hI ((hc.maximal_spans hB).trans
      (hc.closure_mono_of_subset_closure hB.1.1 hI.1 h)))
  obtain ⟨x, hxB, hx⟩ := Set.not_subset.mp hBI
  exact ⟨x, ⟨hxB, fun h => hx (hc.2.1 I hI.1 h)⟩,
    hc.independent_insert hI (hB.1.1 hxB) hx⟩

end ClosurePresentation

/-- The hereditary system specified by the source's closure test. -/
def closureSystem (hE : E.Finite) (c : Set α → Set α) (hc : ClosurePresentation E c) :
    IndependenceSystem E where
  finite_ground := hE
  Indep := ClosureIndependent E c
  empty_indep := ⟨empty_subset E, by simp⟩
  hereditary := fun {_ _} h hsub => hc.independent_subset h hsub
  subset_ground := fun {_} h => h.1

/-- An intermediate matroid using maximal-set augmentation. Its size bound is only
that every independent set is a subset of E; no closure cardinal bound is assumed. -/
private def closureAux (hE : E.Finite) (hc : ClosurePresentation E c) : _root_.Matroid α :=
  (IndepMatroid.ofBdd E (ClosureIndependent E c)
    ⟨empty_subset E, by simp⟩ (fun {_ _} h hsub => hc.independent_subset h hsub)
    (fun {_ _} h hn hb => hc.maximal_augmentation h hn hb)
    (fun _ h => h.1) ⟨E.ncard, fun I h => by
      rw [hE.cast_ncard_eq]
      exact encard_mono h.1⟩).matroid

theorem closureAugmentation : Expected.closureAugmentation.{u} := by
  intro α E hE c hc I J hI hJ hlt
  change ClosurePresentation E c at hc
  change ClosureIndependent E c I at hI
  change ClosureIndependent E c J at hJ
  have hIe : (closureAux hE hc).Indep I := hI
  have hJe : (closureAux hE hc).Indep J := hJ
  apply hIe.exists_insert_of_encard_lt hJe
  rw [← (hE.subset hI.1).cast_ncard_eq, ← (hE.subset hJ.1).cast_ncard_eq]
  exact_mod_cast hlt

/-- The final construction uses the shared canonical augmentation constructor. -/
def ofClosure (hE : E.Finite) (c : Set α → Set α) (hc : ClosurePresentation E c) :
    _root_.Matroid α :=
  ofAugmentation (closureSystem hE c hc) (by
    intro I J hI hJ hlt
    exact closureAugmentation E hE c hc I J hI hJ hlt)

instance (hE : E.Finite) (hc : ClosurePresentation E c) : (ofClosure hE c hc).Finite :=
  finiteConstruction E _ _

@[simp] theorem ofClosure_ground (hE : E.Finite) (hc : ClosurePresentation E c) :
    (ofClosure hE c hc).E = E := rfl

@[simp] theorem ofClosure_indep (hE : E.Finite) (hc : ClosurePresentation E c) (I : Set α) :
    (ofClosure hE c hc).Indep I ↔ ClosureIndependent E c I := Iff.rfl

/-- On an independent set, both closure functions have the same insertion test. -/
lemma ofClosure_closure_of_indep (hE : E.Finite) (hc : ClosurePresentation E c)
    {I : Set α} (hI : ClosureIndependent E c I) :
    (ofClosure hE c hc).closure I = c I := by
  have hIM : (ofClosure hE c hc).Indep I := hI
  ext x
  constructor
  · intro hx
    by_contra hxc
    have hxE : x ∈ E := (ofClosure hE c hc).closure_subset_ground I hx
    have hins : (ofClosure hE c hc).Indep (insert x I) :=
      hc.independent_insert hI hxE hxc
    exact hxc (hc.2.1 I hI.1 ((hIM.mem_closure_iff'.mp hx).2 hins))
  · intro hxc
    by_contra hx
    have hxE : x ∈ (ofClosure hE c hc).E := hc.1 I hI.1 hxc
    obtain ⟨hins, hxI⟩ := (hIM.notMem_closure_iff hxE).mp hx
    have htest := (ofClosure_indep hE hc _).mp hins
    have hnot := htest.2 x (mem_insert x I)
    have hdel : insert x I \ {x} = I := by ext y; simp; aesop
    rw [hdel] at hnot
    exact hnot hxc

/-- Recovery of the supplied closure on its complete domain 2^E. -/
theorem ofClosure_closure (hE : E.Finite) (hc : ClosurePresentation E c)
    (A : Set α) (hA : A ⊆ E) : (ofClosure hE c hc).closure A = c A := by
  obtain ⟨I, hIA⟩ := (ofClosure hE c hc).exists_isBasis A hA
  have hI : ClosureIndependent E c I := hIA.indep
  have hcl := ofClosure_closure_of_indep hE hc hI
  have hAI : A ⊆ c I := by rw [← hcl]; exact hIA.subset_closure
  have hIcA : c I = c A := subset_antisymm
    (hc.2.2.1 I hI.1 A hA hIA.subset)
    (hc.closure_mono_of_subset_closure hA hI.1 hAI)
  exact hIA.closure_eq_closure.symm.trans (hcl.trans hIcA)

theorem closureRealization : Expected.closureRealization.{u} := by
  intro α E hE c hc
  exact ⟨ofClosure hE c hc, rfl, ⟨hE⟩,
    ofClosure_indep hE hc, ofClosure_closure hE hc⟩

end FiniteCombinatorics.Matroid
