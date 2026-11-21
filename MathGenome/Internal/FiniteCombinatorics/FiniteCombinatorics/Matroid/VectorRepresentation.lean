import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.VectorRepresentation

/-! The vector matroid of paper.tex W70, on its original index ground.
The construction uses finite augmentation; vector values are never used as indices.
-/
namespace FiniteCombinatorics.Matroid
open Set Submodule
universe u v w
variable {α : Type u}

def vectorMatroid (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) : _root_.Matroid α :=
  ofAugmentation (vectorSystem K E hE v) (vectorSystem_augmentation E hE v)

instance (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (E : Set α) (hE : E.Finite) (v : α → V) : (vectorMatroid K E hE v).Finite := ⟨hE⟩

def Represents (K : Type v) [Field K] {V : Type w} [AddCommGroup V] [Module K V]
    (M : _root_.Matroid α) (v : α → V) : Prop :=
  ∀ I, M.Indep I ↔ I ⊆ M.E ∧ LinearIndepOn K v I

def Representable (K : Type v) [Field K] (M : _root_.Matroid α) : Prop :=
  ∃ (V : Type w) (_ : AddCommGroup V) (_ : Module K V) (v : α → V), Represents K M v

theorem vectorGround : Expected.vectorGround := by
  intro α K _ V _ _ E hE v
  rfl

theorem vectorFinite : Expected.vectorFinite := by
  intro α K _ V _ _ E hE v
  infer_instance

theorem vectorIndep : Expected.vectorIndep := by
  intro α K _ V _ _ E hE v I
  rfl

theorem vectorSpanFinite : Expected.vectorSpanFinite := by
  intro α K _ V _ _ E hE v A hA
  exact Module.Finite.span_of_finite K ((hE.subset hA).image v)

/-- Maximality forces the chosen independent subfamily to span every column. -/
theorem vectorRank : Expected.vectorRank := by
  intro α K _ V _ _ E hE v A hA
  let M := vectorMatroid K E hE v
  obtain ⟨B, hB⟩ := M.exists_isBasis A hA
  have hi : B ⊆ E ∧ LinearIndepOn K v B := hB.indep
  have hspan : span K (v '' A) = span K (v '' B) := by
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨e, he, rfl⟩
      by_contra hn
      have hins : M.Indep (insert e B) :=
        ⟨insert_subset (hA he) hi.1, hi.2.insert hn⟩
      exact hn (subset_span ⟨e, hB.mem_of_insert_indep he hins, rfl⟩)
    · exact span_mono (image_mono hB.subset)
  change ((M.eRk A).toNat : ℤ) = _
  rw [hB.eRk_eq_encard, hspan, linearIndepOn_finrank_image (hE.subset hi.1) hi.2]
  rfl

theorem vectorZeroLoop : Expected.vectorZeroLoop := by
  intro α K _ V _ _ E hE v e he
  rw [← _root_.Matroid.singleton_not_indep (show e ∈ (Expected.vectorMatroid K E hE v).E from he),
    vectorIndep]
  simp [singleton_subset_iff, he, linearIndepOn_singleton_iff]

theorem vectorProportionalDependent : Expected.vectorProportionalDependent := by
  intro α K _ V _ _ E hE v e f he hf hne c hval
  rw [_root_.Matroid.dep_iff]
  refine ⟨?_, pair_subset he hf⟩
  intro hi
  have hli := (vectorIndep K E hE v {e, f}).mp hi |>.2
  apply hli.notMem_span (by simp : f ∈ ({e, f} : Set α))
  rw [hval]
  exact (span K (v '' ({e, f} \ {f}))).smul_mem c
    (subset_span ⟨e, by simp [hne], rfl⟩)

theorem vectorRepeatedDependent : Expected.vectorRepeatedDependent := by
  intro α K _ V _ _ E hE v e f he hf hne hval
  exact vectorProportionalDependent K E hE v e f he hf hne 1 (by simpa using hval.symm)

theorem vectorRepresents : Expected.vectorRepresents := by
  intro α K _ V _ _ E hE v I
  exact vectorIndep K E hE v I

theorem represents_iff_vectorMatroid : Expected.represents_iff_vectorMatroid := by
  intro α K _ V _ _ M _ v
  constructor
  · intro h
    exact _root_.Matroid.ext_indep rfl (fun I _ => (h I).trans (vectorIndep K M.E M.ground_finite v I).symm)
  · intro h I
    rw [h]
    exact vectorIndep K M.E M.ground_finite v I

theorem representsRank : Expected.representsRank := by
  intro α K _ V _ _ M _ v hv A hA
  have heq := (represents_iff_vectorMatroid K M v).mp hv
  have hr := vectorRank K M.E M.ground_finite v A hA
  change (((Expected.vectorMatroid K M.E M.ground_finite v).eRk A).toNat : ℤ) = _ at hr
  rw [← heq] at hr
  exact hr

theorem vectorRepresentable : Expected.vectorRepresentable := by
  intro α K _ V _ _ E hE v
  exact ⟨V, inferInstance, inferInstance, v, vectorRepresents K E hE v⟩

end FiniteCombinatorics.Matroid
