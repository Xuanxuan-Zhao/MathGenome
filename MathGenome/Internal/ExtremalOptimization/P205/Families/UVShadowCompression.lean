import MathGenome.Internal.ExtremalOptimization.Specs.P205.Families.UVShadowCompression

/-! UV-compression and the shadow inclusion of Lemma 2.6 of paper.tex.
The canonical Mathlib compression retains a member when its compressed image is
already present, and otherwise replaces it. Closure is stated using the paper's
replacement `(A \ V) ∪ U`, and is proved equivalent to invariance. -/
namespace P205.Families.UV

variable {α : Type*} [DecidableEq α]

/-- The canonical cardinality-preserving UV-compression of a family. -/
def compression (U V : Finset α) (F : Finset (Finset α)) : Finset (Finset α) :=
  _root_.UV.compression U V F

/-- A family contains the replacement of each movable member. -/
def IsClosed (U V : Finset α) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, Disjoint U A → V ⊆ A → (A \ V) ∪ U ∈ F

theorem movable_replacement (U V A : Finset α) (hUA : Disjoint U A) (hVA : V ⊆ A) :
    _root_.UV.compress U V A = (A \ V) ∪ U := by
  rw [_root_.UV.compress_of_disjoint_of_le hUA hVA]
  change (A ∪ U) \ V = (A \ V) ∪ U
  rw [Finset.union_sdiff_distrib, (hUA.mono_right hVA).sdiff_eq_left]

theorem replacement_inverse (U V A : Finset α) (hUA : Disjoint U A) (hVA : V ⊆ A) :
    (((A \ V) ∪ U) \ U) ∪ V = A := by
  rw [Finset.union_sdiff_distrib, Finset.sdiff_self, Finset.union_empty,
    (hUA.symm.mono_left Finset.sdiff_subset).sdiff_eq_left,
    Finset.sdiff_union_of_subset hVA]

theorem closed_iff_invariant (U V : Finset α) (F : Finset (Finset α)) :
    IsClosed U V F ↔ compression U V F = F := by
  have bridge : IsClosed U V F ↔ ∀ A ∈ F, _root_.UV.compress U V A ∈ F := by
    constructor
    · intro h A hA
      by_cases hm : Disjoint U A ∧ V ⊆ A
      · rw [movable_replacement U V A hm.1 hm.2]
        exact h A hA hm.1 hm.2
      · simpa [_root_.UV.compress, hm] using hA
    · intro h A hA hUA hVA
      rw [← movable_replacement U V A hUA hVA]
      exact h A hA
  rw [bridge]
  constructor
  · intro h
    apply Finset.ext
    intro A
    change A ∈ _root_.UV.compression U V F ↔ A ∈ F
    rw [_root_.UV.mem_compression]
    constructor
    · rintro (⟨hA, _⟩ | ⟨_, B, hB, rfl⟩)
      · exact hA
      · exact h B hB
    · intro hA
      exact Or.inl ⟨hA, h A hA⟩
  · intro h A hA
    have hm := _root_.UV.compress_mem_compression (u := U) (v := V) hA
    change _root_.UV.compression U V F = F at h
    rwa [h] at hm

theorem closed_empty (F : Finset (Finset α)) : IsClosed ∅ ∅ F := by
  intro A hA _ _
  simpa using hA

theorem card_compression (U V : Finset α) (F : Finset (Finset α)) :
    (compression U V F).card = F.card :=
  _root_.UV.card_compression U V F

theorem rank_compression (U V : Finset α) (F : Finset (Finset α)) (k : ℕ)
    (hUV : U.card = V.card) (hF : ∀ A ∈ F, A.card = k) :
    ∀ A ∈ compression U V F, A.card = k := by
  exact Set.Sized.uvCompression hUV hF

theorem shadow_subset (U V : Finset α) (F : Finset (Finset α))
    (_hdisj : Disjoint U V) (_hU : U.Nonempty) (_hV : V.Nonempty)
    (_hcard : U.card = V.card)
    (hsmall : ∀ x ∈ U, ∃ y ∈ V, IsClosed (U.erase x) (V.erase y) F) :
    (compression U V F).shadow ⊆ compression U V F.shadow := by
  apply _root_.UV.shadow_compression_subset_compression_shadow
  intro x hx
  obtain ⟨y, hy, hclosed⟩ := hsmall x hx
  exact ⟨y, hy, (closed_iff_invariant _ _ _).mp hclosed⟩

theorem shadow_card_le (U V : Finset α) (F : Finset (Finset α))
    (hdisj : Disjoint U V) (hU : U.Nonempty) (hV : V.Nonempty)
    (hcard : U.card = V.card)
    (hsmall : ∀ x ∈ U, ∃ y ∈ V, IsClosed (U.erase x) (V.erase y) F) :
    (compression U V F).shadow.card ≤ F.shadow.card := by
  calc
    (compression U V F).shadow.card ≤ (compression U V F.shadow).card :=
      Finset.card_le_card (shadow_subset U V F hdisj hU hV hcard hsmall)
    _ = F.shadow.card := card_compression U V F.shadow

end P205.Families.UV
