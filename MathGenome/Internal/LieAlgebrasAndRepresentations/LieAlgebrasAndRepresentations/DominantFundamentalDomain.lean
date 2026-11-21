import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.DominantFundamentalDomain
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeylChambersLength
import Mathlib.Analysis.Convex.Topology

/-! The fundamental domain assertion of res:E03. Reduced-word prefixes take
 the next simple root to a positive root. Telescoping along such a word proves
 the dominant difference assertion. The simple-root basis makes its cone
 pointed. Maximizing on a finite orbit also handles all chamber walls. -/
noncomputable section
namespace LieAlgebrasAndRepresentations
open Set Module
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma simpleRootCone_zero (R : Set E) (v : E) : (0 : E) ∈ simpleRootCone R v :=
  ⟨0, by simp, by simp⟩

lemma simpleRootCone_add {R : Set E} {v x y : E}
    (hx : x ∈ simpleRootCone R v) (hy : y ∈ simpleRootCone R v) :
    x + y ∈ simpleRootCone R v := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  exact ⟨c + d, fun i => add_nonneg (hc i) (hd i), by simp⟩

lemma simpleRootCone_smul {R : Set E} {v x : E} {t : ℝ}
    (ht : 0 ≤ t) (hx : x ∈ simpleRootCone R v) : t • x ∈ simpleRootCone R v := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨t • c, fun i => mul_nonneg ht (hc i), by simp⟩

lemma positive_mem_simpleRootCone {R : Set E} (hR : RootAxioms R) {v a : E}
    (ha : a ∈ positiveRoots R v) : a ∈ simpleRootCone R v := by
  classical
  refine AddSubmonoid.closure_induction (fun x hx => ?_) (simpleRootCone_zero R v)
    (fun x y hx hy ihx ihy => simpleRootCone_add ihx ihy)
    (positive_mem_closure_simple hR v ha)
  exact ⟨Finsupp.single ⟨x, hx⟩ 1, fun i => by
    simp only [Finsupp.single_apply]; split_ifs <;> norm_num, by simp⟩

lemma simpleRootCone_coords {R : Set E} {v x : E}
    (b : Basis (simpleRoots R v) ℝ E) (hb : ∀ i, b i = (i : E))
    (hx : x ∈ simpleRootCone R v) : ∀ i, 0 ≤ b.repr x i := by
  obtain ⟨c, hc, he⟩ := hx
  have hfun : (fun i : simpleRoots R v => (i : E)) = b := funext (fun i => (hb i).symm)
  rw [hfun] at he
  rw [← he, b.repr_linearCombination]
  exact hc

lemma simpleRootCone_pointed {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ simpleRootCone R v)
    (hn : -x ∈ simpleRootCone R v) : x = 0 := by
  obtain ⟨b, hb⟩ := simpleRoots_basis R hR v hv
  have hp := simpleRootCone_coords b hb hx
  have hm := simpleRootCone_coords b hb hn
  apply b.repr.injective
  ext i
  have hi := hm i
  simp only [map_neg, Finsupp.neg_apply] at hi
  simpa using le_antisymm (neg_nonneg.mp hi) (hp i)

/-- Prefix positivity follows from deletion and minimality. -/
lemma shortest_append_positive {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) (l : List (simpleRoots R v)) (i : simpleRoots R v)
    (hmin : ∀ k : List (simpleRoots R v),
      weylWordProduct k = weylWordProduct (l ++ [i]) → (l ++ [i]).length ≤ k.length) :
    weylWordProduct l (i : E) ∈ positiveRoots R v := by
  have hr := (rootWeylGroup_mem_iff hR.toRootAxioms (weylWordProduct_mem l) _).mp i.property.1.1
  refine ⟨hr, ?_⟩
  rcases lt_or_gt_of_ne (hv _ hr) with hn | hp
  · obtain ⟨k, hk, hlen⟩ := weyl_word_deletion hR hv l i.property.1 hn
    have hm := hmin k (by simpa [weylWordProduct] using hk)
    simp only [List.length_append, List.length_singleton] at hm
    omega
  · exact hp

lemma shortest_word_dominant_difference {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ closedSimpleChamber R v)
    (l : List (simpleRoots R v))
    (hmin : ∀ k : List (simpleRoots R v), weylWordProduct k = weylWordProduct l →
      l.length ≤ k.length) : x - weylWordProduct l x ∈ simpleRootCone R v := by
  induction l using List.reverseRecOn with
  | nil => simpa using simpleRootCone_zero R v
  | append_singleton l i ih =>
    have hminl : ∀ k : List (simpleRoots R v), weylWordProduct k = weylWordProduct l →
        l.length ≤ k.length := by
      intro k hk
      have hm := hmin (k ++ [i]) (by simp [hk])
      simpa using hm
    have hp := shortest_append_positive hR hv l i hmin
    have ht : 0 ≤ 2 * inner ℝ x (i : E) / inner ℝ (i : E) (i : E) :=
      div_nonneg (mul_nonneg (by norm_num) (hx i i.property)) (real_inner_self_nonneg)
    have hc := simpleRootCone_smul ht (positive_mem_simpleRootCone hR.toRootAxioms hp)
    have he : x - weylWordProduct (l ++ [i]) x =
        (x - weylWordProduct l x) +
        (2 * inner ℝ x (i : E) / inner ℝ (i : E) (i : E)) • weylWordProduct l (i : E) := by
      simp only [weylWordProduct_append, weylWordProduct_cons, weylWordProduct_nil,
        mul_one, LinearEquiv.mul_apply, rootReflectionEquiv_apply, rootReflection,
        map_sub, map_smul]
      abel
    rw [he]
    exact simpleRootCone_add (ih hminl) hc

theorem dominant_weyl_difference : DominantFundamentalDomainSpecs.dominantDifferenceType := by
  intro E _ _ R hR v hv x hx w
  obtain ⟨l, hl, _, hmin⟩ := weyl_shortest_word R hR v hv w
  rw [← hl]
  exact shortest_word_dominant_difference hR hv hx l (fun k hk => hmin k (hk.trans hl))

/-- The inequalities describe the actual topological closure, including walls. -/
theorem closedSimpleChamber_eq_closure : DominantFundamentalDomainSpecs.closureType := by
  intro E _ _ R _hR v _hv
  apply Subset.antisymm
  · intro x hx a ha
    have hc : IsClosed {y : E | 0 ≤ inner ℝ y a} :=
      isClosed_le continuous_const (continuous_id.inner continuous_const)
    exact closure_minimal (fun y hy => (hy a ha).le) hc hx
  · intro x hx
    apply closure_mono (s := openSegment ℝ x v) ?_
      (segment_subset_closure_openSegment (left_mem_segment ℝ x v))
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    intro i hi
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (hx i hi)) (mul_pos hb hi.1.2)

/-- Maximization does not require the orbit vector to be regular. -/
lemma exists_weyl_into_closedSimpleChamber {R : Set E} (hR : IsRootSystem R)
    (v x : E) : ∃ w : rootWeylGroup R, w.val x ∈ closedSimpleChamber R v := by
  haveI := rootWeylGroup_finite hR
  obtain ⟨w, hw⟩ := (Set.finite_univ : (Set.univ : Set (rootWeylGroup R)).Finite).exists_maximalFor
    (fun w : rootWeylGroup R => inner ℝ v (w.val x)) Set.univ ⟨1, trivial⟩
  refine ⟨w, ?_⟩
  intro a ha
  by_contra! hn
  let s : rootWeylGroup R :=
    ⟨rootReflectionEquiv a, simpleWeylGroup_le R v (simple_reflection_mem ha)⟩
  have hcart : 2 * inner ℝ (w.val x) a / inner ℝ a a < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg two_pos hn)
      (real_inner_self_pos.mpr (hR.nonzero a ha.1.1))
  have hlt : inner ℝ v (w.val x) < inner ℝ v ((s * w).val x) := by
    change inner ℝ v (w.val x) < inner ℝ v (rootReflectionEquiv a (w.val x))
    rw [rootReflectionEquiv_apply, rootReflection, inner_sub_right, real_inner_smul_right]
    linarith [mul_neg_of_neg_of_pos hcart ha.1.2]
  exact not_le_of_gt hlt (hw.2 (show s * w ∈ (Set.univ : Set (rootWeylGroup R)) from trivial) hlt.le)

lemma dominant_weyl_eq {R : Set E} (hR : IsRootSystem R) {v : E}
    (hv : RootRegular R v) {x : E} (hx : x ∈ closedSimpleChamber R v)
    (w : rootWeylGroup R) (hw : w.val x ∈ closedSimpleChamber R v) : w.val x = x := by
  have hp := dominant_weyl_difference R hR v hv x hx w
  have hn := dominant_weyl_difference R hR v hv (w.val x) hw w⁻¹
  have hcancel : w⁻¹.val (w.val x) = x := w.val.symm_apply_apply x
  rw [hcancel] at hn
  have he := simpleRootCone_pointed hR hv hp (by simpa only [neg_sub] using hn)
  exact (sub_eq_zero.mp he).symm

theorem weyl_closed_chamber_fundamental_domain : DominantFundamentalDomainSpecs.fundamentalDomainType := by
  intro E _ _ R hR v hv x
  obtain ⟨w, hw⟩ := exists_weyl_into_closedSimpleChamber hR v x
  refine ⟨w.val x, ⟨hw, w, rfl⟩, ?_⟩
  rintro y ⟨hy, z, rfl⟩
  have he : (z * w⁻¹).val (w.val x) = z.val x := by
    change z.val (w.val.symm (w.val x)) = z.val x
    rw [LinearEquiv.symm_apply_apply]
  have hu := dominant_weyl_eq hR hv hw (z * w⁻¹) (he.symm ▸ hy)
  rwa [he] at hu

end LieAlgebrasAndRepresentations
