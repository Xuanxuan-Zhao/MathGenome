import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.ImproperExhaustions
import MathGenome.Internal.MultivariableAnalysis.D04.C06.JordanRegions
import MathGenome.Internal.MultivariableAnalysis.D04.C01.DistanceFunction

noncomputable section
open Set Filter Topology
open scoped BigOperators Classical ENNReal
namespace D04.ImproperExhaustions
open Darboux NullCovers DiscontinuityCriterion JordanRegions
abbrev LocallyRiemannIntegrable := @Specs.D04.C06.ImproperExhaustions.Model.LocallyRiemannIntegrable
abbrev CompactJordanSubset := @Specs.D04.C06.ImproperExhaustions.Model.CompactJordanSubset
abbrev absoluteMass := @Specs.D04.C06.ImproperExhaustions.Model.absoluteMass
abbrev AbsolutelyConvergent := @Specs.D04.C06.ImproperExhaustions.Model.AbsolutelyConvergent
abbrev RegularExhaustion := @Specs.D04.C06.ImproperExhaustions.Model.RegularExhaustion
abbrev HasIntegralAlong := @Specs.D04.C06.ImproperExhaustions.Model.HasIntegralAlong
abbrev ConditionalConvergesAlong := @Specs.D04.C06.ImproperExhaustions.Model.ConditionalConvergesAlong

variable {n : ℕ} {Ω C : Set (E n)} {K : ℕ → Set (E n)}

lemma regular_exhaustion_mono (hK : RegularExhaustion Ω K) : Monotone K :=
  monotone_nat_of_le_succ (fun j => (hK.2.1 j).trans interior_subset)

lemma compact_contained_in_exhaustion (hK : RegularExhaustion Ω K)
    {C : Set (E n)} (hC : IsCompact C) (hCΩ : C ⊆ Ω) : ∃ j, C ⊆ K j := by
  obtain ⟨j, hj⟩ := hC.elim_directed_cover (fun j => interior (K j))
    (fun _ => isOpen_interior) (by simpa only [hK.2.2] using hCΩ)
    (Monotone.directed_le (fun _ _ h => interior_mono (regular_exhaustion_mono hK h)))
  exact ⟨j, hj.trans interior_subset⟩

lemma integral_along_unique {f : E n → ℝ} {K : ℕ → Set (E n)} {I J : ℝ}
    (hI : HasIntegralAlong f K I) (hJ : HasIntegralAlong f K J) : I = J :=
  tendsto_nhds_unique hI hJ

/-- A small closed coordinate cube whose interior contains the given point. -/
lemma exists_box_neighborhood (hΩ : IsOpen Ω) {x : E n} (hx : x ∈ Ω) :
    ∃ Q : Box n, x ∈ interior (carrier Q) ∧ carrier Q ⊆ Ω := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  let δ : ℝ := r / ((n : ℝ) + 1)
  have hδ : 0 < δ := div_pos hr (by positivity)
  let Q : Box n := ⟨WithLp.toLp 2 (fun i => x i - δ),
    WithLp.toLp 2 (fun i => x i + δ), fun i => by change x i - δ ≤ x i + δ; linarith⟩
  refine ⟨Q, ?_, ?_⟩
  · rw [interior_carrier]
    intro i
    change x i - δ < x i ∧ x i < x i + δ
    constructor <;> linarith
  · intro y hy
    apply hsub
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖y - x‖ ≤ ∑ i, |(y - x) i| := norm_le_sum_abs _
      _ ≤ ∑ _i : Fin n, δ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := hy i
        change x i - δ ≤ y i ∧ y i ≤ x i + δ at hi
        change |y i - x i| ≤ δ
        exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
      _ < r := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have he : ((n : ℝ) + 1) * δ = r := mul_div_cancel₀ r (by positivity)
        nlinarith

/-- A compact set is covered by the interiors of finitely many boxes in Ω. -/
lemma compact_box_cover (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∃ s : Finset (Box n), (∀ Q ∈ s, carrier Q ⊆ Ω) ∧
      C ⊆ ⋃ Q ∈ s, interior (carrier Q) := by
  have hc : ∀ x : C, ∃ Q : Box n, x.val ∈ interior (carrier Q) ∧ carrier Q ⊆ Ω :=
    fun x => exists_box_neighborhood hΩ (hCΩ x.property)
  choose Q hQ hQΩ using hc
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : C => interior (carrier (Q x)))
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hQ ⟨x, hx⟩⟩)
  refine ⟨t.image Q, ?_, ?_⟩
  · intro R hR
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hR
    exact hQΩ x
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨Q i, Finset.mem_image.mpr ⟨i, hi, rfl⟩, hxi⟩

lemma locally_integrable_on_compact_jordan {f : E n → ℝ}
    (hΩ : IsOpen Ω) (hf : LocallyRiemannIntegrable Ω f)
    (hC : CompactJordanSubset Ω C) : RegionIntegrable (fun x : C => f x) := by
  rcases n with _ | n
  · exact region_integrable_zero_dim _ _
  have hn : 0 < n + 1 := Nat.succ_pos _
  obtain ⟨s, hsΩ, hcover⟩ := compact_box_cover hΩ hC.1 hC.2.2
  have hbound : BddAbove (⋃ Q ∈ s, (fun x => |f x|) '' carrier Q) :=
    s.finite_toSet.bddAbove_biUnion.mpr (fun Q hQ => (bounded_abs (hf Q (hsΩ Q hQ)).1).2)
  obtain ⟨M, hM⟩ := hbound
  apply integrable_of_null_relative_discontinuities hn hC.2.1
  · refine ⟨M, ?_⟩
    intro x
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (hcover x.property)
    exact hM (mem_iUnion₂.mpr ⟨Q, hQ, ⟨x, interior_subset hxQ, rfl⟩⟩)
  · have hd : Null (⋃ Q : s, discontinuitySet f Q.val) :=
      null_iUnion_countable _ (fun Q =>
        (integrable_iff_null_discontinuitySet hn f Q.val (hf Q.val (hsΩ Q.val Q.property)).1).mp
          (hf Q.val (hsΩ Q.val Q.property)))
    apply null_mono (T := ⋃ Q : s, discontinuitySet f Q.val) _ hd
    rintro x ⟨hx, hdisc⟩
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (hcover hx)
    apply mem_iUnion.mpr
    refine ⟨⟨Q, hQ⟩, interior_subset hxQ, ?_⟩
    intro hc
    have hcont : ContinuousAt f x := hc.continuousAt (mem_interior_iff_mem_nhds.mp hxQ)
    exact hdisc (hcont.comp continuous_subtype_val.continuousAt)

lemma jordan_box (Q : Box n) : Jordan (carrier Q) := by
  rcases n with _ | n
  · exact jordan_zero_dim _
  apply (jordan_iff_boundary (Nat.succ_pos _) _ (carrier_isBounded Q)).mpr
  let F : Finset (Fin (n + 1) × ℝ) :=
    Finset.univ.image (fun i => (i, Q.lower i)) ∪
      Finset.univ.image (fun i => (i, Q.upper i))
  apply contentZero_mono (T := ⋃ p ∈ F, coordinateFace Q p.1 p.2) _
    (finite_faces_contentZero Q F)
  intro x hx
  have hxQ : x ∈ carrier Q := (isClosed_carrier Q).closure_eq ▸ hx.1
  have hnot : ¬ ∀ i, Q.lower i < x i ∧ x i < Q.upper i := by
    intro h
    exact hx.2 (by rw [interior_carrier]; exact h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  by_cases hl : Q.lower i < x i
  · have he : x i = Q.upper i := le_antisymm (hxQ i).2 (hi hl)
    exact mem_iUnion₂.mpr ⟨(i, Q.upper i), Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), hxQ, he⟩
  · have he : x i = Q.lower i := le_antisymm (not_lt.mp hl) (hxQ i).1
    exact mem_iUnion₂.mpr ⟨(i, Q.lower i), Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), hxQ, he⟩

lemma compact_jordan_neighborhood (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∃ L, CompactJordanSubset Ω L ∧ C ⊆ interior L := by
  obtain ⟨s, hsΩ, hs⟩ := compact_box_cover hΩ hC hCΩ
  refine ⟨⋃ Q ∈ s, carrier Q, ⟨s.isCompact_biUnion (fun Q _ => carrier_compact Q),
    jordan_finite_union s _ (fun Q _ => jordan_box Q), ?_⟩, ?_⟩
  · exact iUnion₂_subset (fun Q hQ => hsΩ Q hQ)
  · intro x hx
    obtain ⟨Q, hQ, hxQ⟩ := mem_iUnion₂.mp (hs hx)
    exact interior_mono (subset_iUnion₂_of_subset Q hQ Subset.rfl) hxQ

lemma regular_exhaustion_exists (Ω : Set (E n)) (hΩ : IsOpen Ω) :
    ∃ K, RegularExhaustion Ω K := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let B := CompactExhaustion.choice Ω
  let C : ℕ → Set (E n) := fun j => Subtype.val '' B j
  have hC (j : ℕ) : IsCompact (C j) := (B.isCompact j).image continuous_subtype_val
  have hCΩ (j : ℕ) : C j ⊆ Ω := by rintro x ⟨y, _, rfl⟩; exact y.property
  have enlarge : ∀ L : {L : Set (E n) // CompactJordanSubset Ω L}, ∀ j : ℕ,
      ∃ N : {N : Set (E n) // CompactJordanSubset Ω N},
        L.val ∪ C j ⊆ interior N.val := by
    intro L j
    obtain ⟨N, hN, hsub⟩ := compact_jordan_neighborhood hΩ (L.property.1.union (hC j))
      (union_subset L.property.2.2 (hCΩ j))
    exact ⟨⟨N, hN⟩, hsub⟩
  let L : ℕ → {L : Set (E n) // CompactJordanSubset Ω L} :=
    fun j => Nat.recOn j ⟨∅, isCompact_empty, jordan_empty n, empty_subset Ω⟩
      (fun j L => Classical.choose (enlarge L j))
  have hstep (j : ℕ) : (L j).val ∪ C j ⊆ interior (L (j+1)).val :=
    Classical.choose_spec (enlarge (L j) j)
  refine ⟨fun j => (L j).val, (fun j => (L j).property),
    (fun j => subset_union_left.trans (hstep j)), ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset (fun j => interior_subset.trans (L j).property.2.2)
  · intro x hx
    obtain ⟨j, hj⟩ := B.exists_mem ⟨x, hx⟩
    exact mem_iUnion.mpr ⟨j+1, hstep j (Or.inr ⟨⟨x, hx⟩, hj, rfl⟩)⟩

lemma empty_absoluteMass (f : E n → ℝ) : absoluteMass ∅ f = 0 := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro S
  apply iSup_le
  intro hS
  have he : S = ∅ := subset_empty_iff.mp hS.2.2
  subst S
  change ENNReal.ofReal (regionIntegral (fun x : (∅ : Set (E n)) => |f x|)) ≤ 0
  rw [(empty_region (fun x : (∅ : Set (E n)) => |f x|)).2]
  simp

lemma zero_dimension (Ω : Set (E 0)) (f : E 0 → ℝ) :
    (Ω = ∅ ∨ Ω = univ) ∧ LocallyRiemannIntegrable Ω f ∧
    absoluteMass Ω f = (if (0 : E 0) ∈ Ω then ENNReal.ofReal |f 0| else 0) ∧
    AbsolutelyConvergent Ω f ∧ ∀ K, RegularExhaustion Ω K →
      HasIntegralAlong f K (if (0 : E 0) ∈ Ω then f 0 else 0) := by
  have hlocal : LocallyRiemannIntegrable Ω f := fun Q _ => (Darboux.zero_dimension Q f).2.1
  have hmass : absoluteMass Ω f =
      (if (0 : E 0) ∈ Ω then ENNReal.ofReal |f 0| else 0) := by
    apply le_antisymm
    · apply iSup_le
      intro S
      apply iSup_le
      intro hS
      change ENNReal.ofReal (regionIntegral (fun x : S => |f x|)) ≤ _
      rw [((JordanRegions.zero_dimension S).2.2 (fun x : S => |f x|)).2]
      by_cases h0S : (0 : E 0) ∈ S
      · simp only [h0S, dite_true, hS.2.2 h0S, ite_true, le_refl]
      · simp only [h0S, dite_false, ENNReal.ofReal_zero]
        exact bot_le
    · have hΩ : CompactJordanSubset Ω Ω :=
        ⟨Set.Subsingleton.isCompact (fun _ _ _ _ => Subsingleton.elim _ _),
          jordan_zero_dim Ω, Subset.rfl⟩
      have hle : ENNReal.ofReal (regionIntegral (fun x : Ω => |f x|)) ≤ absoluteMass Ω f :=
        le_iSup_of_le Ω (le_iSup_of_le hΩ le_rfl)
      rw [((JordanRegions.zero_dimension Ω).2.2 (fun x : Ω => |f x|)).2] at hle
      split_ifs at hle ⊢ <;> simp_all
  have habs : AbsolutelyConvergent Ω f := ⟨hlocal, by change absoluteMass Ω f < ⊤; rw [hmass]; split_ifs <;> simp⟩
  refine ⟨?_, hlocal, hmass, habs, ?_⟩
  · by_cases h0 : (0 : E 0) ∈ Ω
    · right
      apply eq_univ_of_forall
      intro x
      simpa only [Subsingleton.elim x (0 : E 0)] using h0
    · left
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h0 (by simpa only [Subsingleton.elim x (0 : E 0)] using hx)
  · intro K hK
    by_cases h0 : (0 : E 0) ∈ Ω
    · rw [ite_eq_left h0]
      obtain ⟨j, hj⟩ := compact_contained_in_exhaustion hK isCompact_singleton
        (singleton_subset_iff.mpr h0)
      apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => f 0) atTop (𝓝 (f 0))).congr'
      filter_upwards [eventually_ge_atTop j] with k hk
      have h0K : (0 : E 0) ∈ K k := regular_exhaustion_mono hK hk (hj (mem_singleton 0))
      change f 0 = regionIntegral (fun x : K k => f x)
      rw [((JordanRegions.zero_dimension (K k)).2.2 (fun x : K k => f x)).2,
        dite_eq_left h0K]
    · rw [ite_eq_right h0]
      have hz (j : ℕ) : K j = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact h0 (by simpa only [Subsingleton.elim x (0 : E 0)] using (hK.1 j).2.2 hx)
      have he : (fun j => regionIntegral (fun x : K j => f x)) = fun _ => 0 := by
        funext j
        rw [((JordanRegions.zero_dimension (K j)).2.2 (fun x : K j => f x)).2]
        have h0K : (0 : E 0) ∉ K j := by rw [hz j]; exact notMem_empty 0
        rw [dite_eq_right h0K]
      change Tendsto _ atTop (𝓝 0)
      rw [he]
      exact tendsto_const_nhds

end D04.ImproperExhaustions
