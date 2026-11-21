import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.BarrierSqueeze
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.PerronEnvelope

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex

/-- A positive superharmonic barrier, continuously extended to its cap closure. -/
def PositiveLocalBarrier (Ω : Set ℂ) (ξ : ℂ) (r : ℝ) (b : ℂ → ℝ) : Prop :=
  0 < r ∧ SuperharmonicOn (Ω ∩ ball ξ r) b ∧
    ContinuousOn b (closure (Ω ∩ ball ξ r)) ∧ b ξ = 0 ∧
    ∀ z ∈ closure (Ω ∩ ball ξ r), z ≠ ξ → 0 < b z

/-- Regularity means the existence of a barrier at this boundary point. -/
def RegularBoundaryPoint (Ω : Set ℂ) (ξ : ℂ) : Prop :=
  ξ ∈ frontier Ω ∧ ∃ r : ℝ, ∃ b : ℂ → ℝ, PositiveLocalBarrier Ω ξ r b

end D12Complex

namespace D12Complex.BarrierSqueeze

lemma closedCap_subset {Ω : Set ℂ} {ξ : ℂ} {ρ r : ℝ} (hρr : ρ < r) :
    closure Ω ∩ closedBall ξ ρ ⊆ closure (Ω ∩ ball ξ r) := by
  intro z hz
  exact isOpen_ball.closure_inter ⟨hz.1, lt_of_le_of_lt hz.2 hρr⟩

/-- This includes the empty artificial boundary: choose zero in that case. -/
lemma artificial_boundary_scale {K : Set ℂ} {b : ℂ → ℝ} {c m : ℝ}
    (hK : IsCompact K) (hb : ContinuousOn b K)
    (hpos : ∀ z ∈ K, 0 < b z) (hmc : m ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, c - C * b z ≤ m := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hne hb
    have hβ := hpos a ha
    let C := (c - m) / b a
    have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hmc) hβ.le
    refine ⟨C, hC, fun z hz => ?_⟩
    have he : C * b a = c - m := div_mul_cancel₀ _ hβ.ne'
    have hl := mul_le_mul_of_nonneg_left (hmin hz) hC
    linarith
  · exact ⟨0, le_rfl, fun z hz => False.elim (hne ⟨z, hz⟩)⟩

lemma barrier_nonneg {Ω : Set ℂ} {ξ : ℂ} {r : ℝ} {b : ℂ → ℝ}
    (hb : PositiveLocalBarrier Ω ξ r b) {z : ℂ}
    (hz : z ∈ closure (Ω ∩ ball ξ r)) : 0 ≤ b z := by
  by_cases he : z = ξ
  · simp [he, hb.2.2.2.1]
  · exact (hb.2.2.2.2 z hz he).le

/-- Gluing a depressed barrier to a constant yields a genuine Perron minorant.
The actual boundary need not be smooth, and the artificial boundary may be empty. -/
lemma barrier_minorant {Ω : Set ℂ} {φ : ℂ → ℝ} {ξ : ℂ} {r ρ c m C : ℝ}
    {b : ℂ → ℝ} (hΩ : IsOpen Ω) (hb : PositiveLocalBarrier Ω ξ r b)
    (hρr : ρ < r) (hC : 0 ≤ C)
    (hm : ∀ η ∈ frontier Ω, m ≤ φ η)
    (hc : ∀ η ∈ frontier Ω, dist η ξ ≤ ρ → c ≤ φ η)
    (hcap : ∀ η ∈ closure Ω ∩ sphere ξ ρ, c - C * b η ≤ m) :
    subharmonicPaste (Ω ∩ ball ξ ρ) (fun _ => m) (fun z => c - C * b z)
      ∈ perronClass Ω φ := by
  classical
  let W := Ω ∩ ball ξ ρ
  let q : ℂ → ℝ := fun z => c - C * b z
  let p := subharmonicPaste W (fun _ => m) q
  have hWo : IsOpen W := hΩ.inter isOpen_ball
  have hWs : W ⊆ Ω ∩ ball ξ r := inter_subset_inter_right Ω (ball_subset_ball hρr.le)
  have hclosure : closure W ⊆ closure (Ω ∩ ball ξ r) := closure_mono hWs
  have hqcont : ContinuousOn q (closure W) :=
    continuousOn_const.sub (continuousOn_const.mul (hb.2.2.1.mono hclosure))
  have hqsub : SubharmonicOn W q := by
    have hs := HarmonicReplacementPasting.subharmonicOn_mono hb.2.1 hWo hWs
    have hmul := SubharmonicOperations.subharmonicOn_nonneg_mul W (fun z => -b z) C hC hs
    have hadd := SubharmonicOperations.subharmonicOn_add_const W _ c hmul
    convert hadd using 1
    ext z
    dsimp [q]
    ring
  have hinterface : ∀ η ∈ Ω ∩ frontier W, q η ≤ m := by
    intro η hη
    have hcl := closure_inter_subset (frontier_subset_closure hη.2)
    have hle : dist η ξ ≤ ρ := closure_ball_subset_closedBall hcl.2
    have hn : η ∉ W := by
      have hh := hη.2
      rw [hWo.frontier_eq] at hh
      exact hh.2
    have hge : ρ ≤ dist η ξ := le_of_not_gt (fun hi => hn ⟨hη.1, hi⟩)
    exact hcap η ⟨hcl.1, le_antisymm hle hge⟩
  have hpcont : ContinuousOn p Ω := by
    have hh : ContinuousOn (fun z => if z ∈ W then max m (q z) else m) Ω := by
      apply ContinuousOn.if (p := fun z => z ∈ W)
      · intro z hz
        exact max_eq_left (hinterface z hz)
      · exact continuousOn_const.sup (hqcont.mono inter_subset_right)
      · exact continuousOn_const
    unfold p subharmonicPaste
    convert hh using 1
    ext z
    split_ifs <;> rfl
  refine ⟨HarmonicReplacementPasting.subharmonic_paste_of_continuous Ω W (fun _ => m) q
    (SubharmonicOperations.subharmonicOn_const Ω m hΩ) hqsub inter_subset_left hpcont, ?_⟩
  intro η hη ε hε
  by_cases hηW : η ∈ closure W
  · have hqη : q η ≤ φ η := by
      have hle : dist η ξ ≤ ρ := closure_ball_subset_closedBall
        (closure_inter_subset hηW).2
      have hp := mul_nonneg hC (barrier_nonneg hb (hclosure hηW))
      dsimp [q]
      linarith [hc η hη hle]
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
      (hqcont η hηW) ε hε
    refine ⟨δ, hδ, fun z hz hdist => ?_⟩
    by_cases hzW : z ∈ W
    · have hh := hd (subset_closure hzW) hdist
      have he : q z < q η + ε := by
        have := (abs_lt.mp (show |q z - q η| < ε by simpa [Real.dist_eq] using hh)).2
        linarith
      change p z ≤ φ η + ε
      simp only [p, subharmonicPaste, ite_eq_left hzW]
      exact max_le (by linarith [hm η hη]) (by linarith)
    · change p z ≤ φ η + ε
      simp only [p, subharmonicPaste, ite_eq_right hzW]
      linarith [hm η hη]
  · obtain ⟨δ, hδ, hd⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl η hηW
    refine ⟨δ, hδ, fun z _ hdist => ?_⟩
    have hzW : z ∉ W := fun hi => hd hdist (subset_closure hi)
    change p z ≤ φ η + ε
    simp only [p, subharmonicPaste, ite_eq_right hzW]
    linarith [hm η hη]



/-- A class member with a limit arbitrarily close below the prescribed value. -/
lemma exists_minorant_limit {Ω : Set ℂ} {φ : ℂ → ℝ} {ξ : ℂ}
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω)
    (hφ : ContinuousOn φ (frontier Ω)) (hreg : RegularBoundaryPoint Ω ξ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v ∈ perronClass Ω φ, Tendsto v (𝓝[Ω] ξ) (𝓝 (φ ξ - ε)) := by
  obtain ⟨hξ, r, b, hb⟩ := hreg
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hφ ξ hξ) ε hε
  let ρ := min (r / 2) (δ / 2)
  have hρ : 0 < ρ := lt_min (half_pos hb.1) (half_pos hδ)
  have hρr : ρ < r := (min_le_left _ _).trans_lt (by linarith [hb.1])
  have hρδ : ρ < δ := (min_le_right _ _).trans_lt (by linarith)
  let c := φ ξ - ε
  let m := min (sInf (φ '' frontier Ω)) c
  have hm : ∀ η ∈ frontier Ω, m ≤ φ η := by
    have hK : IsCompact (frontier Ω) :=
      hΩb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
    intro η hη
    exact (min_le_left _ _).trans (csInf_le (hK.bddBelow_image hφ) ⟨η, hη, rfl⟩)
  have hmc : m ≤ c := min_le_right _ _
  have hc : ∀ η ∈ frontier Ω, dist η ξ ≤ ρ → c ≤ φ η := by
    intro η hη hdist
    have hh := hd hη (hdist.trans_lt hρδ)
    have := (abs_lt.mp (show |φ η - φ ξ| < ε by simpa [Real.dist_eq] using hh)).1
    dsimp [c]
    linarith
  let K := closure Ω ∩ sphere ξ ρ
  have hK : IsCompact K := hΩb.isCompact_closure.inter_right isClosed_sphere
  have hKs : K ⊆ closure (Ω ∩ ball ξ r) :=
    (inter_subset_inter_right _ sphere_subset_closedBall).trans (closedCap_subset hρr)
  have hpos : ∀ z ∈ K, 0 < b z := by
    intro z hz
    apply hb.2.2.2.2 z (hKs hz)
    intro he
    have hh := hz.2
    simp only [mem_sphere, he, dist_self] at hh
    linarith
  obtain ⟨C, hC, hcap⟩ := artificial_boundary_scale hK (hb.2.2.1.mono hKs) hpos hmc
  let W := Ω ∩ ball ξ ρ
  let q : ℂ → ℝ := fun z => c - C * b z
  let v := subharmonicPaste W (fun _ => m) q
  have hv : v ∈ perronClass Ω φ := barrier_minorant hΩ.2.1 hb hρr hC hm hc hcap
  refine ⟨v, hv, ?_⟩
  have hξcl : ξ ∈ closure W := isOpen_ball.closure_inter
    ⟨frontier_subset_closure hξ, mem_ball_self hρ⟩
  have hclos : closure W ⊆ closure (Ω ∩ ball ξ r) :=
    closure_mono (inter_subset_inter_right Ω (ball_subset_ball hρr.le))
  have hqcont : ContinuousOn q (closure W) :=
    continuousOn_const.sub (continuousOn_const.mul (hb.2.2.1.mono hclos))
  have hmax : ContinuousWithinAt (fun z => max m (q z)) (closure W) ξ :=
    continuousWithinAt_const.sup (hqcont ξ hξcl)
  have hval : max m (q ξ) = c := by
    simp only [q, hb.2.2.2.1, mul_zero, sub_zero, max_eq_right hmc]
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro η hη
  obtain ⟨d, hdp, hdist⟩ := Metric.continuousWithinAt_iff.mp hmax η hη
  refine ⟨min d ρ, lt_min hdp hρ, fun {z} hz hdz => ?_⟩
  have hzW : z ∈ W := ⟨hz, hdz.trans_le (min_le_right _ _)⟩
  have hh := hdist (subset_closure hzW) (hdz.trans_le (min_le_left _ _))
  simpa only [hval, v, subharmonicPaste, ite_eq_left hzW] using hh

/-- Minorants for opposite data compare without imposing boundary values
on either member. -/
lemma opposite_class_comparison {Ω : Set ℂ} {φ u v : ℂ → ℝ}
    (hΩb : Bornology.IsBounded Ω) (hu : u ∈ perronClass Ω φ)
    (hv : v ∈ perronClass Ω (fun z => -φ z)) : ∀ z ∈ Ω, u z ≤ -v z := by
  have hs := SubharmonicOperations.subharmonicOn_add Ω u v hu.1 hv.1
  have hb : BoundaryLimsupLE Ω (fun z => u z + v z) 0 := by
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hξ (ε / 2) (half_pos hε)
    obtain ⟨η, hη, he⟩ := hv.2 ξ hξ (ε / 2) (half_pos hε)
    refine ⟨min δ η, lt_min hδ hη, fun z hz ht => ?_⟩
    have h1 := hd z hz (ht.trans_le (min_le_left _ _))
    have h2 := he z hz (ht.trans_le (min_le_right _ _))
    linarith
  have hle := SubharmonicMaximum.subharmonic_boundary_maximum Ω _ 0 hΩb hs hb
  intro z hz
  linarith [hle z hz]

/-- Both Perron comparisons, from a lower barrier minorant and its dual. -/
lemma envelope_between_minorants {Ω : Set ℂ} {φ u v : ℂ → ℝ}
    (hΩb : Bornology.IsBounded Ω) (hu : u ∈ perronClass Ω φ)
    (hv : v ∈ perronClass Ω (fun z => -φ z)) :
    ∀ z ∈ Ω, u z ≤ perronEnvelope Ω φ z ∧ perronEnvelope Ω φ z ≤ -v z := by
  intro z hz
  have hbound : ∀ w ∈ perronClass Ω φ, w z ≤ -v z :=
    fun w hw => opposite_class_comparison hΩb hw hv z hz
  have hbd : BddAbove ((fun w : ℂ → ℝ => w z) '' perronClass Ω φ) := by
    refine ⟨-v z, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw
  refine ⟨PerronEnvelope.le_envelope hbd hu, ?_⟩
  apply csSup_le (s := ((fun w : ℂ → ℝ => w z) '' perronClass Ω φ)) ⟨u z, u, hu, rfl⟩
  rintro _ ⟨w, hw, rfl⟩
  exact hbound w hw

theorem barrier_squeeze :
    ∀ (Ω : Set ℂ) (φ : ℂ → ℝ) (ξ : ℂ), IsDomain Ω → Bornology.IsBounded Ω →
      ContinuousOn φ (frontier Ω) → RegularBoundaryPoint Ω ξ →
      Tendsto (perronEnvelope Ω φ) (𝓝[Ω] ξ) (𝓝 (φ ξ)) := by
  intro Ω φ ξ hΩ hΩb hφ hreg
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨u, hu, htu⟩ := exists_minorant_limit hΩ hΩb hφ hreg (half_pos hε)
  obtain ⟨v, hv, htv⟩ := exists_minorant_limit hΩ hΩb hφ.neg hreg (half_pos hε)
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp htu
    (ε / 2) (half_pos hε)
  obtain ⟨η, hη, he⟩ := Metric.tendsto_nhdsWithin_nhds.mp htv
    (ε / 2) (half_pos hε)
  refine ⟨min δ η, lt_min hδ hη, fun {z} hz ht => ?_⟩
  obtain ⟨hlo, hhi⟩ := envelope_between_minorants hΩb hu hv z hz
  have h1 := hd hz (ht.trans_le (min_le_left _ _))
  have h2 := he hz (ht.trans_le (min_le_right _ _))
  rw [Real.dist_eq] at h1 h2 ⊢
  obtain ⟨hl1, hh1⟩ := abs_lt.mp h1
  obtain ⟨hl2, hh2⟩ := abs_lt.mp h2
  apply abs_lt.mpr
  constructor <;> dsimp at * <;> linarith

end D12Complex.BarrierSqueeze
