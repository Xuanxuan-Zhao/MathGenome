import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.AsymptoticCenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachConvex.ChebyshevCenters

namespace ExpandedFA.BanachConvex.AsymptoticCenters
open Set Filter
universe u
noncomputable section
variable {X : Type u} [NormedAddCommGroup X] {a : ℕ → X} {C : Set X}

omit [NormedAddCommGroup X] in
lemma tailSet_nonempty (a : ℕ → X) (n : ℕ) : (tailSet a n).Nonempty :=
  ⟨a n, n, by simp, rfl⟩

omit [NormedAddCommGroup X] in
lemma tailSet_subset_range (a : ℕ → X) (n : ℕ) : tailSet a n ⊆ range a :=
  image_subset_range _ _

lemma tailSet_bounded (hb : Bornology.IsBounded (range a)) (n : ℕ) :
    Bornology.IsBounded (tailSet a n) := hb.subset (tailSet_subset_range a n)

lemma distances_bounded (hb : Bornology.IsBounded (range a)) (x : X) :
    atTop.IsBoundedUnder (· ≤ ·) (fun n => ‖x - a n‖) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  exact isBoundedUnder_of ⟨‖x‖ + M, fun n =>
    (norm_sub_le x (a n)).trans (add_le_add le_rfl (hM _ (mem_range_self n)))⟩

lemma distances_cobounded (a : ℕ → X) (x : X) :
    atTop.IsCoboundedUnder (· ≤ ·) (fun n => ‖x - a n‖) :=
  isCoboundedUnder_le_of_le atTop (fun n => norm_nonneg (x - a n))

lemma radius_nonneg (hb : Bornology.IsBounded (range a)) (x : X) : 0 ≤ radius a x := by
  apply le_limsup_of_le (distances_bounded hb x)
  intro b hb
  obtain ⟨n, hn⟩ := hb.exists
  exact (norm_nonneg _).trans hn

lemma radius_le_of_eventually {x : X} {R : ℝ}
    (h : ∀ᶠ n in atTop, ‖x - a n‖ ≤ R) : radius a x ≤ R :=
  limsup_le_of_le (distances_cobounded a x) h

lemma eventually_distance_lt (hb : Bornology.IsBounded (range a))
    {x : X} {R : ℝ} (h : radius a x < R) : ∀ᶠ n in atTop, ‖x - a n‖ < R :=
  eventually_lt_of_limsup_lt h (distances_bounded hb x)

lemma radius_le_tail (hb : Bornology.IsBounded (range a)) (n : ℕ) (x : X) :
    radius a x ≤ tailRadius a n x := by
  apply radius_le_of_eventually
  filter_upwards [eventually_ge_atTop n] with i hi
  exact ChebyshevCenters.distance_le_radius (tailSet_bounded hb n) ⟨i, hi, rfl⟩ x

lemma tailRadius_antitone (hb : Bornology.IsBounded (range a)) (x : X) :
    Antitone (fun n => tailRadius a n x) := by
  intro m n hmn
  apply ChebyshevCenters.radius_le (tailSet_nonempty a n)
  rintro _ ⟨i, hi, rfl⟩
  exact ChebyshevCenters.distance_le_radius (tailSet_bounded hb m)
    ⟨i, hmn.trans hi, rfl⟩ x

lemma tailRadius_tendsto (hb : Bornology.IsBounded (range a)) (x : X) :
    Tendsto (fun n => tailRadius a n x) atTop (nhds (radius a x)) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Eventually.of_forall (fun n => hl.trans_le (radius_le_tail hb n x))
  · intro r hr
    obtain ⟨s, hs, hsr⟩ := exists_between hr
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_distance_lt hb hs)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply lt_of_le_of_lt _ hsr
    apply ChebyshevCenters.radius_le (tailSet_nonempty a n)
    rintro _ ⟨i, hi, rfl⟩
    exact (hN i (hn.trans hi)).le

theorem tail_limit : Spec.TailLimit.{u} := by
  intro X _ a hb x
  exact ⟨tailRadius_antitone hb x, tailRadius_tendsto hb x⟩

lemma radius_le_add (hb : Bornology.IsBounded (range a)) (x y : X) :
    radius a x ≤ ‖x - y‖ + radius a y := by
  apply ge_of_tendsto (tendsto_const_nhds.add (tailRadius_tendsto hb y))
  exact Eventually.of_forall (fun n => (radius_le_tail hb n x).trans
    (ChebyshevCenters.radius_le_add (tailSet_nonempty a n) (tailSet_bounded hb n) x y))

lemma radius_lipschitz (hb : Bornology.IsBounded (range a)) : LipschitzWith 1 (radius a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  apply abs_le.mpr
  have h₁ := radius_le_add hb x y
  have h₂ := radius_le_add hb y x
  rw [norm_sub_rev y x] at h₂
  constructor <;> linarith

lemma radius_norm_bounds (hb : Bornology.IsBounded (range a)) :
    ∃ M : ℝ, ∀ x, (0 ≤ radius a x ∧ radius a x ≤ ‖x‖ + M) ∧
      ‖x‖ - M ≤ radius a x := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨M, fun x => ⟨⟨radius_nonneg hb x, ?_⟩, ?_⟩⟩
  · apply radius_le_of_eventually
    exact Eventually.of_forall (fun n => (norm_sub_le x (a n)).trans
      (add_le_add le_rfl (hM _ (mem_range_self n))))
  · apply le_limsup_of_le (distances_bounded hb x)
    intro b hb'
    obtain ⟨n, hn⟩ := hb'.exists
    have h := norm_le_norm_sub_add x (a n)
    have h' := hM _ (mem_range_self n)
    linarith

lemma radius_coercive (hb : Bornology.IsBounded (range a)) : RadiusCoercive a := by
  obtain ⟨M, hM⟩ := radius_norm_bounds hb
  intro b
  refine ⟨b + M + 1, fun x hx => ?_⟩
  have h := (hM x).2
  linarith

variable [NormedSpace ℝ X]

lemma radius_convex (hb : Bornology.IsBounded (range a)) : ConvexOn ℝ univ (radius a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  apply le_of_tendsto_of_tendsto (tailRadius_tendsto hb (s • x + t • y))
    (((tailRadius_tendsto hb x).const_mul s).add ((tailRadius_tendsto hb y).const_mul t))
  exact Eventually.of_forall (fun n =>
    (ChebyshevCenters.radius_convex (tailSet_nonempty a n) (tailSet_bounded hb n)).2
      (mem_univ x) (mem_univ y) hs ht hst)

theorem radius_regularity : Spec.Regularity.{u} := by
  intro X _ _ a hb
  obtain ⟨M, hM⟩ := radius_norm_bounds hb
  exact ⟨⟨M, fun x => (hM x).1⟩, radius_convex hb, radius_lipschitz hb, radius_coercive hb⟩


omit [NormedSpace ℝ X] in
/-- Two radii always control the distance between their base points. -/
lemma norm_sub_le_radius_add (hb : Bornology.IsBounded (range a)) (x y : X) :
    ‖x - y‖ ≤ radius a x + radius a y := by
  apply ge_of_tendsto ((tailRadius_tendsto hb x).add (tailRadius_tendsto hb y))
  apply Eventually.of_forall
  intro n
  have h := norm_sub_le_norm_sub_add_norm_sub x (a n) y
  rw [norm_sub_rev (a n) y] at h
  exact h.trans (add_le_add
    (ChebyshevCenters.distance_le_radius (tailSet_bounded hb n) ⟨n, by simp, rfl⟩ x)
    (ChebyshevCenters.distance_le_radius (tailSet_bounded hb n) ⟨n, by simp, rfl⟩ y))

/-- The modulus is chosen before the common tail; it is independent of that tail. -/
lemma radius_midpoint_drop [UniformConvexSpace X]
    (hb : Bornology.IsBounded (range a)) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R : ℝ, 0 < R → R ≤ B → ∀ x y : X,
      radius a x < R → radius a y < R → ε ≤ ‖x - y‖ →
      radius a ((1 / 2 : ℝ) • (x + y)) ≤ R * (1 - δ) := by
  obtain ⟨δ, hδ, hdrop⟩ := ChebyshevCenters.radius_midpoint_drop
    (X := X) (A := {0}) (singleton_nonempty _) Bornology.isBounded_singleton hε hB
  refine ⟨δ, hδ, ?_⟩
  intro R hR hRB x y hx hy hxy
  apply radius_le_of_eventually
  filter_upwards [eventually_distance_lt hb hx, eventually_distance_lt hb hy] with n hxn hyn
  have h := hdrop R hR hRB (x - a n) (y - a n)
    (by simpa [ChebyshevCenters.radius] using hxn.le)
    (by simpa [ChebyshevCenters.radius] using hyn.le)
    (by simpa only [sub_sub_sub_cancel_right] using hxy)
  simp only [ChebyshevCenters.radius, image_singleton, sub_zero, csSup_singleton] at h
  have heq : (1 / 2 : ℝ) • (x + y) - a n =
      (1 / 2 : ℝ) • ((x - a n) + (y - a n)) := by module
  rw [heq]
  exact h

lemma near_minimizers_close [UniformConvexSpace X]
    (hb : Bornology.IsBounded (range a)) (hC : Convex ℝ C)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hmin : ∀ x ∈ C, ρ ≤ radius a x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ C, ∀ y ∈ C,
      radius a x < ρ + η → radius a y < ρ + η → ‖x - y‖ < ε := by
  by_cases hz : ρ = 0
  · refine ⟨ε / 3, by linarith, ?_⟩
    intro x _ y _ hx hy
    have h := norm_sub_le_radius_add hb x y
    rw [hz] at hx hy
    linarith
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
  obtain ⟨δ, hδ, hdrop⟩ := radius_midpoint_drop hb hε (show 0 < ρ + 1 by linarith)
  let η := min 1 (ρ * δ / 2)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη₁ : η ≤ 1 := min_le_left _ _
  have hη₂ : η ≤ ρ * δ / 2 := min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro x hx y hy hrx hry
  by_contra hn
  have hm := hC hx hy (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ) + 1/2 = 1 by norm_num)
  rw [← smul_add] at hm
  have hlo := hmin _ hm
  have hhi := hdrop (ρ + η) (by linarith) (by linarith) x y hrx hry (le_of_not_gt hn)
  nlinarith [mul_pos hη hδ]

lemma cauchy_of_radius_tendsto [UniformConvexSpace X]
    (hb : Bornology.IsBounded (range a)) (hC : Convex ℝ C)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hmin : ∀ x ∈ C, ρ ≤ radius a x)
    {x : ℕ → X} (hx : ∀ n, x n ∈ C)
    (hlim : Tendsto (fun n => radius a (x n)) atTop (nhds ρ)) : CauchySeq x := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hb hC hρ hmin hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (ρ + η) (by linarith))
  refine ⟨N, ?_⟩
  intro m hm n hn
  rw [dist_eq_norm]
  exact hclose _ (hx m) _ (hx n) (hN m hm) (hN n hn)

/-- Completeness suffices, with no extra compactness or boundedness assumption on C. -/
lemma exists_center [UniformConvexSpace X] [CompleteSpace X]
    (hCne : C.Nonempty) (hclosed : IsClosed C) (hC : Convex ℝ C)
    (hb : Bornology.IsBounded (range a)) : ∃ c, IsCenter C a c := by
  let S : Set ℝ := radius a '' C
  have hS : S.Nonempty := hCne.image _
  have hS0 : ∀ z ∈ S, (0 : ℝ) ≤ z := by
    rintro _ ⟨x, _, rfl⟩
    exact radius_nonneg hb x
  have hSb : BddBelow S := ⟨0, hS0⟩
  have hρ : 0 ≤ sInf S := le_csInf hS hS0
  have hmin : ∀ x ∈ C, sInf S ≤ radius a x :=
    fun x hx => csInf_le hSb ⟨x, hx, rfl⟩
  obtain ⟨v, _, hv, hvS⟩ := exists_seq_tendsto_sInf hS hSb
  choose x hx hval using hvS
  have hlim : Tendsto (fun n => radius a (x n)) atTop (nhds (sInf S)) := by
    simpa only [hval] using hv
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete
    (cauchy_of_radius_tendsto hb hC hρ hmin hx hlim)
  have hcC : c ∈ C := hclosed.mem_of_tendsto hc (Eventually.of_forall hx)
  have hrc : radius a c = sInf S := tendsto_nhds_unique
    (((radius_lipschitz hb).continuous.tendsto c).comp hc) hlim
  exact ⟨c, hcC, fun x hx => hrc ▸ hmin x hx⟩

lemma center_unique [UniformConvexSpace X]
    (hb : Bornology.IsBounded (range a)) (hC : Convex ℝ C)
    {c d : X} (hc : IsCenter C a c) (hd : IsCenter C a d) : c = d := by
  by_contra hn
  have hε : 0 < ‖c - d‖ := norm_sub_pos_iff.mpr hn
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hb hC
    (radius_nonneg hb c) hc.2 hε
  have heq : radius a d = radius a c := le_antisymm (hd.2 c hc.1) (hc.2 d hd.1)
  exact (lt_irrefl _) (hclose c hc.1 d hd.1 (by linarith) (by linarith))

theorem unique_center : Spec.UniqueCenter.{u} := by
  intro X _ _ _ _ C a hCne hclosed hC hb _haC
  obtain ⟨c, hc⟩ := exists_center hCne hclosed hC hb
  exact ⟨c, hc, fun d hd => center_unique hb hC hd hc⟩

lemma minimizing_sequence_tendsto [UniformConvexSpace X]
    (hb : Bornology.IsBounded (range a)) (hC : Convex ℝ C)
    {c : X} (hc : IsCenter C a c) {x : ℕ → X} (hx : ∀ n, x n ∈ C)
    (hlim : Tendsto (fun n => radius a (x n)) atTop (nhds (radius a c))) :
    Tendsto x atTop (nhds c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hclose⟩ := near_minimizers_close hb hC
    (radius_nonneg hb c) hc.2 hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlim).2 (radius a c + η) (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  exact hclose (x n) (hx n) c hc.1 (hN n hn) (by linarith)

theorem minimizing_sequences : Spec.MinimizingSequences.{u} := by
  intro X _ _ _ _ C a _hCne _hclosed hC hb _haC c hc x hx hlim
  exact minimizing_sequence_tendsto hb hC hc hx hlim

theorem tail_center_existence : Spec.TailCenterExistence.{u} := by
  intro X _ _ _ _ C a hCne hclosed hC hb _haC
  have h : ∀ n, ∃ c, ChebyshevCenters.IsCenter C (tailSet a n) c := fun n =>
    ChebyshevCenters.exists_center hCne hclosed hC (tailSet_nonempty a n) (tailSet_bounded hb n)
  exact Classical.axiomOfChoice h

theorem tail_centers : Spec.TailCenters.{u} := by
  intro X _ _ _ _ C a _hCne _hclosed hC hb _haC c hc cn hcn
  have hlow : ∀ n, radius a c ≤ radius a (cn n) := fun n => hc.2 _ (hcn n).1
  have hmid : ∀ n, radius a (cn n) ≤ tailRadius a n (cn n) :=
    fun n => radius_le_tail hb n (cn n)
  have hupp : ∀ n, tailRadius a n (cn n) ≤ tailRadius a n c :=
    fun n => (hcn n).2 c hc.1
  have htail : Tendsto (fun n => tailRadius a n (cn n)) atTop (nhds (radius a c)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (tailRadius_tendsto hb c)
      (fun n => (hlow n).trans (hmid n)) hupp
  have hr : Tendsto (fun n => radius a (cn n)) atTop (nhds (radius a c)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail hlow hmid
  exact ⟨minimizing_sequence_tendsto hb hC hc (fun n => (hcn n).1) hr, htail, hr⟩

end
end ExpandedFA.BanachConvex.AsymptoticCenters
