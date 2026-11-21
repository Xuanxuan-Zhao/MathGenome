import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PolygonalConnectivity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactExhaustion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.GeometricBarriers
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.FiniteCircularArcs
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.DiskUnionBoundarySectors
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Order.Interval.Set.Infinite

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.CircularExhaustion

lemma diskUnion_open (s : Finset ℂ) (r : ℂ → ℝ) : IsOpen (diskUnion s r) :=
  isOpen_biUnion fun _ _ => isOpen_ball

lemma diskUnion_closure_compact (s : Finset ℂ) (r : ℂ → ℝ) :
    IsCompact (closure (diskUnion s r)) := by
  have hb : Bornology.IsBounded (diskUnion s r) := by
    exact (Bornology.isBounded_biUnion s.finite_toSet).mpr (fun c _ => isBounded_ball)
  exact (isCompact_iff_isClosed_bounded).mpr ⟨isClosed_closure, hb.closure⟩

lemma diskUnion_closure_subset (s : Finset ℂ) (r : ℂ → ℝ)
    {Ω : Set ℂ} (h : ∀ c ∈ s, closedBall c (r c) ⊆ Ω) :
    closure (diskUnion s r) ⊆ Ω := by
  have hclosed : IsClosed (⋃ c ∈ s, closedBall c (r c)) :=
    s.finite_toSet.isClosed_biUnion (fun _ _ => isClosed_closedBall)
  apply (closure_minimal ?_ hclosed).trans
    (iUnion₂_subset fun c hc => h c hc)
  exact iUnion₂_mono fun _ _ => ball_subset_closedBall

/-- Two circles with distinct centers have finite intersection in the plane.
This checks the real dimension hypothesis of the Euclidean two-circle theorem. -/
lemma finite_circle_intersection {c d : ℂ} (hcd : c ≠ d) (R S : ℝ) :
    (sphere c R ∩ sphere d S).Finite := by
  classical
  by_cases h : (sphere c R ∩ sphere d S).Subsingleton
  · exact h.finite
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.mp h
  apply (Set.toFinite {x, y}).subset
  intro z hz
  exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    Complex.finrank_real_complex hcd hxy hx.1 hy.1 hz.1 hx.2 hy.2 hz.2

/-- An interval of radii remains after excluding every tangency and every
circle through an intersection of two earlier circles. -/
lemma choose_new_radius (s : Finset ℂ) (r : ℂ → ℝ) (c : ℂ)
    {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ t ∈ Ioo lo hi,
      (∀ d ∈ s, dist c d ≠ t + r d ∧ dist c d ≠ |t - r d|) ∧
      ∀ d ∈ s, ∀ e ∈ s, d ≠ e →
        sphere c t ∩ sphere d (r d) ∩ sphere e (r e) = ∅ := by
  classical
  let B₁ : Set ℝ := ⋃ d ∈ s,
    {dist c d - r d, r d + dist c d, r d - dist c d}
  let B₂ : Set ℝ := ⋃ d ∈ s, ⋃ e ∈ s,
    if d = e then ∅ else (fun z => dist z c) '' (sphere d (r d) ∩ sphere e (r e))
  have hB₁ : B₁.Finite := s.finite_toSet.biUnion (fun d _ => by
    exact Set.toFinite _)
  have hB₂ : B₂.Finite := s.finite_toSet.biUnion (fun d _ =>
    s.finite_toSet.biUnion (fun e _ => by
      by_cases hde : d = e
      · simp only [hde, ite_eq_left, Set.finite_empty]
      · simpa only [ite_eq_right (show d ≠ e from hde)] using (finite_circle_intersection hde (r d) (r e)).image
          (fun z => dist z c)))
  obtain ⟨t, ht, htB⟩ := (Set.Ioo_infinite hlohi).exists_notMem_finite (hB₁.union hB₂)
  have ht₁ : t ∉ B₁ := fun h => htB (Or.inl h)
  have ht₂ : t ∉ B₂ := fun h => htB (Or.inr h)
  refine ⟨t, ht, ?_, ?_⟩
  · intro d hd
    have hbad : t ∉ ({dist c d - r d, r d + dist c d, r d - dist c d} : Set ℝ) :=
      fun h => ht₁ (mem_iUnion₂.mpr ⟨d, hd, h⟩)
    constructor
    · intro he
      apply hbad
      have he' : t = dist c d - r d := by linarith
      simp only [he', mem_insert_iff, mem_singleton_iff, true_or]
    · intro he
      apply hbad
      rcases le_total (r d) t with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h)] at he
        have he' : t = r d + dist c d := by linarith
        simp [he']
      · rw [abs_of_nonpos (sub_nonpos.mpr h)] at he
        have he' : t = r d - dist c d := by linarith
        simp [he']
  · intro d hd e he hde
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply ht₂
    refine mem_iUnion₂.mpr ⟨d, hd, mem_iUnion₂.mpr ⟨e, he, ?_⟩⟩
    simp only [ite_eq_right (show d ≠ e from hde)]
    exact ⟨z, ⟨hz.1.2, hz.2⟩, hz.1.1⟩

/-- General position can be imposed in independent open intervals of radii.
No center is moved, so all previously arranged covering margins survive. -/
lemma generalPosition_radii (s : Finset ℂ) (lo hi : ℂ → ℝ)
    (hpos : ∀ c ∈ s, 0 < lo c) (hlt : ∀ c ∈ s, lo c < hi c) :
    ∃ r : ℂ → ℝ, (∀ c ∈ s, r c ∈ Ioo (lo c) (hi c)) ∧ GeneralPosition s r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, by simp, by simp [GeneralPosition]⟩
  | @insert c s hcs ih =>
    obtain ⟨r, hr, hG⟩ := ih (fun d hd => hpos d (Finset.mem_insert_of_mem hd))
      (fun d hd => hlt d (Finset.mem_insert_of_mem hd))
    obtain ⟨t, ht, hpair, htriple⟩ := choose_new_radius s r c (hlt c (Finset.mem_insert_self _ _))
    let r' : ℂ → ℝ := Function.update r c t
    have hrc : r' c = t := by simp [r']
    have hrd {d : ℂ} (hd : d ∈ s) : r' d = r d :=
      by
      have hdc : d ≠ c := fun h => hcs (h ▸ hd)
      simp [r', hdc]
    have hbound : ∀ d ∈ insert c s, r' d ∈ Ioo (lo d) (hi d) := by
      intro d hd
      rcases Finset.mem_insert.mp hd with rfl | hd
      · simpa only [hrc] using ht
      · simpa only [hrd hd] using hr d hd
    refine ⟨r', hbound, ?_, ?_, ?_⟩
    · intro d hd
      exact (hpos d hd).trans (hbound d hd).1
    · intro x hx y hy hxy
      by_cases hxC : x = c
      · subst x
        have hyS : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hxy.symm
        simpa only [hrc, hrd hyS] using hpair y hyS
      · have hxS : x ∈ s := (Finset.mem_insert.mp hx).resolve_left hxC
        by_cases hyC : y = c
        · subst y
          have hp := hpair x hxS
          simpa only [hrc, hrd hxS, dist_comm, add_comm, abs_sub_comm] using hp
        · have hyS : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyC
          simpa only [hrd hxS, hrd hyS] using hG.2.1 x hxS y hyS hxy
    · intro x hx y hy z hz hxy hxz hyz
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      by_cases hxC : x = c
      · subst x
        have hyS : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hxy.symm
        have hzS : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hxz.symm
        have hh : w ∈ sphere c t ∩ sphere y (r y) ∩ sphere z (r z) := by
          simpa only [hrc, hrd hyS, hrd hzS] using hw
        rw [htriple y hyS z hzS hyz] at hh
        exact hh
      · have hxS : x ∈ s := (Finset.mem_insert.mp hx).resolve_left hxC
        by_cases hyC : y = c
        · subst y
          have hzS : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hyz.symm
          have hh : w ∈ sphere c t ∩ sphere x (r x) ∩ sphere z (r z) := by
            have h := hw
            simp only [hrc, hrd hxS, hrd hzS] at h
            exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
          rw [htriple x hxS z hzS hxz] at hh
          exact hh
        · have hyS : y ∈ s := (Finset.mem_insert.mp hy).resolve_left hyC
          by_cases hzC : z = c
          · subst z
            have hh : w ∈ sphere c t ∩ sphere x (r x) ∩ sphere y (r y) := by
              have h := hw
              simp only [hrc, hrd hxS, hrd hyS] at h
              exact ⟨⟨h.2, h.1.1⟩, h.1.2⟩
            rw [htriple x hxS y hyS hxy] at hh
            exact hh
          · have hzS : z ∈ s := (Finset.mem_insert.mp hz).resolve_left hzC
            have hh : w ∈ sphere x (r x) ∩ sphere y (r y) ∩ sphere z (r z) := by
              simpa only [hrd hxS, hrd hyS, hrd hzS] using hw
            rw [hG.2.2 x hxS y hyS z hzS hxy hxz hyz] at hh
            exact hh

/-- An auxiliary compact connected core can be thickened by a finite disk
cover without losing connectedness. The centers remain on the core. -/
lemma thicken_connected_compact_generalPosition {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hconn : IsConnected K) (hsub : K ⊆ Ω) :
    ∃ (s : Finset ℂ) (r : ℂ → ℝ),
      DiskStage Ω s r ∧ K ⊆ diskUnion s r ∧ GeneralPosition s r := by
  classical
  have hr : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : ℂ) r ⊆ Ω := by
    intro x
    obtain ⟨R, hR, hx⟩ := Metric.isOpen_iff.mp hΩ x (hsub x.property)
    exact ⟨R / 2, half_pos hR, (closedBall_subset_ball (by linarith)).trans hx⟩
  choose ρ hρ hρΩ using hr
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (ρ x / 2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (half_pos (hρ ⟨x, hx⟩))⟩)
  let s : Finset ℂ := t.image Subtype.val
  let R : ℂ → ℝ := fun x => if hx : x ∈ K then ρ ⟨x, hx⟩ else 1
  have hval (x : K) : R x = ρ x := by simp [R]
  have hposR : ∀ c ∈ s, 0 < R c := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    simpa only [hval] using hρ x
  obtain ⟨r, hr, hG⟩ := generalPosition_radii s (fun c => R c / 2) R
    (fun c hc => half_pos (hposR c hc)) (fun c hc => by linarith [hposR c hc])
  have hpos : ∀ c ∈ s, 0 < r c := hG.1
  have hcover : K ⊆ diskUnion s r := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (ht hx)
    have hcS : (c : ℂ) ∈ s := Finset.mem_image.mpr ⟨c, hc, rfl⟩
    refine mem_iUnion₂.mpr ⟨c, hcS, ?_⟩
    apply (ball_subset_ball ?_) hxc
    simpa only [hval] using (hr c hcS).1.le
  have hball : ∀ c ∈ s, closedBall c (r c) ⊆ Ω := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    have hxS : (x : ℂ) ∈ s := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    apply (closedBall_subset_closedBall ?_).trans (hρΩ x)
    simpa only [hval] using (hr x hxS).2.le
  have hpre : IsPreconnected (diskUnion s r) := by
    obtain ⟨a, ha⟩ := hconn.nonempty
    have hp : ∀ c ∈ s, IsPreconnected (K ∪ ball c (r c)) := by
      intro c hc
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
      have hxS : (x : ℂ) ∈ s := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact hconn.isPreconnected.union (x : ℂ) x.property (mem_ball_self (hpos x hxS))
        (convex_ball (x : ℂ) (r x)).isPreconnected
    have hu' : IsPreconnected (⋃ c : (↑s : Set ℂ), K ∪ ball (c : ℂ) (r c)) :=
      isPreconnected_iUnion ⟨a, mem_iInter.mpr (fun _ => Or.inl ha)⟩
        (fun c => hp c c.property)
    have hu : IsPreconnected (⋃ c ∈ s, K ∪ ball c (r c)) := by
      simpa only [iUnion_subtype, Finset.mem_coe] using hu'
    have he : (⋃ c ∈ s, K ∪ ball c (r c)) = diskUnion s r := by
      ext x
      constructor
      · intro hx
        obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hx
        exact hx.elim (fun hk => hcover hk) (fun hx => mem_iUnion₂.mpr ⟨c, hc, hx⟩)
      · intro hx
        obtain ⟨c, hc, hx⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨c, hc, Or.inr hx⟩
    exact he ▸ hu
  exact ⟨s, r, ⟨hpos, ⟨hconn.nonempty.mono hcover, diskUnion_open s r, hpre⟩,
    diskUnion_closure_compact s r, diskUnion_closure_subset s r hball⟩, hcover, hG⟩

lemma thicken_connected_compact {Ω K : Set ℂ} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hconn : IsConnected K) (hsub : K ⊆ Ω) :
    ∃ (s : Finset ℂ) (r : ℂ → ℝ),
      (∀ c ∈ s, 0 < r c) ∧ K ⊆ diskUnion s r ∧ IsDomain (diskUnion s r) ∧
      IsCompact (closure (diskUnion s r)) ∧ closure (diskUnion s r) ⊆ Ω := by
  obtain ⟨s, r, hD, hK, _⟩ := thicken_connected_compact_generalPosition hΩ hK hconn hsub
  exact ⟨s, r, hD.1, hK, hD.2⟩

/-- Joining finitely many covering disks to one basepoint produces a compact
connected subset of the domain containing the prescribed compact set. -/
lemma connected_compact_core (Ω K : Set ℂ) (hΩ : IsDomain Ω)
    (hK : IsCompact K) (hsub : K ⊆ Ω) :
    ∃ L : Set ℂ, IsCompact L ∧ IsConnected L ∧ K ⊆ L ∧ L ⊆ Ω := by
  classical
  obtain ⟨a, ha⟩ := hΩ.1
  have hr : ∀ x : K, ∃ r : ℝ, 0 < r ∧ closedBall (x : ℂ) r ⊆ Ω := by
    intro x
    obtain ⟨R, hR, hx⟩ := Metric.isOpen_iff.mp hΩ.2.1 x (hsub x.property)
    exact ⟨R / 2, half_pos hR, (closedBall_subset_ball (by linarith)).trans hx⟩
  choose ρ hρ hρΩ using hr
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) (ρ x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρ ⟨x, hx⟩)⟩)
  have hj : ∀ x : K, JoinedIn Ω a x := fun x =>
    joinedIn_of_open_isPreconnected Ω hΩ.2.1 hΩ.2.2 a ha x (hsub x.property)
  choose p hp using hj
  let P : K → Set ℂ := fun x => closedBall (x : ℂ) (ρ x) ∪ range (p x)
  have hPa (x : K) : a ∈ P x :=
    Or.inr ⟨0, (p x).source⟩
  have hPx (x : K) : (x : ℂ) ∈ P x :=
    Or.inl (mem_closedBall_self (hρ x).le)
  have hPc (x : K) : IsCompact (P x) :=
    (isCompact_closedBall _ _).union (isCompact_range (p x).continuous)
  have hPconn (x : K) : IsPreconnected (P x) :=
    (isConnected_closedBall (hρ x).le).isPreconnected.union (x : ℂ)
      (mem_closedBall_self (hρ x).le) ⟨1, (p x).target⟩
      (isConnected_range (p x).continuous).isPreconnected
  have hPΩ (x : K) : P x ⊆ Ω := by
    rintro z (hz | ⟨u, rfl⟩)
    · exact hρΩ x hz
    · exact hp x u
  let L : Set ℂ := {a} ∪ ⋃ x ∈ t, P x
  have hLc : IsCompact L :=
    isCompact_singleton.union (t.isCompact_biUnion fun x _ => hPc x)
  have hLpre : IsPreconnected L := by
    have hU' : IsPreconnected (⋃ x : (↑t : Set K), P x) :=
      isPreconnected_iUnion ⟨a, mem_iInter.mpr (fun x => hPa x)⟩
        (fun x => hPconn x)
    have hU : IsPreconnected (⋃ x ∈ t, P x) := by
      simpa only [iUnion_subtype, Finset.mem_coe] using hU'
    by_cases ht0 : t = ∅
    · simpa [L, ht0] using (isPreconnected_singleton (x := a))
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr ht0
      exact isPreconnected_singleton.union a (mem_singleton a)
        (mem_iUnion₂.mpr ⟨x, hx, hPa x⟩) hU
  refine ⟨L, hLc, ⟨⟨a, Or.inl (mem_singleton a)⟩, hLpre⟩, ?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (ht hz)
    exact Or.inr (mem_iUnion₂.mpr ⟨x, hx, Or.inl (ball_subset_closedBall hzx)⟩)
  · rintro z (hz | hz)
    · exact (mem_singleton_iff.mp hz) ▸ ha
    · obtain ⟨x, _, hz⟩ := mem_iUnion₂.mp hz
      exact hPΩ x hz

theorem connected_finite_disk_thickening :
    Specs.D12Complex.Ch14.CircularExhaustion.connected_finite_disk_thickening_type := by
  intro Ω K hΩ hK hKΩ
  obtain ⟨L, hLc, hLconn, hKL, hLΩ⟩ := connected_compact_core Ω K hΩ hK hKΩ
  obtain ⟨s, r, hr, hL, hD, hc, hsub⟩ :=
    thicken_connected_compact hΩ.2.1 hLc hLconn hLΩ
  exact ⟨s, r, hr, hKL.trans hL, hD, hc, hsub⟩

/-- Dependent recursion on compact stages, including the preceding closure at
every successor, preserves any available additional disk-family property. -/
theorem exhaustion_of_thickening :
    Specs.D12Complex.Ch14.CircularExhaustion.exhaustion_of_thickening_type := by
  intro Ω hΩ P hthick
  let C : ℕ → Set ℂ := fun j => Ch11.compactExhaustionStage Ω (j + 1)
  have hCc (j : ℕ) : IsCompact (C j) :=
    Ch11.CompactExhaustion.compact Ω hΩ.2.1 (j + 1) (by omega)
  have hCΩ (j : ℕ) : C j ⊆ Ω := fun _ hz => hz.1
  let A := {p : Finset ℂ × (ℂ → ℝ) // DiskStage Ω p.1 p.2 ∧ P p.1 p.2}
  have hcover : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ a : A, K ⊆ diskUnion a.val.1 a.val.2 := by
    intro K hc hs
    obtain ⟨s, r, hD, hK, hP⟩ := hthick K hc hs
    exact ⟨⟨(s, r), hD, hP⟩, hK⟩
  obtain ⟨a₀, ha₀⟩ := hcover (C 0) (hCc 0) (hCΩ 0)
  have hnext : ∀ (j : ℕ) (a : A), ∃ b : A,
      C (j + 1) ∪ closure (diskUnion a.val.1 a.val.2) ⊆ diskUnion b.val.1 b.val.2 := by
    intro j a
    exact hcover _ ((hCc (j + 1)).union a.property.1.2.2.1)
      (union_subset (hCΩ (j + 1)) a.property.1.2.2.2)
  choose next hnext using hnext
  let a : ℕ → A := Nat.rec a₀ (fun j prev => next j prev)
  have ha0 : a 0 = a₀ := rfl
  have hasucc (j : ℕ) : a (j + 1) = next j (a j) := rfl
  let s : ℕ → Finset ℂ := fun j => (a j).val.1
  let r : ℕ → ℂ → ℝ := fun j => (a j).val.2
  have hstage (j : ℕ) : DiskStage Ω (s j) (r j) := (a j).property.1
  have hnest (j : ℕ) : closure (diskUnion (s j) (r j)) ⊆
      diskUnion (s (j + 1)) (r (j + 1)) := by
    exact (subset_union_right.trans (hnext j (a j)))
  have hCcover : ∀ j, C j ⊆ diskUnion (s j) (r j) := by
    intro j
    cases j with
    | zero => exact ha₀
    | succ j => exact subset_union_left.trans (hnext j (a j))
  have hcofinal : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ j, K ⊆ diskUnion (s j) (r j) := by
    intro K hK hs
    obtain ⟨j, hj, hKj⟩ := Ch11.CompactExhaustion.cofinal Ω hΩ.2.1 K hK hs
    exact ⟨j, hKj.trans ((Ch11.CompactExhaustion.stage_mono Ω hj
      (Nat.le_succ j)).trans (hCcover j))⟩
  refine ⟨s, r, ⟨?_, ?_, hcofinal⟩, fun j => (a j).property.2⟩
  · exact fun j => ⟨hstage j, hnest j⟩
  · apply Subset.antisymm
    · exact iUnion_subset fun j => subset_closure.trans (hstage j).2.2.2
    · intro z hz
      obtain ⟨j, hj⟩ := hcofinal {z} isCompact_singleton (singleton_subset_iff.mpr hz)
      exact mem_iUnion.mpr ⟨j, hj (mem_singleton z)⟩

theorem finite_disk_exhaustion :
    Specs.D12Complex.Ch14.CircularExhaustion.finite_disk_exhaustion_type := by
  intro Ω hΩ
  obtain ⟨s, r, h, _⟩ := exhaustion_of_thickening Ω hΩ (fun _ _ => True) (by
    intro K hK hs
    obtain ⟨s, r, hp, hK, hd, hc, hs⟩ := connected_finite_disk_thickening Ω K hΩ hK hs
    exact ⟨s, r, ⟨hp, hd, hc, hs⟩, hK, trivial⟩)
  exact ⟨s, r, h⟩

/-- All compact disk neighborhoods can simultaneously be chosen connected and
in general position, without changing the domain hypothesis. -/
theorem connected_finite_disk_thickening_generalPosition :
    Specs.D12Complex.Ch14.CircularExhaustion.connected_finite_disk_thickening_generalPosition_type := by
  intro Ω K hΩ hK hKΩ
  obtain ⟨L, hc, hconn, hKL, hLΩ⟩ := connected_compact_core Ω K hΩ hK hKΩ
  obtain ⟨s, r, hD, hL, hG⟩ := thicken_connected_compact_generalPosition hΩ.2.1 hc hconn hLΩ
  exact ⟨s, r, hD, hKL.trans hL, hG⟩

theorem generalPosition_exhaustion :
    Specs.D12Complex.Ch14.CircularExhaustion.generalPosition_exhaustion_type := by
  intro Ω hΩ
  exact exhaustion_of_thickening Ω hΩ GeneralPosition (fun K hc hs =>
    connected_finite_disk_thickening_generalPosition Ω K hΩ hc hs)

/-- A boundary point of a finite disk union lies on one of the circles. -/
lemma frontier_diskUnion_subset_circles (s : Finset ℂ) (r : ℂ → ℝ) :
    frontier (diskUnion s r) ⊆ ⋃ c ∈ s, sphere c (r c) :=
  (s.frontier_biUnion_subset (fun c => ball c (r c))).trans
    (iUnion₂_mono fun _ _ => frontier_ball_subset_sphere)

/-- The finite intersection set contains every possible nonsmooth boundary point. -/
lemma finite_double_circle_points (s : Finset ℂ) (r : ℂ → ℝ) :
    (⋃ c ∈ s, ⋃ d ∈ s, if c = d then ∅ else sphere c (r c) ∩ sphere d (r d)).Finite := by
  classical
  apply s.finite_toSet.biUnion
  intro c _
  apply s.finite_toSet.biUnion
  intro d _
  by_cases hcd : c = d
  · simp [hcd]
  · simpa only [ite_eq_right hcd] using finite_circle_intersection hcd (r c) (r d)

theorem local_boundary_disk_model :
    Specs.D12Complex.Ch14.CircularExhaustion.local_boundary_disk_model_type := by
  classical
  intro s r hG ξ hξ
  let t : Finset ℂ := s.filter (fun c => ξ ∈ sphere c (r c))
  have htS : t ⊆ s := Finset.filter_subset _ _
  have htξ : ∀ c ∈ t, ξ ∈ sphere c (r c) := fun c hc => (Finset.mem_filter.mp hc).2
  have htne : t.Nonempty := by
    obtain ⟨c, hc, hξc⟩ := mem_iUnion₂.mp (frontier_diskUnion_subset_circles s r hξ)
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, hξc⟩⟩
  have htcard : t.card ≤ 2 := by
    by_contra h
    obtain ⟨c, d, e, hc, hd, he, hcd, hce, hde⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < t.card)
    have hh : ξ ∈ sphere c (r c) ∩ sphere d (r d) ∩ sphere e (r e) :=
      ⟨⟨htξ c hc, htξ d hd⟩, htξ e he⟩
    rw [hG.2.2 c (htS hc) d (htS hd) e (htS he) hcd hce hde] at hh
    exact hh
  have hξnot : ξ ∉ diskUnion s r := by
    simpa only [(diskUnion_open s r).interior_eq] using hξ.2
  let U : Set ℂ := ⋂ c ∈ s \ t, (closedBall c (r c))ᶜ
  have hU : IsOpen U := isOpen_biInter_finset (fun _ _ => isClosed_closedBall.isOpen_compl)
  have hξU : ξ ∈ U := by
    apply mem_iInter₂.mpr
    intro c hc
    obtain ⟨hcS, hct⟩ := Finset.mem_sdiff.mp hc
    change ¬dist ξ c ≤ r c
    have hn : ¬dist ξ c < r c := fun h => hξnot (mem_iUnion₂.mpr ⟨c, hcS, h⟩)
    have hne : dist ξ c ≠ r c := by
      intro he
      exact hct (Finset.mem_filter.mpr ⟨hcS, he⟩)
    exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne) |>.not_ge
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU ξ hξU
  refine ⟨t, δ, htS, htne, htcard, hδ, htξ, ?_⟩
  intro z hz
  constructor
  · intro h
    obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.mp h
    by_cases hct : c ∈ t
    · exact mem_iUnion₂.mpr ⟨c, hct, hzc⟩
    · have he := mem_iInter₂.mp (hball hz) c (Finset.mem_sdiff.mpr ⟨hc, hct⟩)
      exact False.elim (he (ball_subset_closedBall hzc))
  · exact fun h => (iUnion₂_mono' fun c hc => ⟨c, htS hc, Subset.rfl⟩) h

/-- Assembly of the exhaustion construction with boundary geometry and the
canonical exterior-cone regularity theorem. -/
theorem circular_exhaustion_of_boundary_geometry :
    Specs.D12Complex.Ch14.CircularExhaustion.circular_exhaustion_of_boundary_geometry_type := by
  intro hgeom Ω hΩ
  obtain ⟨s, r, ht, hG⟩ := generalPosition_exhaustion Ω hΩ
  refine ⟨s, r, ?_, ht.2.1, ht.2.2⟩
  intro j
  obtain ⟨ha, hs, hc⟩ := hgeom (s j) (r j) (hG j)
  have hD := (ht.1 j).1
  refine ⟨hG j, hD.2.1, hD.2.2.1, hD.2.2.2, (ht.1 j).2, ha, hs, hc, ?_⟩
  intro ξ hξ
  exact GeometricBarriers.exterior_cone_regular _ ξ hD.2.1.2.1 hξ (hc ξ hξ)

/-- The empty triple-circle intersections in the parent interface exclude
exactly the distance-equality triples in the two geometry interfaces. -/
lemma no_triple_circle_point {s : Finset ℂ} {r : ℂ → ℝ}
    (hG : GeneralPosition s r) {c d e : ℂ} (hc : c ∈ s) (hd : d ∈ s)
    (he : e ∈ s) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ¬ ∃ z : ℂ, dist z c = r c ∧ dist z d = r d ∧ dist z e = r e := by
  rintro ⟨z, hzc, hzd, hze⟩
  have hz : z ∈ sphere c (r c) ∩ sphere d (r d) ∩ sphere e (r e) :=
    ⟨⟨hzc, hzd⟩, hze⟩
  rw [hG.2.2 c hc d hd e he hcd hce hde] at hz
  exact hz

/-- Import the actual closed-arc decomposition, retaining endpoint analyticity,
nonzero velocities and injectivity on each open parameter interval. -/
lemma finiteCircularArcs_of_generalPosition (s : Finset ℂ) (r : ℂ → ℝ)
    (hG : GeneralPosition s r) : FiniteCircularArcs (diskUnion s r) := by
  have hA : D12Complex.FiniteCircularArcs.Arrangement s r :=
    ⟨hG.1, hG.2.1, fun _ hc _ hd _ he hcd hce hde =>
      no_triple_circle_point hG hc hd he hcd hce hde⟩
  obtain ⟨n, c, R, a, b, hpos, heq, hreg⟩ :=
    D12Complex.FiniteCircularArcs.finite_circular_arcs s r hA
  refine ⟨n, c, R, a, b, hpos, heq, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨U, _, hIU, hU, _⟩ := (hreg i).1
    exact hU.mono hIU
  · intro i t ht
    obtain ⟨U, _, hIU, _, hU⟩ := (hreg i).1
    exact hU t (hIU ht)
  · exact fun i => (hreg i).2

/-- The sector descriptions use the same polar formula; this bridge only
reorders its existential witnesses. -/
lemma sectorChart_of_geometry {D : Set ℂ} {ξ : ℂ} {θ : ℝ}
    (h : Specs.D12Complex.Ch14.DiskUnionBoundarySectors.SectorChart D ξ θ) :
    SectorChart D ξ θ := by
  obtain ⟨U, V, f, g, hξ, hbi, hf, hder, hside⟩ := h
  refine ⟨U, V, f, g, hξ, hbi, hf, hder, ?_⟩
  intro z hz
  refine (hside z hz).trans ?_
  constructor
  · rintro ⟨ρ, hρ, t, ht, htθ, heq⟩
    exact ⟨ρ, t, hρ, ht, htθ, heq⟩
  · rintro ⟨ρ, t, hρ, ht, htθ, heq⟩
    exact ⟨ρ, hρ, t, ht, htθ, heq⟩

/-- Full geometric conclusion for every general-position finite disk union,
including empty and disconnected unions. -/
theorem boundary_geometry :
    Specs.D12Complex.Ch14.CircularExhaustion.boundary_geometry_type := by
  classical
  intro s r hG
  have hA : Specs.D12Complex.Ch14.DiskUnionBoundarySectors.GeneralPosition s r :=
    ⟨hG.1, hG.2.1, fun _ hc _ hd _ he hcd hce hde =>
      no_triple_circle_point hG hc hd he hcd hce hde⟩
  obtain ⟨hsectors, hcones⟩ :=
    D12Complex.DiskUnionBoundarySectors.disk_union_boundary_sectors s r hA
  refine ⟨finiteCircularArcs_of_generalPosition s r hG, ?_, hcones⟩
  obtain ⟨F, hF, hFbd, hsmooth, hcorner⟩ := hsectors
  refine ⟨hF.toFinset, ?_, ?_, ?_⟩
  · exact fun _ hξ => hFbd (hF.mem_toFinset.mp hξ)
  · intro ξ hξ hξF
    apply sectorChart_of_geometry
    exact hsmooth ξ ⟨hξ, by simpa only [hF.mem_toFinset] using hξF⟩
  · intro ξ hξF
    obtain ⟨θ, hθ, hθ2, hchart⟩ := hcorner ξ (hF.mem_toFinset.mp hξF)
    exact ⟨θ, hθ, hθ2, sectorChart_of_geometry hchart⟩

/-- Every plane domain has the connected, compact-cofinal, closure-nested
circular exhaustion with analytic arcs, genuine sector charts, exterior cones
and regular boundary points asserted in paper.tex:2660–2669. -/
theorem circular_exhaustion :
    Specs.D12Complex.Ch14.CircularExhaustion.circular_exhaustion_type :=
  circular_exhaustion_of_boundary_geometry boundary_geometry

end D12Complex.CircularExhaustion
