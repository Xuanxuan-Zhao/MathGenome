import LinearAlgebraicGroups.Geometry.Projection
import Mathlib.Analysis.Real.Sqrt
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-! Circumcenters of bounded sets in complete CAT(0) spaces. -/

open Bornology Filter Set unitInterval
open scoped Pointwise Topology

noncomputable section

namespace LinearAlgebraicGroups.Geometry

variable {X : Type*} [MetricSpace X] {A C : Set X}

/-- The supremum of distances from a proposed center to a bounded set. -/
noncomputable def enclosingRadius (A : Set X) (x : X) : ℝ :=
  ⨆ a : A, dist x (a : X)

/-- A circumcenter minimizes the enclosing radius over the whole space. -/
def IsCircumcenter (A : Set X) (c : X) : Prop :=
  ∀ x : X, enclosingRadius A c ≤ enclosingRadius A x

/-- Choose a global minimizer of the enclosing radius when one exists, or a point of the
set otherwise. The minimizer exists for nonempty bounded sets in complete CAT(0) spaces. -/
noncomputable def circumcenter (A : Set X) (hA : A.Nonempty) : X := by
  classical
  exact if h : ∃ c, IsCircumcenter A c then Classical.choose h else Classical.choose hA

private theorem dist_le_enclosingRadius (hA : IsBounded A) (x : X) (a : A) :
    dist x (a : X) ≤ enclosingRadius A x := by
  obtain ⟨r, hr⟩ := hA.subset_closedBall x
  apply le_ciSup _ a
  refine ⟨r, ?_⟩
  rintro _ ⟨b, rfl⟩
  simpa only [Metric.mem_closedBall, dist_comm] using hr b.prop

private theorem enclosingRadius_le (hA : A.Nonempty) {x : X} {r : ℝ}
    (hr : ∀ a : A, dist x (a : X) ≤ r) : enclosingRadius A x ≤ r := by
  let : Nonempty A := hA.to_subtype
  exact ciSup_le hr

private theorem enclosingRadius_nonneg (hA : A.Nonempty) (hb : IsBounded A) (x : X) :
    0 ≤ enclosingRadius A x := by
  obtain ⟨a, ha⟩ := hA
  exact dist_nonneg.trans (dist_le_enclosingRadius hb x ⟨a, ha⟩)

private theorem isLUB_dist_sq (hA : A.Nonempty) (hb : IsBounded A) (x : X) :
    IsLUB (range fun a : A => dist x (a : X) ^ 2) (enclosingRadius A x ^ 2) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact (sq_le_sq₀ dist_nonneg (enclosingRadius_nonneg hA hb x)).2
      (dist_le_enclosingRadius hb x a)
  · intro r hr
    obtain ⟨a, ha⟩ := hA
    have hr₀ : 0 ≤ r := (sq_nonneg (dist x a)).trans (hr (mem_range_self (⟨a, ha⟩ : A)))
    rw [← Real.sq_sqrt hr₀]
    exact (sq_le_sq₀ (enclosingRadius_nonneg ⟨a, ha⟩ hb x) (Real.sqrt_nonneg r)).2
      (enclosingRadius_le ⟨a, ha⟩ fun b => Real.le_sqrt_of_sq_le (hr (mem_range_self b)))

/-- Squaring the enclosing radius gives the supremum of squared distances. -/
theorem enclosingRadius_sq_eq (hA : A.Nonempty) (hb : IsBounded A) (x : X) :
    enclosingRadius A x ^ 2 = ⨆ a : A, dist x (a : X) ^ 2 := by
  let : Nonempty A := hA.to_subtype
  exact ((isLUB_dist_sq hA hb x).csSup_eq (range_nonempty _)).symm

private theorem dist_sq_le_enclosingRadius_sq (hA : A.Nonempty) (hb : IsBounded A)
    (x : X) (a : A) : dist x (a : X) ^ 2 ≤ enclosingRadius A x ^ 2 :=
  (isLUB_dist_sq hA hb x).1 (mem_range_self a)

private theorem enclosingRadius_sq_le (hA : A.Nonempty) (hb : IsBounded A) {x : X} {r : ℝ}
    (hr : ∀ a : A, dist x (a : X) ^ 2 ≤ r) : enclosingRadius A x ^ 2 ≤ r :=
  (isLUB_dist_sq hA hb x).2 (by rintro _ ⟨a, rfl⟩; exact hr a)

private theorem enclosingRadius_lipschitz (hA : A.Nonempty) (hb : IsBounded A) :
    LipschitzWith 1 (enclosingRadius A) := by
  have h (x y : X) : enclosingRadius A x ≤ enclosingRadius A y + dist x y :=
    enclosingRadius_le hA fun a =>
      (dist_triangle x y (a : X)).trans (by
        rw [add_comm (enclosingRadius A y)]
        exact add_le_add le_rfl (dist_le_enclosingRadius hb y a))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [abs_le]
  constructor
  · linarith only [h y x, dist_comm y x]
  · linarith only [h x y]

private theorem CAT0.enclosingRadius_midpoint (hX : CAT0 X) (hA : A.Nonempty) (hb : IsBounded A)
    {x y : X} (p : GeodesicSegment x y) :
    enclosingRadius A (p.val (⟨1 / 2, by norm_num⟩ : I)) ^ 2 ≤
      (enclosingRadius A x ^ 2 + enclosingRadius A y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  apply enclosingRadius_sq_le hA hb
  intro a
  have hmid := hX.squaredDistanceComparison.midpointComparison (a : X) p
  rw [dist_comm (a : X) x, dist_comm (a : X) y, dist_comm (a : X) (p.val _)] at hmid
  linarith only [hmid, dist_sq_le_enclosingRadius_sq hA hb x a,
    dist_sq_le_enclosingRadius_sq hA hb y a]

/-- In a complete CAT(0) space, every nonempty bounded set has a unique circumcenter. -/
theorem CAT0.existsUnique_circumcenter [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) : ∃! c, IsCircumcenter A c := by
  let F : X → ℝ := fun x => enclosingRadius A x ^ 2
  let r := sInf (range F)
  have hr : BddBelow (range F) := ⟨0, by rintro _ ⟨x, rfl⟩; exact sq_nonneg _⟩
  let : Nonempty X := hA.elim fun x _ => ⟨x⟩
  obtain ⟨v, _, hv, hv_mem⟩ := exists_seq_tendsto_sInf (range_nonempty F) hr
  choose u hu using hv_mem
  have hu_lim : Tendsto (fun n => F (u n)) atTop (𝓝 r) := by
    simpa only [hu] using hv
  have hpair (x y : X) : dist x y ^ 2 ≤ 2 * F x + 2 * F y - 4 * r := by
    obtain ⟨p⟩ := hX.1.2 x y
    have hlow : r ≤ F (p.val (⟨1 / 2, by norm_num⟩ : I)) :=
      csInf_le hr (mem_range_self _)
    have hmid := hX.enclosingRadius_midpoint hA hb p
    change F (p.val (⟨1 / 2, by norm_num⟩ : I)) ≤ (F x + F y) / 2 - dist x y ^ 2 / 4 at hmid
    linarith only [hlow, hmid]
  have hcauchy : CauchySeq u := by
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hu_lim (ε ^ 2 / 4) (by positivity)
    have hupper (n : ℕ) (hn : N ≤ n) : F (u n) - r < ε ^ 2 / 4 :=
      (abs_lt.mp (by simpa only [Real.dist_eq] using hN n hn)).2
    refine ⟨N, fun m hm n hn => (sq_lt_sq₀ dist_nonneg hε.le).1 ?_⟩
    linarith only [hpair (u m) (u n), hupper m hm, hupper n hn]
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hlim : Tendsto (fun n => F (u n)) atTop (𝓝 (F c)) :=
    (((enclosingRadius_lipschitz hA hb).continuous.pow 2).tendsto c).comp hc
  have hcr : F c = r := tendsto_nhds_unique hlim hu_lim
  have hmin : IsCircumcenter A c := fun x =>
    le_of_sq_le_sq (hcr.le.trans (csInf_le hr (mem_range_self x)))
      (enclosingRadius_nonneg hA hb x)
  refine ⟨c, hmin, fun q hq => ?_⟩
  have hqr : F q ≤ r := hcr ▸
    ((sq_le_sq₀ (enclosingRadius_nonneg hA hb q) (enclosingRadius_nonneg hA hb c)).2 (hq c))
  have hzero : dist q c ^ 2 = 0 := by
    linarith only [hpair q c, hqr, hcr, sq_nonneg (dist q c)]
  exact dist_eq_zero.mp (sq_eq_zero_iff.mp hzero)

theorem CAT0.isCircumcenter_circumcenter [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) : IsCircumcenter A (circumcenter A hA) := by
  classical
  have hex := (hX.existsUnique_circumcenter hA hb).exists
  rw [circumcenter, dite_eq_left hex]
  exact Classical.choose_spec hex

private theorem enclosingRadius_image_isometry (hA : A.Nonempty) (hb : IsBounded A)
    {g : X → X} (hisom : Isometry g) (hg : g '' A = A) (x : X) :
    enclosingRadius A (g x) = enclosingRadius A x := by
  apply le_antisymm
  · refine enclosingRadius_le hA fun a => ?_
    have ha : (a : X) ∈ g '' A := hg.symm ▸ a.prop
    obtain ⟨b, hbA, hab⟩ := ha
    rw [← hab, hisom.dist_eq]
    exact dist_le_enclosingRadius hb x ⟨b, hbA⟩
  · refine enclosingRadius_le hA fun a => ?_
    have ha : g a ∈ A := by
      simpa only [hg] using mem_image_of_mem g a.prop
    simpa only [hisom.dist_eq] using dist_le_enclosingRadius hb (g x) ⟨g a, ha⟩

/-- Any isometry preserving the bounded set fixes its circumcenter. -/
theorem CAT0.circumcenter_fixed [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) {g : X → X} (hisom : Isometry g) (hg : g '' A = A) :
    g (circumcenter A hA) = circumcenter A hA := by
  let c := circumcenter A hA
  have hc := hX.isCircumcenter_circumcenter hA hb
  have hgc : IsCircumcenter A (g c) := fun x =>
    (enclosingRadius_image_isometry hA hb hisom hg c).le.trans (hc x)
  exact (hX.existsUnique_circumcenter hA hb).unique hgc hc

/-- Projection onto a closed convex set containing A reduces the supremum of squared
distances to A by at least the squared distance to the projection. -/
theorem CAT0.iSup_dist_nearestPoint_sq_le [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) (hAC : A ⊆ C)
    (hclosed : IsClosed C) (hconvex : GeodesicConvex C) (x : X) :
    (⨆ a : A, dist (nearestPoint C x) (a : X) ^ 2) ≤
      (⨆ a : A, dist x (a : X) ^ 2) - dist x (nearestPoint C x) ^ 2 := by
  let : CompleteSpace C := hclosed.completeSpace_coe
  rw [← enclosingRadius_sq_eq hA hb, ← enclosingRadius_sq_eq hA hb]
  apply enclosingRadius_sq_le hA hb
  intro a
  have hp := hX.dist_sq_add_dist_nearestPoint_sq_le (hA.mono hAC) hconvex x (hAC a.prop)
  linarith only [hp, dist_sq_le_enclosingRadius_sq hA hb x a]

theorem CAT0.circumcenter_mem [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) (hAC : A ⊆ C)
    (hclosed : IsClosed C) (hconvex : GeodesicConvex C) : circumcenter A hA ∈ C := by
  let c := circumcenter A hA
  let p := nearestPoint C c
  let : CompleteSpace C := hclosed.completeSpace_coe
  have hproj := hX.iSup_dist_nearestPoint_sq_le hA hb hAC hclosed hconvex c
  rw [← enclosingRadius_sq_eq hA hb, ← enclosingRadius_sq_eq hA hb] at hproj
  have hmin : enclosingRadius A c ^ 2 ≤ enclosingRadius A p ^ 2 :=
    (sq_le_sq₀ (enclosingRadius_nonneg hA hb c) (enclosingRadius_nonneg hA hb p)).2
      (hX.isCircumcenter_circumcenter hA hb p)
  have heq : c = p := dist_eq_zero.mp (sq_eq_zero_iff.mp (by
    change enclosingRadius A p ^ 2 ≤ enclosingRadius A c ^ 2 - dist c p ^ 2 at hproj
    linarith only [hproj, hmin, sq_nonneg (dist c p)]))
  change c ∈ C
  rw [heq]
  exact (hX.isNearestPoint_nearestPoint (hA.mono hAC) hconvex c).1

theorem CAT0.circumcenter_mem_commonMinset [CompleteSpace X] (hX : CAT0 X)
    (hA : A.Nonempty) (hb : IsBounded A) {ι : Type*} (f : ι → X ≃ᵢ X)
    (hsub : A ⊆ commonMinset f) : circumcenter A hA ∈ commonMinset f :=
  hX.circumcenter_mem hA hb hsub (isClosed_commonMinset f) (hX.geodesicConvex_commonMinset f)

section Actions

variable {G : Type*} [Group G] [MulAction G X] [IsIsometricSMul G X] [CompleteSpace X]

theorem CAT0.orbit_circumcenter_fixed (hX : CAT0 X) {x : X}
    (hb : IsBounded (MulAction.orbit G x)) :
    circumcenter (MulAction.orbit G x) (MulAction.nonempty_orbit x) ∈ MulAction.fixedPoints G X := by
  intro g
  exact hX.circumcenter_fixed (MulAction.nonempty_orbit x) hb
    (isometry_smul X g) (MulAction.smul_orbit g x)

theorem CAT0.fixedPoints_nonempty_of_boundedOrbit (hX : CAT0 X)
    (h : ∃ x : X, IsBounded (MulAction.orbit G x)) : (MulAction.fixedPoints G X).Nonempty := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, hX.orbit_circumcenter_fixed hx⟩

theorem CAT0.fixedPoints_nonempty_of_finiteGroup [Finite G] (hX : CAT0 X) :
    (MulAction.fixedPoints G X).Nonempty := by
  obtain ⟨x⟩ := hX.1.1
  exact hX.fixedPoints_nonempty_of_boundedOrbit ⟨x, (Finite.finite_mulAction_orbit (M := G) x).isBounded⟩

theorem CAT0.closedConvex_fixedPoints (hX : CAT0 X) (hne : (MulAction.fixedPoints G X).Nonempty) :
    IsClosed (MulAction.fixedPoints G X) ∧ GeodesicConvex (MulAction.fixedPoints G X) ∧
      CAT0 (MulAction.fixedPoints G X) ∧ CompleteSpace (MulAction.fixedPoints G X) := by
  have hclosed : IsClosed (MulAction.fixedPoints G X) := by
    rw [MulAction.fixed_eq_iInter_fixedBy]
    exact isClosed_iInter fun g : G =>
      isClosed_eq (IsometryEquiv.constSMul (X := X) g).isometry.continuous continuous_id
  have hconvex : GeodesicConvex (MulAction.fixedPoints G X) := by
    intro a b ha hb p t g
    have h := hX.distAlongSegments (p.mapIsometry (IsometryEquiv.constSMul g).isometry) p t
    change dist (g • p.val t) (p.val t) ≤
      (1 - (t : ℝ)) * dist (g • a) a + (t : ℝ) * dist (g • b) b at h
    simp only [ha g, hb g, dist_self, mul_zero, add_zero] at h
    exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
  exact ⟨hclosed, hconvex, hX.closedConvexSubtype hne hclosed hconvex⟩

/-- The center of a finite orbit contained in a family of minsets is fixed by the action
and belongs to their intersection. -/
theorem CAT0.finiteOrbit_circumcenter_mem (hX : CAT0 X) {x : X}
    (hfinite : (MulAction.orbit G x).Finite) {ι : Type*} (f : ι → X ≃ᵢ X)
    (hsub : MulAction.orbit G x ⊆ commonMinset f) :
    circumcenter (MulAction.orbit G x) (MulAction.nonempty_orbit x) ∈
      MulAction.fixedPoints G X ∩ commonMinset f :=
  ⟨hX.orbit_circumcenter_fixed hfinite.isBounded,
    hX.circumcenter_mem_commonMinset (MulAction.nonempty_orbit (M := G) x) hfinite.isBounded f hsub⟩

end Actions

end LinearAlgebraicGroups.Geometry
