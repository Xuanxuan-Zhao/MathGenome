import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.FiniteCircularArcs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Metric Complex
open scoped Topology ComplexConjugate

namespace D12Complex.FiniteCircularArcs

/-- Analyticity is on the whole real line, so includes both ends of every arc. -/
theorem analytic_circle (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℝ (circleMap c R) Set.univ := by
  intro z _
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  exact analyticAt_cexp.restrictScalars.comp
    ((ofRealCLM.analyticAt z).mul analyticAt_const)

theorem circle_hasDerivAt (c : ℂ) (R t : ℝ) :
    HasDerivAt (circleMap c R) ((R : ℂ) * Complex.exp ((t : ℂ) * I) * I) t := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, ofReal_one]
    using! (((ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp.const_mul (R : ℂ)).const_add c

theorem circular_parametrization :
    Specs.D12Complex.Ch14.FiniteCircularArcs.circular_parametrization_type := by
  intro c R a b hR hab hlen
  change AnalyticOnNhd ℝ (circleMap c R) Set.univ ∧
    (∀ t, deriv (circleMap c R) t ≠ 0) ∧ Set.InjOn (circleMap c R) (Ioo a b)
  refine ⟨analytic_circle c R, ?_, ?_⟩
  · intro t
    rw [(circle_hasDerivAt c R t).deriv]
    exact mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hR.ne') (exp_ne_zero _)) I_ne_zero
  · exact (injOn_circleMap_of_abs_sub_le' hR.ne' hlen).mono Ioo_subset_Ico_self

/-- The finite-union closure is the union of the corresponding closed disks. -/
theorem closure_diskUnion (s : Finset ℂ) (r : ℂ → ℝ) (hr : ∀ c ∈ s, 0 < r c) :
    closure (diskUnion s r) = ⋃ c ∈ s, closedBall c (r c) := by
  rw [diskUnion, s.closure_biUnion]
  exact iUnion_congr fun c => iUnion_congr fun hc => closure_ball c (hr c hc).ne'

theorem isOpen_diskUnion (s : Finset ℂ) (r : ℂ → ℝ) : IsOpen (diskUnion s r) := by
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball

theorem mem_frontier_diskUnion :
    Specs.D12Complex.Ch14.FiniteCircularArcs.mem_frontier_diskUnion_type := by
  intro s r hr z
  rw [(isOpen_diskUnion s r).frontier_eq, closure_diskUnion s r hr]
  simp only [mem_sdiff, mem_iUnion, mem_closedBall, diskUnion, mem_ball,
    not_exists, not_lt]
  constructor
  · rintro ⟨⟨c, hc, hz⟩, hout⟩
    exact ⟨⟨c, hc, le_antisymm hz (hout c hc)⟩, hout⟩
  · rintro ⟨⟨c, hc, hz⟩, hout⟩
    exact ⟨⟨c, hc, hz.le⟩, hout⟩

/-- Compactness will turn a proved local arc cover into a finite cover. -/
theorem isCompact_frontier_diskUnion (s : Finset ℂ) (r : ℂ → ℝ)
    (hr : ∀ c ∈ s, 0 < r c) : IsCompact (frontier (diskUnion s r)) := by
  have h : IsCompact (closure (diskUnion s r)) := by
    rw [closure_diskUnion s r hr]
    exact s.finite_toSet.isCompact_biUnion (fun c _ => isCompact_closedBall c (r c))
  exact h.of_isClosed_subset isClosed_frontier frontier_subset_closure

theorem empty_decomposition :
    Specs.D12Complex.Ch14.FiniteCircularArcs.empty_decomposition_type := by
  intro r
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · exact fun i => Fin.elim0 i
  · simp [diskUnion]
  · exact fun i => Fin.elim0 i

/-- Two distinct circles have at most two common points, hence finitely many. -/
theorem finite_circle_intersection (c d : ℂ) (R S : ℝ) (hcd : c ≠ d) :
    ({z : ℂ | dist z c = R ∧ dist z d = S}).Finite := by
  classical
  let T : Set ℂ := {z : ℂ | dist z c = R ∧ dist z d = S}
  by_cases h : ∃ p ∈ T, ∃ q ∈ T, p ≠ q
  · obtain ⟨p, hp, q, hq, hpq⟩ := h
    apply (Set.toFinite ({p, q} : Set ℂ)).subset
    intro z hz
    have he := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
      Complex.finrank_real_complex hcd hpq hp.1 hq.1 hz.1 hp.2 hq.2 hz.2
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using he
  · apply Set.Subsingleton.finite
    intro p hp q hq
    by_contra hpq
    exact h ⟨p, hp, q, hq, hpq⟩

/-- All possible double-circle points in the finite arrangement form a finite set. -/
theorem finite_double_points (s : Finset ℂ) (r : ℂ → ℝ) :
    {z : ℂ | ∃ c ∈ s, ∃ d ∈ s, c ≠ d ∧ dist z c = r c ∧ dist z d = r d}.Finite := by
  classical
  have hf : (⋃ c ∈ s, ⋃ d ∈ s.erase c,
      {z : ℂ | dist z c = r c ∧ dist z d = r d}).Finite := by
    apply s.finite_toSet.biUnion
    intro c hc
    apply (s.erase c).finite_toSet.biUnion
    intro d hd
    exact finite_circle_intersection c d (r c) (r d) (Finset.mem_erase.mp hd).1.symm
  apply hf.subset
  rintro z ⟨c, hc, d, hd, hcd, hz⟩
  exact mem_iUnion.mpr ⟨c, mem_iUnion.mpr ⟨hc,
    mem_iUnion.mpr ⟨d, mem_iUnion.mpr ⟨Finset.mem_erase.mpr ⟨hcd.symm, hd⟩, hz⟩⟩⟩⟩

/-- At most one other circle can be active at any point of a given circle. -/
theorem other_active_unique (s : Finset ℂ) (r : ℂ → ℝ) (h : Arrangement s r)
    {z c d e : ℂ} (hc : c ∈ s) (hd : d ∈ s) (he : e ∈ s)
    (hcd : c ≠ d) (hce : c ≠ e) (hzc : dist z c = r c)
    (hzd : dist z d = r d) (hze : dist z e = r e) : d = e := by
  by_contra hde
  exact h.2.2 c hc d hd e he hcd hce hde ⟨z, hzc, hzd, hze⟩

/-- The radial vectors of two non-tangent circles are not collinear at a common point. -/
theorem radial_cross_ne_zero {u v : ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 0 < S) (hu : ‖u‖ = R) (hv : ‖v‖ = S)
    (hext : ‖u - v‖ ≠ R + S) (hint : ‖u - v‖ ≠ |R - S|) :
    (u * conj v).im ≠ 0 := by
  intro hzero
  have hu2 : normSq u = R ^ 2 := by rw [normSq_eq_norm_sq, hu]
  have hv2 : normSq v = S ^ 2 := by rw [normSq_eq_norm_sq, hv]
  have hprod : (u * conj v).re ^ 2 = (R * S) ^ 2 := by
    have hh := normSq_mul u (conj v)
    rw [normSq_conj, hu2, hv2, normSq_apply, hzero] at hh
    nlinarith [hh]
  have hdist : ‖u - v‖ ^ 2 = R ^ 2 + S ^ 2 - 2 * (u * conj v).re := by
    rw [← normSq_eq_norm_sq, normSq_sub, hu2, hv2]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hprod with hp | hp
  · apply hint
    have habs := sq_abs (R - S)
    nlinarith [norm_nonneg (u - v), abs_nonneg (R - S)]
  · apply hext
    nlinarith [norm_nonneg (u - v)]

/-- Primitive version of transverse intersection, directly from Arrangement. -/
theorem circle_radials_transverse (s : Finset ℂ) (r : ℂ → ℝ) (h : Arrangement s r)
    {z c d : ℂ} (hc : c ∈ s) (hd : d ∈ s) (hcd : c ≠ d)
    (hzc : dist z c = r c) (hzd : dist z d = r d) :
    ((z - c) * conj (z - d)).im ≠ 0 := by
  apply radial_cross_ne_zero (h.1 c hc) (h.1 d hd)
    (by simpa only [dist_eq_norm] using hzc)
    (by simpa only [dist_eq_norm] using hzd)
  · simpa only [sub_sub_sub_cancel_left, ← dist_eq_norm, dist_comm] using
      (h.2.1 c hc d hd hcd).1
  · simpa only [sub_sub_sub_cancel_left, ← dist_eq_norm, dist_comm] using
      (h.2.1 c hc d hd hcd).2

/-- The real derivative of squared modulus, obtained from its two coordinates. -/
theorem normSq_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun x => normSq (f x)) (2 * (f' * conj (f t)).re) t := by
  have hre : HasDerivAt (fun x => (f x).re) f'.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have him : HasDerivAt (fun x => (f x).im) f'.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  convert (hre.pow 2).add (him.pow 2) using 1
  · ext x
    simp [Complex.normSq_apply, pow_two]
  · simp only [Nat.cast_ofNat,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring

/-- The distance-squared constraint has a simple zero at a transverse crossing. -/
theorem circle_power_hasDerivAt (c d : ℂ) (R S t : ℝ) :
    HasDerivAt (fun x => normSq (circleMap c R x - d) - S ^ 2)
      (-2 * ((circleMap c R t - c) * conj (circleMap c R t - d)).im) t := by
  have hh := (normSq_hasDerivAt ((circle_hasDerivAt c R t).sub_const d)).sub_const (S ^ 2)
  convert hh using 1
  simp only [circleMap_sub_center, circleMap_zero, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

/-- A simple real zero has the expected sign on each side, including the zero itself. -/
theorem sign_near_simple_zero {f : ℝ → ℝ} {k t : ℝ}
    (hf : HasDerivAt f k t) (hzero : f t = 0) (hk : k ≠ 0) :
    ∃ δ > 0, ∀ x, |x - t| < δ →
      (0 ≤ f x ↔ 0 ≤ k * (x - t)) := by
  have heps : 0 < |k| / 2 := by positivity
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp hf.tendsto_slope (|k| / 2) heps
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hxt : x = t
  · subst x
    simp [hzero]
  have hh := hd (by simpa using hxt) (by simpa [Real.dist_eq] using hx)
  simp only [slope_def_field, hzero, sub_zero, Real.dist_eq, abs_lt] at hh
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · have hquot : f x / (x - t) < 0 := by rw [abs_of_neg hneg] at hh; linarith
    rcases lt_or_gt_of_ne hxt with hleft | hright
    · -- Use the strict quotient inequality with the negative denominator.
      have : 0 < f x := (div_neg_iff.mp hquot).resolve_right (by intro h; linarith)
        |>.1
      exact ⟨fun _ => (mul_pos_of_neg_of_neg hneg (sub_neg.mpr hleft)).le, fun _ => this.le⟩
    · have hfx : f x < 0 := (div_neg_iff.mp hquot).resolve_left (by intro h; linarith) |>.1
      constructor
      · intro h; linarith
      · intro h
        have := mul_neg_of_neg_of_pos hneg (sub_pos.mpr hright)
        linarith
  · have hquot : 0 < f x / (x - t) := by rw [abs_of_pos hpos] at hh; linarith
    rcases lt_or_gt_of_ne hxt with hleft | hright
    · have hfx : f x < 0 := (div_pos_iff.mp hquot).resolve_left (by intro h; linarith) |>.1
      constructor
      · intro h; linarith
      · intro h
        have := mul_neg_of_pos_of_neg hpos (sub_neg.mpr hleft)
        linarith
    · have hfx : 0 < f x := (div_pos_iff.mp hquot).resolve_right (by intro h; linarith) |>.1
      exact ⟨fun _ => (mul_pos hpos (sub_pos.mpr hright)).le, fun _ => hfx.le⟩

@[fun_prop]
theorem continuous_circle (c : ℂ) (R : ℝ) : Continuous (circleMap c R) := by
  change Continuous (fun t : ℝ => c + (R : ℂ) * exp ((t : ℂ) * I))
  fun_prop

theorem nonneg_power_iff {z d : ℂ} {S : ℝ} (hS : 0 ≤ S) :
    0 ≤ normSq (z - d) - S ^ 2 ↔ S ≤ dist z d := by
  rw [normSq_eq_norm_sq, ← dist_eq_norm]
  constructor <;> intro h <;> nlinarith [(dist_nonneg : 0 ≤ dist z d)]

/-- Every inactive disk remains strictly inactive on a common parameter neighborhood. -/
theorem inactive_margin (s : Finset ℂ) (r : ℂ → ℝ) (c : ℂ) (R t : ℝ)
    (ht : ∀ d ∈ s, r d ≤ dist (circleMap c R t) d) :
    ∃ η > 0, ∀ u, |u - t| < η → ∀ d ∈ s,
      dist (circleMap c R t) d ≠ r d → r d < dist (circleMap c R u) d := by
  have he : ∀ᶠ u in 𝓝 t, ∀ d ∈ s,
      dist (circleMap c R t) d ≠ r d → r d < dist (circleMap c R u) d := by
    apply s.eventually_all.mpr
    intro d hd
    by_cases hact : dist (circleMap c R t) d = r d
    · exact Filter.Eventually.of_forall (fun _ h => (h hact).elim)
    · have hstrict : r d < dist (circleMap c R t) d := lt_of_le_of_ne (ht d hd) (Ne.symm hact)
      have hn : ∀ᶠ u in 𝓝 t, r d < dist (circleMap c R u) d :=
        (isOpen_lt continuous_const ((continuous_circle c R).dist continuous_const)).mem_nhds hstrict
      exact hn.mono (fun u hu _ => hu)
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp he
  exact ⟨η, hη, fun u hu => hsub (by simpa only [mem_ball, Real.dist_eq] using hu)⟩

/-- A parameter of the exposed part of a circle has a whole short interval,
or a closed one-sided interval at a crossing, which covers its nearby exposed
parameters. This rules out an unaccounted isolated endpoint. -/
theorem local_exposed_interval (s : Finset ℂ) (r : ℂ → ℝ) (h : Arrangement s r)
    {c : ℂ} (hc : c ∈ s) (t : ℝ)
    (ht : ∀ d ∈ s, r d ≤ dist (circleMap c (r c) t) d) :
    ∃ a b δ : ℝ, 0 < δ ∧ a < b ∧ b - a ≤ 2 * Real.pi ∧
      (∀ u ∈ Icc a b, ∀ d ∈ s, r d ≤ dist (circleMap c (r c) u) d) ∧
      (∀ u, |u - t| < δ → (∀ d ∈ s, r d ≤ dist (circleMap c (r c) u) d) →
        u ∈ Icc a b) := by
  classical
  have hself (u : ℝ) : dist (circleMap c (r c) u) c = r c :=
    mem_sphere.mp (circleMap_mem_sphere c (h.1 c hc).le u)
  obtain ⟨η, hη, hmargin⟩ := inactive_margin s r c (r c) t ht
  by_cases ha : ∃ d ∈ s, d ≠ c ∧ dist (circleMap c (r c) t) d = r d
  · obtain ⟨d, hd, hdc, hdt⟩ := ha
    let k := -2 * ((circleMap c (r c) t - c) * conj (circleMap c (r c) t - d)).im
    have hk : k ≠ 0 := mul_ne_zero (by norm_num)
      (circle_radials_transverse s r h hc hd hdc.symm (hself t) hdt)
    obtain ⟨ν, hν, hsign⟩ := sign_near_simple_zero (circle_power_hasDerivAt c d (r c) (r d) t)
      (by rw [normSq_eq_norm_sq, ← dist_eq_norm, hdt]; ring) hk
    let ε := min (min η ν) Real.pi / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεη : ε < η := by
      dsimp [ε]
      have h₁ := min_le_left (min η ν) Real.pi
      have h₂ := min_le_left η ν
      linarith
    have hεν : ε < ν := by
      dsimp [ε]
      have h₁ := min_le_left (min η ν) Real.pi
      have h₂ := min_le_right η ν
      linarith
    have hεπ : ε ≤ Real.pi := by
      dsimp [ε]
      have h₁ := min_le_right (min η ν) Real.pi
      linarith [Real.pi_pos]
    have hexterior (u : ℝ) (hu : |u - t| ≤ ε) :
        (∀ e ∈ s, r e ≤ dist (circleMap c (r c) u) e) ↔ 0 ≤ k * (u - t) := by
      have hs := hsign u (hu.trans_lt hεν)
      rw [nonneg_power_iff (h.1 d hd).le] at hs
      constructor
      · intro huall
        exact hs.mp (huall d hd)
      · intro hku e he
        by_cases hec : e = c
        · subst e; exact (hself u).ge
        by_cases hed : e = d
        · subst e; exact hs.mpr hku
        apply (hmargin u (hu.trans_lt hεη) e he ?_).le
        intro hact
        have heq := other_active_unique s r h hc hd he (Ne.symm hdc) (Ne.symm hec) (hself t) hdt hact
        exact hed heq.symm
    rcases lt_or_gt_of_ne hk with hkneg | hkpos
    · refine ⟨t - ε, t, ε, hε, by linarith, by linarith, ?_, ?_⟩
      · intro u hu
        apply (hexterior u ?_).mpr
        · exact mul_nonneg_of_nonpos_of_nonpos hkneg.le (sub_nonpos.mpr hu.2)
        · rw [abs_of_nonpos (sub_nonpos.mpr hu.2)]; linarith [hu.1]
      · intro u hu hue
        have hku := (hexterior u hu.le).mp hue
        have hut : u ≤ t := by nlinarith
        exact ⟨by have := (abs_lt.mp hu).1; linarith, hut⟩
    · refine ⟨t, t + ε, ε, hε, by linarith, by linarith, ?_, ?_⟩
      · intro u hu
        apply (hexterior u ?_).mpr
        · exact mul_nonneg hkpos.le (sub_nonneg.mpr hu.1)
        · rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]; linarith [hu.2]
      · intro u hu hue
        have hku := (hexterior u hu.le).mp hue
        have hut : t ≤ u := by nlinarith
        exact ⟨hut, by have := (abs_lt.mp hu).2; linarith⟩
  · let ε := min η Real.pi / 2
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεη : ε < η := by dsimp [ε]; have := min_le_left η Real.pi; linarith
    have hεπ : ε ≤ Real.pi := by
      dsimp [ε]
      have h₁ := min_le_right η Real.pi
      linarith [Real.pi_pos]
    refine ⟨t - ε, t + ε, ε, hε, by linarith, by linarith, ?_, ?_⟩
    · intro u hu d hd
      by_cases hdc : d = c
      · subst d; exact (hself u).ge
      apply (hmargin u ?_ d hd ?_).le
      · rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
      · intro hact; exact ha ⟨d, hd, hdc, hact⟩
    · intro u hu _
      exact ⟨by have := (abs_lt.mp hu).1; linarith, by have := (abs_lt.mp hu).2; linarith⟩

/-- A full closed period covers the entire circle, including the seam. -/
theorem circle_image_period (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    circleMap c R '' Icc (-Real.pi) Real.pi = sphere c R := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, _, rfl⟩
    exact circleMap_mem_sphere c hR t
  · intro z hz
    have hn : ‖z - c‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hz
    refine ⟨arg (z - c), ⟨(neg_pi_lt_arg _).le, arg_le_pi _⟩, ?_⟩
    change c + (R : ℂ) * exp ((arg (z - c) : ℂ) * I) = z
    rw [← hn, norm_mul_exp_arg_mul_I]
    abel

/-- The exposed part of one circle is compact in a chosen closed period. -/
theorem compact_exposed_parameters (s : Finset ℂ) (r : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    IsCompact {t : ℝ | t ∈ Icc (-Real.pi) Real.pi ∧
      ∀ d ∈ s, r d ≤ dist (circleMap c R t) d} := by
  have hc : IsClosed {t : ℝ | ∀ d ∈ s, r d ≤ dist (circleMap c R t) d} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun d => isClosed_iInter fun _ =>
      isClosed_le continuous_const ((continuous_circle c R).dist continuous_const)
  exact isCompact_Icc.inter_right hc

/-- Finite extraction on one circle; each selected interval is nondegenerate,
and all of its closed image belongs to the actual frontier. -/
theorem finite_arcs_on_circle (s : Finset ℂ) (r : ℂ → ℝ) (h : Arrangement s r)
    {c : ℂ} (hc : c ∈ s) :
    ∃ (n : ℕ) (a b : Fin n → ℝ),
      (∀ i, a i < b i ∧ b i - a i ≤ 2 * Real.pi) ∧
      sphere c (r c) ∩ frontier (diskUnion s r) =
        ⋃ i : Fin n, circleMap c (r c) '' Icc (a i) (b i) := by
  classical
  let K : Set ℝ := {t | t ∈ Icc (-Real.pi) Real.pi ∧
      ∀ d ∈ s, r d ≤ dist (circleMap c (r c) t) d}
  have hloc (t : K) := local_exposed_interval s r h hc t t.property.2
  choose a b δ hδ hab hlen hout hcover using hloc
  obtain ⟨F, hF⟩ := (compact_exposed_parameters s r c (r c)).elim_finite_subcover
    (fun t : K => ball (t : ℝ) (δ t)) (fun _ => isOpen_ball) (by
      intro t ht
      exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_ball_self (hδ ⟨t, ht⟩)⟩)
  let e := F.equivFin
  let selected (i : Fin F.card) : K := (e.symm i).val
  refine ⟨F.card, fun i => a (selected i), fun i => b (selected i), ?_, ?_⟩
  · exact fun i => ⟨hab (selected i), hlen (selected i)⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := (circle_image_period c (h.1 c hc).le).symm ▸ hz.1
      have huout : ∀ d ∈ s, r d ≤ dist (circleMap c (r c) u) d := by
        rw [huz]
        exact ((mem_frontier_diskUnion s r h.1 z).mp hz.2).2
      have huK : u ∈ K := ⟨hu, huout⟩
      obtain ⟨t, ht, hut⟩ := mem_iUnion₂.mp (hF huK)
      have huδ : |u - (t : ℝ)| < δ t := by simpa only [mem_ball, Real.dist_eq] using hut
      have hui := hcover t u huδ huout
      refine mem_iUnion.mpr ⟨e ⟨t, ht⟩, ?_⟩
      have hs : selected (e ⟨t, ht⟩) = t := by simp [selected]
      dsimp only
      rw [hs]
      exact ⟨u, hui, huz⟩
    · intro hz
      obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp hz
      have hsphere := circleMap_mem_sphere c (h.1 c hc).le u
      refine ⟨hsphere, (mem_frontier_diskUnion s r h.1 _).mpr ?_⟩
      exact ⟨⟨c, hc, mem_sphere.mp hsphere⟩, hout (selected i) u hu⟩

/-- Every finite arrangement satisfying exactly the stated hypotheses has a
finite decomposition of its entire frontier into regular analytic circular arcs. -/
theorem finite_circular_arcs :
    Specs.D12Complex.Ch14.FiniteCircularArcs.finite_circular_arcs_type := by
  intro s r h
  classical
  have heach (c : ↥s) := finite_arcs_on_circle s r h c.property
  choose n a b hab heq using heach
  let J := (c : ↥s) × Fin (n c)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun i => (e i).1.val, fun i => r (e i).1.val,
    fun i => a (e i).1 (e i).2, fun i => b (e i).1 (e i).2, ?_, ?_, ?_⟩
  · intro i
    exact ⟨h.1 (e i).1.val (e i).1.property, hab (e i).1 (e i).2⟩
  · change frontier (diskUnion s r) = ⋃ i : Fin (Fintype.card J),
      circleMap (e i).1.val (r (e i).1.val) '' Icc (a (e i).1 (e i).2) (b (e i).1 (e i).2)
    ext z
    constructor
    · intro hz
      obtain ⟨c, hc, hzc⟩ := ((mem_frontier_diskUnion s r h.1 z).mp hz).1
      let c' : ↥s := ⟨c, hc⟩
      have hzone : z ∈ sphere c (r c) ∩ frontier (diskUnion s r) :=
        ⟨mem_sphere.mpr hzc, hz⟩
      have hzi : z ∈ ⋃ j : Fin (n c'), circleMap c (r c) '' Icc (a c' j) (b c' j) := by
        rw [← heq c']; exact hzone
      obtain ⟨j, hj⟩ := mem_iUnion.mp hzi
      obtain ⟨i, hi⟩ := e.surjective ⟨c', j⟩
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      rw [hi]
      exact hj
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      have hzi : z ∈ ⋃ j : Fin (n (e i).1),
          circleMap (e i).1.val (r (e i).1.val) '' Icc (a (e i).1 j) (b (e i).1 j) :=
        mem_iUnion.mpr ⟨(e i).2, hi⟩
      rw [← heq (e i).1] at hzi
      exact hzi.2
  · intro i
    have hp := circular_parametrization (e i).1.val (r (e i).1.val)
      (a (e i).1 (e i).2) (b (e i).1 (e i).2)
      (h.1 (e i).1.val (e i).1.property) (hab (e i).1 (e i).2).1 (hab (e i).1 (e i).2).2
    exact ⟨⟨Set.univ, isOpen_univ, subset_univ _, hp.1, fun t _ => hp.2.1 t⟩, hp.2.2⟩

end D12Complex.FiniteCircularArcs
