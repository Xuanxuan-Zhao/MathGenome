import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.Oscillation
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Prufer
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.Spectrum
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter
namespace D13Unified.Ch10.Oscillation
open Specs.D13Unified.Ch10.RegularProblem
open Specs.D13Unified.Ch10.Prufer
open Specs.D13Unified.Ch10.Oscillation

open scoped Topology

/-- Positive within derivative gives the two strict local crossing signs,
including at the endpoints of a closed interval. -/
lemma local_crossing {f : ℝ → ℝ} {a b x d : ℝ}
    (hd : HasDerivWithinAt f d (Icc a b) x) (hpos : 0 < d) :
    ∃ eps > 0, ∀ y ∈ Icc a b, |y - x| < eps →
      (y < x → f y < f x) ∧ (x < y → f x < f y) := by
  have hs := (hasDerivWithinAt_iff_tendsto_slope.mp hd).eventually
    (eventually_gt_nhds hpos)
  obtain ⟨eps, heps, hs⟩ := Metric.mem_nhdsWithin_iff.mp hs
  refine ⟨eps, heps, fun y hy hnear => ?_⟩
  constructor
  · intro hyx
    have h := hs ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hnear,
      hy, by simpa using ne_of_lt hyx⟩
    change 0 < slope f x y at h
    rw [slope_def_field] at h
    exact sub_neg.mp ((div_pos_iff.mp h).resolve_left (by rintro ⟨_, h⟩; linarith)).1
  · intro hxy
    have h := hs ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hnear,
      hy, by simpa using ne_of_gt hxy⟩
    change 0 < slope f x y at h
    rw [slope_def_field] at h
    exact sub_pos.mp ((div_pos_iff.mp h).resolve_right (by rintro ⟨_, h⟩; linarith)).1

/-- A continuous function whose crossings of a fixed level are all upward
cannot return to or below that level after one such crossing. -/
lemma above_after_upward_crossing {f : ℝ → ℝ} {a b c x y : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hcross : ∀ t ∈ Icc a b, f t = c →
      ∃ d > 0, HasDerivWithinAt f d (Icc a b) t)
    (hx : x ∈ Icc a b) (hfx : f x = c) (hy : y ∈ Icc a b) (hxy : x < y) :
    c < f y := by
  by_contra hbad
  have hfy : f y ≤ c := le_of_not_gt hbad
  obtain ⟨d, hd, hder⟩ := hcross x hx hfx
  obtain ⟨eps, heps, hlocal⟩ := local_crossing hder hd
  obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxy (by linarith : x < x + eps))
  have hzI : z ∈ Icc a b := ⟨hx.1.trans hxz.le, (hzy.trans_le (min_le_left _ _)).le.trans hy.2⟩
  have hzpos : c < f z := by
    rw [← hfx]
    have hnear : |z - x| < eps := by
      rw [abs_of_pos (sub_pos.mpr hxz)]
      linarith [hzy.trans_le (min_le_right y (x + eps))]
    exact (hlocal z hzI hnear).2 hxz
  have hzy' : z < y := hzy.trans_le (min_le_left _ _)
  have hsub : Icc z y ⊆ Icc a b := Icc_subset_Icc hzI.1 hy.2
  have hnonempty : {t ∈ Icc z y | f t = c}.Nonempty := by
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc' hzy'.le (hf.mono hsub)
      ⟨hfy, hzpos.le⟩
    exact ⟨t, ht, heq⟩
  have hcompact : IsCompact {t ∈ Icc z y | f t = c} :=
    isCompact_Icc.of_isClosed_subset
      ((hf.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
      (sep_subset _ _)
  obtain ⟨t, ht, hmin⟩ := hcompact.exists_isLeast hnonempty
  have htI := hsub ht.1
  have hzt : z < t := lt_of_le_of_ne ht.1.1 (by
    intro heq
    have := ht.2
    rw [← heq] at this
    linarith)
  obtain ⟨e, he, hdt⟩ := hcross t htI ht.2
  obtain ⟨delta, hdelta, htlocal⟩ := local_crossing hdt he
  obtain ⟨u, hlu, hut⟩ := exists_between
    (max_lt hzt (by linarith : t - delta < t))
  have hzu : z < u := lt_of_le_of_lt (le_max_left _ _) hlu
  have huI : u ∈ Icc a b :=
    ⟨hzI.1.trans hzu.le, hut.le.trans htI.2⟩
  have huneg : f u < c := by
    rw [← ht.2]
    have hnear : |u - t| < delta := by
      rw [abs_of_neg (sub_neg.mpr hut)]
      linarith [lt_of_le_of_lt (le_max_right z (t - delta)) hlu]
    exact (htlocal u huI hnear).1 hut
  obtain ⟨v, hv, hveq⟩ := intermediate_value_Icc' hzu.le
    (hf.mono (Icc_subset_Icc hzI.1 huI.2)) ⟨huneg.le, hzpos.le⟩
  have hvZ : v ∈ {s ∈ Icc z y | f s = c} :=
    ⟨⟨hv.1, hv.2.trans (hut.le.trans ht.1.2)⟩, hveq⟩
  exact (not_lt_of_ge (hmin hvZ)) (hv.2.trans_lt hut)

/-- The existing spectral theorem really supplies the sequence data used by
the oscillation statement, including exhaustiveness. -/
theorem sequence_exists : SequenceExists := by
  intro P
  obtain ⟨lam, phi, hphi, B, hm, ht, he, hB, hall, hs, hsum⟩ := Spectrum.spectrum P
  refine ⟨lam, hm, ht, (fun n => ⟨phi n, he n⟩), ?_⟩
  intro mu hmu
  obtain ⟨y, hy⟩ := hmu
  obtain ⟨n, hn⟩ := hall (mu : ℂ) (fun x => (y x : ℂ)) hy
  exact ⟨n, Complex.ofReal_injective hn⟩

theorem terminal_strictMono : TerminalStrictMono := by
  intro P
  exact strictMono_of_hasDerivAt_pos
    (fun mu => (Prufer.terminal_parameter_derivative P mu).1)
    (fun mu => (Prufer.terminal_parameter_derivative P mu).2)

lemma terminal_continuous (P : Problem) : Continuous (fun mu => angle P mu P.b) := by
  exact continuous_iff_continuousAt.mpr fun mu =>
    (Prufer.terminal_parameter_derivative P mu).1.continuousAt

/-- This zero criterion refers to the continuous lifted angle, not a principal
argument, so it can be used for all integer levels. -/
lemma solution_zero_iff_angle (P : Problem) (mu : ℝ) {x : ℝ}
    (hx : x ∈ intervalValue P) :
    solution P mu x = 0 ↔ ∃ k : ℤ, angle P mu x = (k : ℝ) * Real.pi := by
  have h := (Prufer.angle_lift P mu).2.2.2 x hx
  rw [h.2.1, mul_eq_zero]
  simp only [ne_of_gt h.1, false_or]
  simpa only [eq_comm] using (Real.sin_eq_zero_iff (x := angle P mu x))

lemma angle_crossings (P : Problem) (mu : ℝ) (k : ℤ) :
    ∀ x ∈ Icc P.a P.b, angle P mu x = (k : ℝ) * Real.pi →
      ∃ d > 0, HasDerivWithinAt (angle P mu) d (Icc P.a P.b) x := by
  intro x hx heq
  have hz := (solution_zero_iff_angle P mu hx).mpr ⟨k, heq⟩
  exact ⟨(P.p x)⁻¹, (Prufer.upward_crossings P mu x hx hz).2,
    (Prufer.upward_crossings P mu x hx hz).1⟩

lemma angle_positive (P : Problem) (mu : ℝ) {x : ℝ} (hx : x ∈ Ioc P.a P.b) :
    0 < angle P mu x := by
  have h := above_after_upward_crossing (Prufer.angle_continuous P mu)
    (angle_crossings P mu 0) (Prufer.left_mem P)
    (by simpa using Prufer.angle_left P mu) ⟨hx.1.le, hx.2⟩ hx.1
  simpa using h

lemma angle_level_unique (P : Problem) (mu : ℝ) (k : ℤ) {x y : ℝ}
    (hx : x ∈ intervalValue P) (hy : y ∈ intervalValue P)
    (hfx : angle P mu x = (k : ℝ) * Real.pi)
    (hfy : angle P mu y = (k : ℝ) * Real.pi) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · have := above_after_upward_crossing (Prufer.angle_continuous P mu)
      (angle_crossings P mu k) hx hfx hy h
    linarith
  · exact h
  · have := above_after_upward_crossing (Prufer.angle_continuous P mu)
      (angle_crossings P mu k) hy hfy hx h
    linarith

lemma angle_lt_terminal (P : Problem) (mu : ℝ) {x : ℝ}
    (hx : x ∈ Ioo P.a P.b) (hz : solution P mu x = 0) :
    angle P mu x < angle P mu P.b := by
  obtain ⟨k, hk⟩ := (solution_zero_iff_angle P mu ⟨hx.1.le, hx.2.le⟩).mp hz
  rw [hk]
  exact above_after_upward_crossing (Prufer.angle_continuous P mu)
    (angle_crossings P mu k) ⟨hx.1.le, hx.2.le⟩ hk (Prufer.right_mem P) hx.2

lemma angle_lt_pi_of_positive_solution (P : Problem) (mu : ℝ)
    (hpos : ∀ x ∈ Ioc P.a P.b, 0 < solution P mu x) :
    angle P mu P.b < Real.pi := by
  by_contra h
  obtain ⟨x, hx, heq⟩ := intermediate_value_Icc P.a_lt_b.le
    (Prufer.angle_continuous P mu) ⟨by rw [Prufer.angle_left]; exact Real.pi_pos.le,
      le_of_not_gt h⟩
  have hax : P.a < x := lt_of_le_of_ne hx.1 (by
    intro he
    subst x
    rw [Prufer.angle_left] at heq
    exact Real.pi_ne_zero heq.symm)
  have hz := (solution_zero_iff_angle P mu hx).mpr ⟨1, by simpa using heq⟩
  exact (ne_of_gt (hpos x ⟨hax, hx.2⟩)) hz

lemma left_mode_normalized (P : Problem) (mu : ℝ) :
    Normalized P mu (GreenKernel.leftMode P (-mu)) := by
  obtain ⟨hreg, _, ha, _, hflux, _, heq, _⟩ := GreenKernel.modes P (-mu)
  refine ⟨⟨hreg, ?_⟩, ha, hflux⟩
  intro x hx
  have h := heq x hx
  change -derivWithin (fun t => P.p t * derivWithin (GreenKernel.leftMode P (-mu))
      (intervalValue P) t) (intervalValue P) x +
      P.q x * GreenKernel.leftMode P (-mu) x =
    mu * P.w x * GreenKernel.leftMode P (-mu) x
  dsimp [GreenKernel.Q] at h
  nlinarith

lemma solution_eq_left_mode (P : Problem) (mu : ℝ) :
    EqOn (solution P mu) (GreenKernel.leftMode P (-mu)) (intervalValue P) :=
  Prufer.normalized_unique (Prufer.normalized P mu) (left_mode_normalized P mu)

/-- Every nonzero real Dirichlet eigenfunction has exactly the same zeros as
the left-normalized solution. No choice of its sign or L² normalization enters. -/
lemma eigenfunction_zero_iff_solution (P : Problem) (mu : ℝ) (y : ℝ → ℝ)
    (hy : RealDirichletEigenfunction P mu y) {x : ℝ} (hx : x ∈ intervalValue P) :
    y x = 0 ↔ solution P mu x = 0 := by
  obtain ⟨hA, hprop⟩ := ClassicalEigenfunctionBridge.proportional_to_real_mode
    P (mu : ℂ) (fun x => (y x : ℂ)) hy
  have hp := hprop hx
  simp only [Complex.ofReal_re] at hp
  rw [← solution_eq_left_mode P mu hx] at hp
  have heq : (y x : ℂ) =
      ((P.p P.a : ℂ) * RegularProblem.derivative P (fun x => (y x : ℂ)) P.a) *
        (solution P mu x : ℂ) := hp
  constructor
  · intro hz
    have hh := heq
    rw [hz, Complex.ofReal_zero] at hh
    exact Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hh.symm).resolve_left hA)
  · intro hz
    apply Complex.ofReal_injective
    simpa [hz] using heq

lemma eigenvalue_terminal_zero (P : Problem) (mu : ℝ)
    (hmu : ∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y) :
    solution P mu P.b = 0 := by
  obtain ⟨y, hy⟩ := hmu
  have hb := (RegularProblem.dirichlet_boundary P (fun x => (y x : ℂ))).mp hy.2.2.1
  exact (eigenfunction_zero_iff_solution P mu y hy (Prufer.right_mem P)).mp
    (Complex.ofReal_eq_zero.mp hb.2)

lemma eigenvalue_terminal_angle (P : Problem) (mu : ℝ)
    (hmu : ∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y) :
    ∃ k : ℤ, angle P mu P.b = (k : ℝ) * Real.pi :=
  (solution_zero_iff_angle P mu (Prufer.right_mem P)).mp (eigenvalue_terminal_zero P mu hmu)

/-- The converse shooting criterion, including the real-to-complex classical
regularity bridge required by the spectral interface. -/
lemma eigenfunction_of_terminal_zero (P : Problem) (mu : ℝ)
    (hb : solution P mu P.b = 0) :
    RealDirichletEigenfunction P mu (solution P mu) := by
  let u := solution P mu
  have hu := (Prufer.normalized P mu).1
  have hc : ContDiffOn ℝ 2 (fun x => (u x : ℂ)) (intervalValue P) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hu.1
  have hcast (x : ℝ) (hx : x ∈ intervalValue P) :
      HasDerivWithinAt (fun t => (u t : ℂ))
        (Specs.D13Unified.Ch10.Separation.derivative P u x : ℂ) (intervalValue P) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt x (Separation.solution_derivative hu hx)
  have hf : EqOn (fun x => (P.p x : ℂ) *
      derivativeValue P (fun t => (u t : ℂ)) x)
      (fun x => (Specs.D13Unified.Ch10.Separation.flux P u x : ℂ)) (intervalValue P) := by
    intro x hx
    have hd := (hcast x hx).derivWithin (Separation.uniqueDiff P x hx)
    change (P.p x : ℂ) * derivWithin (fun t => (u t : ℂ)) (intervalValue P) x = _
    rw [hd]
    simp [Specs.D13Unified.Ch10.Separation.flux]
  refine ⟨hc, ?_, ?_, ?_⟩
  · obtain ⟨x, hx, hn⟩ := Prufer.solution_nonzero P mu
    exact ⟨x, hx, Complex.ofReal_ne_zero.mpr hn⟩
  · apply (RegularProblem.dirichlet_boundary P _).mpr
    exact ⟨by simp [(Prufer.normalized P mu).2.1], by simp [hb]⟩
  · intro x hx
    have hdf : HasDerivWithinAt
        (fun t => (Specs.D13Unified.Ch10.Separation.flux P u t : ℂ))
        (((P.q x - mu * P.w x) * u x : ℝ) : ℂ) (intervalValue P) x :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivWithinAt x
        (Separation.solution_flux_derivative hu hx)
    have hd := (hdf.congr_of_mem hf hx).derivWithin (Separation.uniqueDiff P x hx)
    change -derivWithin (fun t => (P.p t : ℂ) * derivativeValue P (fun s => (u s : ℂ)) t)
      (intervalValue P) x + (P.q x : ℂ) * (u x : ℂ) = _
    rw [hd]
    push_cast
    ring

lemma terminal_zero_iff_eigenvalue (P : Problem) (mu : ℝ) :
    solution P mu P.b = 0 ↔ ∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y :=
  ⟨fun h => ⟨solution P mu, eigenfunction_of_terminal_zero P mu h⟩,
    eigenvalue_terminal_zero P mu⟩

/-- A sufficiently negative parameter has a strictly positive normalized
solution. This will anchor the first angle without a new spectral assumption. -/
lemma exists_positive_normalized (P : Problem) :
    ∃ mu : ℝ, ∀ x ∈ Ioc P.a P.b, 0 < solution P mu x := by
  obtain ⟨c, hc, hQ⟩ := GreenKernel.shift_exists P
  refine ⟨-c, ?_⟩
  intro x hx
  rw [solution_eq_left_mode P (-c) ⟨hx.1.le, hx.2⟩, neg_neg]
  exact (GreenKernel.positive_modes P c hc hQ).1 x hx

lemma eigenvalue_angle_ge_pi (P : Problem) (mu : ℝ)
    (hmu : ∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y) :
    Real.pi ≤ angle P mu P.b := by
  obtain ⟨k, hk⟩ := eigenvalue_terminal_angle P mu hmu
  have hp := angle_positive P mu (show P.b ∈ Ioc P.a P.b from ⟨P.a_lt_b, le_rfl⟩)
  have hkpos : (0 : ℝ) < (k : ℝ) := by nlinarith [Real.pi_pos]
  have hkone : (1 : ℤ) ≤ k := by exact_mod_cast hkpos
  have hkone' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkone
  rw [hk]
  nlinarith [Real.pi_pos]

lemma first_endpoint_angle (P : Problem) (lam : ℕ → ℝ) (hs : IsDirichletSequence P lam) :
    angle P (lam 0) P.b = Real.pi := by
  have hge := eigenvalue_angle_ge_pi P (lam 0) (hs.2.2.1 0)
  apply le_antisymm _ hge
  by_contra hbad
  have hgt : Real.pi < angle P (lam 0) P.b := lt_of_not_ge hbad
  obtain ⟨mu, hpos⟩ := exists_positive_normalized P
  have hlo := angle_lt_pi_of_positive_solution P mu hpos
  have hmu : mu < lam 0 := (terminal_strictMono P).lt_iff_lt.mp (hlo.trans hgt)
  obtain ⟨nu, hnu, heq⟩ := intermediate_value_Icc hmu.le
    (terminal_continuous P).continuousOn ⟨hlo.le, hgt.le⟩
  have hz := (solution_zero_iff_angle P nu (Prufer.right_mem P)).mpr ⟨1, by simpa using heq⟩
  obtain ⟨n, hn⟩ := hs.2.2.2 nu ((terminal_zero_iff_eigenvalue P nu).mp hz)
  have hle : angle P (lam 0) P.b ≤ angle P nu P.b := by
    rw [hn]
    exact (terminal_strictMono P).monotone (hs.1.monotone (Nat.zero_le n))
  linarith

lemma no_eigenvalue_between (P : Problem) (lam : ℕ → ℝ) (hs : IsDirichletSequence P lam)
    (n : ℕ) {mu : ℝ} (hlo : lam n < mu) (hhi : mu < lam (n + 1)) :
    ¬ ∃ y : ℝ → ℝ, RealDirichletEigenfunction P mu y := by
  intro he
  obtain ⟨k, rfl⟩ := hs.2.2.2 mu he
  have hnk := hs.1.lt_iff_lt.mp hlo
  have hkn := hs.1.lt_iff_lt.mp hhi
  omega

lemma endpoint_angle_nat (P : Problem) (lam : ℕ → ℝ) (hs : IsDirichletSequence P lam) :
    ∀ n : ℕ, angle P (lam n) P.b = ((n + 1 : ℕ) : ℝ) * Real.pi := by
  intro n
  induction n with
  | zero => simpa using first_endpoint_angle P lam hs
  | succ n ih =>
    obtain ⟨k, hk⟩ := eigenvalue_terminal_angle P (lam (n + 1)) (hs.2.2.1 (n + 1))
    have hinc := terminal_strictMono P (hs.1 (Nat.lt_succ_self n))
    dsimp only at hinc
    have hklarge : ((n + 1 : ℕ) : ℝ) < (k : ℝ) := by
      rw [ih, hk] at hinc
      exact (mul_lt_mul_iff_left₀ Real.pi_pos).mp hinc
    have hklarge' : (n : ℤ) + 2 ≤ k := by
      have : (n : ℤ) + 1 < k := by exact_mod_cast hklarge
      omega
    have hge : ((n + 2 : ℕ) : ℝ) * Real.pi ≤ angle P (lam (n + 1)) P.b := by
      rw [hk]
      apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
      exact_mod_cast hklarge'
    apply le_antisymm _ hge
    by_contra hbad
    have hgt : ((n + 2 : ℕ) : ℝ) * Real.pi < angle P (lam (n + 1)) P.b :=
      lt_of_not_ge hbad
    have hlo : angle P (lam n) P.b < ((n + 2 : ℕ) : ℝ) * Real.pi := by
      rw [ih]
      push_cast
      nlinarith [Real.pi_pos]
    obtain ⟨mu, hmu, heq⟩ := intermediate_value_Icc (hs.1 (Nat.lt_succ_self n)).le
      (terminal_continuous P).continuousOn ⟨hlo.le, hgt.le⟩
    dsimp only at heq
    have hmulow : lam n < mu := (terminal_strictMono P).lt_iff_lt.mp (by rwa [heq])
    have hmuhi : mu < lam (n + 1) := (terminal_strictMono P).lt_iff_lt.mp (by rwa [heq])
    have hz := (solution_zero_iff_angle P mu (Prufer.right_mem P)).mpr
      ⟨(n : ℤ) + 2, by push_cast; simpa only [Nat.cast_add, Nat.cast_ofNat] using heq⟩
    exact no_eigenvalue_between P lam hs n hmulow hmuhi
      ((terminal_zero_iff_eigenvalue P mu).mp hz)

theorem endpoint_angles : EndpointAngles := by
  intro P lam hs j hj
  have h := endpoint_angle_nat P lam hs (j - 1)
  simpa [Nat.sub_add_cancel hj] using h

lemma angle_lt_pi_of_terminal_pi (P : Problem) (mu : ℝ)
    (hb : angle P mu P.b = Real.pi) {x : ℝ} (hx : x ∈ Ioo P.a P.b) :
    angle P mu x < Real.pi := by
  by_contra hbad
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hx.1.le
    ((Prufer.angle_continuous P mu).mono (Icc_subset_Icc_right hx.2.le))
    ⟨by rw [Prufer.angle_left]; exact Real.pi_pos.le, le_of_not_gt hbad⟩
  have htb := angle_level_unique P mu 1 ⟨ht.1, ht.2.trans hx.2.le⟩
    (Prufer.right_mem P) (by simpa using heq) (by simpa using hb)
  exact (not_le_of_gt hx.2) (htb ▸ ht.2)

theorem positive_first : PositiveFirst := by
  intro P lam hs
  have hang := first_endpoint_angle P lam hs
  have hb := (solution_zero_iff_angle P (lam 0) (Prufer.right_mem P)).mpr
    ⟨1, by simpa using hang⟩
  refine ⟨solution P (lam 0), eigenfunction_of_terminal_zero P (lam 0) hb, ?_⟩
  intro x hx
  have hlift := (Prufer.angle_lift P (lam 0)).2.2.2 x ⟨hx.1.le, hx.2.le⟩
  rw [hlift.2.1]
  exact mul_pos hlift.1 (Real.sin_pos_of_pos_of_lt_pi
    (angle_positive P (lam 0) ⟨hx.1, hx.2.le⟩) (angle_lt_pi_of_terminal_pi P (lam 0) hang hx))

/-- Each of the n interior levels is attained exactly once when the terminal
angle is (n+1)π. The function itself need not be monotone between levels. -/
lemma normalized_zero_count (P : Problem) (mu : ℝ) (n : ℕ)
    (hb : angle P mu P.b = ((n + 1 : ℕ) : ℝ) * Real.pi) :
    {x ∈ Ioo P.a P.b | solution P mu x = 0}.Finite ∧
    {x ∈ Ioo P.a P.b | solution P mu x = 0}.ncard = n := by
  have hex (i : Fin n) : ∃ x ∈ Ioo P.a P.b,
      angle P mu x = ((i.val + 1 : ℕ) : ℝ) * Real.pi := by
    have hlo : angle P mu P.a < ((i.val + 1 : ℕ) : ℝ) * Real.pi := by
      rw [Prufer.angle_left]
      positivity
    have hhi : ((i.val + 1 : ℕ) : ℝ) * Real.pi < angle P mu P.b := by
      rw [hb]
      apply mul_lt_mul_of_pos_right _ Real.pi_pos
      exact_mod_cast Nat.add_lt_add_right i.isLt 1
    obtain ⟨x, hx, heq⟩ := intermediate_value_Icc P.a_lt_b.le
      (Prufer.angle_continuous P mu) ⟨hlo.le, hhi.le⟩
    refine ⟨x, ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩, heq⟩
    · intro h; subst x; linarith
    · intro h; subst x; linarith
  choose z hz hangle using hex
  have hzinj : Function.Injective z := by
    intro i j heq
    have hi := hangle i
    have hj := hangle j
    rw [heq] at hi
    have hc := mul_right_cancel₀ Real.pi_ne_zero (hi.symm.trans hj)
    have hval : i.val + 1 = j.val + 1 := by exact_mod_cast hc
    apply Fin.ext
    omega
  have hset : {x ∈ Ioo P.a P.b | solution P mu x = 0} = range z := by
    ext x
    constructor
    · rintro ⟨hx, hzero⟩
      obtain ⟨k, hk⟩ := (solution_zero_iff_angle P mu ⟨hx.1.le, hx.2.le⟩).mp hzero
      have hpos := angle_positive P mu ⟨hx.1, hx.2.le⟩
      have hlt := angle_lt_terminal P mu hx hzero
      have hkpos : (0 : ℝ) < (k : ℝ) := by rw [hk] at hpos; nlinarith [Real.pi_pos]
      have hklt : (k : ℝ) < ((n + 1 : ℕ) : ℝ) := by
        rw [hk, hb] at hlt
        exact (mul_lt_mul_iff_left₀ Real.pi_pos).mp hlt
      have hknonneg : 0 ≤ k := le_of_lt (by exact_mod_cast hkpos : (0 : ℤ) < k)
      lift k to ℕ using hknonneg with m
      have hmpos : 0 < m := by exact_mod_cast hkpos
      have hmlt : m < n + 1 := by exact_mod_cast hklt
      let i : Fin n := ⟨m - 1, by omega⟩
      have hi : i.val + 1 = m := Nat.sub_add_cancel hmpos
      have hxz : x = z i := by
        apply angle_level_unique P mu (m : ℤ) ⟨hx.1.le, hx.2.le⟩
          ⟨(hz i).1.le, (hz i).2.le⟩ hk
        simpa only [hi, Int.cast_natCast] using hangle i
      exact ⟨i, hxz.symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨hz i, (solution_zero_iff_angle P mu ⟨(hz i).1.le, (hz i).2.le⟩).mpr ?_⟩
      exact ⟨(i.val + 1 : ℕ), by simpa only [Int.cast_natCast] using hangle i⟩
  rw [hset]
  exact ⟨finite_range z, by simpa using ncard_range_of_injective hzinj⟩

theorem oscillation_count : OscillationCount := by
  intro P lam hs j hj y hy
  have h := normalized_zero_count P (lam (j - 1)) (j - 1)
    (endpoint_angle_nat P lam hs (j - 1))
  have heq : {x ∈ Ioo P.a P.b | y x = 0} =
      {x ∈ Ioo P.a P.b | solution P (lam (j - 1)) x = 0} := by
    ext x
    simp only [mem_ofPred_eq]
    exact and_congr_right fun hx => eigenfunction_zero_iff_solution P (lam (j - 1)) y hy
      ⟨hx.1.le, hx.2.le⟩
  rwa [heq]

end D13Unified.Ch10.Oscillation
