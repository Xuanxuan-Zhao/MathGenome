import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.RealAnalyticLocal
import MathGenome.Internal.ODEDynamics.D13Unified.Ch06.HolomorphicDependence
import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.OpenDomain
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.LocalExistenceUniqueness
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
namespace D13Unified.Ch06.RealAnalytic
open Filter Metric Set
open scoped Topology
open D13Unified.Ch06.HolomorphicLimits D13Unified.Ch06.HolomorphicDependence
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch03.LocalLipschitz
open Specs.D13Unified.Ch04.MaximalSolutionMap

@[simp] lemma complexifyPoint_apply {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    complexifyPoint x i = (x i : ℂ) := rfl

@[simp] lemma norm_complexifyPoint {d : ℕ} (x : Fin d → ℝ) :
    ‖complexifyPoint x‖ = ‖x‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
    intro i
    simpa using norm_le_pi_norm x i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (complexifyPoint x))).mpr
    intro i
    simpa using norm_le_pi_norm (complexifyPoint x) i

@[simp] lemma complexifyPoint_sub {d : ℕ} (x y : Fin d → ℝ) :
    complexifyPoint (x-y) = complexifyPoint x - complexifyPoint y := by
  ext i; simp [complexifyPoint]

@[simp] lemma complexifyPoint_mem_ball {d : ℕ} (x a : Fin d → ℝ) (r : ℝ) :
    complexifyPoint x ∈ ball (complexifyPoint a) r ↔ x ∈ ball a r := by
  simp only [mem_ball_iff_norm, ← complexifyPoint_sub, norm_complexifyPoint]

lemma continuous_complexifyPoint (d : ℕ) : Continuous (@complexifyPoint d) :=
  continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)

@[simp] lemma fieldData_realFieldPoint {n m : ℕ} (t : ℝ) (x : Fin n → ℝ)
    (p : Fin m → ℝ) : fieldData (realFieldPoint t x p) = ((t,x),p) := by
  simp [fieldData, realFieldPoint, Fin.tail_cons, Fin.append_left, Fin.append_right]

lemma continuous_fieldData (n m : ℕ) : Continuous (@fieldData n m) := by
  exact ((continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply _)).prodMk
    (continuous_pi fun i => continuous_apply _)

/-- The convergence majorant is obtained at the positive real increment
r/2. The same real coefficients then dominate the complex polydisc. -/
lemma real_series_complex_majorant {d : ℕ} (a : Fin d → ℝ) (r : ℝ)
    (c : (Fin d → ℕ) → ℝ) (hr : 0 < r)
    (hs : ∀ x ∈ ball a r,
      Summable (fun α => ‖c α * ∏ j : Fin d, (x j - a j) ^ α j‖)) :
    ∃ u : (Fin d → ℕ) → ℝ, Summable u ∧
      ∀ α z, z ∈ ball (complexifyPoint a) (r/2) →
        ‖(c α : ℂ) * ∏ j : Fin d, (z j - (a j : ℂ)) ^ α j‖ ≤ u α := by
  let q : Fin d → ℝ := fun j => a j + r/2
  have hq : q ∈ ball a r := by
    rw [mem_ball_iff_norm]
    apply lt_of_le_of_lt _ (half_lt_self hr)
    apply (pi_norm_le_iff_of_nonneg (half_pos hr).le).mpr
    intro j
    simp [q, abs_of_pos hr]
  refine ⟨fun α => ‖c α * ∏ j : Fin d, (q j - a j) ^ α j‖, hs q hq, ?_⟩
  intro α z hz
  rw [mem_ball_iff_norm] at hz
  simp only [norm_mul, norm_prod, norm_pow, Complex.norm_real]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro j _
  have hj : ‖z j - (a j : ℂ)‖ ≤ r/2 :=
    (norm_le_pi_norm (z-complexifyPoint a) j).trans hz.le
  simpa [q, abs_of_pos hr] using pow_le_pow_left₀ (norm_nonneg _) hj (α j)


/-- Extension is built from the given real coefficients, after reducing the
radius. Normal convergence proves holomorphy on the full complex ball. -/
theorem local_complexification :
    Specs.D13Unified.Ch06.RealAnalyticLocal.localComplexification_type := by
  intro d n V f hf a ha
  obtain ⟨r, hr, hrV, hc⟩ := hf a ha
  choose c hc using hc
  let g : (Fin d → ℂ) → Fin n → ℂ := fun z i =>
    ∑' α, (c i α : ℂ) * ∏ j : Fin d, (z j - (a j : ℂ)) ^ α j
  have major : ∀ i, ∃ u : (Fin d → ℕ) → ℝ, Summable u ∧
      ∀ α z, z ∈ ball (complexifyPoint a) (r/2) →
        ‖(c i α : ℂ) * ∏ j : Fin d, (z j - (a j : ℂ)) ^ α j‖ ≤ u α := by
    intro i
    exact real_series_complex_majorant a r (c i) hr (fun x hx => (hc i x hx).1)
  refine ⟨r/2, half_pos hr, (ball_subset_ball (half_le_self hr.le)).trans hrV, g, ?_, ?_, ?_⟩
  · apply coordinateHolomorphicOn_of_continuous_lineAnalytic isOpen_ball
    · apply continuousOn_pi.mpr
      intro i
      obtain ⟨u, hu, hub⟩ := major i
      apply continuousOn_tsum _ hu hub
      intro α z _
      exact (analyticAt_coordinate_term (complexifyPoint a)
        (fun α => (c i α : ℂ)) α z).continuousAt.continuousWithinAt
    · intro b v
      apply analyticOnNhd_pi_iff.mpr
      intro i
      obtain ⟨u, hu, hub⟩ := major i
      apply DifferentiableOn.analyticOnNhd _
        (isOpen_ball.preimage (continuous_affineLine b v))
      refine Complex.differentiableOn_tsum_of_summable_norm hu ?_
        (isOpen_ball.preimage (continuous_affineLine b v)) ?_
      · intro α z _
        exact ((analyticAt_coordinate_term (complexifyPoint a)
          (fun α => (c i α : ℂ)) α (affineLine b v z)).comp
          (analyticAt_affineLine b v z)).differentiableAt.differentiableWithinAt
      · intro α z hz
        exact hub α _ hz
  · intro x hx
    ext i
    have hh := Complex.ofRealCLM.hasSum
      (hc i x (ball_subset_ball (half_le_self hr.le) hx)).2
    have he : (fun α => Complex.ofRealCLM
        (c i α * ∏ j : Fin d, (x j-a j)^α j)) =
        (fun α => (c i α : ℂ) * ∏ j : Fin d, ((x j : ℂ)-(a j : ℂ))^α j) := by
      ext α
      simp
    rw [he] at hh
    exact hh.tsum_eq
  · intro z
    ext i
    simp only [g, conjugatePoint, Complex.star_def, Complex.conj_tsum,
      map_mul, map_prod, map_pow, map_sub, Complex.conj_ofReal]

/-- A locally available holomorphic extension gives real coordinate series
by applying the continuous real-part map to each absolutely convergent sum. -/
theorem coordinateRealAnalyticOn_of_local_extension {d n : ℕ}
    {V : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → Fin n → ℝ}
    (h : ∀ a ∈ V, ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧
      ∃ g : (Fin d → ℂ) → Fin n → ℂ,
        CoordinateHolomorphicOn (ball (complexifyPoint a) r) g ∧
        ∀ x ∈ ball a r, (fun i => (g (complexifyPoint x) i).re) = f x) :
    CoordinateRealAnalyticOn V f := by
  intro a ha
  obtain ⟨r, hr, hrV, g, hg, he⟩ := h a ha
  obtain ⟨s, hs, hsU, hc⟩ := hg (complexifyPoint a) (mem_ball_self hr)
  refine ⟨s, hs, ?_, ?_⟩
  · intro x hx
    exact hrV ((complexifyPoint_mem_ball x a r).mp
      (hsU ((complexifyPoint_mem_ball x a s).mpr hx)))
  · intro i
    obtain ⟨c, hc⟩ := hc i
    refine ⟨fun α => (c α).re, ?_⟩
    intro x hx
    have hxs := (complexifyPoint_mem_ball x a s).mpr hx
    have hxr := (complexifyPoint_mem_ball x a r).mp (hsU hxs)
    have term : ∀ α, (c α * ∏ j : Fin d,
        (complexifyPoint x j - complexifyPoint a j)^α j).re =
        (c α).re * ∏ j : Fin d, (x j-a j)^α j := by
      intro α
      have hp : (∏ j : Fin d, (complexifyPoint x j-complexifyPoint a j)^α j) =
          ((∏ j : Fin d, (x j-a j)^α j : ℝ) : ℂ) := by simp
      rw [hp, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    constructor
    · apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hc _ hxs).1
      intro α
      rw [← term α, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    · have hh := Complex.reCLM.hasSum (hc _ hxs).2
      simp only [Complex.reCLM_apply, term] at hh
      rw [congrFun (he x hxr) i] at hh
      exact hh


/-- Restrict real coordinate series to any smaller open domain. -/
theorem CoordinateRealAnalyticOn.mono {d n : ℕ} {U V : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → Fin n → ℝ} (hf : CoordinateRealAnalyticOn U f)
    (hV : IsOpen V) (hVU : V ⊆ U) : CoordinateRealAnalyticOn V f := by
  intro a ha
  obtain ⟨r, hr, hrU, hc⟩ := hf a (hVU ha)
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV a ha
  refine ⟨min r s, lt_min hr hs,
    (ball_subset_ball (min_le_right _ _)).trans hsV, ?_⟩
  intro i
  obtain ⟨c, hc⟩ := hc i
  exact ⟨c, fun x hx => hc x (ball_subset_ball (min_le_left _ _) hx)⟩

/-- Agreement on the actual open set preserves real analyticity. -/
theorem CoordinateRealAnalyticOn.congr {d n : ℕ} {V : Set (Fin d → ℝ)}
    {f g : (Fin d → ℝ) → Fin n → ℝ} (hf : CoordinateRealAnalyticOn V f)
    (heq : EqOn g f V) : CoordinateRealAnalyticOn V g := by
  intro a ha
  obtain ⟨r, hr, hrV, hc⟩ := hf a ha
  refine ⟨r, hr, hrV, ?_⟩
  intro i
  obtain ⟨c, hc⟩ := hc i
  refine ⟨c, fun x hx => ?_⟩
  rw [heq (hrV hx)]
  exact hc x hx

/-- Real coordinate series are jointly continuous on their original domain. -/
theorem CoordinateRealAnalyticOn.continuousOn {d n : ℕ} {V : Set (Fin d → ℝ)}
    {f : (Fin d → ℝ) → Fin n → ℝ} (hf : CoordinateRealAnalyticOn V f) :
    ContinuousOn f V := by
  intro a ha
  obtain ⟨r, hr, _, g, hg, he, _⟩ := local_complexification hf a ha
  have hcg : ContinuousOn (fun x => g (complexifyPoint x)) (ball a r) :=
    hg.continuousOn.comp (continuous_complexifyPoint d).continuousOn
      (fun x hx => (complexifyPoint_mem_ball x a r).mpr hx)
  have hreal : ContinuousOn (fun x i => (g (complexifyPoint x) i).re) (ball a r) := by
    apply continuousOn_pi.mpr
    intro i
    exact Complex.continuous_re.comp_continuousOn
      ((continuous_apply i).comp_continuousOn hcg)
  have hcf : ContinuousOn f (ball a r) := hreal.congr (fun x hx => by simp [he x hx])
  exact (hcf.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt

/-- Real local Lipschitz estimates are consequences of analyticity, not
additional ODE hypotheses. -/
theorem CoordinateRealAnalyticOn.exists_local_lipschitz {d n : ℕ}
    {V : Set (Fin d → ℝ)} {f : (Fin d → ℝ) → Fin n → ℝ}
    (hf : CoordinateRealAnalyticOn V f) {a : Fin d → ℝ} (ha : a ∈ V) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ V ∧ ∃ L : NNReal, LipschitzOnWith L f (ball a r) := by
  obtain ⟨r, hr, hrV, g, hg, he, _⟩ := local_complexification hf a ha
  obtain ⟨s, hs, hsU, M, L, _, hL⟩ :=
    exists_local_bound_lipschitz isOpen_ball hg (mem_ball_self hr)
  refine ⟨s, hs, ?_, L, ?_⟩
  · intro x hx
    exact hrV ((complexifyPoint_mem_ball x a r).mp
      (hsU ((complexifyPoint_mem_ball x a s).mpr hx)))
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxs := (complexifyPoint_mem_ball x a s).mpr hx
    have hys := (complexifyPoint_mem_ball y a s).mpr hy
    have hxr := (complexifyPoint_mem_ball x a r).mp (hsU hxs)
    have hyr := (complexifyPoint_mem_ball y a r).mp (hsU hys)
    have hh := hL.dist_le_mul (complexifyPoint x) hxs (complexifyPoint y) hys
    rw [he x hxr, he y hyr] at hh
    simpa only [dist_eq_norm, ← complexifyPoint_sub, norm_complexifyPoint] using hh


@[simp] lemma complexifyPoint_realFieldPoint {n m : ℕ} (t : ℝ) (x : Fin n → ℝ)
    (p : Fin m → ℝ) : complexifyPoint (realFieldPoint t x p) =
      fieldPoint (t : ℂ) (complexifyPoint x) (complexifyPoint p) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((Fin.append x p j : ℝ) : ℂ) =
      Fin.append (complexifyPoint x) (complexifyPoint p) j
    exact Fin.addCases (fun k => by simp [complexifyPoint])
      (fun k => by simp [complexifyPoint]) j

@[simp] lemma realFieldPoint_fieldData {n m : ℕ} (q : Fin (n+m+1) → ℝ) :
    realFieldPoint (fieldData q).1.1 (fieldData q).1.2 (fieldData q).2 = q := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Fin.addCases (fun k => by simp [realFieldPoint, fieldData, Fin.tail])
      (fun k => by simp [realFieldPoint, fieldData, Fin.tail]) j

lemma realFieldPoint_mem_ball {n m : ℕ} {s t r : ℝ} {x ξ : Fin n → ℝ}
    {p q : Fin m → ℝ} (ht : t ∈ ball s r) (hx : x ∈ ball ξ r)
    (hp : p ∈ ball q r) : realFieldPoint t x p ∈ ball (realFieldPoint s ξ q) r := by
  rw [mem_ball_iff_norm]
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp ht)
  apply (pi_norm_lt_iff hr).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact mem_ball_iff_norm.mp ht
  · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
    · simpa [realFieldPoint] using
        (norm_le_pi_norm (x-ξ) k).trans_lt (mem_ball_iff_norm.mp hx)
    · simpa [realFieldPoint] using
        (norm_le_pi_norm (p-q) k).trans_lt (mem_ball_iff_norm.mp hp)

/-- Derive precisely the uniform-in-time-and-parameter state hypothesis
used by the original canonical solution construction. -/
theorem analytic_field_locallyLipschitz {n m : ℕ}
    (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hf : CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F)) :
    parameterLocallyLipschitzInStateValue F := by
  intro s ξ p ha
  obtain ⟨r, hr, hrU, L, hL⟩ := hf.exists_local_lipschitz
    (a := realFieldPoint s ξ p) (by simpa using ha)
  refine ⟨r, r, r, L, hr, hr, hr, L.coe_nonneg, ?_, ?_⟩
  · intro z hz
    have hh := hrU (realFieldPoint_mem_ball hz.1.1 hz.1.2 hz.2)
    simpa using hh
  · intro q hq t ht x hx y hy
    have hxb := realFieldPoint_mem_ball ht hx hq
    have hyb := realFieldPoint_mem_ball ht hy hq
    have hh := hL.dist_le_mul _ hxb _ hyb
    simp only [dist_eq_norm, fieldInCoordinates, fieldData_realFieldPoint] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [realFieldPoint]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa [realFieldPoint] using norm_le_pi_norm (x-y) k
      · simp [realFieldPoint]

/-- Openness concerns the actual canonical maximal domain. -/
theorem analytic_solution_domain_open {n m : ℕ}
    (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hf : CoordinateRealAnalyticOn (fieldData ⁻¹' F.domain) (fieldInCoordinates F)) :
    IsOpen (solutionDomainInCoordinates F) := by
  exact (D13Unified.Ch05.OpenDomain.open_domain F (analytic_field_locallyLipschitz F hf)).preimage
    ((continuous_apply 0).prodMk ((continuous_fieldData n m).comp
      (continuous_pi fun i => continuous_apply i.succ)))


@[simp] lemma conjugatePoint_complexifyPoint {d : ℕ} (x : Fin d → ℝ) :
    conjugatePoint (complexifyPoint x) = complexifyPoint x := by
  ext i; simp [conjugatePoint, complexifyPoint]

@[simp] lemma conjugatePoint_fieldPoint {n m : ℕ} (z : ℂ) (w : State n) (p : State m) :
    conjugatePoint (fieldPoint z w p) = fieldPoint (star z) (conjugatePoint w)
      (conjugatePoint p) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact Fin.addCases (fun k => by simp [conjugatePoint, fieldPoint])
      (fun k => by simp [conjugatePoint, fieldPoint]) j

@[simp] lemma conjugatePoint_mem_real_ball {d : ℕ} (z : Fin d → ℂ)
    (a : Fin d → ℝ) (r : ℝ) :
    conjugatePoint z ∈ ball (complexifyPoint a) r ↔ z ∈ ball (complexifyPoint a) r := by
  rw [mem_ball_iff_norm, mem_ball_iff_norm]
  have hh : conjugatePoint z - complexifyPoint a = star (z - complexifyPoint a) := by
    ext i; simp [conjugatePoint, complexifyPoint]
  rw [hh, norm_star]

/-- Reflection and germ uniqueness imply reality on the entire time disc.
The identity theorem avoids any uniform radius assumption for germ equality. -/
theorem complex_solution_real {n m : ℕ} {U : Set (FieldPoint n m)}
    {f : FieldPoint n m → State n} {s η : ℝ} {a : ℝ}
    {ξ : Fin n → ℝ} {p : Fin m → ℝ} {u : ℂ → State n}
    (hU : ∀ z ∈ U, conjugatePoint z ∈ U)
    (hf : ∀ z, f (conjugatePoint z) = conjugatePoint (f z))
    (hη : (η : ℂ) ∈ ball (s : ℂ) a)
    (hinit : u (η : ℂ) = complexifyPoint ξ)
    (hu : ∀ z ∈ ball (s : ℂ) a,
      fieldPoint z (u z) (complexifyPoint p) ∈ U ∧
      HasDerivAt u (f (fieldPoint z (u z) (complexifyPoint p))) z)
    (huniq : UniqueSolutionGerm U f (η : ℂ) (complexifyPoint ξ) (complexifyPoint p) u) :
    ∀ t : ℝ, (t : ℂ) ∈ ball (s : ℂ) a →
      u (t : ℂ) = complexifyPoint (fun i => (u (t : ℂ) i).re) := by
  let v : ℂ → State n := fun z => conjugatePoint (u (star z))
  have hconj : ∀ z : ℂ, z ∈ ball (s : ℂ) a → star z ∈ ball (s : ℂ) a := by
    intro z hz
    rw [mem_ball_iff_norm] at hz ⊢
    have he : star z - (s : ℂ) = star (z - (s : ℂ)) := by simp
    rw [he, norm_star]
    exact hz
  have hv : ∀ z ∈ ball (s : ℂ) a,
      fieldPoint z (v z) (complexifyPoint p) ∈ U ∧
      HasDerivAt v (f (fieldPoint z (v z) (complexifyPoint p))) z := by
    intro z hz
    have hz' := hconj z hz
    have hq : conjugatePoint (fieldPoint (star z) (u (star z)) (complexifyPoint p)) =
        fieldPoint z (v z) (complexifyPoint p) := by
      simp [v]
    refine ⟨hq ▸ hU _ (hu _ hz').1, ?_⟩
    have hd := (hu _ hz').2.star_conj
    have hval : star (f (fieldPoint (star z) (u (star z)) (complexifyPoint p))) =
        f (fieldPoint z (v z) (complexifyPoint p)) := by
      exact (hf _).symm.trans (congrArg f hq)
    rw [hval] at hd
    convert! hd using 1
    simp
  have hvi : v (η : ℂ) = complexifyPoint ξ := by
    simp [v, hinit]
  have heq : v =ᶠ[𝓝 (η : ℂ)] u := huniq _ v isOpen_ball hη hvi hv
  have hau : AnalyticOnNhd ℂ u (ball (s : ℂ) a) :=
    (show DifferentiableOn ℂ u (ball (s : ℂ) a) from
      fun z hz => (hu z hz).2.differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have hav : AnalyticOnNhd ℂ v (ball (s : ℂ) a) :=
    (show DifferentiableOn ℂ v (ball (s : ℂ) a) from
      fun z hz => (hv z hz).2.differentiableAt.differentiableWithinAt).analyticOnNhd isOpen_ball
  have he := hav.eqOn_of_preconnected_of_eventuallyEq hau
    (convex_ball (s : ℂ) a).isPreconnected hη heq
  intro t ht
  have hfixed : conjugatePoint (u (t : ℂ)) = u (t : ℂ) := by
    simpa [v] using he ht
  ext i
  apply Complex.ext
  · rfl
  · have hi := congrArg Complex.im (congrFun hfixed i)
    simp only [conjugatePoint, Complex.star_def, Complex.conj_im] at hi
    simp only [complexifyPoint, Complex.ofReal_im]
    linarith


/-- Identify a real complex solution with the original canonical maximal
solution, retaining its entire common real time interval. -/
theorem canonical_real_restriction {n m : ℕ}
    (F : ParameterODE (Fin n → ℝ) (Fin m → ℝ))
    (hL : parameterLocallyLipschitzInStateValue F)
    {q₀ : Fin (n+m+1) → ℝ} {r a : ℝ} {s₀ s : ℝ}
    {ξ : Fin n → ℝ} {p : Fin m → ℝ}
    {g : (Fin (n+m+1) → ℂ) → State n} {u : ℂ → State n}
    (ha : 0 < a) (hs : s ∈ ball s₀ a)
    (hball : ball q₀ r ⊆ fieldData ⁻¹' F.domain)
    (hg : ∀ x ∈ ball q₀ r, g (complexifyPoint x) = complexifyPoint (fieldInCoordinates F x))
    (hinit : u (s : ℂ) = complexifyPoint ξ)
    (hu : ∀ z ∈ ball (s₀ : ℂ) a,
      fieldPoint z (u z) (complexifyPoint p) ∈ ball (complexifyPoint q₀) r ∧
      HasDerivAt u (g (fieldPoint z (u z) (complexifyPoint p))) z)
    (hreal : ∀ t : ℝ, (t : ℂ) ∈ ball (s₀ : ℂ) a →
      u (t : ℂ) = complexifyPoint (fun i => (u (t : ℂ) i).re)) :
    ∀ t ∈ ball s₀ a,
      (t, ((s, ξ), p)) ∈ parameterSolutionDomainValue F ∧
      parameterSolutionValueValue F t s ξ p = fun i => (u (t : ℂ) i).re := by
  let x : ℝ → Fin n → ℝ := fun t i => (u (t : ℂ) i).re
  have hcast : ∀ t : ℝ, t ∈ ball s₀ a → (t : ℂ) ∈ ball (s₀ : ℂ) a := by
    intro t ht
    rw [mem_ball_iff_norm] at ht ⊢
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact ht
  have hgraph : ∀ t ∈ ball s₀ a,
      realFieldPoint t (x t) p ∈ ball q₀ r := by
    intro t ht
    apply (complexifyPoint_mem_ball _ _ _).mp
    rw [complexifyPoint_realFieldPoint, ← hreal t (hcast t ht)]
    exact (hu _ (hcast t ht)).1
  have hdomain : ∀ t ∈ ball s₀ a, ((t,x t),p) ∈ F.domain := by
    intro t ht
    have hh := hball (hgraph t ht)
    simpa using hh
  have hderiv : ∀ t ∈ ball s₀ a, HasDerivAt x (parameterEvalValue F t (x t) p) t := by
    intro t ht
    have heq : g (fieldPoint (t : ℂ) (u (t : ℂ)) (complexifyPoint p)) =
        complexifyPoint (parameterEvalValue F t (x t) p) := by
      rw [hreal t (hcast t ht), ← complexifyPoint_realFieldPoint, hg _ (hgraph t ht)]
      simp only [fieldInCoordinates, fieldData_realFieldPoint]
    apply hasDerivAt_pi.mpr
    intro i
    have hh := ((hasDerivAt_pi.mp (hu _ (hcast t ht)).2) i).real_of_complex
    rw [heq] at hh
    exact hh
  let J : OpenTimeInterval :=
    { carrier := ball s₀ a
      nonempty := ⟨s₀, mem_ball_self ha⟩
      ordConnected := (convex_ball s₀ a).ordConnected
      isOpen := isOpen_ball }
  have hxs : x s = ξ := by
    ext i
    simp [x, hinit]
  have hadm : ((s,ξ),p) ∈ F.domain := hxs ▸ hdomain s hs
  have hx : Specs.D13Unified.Ch01.SolutionConcepts.classicalIVPOnValue
      (atParameterValue F p) J x s ξ := by
    refine ⟨(classical_iff_solutionOn (atParameterValue F p) J x).mpr ?_, hs, hxs⟩
    refine ⟨?_, hdomain, ?_⟩
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      convert (hderiv t ht).hasDerivWithinAt using 1
      exact ParameterODE.atParameter_eval F p t (x t)
  obtain ⟨_, _, _, _, _, hcompare, _⟩ := ParameterODE.canonical_solution F hL s ξ p hadm
  obtain ⟨hsub, heq⟩ := hcompare J x hx
  intro t ht
  have htD : (t, ((s,ξ),p)) ∈ parameterSolutionDomainValue F := ⟨hadm, hsub ht⟩
  exact ⟨htD, (ParameterODE.solutionValue_on_domain F hL t s ξ p htD).1.trans (heq ht)⟩


/-- Restriction of a coordinate-holomorphic map to real inputs, followed by
real parts, has the literal absolutely convergent real coordinate series. -/
theorem coordinateRealAnalyticOn_real_restriction {d n : ℕ}
    {U : Set (Fin d → ℂ)} {V : Set (Fin d → ℝ)}
    {g : (Fin d → ℂ) → Fin n → ℂ} (hg : CoordinateHolomorphicOn U g)
    (hV : IsOpen V) (hmap : MapsTo complexifyPoint V U) :
    CoordinateRealAnalyticOn V (fun x i => (g (complexifyPoint x) i).re) := by
  apply coordinateRealAnalyticOn_of_local_extension
  intro a ha
  obtain ⟨r, hr, hrU, _⟩ := hg _ (hmap ha)
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV a ha
  refine ⟨min r s, lt_min hr hs, (ball_subset_ball (min_le_right _ _)).trans hsV,
    g, coordinateHolomorphicOn_mono hg isOpen_ball
      ((ball_subset_ball (min_le_left _ _)).trans hrU), fun _ _ => rfl⟩

/-- The local diagonal case, jointly in terminal time, starting time, initial
state and parameter. The curve is identified with the canonical real solution
on its actual maximal domain using the competitor clause of maximality. -/
theorem local_real_analytic_dependence :
    Specs.D13Unified.Ch06.RealAnalyticLocal.localRealAnalyticDependence_type := by
  intro n m F hf s₀ ξ₀ p₀ hadm
  let q₀ := realFieldPoint s₀ ξ₀ p₀
  have hq₀ : q₀ ∈ fieldData ⁻¹' F.domain := by simpa [q₀] using hadm
  obtain ⟨r, hr, hrU, g, hg, he, hsym⟩ := local_complexification hf q₀ hq₀
  have hc₀ : fieldPoint (s₀ : ℂ) (complexifyPoint ξ₀) (complexifyPoint p₀) =
      complexifyPoint q₀ := (complexifyPoint_realFieldPoint s₀ ξ₀ p₀).symm
  obtain ⟨a, e, b, c, ha, hepos, hea, hb, hc, W, hW, hdata⟩ :=
    (holomorphic_dependence n m (ball (complexifyPoint q₀) r) g
      (s₀ : ℂ) (complexifyPoint ξ₀) (complexifyPoint p₀)
      isOpen_ball (hc₀.symm ▸ mem_ball_self hr) hg).2
  let U := movingProduct (s₀ : ℂ) (complexifyPoint ξ₀) (complexifyPoint p₀) a e b c
  let V : Set (Fin (n+m+2) → ℝ) := complexifyPoint ⁻¹' U
  let G : MovingPoint n m → State n := fun q =>
    W (q 0) (Fin.tail q 0) (stateCoordinates (Fin.tail (Fin.tail q)))
      (parameterCoordinates (Fin.tail (Fin.tail q)))
  have hV : IsOpen V := (isOpen_movingProduct _ _ _ _ _ _ _).preimage
    (continuous_complexifyPoint _)
  have hcenter : Fin.cons s₀ q₀ ∈ V := by
    change complexifyPoint (Fin.cons s₀ q₀) ∈ U
    have hpack : complexifyPoint (Fin.cons s₀ q₀) =
        movingPoint (s₀ : ℂ) (s₀ : ℂ) (complexifyPoint ξ₀) (complexifyPoint p₀) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact congrFun (complexifyPoint_realFieldPoint s₀ ξ₀ p₀) j
    rw [hpack]
    simpa [U, movingProduct, movingPoint, fieldPoint] using
      (show (s₀ : ℂ) ∈ ball (s₀ : ℂ) a ∧ (s₀ : ℂ) ∈ ball (s₀ : ℂ) e ∧
        complexifyPoint ξ₀ ∈ ball (complexifyPoint ξ₀) b ∧
        complexifyPoint p₀ ∈ ball (complexifyPoint p₀) c from
        ⟨mem_ball_self ha, mem_ball_self hepos, mem_ball_self hb, mem_ball_self hc⟩)
  have hL := analytic_field_locallyLipschitz F hf
  have identify : ∀ q ∈ V, q ∈ solutionDomainInCoordinates F ∧
      solutionInCoordinates F q = fun i => (G (complexifyPoint q) i).re := by
    intro q hq
    let s := (fieldData (Fin.tail q)).1.1
    let ξ := (fieldData (Fin.tail q)).1.2
    let p := (fieldData (Fin.tail q)).2
    have hη : (s : ℂ) ∈ ball (s₀ : ℂ) e := hq.2.1
    have hξ : complexifyPoint ξ ∈ ball (complexifyPoint ξ₀) b := hq.2.2.1
    have hp : complexifyPoint p ∈ ball (complexifyPoint p₀) c := hq.2.2.2
    obtain ⟨hinit, hu, huniq⟩ := hdata (s : ℂ) hη (complexifyPoint ξ) hξ
      (complexifyPoint p) hp
    have hsC : (s : ℂ) ∈ ball (s₀ : ℂ) a := ball_subset_ball hea hη
    have hs : s ∈ ball s₀ a := by
      rw [mem_ball_iff_norm] at hsC ⊢
      rwa [← Complex.ofReal_sub, Complex.norm_real] at hsC
    have hreflect : ∀ z ∈ ball (complexifyPoint q₀) r,
        conjugatePoint z ∈ ball (complexifyPoint q₀) r := by
      intro z hz
      exact (conjugatePoint_mem_real_ball z q₀ r).mpr hz
    have hreal := complex_solution_real hreflect hsym hsC hinit hu huniq
    have ht : q 0 ∈ ball s₀ a := by
      have htC : (q 0 : ℂ) ∈ ball (s₀ : ℂ) a := hq.1
      rw [mem_ball_iff_norm] at htC ⊢
      rwa [← Complex.ofReal_sub, Complex.norm_real] at htC
    exact canonical_real_restriction F hL ha hs hrU he hinit hu hreal (q 0) ht
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV _ hcenter
  refine ⟨δ, hδ, fun q hq => (identify q (hδV hq)).1, ?_⟩
  have hRG : CoordinateRealAnalyticOn V
      (fun x i => (G (complexifyPoint x) i).re) :=
    coordinateRealAnalyticOn_real_restriction hW hV (fun _ hq => hq)
  exact (hRG.mono isOpen_ball hδV).congr
    (fun q hq => (identify q (hδV hq)).2)


/-- Finite composition preserves real coordinate analyticity. This helper is
also available to the separate long-time propagation step. -/
theorem CoordinateRealAnalyticOn.comp {d k n : ℕ}
    {U : Set (Fin d → ℝ)} {V : Set (Fin k → ℝ)}
    {f : (Fin d → ℝ) → Fin n → ℝ} {g : (Fin k → ℝ) → Fin d → ℝ}
    (hf : CoordinateRealAnalyticOn U f) (hg : CoordinateRealAnalyticOn V g)
    (_hV : IsOpen V) (hmap : MapsTo g V U) :
    CoordinateRealAnalyticOn V (f ∘ g) := by
  apply coordinateRealAnalyticOn_of_local_extension
  intro a ha
  obtain ⟨r, hr, _, F, hF, heF, _⟩ := local_complexification hf (g a) (hmap ha)
  obtain ⟨s, hs, hsV, G, hG, heG, _⟩ := local_complexification hg a ha
  have hGa : G (complexifyPoint a) = complexifyPoint (g a) := heG a (mem_ball_self hs)
  have hcont : ContinuousAt G (complexifyPoint a) :=
    hG.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hs))
  obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.mp hcont r hr
  let ρ := min s δ
  have hρ : 0 < ρ := lt_min hs hδ
  have hρG : MapsTo G (ball (complexifyPoint a) ρ) (ball (complexifyPoint (g a)) r) := by
    intro z hz
    rw [mem_ball] at hz ⊢
    rw [← hGa]
    exact hδG (hz.trans_le (min_le_right _ _))
  have hGc : CoordinateHolomorphicOn (ball (complexifyPoint a) ρ) G :=
    coordinateHolomorphicOn_mono hG isOpen_ball (ball_subset_ball (min_le_left _ _))
  refine ⟨ρ, hρ, (ball_subset_ball (min_le_left _ _)).trans hsV,
    F ∘ G, coordinateHolomorphicOn_comp hF hGc isOpen_ball hρG, ?_⟩
  intro x hx
  have hxs : x ∈ ball a s := ball_subset_ball (min_le_left _ _) hx
  have hcx : complexifyPoint x ∈ ball (complexifyPoint a) ρ :=
    (complexifyPoint_mem_ball x a ρ).mpr hx
  have hgr : g x ∈ ball (g a) r := by
    apply (complexifyPoint_mem_ball _ _ _).mp
    rw [← heG x hxs]
    exact hρG hcx
  simp only [Function.comp_apply, heG x hxs, heF _ hgr, complexifyPoint, Complex.ofReal_re]

end D13Unified.Ch06.RealAnalytic
