import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.DirectionalSupport
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.DifferentiabilityMonotonicity
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Module

noncomputable section
open Set Filter Topology
universe u
namespace VariationalNotes.ConvexAnalysis

private lemma finite_value {r : WithTop ℝ} (hr : r < ⊤) :
    r = ((r.untopD 0 : ℝ) : WithTop ℝ) := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hr)
  rw [← hs, WithTop.untopD_coe]

/-- A differentiable representative has its derivative as a global supporting
functional. Only local agreement with the extended function is needed. -/
lemma derivative_mem_subdifferential {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → WithTop ℝ} {g : E → ℝ} {x : E} {D : E →L[ℝ] ℝ}
    (hc : IsConvex f) (hlocal : ∀ᶠ z in 𝓝 x, f z = (g z : WithTop ℝ))
    (hd : HasFDerivAt g D x) : D ∈ subdifferential f x := by
  have hx := hlocal.self_of_nhds
  apply (mem_subdifferential_iff hx D).mpr
  intro z
  by_cases hz : f z = ⊤
  · simp [hz]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hz
  rw [← hr]
  apply WithTop.coe_le_coe.mpr
  have ht : Tendsto (fun t : ℝ => x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • (z - x)) := by fun_prop
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (g (x + t • (z - x)) - g x) ≤ r - g x := by
    filter_upwards [ht.eventually hlocal, self_mem_nhdsWithin,
      ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds)] with t he ht0 ht1
    have h := convex_upper_bound hc hx.le hr.symm.le (show 0 ≤ 1 - t by linarith) ht0.le
      (show 1 - t + t = 1 by ring)
    have hv : (1 - t) • x + t • z = x + t • (z - x) := by module
    rw [hv, he, WithTop.coe_le_coe] at h
    apply (inv_mul_le_iff₀ ht0).mpr
    nlinarith
  have hlim := (hd.hasLineDerivAt (z - x)).tendsto_slope_zero_right
  simp only [smul_eq_mul] at hlim
  have h := le_of_tendsto hlim hb
  linarith

lemma subgradient_eq_of_hasFDerivAt {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → WithTop ℝ} {g : E → ℝ} {x : E} {D y : E →L[ℝ] ℝ}
    (hlocal : ∀ᶠ z in 𝓝 x, f z = (g z : WithTop ℝ))
    (hd : HasFDerivAt g D x) (hy : y ∈ subdifferential f x) : y = D := by
  have hs := (mem_subdifferential_iff hlocal.self_of_nhds y).mp hy
  have hmin : IsLocalMin (fun z => g z - y z) x := by
    filter_upwards [hlocal] with z hz
    have h := hs z
    rw [hz, WithTop.coe_le_coe, map_sub] at h
    linarith
  have hzero := hmin.hasFDerivAt_eq_zero (hd.sub y.hasFDerivAt)
  exact (sub_eq_zero.mp hzero).symm

theorem subdifferential_eq_singleton_of_hasFDerivAt :
    Specs.subdifferential_eq_singleton_of_hasFDerivAt.{u} := by
  intro E _ _ f _ hc x D hx hd
  have hlocal : ∀ᶠ z in 𝓝 x, f z = (((f z).untopD 0 : ℝ) : WithTop ℝ) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hx] with z hz
    exact finite_value hz
  ext y
  constructor
  · exact fun hy => subgradient_eq_of_hasFDerivAt hlocal hd hy
  · intro hy
    have he : y = D := hy
    rw [he]
    exact derivative_mem_subdifferential hc hlocal hd

theorem subdifferential_monotone : Specs.subdifferential_monotone.{u} := by
  intro E _ _ _ f x₁ x₂ y₁ y₂ hy₁ hy₂
  obtain ⟨r₁, hr₁, hs₁⟩ := hy₁
  obtain ⟨r₂, hr₂, hs₂⟩ := hy₂
  have h₁ := hs₁ x₂
  have h₂ := hs₂ x₁
  rw [hr₂, WithTop.coe_le_coe, map_sub] at h₁
  rw [hr₁, WithTop.coe_le_coe, map_sub] at h₂
  simp only [sub_apply, map_sub]
  linarith

theorem convexOn_iff_derivative_supports : Specs.convexOn_iff_derivative_supports.{u} := by
  intro E _ _ U g D hU hconv hd
  constructor
  · intro hg x hx z hz
    have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        t⁻¹ * (g (x + t • (z - x)) - g x) ≤ g z - g x := by
      filter_upwards [self_mem_nhdsWithin,
        ((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
          nhdsWithin_le_nhds)] with t ht0 ht1
      have h := hg.2 hx hz (show 0 ≤ 1-t by linarith) ht0.le
        (show 1-t+t=1 by ring)
      have hv : (1 - t) • x + t • z = x + t • (z - x) := by module
      rw [hv] at h
      apply (inv_mul_le_iff₀ ht0).mpr
      simp only [smul_eq_mul] at h
      nlinarith
    have hlim := ((hd x hx).hasLineDerivAt (z-x)).tendsto_slope_zero_right
    simp only [smul_eq_mul] at hlim
    have h := le_of_tendsto hlim hb
    linarith
  · intro hs
    refine ⟨hconv, ?_⟩
    intro x hx z hz a b ha hb hab
    let w := a • x + b • z
    have hw : w ∈ U := hconv hx hz ha hb hab
    have h₁ := hs w hw x hx
    have h₂ := hs w hw z hz
    have hlin : a * (D w) (x - w) + b * (D w) (z - w) = 0 := by
      rw [← smul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_smul, ← map_add]
      have hv : a • (x-w) + b • (z-w) = 0 := by
        calc
          _ = a • x + b • z - (a+b) • w := by module
          _ = 0 := by rw [hab, one_smul]; exact sub_self w
      rw [hv, map_zero]
    change g w ≤ a * g x + b * g z
    nlinarith [congrArg (fun t : ℝ => t * g w) hab, mul_nonneg ha (sub_nonneg.mpr h₁), mul_nonneg hb (sub_nonneg.mpr h₂)]

def negativeSqrt (t : ℝ) : WithTop ℝ := Specs.negativeSqrt t

lemma negativeSqrt_proper : Proper negativeSqrt := by
  exact ⟨0, by simp [negativeSqrt, Specs.negativeSqrt]⟩

lemma negativeSqrt_convex : IsConvex negativeSqrt := by
  have hsqrt : ConcaveOn ℝ (Ici 0) Real.sqrt := by
    change ConcaveOn ℝ (Ici 0) (fun x => Real.sqrt x)
    simpa only [Real.sqrt_eq_rpow, one_div] using
      (Real.concaveOn_rpow (p := 1 / 2) (by norm_num) (by norm_num))
  apply (convex_iff_twoPoint negativeSqrt).mpr
  intro x y r s hx hy a b ha hb hab
  have hx0 : 0 ≤ x := by
    by_contra h
    simp [negativeSqrt, Specs.negativeSqrt, h] at hx
  have hy0 : 0 ≤ y := by
    by_contra h
    simp [negativeSqrt, Specs.negativeSqrt, h] at hy
  have hr : -Real.sqrt x = r := by
    change (if 0 ≤ x then ((-Real.sqrt x : ℝ) : WithTop ℝ) else ⊤) = _ at hx
    rw [ite_eq_left hx0] at hx
    exact WithTop.coe_inj.mp hx
  have hs : -Real.sqrt y = s := by
    change (if 0 ≤ y then ((-Real.sqrt y : ℝ) : WithTop ℝ) else ⊤) = _ at hy
    rw [ite_eq_left hy0] at hy
    exact WithTop.coe_inj.mp hy
  have hz0 : 0 ≤ a • x + b • y := by
    simp only [smul_eq_mul]
    positivity
  change (if 0 ≤ a • x + b • y then
    ((-Real.sqrt (a • x + b • y) : ℝ) : WithTop ℝ) else ⊤) ≤ _
  rw [ite_eq_left hz0, WithTop.coe_le_coe]
  simp only [smul_eq_mul]
  have h := hsqrt.2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at h
  rw [← hr, ← hs]
  linarith

lemma negativeSqrt_lowerSemicontinuous : IsLowerSemicontinuous negativeSqrt := by
  apply (lowerSemicontinuous_iff_closed_epigraph negativeSqrt).mpr
  have hepi : Specs.epigraph negativeSqrt =
      {p : ℝ × ℝ | 0 ≤ p.1} ∩ {p : ℝ × ℝ | -Real.sqrt p.1 ≤ p.2} := by
    ext p
    by_cases hp : 0 ≤ p.1 <;>
      simp only [Specs.epigraph, negativeSqrt, Specs.negativeSqrt, mem_ofPred_eq, mem_inter_iff, hp,
        ite_true, ite_false, WithTop.coe_le_coe, top_le_iff, WithTop.coe_ne_top, true_and, false_and]
  rw [hepi]
  exact (isClosed_le continuous_const continuous_fst).inter
    (isClosed_le (Real.continuous_sqrt.comp continuous_fst).neg continuous_snd)

lemma negativeSqrt_directionalDerivative : directionalDerivative negativeSqrt 0 1 = ⊥ := by
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro r
  let c : ℝ := |r| + 1
  have hc : 0 < c := by dsimp [c]; positivity
  let t : ℝ := (c⁻¹) ^ 2
  have ht : 0 < t := sq_pos_of_pos (inv_pos.mpr hc)
  have hq : directionalQuotient negativeSqrt 0 1 t = ((-c : ℝ) : EReal) := by
    have hval : negativeSqrt (0 + t • (1 : ℝ)) = ((-c⁻¹ : ℝ) : WithTop ℝ) := by
      simp only [smul_eq_mul, mul_one, zero_add]
      change (if 0 ≤ t then ((-Real.sqrt t : ℝ) : WithTop ℝ) else ⊤) = _
      rw [ite_eq_left ht.le]
      dsimp [t]
      rw [Real.sqrt_sq (inv_nonneg.mpr hc.le)]
    rw [directionalQuotient, Specs.directionalQuotient, hval]
    simp only [WithTop.coe_ne_top, ↓reduceIte, WithTop.untopD_coe]
    have hzero : negativeSqrt 0 = (0 : WithTop ℝ) := by
      simp [negativeSqrt, Specs.negativeSqrt]
    rw [hzero]
    simp only [WithTop.untopD_zero, sub_zero]
    congr 1
    dsimp [t]
    field_simp [ne_of_gt hc]
  have hi : directionalDerivative negativeSqrt 0 1 ≤ directionalQuotient negativeSqrt 0 1 t :=
    iInf_le (fun u : {t : ℝ // 0 < t} => directionalQuotient negativeSqrt 0 1 u) ⟨t, ht⟩
  rw [hq] at hi
  apply lt_of_le_of_lt hi
  apply EReal.coe_lt_coe_iff.mpr
  dsimp [c]
  linarith [neg_abs_le r]

lemma negativeSqrt_subdifferential : subdifferential negativeSqrt 0 = ∅ := by
  change Specs.subdifferential negativeSqrt 0 = ∅
  rw [subdifferential_eq_directional_le negativeSqrt negativeSqrt_proper negativeSqrt_convex 0
    (by simp [negativeSqrt, Specs.negativeSqrt])]
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have h := hy 1
  change (y 1 : EReal) ≤ directionalDerivative negativeSqrt 0 1 at h
  rw [negativeSqrt_directionalDerivative] at h
  exact (EReal.coe_ne_bot (y 1)) (le_bot_iff.mp h)

theorem negativeSqrt_boundary : Specs.negativeSqrt_boundary :=
  ⟨negativeSqrt_proper, negativeSqrt_convex, negativeSqrt_lowerSemicontinuous,
    negativeSqrt_directionalDerivative, negativeSqrt_subdifferential⟩

/-- In finite dimension, local Lipschitz continuity makes convergence of
directional quotients to a continuous linear map into a Fréchet derivative.
The normalized increments lie in the compact closed unit ball. -/
lemma hasFDerivAt_of_lipschitz_directional {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {g : E → ℝ} {x : E} {D : E →L[ℝ] ℝ} {U : Set E} {K : NNReal}
    (hU : U ∈ 𝓝 x) (hLip : LipschitzOnWith K g U)
    (hdir : ∀ d, Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t)
      (𝓝[>] 0) (𝓝 (D d))) : HasFDerivAt g D x := by
  apply hasFDerivAt_iff_tendsto.mpr
  apply tendsto_of_subseq_tendsto
  intro v hv
  by_cases hz : ∃ᶠ n in atTop, v n = x
  · obtain ⟨φ, _, hφ⟩ := exists_seq_forall_of_frequently hz
    refine ⟨φ, ?_⟩
    simp only [hφ, sub_self, map_zero, norm_zero, inv_zero, mul_zero]
    exact tendsto_const_nhds
  have hne : ∀ᶠ n in atTop, v n ≠ x := not_frequently.mp hz
  let dir : ℕ → E := fun n => ‖v n - x‖⁻¹ • (v n - x)
  obtain ⟨d, _, φ, hφ, hconv⟩ := (isCompact_closedBall (0 : E) 1).tendsto_subseq
    (fun n => show dir n ∈ Metric.closedBall (0 : E) 1 from
      inv_norm_smul_mem_unitClosedBall (v n - x))
  let t : ℕ → ℝ := fun n => ‖v (φ n) - x‖
  let dn : ℕ → E := dir ∘ φ
  have hvφ := hv.comp hφ.tendsto_atTop
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa [t] using (hvφ.sub_const x).norm
  have htpos : ∀ᶠ n in atTop, 0 < t n := by
    filter_upwards [hφ.tendsto_atTop.eventually hne] with n hn
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  have ht' : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨ht, htpos⟩
  have hpoint : Tendsto (fun n => x + t n • d) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add (ht.smul_const d)
  have hq := (hdir d).comp ht'
  have hD : Tendsto (fun n => D (dn n)) atTop (𝓝 (D d)) :=
    D.continuous.continuousAt.tendsto.comp hconv
  have hbound : Tendsto (fun n => (K : ℝ) * ‖dn n - d‖ +
      |(g (x + t n • d) - g x) / t n - D (dn n)|) atTop (𝓝 0) := by
    have h₁ := (tendsto_const_nhds (x := (K : ℝ))).mul ((hconv.sub_const d).norm)
    have h₂ := (hq.sub hD).abs
    simpa [dn] using h₁.add h₂
  refine ⟨φ, squeeze_zero' (Eventually.of_forall (fun n => ?_)) ?_ hbound⟩
  · positivity
  filter_upwards [htpos, hvφ.eventually hU, hpoint.eventually hU] with n hn hvn hpn
  have htn : t n ≠ 0 := ne_of_gt hn
  have hrep : t n • dn n = v (φ n) - x := by
    change ‖v (φ n) - x‖ • (‖v (φ n) - x‖⁻¹ • (v (φ n) - x)) = _
    rw [smul_smul, mul_inv_cancel₀ htn, one_smul]
  have hdiff : v (φ n) - (x + t n • d) = t n • (dn n - d) := by
    rw [smul_sub, hrep]
    abel
  have hdist := hLip.dist_le_mul (v (φ n)) hvn (x + t n • d) hpn
  rw [Real.dist_eq, dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg hn.le] at hdist
  have hdist' : |(g (v (φ n)) - g (x + t n • d)) / t n| ≤ (K : ℝ) * ‖dn n - d‖ := by
    rw [abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    nlinarith only [hdist]
  have herr : ‖v (φ n) - x‖⁻¹ * ‖g (v (φ n)) - g x - D (v (φ n) - x)‖ =
      |(g (v (φ n)) - g x) / t n - D (dn n)| := by
    have hDrep : D (v (φ n) - x) = t n * D (dn n) := by
      rw [← hrep, map_smul, smul_eq_mul]
    rw [hDrep, Real.norm_eq_abs]
    change (t n)⁻¹ * |g (v (φ n)) - g x - t n * D (dn n)| = _
    rw [← abs_of_pos (inv_pos.mpr hn), ← abs_mul]
    congr 1
    field_simp
  rw [herr]
  calc
    _ = |(g (v (φ n)) - g (x + t n • d)) / t n +
        ((g (x + t n • d) - g x) / t n - D (dn n))| := by congr 1; ring
    _ ≤ |(g (v (φ n)) - g (x + t n • d)) / t n| +
        |(g (x + t n • d) - g x) / t n - D (dn n)| := abs_add_le _ _
    _ ≤ _ := add_le_add hdist' le_rfl

theorem hasFDerivAt_of_subdifferential_singleton :
    Specs.hasFDerivAt_of_subdifferential_singleton.{u} := by
  intro E _ _ _ f hp hc x D hx hsing
  change x ∈ interior (effectiveDomain f) at hx
  let g : E → ℝ := fun z => (f z).untopD 0
  have hcv : ConvexOn ℝ (effectiveDomain f) g :=
    convexOn_untopD_comp hc (AffineMap.id ℝ E) (convex_effectiveDomain hc)
      (fun _ hz => hz)
  obtain ⟨K, U, hU, hLip⟩ := hcv.locallyLipschitzOn_interior hx
  rw [isOpen_interior.nhdsWithin_eq hx] at hU
  let V := U ∩ effectiveDomain f
  have hV : V ∈ 𝓝 x := inter_mem hU (mem_interior_iff_mem_nhds.mp hx)
  have hfin : ∀ z ∈ V, f z < ⊤ := fun _ hz => hz.2
  have hLV : LipschitzOnWith K g V := hLip.mono inter_subset_left
  apply hasFDerivAt_of_lipschitz_directional hV hLV
  intro d
  obtain ⟨y, hy, heq, _⟩ := directionalDerivative_max_of_localLipschitz
    hp hc hV hfin hLV d
  have hyD : y = D := by
    change y ∈ Specs.subdifferential f x at hy
    rw [hsing] at hy
    exact hy
  rw [hyD] at heq
  have hlim := directionalQuotient_tendsto f hp hc x (hfin x (mem_of_mem_nhds hV)) d
  change Tendsto (directionalQuotient f x d) (𝓝[>] 0)
    (𝓝 (directionalDerivative f x d)) at hlim
  rw [heq] at hlim
  have ht : Tendsto (fun t : ℝ => x + t • d) (𝓝[>] 0) (𝓝 x) := by
    have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hevent : directionalQuotient f x d =ᶠ[𝓝[>] 0]
      (fun t : ℝ => (((g (x + t • d) - g x) / t : ℝ) : EReal)) := by
    filter_upwards [ht.eventually hV] with t ht
    exact directionalQuotient_of_finite (hfin _ ht)
  exact EReal.tendsto_coe.mp (hlim.congr' hevent)

end VariationalNotes.ConvexAnalysis
