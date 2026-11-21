import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.NonlinearMonotoneEvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.NonlinearYosidaEvolution
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

noncomputable section
open Filter MeasureTheory Set
open scoped Topology NNReal
namespace ExpandedFA.Evolution.NonlinearMonotoneEvolution
universe u

/-- Uniform Cauchy convergence extends from a set of initial data to its closure
when the approximating maps are contractions, uniformly in time. -/
theorem uniform_cauchy_on_closure {H : Type u} [NormedAddCommGroup H]
    (F : ℝ → H → ℝ → H) (D s : Set ℝ) (B : Set H)
    (hF : ∀ lam ∈ D, ∀ x y t, t ∈ s → ‖F lam x t - F lam y t‖ ≤ ‖x - y‖)
    (hD : D ∈ 𝓝[>] (0 : ℝ))
    (hB : ∀ y ∈ B, UniformCauchySeqOn (fun lam => F lam y) (𝓝[>] (0 : ℝ)) s)
    {x : H} (hx : x ∈ closure B) :
    UniformCauchySeqOn (fun lam => F lam x) (𝓝[>] (0 : ℝ)) s := by
  intro V hV
  obtain ⟨ε, hε, hVε⟩ := Metric.mem_uniformity_dist.mp hV
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
  have hsmall := hB y hy _ (Metric.dist_mem_uniformity (by positivity : 0 < ε / 3))
  have hD₁ : ∀ᶠ q : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)), q.1 ∈ D :=
    tendsto_fst.eventually hD
  have hD₂ : ∀ᶠ q : ℝ × ℝ in (𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ)), q.2 ∈ D :=
    tendsto_snd.eventually hD
  filter_upwards [hsmall, hD₁, hD₂] with q hq hq₁ hq₂
  intro t ht
  apply hVε
  have h₁ := hF q.1 hq₁ x y t ht
  have h₂ := hF q.2 hq₂ y x t ht
  have h₃ := hq t ht
  simp only [dist_eq_norm] at hxy h₃ ⊢
  rw [norm_sub_rev y x] at h₂
  calc
    ‖F q.1 x t - F q.2 x t‖ ≤
        ‖F q.1 x t - F q.1 y t‖ + ‖F q.1 y t - F q.2 y t‖ +
          ‖F q.2 y t - F q.2 x t‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _ |>.trans
            (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ < ε := by linarith

/-- The regularized flows have a uniform limit for every initial value in the
closure of the graph domain, without a separability assumption. -/
theorem closure_uniform_limit {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (honto : ∀ lam : ℝ, 0 < lam → MonotoneGraphResolvents.ShiftOnto H A lam)
    (F : ℝ → H → ℝ → H)
    (hF : ∀ lam : ℝ, ∀ hlam : 0 < lam, ∀ x : H,
      Spec.GlobalApproximation A lam (honto lam hlam) x (F lam x))
    {x : H} (hx : x ∈ closure (Spec.domain A)) :
    ∃ u : ℝ → H, u 0 = x ∧
      ∀ T : ℝ, 0 < T → TendstoUniformlyOn (fun lam => F lam x) u
        (𝓝[>] (0 : ℝ)) (Icc 0 T) := by
  have hcauchy (T : ℝ) (hT : 0 < T) :
      UniformCauchySeqOn (fun lam => F lam x) (𝓝[>] (0 : ℝ)) (Icc 0 T) := by
    apply uniform_cauchy_on_closure F (Ioi 0) (Icc 0 T) (Spec.domain A) ?_
      self_mem_nhdsWithin ?_ hx
    · intro lam hlam y z t ht
      exact NonlinearYosidaEvolution.approximate_contraction H A hm lam hlam (honto lam hlam) y z
        (F lam y) (F lam z) (hF lam hlam y) (hF lam hlam z) t ht.1
    · rintro y ⟨a, hya⟩
      obtain ⟨u, _, _, hu⟩ := NonlinearYosidaEvolution.approximate_uniform_limit H A hm honto F hF y a hya
      exact (hu T hT).uniformCauchySeqOn
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      ∃ y : H, Tendsto (fun lam => F lam x t) (𝓝[>] (0 : ℝ)) (𝓝 y) :=
    cauchy_map_iff_exists_tendsto.mp
      ((hcauchy (t + 1) (by linarith)).cauchy_map ⟨ht, by linarith⟩)
  let u : ℝ → H := fun t => if ht : 0 ≤ t then (hpoint t ht).choose else x
  have hu (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun lam => F lam x t) (𝓝[>] (0 : ℝ)) (𝓝 (u t)) := by
    simpa only [u, dite_eq_left ht] using (hpoint t ht).choose_spec
  refine ⟨u, ?_, ?_⟩
  · apply tendsto_nhds_unique (hu 0 le_rfl)
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact (hF lam hlam x).1.symm
  · intro T hT
    exact (hcauchy T hT).tendstoUniformlyOn_of_tendsto (fun t ht => hu t ht.1)



open MonotoneGraphResolvents NonlinearYosidaEvolution

/-- Autonomous regularized flows satisfy the forward semigroup law. -/
theorem approximation_flow {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (lam : ℝ) (hlam : 0 < lam) (ho : ShiftOnto H A lam)
    (F : H → ℝ → H) (hF : ∀ x, Spec.GlobalApproximation A lam ho x (F x))
    (x : H) (s t : ℝ) (ht : 0 ≤ t) : F x (s + t) = F (F x s) t := by
  have hshift : Spec.GlobalApproximation A lam ho (F x s) (fun r => F x (s + r)) := by
    refine ⟨by simp, ?_⟩
    intro r
    simpa only [Function.comp_def, one_smul] using ((hF x).2 (s + r)).scomp r ((hasDerivAt_id r).const_add s)
  have h := approximate_contraction H A hm lam hlam ho (F x s) (F x s)
    (fun r => F x (s + r)) (F (F x s)) hshift (hF _) t ht
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using h

/-- Changing a trajectory on negative times does not change its forward a.e.
differential inclusion. The endpoint is removed using the null singleton. -/
theorem inclusion_congr {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H)) {u v : ℝ → H} (heq : ∀ t, 0 ≤ t → v t = u t)
    (hu : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t) :
    ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (v t, a) ∈ A ∧ HasDerivAt v (-a) t := by
  rw [ae_restrict_iff' measurableSet_Ici] at hu ⊢
  filter_upwards [hu, (volume.ae_ne (0 : ℝ))] with t ht hne hnonneg
  obtain ⟨a, ha, hder⟩ := ht hnonneg
  have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hne)
  refine ⟨a, by simpa only [heq t hnonneg] using ha, ?_⟩
  apply hder.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htpos] with r hr
  exact heq r hr.le

/-- Construction on the entire closed domain by limits of regularized flows. -/
theorem semigroup_existence : Spec.SemigroupExistence.{u} := by
  intro H _ _ _ A hm ho
  classical
  obtain ⟨F, hF, hcontract, hsol⟩ := yosida_evolution H A hm ho
  have hlim (x : H) (hx : x ∈ closure (Spec.domain A)) :=
    closure_uniform_limit A hm ho F hF hx
  let U : H → ℝ → H := fun x =>
    if hx : x ∈ closure (Spec.domain A) then (hlim x hx).choose else fun _ => x
  have hU (x : H) (hx : x ∈ closure (Spec.domain A)) :
      U x 0 = x ∧ ∀ T : ℝ, 0 < T →
        TendstoUniformlyOn (fun lam => F lam x) (U x) (𝓝[>] (0 : ℝ)) (Icc 0 T) := by
    simpa only [U, dite_eq_left hx] using (hlim x hx).choose_spec
  have hp (x : H) (hx : x ∈ closure (Spec.domain A)) (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun lam => F lam x t) (𝓝[>] (0 : ℝ)) (𝓝 (U x t)) :=
    ((hU x hx).2 (t + 1) (by linarith)).tendsto_at ⟨ht, by linarith⟩
  have hc (x y : H) (hx : x ∈ closure (Spec.domain A))
      (hy : y ∈ closure (Spec.domain A)) (t : ℝ) (ht : 0 ≤ t) :
      ‖U x t - U y t‖ ≤ ‖x - y‖ := by
    apply le_of_tendsto (((hp x hx t ht).sub (hp y hy t ht)).norm)
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    exact hcontract lam hlam x y t ht
  have hd (x a₀ : H) (hxa : (x, a₀) ∈ A) :
      LipschitzOnWith ‖a₀‖₊ (U x) (Ici 0) ∧
      ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
        ∃ a : H, (U x t, a) ∈ A ∧ HasDerivAt (U x) (-a) t := by
    have hx : x ∈ closure (Spec.domain A) := subset_closure ⟨a₀, hxa⟩
    obtain ⟨_, u, _, hlu, hconv, hincl⟩ := hsol x a₀ hxa
    have heq (t : ℝ) (ht : 0 ≤ t) : U x t = u t :=
      tendsto_nhds_unique (hp x hx t ht)
        ((hconv (t + 1) (by linarith)).tendsto_at ⟨ht, by linarith⟩)
    refine ⟨?_, inclusion_congr A heq hincl⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [heq s hs, heq t ht] using hlu.dist_le_mul s hs t ht
  have hcont (x : H) (hx : x ∈ closure (Spec.domain A)) :
      ContinuousOn (U x) (Ici 0) := by
    intro t ht
    have hct : ContinuousOn (U x) (Icc 0 (t + 1)) :=
      ((hU x hx).2 (t + 1) (by have ht0 : 0 ≤ t := ht; linarith)).continuousOn (by
        apply Filter.Eventually.frequently
        filter_upwards [self_mem_nhdsWithin] with lam hlam
        exact (continuous_iff_continuousAt.mpr (fun r => ((hF lam hlam x).2 r).continuousAt)).continuousOn)
    apply (hct t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin
    have hne : Iic (t + 1) ∈ 𝓝 t := Iic_mem_nhds (by linarith)
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hne)
  have hinvD (x a₀ : H) (hxa : (x, a₀) ∈ A) (t : ℝ) (ht : 0 ≤ t) :
      U x t ∈ closure (Spec.domain A) := by
    have hx : x ∈ closure (Spec.domain A) := subset_closure ⟨a₀, hxa⟩
    let G : ℝ → H := fun lam => if hlam : 0 < lam then
      MonotoneGraphResolvents.Spec.ResolventValue H A lam (ho lam hlam) (F lam x t) else x
    have hdist : Tendsto (fun lam => dist (F lam x t) (G lam))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_
        (show Tendsto (fun lam : ℝ => lam * ‖a₀‖) (𝓝[>] (0 : ℝ)) (𝓝 0) from by
          simpa using (tendsto_id.mono_right nhdsWithin_le_nhds : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0)).mul_const ‖a₀‖)
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      have hl : 0 < lam := hlam
      simp only [G, dite_eq_left hl, dist_eq_norm]
      have heq : F lam x t - Spec.R.J H A lam (ho lam hl) (F lam x t) =
          lam • MonotoneGraphResolvents.Spec.YosidaValue H A lam (ho lam hl) (F lam x t) := by
        apply sub_eq_iff_eq_add.mpr
        exact (resolvent_identity H A lam hl (ho lam hl) (F lam x t)).trans (add_comm _ _)
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hl]
      exact mul_le_mul_of_nonneg_left ((hsol x a₀ hxa).1 lam hlam t ht) hlam.le
    apply isClosed_closure.mem_of_tendsto ((hp x hx t ht).congr_dist hdist)
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    apply subset_closure
    refine ⟨MonotoneGraphResolvents.Spec.YosidaValue H A lam (ho lam hlam) (F lam x t), ?_⟩
    simpa only [G, dite_eq_left (show 0 < lam from hlam)] using yosida_graph H A lam hlam (ho lam hlam) (F lam x t)
  have hinv (x : H) (hx : x ∈ closure (Spec.domain A)) (t : ℝ) (ht : 0 ≤ t) :
      U x t ∈ closure (Spec.domain A) := by
    rw [← closure_closure (s := Spec.domain A)]
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨y, ⟨a, hya⟩, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
    refine ⟨U y t, hinvD y a hya t ht, ?_⟩
    rw [dist_eq_norm] at hxy ⊢
    exact (hc x y hx (subset_closure ⟨a, hya⟩) t ht).trans_lt hxy
  have hflow (x : H) (hx : x ∈ closure (Spec.domain A))
      (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : U x (s + t) = U (U x s) t := by
    have hin := hinv x hx s hs
    have he : Tendsto (fun lam => dist (F lam (U x s) t) (F lam x (s + t)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => dist_nonneg)) ?_
        (show Tendsto (fun lam => dist (U x s) (F lam x s))
          (𝓝[>] (0 : ℝ)) (𝓝 0) from by
          simpa using (tendsto_const_nhds (x := U x s)).dist (hp x hx s hs))
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      rw [approximation_flow A hm lam hlam (ho lam hlam) (F lam) (hF lam hlam) x s t ht]
      simpa only [dist_eq_norm] using hcontract lam hlam (U x s) (F lam x s) t ht
    exact tendsto_nhds_unique (hp x hx (s + t) (add_nonneg hs ht))
      ((hp (U x s) hin t ht).congr_dist he)
  refine ⟨F, (fun t x => U x t), hF, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun x hx => (hU x hx).1
  · exact fun x hx t ht => hinv x hx t ht
  · exact fun t ht x hx y hy => hc x y hx hy t ht
  · exact fun s hs t ht x hx => hflow x hx s t hs ht
  · exact hcont
  · exact fun x hx => (hU x hx).2
  · exact hd



/-- The fundamental theorem for absolutely continuous real functions gives a
linear upper bound from an almost-everywhere upper bound on the derivative. -/
theorem ac_image_sub_le {f : ℝ → ℝ} {s t c : ℝ} (hst : s ≤ t)
    (hf : AbsolutelyContinuousOnInterval f s t)
    (hd : ∀ᵐ r ∂(volume.restrict (Icc s t)), deriv f r ≤ c) :
    f t - f s ≤ c * (t - s) := by
  have h := intervalIntegral.integral_mono_ae_restrict hst hf.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume s t) hd
  rwa [hf.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul, mul_comm] at h

/-- Forward Lipschitz strong solutions contract, including arbitrary constants
for their Lipschitz bounds. -/
theorem strong_contraction {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (x y : H) (u v : ℝ → H) (hu : Spec.StrongSolution A x u)
    (hv : Spec.StrongSolution A y v) (t : ℝ) (ht : 0 ≤ t) :
    ‖u t - v t‖ ≤ ‖x - y‖ := by
  obtain ⟨hu0, ⟨Cu, hLu⟩, hdu⟩ := hu
  obtain ⟨hv0, ⟨Cv, hLv⟩, hdv⟩ := hv
  have huAC : AbsolutelyContinuousOnInterval u 0 t :=
    (hLu.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).absolutelyContinuousOnInterval
  have hvAC : AbsolutelyContinuousOnInterval v 0 t :=
    (hLv.mono (by rw [uIcc_of_le ht]; exact Icc_subset_Ici_self)).absolutelyContinuousOnInterval
  have hnAC := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval (huAC.sub hvAC)
  have hfAC : AbsolutelyContinuousOnInterval (fun r => ‖u r - v r‖ ^ 2) 0 t := by
    convert hnAC.mul hnAC using 1
    funext r
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, pow_two]
  have hnonpos : ∀ᵐ r ∂(volume.restrict (Icc 0 t)),
      deriv (fun r => ‖u r - v r‖ ^ 2) r ≤ 0 := by
    rw [ae_restrict_iff' measurableSet_Ici] at hdu hdv
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hdu, hdv] with r hur hvr hr
    obtain ⟨a, ha, hda⟩ := hur hr.1
    obtain ⟨b, hb, hdb⟩ := hvr hr.1
    have hmono := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hm ha hb
    change deriv (fun r => ‖(u - v) r‖ ^ 2) r ≤ 0
    rw [((hda.sub hdb).norm_sq).deriv]
    simp only [Pi.sub_apply, inner_sub_right, inner_neg_right]
    rw [real_inner_comm] at hmono
    rw [inner_sub_right] at hmono
    linarith
  have h := ac_image_sub_le ht hfAC hnonpos
  rw [hu0, hv0, zero_mul] at h
  nlinarith [norm_nonneg (u t - v t), norm_nonneg (x - y)]

/-- Uniqueness is in the full Lipschitz strong-solution class. -/
theorem strong_unique {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (x : H) (u v : ℝ → H) (hu : Spec.StrongSolution A x u)
    (hv : Spec.StrongSolution A x v) (t : ℝ) (ht : 0 ≤ t) : u t = v t := by
  have h := strong_contraction A hm x x u v hu hv t ht
  simpa only [sub_self, norm_zero, norm_le_zero_iff, sub_eq_zero] using h



/-- The graph velocities of the implicit scheme never exceed the chosen
initial graph velocity. -/
theorem implicit_speed_bound {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (h : ℝ) (hh : 0 < h) (ho : ShiftOnto H A h) (x a₀ : H) (hxa : (x, a₀) ∈ A) :
    ∀ n : ℕ, ‖MonotoneGraphResolvents.Spec.YosidaValue H A h ho
      ((MonotoneGraphResolvents.Spec.ResolventValue H A h ho)^[n] x)‖ ≤ ‖a₀‖ := by
  intro n
  induction n with
  | zero => exact initial_yosida_bound H A hm h hh ho x a₀ hxa
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (initial_yosida_bound H A hm h hh ho _ _
      (yosida_graph H A h hh ho _)).trans ih

/-- One implicit step compared with a Lipschitz strong solution. The affine
interpolant is used only on this one interval, so no piecewise differentiation
or choice of a mesh-dependent null set is needed. -/
theorem implicit_step_energy {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (u : ℝ → H) (C : ℝ≥0) (hLu : LipschitzOnWith C u (Ici 0))
    (hu : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t)
    (z a : H) (hza : (z, a) ∈ A) (ha : ‖a‖ ≤ C)
    (s h : ℝ) (hs : 0 ≤ s) (hh : 0 < h) :
    ‖z - u (s + h)‖ ^ 2 ≤ ‖z + h • a - u s‖ ^ 2 + 4 * h ^ 2 * (C : ℝ) ^ 2 := by
  let P : ℝ → H := fun r => z + (s + h - r) • a
  have hP (r : ℝ) : HasDerivAt P (-a) r := by
    convert (((hasDerivAt_const r (s + h)).sub (hasDerivAt_id r)).smul_const a).const_add z using 1 <;>
      simp [P]
  have hLP : LipschitzOnWith ‖a‖₊ P (uIcc s (s + h)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_uIcc s (s + h))
      (fun r _ => (hP r).hasDerivWithinAt)
    intro r hr
    simp only [nnnorm_neg, le_refl]
  have huAC : AbsolutelyContinuousOnInterval u s (s + h) :=
    (hLu.mono (by
      rw [uIcc_of_le (by linarith)]
      exact fun r hr => hs.trans hr.1)).absolutelyContinuousOnInterval
  have hnAC := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval
    (hLP.absolutelyContinuousOnInterval.sub huAC)
  have hfAC : AbsolutelyContinuousOnInterval (fun r => ‖P r - u r‖ ^ 2) s (s + h) := by
    convert hnAC.mul hnAC using 1
    funext r
    simp only [Pi.mul_apply, Pi.sub_apply, Function.comp_def, pow_two]
  have hder : ∀ᵐ r ∂(volume.restrict (Icc s (s + h))),
      deriv (fun r => ‖P r - u r‖ ^ 2) r ≤ 4 * h * (C : ℝ) ^ 2 := by
    rw [ae_restrict_iff' measurableSet_Ici] at hu
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hu, volume.ae_ne (0 : ℝ)] with r hur hne hr
    have hrnonneg : 0 ≤ r := hs.trans hr.1
    have hrpos : 0 < r := lt_of_le_of_ne hrnonneg (Ne.symm hne)
    obtain ⟨b, hb, hdb⟩ := hur hrnonneg
    have hbC : ‖b‖ ≤ C := by
      simpa only [norm_neg] using hdb.le_of_lipschitzOn (Ici_mem_nhds hrpos) hLu
    have hmab := (ExpandedFA.Monotone.monotone_hilbertGraph_iff H A).mp hm hza hb
    have habC : ‖a - b‖ ≤ 2 * (C : ℝ) := (norm_sub_le _ _).trans (by linarith)
    have hPz : ‖P r - z‖ ≤ h * (C : ℝ) := by
      simp only [P, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by linarith [hr.2])]
      exact (mul_le_mul_of_nonneg_left ha (by linarith [hr.2])).trans
        (mul_le_mul_of_nonneg_right (by linarith [hr.1]) C.coe_nonneg)
    have hCS : -inner ℝ (a - b) (P r - z) ≤ 2 * h * (C : ℝ) ^ 2 := by
      calc
        -inner ℝ (a - b) (P r - z) ≤ ‖a - b‖ * ‖P r - z‖ :=
          (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
        _ ≤ (2 * (C : ℝ)) * (h * C) := mul_le_mul habC hPz (norm_nonneg _) (by positivity)
        _ = 2 * h * (C : ℝ) ^ 2 := by ring
    have hsplit : P r - u r = (z - u r) + (P r - z) := by abel
    have hip : -inner ℝ (a - b) (P r - u r) ≤ 2 * h * (C : ℝ) ^ 2 := by
      rw [hsplit, inner_add_right]
      linarith
    change deriv (fun r => ‖(P - u) r‖ ^ 2) r ≤ 4 * h * (C : ℝ) ^ 2
    rw [((hP r).sub hdb).norm_sq.deriv]
    simp only [Pi.sub_apply]
    rw [show -a - -b = -(a - b) by abel, inner_neg_right, real_inner_comm]
    linarith
  have he := ac_image_sub_le (by linarith) hfAC hder
  simp only [P, sub_self, zero_smul, add_zero, add_sub_cancel_left] at he
  nlinarith

/-- Quantitative comparison at every mesh point, for any initial graph value. -/
theorem implicit_error_sq {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (u : ℝ → H) (x a₀ : H) (hxa : (x, a₀) ∈ A) (hu0 : u 0 = x)
    (hLu : LipschitzOnWith ‖a₀‖₊ u (Ici 0))
    (hu : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t)
    (h : ℝ) (hh : 0 < h) (ho : ShiftOnto H A h) :
    ∀ n : ℕ,
      ‖(MonotoneGraphResolvents.Spec.ResolventValue H A h ho)^[n] x - u ((n : ℝ) * h)‖ ^ 2 ≤
        4 * (n : ℝ) * h ^ 2 * ‖a₀‖ ^ 2 := by
  intro n
  induction n with
  | zero => simp [hu0]
  | succ n ih =>
    let w := (MonotoneGraphResolvents.Spec.ResolventValue H A h ho)^[n] x
    let z := MonotoneGraphResolvents.Spec.ResolventValue H A h ho w
    let a := MonotoneGraphResolvents.Spec.YosidaValue H A h ho w
    have hza : (z, a) ∈ A := yosida_graph H A h hh ho w
    have ha : ‖a‖ ≤ ‖a₀‖ := implicit_speed_bound A hm h hh ho x a₀ hxa n
    have he := implicit_step_energy A hm u ‖a₀‖₊ hLu hu z a hza ha
      ((n : ℝ) * h) h (by positivity) hh
    have hid : z + h • a = w := (resolvent_identity H A h hh ho w).symm
    rw [hid] at he
    change ‖z - u ((n : ℝ) * h + h)‖ ^ 2 ≤
      ‖w - u ((n : ℝ) * h)‖ ^ 2 + 4 * h ^ 2 * ‖a₀‖ ^ 2 at he
    rw [Function.iterate_succ_apply']
    push_cast
    have ht : ((n : ℝ) + 1) * h = (n : ℝ) * h + h := by ring
    rw [ht]
    change ‖z - u ((n : ℝ) * h + h)‖ ^ 2 ≤ _
    change ‖w - u ((n : ℝ) * h)‖ ^ 2 ≤ _ at ih
    nlinarith



/-- The exact constant in the manuscript's implicit-step estimate. -/
theorem implicit_error {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (u : ℝ → H) (x a₀ : H) (hxa : (x, a₀) ∈ A) (hu0 : u 0 = x)
    (hLu : LipschitzOnWith ‖a₀‖₊ u (Ici 0))
    (hu : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t)
    (h : ℝ) (hh : 0 < h) (ho : ShiftOnto H A h) (n : ℕ) :
    ‖(MonotoneGraphResolvents.Spec.ResolventValue H A h ho)^[n] x - u ((n : ℝ) * h)‖ ≤
      2 * ‖a₀‖ * Real.sqrt (((n : ℝ) * h) * h) := by
  have he := implicit_error_sq A hm u x a₀ hxa hu0 hLu hu h hh ho n
  have hs := Real.sq_sqrt (show 0 ≤ ((n : ℝ) * h) * h by positivity)
  have hrhs : (2 * ‖a₀‖ * Real.sqrt (((n : ℝ) * h) * h)) ^ 2 =
      4 * (n : ℝ) * h ^ 2 * ‖a₀‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  have hp : 0 ≤ 2 * ‖a₀‖ * Real.sqrt (((n : ℝ) * h) * h) := by positivity
  nlinarith [norm_nonneg ((MonotoneGraphResolvents.Spec.ResolventValue H A h ho)^[n] x -
    u ((n : ℝ) * h))]

/-- Every canonical implicit product is a contraction, including time zero. -/
theorem implicit_product_contraction {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (ho : ∀ h : ℝ, 0 < h → ShiftOnto H A h) (n : ℕ) (t : ℝ) (x y : H) :
    ‖Spec.implicitProduct A ho n t x - Spec.implicitProduct A ho n t y‖ ≤ ‖x - y‖ := by
  unfold Spec.implicitProduct
  split_ifs with ht
  · have hL := (resolvent_nonexpansive H A hm (t / n) ht (ho _ ht)).iterate n
    simpa only [one_pow, NNReal.coe_one, one_mul, dist_eq_norm] using hL.dist_le_mul x y
  · exact le_rfl

/-- A bound uniform for 0 ≤ t ≤ T, expressed with a vanishing 1/n factor. -/
theorem implicit_product_sq_bound {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (ho : ∀ h : ℝ, 0 < h → ShiftOnto H A h)
    (u : ℝ → H) (x a₀ : H) (hxa : (x, a₀) ∈ A) (hu0 : u 0 = x)
    (hLu : LipschitzOnWith ‖a₀‖₊ u (Ici 0))
    (hu : ∀ᵐ t ∂(volume.restrict (Ici (0 : ℝ))),
      ∃ a : H, (u t, a) ∈ A ∧ HasDerivAt u (-a) t)
    (n : ℕ) (hn : 0 < n) (T t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖Spec.implicitProduct A ho n t x - u t‖ ^ 2 ≤ 4 * T ^ 2 * ‖a₀‖ ^ 2 / n := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  by_cases ht0 : t = 0
  · subst t
    simp only [Spec.implicitProduct, zero_div, lt_self_iff_false, dite_false, hu0, sub_self,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  have hstep : 0 < t / (n : ℝ) := div_pos (lt_of_le_of_ne ht (Ne.symm ht0)) hnpos
  have he := implicit_error_sq A hm u x a₀ hxa hu0 hLu hu (t / n) hstep (ho _ hstep) n
  have hnt : (n : ℝ) * (t / (n : ℝ)) = t := mul_div_cancel₀ t hnpos.ne'
  rw [hnt] at he
  simp only [Spec.implicitProduct, dite_eq_left hstep]
  calc
    _ ≤ 4 * (n : ℝ) * (t / n) ^ 2 * ‖a₀‖ ^ 2 := he
    _ = 4 * t ^ 2 * ‖a₀‖ ^ 2 / n := by field_simp [hnpos.ne']
    _ ≤ 4 * T ^ 2 * ‖a₀‖ ^ 2 / n := by
      apply div_le_div_of_nonneg_right ?_ hnpos.le
      have hs : t ^ 2 ≤ T ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg ‖a₀‖)]

/-- The exponential formula follows first on D(A) from the mesh-point bound,
then on its closure from the two contraction estimates. -/
theorem exponential_formula {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : Set (H × H))
    (hm : ExpandedFA.Monotone.Monotone H (ExpandedFA.Monotone.hilbertGraph H A))
    (ho : ∀ h : ℝ, 0 < h → ShiftOnto H A h)
    (F : ℝ → H → ℝ → H) (S : ℝ → H → H) (hdata : Spec.SemigroupData A ho F S) :
    ∀ x ∈ closure (Spec.domain A), ∀ T : ℝ, 0 < T →
      TendstoUniformlyOn (fun n : ℕ => fun t => Spec.implicitProduct A ho n t x)
        (fun t => S t x) atTop (Icc 0 T) := by
  obtain ⟨_, h0, _, hc, _, _, _, hd⟩ := hdata
  have hdom (x : H) (hx : x ∈ Spec.domain A) (T : ℝ) (hT : 0 < T) :
      TendstoUniformlyOn (fun n : ℕ => fun t => Spec.implicitProduct A ho n t x)
        (fun t => S t x) atTop (Icc 0 T) := by
    obtain ⟨a₀, hxa⟩ := hx
    have hxcl : x ∈ closure (Spec.domain A) := subset_closure ⟨a₀, hxa⟩
    obtain ⟨hL, hu⟩ := hd x a₀ hxa
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (4 * T ^ 2 * ‖a₀‖ ^ 2)).eventually
      (gt_mem_nhds (sq_pos_of_pos hε))
    filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    intro t ht
    rw [dist_eq_norm, norm_sub_rev]
    have he := implicit_product_sq_bound A hm ho (fun t => S t x) x a₀ hxa
      (h0 x hxcl) hL hu n hnpos T t ht.1 ht.2
    nlinarith [norm_nonneg (Spec.implicitProduct A ho n t x - S t x)]
  intro x hx T hT
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 3) (by positivity)
  have hnear := Metric.tendstoUniformlyOn_iff.mp (hdom y hy T hT) (ε / 3) (by positivity)
  filter_upwards [hnear] with n hn
  intro t ht
  have h₁ := implicit_product_contraction A hm ho n t x y
  have h₂ := hc t ht.1 x hx y (subset_closure hy)
  have h₃ := hn t ht
  rw [dist_eq_norm] at hxy h₃ ⊢
  calc
    ‖S t x - Spec.implicitProduct A ho n t x‖ ≤
        ‖S t x - S t y‖ + ‖S t y - Spec.implicitProduct A ho n t y‖ +
          ‖Spec.implicitProduct A ho n t y - Spec.implicitProduct A ho n t x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _ |>.trans
        (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
    _ < ε := by
      rw [norm_sub_rev (Spec.implicitProduct A ho n t y) (Spec.implicitProduct A ho n t x)]
      linarith

/-- Full nonlinear monotone evolution theorem, with all original graph,
closure-domain, a.e., uniformity and quantitative conclusions. -/
theorem nonlinear_evolution : Spec.NonlinearEvolution.{u} := by
  intro H _ _ _ A hm ho
  obtain ⟨F, S, hdata⟩ := semigroup_existence H A hm ho
  have hdata' := hdata
  obtain ⟨_, h0, _, _, _, _, _, hd⟩ := hdata'
  refine ⟨F, S, hdata, ?_, exponential_formula A hm ho F S hdata, ?_⟩
  · rintro x ⟨a₀, hxa⟩ v hv t ht
    have hS : Spec.StrongSolution A x (fun t => S t x) :=
      ⟨h0 x (subset_closure ⟨a₀, hxa⟩), ⟨‖a₀‖₊, (hd x a₀ hxa).1⟩, (hd x a₀ hxa).2⟩
    exact strong_unique A hm x v (fun t => S t x) hv hS t ht
  · intro x a₀ hxa h hh n
    exact implicit_error A hm (fun t => S t x) x a₀ hxa
      (h0 x (subset_closure ⟨a₀, hxa⟩)) (hd x a₀ hxa).1 (hd x a₀ hxa).2 h hh (ho h hh) n

end ExpandedFA.Evolution.NonlinearMonotoneEvolution
