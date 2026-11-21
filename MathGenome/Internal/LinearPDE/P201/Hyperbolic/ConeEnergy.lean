import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.ConeEnergy
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.SmoothCone
import MathGenome.Internal.LinearPDE.P201.Hyperbolic.WaveEnergy
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Localized wave energy for the original whole-space energy solution class.
Steklov time averages, weak Sobolev products, and smooth shrinking-cone weights
prove the sharp local bound without moving-sphere traces. The endpoint and L¹
forcing limits give vanishing, domain of dependence, and essential finite speed.
The independent statements are in P201Specs.Hyperbolic.ConeEnergy. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology ENNReal
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
open P201Specs.Wave.Cone
namespace P201.Wave.Cone

section Restriction
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restricting an L² class never increases its norm. -/
theorem restrictedNorm_le (B : Set (Space n))
    (w : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    restrictedNorm B w ≤ ‖w‖ :=
  norm_Lp_toLp_restrict_le B w

/-- A uniform contraction bound, independent of the restricting set. -/
theorem restrictedNorm_sub_le (B : Set (Space n))
    (w z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    |restrictedNorm B w - restrictedNorm B z| ≤ ‖w - z‖ := by
  calc
    |restrictedNorm B w - restrictedNorm B z| ≤ ‖restrictL2 B w - restrictL2 B z‖ :=
      abs_norm_sub_norm_le _ _
    _ = restrictedNorm B (w - z) := by rw [restrictedNorm, map_sub]
    _ ≤ ‖w - z‖ := restrictedNorm_le B _

/-- For a fixed set, the restricted norm is continuous in the L² class. -/
theorem restrictedNorm_continuous (B : Set (Space n)) :
    Continuous (restrictedNorm (E := E) B) :=
  (restrictL2 B).continuous.norm

/-- Restricted norms therefore pass to every strong L² limit. -/
theorem restrictedNorm_tendsto {ι : Type} {l : Filter ι}
    (B : Set (Space n)) {w : ι → MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))}
    {z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))}
    (hw : Tendsto w l (𝓝 z)) :
    Tendsto (fun k => restrictedNorm B (w k)) l (𝓝 (restrictedNorm B z)) :=
  (restrictedNorm_continuous B).continuousAt.tendsto.comp hw

/-- The norm definition is the genuine local square integral. -/
theorem restrictedNorm_sq_integral [CompleteSpace E]
    (B : Set (Space n)) (w : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    restrictedNorm B w ^ 2 = ∫ x in B, ‖w x‖ ^ 2 := by
  rw [restrictedNorm, P201.Wave.lp2_norm_sq_integral (𝕜 := ℝ)]
  have he := LpToLpRestrictCLM_coeFn ℝ B w
  have hi : (∫ x, ‖restrictL2 B w x‖ ^ 2 ∂(domainMeasure (⊤ : Domain n)).restrict B) =
      ∫ x, ‖w x‖ ^ 2 ∂(domainMeasure (⊤ : Domain n)).restrict B := by
    apply integral_congr_ae
    exact he.mono fun x hx => congrArg (fun y : E => ‖y‖ ^ 2) hx
  simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using hi

/-- Vanishing of the restricted norm is precisely a.e. vanishing on the set. -/
theorem restrictedNorm_eq_zero_iff (B : Set (Space n))
    (w : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    restrictedNorm B w = 0 ↔ ∀ᵐ x ∂volume.restrict B, w x = 0 := by
  rw [restrictedNorm, norm_eq_zero, MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  have he := LpToLpRestrictCLM_coeFn ℝ B w
  have h : (restrictL2 B w : Space n → E) =ᵐ[(domainMeasure (⊤ : Domain n)).restrict B] 0 ↔
      (w : Space n → E) =ᵐ[(domainMeasure (⊤ : Domain n)).restrict B] 0 := by
    exact ⟨fun h => he.symm.trans h, fun h => he.trans h⟩
  simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
    Measure.restrict_univ, Filter.EventuallyEq, Pi.zero_apply] using h

end Restriction

section LocalEnergy
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- Identification with the local weak-gradient energy in the manuscript. -/
theorem localEnergy_eq_integral (c : ℝ) (a : Space n) (R : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) (s : ℝ) :
    localEnergy c a R u v s = (1 / 2 : ℝ) *
      ∫ x in coneBall c a R s, (‖v s x‖ ^ 2 + c ^ 2 * ‖hGradient (u s) x‖ ^ 2) := by
  have hv : IntegrableOn (fun x : Space n => ‖v s x‖ ^ 2) (coneBall c a R s) := by
    have h := (MeasureTheory.Lp.memLp (v s)).norm.integrable_sq
    simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    exact h.integrableOn
  have hu : IntegrableOn (fun x : Space n => ‖hGradient (u s) x‖ ^ 2) (coneBall c a R s) := by
    have h := (MeasureTheory.Lp.memLp (hGradient (u s))).norm.integrable_sq
    simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
    exact h.integrableOn
  rw [localEnergy, restrictedNorm_sq_integral, restrictedNorm_sq_integral,
    integral_add hv (hu.const_mul _), integral_const_mul]
  ring

theorem localEnergy_nonneg (c : ℝ) (a : Space n) (R : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) (s : ℝ) :
    0 ≤ localEnergy c a R u v s := by
  unfold localEnergy
  positivity

/-- A fixed-time energy limit requires only convergence of velocity and genuine
weak gradient in L². It imposes no trace or boundary regularity. -/
theorem localEnergy_tendsto {ι : Type} {l : Filter ι}
    (c : ℝ) (a : Space n) (R s : ℝ)
    (uₖ : ι → ℝ → WholeH1 n 𝕜) (vₖ : ι → ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hv : Tendsto (fun k => vₖ k s) l (𝓝 (v s)))
    (hu : Tendsto (fun k => hGradient (uₖ k s)) l (𝓝 (hGradient (u s)))) :
    Tendsto (fun k => localEnergy c a R (uₖ k) (vₖ k) s) l
      (𝓝 (localEnergy c a R u v s)) := by
  exact ((restrictedNorm_tendsto _ hv).pow 2 |>.add
    ((restrictedNorm_tendsto _ hu).pow 2 |>.const_mul (c ^ 2))).div_const 2

/-- Scalar passage to the limit in the sharp cone inequality. -/
theorem localEstimate_of_limits {ι : Type} {l : Filter ι} [NeBot l]
    {A A₀ F : ι → ℝ} {a a₀ f : ℝ}
    (hA : Tendsto A l (𝓝 a)) (hA₀ : Tendsto A₀ l (𝓝 a₀))
    (hF : Tendsto F l (𝓝 f))
    (h : ∀ᶠ k in l, Real.sqrt (2 * A k) ≤ Real.sqrt (2 * A₀ k) + F k) :
    Real.sqrt (2 * a) ≤ Real.sqrt (2 * a₀) + f := by
  exact le_of_tendsto_of_tendsto ((hA.const_mul 2).sqrt)
    (((hA₀.const_mul 2).sqrt).add hF) h

/-- Integrating a zero restricted velocity preserves the initial displacement
on the final ball. This also deals with time zero. -/
theorem displacement_vanishes_of_velocity
    {c R t : ℝ} {a : Space n} {g : WholeH1 n 𝕜} {h : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜} {v : ℝ → WholeL2 n 𝕜}
    (hc : 0 ≤ c) (ht : 0 ≤ t) (hs : IsEnergySolution c g h f u v)
    (hg : VanishesOn (coneBall c a R 0) (hUnderlying ⊤ 1 g))
    (hv : ∀ s ∈ Icc 0 t, VanishesOn (coneBall c a R s) (v s)) :
    VanishesOn (coneBall c a R t) (hUnderlying ⊤ 1 (u t)) := by
  let B := coneBall c a R t
  let L := restrictL2 (E := 𝕜) B
  have hvel (s : ℝ) (hs' : s ∈ Icc 0 t) : L (v s) = 0 := by
    apply norm_eq_zero.mp
    apply (restrictedNorm_eq_zero_iff B _).mpr
    exact ae_restrict_of_ae_restrict_of_subset
      (P201.SmoothCone.coneBall_antitone a R hc hs'.2) (hv s hs')
  have hd : ∀ s ∈ Icc 0 t,
      HasDerivWithinAt (fun r => L (hUnderlying ⊤ 1 (u r))) 0 (Icc 0 t) s := by
    intro s hs'
    have hds := ((L.hasFDerivAt).comp_hasDerivWithinAt s
      (hs.2.2.1 s hs'.1)).mono (show Icc 0 t ⊆ Ici (0 : ℝ) from fun _ hr => hr.1)
    simpa only [Function.comp_def, hvel s hs'] using! hds
  have he := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun s _ => le_refl ‖(0 : MeasureTheory.Lp 𝕜 2 ((domainMeasure ⊤).restrict B))‖)
    t (right_mem_Icc.mpr ht)
  have he' : L (hUnderlying ⊤ 1 (u t)) = L (hUnderlying ⊤ 1 (u 0)) := by
    simpa only [norm_zero, zero_mul, norm_le_zero_iff, sub_eq_zero] using he
  have hg' : L (hUnderlying ⊤ 1 (u 0)) = 0 := by
    rw [hs.2.2.2.1]
    apply norm_eq_zero.mp
    apply (restrictedNorm_eq_zero_iff B _).mpr
    exact ae_restrict_of_ae_restrict_of_subset
      (P201.SmoothCone.coneBall_antitone a R hc ht) hg
  apply (restrictedNorm_eq_zero_iff B _).mp
  exact norm_eq_zero.mpr (he'.trans hg')

end LocalEnergy

/-- Restricted L² norms are monotone with respect to the restricting set. -/
theorem restrictedNorm_mono_set {n : ℕ} {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B C : Set (Space n)} (hBC : B ⊆ C)
    (w : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    restrictedNorm B w ≤ restrictedNorm C w := by
  change ‖((MeasureTheory.Lp.memLp w).restrict B).toLp w‖ ≤
    ‖((MeasureTheory.Lp.memLp w).restrict C).toLp w‖
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  exact ENNReal.toReal_mono ((MeasureTheory.Lp.memLp w).restrict C).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono_set _ hBC))

/-- Measurability of the moving forcing norm follows from measurability in the
radius and continuity in the L² class. It does not use a sphere trace, or time
continuity of the forcing. -/
theorem localForcing_aestronglyMeasurable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {μ : Measure ℝ} (c : ℝ) (a : Space n) (R : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (localForcingNorm c a R f) μ := by
  borelize (WholeL2 n 𝕜)
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let H : WholeL2 n 𝕜 → ℝ → ℝ := fun w s => restrictedNorm (coneBall c a R s) w
  have hcont (s : ℝ) : Continuous (fun w => H w s) := restrictedNorm_continuous _
  have hmeas (w : WholeL2 n 𝕜) : Measurable (H w) := by
    have hmon : Monotone (fun r : ℝ => restrictedNorm (ball a r) w) :=
      fun r q hrq => restrictedNorm_mono_set (ball_subset_ball hrq) w
    exact hmon.measurable.comp (measurable_const.sub (measurable_const.mul measurable_id))
  have hH : Measurable (Function.uncurry H) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  exact (hH.comp_aemeasurable
    (hf.aemeasurable.prodMk measurable_id.aemeasurable)).aestronglyMeasurable

/-- The localized forcing is integrable on every interval on which the original
Bochner forcing is integrable, with no L²-in-time strengthening. -/
theorem localForcing_integrableOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ) (f : ℝ → WholeL2 n 𝕜)
    {J : Set ℝ} (hf : IntegrableOn f J) :
    IntegrableOn (localForcingNorm c a R f) J := by
  apply hf.norm.mono' (localForcing_aestronglyMeasurable c a R f hf.aestronglyMeasurable)
  apply Eventually.of_forall
  intro s
  change ‖‖restrictL2 (coneBall c a R s) (f s)‖‖ ≤ ‖f s‖
  rw [norm_norm]
  exact restrictedNorm_le _ _

/-- The assembled genuine weak gradient respects subtraction in the L² space. -/
theorem gradient_sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u z : WholeH1 n 𝕜) : hGradient (u - z) = hGradient u - hGradient z := by
  have hrep (w : WholeH1 n 𝕜) :
      (hGradient w : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[domainMeasure ⊤]
        (fun x => WithLp.toLp 2 (fun j => hFirstDerivative w j x)) :=
    (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (hFirstDerivative w j))).coeFn_toLp
  have hd (j : Fin n) : hFirstDerivative (u - z) j = hFirstDerivative u j - hFirstDerivative z j :=
    (Cauchy.Uniqueness.firstDerivativeCLM j).map_sub u z
  have hdrep (j : Fin n) : ∀ᵐ x ∂domainMeasure ⊤,
      hFirstDerivative (u - z) j x = hFirstDerivative u j x - hFirstDerivative z j x := by
    rw [hd j]
    exact MeasureTheory.Lp.coeFn_sub _ _
  apply MeasureTheory.Lp.ext
  filter_upwards [hrep (u - z), hrep u, hrep z,
    MeasureTheory.Lp.coeFn_sub (hGradient u) (hGradient z), ae_all_iff.mpr hdrep]
    with x hdiff hu hz hsub hd
  rw [hsub, hdiff, Pi.sub_apply, hu, hz]
  ext j
  exact hd j

@[simp] theorem gradient_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    hGradient (0 : WholeH1 n 𝕜) = 0 := by
  simpa only [sub_self] using gradient_sub (0 : WholeH1 n 𝕜) 0

/-- The gradient map is bounded by the full H¹ norm used in the shared spaces. -/
theorem gradient_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : WholeH1 n 𝕜) : ‖hGradient u‖ ≤ ‖u‖ := by
  have h := P201.Wave.h1_norm_sq_gradient u
  nlinarith [sq_nonneg ‖hUnderlying ⊤ 1 u‖, norm_nonneg u, norm_nonneg (hGradient u)]

theorem gradient_lipschitz {n : ℕ} {𝕜 : Type} [RCLike 𝕜] :
    LipschitzWith 1 (hGradient (n := n) (𝕜 := 𝕜) (Ω := ⊤)) := by
  apply LipschitzWith.of_dist_le_mul
  intro u z
  simpa only [dist_eq_norm, ← gradient_sub, NNReal.coe_one, one_mul] using
    gradient_norm_le (u - z)

/-- H¹ convergence suffices for the fixed-time weak-gradient limit. -/
theorem localEnergy_tendsto_of_H1 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ι : Type} {l : Filter ι} (c : ℝ) (a : Space n) (R s : ℝ)
    (uₖ : ι → ℝ → WholeH1 n 𝕜) (vₖ : ι → ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hu : Tendsto (fun k => uₖ k s) l (𝓝 (u s)))
    (hv : Tendsto (fun k => vₖ k s) l (𝓝 (v s))) :
    Tendsto (fun k => localEnergy c a R (uₖ k) (vₖ k) s) l
      (𝓝 (localEnergy c a R u v s)) := by
  exact localEnergy_tendsto c a R s uₖ vₖ u v hv
    (gradient_lipschitz.continuous.continuousAt.tendsto.comp hu)

/-- The moving restriction does not enlarge the L¹ forcing approximation
error. No time continuity or L²-in-time hypothesis is used. -/
theorem localForcing_integral_sub_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R t : ℝ) (ht : 0 ≤ t)
    (f z : ℝ → WholeL2 n 𝕜)
    (hf : IntegrableOn (localForcingNorm c a R f) (Icc 0 t))
    (hz : IntegrableOn (localForcingNorm c a R z) (Icc 0 t))
    (herror : IntegrableOn (fun s => ‖f s - z s‖) (Icc 0 t)) :
    |(∫ s in (0 : ℝ)..t, localForcingNorm c a R f s) -
      (∫ s in (0 : ℝ)..t, localForcingNorm c a R z s)| ≤
        ∫ s in (0 : ℝ)..t, ‖f s - z s‖ := by
  have hf' := (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr hf
  have hz' := (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr hz
  have herr' := (intervalIntegrable_iff_integrableOn_Icc_of_le ht).mpr herror
  rw [← intervalIntegral.integral_sub hf' hz', ← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ herr'
  exact Eventually.of_forall fun s _ => restrictedNorm_sub_le _ (f s) (z s)

/-- Restricted forcing integrals converge under Bochner L¹ approximation. -/
theorem localForcing_integral_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ι : Type} {l : Filter ι} (c : ℝ) (a : Space n) (R t : ℝ) (ht : 0 ≤ t)
    (fₖ : ι → ℝ → WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (hfk : ∀ k, IntegrableOn (localForcingNorm c a R (fₖ k)) (Icc 0 t))
    (hf : IntegrableOn (localForcingNorm c a R f) (Icc 0 t))
    (herr : ∀ k, IntegrableOn (fun s => ‖fₖ k s - f s‖) (Icc 0 t))
    (hlim : Tendsto (fun k => ∫ s in (0 : ℝ)..t, ‖fₖ k s - f s‖) l (𝓝 0)) :
    Tendsto (fun k => ∫ s in (0 : ℝ)..t, localForcingNorm c a R (fₖ k) s) l
      (𝓝 (∫ s in (0 : ℝ)..t, localForcingNorm c a R f s)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun k => norm_nonneg _) _ hlim
  intro k
  exact localForcing_integral_sub_le c a R t ht (fₖ k) f (hfk k) hf (herr k)

/-- Strong energy limits at the two endpoints and Bochner L¹ forcing limits
preserve the sharp cone estimate. Existence of these approximants is a separate
PDE obligation; this theorem does not postulate such an existence certificate. -/
theorem localEstimate_of_approximants {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ι : Type} {l : Filter ι} [NeBot l]
    (c : ℝ) (a : Space n) (R t : ℝ) (ht : 0 ≤ t)
    (uₖ : ι → ℝ → WholeH1 n 𝕜) (vₖ : ι → ℝ → WholeL2 n 𝕜)
    (fₖ : ι → ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v f : ℝ → WholeL2 n 𝕜)
    (hu₀ : Tendsto (fun k => uₖ k 0) l (𝓝 (u 0)))
    (hv₀ : Tendsto (fun k => vₖ k 0) l (𝓝 (v 0)))
    (hut : Tendsto (fun k => uₖ k t) l (𝓝 (u t)))
    (hvt : Tendsto (fun k => vₖ k t) l (𝓝 (v t)))
    (hfk : ∀ k, IntegrableOn (localForcingNorm c a R (fₖ k)) (Icc 0 t))
    (hf : IntegrableOn (localForcingNorm c a R f) (Icc 0 t))
    (herr : ∀ k, IntegrableOn (fun s => ‖fₖ k s - f s‖) (Icc 0 t))
    (hlim : Tendsto (fun k => ∫ s in (0 : ℝ)..t, ‖fₖ k s - f s‖) l (𝓝 0))
    (he : ∀ᶠ k in l, Real.sqrt (2 * localEnergy c a R (uₖ k) (vₖ k) t) ≤
      Real.sqrt (2 * localEnergy c a R (uₖ k) (vₖ k) 0) +
        ∫ s in (0 : ℝ)..t, localForcingNorm c a R (fₖ k) s) :
    Real.sqrt (2 * localEnergy c a R u v t) ≤
      Real.sqrt (2 * localEnergy c a R u v 0) +
        ∫ s in (0 : ℝ)..t, localForcingNorm c a R f s := by
  exact localEstimate_of_limits
    (localEnergy_tendsto_of_H1 c a R t uₖ vₖ u v hut hvt)
    (localEnergy_tendsto_of_H1 c a R 0 uₖ vₖ u v hu₀ hv₀)
    (localForcing_integral_tendsto c a R t ht fₖ f hfk hf herr hlim) he

/-- The localized forcing norm equals its square-integral formula. -/
theorem localForcingNorm_eq_sqrt_integral {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ) (f : ℝ → WholeL2 n 𝕜) (s : ℝ) :
    localForcingNorm c a R f s = Real.sqrt (∫ x in coneBall c a R s, ‖f s x‖ ^ 2) := by
  rw [← restrictedNorm_sq_integral, Real.sqrt_sq_eq_abs]
  exact (abs_of_nonneg (show 0 ≤ restrictedNorm (coneBall c a R s) (f s) from
    norm_nonneg _)).symm

/-- For a classical representative with the same genuine weak gradient, the
weak and classical local energies agree, independently of their representatives. -/
theorem localEnergy_eq_smooth {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (U V : ℝ → Space n → 𝕜) (s : ℝ)
    (hv : (v s : Space n → 𝕜) =ᵐ[volume.restrict (coneBall c a R s)] V s)
    (hg : (hGradient (u s) : Space n → EuclideanSpace 𝕜 (Fin n))
      =ᵐ[volume.restrict (coneBall c a R s)] P201Specs.SmoothCone.spatialGradient (U s)) :
    localEnergy c a R u v s = P201Specs.SmoothCone.localEnergy c a R U V s := by
  rw [localEnergy_eq_integral, P201Specs.SmoothCone.localEnergy]
  congr 1
  apply integral_congr_ae
  filter_upwards [hv, hg] with x hvx hgx
  rw [hvx, hgx]

/-- The source norm also agrees for a locally a.e. equal smooth representative. -/
theorem localForcingNorm_eq_smooth {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ)
    (f : ℝ → WholeL2 n 𝕜) (F : ℝ → Space n → 𝕜) (s : ℝ)
    (hf : (f s : Space n → 𝕜) =ᵐ[volume.restrict (coneBall c a R s)] F s) :
    localForcingNorm c a R f s = P201Specs.SmoothCone.localForcingNorm c a R F s := by
  rw [localForcingNorm_eq_sqrt_integral, P201Specs.SmoothCone.localForcingNorm]
  congr 1
  exact integral_congr_ae (hf.mono fun x hx => congrArg (fun z : 𝕜 => ‖z‖ ^ 2) hx)

/-- Transfer of the proved classical bound to actual energy-space curves when
their local representatives and weak gradients are identified. This is the
analytic input for the approximants, not an assumption on the final weak solution. -/
theorem localEstimate_of_smooth_representatives {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (hn : 1 ≤ n) {c R T : ℝ} {a : Space n}
    (hc : 0 < c) (hR : 0 < R) (hT : 0 ≤ T) (hTc : T < R / c)
    (u : ℝ → WholeH1 n 𝕜) (v f : ℝ → WholeL2 n 𝕜)
    (U V F : ℝ → Space n → 𝕜)
    (hs : P201Specs.SmoothCone.IsLocalSmoothWave c a R T U V F)
    (hv : ∀ s ∈ Icc 0 T,
      (v s : Space n → 𝕜) =ᵐ[volume.restrict (coneBall c a R s)] V s)
    (hg : ∀ s ∈ Icc 0 T,
      (hGradient (u s) : Space n → EuclideanSpace 𝕜 (Fin n))
        =ᵐ[volume.restrict (coneBall c a R s)] P201Specs.SmoothCone.spatialGradient (U s))
    (hf : ∀ s ∈ Icc 0 T,
      (f s : Space n → 𝕜) =ᵐ[volume.restrict (coneBall c a R s)] F s)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.sqrt (2 * localEnergy c a R u v t) ≤
      Real.sqrt (2 * localEnergy c a R u v 0) +
        ∫ s in (0 : ℝ)..t, localForcingNorm c a R f s := by
  have hzero : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  rw [localEnergy_eq_smooth c a R u v U V t (hv t ht) (hg t ht),
    localEnergy_eq_smooth c a R u v U V 0 (hv 0 hzero) (hg 0 hzero)]
  have hI : (∫ s in (0 : ℝ)..t, localForcingNorm c a R f s) =
      ∫ s in (0 : ℝ)..t, P201Specs.SmoothCone.localForcingNorm c a R F s := by
    apply intervalIntegral.integral_congr
    intro s hs'
    have hsT : s ∈ Icc 0 T := (Icc_subset_Icc le_rfl ht.2) ((uIcc_of_le ht.1) ▸ hs')
    exact localForcingNorm_eq_smooth c a R f F s (hf s hsT)
  rw [hI]
  exact P201.SmoothCone.localEnergyEstimate 𝕜 hn c a R T U V F hc hR hT hTc hs t ht

/-- Locality of the genuine weak gradient on an open set. Restricting the
Sobolev graph to that set identifies the whole restricted function with zero;
injectivity of the underlying-coordinate map then kills every derivative. -/
theorem gradient_vanishes_on_open {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {B : Set (Space n)} (hB : IsOpen B) (g : WholeH1 n 𝕜)
    (hg : VanishesOn B (hUnderlying ⊤ 1 g)) :
    ∀ᵐ x ∂volume.restrict B, hGradient g x = 0 := by
  let Ω : Domain n := ⟨B, hB⟩
  let w := P102.U4.sobolevRestrict Ω (P201Specs.hToW 𝕜 ⊤ 1 g)
  have hw : w = 0 := by
    apply P102.U4.sobolevUnderlying_injective Ω 1 2
    change P102.U4.domainLpRestrict Ω (hUnderlying ⊤ 1 g) = 0
    apply (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).mpr
    exact (P102.U4.domainLpRestrict_ae Ω (hUnderlying ⊤ 1 g)).trans hg
  have hd (j : Fin n) : ∀ᵐ x ∂volume.restrict B, hFirstDerivative g j x = 0 := by
    have he : P102.U4.domainLpRestrict Ω (hFirstDerivative g j) = 0 := by
      have he := congrArg (fun z => P102.U4.sobolevDerivative z
        (⟨{j}, by simp⟩ : P102.U4.SobolevIndex n 1)) hw
      exact he
    have he' := (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).mp he
    exact (P102.U4.domainLpRestrict_ae Ω (hFirstDerivative g j)).symm.trans he'
  have hrep : (hGradient g : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[volume]
      (fun x => WithLp.toLp 2 (fun j => hFirstDerivative g j x)) := by
    have he : (hGradient g : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[domainMeasure ⊤]
        (fun x => WithLp.toLp 2 (fun j => hFirstDerivative g j x)) :=
      (MemLp.of_eval_piLp
        (fun j => MeasureTheory.Lp.memLp (hFirstDerivative g j))).coeFn_toLp
    simpa only [P201.domainMeasure, P201Specs.domainMeasure,
      TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using he
  filter_upwards [ae_restrict_of_ae hrep, (ae_all_iff.mpr hd)] with x hx hd
  rw [hx]
  ext j
  exact hd j

/-- Zero local energy forces the velocity to vanish a.e. in that slice. -/
theorem velocity_vanishes_of_localEnergy_zero {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) (s : ℝ)
    (he : localEnergy c a R u v s = 0) :
    VanishesOn (coneBall c a R s) (v s) := by
  apply (restrictedNorm_eq_zero_iff _ _).mp
  have hpos : 0 ≤ c ^ 2 * restrictedNorm (coneBall c a R s) (hGradient (u s)) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hv : 0 ≤ restrictedNorm (coneBall c a R s) (v s) := norm_nonneg _
  unfold localEnergy at he
  nlinarith [sq_nonneg (restrictedNorm (coneBall c a R s) (v s))]

/-- The displacement data eliminate the additive constant left by zero energy.
This proves the vanishing conclusion once the sharp weak cone bound is known. -/
theorem vanishing_of_localEnergyEstimate
    (hestimate : P201Specs.Wave.Cone.localEnergyEstimateStatement) :
    P201Specs.Wave.Cone.vanishingStatement := by
  intro n 𝕜 _ hn c g h f u v hc hf hsol a R hR hg hh hsrc t ht htc
  have hgrad := gradient_vanishes_on_open isOpen_ball g hg
  have hgn := (restrictedNorm_eq_zero_iff (coneBall c a R 0) (hGradient g)).mpr hgrad
  have hhn := (restrictedNorm_eq_zero_iff (coneBall c a R 0) h).mpr hh
  have hE0 : localEnergy c a R u v 0 = 0 := by
    unfold localEnergy
    rw [hsol.2.2.2.1, hsol.2.2.2.2.1, hgn, hhn]
    simp
  apply displacement_vanishes_of_velocity hc.le ht hsol hg
  intro s hs
  have hsc : s < R / c := hs.2.trans_lt htc
  obtain ⟨_, he⟩ := hestimate 𝕜 hn c g h f u v hc hf hsol a R s hR hs.1 hsc
  have hsrc' : ∀ᵐ r ∂volume.restrict (Icc 0 s), localForcingNorm c a R f r = 0 := by
    have hsub : Icc 0 s ⊆ Ico 0 (R / c) := fun r hr => ⟨hr.1, hr.2.trans_lt hsc⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsrc] with r hr
    exact (restrictedNorm_eq_zero_iff _ _).mpr hr
  have hI : (∫ r in (0 : ℝ)..s, localForcingNorm c a R f r) = 0 := by
    rw [intervalIntegral.integral_of_le hs.1]
    exact integral_eq_zero_of_ae
      (ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hsrc')
  rw [hE0, hI] at he
  have hE : localEnergy c a R u v s = 0 := by
    have hp := localEnergy_nonneg c a R u v s
    have hsq := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp)
    have hz : Real.sqrt (2 * localEnergy c a R u v s) = 0 :=
      le_antisymm (by simpa using he) (Real.sqrt_nonneg _)
    rw [hz] at hsq
    linarith
  exact velocity_vanishes_of_localEnergy_zero c a R u v s hE

/-- The distributional equation is linear in the entire energy solution class,
including merely locally Bochner-integrable sources. -/
theorem energySolution_sub {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g₁ g₂ : WholeH1 n 𝕜} {h₁ h₂ : WholeL2 n 𝕜}
    {f₁ f₂ : ℝ → WholeL2 n 𝕜} {u₁ u₂ : ℝ → WholeH1 n 𝕜}
    {v₁ v₂ : ℝ → WholeL2 n 𝕜}
    (hf₁ : LocallyIntegrableForcing f₁) (hf₂ : LocallyIntegrableForcing f₂)
    (hs₁ : IsEnergySolution c g₁ h₁ f₁ u₁ v₁)
    (hs₂ : IsEnergySolution c g₂ h₂ f₂ u₂ v₂) :
    IsEnergySolution c (g₁ - g₂) (h₁ - h₂) (f₁ - f₂) (u₁ - u₂) (v₁ - v₂) := by
  refine ⟨hs₁.1.sub hs₂.1, hs₁.2.1.sub hs₂.2.1, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simpa only [Pi.sub_apply, map_sub] using!
      (hs₁.2.2.1 s hs).sub (hs₂.2.2.1 s hs)
  · simp only [Pi.sub_apply, hs₁.2.2.2.1, hs₂.2.2.2.1]
  · simp only [Pi.sub_apply, hs₁.2.2.2.2.1, hs₂.2.2.2.2.1]
  · intro φ
    have hpair (w z q : WholeL2 n 𝕜) :
        Cauchy.TestSlices.scalarPair (w - z) q =
          Cauchy.TestSlices.scalarPair w q - Cauchy.TestSlices.scalarPair z q := by
      simp_rw [← Cauchy.TestSlices.scalarPairCLM_apply]
      simp only [map_sub, sub_apply]
    have hleft (t : ℝ) : (∫ x : Space n,
        hUnderlying ⊤ 1 ((u₁ - u₂) t) x * testWaveOperator c φ t x) =
        (∫ x : Space n, hUnderlying ⊤ 1 (u₁ t) x * testWaveOperator c φ t x) -
          ∫ x : Space n, hUnderlying ⊤ 1 (u₂ t) x * testWaveOperator c φ t x := by
      rw [← Cauchy.scalarPair_waveSlice, Pi.sub_apply, map_sub, hpair,
        Cauchy.scalarPair_waveSlice, Cauchy.scalarPair_waveSlice]
    have hright (t : ℝ) : (∫ x : Space n, (f₁ - f₂) t x * φ (t,x)) =
        (∫ x : Space n, f₁ t x * φ (t,x)) - ∫ x : Space n, f₂ t x * φ (t,x) := by
      rw [← Cauchy.scalarPair_spacetimeSlice, Pi.sub_apply, hpair,
        Cauchy.scalarPair_spacetimeSlice,
        Cauchy.scalarPair_spacetimeSlice]
    change (∫ t in Ioi (0 : ℝ), ∫ x : Space n,
        hUnderlying ⊤ 1 ((u₁ - u₂) t) x * testWaveOperator c φ t x) =
      ∫ t in Ioi (0 : ℝ), ∫ x : Space n, (f₁ - f₂) t x * φ (t,x)
    simp_rw [hleft, hright]
    rw [integral_sub (Cauchy.TestSlices.integrableOn_solution_test_pairing u₁ hs₁.1 c φ)
        (Cauchy.TestSlices.integrableOn_solution_test_pairing u₂ hs₂.1 c φ),
      integral_sub (Cauchy.TestSlices.integrableOn_forcing_test_pairing f₁ hf₁ φ)
        (Cauchy.TestSlices.integrableOn_forcing_test_pairing f₂ hf₂ φ),
      hs₁.2.2.2.2.2 φ, hs₂.2.2.2.2.2 φ]

/-- The full H¹ norm is controlled by its two actual L² components. -/
theorem h1_norm_le_components {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (w : WholeH1 n 𝕜) : ‖w‖ ≤ ‖hUnderlying ⊤ 1 w‖ + ‖hGradient w‖ := by
  have he := P201.Wave.h1_norm_sq_gradient w
  nlinarith [norm_nonneg w, norm_nonneg (hUnderlying ⊤ 1 w),
    norm_nonneg (hGradient w),
    mul_nonneg (norm_nonneg (hUnderlying ⊤ 1 w)) (norm_nonneg (hGradient w))]

/-- Uniform control of an arbitrary energy solution at exactly Bochner L¹
forcing regularity. This uses the proved global balance, not a local estimate. -/
theorem energySolution_norm_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T)
    {g : WholeH1 n 𝕜} {h : WholeL2 n 𝕜} {f : ℝ → WholeL2 n 𝕜}
    {u : ℝ → WholeH1 n 𝕜} {v : ℝ → WholeL2 n 𝕜}
    (hf : LocallyIntegrableForcing f) (hs : IsEnergySolution c g h f u v)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ‖u t‖ + ‖v t‖ ≤ ‖g‖ + (T + c⁻¹ + 1) *
      (P201Specs.Wave.Energy.magnitude c g h + ∫ s in (0 : ℝ)..T, ‖f s‖) := by
  let G := fun s => P201Specs.Wave.Energy.magnitude c (u s) (v s)
  let M := P201Specs.Wave.Energy.magnitude c g h + ∫ s in (0 : ℝ)..T, ‖f s‖
  have he := Energy.estimatesOfBalance c g h f u v hf hs (Energy.balance c g h f u v hf hs)
  have hfI : IntervalIntegrable (fun s => ‖f s‖) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hf T hT).norm
  have hG (s : ℝ) (hs' : s ∈ Icc 0 T) : G s ≤ M := by
    have he' := (he 0 s le_rfl hs'.1).2.2.1
    rw [hs.2.2.2.1, hs.2.2.2.2.1] at he'
    have hi := intervalIntegral.integral_mono_interval le_rfl hs'.1 hs'.2
      (ae_of_all _ fun _ => norm_nonneg _) hfI
    dsimp only [G, M]
    linarith
  have hM : 0 ≤ M := add_nonneg (Energy.magnitude_nonneg c g h)
    (intervalIntegral.integral_nonneg hT (fun _ _ => norm_nonneg _))
  have hgrad : ‖hGradient (u t)‖ ≤ c⁻¹ * M := by
    have hp : c * ‖hGradient (u t)‖ ≤ G t := by
      apply (sq_le_sq₀ (mul_nonneg hc.le (norm_nonneg _))
        (Energy.magnitude_nonneg c (u t) (v t))).mp
      rw [Energy.magnitude_sq]
      dsimp [Energy.gradientSize, P201Specs.Wave.Energy.gradientSize]
      nlinarith [sq_nonneg ‖v t‖]
    have hh : ‖hGradient (u t)‖ ≤ M / c :=
      (le_div_iff₀ hc).mpr (by nlinarith [hG t ht])
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have hvel : ‖v t‖ ≤ M :=
    (Energy.norm_velocity_le_magnitude c (u t) (v t)).trans (hG t ht)
  have hGI : IntervalIntegrable G volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (he 0 t le_rfl ht.1).2.1
  have hInt : (∫ s in (0 : ℝ)..t, G s) ≤ T * M := by
    have hh := intervalIntegral.integral_mono_on ht.1 hGI
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 t)
      (fun s hs' => hG s ⟨hs'.1, hs'.2.trans ht.2⟩)
    have hh' : (∫ s in (0 : ℝ)..t, G s) ≤ t * M := by simpa using hh
    exact hh'.trans (mul_le_mul_of_nonneg_right ht.2 hM)
  have hdisp := (he 0 t le_rfl ht.1).2.2.2
  rw [hs.2.2.2.1] at hdisp
  have hg : ‖hUnderlying ⊤ 1 g‖ ≤ ‖g‖ := by
    have hsq := P201.Wave.h1_norm_sq_gradient g
    nlinarith [sq_nonneg ‖hGradient g‖, norm_nonneg g, norm_nonneg (hUnderlying ⊤ 1 g)]
  have hu := h1_norm_le_components (u t)
  change ‖u t‖ + ‖v t‖ ≤ ‖g‖ + (T + c⁻¹ + 1) * M
  linarith

/-- Convergence of data in full H¹ × L² and of the forcing in Bochner L¹
gives uniform convergence of *any* corresponding energy solutions. In particular
this applies to smooth approximants once their construction is established. -/
theorem energySolutions_tendstoUniformlyOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ι : Type} {l : Filter ι} {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T)
    (gₖ : ι → WholeH1 n 𝕜) (hₖ : ι → WholeL2 n 𝕜)
    (fₖ : ι → ℝ → WholeL2 n 𝕜)
    (uₖ : ι → ℝ → WholeH1 n 𝕜) (vₖ : ι → ℝ → WholeL2 n 𝕜)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hfₖ : ∀ k, LocallyIntegrableForcing (fₖ k)) (hf : LocallyIntegrableForcing f)
    (hsₖ : ∀ k, IsEnergySolution c (gₖ k) (hₖ k) (fₖ k) (uₖ k) (vₖ k))
    (hs : IsEnergySolution c g h f u v)
    (hg : Tendsto gₖ l (𝓝 g)) (hh : Tendsto hₖ l (𝓝 h))
    (herror : Tendsto (fun k => ∫ s in (0 : ℝ)..T, ‖fₖ k s - f s‖) l (𝓝 0)) :
    TendstoUniformlyOn uₖ u l (Icc 0 T) ∧ TendstoUniformlyOn vₖ v l (Icc 0 T) := by
  let B := fun k => ‖gₖ k - g‖ + (T + c⁻¹ + 1) *
    (P201Specs.Wave.Energy.magnitude c (gₖ k - g) (hₖ k - h) +
      ∫ s in (0 : ℝ)..T, ‖fₖ k s - f s‖)
  have hgn : Tendsto (fun k => gₖ k - g) l (𝓝 0) := by
    simpa only [sub_self] using hg.sub (tendsto_const_nhds (x := g))
  have hhn : Tendsto (fun k => hₖ k - h) l (𝓝 0) := by
    simpa only [sub_self] using hh.sub (tendsto_const_nhds (x := h))
  have hmag : Tendsto
      (fun k => P201Specs.Wave.Energy.magnitude c (gₖ k - g) (hₖ k - h)) l (𝓝 0) := by
    have hm := (Energy.continuous_magnitude c).continuousAt.tendsto.comp
      (hgn.prodMk_nhds hhn)
    simpa [Function.comp_def, Energy.magnitude, P201Specs.Wave.Energy.magnitude,
      P201Specs.Wave.Energy.gradientSize] using! hm
  have hB : Tendsto B l (𝓝 0) := by
    simpa only [norm_zero, add_zero, mul_zero] using hgn.norm.add
      ((hmag.add herror).const_mul (T + c⁻¹ + 1))
  have hbound (k : ι) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖uₖ k t - u t‖ + ‖vₖ k t - v t‖ ≤ B k := by
    exact energySolution_norm_le hc hT (fun S hS => (hfₖ k S hS).sub (hf S hS))
      (energySolution_sub (hfₖ k) hf (hsₖ k) hs) ht
  constructor
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hB).2 ε hε] with k hk t ht
    rw [dist_eq_norm, norm_sub_rev]
    exact (le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hbound k t ht)).trans_lt hk
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hB).2 ε hε] with k hk t ht
    rw [dist_eq_norm, norm_sub_rev]
    exact (le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hbound k t ht)).trans_lt hk

/-- Equality of L² classes on a region is equivalent to a.e. vanishing of the
difference, with the representative issue handled explicitly. -/
theorem equalOn_iff_sub_vanishes {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (B : Set (Space n)) (w z : WholeL2 n 𝕜) :
    EqualOn B w z ↔ VanishesOn B (w - z) := by
  have hsub := MeasureTheory.Lp.coeFn_sub w z
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
    Measure.restrict_univ] at hsub
  have hs : ∀ᵐ x ∂volume.restrict B, (w - z) x = w x - z x :=
    ae_restrict_of_ae hsub
  constructor
  · intro h
    filter_upwards [h, hs] with x hx hxs
    simp only [hxs, hx, sub_self]
  · intro h
    filter_upwards [h, hs] with x hx hxs
    exact sub_eq_zero.mp (hxs.symm.trans hx)

/-- The full domain-of-dependence conclusion is the zero-data cone statement
applied to differences, without equality hypotheses outside the cone. -/
theorem domainOfDependence_of_vanishing
    (hvan : P201Specs.Wave.Cone.vanishingStatement) :
    P201Specs.Wave.Cone.domainOfDependenceStatement := by
  intro n 𝕜 _ hn c g₁ g₂ h₁ h₂ f₁ f₂ u₁ u₂ v₁ v₂ hc hf₁ hf₂ hs₁ hs₂ a R hR hg hh hf
  have hfd : LocallyIntegrableForcing (f₁ - f₂) := fun T hT => (hf₁ T hT).sub (hf₂ T hT)
  have hgd : VanishesOn (coneBall c a R 0) (hUnderlying ⊤ 1 (g₁ - g₂)) := by
    rw [map_sub]
    exact (equalOn_iff_sub_vanishes _ _ _).mp hg
  have hhd := (equalOn_iff_sub_vanishes _ _ _).mp hh
  have hfs : ∀ᵐ s ∂volume.restrict (Ico 0 (R / c)),
      VanishesOn (coneBall c a R s) ((f₁ - f₂) s) := by
    filter_upwards [hf] with s hs
    exact (equalOn_iff_sub_vanishes _ _ _).mp hs
  intro t ht htc
  have hzero := hvan 𝕜 hn c (g₁ - g₂) (h₁ - h₂) (f₁ - f₂) (u₁ - u₂) (v₁ - v₂)
    hc hfd (energySolution_sub hf₁ hf₂ hs₁ hs₂) a R hR hgd hhd hfs t ht htc
  apply (equalOn_iff_sub_vanishes _ _ _).mpr
  simpa only [Pi.sub_apply, map_sub] using hzero

/-- Local a.e. vanishing on open neighborhoods implies a.e. vanishing on the
entire set. A countable subcover keeps the union of exceptional sets null. -/
theorem ae_zero_of_local {n : ℕ} {E : Type} [Zero E]
    (B : Set (Space n)) (w : Space n → E)
    (h : ∀ x ∈ B, ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧
      ∀ᵐ y ∂volume.restrict U, w y = 0) :
    ∀ᵐ y ∂volume.restrict B, w y = 0 := by
  classical
  choose U hU using (fun x : B => h x x.property)
  have hc : B ⊆ ⋃ x : B, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, (hU ⟨x,hx⟩).2.1⟩
  obtain ⟨I, hI, hcI⟩ :=
    (HereditarilyLindelofSpace.isLindelof B).elim_countable_subcover U
      (fun x => (hU x).1) hc
  apply ae_restrict_of_ae_restrict_of_subset hcI
  exact (ae_restrict_biUnion_iff U hI _).mpr fun x _ => (hU x).2.2

/-- The essential-support conclusion follows from the full cone-vanishing
statement, retaining a single null set on the entire exterior. -/
theorem finiteSpeed_of_vanishing (hvan : P201Specs.Wave.Cone.vanishingStatement) :
    P201Specs.Wave.Cone.finiteSpeedStatement := by
  intro n 𝕜 _ hn c g h u v hc hsol a R₀ hR₀ hg hh t ht
  change ∀ᵐ x ∂volume.restrict (closedBall a (R₀ + c * t))ᶜ,
    hUnderlying ⊤ 1 (u t) x = 0
  apply ae_zero_of_local
  intro x hx
  have hdist : R₀ + c * t < dist x a := by
    simpa only [mem_compl_iff, mem_closedBall, not_le] using hx
  let δ : ℝ := (dist x a - R₀ - c * t) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let R : ℝ := c * t + δ
  have hR : 0 < R := add_pos_of_nonneg_of_pos (mul_nonneg hc.le ht) hδ
  have hRt : t < R / c := (lt_div_iff₀ hc).mpr (by dsimp [R]; linarith)
  have hdisjoint : coneBall c x R 0 ⊆ (closedBall a R₀)ᶜ := by
    intro y hy
    have hy' : dist y x < R := by simpa only [coneBall, P201Specs.SmoothCone.coneBall,
      mul_zero, sub_zero, mem_ball] using hy
    have htriangle := dist_triangle x y a
    rw [dist_comm x y] at htriangle
    have hRdist : R < dist x a - R₀ := by dsimp [R,δ]; linarith
    simp only [mem_compl_iff, mem_closedBall, not_le]
    linarith
  have hg' : VanishesOn (coneBall c x R 0) (hUnderlying ⊤ 1 g) :=
    ae_restrict_of_ae_restrict_of_subset hdisjoint hg
  have hh' : VanishesOn (coneBall c x R 0) h :=
    ae_restrict_of_ae_restrict_of_subset hdisjoint hh
  have hf : LocallyIntegrableForcing (0 : ℝ → WholeL2 n 𝕜) :=
    fun T _ => integrableOn_zero
  have hfzero : ∀ᵐ s ∂volume.restrict (Ico 0 (R / c)),
      VanishesOn (coneBall c x R s) ((0 : ℝ → WholeL2 n 𝕜) s) := by
    apply Eventually.of_forall
    intro s
    have hz := MeasureTheory.Lp.coeFn_zero 𝕜 2 (domainMeasure (⊤ : Domain n))
    simp only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] at hz
    exact ae_restrict_of_ae hz
  refine ⟨coneBall c x R t, isOpen_ball, ?_, ?_⟩
  · change dist x x < R - c * t
    simp only [dist_self]
    dsimp [R]
    linarith
  · exact hvan 𝕜 hn c g h 0 u v hc hf hsol x R hR hg' hh' hfzero t ht hRt

/-- The classical cone calculation is local and requires no global energy hypothesis. -/
theorem localSmoothApplicability :
    P201Specs.Wave.Cone.localSmoothApplicabilityStatement :=
  ⟨P201.SmoothCone.localEnergyEstimate, P201.SmoothCone.vanishing,
    P201.SmoothCone.localUniqueness⟩

section TimeRegularization
open ExpandedFA.Evolution.SymmetricHyperbolicEquation

/-- Canonical H¹ representative of the time-averaged velocity. -/
def velocityAverageH1 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : ℝ → WholeH1 n 𝕜) (h s : ℝ) : WholeH1 n 𝕜 :=
  h⁻¹ • (u (s+h) - u s)

theorem velocityAverageH1_underlying {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜}
    {v : ℝ → WholeL2 n 𝕜} (hz : IsEnergySolution c g k f u v)
    {h s : ℝ} (hh : 0 ≤ h) (hs : 0 ≤ s) :
    hUnderlying ⊤ 1 (velocityAverageH1 u h s) = timeAverage v h s := by
  simp only [velocityAverageH1, ContinuousLinearMap.map_smul_of_tower, map_sub, timeAverage]
  rw [Energy.displacement_increment c g k f u v hz s (s+h) hs (by linarith)]

theorem velocityAverageH1_continuousOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : ℝ → WholeH1 n 𝕜} (hu : ContinuousOn u (Ici 0))
    {h : ℝ} (hh : 0 ≤ h) :
    ContinuousOn (velocityAverageH1 u h) (Ici 0) := by
  unfold velocityAverageH1
  exact ((hu.comp (continuousOn_id.add continuousOn_const)
    (fun s hs => show 0 ≤ s+h from add_nonneg hs hh)).sub hu).const_smul h⁻¹

/-- Both time averages converge in the original energy topology. -/
theorem timeAverage_state_tendstoUniformlyOn {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜}
    {v : ℝ → WholeL2 n 𝕜} (hz : IsEnergySolution c g k f u v)
    (B T : ℝ) (hBT : B < T) :
    TendstoUniformlyOn (fun h => timeAverage u h) u (𝓝[>] (0 : ℝ)) (Icc 0 B) ∧
    TendstoUniformlyOn (fun h => timeAverage v h) v (𝓝[>] (0 : ℝ)) (Icc 0 B) := by
  exact ⟨timeAverage_tendstoUniformlyOn hBT (hz.1.mono (fun _ ht => ht.1)),
    timeAverage_tendstoUniformlyOn hBT (hz.2.1.mono (fun _ ht => ht.1))⟩

/-- Steklov averages give genuine strong graphs suitable for weighted
energy differentiation, while the original velocity need not lie in H¹. -/
theorem timeAverage_state_graphs {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜}
    {v : ℝ → WholeL2 n 𝕜} (hz : IsEnergySolution c g k f u v)
    (T B h : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B) (hh : 0 ≤ h)
    (hBh : B+h ≤ T) :
    AbsolutelyContinuousOnInterval (timeAverage u h) 0 B ∧
    AbsolutelyContinuousOnInterval (timeAverage v h) 0 B ∧
    (∀ᵐ s ∂volume, s ∈ Icc 0 B →
      HasDerivAt (timeAverage u h) (velocityAverageH1 u h s) s) ∧
    (∀ᵐ s ∂volume, s ∈ Icc 0 B →
      HasDerivAt (timeAverage v h) (h⁻¹ • (v (s+h)-v s)) s) ∧
    ∀ s ∈ Icc 0 B,
      hUnderlying ⊤ 1 (velocityAverageH1 u h s) = timeAverage v h s := by
  have hu := timeAverage_regular hT hB hh hBh
    (hz.1.mono (show Icc 0 T ⊆ Ici (0 : ℝ) from fun _ ht => ht.1))
  have hv := timeAverage_regular hT hB hh hBh
    (hz.2.1.mono (show Icc 0 T ⊆ Ici (0 : ℝ) from fun _ ht => ht.1))
  exact ⟨hu.1, hv.1, hu.2, hv.2,
    fun s hs => velocityAverageH1_underlying hz hh hs.1⟩

/-- Endpoint local weak energies converge under time averaging. -/
theorem localEnergy_timeAverage_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜}
    {v : ℝ → WholeL2 n 𝕜} (hz : IsEnergySolution c g k f u v)
    (a : Space n) (R B T s : ℝ) (hBT : B < T) (hs : s ∈ Icc 0 B) :
    Tendsto (fun h => P201Specs.Wave.Cone.localEnergy c a R
      (timeAverage u h) (timeAverage v h) s)
      (𝓝[>] (0 : ℝ)) (𝓝 (P201Specs.Wave.Cone.localEnergy c a R u v s)) := by
  have hc := timeAverage_state_tendstoUniformlyOn hz B T hBT
  exact localEnergy_tendsto_of_H1 c a R s (fun h => timeAverage u h)
    (fun h => timeAverage v h) u v (hc.1.tendsto_at hs) (hc.2.tendsto_at hs)

/-- Cutting off outside a longer time interval preserves the original forcing
on every shorter forward interval, up to the null initial endpoint. -/
theorem forcing_zeroExtension_ae_on {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → WholeL2 n 𝕜) {B T : ℝ} (hBT : B < T) :
    (Ioo 0 T).indicator f =ᵐ[volume.restrict (Icc 0 B)] f := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (show ∀ᵐ s : ℝ ∂volume, s ≠ 0 from by simp [ae_iff, measure_singleton])] with s hs hs0
  exact indicator_of_mem (show s ∈ Ioo (0 : ℝ) T from
    ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2.trans_lt hBT⟩) f

/-- Forward time averaging approximates the original source in precisely
Bochner L¹(L²), including at the initial end of the time interval. -/
theorem timeAverage_forcing_error_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B < T)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) :
    Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..B,
      ‖timeAverage ((Ioo 0 T).indicator f) ε s - f s‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hF : Integrable ((Ioo 0 T).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hf.mono_set Ioo_subset_Icc_self)
  have hlim := timeAverage_L1_tendsto _ hF B hB
  have he (ε : ℝ) :
      (∫ s in (0 : ℝ)..B,
        ‖timeAverage ((Ioo 0 T).indicator f) ε s - (Ioo 0 T).indicator f s‖) =
      ∫ s in (0 : ℝ)..B, ‖timeAverage ((Ioo 0 T).indicator f) ε s - f s‖ := by
    rw [intervalIntegral.integral_of_le hB, intervalIntegral.integral_of_le hB]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (forcing_zeroExtension_ae_on f hBT)] with s hs
    rw [hs]
  simp_rw [he] at hlim
  exact hlim

/-- The sharp moving-ball forcing integral survives forward time averaging;
no time continuity or square integrability of the original source is needed. -/
theorem localForcing_timeAverage_integral_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R : ℝ) {B T : ℝ} (hB : 0 ≤ B) (hBT : B < T)
    (f : ℝ → WholeL2 n 𝕜) (hf : IntegrableOn f (Icc 0 T)) :
    Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..B,
      localForcingNorm c a R (timeAverage ((Ioo 0 T).indicator f) ε) s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s in (0 : ℝ)..B, localForcingNorm c a R f s)) := by
  have hF : Integrable ((Ioo 0 T).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hf.mono_set Ioo_subset_Icc_self)
  have hfB : IntegrableOn f (Icc 0 B) :=
    hf.mono_set (Icc_subset_Icc le_rfl hBT.le)
  have hcont (ε : ℝ) : Continuous (timeAverage ((Ioo 0 T).indicator f) ε) :=
    timeAverage_continuous _ hF ε
  exact localForcing_integral_tendsto c a R B hB
    (fun ε => timeAverage ((Ioo 0 T).indicator f) ε) f
    (fun ε => localForcing_integrableOn c a R _ (hcont ε).continuousOn.integrableOn_Icc)
    (localForcing_integrableOn c a R f hfB)
    (fun ε => ((hcont ε).continuousOn.integrableOn_Icc.sub hfB).norm)
    (timeAverage_forcing_error_tendsto hB hBT f hf)

/-- The complete limit step for a time-regularization proof. The estimate for
the regularized states is supplied separately by weighted strong-graph
calculus; the conclusion requires only the original energy topology. -/
theorem localEstimate_of_timeAverages {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜} {v : ℝ → WholeL2 n 𝕜}
    (hz : IsEnergySolution c g k f u v) (a : Space n) (R : ℝ)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B < T) (hf : IntegrableOn f (Icc 0 T))
    (he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      Real.sqrt (2 * localEnergy c a R (timeAverage u ε) (timeAverage v ε) B) ≤
        Real.sqrt (2 * localEnergy c a R (timeAverage u ε) (timeAverage v ε) 0) +
          ∫ s in (0 : ℝ)..B,
            localForcingNorm c a R (timeAverage ((Ioo 0 T).indicator f) ε) s) :
    IntegrableOn (localForcingNorm c a R f) (Icc 0 B) ∧
      Real.sqrt (2 * localEnergy c a R u v B) ≤
        Real.sqrt (2 * localEnergy c a R u v 0) +
          ∫ s in (0 : ℝ)..B, localForcingNorm c a R f s := by
  refine ⟨localForcing_integrableOn c a R f
    (hf.mono_set (Icc_subset_Icc le_rfl hBT.le)), ?_⟩
  exact localEstimate_of_limits
    (localEnergy_timeAverage_tendsto hz a R B T B hBT (right_mem_Icc.mpr hB))
    (localEnergy_timeAverage_tendsto hz a R B T 0 hBT (left_mem_Icc.mpr hB))
    (localForcing_timeAverage_integral_tendsto c a R hB hBT f hf) he

section AveragedEquation

open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open Cauchy.Uniqueness
attribute [local instance] Cauchy.Uniqueness.realInnerProductH1

/-- Temporal averaging turns the dual primitive equation into a pointwise
strong dual equation, retaining only Bochner L¹ source regularity. -/
theorem timeAverage_dual_equation_of_increment {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (j : HilbertTriple V H) (a : Form V)
    (T h s : ℝ) (hh : 0 ≤ h) (hs : 0 ≤ s) (hsh : s+h ≤ T)
    (u : ℝ → V) (v f : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hf : IntegrableOn f (Icc 0 T))
    (hdv : ∀ r t : Icc (0 : ℝ) T,
      pivotValue j (v t) - pivotValue j (v r) =
        ∫ q in (r : ℝ)..(t : ℝ), (pivotValue j (f q) - a (u q))) :
    pivotValue j (h⁻¹ • (v (s+h)-v s)) + a (timeAverage u h s) =
      pivotValue j (timeAverage f h s) := by
  have hsi : s ∈ Icc 0 T := ⟨hs, by linarith⟩
  have hshi : s+h ∈ Icc 0 T := ⟨by linarith, hsh⟩
  have hseg : uIcc s (s+h) ⊆ Icc 0 T := uIcc_subset_Icc hsi hshi
  have hfr : IntervalIntegrable f volume s (s+h) := (hf.mono_set hseg).intervalIntegrable
  have hur : IntervalIntegrable u volume s (s+h) := (hu.mono hseg).intervalIntegrable
  have hpfr : IntervalIntegrable (fun r => pivotValue j (f r)) volume s (s+h) :=
    ⟨(pivotValue j).integrable_comp hfr.1, (pivotValue j).integrable_comp hfr.2⟩
  have haur : IntervalIntegrable (fun r => a (u r)) volume s (s+h) :=
    ⟨a.integrable_comp hur.1, a.integrable_comp hur.2⟩
  have hi := hdv ⟨s,hsi⟩ ⟨s+h,hshi⟩
  rw [intervalIntegral.integral_sub hpfr haur,
    (pivotValue j).intervalIntegral_comp_comm hfr,
    a.intervalIntegral_comp_comm hur] at hi
  have hi' := congrArg (h⁻¹ • ·) hi
  simp only [map_smul, map_sub, timeAverage] at hi' ⊢
  rw [hi', smul_sub]
  abel

/-- The averaged whole-space wave equation follows from its original
spacetime distributional PDE; there is no assumed velocity derivative. -/
theorem timeAverage_dual_equation {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {k : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜}
    {v : ℝ → WholeL2 n 𝕜} (hf : LocallyIntegrableForcing f)
    (hz : IsEnergySolution c g k f u v)
    (T h s : ℝ) (hT : 0 < T) (hh : 0 ≤ h) (hs : 0 ≤ s) (hsh : s+h ≤ T) :
    pivotValue (wholeSpaceHilbertTriple n 𝕜) (h⁻¹ • (v (s+h)-v s)) +
      waveForm n 𝕜 c (timeAverage u h s) =
      pivotValue (wholeSpaceHilbertTriple n 𝕜) (timeAverage f h s) := by
  have hsub : Icc 0 T ⊆ Ici (0 : ℝ) := fun _ ht => ht.1
  have hu := hz.1.mono hsub
  have hv := hz.2.1.mono hsub
  exact timeAverage_dual_equation_of_increment (wholeSpaceHilbertTriple n 𝕜)
    (waveForm n 𝕜 c) T h s hh hs hsh u v f hu (hf T hT.le)
    (Energy.dual_increment_of_tests testH1 testH1_denseRange
      (wholeSpaceHilbertTriple n 𝕜) (waveForm n 𝕜 c) T hT
      u v f hu hv (hf T hT.le)
      (Energy.forced_test_first_identity c T hT.le g k f hf u v hz))

end AveragedEquation

end TimeRegularization

/-- The transport condition on a weight controls the full real or complex wave flux. -/
theorem weighted_flux_nonpos {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c d : ℝ} (hc : 0 ≤ c) (ξ : Space n) (v : 𝕜)
    (p : EuclideanSpace 𝕜 (Fin n)) (hd : d + c * ‖ξ‖ ≤ 0) :
    d * (‖v‖ ^ 2 + c ^ 2 * ‖p‖ ^ 2) / 2 -
      c ^ 2 * ∑ j : Fin n, ξ j * inner ℝ v (p j) ≤ 0 := by
  let e : ℝ := (‖v‖ ^ 2 + c ^ 2 * ‖p‖ ^ 2) / 2
  let F : Space n := WithLp.toLp 2 (fun j => c ^ 2 * RCLike.re (star v * p j))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hF : ‖F‖ ≤ c * e := by
    simpa only [F, e, mul_div_assoc] using P201.SmoothCone.waveFlux_norm_le hc v p
  have hid : inner ℝ ξ F = c ^ 2 * ∑ j : Fin n, ξ j * inner ℝ v (p j) := by
    rw [PiLp.inner_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hpj : inner ℝ v (p j) = RCLike.re (star v * p j) := by
      rw [real_inner_eq_re_inner 𝕜, RCLike.inner_apply']
      rfl
    rw [hpj]
    simp only [F, Real.inner_apply]
    ring
  have hb : -inner ℝ ξ F ≤ ‖ξ‖ * (c * e) :=
    (neg_le_abs _).trans ((abs_real_inner_le_norm ξ F).trans
      (mul_le_mul_of_nonneg_left hF (norm_nonneg _)))
  have hz := mul_nonpos_of_nonpos_of_nonneg hd he
  have hde : d * (‖v‖ ^ 2 + c ^ 2 * ‖p‖ ^ 2) / 2 = d * e := by
    dsimp [e]
    ring
  rw [hde, ← hid]
  nlinarith

section ConeWeights
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ContDiff
open P201Specs

/-- Smooth cutoffs of the shrinking open ball, using the square of the radius. -/
def coneWeight {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) : ℝ :=
  Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))

theorem coneWeight_contDiff {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R : ℝ) :
    ContDiff ℝ ∞ (Function.uncurry (coneWeight k c a R)) := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul (((contDiff_const.sub (contDiff_const.mul contDiff_fst)).pow 2).sub
    ((contDiff_snd.sub contDiff_const).norm_sq ℝ))

theorem coneWeight_nonneg {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    0 ≤ coneWeight k c a R s x := Real.smoothTransition.nonneg _

theorem coneWeight_le_one {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    coneWeight k c a R s x ≤ 1 := Real.smoothTransition.le_one _

theorem coneWeight_eq_zero_iff {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    coneWeight k c a R s x = 0 ↔ x ∉ ball a (R-c*s) := by
  have hk : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  rw [coneWeight, Real.smoothTransition.zero_iff_nonpos]
  have hmul : ∀ q : ℝ, ((k+1 : ℕ) : ℝ) * q ≤ 0 ↔ q ≤ 0 := by
    intro q
    constructor
    · intro h; nlinarith
    · intro h; exact mul_nonpos_of_nonneg_of_nonpos hk.le h
  rw [hmul]
  rw [mem_ball, dist_eq_norm, not_lt]
  constructor
  · intro h
    nlinarith [norm_nonneg (x-a)]
  · intro h
    nlinarith [norm_nonneg (x-a)]

theorem coneWeight_support {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) : Function.support (coneWeight k c a R s) = ball a (R-c*s) := by
  ext x
  change coneWeight k c a R s x ≠ 0 ↔ _
  constructor
  · intro hx
    by_contra hn
    exact hx ((coneWeight_eq_zero_iff k c a R s hr x).mpr hn)
  · intro hx hz
    exact ((coneWeight_eq_zero_iff k c a R s hr x).mp hz) hx

theorem coneWeight_hasCompactSupport {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) : HasCompactSupport (coneWeight k c a R s) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall a (R-c*s))
  rw [coneWeight_support k c a R s hr]
  exact ball_subset_closedBall

theorem coneWeight_tendsto {n : ℕ} (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    Tendsto (fun k : ℕ => coneWeight k c a R s x) atTop
      (𝓝 ((ball a (R-c*s)).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ ball a (R-c*s)
  · rw [Set.indicator_of_mem hx]
    have hx' : ‖x-a‖ < R-c*s := by simpa [dist_eq_norm] using hx
    have hq : 0 < (R-c*s)^2 - ‖x-a‖^2 := by nlinarith [norm_nonneg (x-a)]
    obtain ⟨K,hK⟩ := exists_nat_gt (1 / ((R-c*s)^2 - ‖x-a‖^2))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    dsimp only [coneWeight]
    symm
    apply Real.smoothTransition.one_of_one_le
    have hK' : 1 < (K : ℝ) * ((R-c*s)^2 - ‖x-a‖^2) := (div_lt_iff₀ hq).mp hK
    have hle : (K : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ k+1)
    exact hK'.le.trans (mul_le_mul_of_nonneg_right hle hq.le)
  · rw [Set.indicator_of_notMem hx]
    have hz : ∀ k : ℕ, coneWeight k c a R s x = 0 := fun k =>
      (coneWeight_eq_zero_iff k c a R s hr x).mpr hx
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

lemma smoothTransition_deriv_nonneg (x : ℝ) : 0 ≤ deriv Real.smoothTransition x :=
  Real.smoothTransition.monotone.deriv_nonneg

lemma smoothTransition_deriv_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  have hm : IsMinOn Real.smoothTransition univ x := by
    intro y _
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y
  exact hm.isLocalMin Filter.univ_mem

theorem coneWeight_hasDerivAt {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    HasDerivAt (fun t => coneWeight k c a R t x)
      (deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2)) *
        (-2 * ((k+1 : ℕ) : ℝ) * c * (R-c*s))) s := by
  have harg : HasDerivAt
      (fun t : ℝ => ((k+1 : ℕ) : ℝ) * ((R-c*t)^2 - ‖x-a‖^2))
      (-2 * ((k+1 : ℕ) : ℝ) * c * (R-c*s)) s := by
    convert ((((hasDerivAt_const s R).sub ((hasDerivAt_id s).const_mul c)).pow 2).sub_const
      (‖x-a‖^2)).const_mul ((k+1 : ℕ) : ℝ) using 1 <;>
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq] <;> ring
  exact ((show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable one_ne_zero).differentiableAt.hasDerivAt.comp s harg

theorem coneWeight_hasFDerivAt {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    HasFDerivAt (coneWeight k c a R s)
      ((-2 * ((k+1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))) •
          innerSL ℝ (x-a)) x := by
  have hnorm := ((hasFDerivAt_id x).sub_const a).norm_sq
  have harg := ((hnorm.const_sub ((R-c*s)^2)).const_mul ((k+1 : ℕ) : ℝ))
  have hθ := (((show ContDiff ℝ 1 Real.smoothTransition from Real.smoothTransition.contDiff).differentiable one_ne_zero)
    (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))).hasDerivAt
  have hcomp := hθ.comp_hasFDerivAt x harg
  have hlin :
      (deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2)) •
        ((k+1 : ℕ) : ℝ) • -(2 • (innerSL ℝ (x-a)).comp (ContinuousLinearMap.id ℝ (Space n)))) =
      ((-2 * ((k+1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))) •
          innerSL ℝ (x-a)) := by
    ext y
    simp only [smul_apply, neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    ring
  simp only [id_eq, ContinuousLinearMap.comp_id] at hlin hcomp
  rw [hlin] at hcomp
  exact hcomp

theorem coneWeight_spatialGradient {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    P201Specs.SmoothCone.spatialGradient (coneWeight k c a R s) x =
      (-2 * ((k+1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))) • (x-a) := by
  apply PiLp.ext
  intro i
  change fderiv ℝ (coneWeight k c a R s) x (coordinate n i) = _
  rw [(coneWeight_hasFDerivAt k c a R s x).fderiv]
  simp [coordinate, P102.U4.coordinateVector, EuclideanSpace.inner_single_right]

theorem coneWeight_gradient_norm {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) :
    ‖P201Specs.SmoothCone.spatialGradient (coneWeight k c a R s) x‖ =
      (2 * ((k+1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))) * ‖x-a‖ := by
  rw [coneWeight_spatialGradient, norm_smul, Real.norm_eq_abs]
  have hd := smoothTransition_deriv_nonneg (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))
  have hk : (0 : ℝ) ≤ ((k+1 : ℕ) : ℝ) := by positivity
  rw [abs_of_nonpos (by nlinarith : -2 * ((k+1 : ℕ) : ℝ) *
    deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2)) ≤ 0)]
  ring

theorem coneWeight_transport {n : ℕ} (k : ℕ) (c : ℝ) (hc : 0 ≤ c) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    deriv (fun t => coneWeight k c a R t x) s +
      c * ‖P201Specs.SmoothCone.spatialGradient (coneWeight k c a R s) x‖ ≤ 0 := by
  rw [(coneWeight_hasDerivAt k c a R s x).deriv, coneWeight_gradient_norm]
  let q : ℝ := ((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2)
  have hk : (0 : ℝ) < ((k+1 : ℕ) : ℝ) := by positivity
  by_cases hq : q ≤ 0
  · rw [smoothTransition_deriv_eq_zero_of_nonpos hq]
    simp
  · have hq' : 0 < (R-c*s)^2 - ‖x-a‖^2 := by
      have := lt_of_not_ge hq
      dsimp [q] at this
      nlinarith
    have hx : ‖x-a‖ ≤ R-c*s := by nlinarith [norm_nonneg (x-a)]
    have hd := smoothTransition_deriv_nonneg q
    calc
      _ = (2 * ((k+1 : ℕ) : ℝ) * deriv Real.smoothTransition q * c) *
          (‖x-a‖ - (R-c*s)) := by dsimp [q]; ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hx)

theorem coneWeight_slice_contDiff {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) :
    ContDiff ℝ ∞ (coneWeight k c a R s) := by
  apply Real.smoothTransition.contDiff.comp
  exact contDiff_const.mul (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

theorem coneWeight_tsupport_subset {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) : tsupport (coneWeight k c a R s) ⊆ closedBall a (R-c*s) := by
  apply closure_minimal _ isClosed_closedBall
  rw [coneWeight_support k c a R s hr]
  exact ball_subset_closedBall

theorem coneWeight_common_support {n : ℕ} (k : ℕ) (c : ℝ) (hc : 0 ≤ c) (a : Space n)
    (R T : ℝ) (hT : 0 < R-c*T) (s : ℝ) (hs : s ∈ Icc 0 T) :
    tsupport (coneWeight k c a R s) ⊆ closedBall a R := by
  have hr : 0 < R-c*s := lt_of_lt_of_le hT (by nlinarith [mul_le_mul_of_nonneg_left hs.2 hc])
  exact (coneWeight_tsupport_subset k c a R s hr).trans
    (closedBall_subset_closedBall (by nlinarith [mul_nonneg hc hs.1]))

theorem coneWeight_le_indicator {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    coneWeight k c a R s x ≤ (ball a (R-c*s)).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ ball a (R-c*s)
  · rw [Set.indicator_of_mem hx]
    exact coneWeight_le_one k c a R s x
  · rw [Set.indicator_of_notMem hx, (coneWeight_eq_zero_iff k c a R s hr x).mpr hx]

theorem coneWeight_norm_smul_le {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (x : Space n) (z : E) :
    ‖coneWeight k c a R s x • z‖ ≤ ‖z‖ := by
  rw [norm_smul, Real.norm_of_nonneg (coneWeight_nonneg k c a R s x)]
  exact mul_le_of_le_one_left (norm_nonneg z) (coneWeight_le_one k c a R s x)

theorem coneWeight_integrable_smul {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (e : Space n → E)
    (he : Integrable e volume) : Integrable (fun x => coneWeight k c a R s x • e x) volume := by
  exact he.norm.mono' ((coneWeight_slice_contDiff k c a R s).continuous.aestronglyMeasurable.smul
    he.aestronglyMeasurable) (Eventually.of_forall (fun x => coneWeight_norm_smul_le k c a R s x (e x)))

/-- Exact open-ball integral convergence, without a sphere-nullness hypothesis. -/
theorem coneWeight_integral_tendsto {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s) (e : Space n → E)
    (he : Integrable e volume) :
    Tendsto (fun k : ℕ => ∫ x, coneWeight k c a R s x • e x) atTop
      (𝓝 (∫ x in ball a (R-c*s), e x)) := by
  rw [← integral_indicator measurableSet_ball]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖e x‖)
  · intro k
    exact (coneWeight_integrable_smul k c a R s e he).aestronglyMeasurable
  · exact he.norm
  · intro k
    exact Eventually.of_forall (fun x => coneWeight_norm_smul_le k c a R s x (e x))
  · apply Eventually.of_forall
    intro x
    have h := (coneWeight_tendsto c a R s hr x).smul (tendsto_const_nhds (x := e x))
    convert h using 1
    by_cases hx : x ∈ ball a (R-c*s) <;> simp [hx]

/-- Applies to both scalar L² fields and Euclidean gradient L² fields. -/
theorem coneWeight_sq_integral_tendsto {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s) (w : Space n → E)
    (hw : MemLp w 2 volume) :
    Tendsto (fun k : ℕ => ∫ x, coneWeight k c a R s x * ‖w x‖^2) atTop
      (𝓝 (∫ x in ball a (R-c*s), ‖w x‖^2)) := by
  exact coneWeight_integral_tendsto c a R s hr (fun x => ‖w x‖^2) hw.norm.integrable_sq

/-- Every weighted forcing square integral is bounded by the exact ball square integral. -/
theorem coneWeight_sq_integral_le_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s) (w : Space n → E)
    (hw : MemLp w 2 volume) :
    (∫ x, coneWeight k c a R s x * ‖w x‖^2) ≤ ∫ x in ball a (R-c*s), ‖w x‖^2 := by
  rw [← integral_indicator measurableSet_ball]
  apply integral_mono (coneWeight_integrable_smul k c a R s _ hw.norm.integrable_sq)
    (hw.norm.integrable_sq.indicator measurableSet_ball)
  intro x
  change coneWeight k c a R s x * ‖w x‖^2 ≤ _
  by_cases hx : x ∈ ball a (R-c*s)
  · rw [Set.indicator_of_mem hx]
    exact mul_le_of_le_one_left (sq_nonneg _) (coneWeight_le_one k c a R s x)
  · rw [Set.indicator_of_notMem hx, (coneWeight_eq_zero_iff k c a R s hr x).mpr hx, zero_mul]

theorem coneWeight_sqrt_sq_integral_le_ball {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s) (w : Space n → E)
    (hw : MemLp w 2 volume) :
    Real.sqrt (∫ x, coneWeight k c a R s x * ‖w x‖^2) ≤
      Real.sqrt (∫ x in ball a (R-c*s), ‖w x‖^2) :=
  Real.sqrt_le_sqrt (coneWeight_sq_integral_le_ball k c a R s hr w hw)

end ConeWeights


/-- The cutoff endpoint energies converge to exactly the manuscript's weak local energy. -/
theorem coneWeight_localEnergy_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) :
    Tendsto (fun k : ℕ => (1 / 2 : ℝ) * ∫ x : Space n,
      coneWeight k c a R s x * (‖v s x‖^2+c^2*‖hGradient (u s) x‖^2)) atTop
      (𝓝 (localEnergy c a R u v s)) := by
  have hv := (MeasureTheory.Lp.memLp (v s)).norm.integrable_sq
  have hg := (MeasureTheory.Lp.memLp (hGradient (u s))).norm.integrable_sq
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hv hg
  rw [localEnergy_eq_integral]
  exact (coneWeight_integral_tendsto c a R s hr _ (hv.add (hg.const_mul (c^2)))).const_mul (1/2)

/-- The cutoff source is controlled by the original, integrable moving-ball source norm. -/
theorem coneWeight_forcing_le {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s)
    (f : ℝ → WholeL2 n 𝕜) :
    Real.sqrt (∫ x : Space n, coneWeight k c a R s x * ‖f s x‖^2) ≤
      localForcingNorm c a R f s := by
  rw [localForcingNorm_eq_sqrt_integral]
  have hf := MeasureTheory.Lp.memLp (f s)
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hf
  exact coneWeight_sqrt_sq_integral_le_ball k c a R s hr (f s) hf


/-! ## Weighted weak calculus -/
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

def testMulH1 (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜) : WholeH1 n 𝕜 :=
  (P201Specs.hToW 𝕜 ⊤ 1).symm
    (P102.U4.sobolev_testMul 1 2 (P201Specs.hToW 𝕜 ⊤ 1 u) a).choose

lemma testMulH1_underlying (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜) :
    P201Specs.hUnderlying ⊤ 1 (testMulH1 a u) = P102.U4.testMulLp a (P201Specs.hUnderlying ⊤ 1 u) := by
  change P102.U4.sobolevUnderlying
    (P201Specs.hToW 𝕜 ⊤ 1 (testMulH1 a u)) = _
  simp only [testMulH1, ContinuousLinearEquiv.apply_symm_apply]
  exact (P102.U4.sobolev_testMul 1 2 (P201Specs.hToW 𝕜 ⊤ 1 u) a).choose_spec

lemma testMulH1_firstDerivative (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜)
    (j : Fin n) :
    P201Specs.hFirstDerivative (testMulH1 a u) j =
      P102.U4.testMulLp (P102.U4.testPartialWord ⊤ [j] a) (P201Specs.hUnderlying ⊤ 1 u) +
      P102.U4.testMulLp a (P201Specs.hFirstDerivative u j) := by
  apply P102.U4.regularLp_injective ⊤ 2
  change P201Specs.regularDistribution ⊤ (P201Specs.hFirstDerivative (testMulH1 a u) j) = _
  rw [← P201.hilbertDerivativeDistribution ⊤ 1 (testMulH1 a u) ⟨{j}, by simp⟩]
  change P102.U4.distributionPartial ({j} : MultiIndex n)
    (P201Specs.regularDistribution ⊤ (P201Specs.hUnderlying ⊤ 1 (testMulH1 a u))) = _
  rw [testMulH1_underlying]
  change P102.U4.distributionPartial ({j} : MultiIndex n)
    (P102.U4.regularDistribution ⊤ (P102.U4.testMulLp a (P201Specs.hUnderlying ⊤ 1 u))) =
      P102.U4.regularDistribution ⊤
        (P102.U4.testMulLp (P102.U4.testPartialWord ⊤ [j] a) (P201Specs.hUnderlying ⊤ 1 u) +
          P102.U4.testMulLp a (P201Specs.hFirstDerivative u j))
  rw [P102.U4.regularLp_testMul,
    P102.U4.distributionMultiplier_productRule, P102.U4.regularLp_add,
    P102.U4.regularLp_testMul, P102.U4.regularLp_testMul]
  have hd : P102.U4.distributionPartial ({j} : MultiIndex n)
      (P102.U4.regularDistribution ⊤ (P201Specs.hUnderlying ⊤ 1 u)) =
        P102.U4.regularDistribution ⊤ (P201Specs.hFirstDerivative u j) :=
    P201.hilbertDerivativeDistribution ⊤ 1 u ⟨{j}, by simp⟩
  rw [hd]
  congr 2

lemma testMulH1_underlying_ae (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜) :
    (P201Specs.hUnderlying ⊤ 1 (testMulH1 a u) : Space n → 𝕜) =ᵐ[volume]
      fun x => a x * P201Specs.hUnderlying ⊤ 1 u x := by
  rw [testMulH1_underlying]
  exact P102.U4.testMulLp_ae _ _

lemma testMulH1_firstDerivative_ae (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜)
    (j : Fin n) :
    (P201Specs.hFirstDerivative (testMulH1 a u) j : Space n → 𝕜) =ᵐ[volume]
      fun x => P102.U4.multiPartial a {j} x * P201Specs.hUnderlying ⊤ 1 u x +
        a x * P201Specs.hFirstDerivative u j x := by
  rw [testMulH1_firstDerivative]
  have hsum := MeasureTheory.Lp.coeFn_add
    (P102.U4.testMulLp (P102.U4.testPartialWord ⊤ [j] a) (P201Specs.hUnderlying ⊤ 1 u))
    (P102.U4.testMulLp a (P201Specs.hFirstDerivative u j))
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at hsum
  filter_upwards [hsum,
    P102.U4.testMulLp_ae (P102.U4.testPartialWord ⊤ [j] a) (P201Specs.hUnderlying ⊤ 1 u),
    P102.U4.testMulLp_ae a (P201Specs.hFirstDerivative u j)] with x h₁ h₂ h₃
  simp only [Pi.add_apply] at h₁
  rw [h₁, h₂, h₃, P102.U4.testPartialWord_coe]
  simp [P102.U4.multiPartial]

lemma testMulH1_gradient_ae (a : P102.U4.WholeTests n 𝕜) (u : WholeH1 n 𝕜) :
    (P201Specs.hGradient (testMulH1 a u) : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun j => P102.U4.multiPartial a {j} x * P201Specs.hUnderlying ⊤ 1 u x) +
        a x • P201Specs.hGradient u x := by
  have hrep (w : WholeH1 n 𝕜) :
      (P201Specs.hGradient w : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[volume]
        fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative w j x) := by
    have h : (P201Specs.hGradient w : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[P201Specs.domainMeasure ⊤]
        (fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative w j x)) :=
      (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (P201Specs.hFirstDerivative w j))).coeFn_toLp
    simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using h
  filter_upwards [hrep (testMulH1 a u), hrep u,
    ae_all_iff.mpr (fun j => testMulH1_firstDerivative_ae a u j)] with x hw hu hd
  rw [hw, hu]
  ext j
  exact hd j

def realTest (a : P102.U4.WholeTests n ℝ) : P102.U4.WholeTests n 𝕜 :=
  TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) a

@[simp] lemma realTest_apply (a : P102.U4.WholeTests n ℝ) (x : Space n) :
    realTest (𝕜 := 𝕜) a x = (a x : 𝕜) := rfl

lemma realTest_partial (a : P102.U4.WholeTests n ℝ) (j : Fin n) (x : Space n) :
    P102.U4.multiPartial (realTest (𝕜 := 𝕜) a) {j} x =
      (fderiv ℝ a x (P201Specs.coordinate n j) : 𝕜) := by
  change P102.U4.multiPartial ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) ∘ a) {j} x = _
  simp only [P102.U4.multiPartial, Multiset.sort_singleton, P102.U4.partialWord]
  rw [fderiv_comp x (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).differentiableAt
    (a.contDiff.differentiable (by simp) x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

def realTestMulH1 (a : P102.U4.WholeTests n ℝ) (u : WholeH1 n 𝕜) : WholeH1 n 𝕜 :=
  testMulH1 (realTest a) u

lemma realTestMulH1_underlying_ae (a : P102.U4.WholeTests n ℝ) (u : WholeH1 n 𝕜) :
    (P201Specs.hUnderlying ⊤ 1 (realTestMulH1 a u) : Space n → 𝕜) =ᵐ[volume]
      fun x => (a x : 𝕜) * P201Specs.hUnderlying ⊤ 1 u x :=
  testMulH1_underlying_ae (realTest a) u

lemma realTestMulH1_firstDerivative_ae (a : P102.U4.WholeTests n ℝ) (u : WholeH1 n 𝕜)
    (j : Fin n) :
    (P201Specs.hFirstDerivative (realTestMulH1 a u) j : Space n → 𝕜) =ᵐ[volume]
      fun x => (fderiv ℝ a x (P201Specs.coordinate n j) : 𝕜) * P201Specs.hUnderlying ⊤ 1 u x +
        (a x : 𝕜) * P201Specs.hFirstDerivative u j x := by
  simpa only [realTestMulH1, realTest_partial, realTest_apply] using testMulH1_firstDerivative_ae (realTest a) u j

lemma realTestMulH1_gradient_ae (a : P102.U4.WholeTests n ℝ) (u : WholeH1 n 𝕜) :
    (P201Specs.hGradient (realTestMulH1 a u) : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun j => (P201Specs.gradient a x j : 𝕜) * P201Specs.hUnderlying ⊤ 1 u x) +
        (a x : 𝕜) • P201Specs.hGradient u x := by
  simpa only [realTestMulH1, realTest_partial, realTest_apply] using testMulH1_gradient_ae (realTest a) u

section WeightedL2
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Multiplication by the square root of a measurable weight between zero and one. -/
theorem sqrtWeight_memLp (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    MemLp (fun x => Real.sqrt (w x) • z x) 2 (domainMeasure (⊤ : Domain n)) := by
  apply (Lp.memLp z).of_le
    (hw.sqrt.aestronglyMeasurable.smul (Lp.aestronglyMeasurable z))
  exact ae_of_all _ fun x => by
    change ‖Real.sqrt (w x) • z x‖ ≤ ‖z x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using Real.sqrt_le_sqrt (hw₁ x))

def sqrtWeightL2 (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n)) :=
  (sqrtWeight_memLp w hw hw₀ hw₁ z).toLp _

theorem sqrtWeightL2_ae (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    (sqrtWeightL2 w hw hw₀ hw₁ z : Space n → E) =ᵐ[domainMeasure (⊤ : Domain n)]
      fun x => Real.sqrt (w x) • z x := MemLp.coeFn_toLp _

theorem sqrtWeightL2_norm_le (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    ‖sqrtWeightL2 w hw hw₀ hw₁ z‖ ≤ ‖z‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [sqrtWeightL2_ae w hw hw₀ hw₁ z] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (by simpa using Real.sqrt_le_sqrt (hw₁ x))

theorem sqrtWeightL2_sub (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z y : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    sqrtWeightL2 w hw hw₀ hw₁ (z-y) =
      sqrtWeightL2 w hw hw₀ hw₁ z - sqrtWeightL2 w hw hw₀ hw₁ y := by
  apply Lp.ext
  filter_upwards [sqrtWeightL2_ae w hw hw₀ hw₁ (z-y),
    sqrtWeightL2_ae w hw hw₀ hw₁ z, sqrtWeightL2_ae w hw hw₀ hw₁ y,
    Lp.coeFn_sub z y,
    Lp.coeFn_sub (sqrtWeightL2 w hw hw₀ hw₁ z) (sqrtWeightL2 w hw hw₀ hw₁ y)]
    with x h₁ h₂ h₃ h₄ h₅
  simp only [Pi.sub_apply, h₁, h₅, h₄, h₂, h₃, smul_sub]

theorem sqrtWeightL2_lipschitz (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    LipschitzWith 1 (sqrtWeightL2 (E := E) w hw hw₀ hw₁) := by
  apply LipschitzWith.of_dist_le_mul
  intro z y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, ← sqrtWeightL2_sub] using
    sqrtWeightL2_norm_le w hw hw₀ hw₁ (z-y)

theorem sqrtWeightL2_norm_sq [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    ‖sqrtWeightL2 w hw hw₀ hw₁ z‖ ^ 2 =
      ∫ x : Space n, w x * ‖z x‖ ^ 2 := by
  rw [P201.Wave.lp2_norm_sq_integral (𝕜 := ℝ)]
  have h := sqrtWeightL2_ae w hw hw₀ hw₁ z
  simp only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h ⊢
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hw₀ x)]

theorem sqrtWeightL2_inner [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z y : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    inner ℝ (sqrtWeightL2 w hw hw₀ hw₁ z) (sqrtWeightL2 w hw hw₀ hw₁ y) =
      ∫ x : Space n, w x * inner ℝ (z x) (y x) := by
  rw [L2.inner_def]
  have h := sqrtWeightL2_ae w hw hw₀ hw₁ z
  have h' := sqrtWeightL2_ae w hw hw₀ hw₁ y
  simp only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h h' ⊢
  apply integral_congr_ae
  filter_upwards [h, h'] with x hx hy
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hw₀ x)]

theorem weighted_inner_le [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z y : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    (∫ x : Space n, w x * inner ℝ (z x) (y x)) ≤
      Real.sqrt (∫ x : Space n, w x * ‖z x‖ ^ 2) *
      Real.sqrt (∫ x : Space n, w x * ‖y x‖ ^ 2) := by
  rw [← sqrtWeightL2_inner w hw hw₀ hw₁, ← sqrtWeightL2_norm_sq w hw hw₀ hw₁,
    ← sqrtWeightL2_norm_sq w hw hw₀ hw₁, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact real_inner_le_norm _ _

/-- A localized weighted source changes by at most its full L² error. -/
theorem weighted_sqrt_sq_le_add_error [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z y : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    Real.sqrt (∫ x : Space n, w x * ‖z x‖ ^ 2) ≤
      Real.sqrt (∫ x : Space n, w x * ‖y x‖ ^ 2) + ‖z - y‖ := by
  rw [← sqrtWeightL2_norm_sq w hw hw₀ hw₁,
    ← sqrtWeightL2_norm_sq w hw hw₀ hw₁,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ht := norm_le_insert (sqrtWeightL2 w hw hw₀ hw₁ y) (sqrtWeightL2 w hw hw₀ hw₁ z)
  rw [norm_sub_rev, ← sqrtWeightL2_sub] at ht
  exact ht.trans (add_le_add_right (sqrtWeightL2_norm_le w hw hw₀ hw₁ (z-y)) _)


/-- A fixed bounded weight is continuous in the strong L² topology. -/
theorem weighted_sq_integral_tendsto {ι : Type*} {l : Filter ι} [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    {z : ι → MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))}
    {y : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))}
    (hz : Tendsto z l (𝓝 y)) :
    Tendsto (fun i => ∫ x : Space n, w x * ‖z i x‖ ^ 2) l
      (𝓝 (∫ x : Space n, w x * ‖y x‖ ^ 2)) := by
  simp_rw [← sqrtWeightL2_norm_sq w hw hw₀ hw₁]
  exact (((sqrtWeightL2_lipschitz w hw hw₀ hw₁).continuous.continuousAt.tendsto).comp hz).norm.pow 2


end WeightedL2
section WeightedEnergy
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- A weighted energy uses the original weak gradient and genuine L² classes. -/
def weightedEnergy (c : ℝ) (w : Space n → ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) : ℝ :=
  ((∫ x : Space n, w x * ‖v x‖ ^ 2) +
    c ^ 2 * (∫ x : Space n, w x * ‖hGradient u x‖ ^ 2)) / 2

theorem weightedEnergy_nonneg (c : ℝ) (w : Space n → ℝ)
    (hw₀ : ∀ x, 0 ≤ w x) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    0 ≤ weightedEnergy c w u v := by
  unfold weightedEnergy
  exact div_nonneg (add_nonneg (integral_nonneg fun x => mul_nonneg (hw₀ x) (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (integral_nonneg fun x => mul_nonneg (hw₀ x) (sq_nonneg _)))) (by norm_num)

theorem weightedEnergy_tendsto {ι : Type*} {l : Filter ι}
    (c : ℝ) (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    {u : ι → WholeH1 n 𝕜} {v : ι → WholeL2 n 𝕜}
    {u₀ : WholeH1 n 𝕜} {v₀ : WholeL2 n 𝕜}
    (hu : Tendsto u l (𝓝 u₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun i => weightedEnergy c w (u i) (v i)) l
      (𝓝 (weightedEnergy c w u₀ v₀)) := by
  unfold weightedEnergy
  exact ((weighted_sq_integral_tendsto w hw hw₀ hw₁ hv).add
    ((weighted_sq_integral_tendsto w hw hw₀ hw₁
      (gradient_lipschitz.continuous.continuousAt.tendsto.comp hu)).const_mul (c ^ 2))).div_const 2

theorem weighted_velocity_le_energy (c : ℝ) (w : Space n → ℝ)
    (hw₀ : ∀ x, 0 ≤ w x) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    Real.sqrt (∫ x : Space n, w x * ‖v x‖ ^ 2) ≤ Real.sqrt (2 * weightedEnergy c w u v) := by
  apply Real.sqrt_le_sqrt
  unfold weightedEnergy
  have hg : 0 ≤ c ^ 2 * ∫ x : Space n, w x * ‖hGradient u x‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (integral_nonneg fun x => mul_nonneg (hw₀ x) (sq_nonneg _))
  linarith

/-- Weighted Cauchy–Schwarz is sharp and is valid for real or complex fields. -/
theorem weighted_source_work_le (c : ℝ) (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (u : WholeH1 n 𝕜) (v f : WholeL2 n 𝕜) :
    (∫ x : Space n, w x * inner ℝ (f x) (v x)) ≤
      Real.sqrt (∫ x : Space n, w x * ‖f x‖ ^ 2) *
        Real.sqrt (2 * weightedEnergy c w u v) := by
  exact (weighted_inner_le w hw hw₀ hw₁ f v).trans
    (mul_le_mul_of_nonneg_left (weighted_velocity_le_energy c w hw₀ u v) (Real.sqrt_nonneg _))

end WeightedEnergy

section WeightedTimeCalculus
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyUniqueness
namespace WeightedForms
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def energy (a : ℝ → Form V) (b : ℝ → Form H) (x : ℝ → V) (y : ℝ → H) (s : ℝ) :=
  (b s (y s) (y s) + a s (x s) (x s)) / 2

def power (T : ℝ) (a : ℝ → Form V) (b : ℝ → Form H)
    (x : ℝ → V) (y : ℝ → H) (s : ℝ) :=
  (derivWithin (fun r => b r (y s) (y s)) (Icc 0 T) s +
   derivWithin (fun r => a r (x s) (x s)) (Icc 0 T) s) / 2

theorem energy_ac (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V) (b : ℝ → Form H)
    (ha : ScalarC1 T a) (hb : ScalarC1 T b) {x : ℝ → V} {y : ℝ → H}
    (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hy : AbsolutelyContinuousOnInterval y 0 T) :
    AbsolutelyContinuousOnInterval (energy a b x y) 0 T := by
  convert ((varying_form_ac T hT b hb hy).add (varying_form_ac T hT a ha hx)).const_mul (1/2) using 1
  ext r
  dsimp [energy]
  ring

theorem energy_ae_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V) (b : ℝ → Form H)
    (ha : ScalarC1 T a) (hb : ScalarC1 T b)
    (has : ∀ t ∈ Icc 0 T, ∀ u v, a t u v = a t v u)
    (hbs : ∀ t ∈ Icc 0 T, ∀ u v, b t u v = b t v u)
    {x q : ℝ → V} {y d : ℝ → H}
    (hdx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (q t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt y (d t) t) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (energy a b x y)
        (power T a b x y t + b t (d t) (y t) + a t (q t) (x t)) t := by
  filter_upwards [varying_form_ae_hasDerivAt T hT a ha has hdx,
    varying_form_ae_hasDerivAt T hT b hb hbs hdy] with t hda hdb ht
  convert ((hdb ht).add (hda ht)).div_const 2 using 1
  · rfl
  · dsimp [power]
    ring

theorem energy_integral_derivative (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (b : ℝ → Form H)
    (ha : ScalarC1 T a) (hb : ScalarC1 T b)
    (has : ∀ t ∈ Icc 0 T, ∀ u v, a t u v = a t v u)
    (hbs : ∀ t ∈ Icc 0 T, ∀ u v, b t u v = b t v u)
    {x q : ℝ → V} {y d : ℝ → H}
    (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hy : AbsolutelyContinuousOnInterval y 0 T)
    (hdx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (q t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt y (d t) t)
    {s t : ℝ} (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun r => power T a b x y r + b r (d r) (y r) + a r (q r) (x r)) volume s t ∧
      (∫ r in s..t, power T a b x y r + b r (d r) (y r) + a r (q r) (x r)) =
        energy a b x y t - energy a b x y s := by
  have hsub : uIcc s t ⊆ Icc 0 T := uIcc_subset_Icc hs ht
  have heac : AbsolutelyContinuousOnInterval (energy a b x y) s t :=
    (energy_ac T hT a b ha hb hx hy).mono (by simpa only [uIcc_of_le hT] using hsub)
  have hd := energy_ae_hasDerivAt T hT a b ha hb has hbs hdx hdy
  have heq : deriv (energy a b x y) =ᵐ[volume.restrict (uIcc s t)]
      (fun r => power T a b x y r + b r (d r) (y r) + a r (q r) (x r)) := by
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_uIcc] with r hr hri
    exact (hr (hsub hri)).deriv
  refine ⟨heac.intervalIntegrable_deriv.congr_ae
    (ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc heq), ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_of_ae_restrict_of_subset uIoc_subset_uIcc heq)]
  exact heac.integral_deriv_eq_sub
/-- A sharp square-root estimate from an AC energy and an a.e. differential inequality.
No continuity or absolute integrability of the derivative field is assumed separately. -/
lemma sqrt_energy_estimate_of_ac (a b : ℝ) (hab : a ≤ b) (E W F : ℝ → ℝ)
    (hE : ∀ s ∈ Icc a b, 0 ≤ E s)
    (hF : ∀ᵐ s ∂volume.restrict (Icc a b), 0 ≤ F s)
    (hEac : AbsolutelyContinuousOnInterval E a b)
    (hFi : IntervalIntegrable F volume a b)
    (hdE : ∀ᵐ s ∂volume, s ∈ Icc a b → HasDerivAt E (W s) s)
    (hbound : ∀ᵐ s ∂volume.restrict (Icc a b), W s ≤ F s * Real.sqrt (2 * E s)) :
    Real.sqrt (2 * E b) ≤ Real.sqrt (2 * E a) + ∫ s in a..b, F s := by
  have hreg (δ : ℝ) (hδ : 0 < δ) :
      Real.sqrt (2 * E b + δ) ≤ Real.sqrt (2 * E a + δ) + ∫ s in a..b, F s := by
    let Q : ℝ → ℝ := fun s => 2 * E s + δ
    let R : ℝ → ℝ := fun s => Real.sqrt (Q s)
    have hQac : AbsolutelyContinuousOnInterval Q a b :=
      (hEac.const_mul 2).add (by simpa using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => δ)).contDiffOn.absolutelyContinuousOnInterval)
    have hQc : ContinuousOn Q (Icc a b) := by
      simpa only [uIcc_of_le hab] using hQac.continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc
    have hsqrt : ContDiffOn ℝ 1 Real.sqrt (Icc δ M) := by
      intro x hx
      exact (Real.contDiffAt_sqrt (by linarith [hx.1] : x ≠ 0)).contDiffWithinAt
    obtain ⟨K, hK⟩ := hsqrt.exists_lipschitzOnWith (by decide) (convex_Icc δ M) isCompact_Icc
    have hmap : MapsTo Q (uIcc a b) (Icc δ M) := by
      intro s hs
      rw [uIcc_of_le hab] at hs
      exact ⟨by dsimp [Q]; linarith [hE s hs], (le_abs_self _).trans (hM s hs)⟩
    have hRac : AbsolutelyContinuousOnInterval R a b :=
      hK.comp_absolutelyContinuousOnInterval hmap hQac
    have hdR : ∀ᵐ s ∂volume, s ∈ Icc a b →
        HasDerivAt R (W s / Real.sqrt (Q s)) s := by
      filter_upwards [hdE] with s hs hsi
      have hpos : 0 < Q s := by dsimp [Q]; linarith [hE s hsi]
      convert (((hs hsi).const_mul 2).add_const δ).sqrt hpos.ne' using 1
      dsimp [R, Q]
      field_simp
    have hderiv : deriv R ≤ᵐ[volume.restrict (Icc a b)] F := by
      filter_upwards [ae_restrict_of_ae hdR, ae_restrict_mem measurableSet_Icc, hF, hbound]
        with s hs hsi hFs hbs
      rw [(hs hsi).deriv]
      have hpos : 0 < Q s := by dsimp [Q]; linarith [hE s hsi]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr hpos)).mpr
      exact hbs.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by dsimp [Q]; linarith)) hFs)
    have hi := intervalIntegral.integral_mono_ae_restrict hab
      hRac.intervalIntegrable_deriv hFi hderiv
    rw [hRac.integral_deriv_eq_sub] at hi
    change Real.sqrt (2 * E b + δ) - Real.sqrt (2 * E a + δ) ≤ _ at hi
    linarith
  have hid : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun δ : ℝ => Real.sqrt (2 * E b + δ))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E b))) := by
    have hsum : Tendsto (fun δ : ℝ => 2 * E b + δ) (nhdsWithin 0 (Ioi 0))
        (nhds (2 * E b + 0)) := tendsto_const_nhds.add hid
    simpa only [add_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsum
  have hright : Tendsto (fun δ : ℝ => Real.sqrt (2 * E a + δ) + ∫ s in a..b, F s)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E a) + ∫ s in a..b, F s)) := by
    have hlim : Tendsto (fun δ : ℝ => Real.sqrt (2 * E a + δ))
        (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E a))) := by
      have hsum : Tendsto (fun δ : ℝ => 2 * E a + δ) (nhdsWithin 0 (Ioi 0))
          (nhds (2 * E a + 0)) := tendsto_const_nhds.add hid
      simpa only [add_zero, Function.comp_def] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    exact hlim.add_const _
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact le_of_tendsto_of_tendsto hleft hright
    (hpos.mono (fun δ hδ => hreg δ hδ))
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Testing the genuine dual wave equation at a weighted Sobolev velocity
cancels the two quadratic cross terms. `hproduct` is the spatial weak Leibniz
rule, and `hpair` is the actual weighted L² pairing. -/
theorem tested_cancellation (j : HilbertTriple V H)
    (A a : Form V) (b : Form H) (x q z : V) (y d f : H) (flux : ℝ)
    (heq : pivotValue j d + A x = pivotValue j f)
    (hpair : ∀ w : H, inner ℝ w (j.embedding z) = b w y)
    (hproduct : A x z = a q x + flux) :
    b d y + a q x = b f y - flux := by
  have h := congrArg (fun L : StrongDual ℝ V => L z) heq
  simp only [add_apply] at h
  rw [show pivotValue j d z = inner ℝ d (j.embedding z) from
      pivotInjection_apply j d z,
    show pivotValue j f z = inner ℝ f (j.embedding z) from
      pivotInjection_apply j f z, hpair d, hpair f, hproduct] at h
  linarith

end WeightedForms
end WeightedTimeCalculus
/-- The local transport condition makes the integrated weight-power term
no greater than the integrated spatial flux, for real and complex fields. -/
theorem transport_power_le_flux {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} (hc : 0 ≤ c) (ξ : Space n → Space n) (d : Space n → ℝ)
    (v : Space n → 𝕜) (p : Space n → EuclideanSpace 𝕜 (Fin n))
    (htransport : ∀ᵐ x ∂volume, d x + c * ‖ξ x‖ ≤ 0)
    (hpower : Integrable (fun x => d x * (‖v x‖^2+c^2*‖p x‖^2) / 2) volume)
    (hflux : Integrable (fun x => ∑ j : Fin n, ξ x j * inner ℝ (v x) (p x j)) volume) :
    (∫ x, d x * (‖v x‖^2+c^2*‖p x‖^2) / 2) ≤
      c^2 * ∫ x, ∑ j : Fin n, ξ x j * inner ℝ (v x) (p x j) := by
  calc
    _ ≤ ∫ x, c^2 * ∑ j : Fin n, ξ x j * inner ℝ (v x) (p x j) := by
      apply integral_mono_ae hpower (hflux.const_mul (c^2))
      filter_upwards [htransport] with x hx
      linarith [weighted_flux_nonpos hc (ξ x) (v x) (p x) hx]
    _ = _ := integral_const_mul _ _


theorem weighted_sq_integrable {n : ℕ} {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (z : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    Integrable (fun x : Space n => w x * ‖z x‖ ^ 2) := by
  have hz := (Lp.memLp z).norm.integrable_sq
  simp only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
    Measure.restrict_univ] at hz
  exact hz.bdd_mul hw.aestronglyMeasurable (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw₀ x)]
    exact hw₁ x)

theorem weightedEnergy_eq_integral {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1)
    (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    weightedEnergy c w u v = (1 / 2 : ℝ) *
      ∫ x : Space n, w x * (‖v x‖ ^ 2 + c ^ 2 * ‖hGradient u x‖ ^ 2) := by
  simp_rw [mul_add, show ∀ x : Space n,
    w x * (c ^ 2 * ‖hGradient u x‖ ^ 2) = c ^ 2 * (w x * ‖hGradient u x‖ ^ 2) by intro x; ring]
  rw [integral_add (weighted_sq_integrable w hw hw₀ hw₁ v)
    ((weighted_sq_integrable w hw hw₀ hw₁ (hGradient u)).const_mul _), integral_const_mul]
  unfold weightedEnergy
  ring

theorem coneWeight_weightedEnergy_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (c : ℝ) (a : Space n) (R s : ℝ) (hr : 0 < R-c*s)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜) :
    Tendsto (fun k : ℕ => weightedEnergy c (coneWeight k c a R s) (u s) (v s)) atTop
      (𝓝 (localEnergy c a R u v s)) := by
  have he (k : ℕ) := weightedEnergy_eq_integral c (coneWeight k c a R s)
    (coneWeight_slice_contDiff k c a R s).continuous.measurable
    (coneWeight_nonneg k c a R s) (coneWeight_le_one k c a R s) (u s) (v s)
  simp_rw [he]
  exact coneWeight_localEnergy_tendsto c a R s hr u v

open ExpandedFA.Evolution.SymmetricHyperbolicEquation

theorem timeAverage_zeroExtension_eq {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : ℝ → WholeL2 n 𝕜) {B T ε s : ℝ}
    (hε : 0 ≤ ε) (hs : s ∈ Icc 0 B) (hBε : B+ε < T) :
    timeAverage ((Ioo 0 T).indicator f) ε s = timeAverage f ε s := by
  unfold timeAverage
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : uIoc s (s+ε) ⊆ Icc 0 (B+ε) := by
    rw [uIoc_of_le (by linarith)]
    intro x hx
    exact ⟨hs.1.trans hx.1.le, hx.2.trans (by linarith [hs.2])⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub (forcing_zeroExtension_ae_on f hBε)

/-- The weighted endpoint energies survive temporal regularization in exactly H¹ × L². -/
theorem weightedEnergy_timeAverage_tendsto {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {h : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜} {v : ℝ → WholeL2 n 𝕜}
    (hz : IsEnergySolution c g h f u v) {B T : ℝ} (hBT : B < T)
    (s : ℝ) (hs : s ∈ Icc 0 B) (w : Space n → ℝ) (hw : Measurable w)
    (hw₀ : ∀ x, 0 ≤ w x) (hw₁ : ∀ x, w x ≤ 1) :
    Tendsto (fun ε => weightedEnergy c w (timeAverage u ε s) (timeAverage v ε s))
      (𝓝[>] (0 : ℝ)) (𝓝 (weightedEnergy c w (u s) (v s))) := by
  have hl := timeAverage_state_tendstoUniformlyOn hz B T hBT
  exact weightedEnergy_tendsto c w hw hw₀ hw₁ (hl.1.tendsto_at hs) (hl.2.tendsto_at hs)

/-- Passing an integrable source majorant through the time-regularization limit. -/
theorem weightedEstimate_of_timeAverages {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {c : ℝ} {g : WholeH1 n 𝕜} {h : WholeL2 n 𝕜}
    {f : ℝ → WholeL2 n 𝕜} {u : ℝ → WholeH1 n 𝕜} {v : ℝ → WholeL2 n 𝕜}
    (hz : IsEnergySolution c g h f u v) {B T : ℝ} (hB : 0 ≤ B) (hBT : B < T)
    (hf : IntegrableOn f (Icc 0 T)) (w : ℝ → Space n → ℝ)
    (hw : ∀ s, Measurable (w s))
    (hw₀ : ∀ s x, 0 ≤ w s x) (hw₁ : ∀ s x, w s x ≤ 1)
    (A : ℝ → ℝ) (hA : IntegrableOn A (Icc 0 B))
    (he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      Real.sqrt (2 * weightedEnergy c (w B) (timeAverage u ε B) (timeAverage v ε B)) ≤
        Real.sqrt (2 * weightedEnergy c (w 0) (timeAverage u ε 0) (timeAverage v ε 0)) +
          ∫ s in (0 : ℝ)..B, (A s + ‖timeAverage ((Ioo 0 T).indicator f) ε s - f s‖)) :
    Real.sqrt (2 * weightedEnergy c (w B) (u B) (v B)) ≤
      Real.sqrt (2 * weightedEnergy c (w 0) (u 0) (v 0)) + ∫ s in (0 : ℝ)..B, A s := by
  have hF : Integrable ((Ioo 0 T).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hf.mono_set Ioo_subset_Icc_self)
  have hfB : IntegrableOn f (Icc 0 B) := hf.mono_set (Icc_subset_Icc le_rfl hBT.le)
  have hAi : IntervalIntegrable A volume 0 B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr hA
  have herr (ε : ℝ) : IntervalIntegrable
      (fun s => ‖timeAverage ((Ioo 0 T).indicator f) ε s - f s‖) volume 0 B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr
      (((timeAverage_continuous _ hF ε).continuousOn.integrableOn_Icc.sub hfB).norm)
  have hint : Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..B,
      (A s + ‖timeAverage ((Ioo 0 T).indicator f) ε s - f s‖))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s in (0 : ℝ)..B, A s)) := by
    simp_rw [intervalIntegral.integral_add hAi (herr _)]
    simpa only [add_zero] using tendsto_const_nhds.add (timeAverage_forcing_error_tendsto hB hBT f hf)
  exact localEstimate_of_limits
    (weightedEnergy_timeAverage_tendsto hz hBT B (right_mem_Icc.mpr hB) (w B) (hw B) (hw₀ B) (hw₁ B))
    (weightedEnergy_timeAverage_tendsto hz hBT 0 (left_mem_Icc.mpr hB) (w 0) (hw 0) (hw₀ 0) (hw₁ 0)) hint he

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

lemma realTest_partialWord (a : P102.U4.WholeTests n ℝ) (j : Fin n) :
    P102.U4.testPartialWord ⊤ [j] (realTest (𝕜 := 𝕜) a) =
      realTest (P102.U4.testPartialWord ⊤ [j] a) := by
  ext x
  change P102.U4.partialWord (realTest (𝕜 := 𝕜) a) [j] x = _
  have h := realTest_partial (𝕜 := 𝕜) a j x
  simpa only [P102.U4.multiPartial, Multiset.sort_singleton, realTest_apply,
    P102.U4.testPartialWord_coe, P102.U4.partialWord] using h

lemma realTestMulH1_firstDerivative (a : P102.U4.WholeTests n ℝ) (u : WholeH1 n 𝕜)
    (j : Fin n) :
    P201Specs.hFirstDerivative (realTestMulH1 a u) j =
      P102.U4.testMulLp (realTest (P102.U4.testPartialWord ⊤ [j] a)) (P201Specs.hUnderlying ⊤ 1 u) +
      P102.U4.testMulLp (realTest a) (P201Specs.hFirstDerivative u j) := by
  simpa only [realTestMulH1, realTest_partialWord] using testMulH1_firstDerivative (realTest a) u j

lemma realTestMulLp_inner (a : P102.U4.WholeTests n ℝ) (f g : WholeL2 n 𝕜) :
    inner ℝ f (P102.U4.testMulLp (realTest a) g) =
      ∫ x : Space n, a x * inner ℝ (g x) (f x) := by
  rw [real_inner_comm, L2.inner_def]
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [P102.U4.testMulLp_ae (realTest a) g] with x hx
  rw [hx, realTest_apply, ← RCLike.real_smul_eq_coe_mul, real_inner_smul_left]

lemma realTestMulLp_integrable_inner (a : P102.U4.WholeTests n ℝ) (f g : WholeL2 n 𝕜) :
    Integrable (fun x : Space n => a x * inner ℝ (g x) (f x)) := by
  have h := L2.integrable_inner (𝕜 := ℝ) (P102.U4.testMulLp (realTest a) g) f
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
  apply h.congr
  filter_upwards [P102.U4.testMulLp_ae (realTest a) g] with x hx
  rw [hx, realTest_apply, ← RCLike.real_smul_eq_coe_mul, real_inner_smul_left]

lemma realTestMulH1_inner_underlying (a : P102.U4.WholeTests n ℝ)
    (f : WholeL2 n 𝕜) (q : WholeH1 n 𝕜) :
    inner ℝ f (P201Specs.hUnderlying ⊤ 1 (realTestMulH1 a q)) =
      ∫ x : Space n, a x * inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (f x) := by
  change inner ℝ f (P201Specs.hUnderlying ⊤ 1 (testMulH1 (realTest a) q)) = _
  rw [testMulH1_underlying]
  exact realTestMulLp_inner _ _ _

lemma hGradient_inner_ae (u q : WholeH1 n 𝕜) :
    (fun x : Space n => inner ℝ (P201Specs.hGradient q x) (P201Specs.hGradient u x)) =ᵐ[volume]
      fun x => ∑ j : Fin n, inner ℝ (P201Specs.hFirstDerivative q j x) (P201Specs.hFirstDerivative u j x) := by
  have hrep (w : WholeH1 n 𝕜) :
      (P201Specs.hGradient w : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[volume]
        fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative w j x) := by
    have h : (P201Specs.hGradient w : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[P201Specs.domainMeasure ⊤]
        (fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative w j x)) :=
      (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (P201Specs.hFirstDerivative w j))).coeFn_toLp
    simpa only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using h
  filter_upwards [hrep q, hrep u] with x hq hu
  rw [hq, hu]
  rw [PiLp.inner_apply]

lemma realTestMulH1_flux_integrable (a : P102.U4.WholeTests n ℝ)
    (u q : WholeH1 n 𝕜) :
    Integrable (fun x : Space n => ∑ j : Fin n,
      P201Specs.gradient a x j *
        inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (P201Specs.hFirstDerivative u j x)) := by
  apply integrable_finsetSum
  intro j _
  have h := realTestMulLp_integrable_inner (P102.U4.testPartialWord ⊤ [j] a)
    (P201Specs.hFirstDerivative u j) (P201Specs.hUnderlying ⊤ 1 q)
  simpa only [P102.U4.testPartialWord_coe, P102.U4.partialWord] using h

lemma waveForm_realTestMulH1 (c : ℝ) (a : P102.U4.WholeTests n ℝ)
    (u q : WholeH1 n 𝕜) :
    Cauchy.Uniqueness.waveForm n 𝕜 c u (realTestMulH1 a q) =
      c ^ 2 * (∫ x : Space n, a x *
        inner ℝ (P201Specs.hGradient q x) (P201Specs.hGradient u x)) +
      c ^ 2 * (∫ x : Space n, ∑ j : Fin n,
        P201Specs.gradient a x j *
          inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (P201Specs.hFirstDerivative u j x)) := by
  have hB (j : Fin n) : Integrable (fun x : Space n =>
      a x * inner ℝ (P201Specs.hFirstDerivative q j x) (P201Specs.hFirstDerivative u j x)) :=
    realTestMulLp_integrable_inner a _ _
  have hA (j : Fin n) : Integrable (fun x : Space n =>
      P201Specs.gradient a x j *
        inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (P201Specs.hFirstDerivative u j x)) := by
    simpa only [P102.U4.testPartialWord_coe, P102.U4.partialWord] using
      realTestMulLp_integrable_inner (P102.U4.testPartialWord ⊤ [j] a)
        (P201Specs.hFirstDerivative u j) (P201Specs.hUnderlying ⊤ 1 q)
  have hGB : (∫ x : Space n, a x * inner ℝ (P201Specs.hGradient q x) (P201Specs.hGradient u x)) =
      ∑ j : Fin n, ∫ x : Space n,
        a x * inner ℝ (P201Specs.hFirstDerivative q j x) (P201Specs.hFirstDerivative u j x) := by
    rw [← integral_finsetSum _ (fun j _ => hB j)]
    apply integral_congr_ae
    filter_upwards [hGradient_inner_ae u q] with x hx
    rw [hx, Finset.mul_sum]
  rw [hGB, Cauchy.Uniqueness.waveForm_apply]
  simp_rw [realTestMulH1_firstDerivative, inner_add_right, realTestMulLp_inner]
  simp only [P102.U4.testPartialWord_coe, P102.U4.partialWord]
  rw [Finset.sum_add_distrib, ← integral_finsetSum _ (fun j _ => hA j)]
  ring

lemma hGradient_coordinate_ae (u : WholeH1 n 𝕜) :
    ∀ᵐ x : Space n ∂volume, ∀ j : Fin n,
      P201Specs.hGradient u x j = P201Specs.hFirstDerivative u j x := by
  have h : (P201Specs.hGradient u : Space n → EuclideanSpace 𝕜 (Fin n)) =ᵐ[P201Specs.domainMeasure ⊤]
      (fun x => WithLp.toLp 2 (fun j => P201Specs.hFirstDerivative u j x)) :=
    (MemLp.of_eval_piLp (fun j => MeasureTheory.Lp.memLp (P201Specs.hFirstDerivative u j))).coeFn_toLp
  simp only [P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at h
  filter_upwards [h] with x hx j
  exact congrArg (fun z : EuclideanSpace 𝕜 (Fin n) => z j) hx

lemma realTestMulH1_flux_integrable_gradient (a : P102.U4.WholeTests n ℝ)
    (u q : WholeH1 n 𝕜) :
    Integrable (fun x : Space n => ∑ j : Fin n,
      P201Specs.gradient a x j *
        inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (P201Specs.hGradient u x j)) := by
  apply (realTestMulH1_flux_integrable a u q).congr
  filter_upwards [hGradient_coordinate_ae u] with x hx
  simp_rw [hx]

lemma waveForm_realTestMulH1_gradient (c : ℝ) (a : P102.U4.WholeTests n ℝ)
    (u q : WholeH1 n 𝕜) :
    Cauchy.Uniqueness.waveForm n 𝕜 c u (realTestMulH1 a q) =
      c ^ 2 * (∫ x : Space n, a x *
        inner ℝ (P201Specs.hGradient q x) (P201Specs.hGradient u x)) +
      c ^ 2 * (∫ x : Space n, ∑ j : Fin n,
        P201Specs.gradient a x j *
          inner ℝ (P201Specs.hUnderlying ⊤ 1 q x) (P201Specs.hGradient u x j)) := by
  rw [waveForm_realTestMulH1]
  congr 2
  apply integral_congr_ae
  filter_upwards [hGradient_coordinate_ae u] with x hx
  simp_rw [hx]


section ConcreteWeightedForms
open scoped ContDiff
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
namespace WeightedForms
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Bounded measurable real coefficients multiply actual L² classes. -/
def weightMul (a : MeasureTheory.Lp ℝ ∞ μ) : MeasureTheory.Lp E 2 μ →L[ℝ] MeasureTheory.Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).holderL μ ∞ 2 2 a

lemma weightMul_ae (a : MeasureTheory.Lp ℝ ∞ μ) (f : MeasureTheory.Lp E 2 μ) :
    (weightMul a f : X → E) =ᵐ[μ] fun x => a x • f x := by
  exact ContinuousLinearMap.coeFn_holder _ _ _

def weightedForm (a : MeasureTheory.Lp ℝ ∞ μ) : Form (MeasureTheory.Lp E 2 μ) :=
  (innerSL ℝ).bilinearComp (weightMul a) (ContinuousLinearMap.id ℝ _)

lemma weightedForm_apply (a : MeasureTheory.Lp ℝ ∞ μ) (f g : MeasureTheory.Lp E 2 μ) :
    weightedForm a f g = ∫ x, a x * inner ℝ (f x) (g x) ∂μ := by
  change inner ℝ (weightMul a f) g = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [weightMul_ae a f] with x hx
  rw [hx, real_inner_smul_left]

lemma weightedForm_symmetric (a : MeasureTheory.Lp ℝ ∞ μ) (f g : MeasureTheory.Lp E 2 μ) :
    weightedForm a f g = weightedForm a g f := by
  simp only [weightedForm_apply, real_inner_comm]

lemma weightedForm_apply_of_ae {a : X → ℝ} (b : MeasureTheory.Lp ℝ ∞ μ)
    (hb : (b : X → ℝ) =ᵐ[μ] a) (f g : MeasureTheory.Lp E 2 μ) :
    weightedForm b f g = ∫ x, a x * inner ℝ (f x) (g x) ∂μ := by
  rw [weightedForm_apply]
  exact integral_congr_ae (hb.mono fun x hx => by simpa only using congrArg (fun z => z * inner ℝ (f x) (g x)) hx)

lemma weighted_pair_integrable {a : X → ℝ} (ha : AEStronglyMeasurable a μ)
    (C : ℝ) (hC : ∀ᵐ x ∂μ, ‖a x‖ ≤ C) (f g : MeasureTheory.Lp E 2 μ) :
    Integrable (fun x => a x * inner ℝ (f x) (g x)) μ :=
  (ContinuousLinearMap.mul ℝ ℝ).integrable_of_bilin_of_bdd_left C ha hC
    (L2.integrable_inner f g)

/-- Scalar differentiation under the integral needs only a bounded coefficient
and bounded time derivative on an open time neighborhood. -/
lemma weighted_pair_hasDerivAt
    {S : Set ℝ} (hS : IsOpen S) {t : ℝ} (ht : t ∈ S)
    (a da : ℝ → X → ℝ) (C D : ℝ)
    (ha : ∀ s ∈ S, AEStronglyMeasurable (a s) μ)
    (hda : ∀ s ∈ S, AEStronglyMeasurable (da s) μ)
    (hbound : ∀ s ∈ S, ∀ᵐ x ∂μ, ‖a s x‖ ≤ C)
    (hdbound : ∀ᵐ x ∂μ, ∀ s ∈ S, ‖da s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ S, HasDerivAt (fun r => a r x) (da s x) s)
    (f g : MeasureTheory.Lp E 2 μ) :
    HasDerivAt (fun s => ∫ x, a s x * inner ℝ (f x) (g x) ∂μ)
      (∫ x, da t x * inner ℝ (f x) (g x) ∂μ) t := by
  have hw := L2.integrable_inner (𝕜 := ℝ) f g
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun x => D * ‖inner ℝ (f x) (g x)‖) (hS.mem_nhds ht) ?_
      (weighted_pair_integrable (ha t ht) C (hbound t ht) f g) ?_ ?_
      (hw.norm.const_mul D) ?_).2
  · filter_upwards [hS.mem_nhds ht] with s hs
    exact (ha s hs).mul hw.aestronglyMeasurable
  · exact (hda t ht).mul hw.aestronglyMeasurable
  · filter_upwards [hdbound] with x hx s hs
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hx s hs) (norm_nonneg _)
  · filter_upwards [hd] with x hx s hs
    exact (hx s hs).mul_const _

lemma weighted_pair_contDiffOn
    {S : Set ℝ} (hS : IsOpen S)
    (a da : ℝ → X → ℝ) (C D : ℝ)
    (ha : ∀ s ∈ S, AEStronglyMeasurable (a s) μ)
    (hda : ∀ s ∈ S, AEStronglyMeasurable (da s) μ)
    (hbound : ∀ s ∈ S, ∀ᵐ x ∂μ, ‖a s x‖ ≤ C)
    (hdbound : ∀ᵐ x ∂μ, ∀ s ∈ S, ‖da s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ S, HasDerivAt (fun r => a r x) (da s x) s)
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun s => da s x) S)
    (f g : MeasureTheory.Lp E 2 μ) :
    ContDiffOn ℝ 1 (fun s => ∫ x, a s x * inner ℝ (f x) (g x) ∂μ) S := by
  have hw := L2.integrable_inner (𝕜 := ℝ) f g
  have hdif (t : ℝ) (ht : t ∈ S) := weighted_pair_hasDerivAt hS ht a da C D ha hda hbound hdbound hd f g
  have hc : ContinuousOn (fun s => ∫ x, da s x * inner ℝ (f x) (g x) ∂μ) S := by
    apply continuousOn_of_dominated (bound := fun x => D * ‖inner ℝ (f x) (g x)‖)
    · intro s hs
      exact (hda s hs).mul hw.aestronglyMeasurable
    · intro s hs
      filter_upwards [hdbound] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hx s hs) (norm_nonneg _)
    · exact hw.norm.const_mul D
    · filter_upwards [hcont] with x hx
      exact hx.mul continuousOn_const
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hS]
  refine ⟨fun t ht => (hdif t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero]
  exact hc.congr (fun t ht => (hdif t ht).deriv)


lemma weightedForm_hasDerivAt
    {S : Set ℝ} (hS : IsOpen S) {t : ℝ} (ht : t ∈ S)
    (b : ℝ → MeasureTheory.Lp ℝ ∞ μ) (a da : ℝ → X → ℝ) (C D : ℝ)
    (hb : ∀ s ∈ S, (b s : X → ℝ) =ᵐ[μ] a s)
    (ha : ∀ s ∈ S, AEStronglyMeasurable (a s) μ)
    (hda : ∀ s ∈ S, AEStronglyMeasurable (da s) μ)
    (hbound : ∀ s ∈ S, ∀ᵐ x ∂μ, ‖a s x‖ ≤ C)
    (hdbound : ∀ᵐ x ∂μ, ∀ s ∈ S, ‖da s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ S, HasDerivAt (fun r => a r x) (da s x) s)
    (f g : MeasureTheory.Lp E 2 μ) :
    HasDerivAt (fun s => weightedForm (b s) f g)
      (∫ x, da t x * inner ℝ (f x) (g x) ∂μ) t := by
  apply (weighted_pair_hasDerivAt hS ht a da C D ha hda hbound hdbound hd f g).congr_of_eventuallyEq
  filter_upwards [hS.mem_nhds ht] with s hs
  exact weightedForm_apply_of_ae (b s) (hb s hs) f g

lemma weightedForm_scalarC1
    (T : ℝ) {S : Set ℝ} (hS : IsOpen S) (hTS : Icc 0 T ⊆ S)
    (b : ℝ → MeasureTheory.Lp ℝ ∞ μ) (a da : ℝ → X → ℝ) (C D : ℝ)
    (hb : ∀ s ∈ S, (b s : X → ℝ) =ᵐ[μ] a s)
    (ha : ∀ s ∈ S, AEStronglyMeasurable (a s) μ)
    (hda : ∀ s ∈ S, AEStronglyMeasurable (da s) μ)
    (hbound : ∀ s ∈ S, ∀ᵐ x ∂μ, ‖a s x‖ ≤ C)
    (hdbound : ∀ᵐ x ∂μ, ∀ s ∈ S, ‖da s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ S, HasDerivAt (fun r => a r x) (da s x) s)
    (hcont : ∀ᵐ x ∂μ, ContinuousOn (fun s => da s x) S) :
    ScalarC1 T (fun s => weightedForm (E := E) (b s)) := by
  intro f g
  apply ((weighted_pair_contDiffOn hS a da C D ha hda hbound hdbound hd hcont f g).mono hTS).congr
  intro s hs
  exact weightedForm_apply_of_ae (b s) (hb s (hTS hs)) f g

lemma weightedForm_derivWithin
    (T : ℝ) (hT : 0 < T) {S : Set ℝ} (hS : IsOpen S) (hTS : Icc 0 T ⊆ S)
    (b : ℝ → MeasureTheory.Lp ℝ ∞ μ) (a da : ℝ → X → ℝ) (C D : ℝ)
    (hb : ∀ s ∈ S, (b s : X → ℝ) =ᵐ[μ] a s)
    (ha : ∀ s ∈ S, AEStronglyMeasurable (a s) μ)
    (hda : ∀ s ∈ S, AEStronglyMeasurable (da s) μ)
    (hbound : ∀ s ∈ S, ∀ᵐ x ∂μ, ‖a s x‖ ≤ C)
    (hdbound : ∀ᵐ x ∂μ, ∀ s ∈ S, ‖da s x‖ ≤ D)
    (hd : ∀ᵐ x ∂μ, ∀ s ∈ S, HasDerivAt (fun r => a r x) (da s x) s)
    (f g : MeasureTheory.Lp E 2 μ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    derivWithin (fun s => weightedForm (b s) f g) (Icc 0 T) t =
      ∫ x, da t x * inner ℝ (f x) (g x) ∂μ := by
  exact (weightedForm_hasDerivAt hS (hTS ht) b a da C D hb ha hda hbound hdbound hd f g).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc hT t ht)

end WeightedForms

namespace WeightedForms
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
open P201.Wave.Cauchy.Uniqueness
attribute [local instance] realInnerProductH1

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The weighted potential uses the original distributional derivatives. -/
def weightedPotentialForm (c : ℝ) (a : MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n))) :
    Form (WholeH1 n 𝕜) :=
  c ^ 2 • ∑ j : Fin n,
    (weightedForm (E := 𝕜) a).bilinearComp
      ((firstDerivativeCLM (𝕜 := 𝕜) j).restrictScalars ℝ)
      ((firstDerivativeCLM (𝕜 := 𝕜) j).restrictScalars ℝ)

lemma weightedPotentialForm_apply (c : ℝ) (a : MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)))
    (f g : WholeH1 n 𝕜) :
    weightedPotentialForm c a f g = c ^ 2 * ∑ j : Fin n,
      ∫ x : Space n, a x * inner ℝ (hFirstDerivative f j x) (hFirstDerivative g j x) := by
  simp [weightedPotentialForm, ContinuousLinearMap.bilinearComp_apply, weightedForm_apply, P201.domainMeasure, P201Specs.domainMeasure]

lemma weightedPotentialForm_symmetric (c : ℝ) (a : MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)))
    (f g : WholeH1 n 𝕜) :
    weightedPotentialForm c a f g = weightedPotentialForm c a g f := by
  rw [weightedPotentialForm_apply, weightedPotentialForm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change a x * inner ℝ (hFirstDerivative f j x) (hFirstDerivative g j x) = _
    congr 1
    apply real_inner_comm)

lemma weightedPotentialForm_scalarC1 (T c : ℝ)
    (b : ℝ → MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)))
    (ha : ScalarC1 T (fun s => weightedForm (E := 𝕜) (b s))) :
    ScalarC1 T (fun s => weightedPotentialForm (𝕜 := 𝕜) c (b s)) := by
  intro f g
  simp only [weightedPotentialForm, smul_apply, sum_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
  exact contDiffOn_const.mul (ContDiffOn.sum (fun j _ => ha (firstDerivativeCLM j f) (firstDerivativeCLM j g)))

end WeightedForms

open WeightedForms
variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Sharp weighted energy estimate for a genuine strong graph. The scalar
form derivatives and spatial product rule enter through explicit integral
identities. Their transport inequality is proved pointwise and integrated;
the theorem does not assume an energy differential inequality. -/
theorem strongWeightedEstimate {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (j : HilbertTriple V H) (A : Form V) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (b : ℝ → Form H)
    (ha : ScalarC1 T a) (hb : ScalarC1 T b)
    (has : ∀ t ∈ Icc 0 T, ∀ u v, a t u v = a t v u)
    (hbs : ∀ t ∈ Icc 0 T, ∀ u v, b t u v = b t v u)
    (x q z : ℝ → V) (y D f : ℝ → H) (F : ℝ → ℝ)
    (hx : AbsolutelyContinuousOnInterval x 0 T)
    (hy : AbsolutelyContinuousOnInterval y 0 T)
    (hdx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (q t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt y (D t) t)
    (heq : ∀ t ∈ Icc 0 T, pivotValue j (D t) + A (x t) = pivotValue j (f t))
    (hpair : ∀ t ∈ Icc 0 T, ∀ w : H,
      inner ℝ w (j.embedding (z t)) = b t w (y t))
    (c : ℝ) (hc : 0 ≤ c)
    (Y : ℝ → Space n → 𝕜)
    (P : ℝ → Space n → EuclideanSpace 𝕜 (Fin n))
    (ξ : ℝ → Space n → Space n) (ρ : ℝ → Space n → ℝ)
    (hproduct : ∀ t ∈ Icc 0 T, A (x t) (z t) = a t (q t) (x t) +
      c^2 * ∫ w, ∑ i : Fin n, ξ t w i * inner ℝ (Y t w) (P t w i))
    (hpower : ∀ t ∈ Icc 0 T, WeightedForms.power T a b x y t =
      ∫ w, ρ t w * (‖Y t w‖^2+c^2*‖P t w‖^2) / 2)
    (hpowerInt : ∀ t ∈ Icc 0 T,
      Integrable (fun w => ρ t w * (‖Y t w‖^2+c^2*‖P t w‖^2) / 2) volume)
    (hfluxInt : ∀ t ∈ Icc 0 T,
      Integrable (fun w => ∑ i : Fin n, ξ t w i * inner ℝ (Y t w) (P t w i)) volume)
    (htransport : ∀ t ∈ Icc 0 T, ∀ᵐ w ∂volume, ρ t w + c * ‖ξ t w‖ ≤ 0)
    (hE : ∀ t ∈ Icc 0 T, 0 ≤ WeightedForms.energy a b x y t)
    (hF : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ F t)
    (hFi : IntervalIntegrable F volume 0 T)
    (hwork : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      b t (f t) (y t) ≤ F t * Real.sqrt (2 * WeightedForms.energy a b x y t)) :
    Real.sqrt (2 * WeightedForms.energy a b x y T) ≤
      Real.sqrt (2 * WeightedForms.energy a b x y 0) + ∫ t in 0..T, F t := by
  apply WeightedForms.sqrt_energy_estimate_of_ac 0 T hT
    (WeightedForms.energy a b x y)
    (fun t => WeightedForms.power T a b x y t + b t (D t) (y t) + a t (q t) (x t))
    F hE hF
    (WeightedForms.energy_ac T hT a b ha hb hx hy) hFi
    (WeightedForms.energy_ae_hasDerivAt T hT a b ha hb has hbs hdx hdy)
  filter_upwards [hwork, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hcancel := WeightedForms.tested_cancellation j A (a t) (b t)
    (x t) (q t) (z t) (y t) (D t) (f t) _ (heq t hti) (hpair t hti) (hproduct t hti)
  have hbound := transport_power_le_flux hc (ξ t) (ρ t) (Y t) (P t)
    (htransport t hti) (hpowerInt t hti) (hfluxInt t hti)
  rw [← hpower t hti] at hbound
  linarith

end ConcreteWeightedForms

def coneWeightTest {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R - c*s) : P102.U4.WholeTests n ℝ :=
  ⟨coneWeight k c a R s, coneWeight_slice_contDiff k c a R s,
    coneWeight_hasCompactSupport k c a R s hr, subset_univ _⟩

@[simp] lemma coneWeightTest_apply {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    coneWeightTest k c a R s hr x = coneWeight k c a R s x := rfl

lemma coneWeightTest_gradient {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) :
    P201Specs.gradient (coneWeightTest k c a R s hr) =
      P201Specs.SmoothCone.spatialGradient (coneWeight k c a R s) := rfl

lemma coneWeightTest_gradient_formula {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (hr : 0 < R-c*s) (x : Space n) :
    P201Specs.gradient (coneWeightTest k c a R s hr) x =
      (-2 * ((k+1 : ℕ) : ℝ) *
        deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2))) • (x-a) :=
  coneWeight_spatialGradient k c a R s x


section SmoothWeightForms
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

namespace WeightedForms
open P201Specs
variable {n : ℕ}

/-- Smooth compact spatial slices give genuine bounded coefficient classes. -/
def weightCoefficient (w : Space n → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) :
    MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)) :=
  (hw.memLp_of_hasCompactSupport hc).toLp w

lemma weightCoefficient_ae (w : Space n → ℝ) (hw : Continuous w) (hc : HasCompactSupport w) :
    (weightCoefficient w hw hc : Space n → ℝ) =ᵐ[domainMeasure (⊤ : Domain n)] w :=
  MemLp.coeFn_toLp _

def weightTimeDerivative (w : ℝ → Space n → ℝ) (s : ℝ) (x : Space n) : ℝ :=
  fderiv ℝ (Function.uncurry w) (s,x) (1,0)

lemma weightTimeDerivative_continuous (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w)) :
    Continuous (Function.uncurry (weightTimeDerivative w)) := by
  exact (hw.continuous_fderiv_apply one_ne_zero).comp
    (continuous_id.prodMk continuous_const)

lemma weightTimeDerivative_hasDerivAt (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w)) (s : ℝ) (x : Space n) :
    HasDerivAt (fun r => w r x) (weightTimeDerivative w s x) s := by
  exact (hw.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))

lemma weightTimeDerivative_zero_of_common_support
    (w : ℝ → Space n → ℝ) (hw : ContDiff ℝ 1 (Function.uncurry w))
    {A B s : ℝ} {K : Set (Space n)} (hs : s ∈ Ioo A B)
    (hsupport : ∀ t ∈ Icc A B, ∀ x ∉ K, w t x = 0)
    (x : Space n) (hx : x ∉ K) : weightTimeDerivative w s x = 0 := by
  have hzero : (fun t => w t x) =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact hsupport t ⟨ht.1.le,ht.2.le⟩ x hx
  exact (weightTimeDerivative_hasDerivAt w hw s x).unique
    ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hzero)

/-- A smooth weight with common compact support on a larger compact time
interval has uniform coefficient and derivative bounds on its interior. -/
lemma smoothWeight_bounds (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w)) (A B : ℝ)
    (K : Set (Space n)) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc A B, ∀ x ∉ K, w t x = 0) :
    ∃ C D : ℝ, (∀ s ∈ Ioo A B, ∀ x, ‖w s x‖ ≤ C) ∧
      (∀ s ∈ Ioo A B, ∀ x, ‖weightTimeDerivative w s x‖ ≤ D) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hw.continuous.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (weightTimeDerivative_continuous w hw).continuousOn
  refine ⟨max C 0, max D 0, ?_, ?_⟩
  · intro s hs x
    by_cases hx : x ∈ K
    · exact (hC (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩).trans (le_max_left _ _)
    · rw [hsupport s ⟨hs.1.le,hs.2.le⟩ x hx, norm_zero]
      exact le_max_right _ _
  · intro s hs x
    by_cases hx : x ∈ K
    · exact (hD (s,x) ⟨⟨hs.1.le,hs.2.le⟩,hx⟩).trans (le_max_left _ _)
    · rw [weightTimeDerivative_zero_of_common_support w hw hs hsupport x hx, norm_zero]
      exact le_max_right _ _

lemma smoothWeightForm_scalarC1 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w))
    (hwc : ∀ s, HasCompactSupport (w s))
    (A B : ℝ) (hA : A < 0) (hB : T < B)
    (K : Set (Space n)) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc A B, ∀ x ∉ K, w t x = 0) :
    ScalarC1 T (fun s => weightedForm (E := E)
      (weightCoefficient (w s) (hw.continuous.comp (continuous_const.prodMk continuous_id)) (hwc s))) := by
  let b := fun s => weightCoefficient (w s) (hw.continuous.comp (continuous_const.prodMk continuous_id)) (hwc s)
  have hdc := weightTimeDerivative_continuous w hw
  obtain ⟨C,D,hC,hD⟩ := smoothWeight_bounds w hw A B K hK hsupport
  apply weightedForm_scalarC1 T isOpen_Ioo (show Icc 0 T ⊆ Ioo A B from
    fun _ hs => ⟨hA.trans_le hs.1, hs.2.trans_lt hB⟩) b w (weightTimeDerivative w) C D
  · intro s _
    exact weightCoefficient_ae _ _ _
  · intro s _
    exact (hw.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro s _
    exact (hdc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro s hs
    exact ae_of_all _ (hC s hs)
  · exact ae_of_all _ (fun x s hs => hD s hs x)
  · exact ae_of_all _ (fun x s _ => weightTimeDerivative_hasDerivAt w hw s x)
  · exact ae_of_all _ (fun x => (hdc.comp (continuous_id.prodMk continuous_const)).continuousOn)

end WeightedForms

end SmoothWeightForms

section FurtherConeForms
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec


namespace WeightedForms
open P201Specs
variable {n : ℕ}

lemma smoothWeightRepresentedForm_scalarC1 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w))
    (b : ℝ → MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)))
    (hb : ∀ s, (b s : Space n → ℝ) =ᵐ[domainMeasure (⊤ : Domain n)] w s)
    (A B : ℝ) (hA : A < 0) (hB : T < B)
    (K : Set (Space n)) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc A B, ∀ x ∉ K, w t x = 0) :
    ScalarC1 T (fun s => weightedForm (E := E) (b s)) := by
  have hdc := weightTimeDerivative_continuous w hw
  obtain ⟨C,D,hC,hD⟩ := smoothWeight_bounds w hw A B K hK hsupport
  apply weightedForm_scalarC1 T isOpen_Ioo (show Icc 0 T ⊆ Ioo A B from
    fun _ hs => ⟨hA.trans_le hs.1, hs.2.trans_lt hB⟩) b w (weightTimeDerivative w) C D
  · exact fun s _ => hb s
  · intro s _
    exact (hw.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro s _
    exact (hdc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro s hs
    exact ae_of_all _ (hC s hs)
  · exact ae_of_all _ (fun x s hs => hD s hs x)
  · exact ae_of_all _ (fun x s _ => weightTimeDerivative_hasDerivAt w hw s x)
  · exact ae_of_all _ (fun x => (hdc.comp (continuous_id.prodMk continuous_const)).continuousOn)

lemma smoothWeightRepresentedForm_derivWithin {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T) (w : ℝ → Space n → ℝ)
    (hw : ContDiff ℝ 1 (Function.uncurry w))
    (b : ℝ → MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)))
    (hb : ∀ s, (b s : Space n → ℝ) =ᵐ[domainMeasure (⊤ : Domain n)] w s)
    (A B : ℝ) (hA : A < 0) (hB : T < B)
    (K : Set (Space n)) (hK : IsCompact K)
    (hsupport : ∀ t ∈ Icc A B, ∀ x ∉ K, w t x = 0)
    (f g : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    derivWithin (fun s => weightedForm (b s) f g) (Icc 0 T) t =
      ∫ x : Space n, weightTimeDerivative w t x * inner ℝ (f x) (g x) := by
  have hdc := weightTimeDerivative_continuous w hw
  obtain ⟨C,D,hC,hD⟩ := smoothWeight_bounds w hw A B K hK hsupport
  have hTS : Icc 0 T ⊆ Ioo A B := fun _ hs => ⟨hA.trans_le hs.1, hs.2.trans_lt hB⟩
  have he := weightedForm_derivWithin T hT isOpen_Ioo hTS b w (weightTimeDerivative w) C D
    (fun s _ => hb s)
    (fun s _ => (hw.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun s _ => (hdc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun s hs => ae_of_all _ (hC s hs))
    (ae_of_all _ (fun x s hs => hD s hs x))
    (ae_of_all _ (fun x s _ => weightTimeDerivative_hasDerivAt w hw s x)) f g ht
  simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using he

end WeightedForms

open WeightedForms Metric
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy

/-- Common compact spatial support on every finite slab, also at times where
the formal cone radius is nonpositive. -/
lemma coneWeight_common_support_slab {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n)
    (R A B : ℝ) :
    ∃ K : Set (Space n), IsCompact K ∧
      ∀ s ∈ Icc A B, ∀ x ∉ K, coneWeight k c a R s x = 0 := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuous_const.sub (continuous_const.mul continuous_id) : Continuous (fun s : ℝ => R-c*s)).continuousOn)
  refine ⟨closedBall a (max C 0 + 1), isCompact_closedBall _ _, ?_⟩
  intro s hs x hx
  have hr : |R-c*s| ≤ max C 0 := (hC s hs).trans (le_max_left _ _)
  have hx' : max C 0 + 1 < ‖x-a‖ := by
    simpa only [mem_closedBall, not_le, dist_eq_norm] using hx
  have hsq : (R-c*s)^2 - ‖x-a‖^2 ≤ 0 := by
    have := abs_nonneg (R-c*s)
    have := sq_abs (R-c*s)
    nlinarith [norm_nonneg (x-a)]
  exact Real.smoothTransition.zero_of_nonpos
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) hsq)

def coneWeightCoefficient {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) :
    MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n)) :=
  (memLp_top_of_bound (coneWeight_slice_contDiff k c a R s).continuous.aestronglyMeasurable 1
    (ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (coneWeight_nonneg k c a R s x)]
      exact coneWeight_le_one k c a R s x))).toLp (coneWeight k c a R s)

lemma coneWeightCoefficient_ae {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) :
    (coneWeightCoefficient k c a R s : Space n → ℝ) =ᵐ[domainMeasure (⊤ : Domain n)]
      coneWeight k c a R s := MemLp.coeFn_toLp _

lemma coneWeightForm_scalarC1 {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (c : ℝ) (a : Space n) (R T : ℝ) :
    ScalarC1 T (fun s => weightedForm (E := E) (coneWeightCoefficient k c a R s)) := by
  obtain ⟨K,hK,hKsupport⟩ := coneWeight_common_support_slab k c a R (-1) (T+1)
  exact smoothWeightRepresentedForm_scalarC1 T (coneWeight k c a R)
    ((coneWeight_contDiff k c a R).of_le (by simp))
    (coneWeightCoefficient k c a R) (coneWeightCoefficient_ae k c a R)
    (-1) (T+1) (by norm_num) (by linarith) K hK hKsupport

lemma coneWeightForm_derivWithin {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (c : ℝ) (a : Space n) (R T : ℝ) (hT : 0 < T)
    (f g : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) {t : ℝ} (ht : t ∈ Icc 0 T) :
    derivWithin (fun s => weightedForm (coneWeightCoefficient k c a R s) f g) (Icc 0 T) t =
      ∫ x : Space n, deriv (fun s => coneWeight k c a R s x) t * inner ℝ (f x) (g x) := by
  obtain ⟨K,hK,hKsupport⟩ := coneWeight_common_support_slab k c a R (-1) (T+1)
  have he := smoothWeightRepresentedForm_derivWithin T hT (coneWeight k c a R)
    ((coneWeight_contDiff k c a R).of_le (by simp))
    (coneWeightCoefficient k c a R) (coneWeightCoefficient_ae k c a R)
    (-1) (T+1) (by norm_num) (by linarith) K hK hKsupport f g ht
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hd := weightTimeDerivative_hasDerivAt (coneWeight k c a R)
    ((coneWeight_contDiff k c a R).of_le (by simp)) t x
  exact congrArg (fun z => z * inner ℝ (f x) (g x)) hd.deriv.symm



end FurtherConeForms

section
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

lemma coneWeight_weightTimeDerivative {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (x : Space n) :
    WeightedForms.weightTimeDerivative (coneWeight k c a R) s x =
      deriv Real.smoothTransition (((k+1 : ℕ) : ℝ) * ((R-c*s)^2 - ‖x-a‖^2)) *
        (-2 * ((k+1 : ℕ) : ℝ) * c * (R-c*s)) :=
  (WeightedForms.weightTimeDerivative_hasDerivAt (coneWeight k c a R)
    ((coneWeight_contDiff k c a R).of_le (by simp)) s x).unique
      (coneWeight_hasDerivAt k c a R s x)

lemma coneWeight_weightTimeDerivative_eq_deriv {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (x : Space n) :
    WeightedForms.weightTimeDerivative (coneWeight k c a R) s x =
      deriv (fun t => coneWeight k c a R t x) s :=
  (WeightedForms.weightTimeDerivative_hasDerivAt (coneWeight k c a R)
    ((coneWeight_contDiff k c a R).of_le (by simp)) s x).deriv.symm

lemma coneWeight_weightTimeDerivative_transport {n : ℕ} (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (a : Space n) (R s : ℝ) (hr : 0 < R-c*s) (x : Space n) :
    WeightedForms.weightTimeDerivative (coneWeight k c a R) s x +
      c * ‖P201Specs.gradient (coneWeight k c a R s) x‖ ≤ 0 := by
  rw [coneWeight_weightTimeDerivative_eq_deriv]
  exact coneWeight_transport k c hc a R s hr x


end

section
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open WeightedForms
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
open Cauchy.Uniqueness
attribute [local instance] realInnerProductH1

lemma coneWeightPotentialForm_scalarC1 {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (k : ℕ) (c : ℝ) (a : Space n) (R T : ℝ) :
    ScalarC1 T (fun s => weightedPotentialForm (𝕜 := 𝕜) c (coneWeightCoefficient k c a R s)) :=
  weightedPotentialForm_scalarC1 T c _ (coneWeightForm_scalarC1 k c a R T)

lemma coneWeightPotentialForm_derivWithin {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (k : ℕ) (c : ℝ) (a : Space n) (R T : ℝ) (hT : 0 < T)
    (f g : WholeH1 n 𝕜) {t : ℝ} (ht : t ∈ Icc 0 T) :
    derivWithin (fun s => weightedPotentialForm c (coneWeightCoefficient k c a R s) f g)
      (Icc 0 T) t = c^2 * ∑ j : Fin n,
      ∫ x : Space n, deriv (fun s => coneWeight k c a R s x) t *
        inner ℝ (hFirstDerivative f j x) (hFirstDerivative g j x) := by
  have hd (j : Fin n) := (coneWeightForm_scalarC1 (E := 𝕜) k c a R T
    (hFirstDerivative f j) (hFirstDerivative g j)).differentiableOn_one t ht
  have hfun : (fun s => weightedPotentialForm c (coneWeightCoefficient k c a R s) f g) =
      (fun s => c^2 * ∑ j : Fin n,
        weightedForm (coneWeightCoefficient k c a R s) (hFirstDerivative f j) (hFirstDerivative g j)) := by
    funext s
    simp only [weightedPotentialForm, smul_apply, sum_apply,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.coe_restrictScalars', smul_eq_mul]
    rfl
  rw [hfun]
  have hsum : DifferentiableWithinAt ℝ (fun s => ∑ j : Fin n,
      weightedForm (coneWeightCoefficient k c a R s) (hFirstDerivative f j) (hFirstDerivative g j))
      (Icc 0 T) t := by
    convert DifferentiableWithinAt.sum (u := Finset.univ) (fun j _ => hd j) using 1
    ext s
    simp only [Finset.sum_apply]
  rw [derivWithin_const_mul (c^2) hsum, derivWithin_fun_sum (fun j _ => hd j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact coneWeightForm_derivWithin k c a R T hT (hFirstDerivative f j) (hFirstDerivative g j) ht


end

section
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

/-- The sharp smooth-cutoff inequalities imply the original weak moving-ball
estimate by convergence of the two endpoint energies. -/
theorem localEnergyEstimate_of_coneWeightedEstimates
    (hweighted : ∀ {n : ℕ} (𝕜 : Type) [RCLike 𝕜], 1 ≤ n →
      ∀ (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
        (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜),
        0 < c → LocallyIntegrableForcing f → IsEnergySolution c g h f u v →
        ∀ (a : Space n) (R t : ℝ), 0 < R → 0 ≤ t → t < R/c →
          ∀ k : ℕ,
            Real.sqrt (2 * weightedEnergy c (coneWeight k c a R t) (u t) (v t)) ≤
              Real.sqrt (2 * weightedEnergy c (coneWeight k c a R 0) (u 0) (v 0)) +
                ∫ s in (0 : ℝ)..t, localForcingNorm c a R f s) :
    P201Specs.Wave.Cone.localEnergyEstimateStatement := by
  intro n 𝕜 _ hn c g h f u v hc hf hsol a R t hR ht htc
  refine ⟨localForcing_integrableOn c a R f (hf t ht), ?_⟩
  have hrt : 0 < R-c*t := by
    have h := (lt_div_iff₀ hc).mp htc
    nlinarith
  exact localEstimate_of_limits
    (coneWeight_weightedEnergy_tendsto c a R t hrt u v)
    (coneWeight_weightedEnergy_tendsto c a R 0 (by simpa using hR) u v)
    tendsto_const_nhds
    (Eventually.of_forall (hweighted 𝕜 hn c g h f u v hc hf hsol a R t hR ht htc))


end


section
open WeightedForms
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy

lemma coneWeight_timeDerivative_continuous {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) :
    Continuous (fun x : Space n => deriv (fun t => coneWeight k c a R t x) s) := by
  have hw : ContDiff ℝ 1 (Function.uncurry (coneWeight k c a R)) :=
    (coneWeight_contDiff k c a R).of_le (by simp)
  have he : (fun x => deriv (fun t => coneWeight k c a R t x) s) =
      weightTimeDerivative (coneWeight k c a R) s := by
    funext x
    exact (weightTimeDerivative_hasDerivAt _ hw s x).deriv
  rw [he]
  exact (weightTimeDerivative_continuous _ hw).comp (continuous_const.prodMk continuous_id)

lemma coneWeight_timeDerivative_bounded {n : ℕ} (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ) :
    ∃ D : ℝ, ∀ x : Space n, ‖deriv (fun t => coneWeight k c a R t x) s‖ ≤ D := by
  have hw : ContDiff ℝ 1 (Function.uncurry (coneWeight k c a R)) :=
    (coneWeight_contDiff k c a R).of_le (by simp)
  obtain ⟨K,hK,hKs⟩ := coneWeight_common_support_slab k c a R (s-1) (s+1)
  obtain ⟨C,D,hC,hD⟩ := smoothWeight_bounds (coneWeight k c a R) hw (s-1) (s+1) K hK hKs
  refine ⟨D, fun x => ?_⟩
  rw [(weightTimeDerivative_hasDerivAt _ hw s x).deriv]
  exact hD s ⟨by linarith,by linarith⟩ x

lemma coneWeight_timeDerivative_inner_integrable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (f g : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    Integrable (fun x : Space n => deriv (fun t => coneWeight k c a R t x) s *
      inner ℝ (f x) (g x)) volume := by
  obtain ⟨D,hD⟩ := coneWeight_timeDerivative_bounded k c a R s
  have hi := weighted_pair_integrable
    (μ := domainMeasure (⊤ : Domain n))
    (coneWeight_timeDerivative_continuous k c a R s).aestronglyMeasurable
    D (ae_of_all _ hD) f g
  simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using hi

lemma coneWeight_power_integrable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    Integrable (fun x : Space n => deriv (fun t => coneWeight k c a R t x) s *
      (‖v x‖^2 + c^2 * ‖hGradient u x‖^2) / 2) volume := by
  have hv := coneWeight_timeDerivative_inner_integrable k c a R s v v
  have hg := coneWeight_timeDerivative_inner_integrable k c a R s (hGradient u) (hGradient u)
  simp only [real_inner_self_eq_norm_sq] at hv hg
  simpa only [Pi.add_apply, mul_add, mul_left_comm] using (hv.add (hg.const_mul (c^2))).div_const 2


end

section StrongConeEstimate
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
namespace WeightedForms
open P201Specs P201Specs.Wave P201Specs.Wave.Cauchy
open P201.Wave.Cauchy.Uniqueness
attribute [local instance] realInnerProductH1
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

lemma weightedLp_pair_integrable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (a : MeasureTheory.Lp ℝ ∞ μ) (f g : MeasureTheory.Lp E 2 μ) :
    Integrable (fun x => a x * inner ℝ (f x) (g x)) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (weightMul a f) g).congr
  filter_upwards [weightMul_ae a f] with x hx
  rw [hx, real_inner_smul_left]

lemma weightedPotentialForm_apply_gradient
    (c : ℝ) (a : MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n))) (f g : WholeH1 n 𝕜) :
    weightedPotentialForm c a f g = c^2 * ∫ x : Space n,
      a x * inner ℝ (hGradient f x) (hGradient g x) := by
  rw [weightedPotentialForm_apply]
  congr 1
  have hB (j : Fin n) : Integrable (fun x : Space n =>
      a x * inner ℝ (hFirstDerivative f j x) (hFirstDerivative g j x)) := by
    simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using
      weightedLp_pair_integrable a (hFirstDerivative f j) (hFirstDerivative g j)
  rw [← integral_finsetSum _ (fun j _ => hB j)]
  apply integral_congr_ae
  filter_upwards [P201.Wave.Cone.hGradient_inner_ae g f] with x hx
  rw [hx, Finset.mul_sum]

lemma weightedPotentialForm_eq_gradientForm
    (c : ℝ) (a : MeasureTheory.Lp ℝ ∞ (domainMeasure (⊤ : Domain n))) (f g : WholeH1 n 𝕜) :
    weightedPotentialForm c a f g = c^2 * weightedForm a (hGradient f) (hGradient g) := by
  rw [weightedPotentialForm_apply_gradient, weightedForm_apply]
  simp only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ]

end WeightedForms

open WeightedForms
open Cauchy.Uniqueness
attribute [local instance] realInnerProductH1
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

lemma coneWeightForm_apply {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (f g : MeasureTheory.Lp E 2 (domainMeasure (⊤ : Domain n))) :
    weightedForm (coneWeightCoefficient k c a R s) f g =
      ∫ x : Space n, coneWeight k c a R s x * inner ℝ (f x) (g x) := by
  have h := weightedForm_apply_of_ae (coneWeightCoefficient k c a R s)
    (coneWeightCoefficient_ae k c a R s) f g
  simpa only [P201.domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top, Measure.restrict_univ] using h

lemma coneWeightPotentialForm_apply (k : ℕ) (c : ℝ) (a : Space n) (R s : ℝ)
    (u q : WholeH1 n 𝕜) :
    weightedPotentialForm c (coneWeightCoefficient k c a R s) u q =
      c^2 * ∫ x : Space n, coneWeight k c a R s x * inner ℝ (hGradient u x) (hGradient q x) := by
  rw [weightedPotentialForm_eq_gradientForm, coneWeightForm_apply]

lemma coneWeight_formEnergy_eq (k : ℕ) (c : ℝ) (a : Space n) (R : ℝ)
    (x : ℝ → WholeH1 n 𝕜) (y : ℝ → WholeL2 n 𝕜) (s : ℝ) :
    WeightedForms.energy
      (fun t => weightedPotentialForm c (coneWeightCoefficient k c a R t))
      (fun t => weightedForm (coneWeightCoefficient k c a R t)) x y s =
      weightedEnergy c (coneWeight k c a R s) (x s) (y s) := by
  simp only [WeightedForms.energy, coneWeightPotentialForm_apply, coneWeightForm_apply,
    real_inner_self_eq_norm_sq, weightedEnergy]

lemma coneWeightPotentialForm_derivWithin_gradient (k : ℕ) (c : ℝ) (a : Space n) (R B : ℝ)
    (hB : 0 < B) (u q : WholeH1 n 𝕜) {s : ℝ} (hs : s ∈ Icc 0 B) :
    derivWithin (fun t => weightedPotentialForm c (coneWeightCoefficient k c a R t) u q)
      (Icc 0 B) s =
      c^2 * ∫ x : Space n, deriv (fun t => coneWeight k c a R t x) s *
        inner ℝ (hGradient u x) (hGradient q x) := by
  simp_rw [weightedPotentialForm_eq_gradientForm]
  have hdiff := ((coneWeightForm_scalarC1 (E := EuclideanSpace 𝕜 (Fin n)) k c a R B)
    (hGradient u) (hGradient q)).differentiableOn (by simp) s hs
  rw [derivWithin_const_mul _ hdiff, coneWeightForm_derivWithin k c a R B hB _ _ hs]

/-- Strong-graph weighted cone estimate; the forcing is only required to admit
an integrable a.e. weighted L² majorant. -/
theorem coneWeight_strongEstimate (k : ℕ) (c : ℝ) (a : Space n) (R B : ℝ)
    (hB : 0 < B) (hc : 0 ≤ c) (hr : 0 < R-c*B)
    (x q : ℝ → WholeH1 n 𝕜) (y D f : ℝ → WholeL2 n 𝕜)
    (hx : AbsolutelyContinuousOnInterval x 0 B)
    (hy : AbsolutelyContinuousOnInterval y 0 B)
    (hdx : ∀ᵐ s ∂volume, s ∈ Icc 0 B → HasDerivAt x (q s) s)
    (hdy : ∀ᵐ s ∂volume, s ∈ Icc 0 B → HasDerivAt y (D s) s)
    (hkin : ∀ s ∈ Icc 0 B, hUnderlying ⊤ 1 (q s) = y s)
    (heq : ∀ s ∈ Icc 0 B,
      pivotValue (wholeSpaceHilbertTriple n 𝕜) (D s) + waveForm n 𝕜 c (x s) =
        pivotValue (wholeSpaceHilbertTriple n 𝕜) (f s))
    (F : ℝ → ℝ) (hFi : IntervalIntegrable F volume 0 B)
    (hF : ∀ᵐ s ∂volume.restrict (Icc 0 B), 0 ≤ F s)
    (hmajor : ∀ᵐ s ∂volume.restrict (Icc 0 B),
      Real.sqrt (∫ z : Space n, coneWeight k c a R s z * ‖f s z‖^2) ≤ F s) :
    Real.sqrt (2 * weightedEnergy c (coneWeight k c a R B) (x B) (y B)) ≤
      Real.sqrt (2 * weightedEnergy c (coneWeight k c a R 0) (x 0) (y 0)) +
        ∫ s in 0..B, F s := by
  let coeff := coneWeightCoefficient k c a R
  let α := fun s => weightedPotentialForm (𝕜 := 𝕜) c (coeff s)
  let β := fun s => weightedForm (E := 𝕜) (coeff s)
  have hrs (s : ℝ) (hs : s ∈ Icc 0 B) : 0 < R-c*s := by nlinarith [mul_nonneg hc (sub_nonneg.mpr hs.2)]
  let τ (s : ℝ) (hs : s ∈ Icc 0 B) : P102.U4.WholeTests n ℝ :=
    ⟨coneWeight k c a R s, coneWeight_slice_contDiff k c a R s,
      coneWeight_hasCompactSupport k c a R s (hrs s hs), subset_univ _⟩
  let z := fun s => if hs : s ∈ Icc 0 B then realTestMulH1 (τ s hs) (q s) else 0
  let ρ := fun s w => deriv (fun t => coneWeight k c a R t w) s
  let ξ := fun s => P201Specs.gradient (coneWeight k c a R s)
  have he (s : ℝ) : WeightedForms.energy α β x y s =
      weightedEnergy c (coneWeight k c a R s) (x s) (y s) :=
    coneWeight_formEnergy_eq k c a R x y s
  have hca : ScalarC1 B α := weightedPotentialForm_scalarC1 B c coeff (coneWeightForm_scalarC1 k c a R B)
  have hcb : ScalarC1 B β := coneWeightForm_scalarC1 k c a R B
  have hp (s : ℝ) (hs : s ∈ Icc 0 B) (w : WholeL2 n 𝕜) :
      inner ℝ w ((wholeSpaceHilbertTriple n 𝕜).embedding (z s)) = β s w (y s) := by
    change inner ℝ w (hUnderlying ⊤ 1 (z s)) = _
    rw [show z s = realTestMulH1 (τ s hs) (q s) by simp only [z, dite_eq_left hs]]
    rw [realTestMulH1_inner_underlying, hkin s hs]
    change (∫ v : Space n, coneWeight k c a R s v * inner ℝ (y s v) (w v)) = _
    rw [coneWeightForm_apply]
    simp only [real_inner_comm]
  have hprod (s : ℝ) (hs : s ∈ Icc 0 B) :
      waveForm n 𝕜 c (x s) (z s) = α s (q s) (x s) +
        c^2 * ∫ w, ∑ i : Fin n, ξ s w i * inner ℝ (y s w) (hGradient (x s) w i) := by
    rw [show z s = realTestMulH1 (τ s hs) (q s) by simp only [z, dite_eq_left hs]]
    rw [waveForm_realTestMulH1_gradient, hkin s hs]
    change c^2 * (∫ w : Space n, coneWeight k c a R s w * inner ℝ (hGradient (q s) w) (hGradient (x s) w)) + _ = _
    rw [show α s (q s) (x s) = _ from coneWeightPotentialForm_apply k c a R s (q s) (x s)]
    rfl
  have hpow (s : ℝ) (hs : s ∈ Icc 0 B) :
      WeightedForms.power B α β x y s =
        ((∫ w : Space n, ρ s w * ‖y s w‖^2) + c^2 * ∫ w : Space n, ρ s w * ‖hGradient (x s) w‖^2) / 2 := by
    unfold WeightedForms.power
    rw [coneWeightForm_derivWithin k c a R B hB _ _ hs,
      coneWeightPotentialForm_derivWithin_gradient k c a R B hB _ _ hs]
    simp only [real_inner_self_eq_norm_sq]
    rfl
  have hpowInt (s : ℝ) (_hs : s ∈ Icc 0 B) :
      Integrable (fun w : Space n => ρ s w * (‖y s w‖^2+c^2*‖hGradient (x s) w‖^2) / 2) volume :=
    coneWeight_power_integrable k c a R s (x s) (y s)
  have hpw (s : ℝ) (hs : s ∈ Icc 0 B) :
      WeightedForms.power B α β x y s =
        ∫ w : Space n, ρ s w * (‖y s w‖^2+c^2*‖hGradient (x s) w‖^2) / 2 := by
    rw [hpow s hs]
    have hyi := coneWeight_timeDerivative_inner_integrable k c a R s (y s) (y s)
    have hgi := coneWeight_timeDerivative_inner_integrable k c a R s (hGradient (x s)) (hGradient (x s))
    simp only [real_inner_self_eq_norm_sq] at hyi hgi
    have hfun (w : Space n) : ρ s w * (‖y s w‖^2+c^2*‖hGradient (x s) w‖^2) / 2 =
        (ρ s w * ‖y s w‖^2+c^2*(ρ s w * ‖hGradient (x s) w‖^2)) / 2 := by ring
    simp_rw [hfun]
    rw [integral_div, integral_add hyi (hgi.const_mul (c^2)), integral_const_mul]
  have hflux (s : ℝ) (hs : s ∈ Icc 0 B) :
      Integrable (fun w => ∑ i : Fin n, ξ s w i * inner ℝ (y s w) (hGradient (x s) w i)) volume := by
    have hi := realTestMulH1_flux_integrable_gradient (τ s hs) (x s) (q s)
    rw [hkin s hs] at hi
    exact hi
  have htransport (s : ℝ) (hs : s ∈ Icc 0 B) :
      ∀ᵐ w ∂volume, ρ s w + c * ‖ξ s w‖ ≤ 0 :=
    ae_of_all _ (fun w => coneWeight_transport k c hc a R s (hrs s hs) w)
  have hwork : ∀ᵐ s ∂volume.restrict (Icc 0 B),
      β s (f s) (y s) ≤ F s * Real.sqrt (2 * WeightedForms.energy α β x y s) := by
    filter_upwards [hmajor, ae_restrict_mem measurableSet_Icc] with s hs _hsi
    rw [he]
    change weightedForm (coneWeightCoefficient k c a R s) (f s) (y s) ≤ _
    rw [coneWeightForm_apply]
    exact (weighted_source_work_le c (coneWeight k c a R s)
      (coneWeight_slice_contDiff k c a R s).continuous.measurable
      (coneWeight_nonneg k c a R s) (coneWeight_le_one k c a R s) (x s) (y s) (f s)).trans
      (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
  have hstrong := strongWeightedEstimate (wholeSpaceHilbertTriple n 𝕜) (waveForm n 𝕜 c)
    B hB.le α β hca hcb
    (fun _ _ => weightedPotentialForm_symmetric c _)
    (fun _ _ => weightedForm_symmetric _)
    x q z y D f F hx hy hdx hdy heq hp c hc
    (fun s => (y s : Space n → 𝕜)) (fun s => (hGradient (x s) : Space n → EuclideanSpace 𝕜 (Fin n)))
    ξ ρ hprod hpw hpowInt hflux htransport
    (fun s _ => by rw [he]; exact weightedEnergy_nonneg c _ (coneWeight_nonneg k c a R s) _ _)
    hF hFi hwork
  simpa only [he] using hstrong


end StrongConeEstimate

section OriginalWeakEstimate
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open ExpandedFA.Evolution.SymmetricHyperbolicEquation
open Cauchy.Uniqueness
attribute [local instance] realInnerProductH1
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]
/-- The cutoff estimate for the original energy solution, with its original L¹(L²) forcing. -/
theorem coneWeightedEstimate
    (k : ℕ) (c : ℝ) (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hc : 0 < c) (hf : LocallyIntegrableForcing f) (hz : IsEnergySolution c g h f u v)
    (a : Space n) (R B : ℝ) (hB : 0 ≤ B) (hr : 0 < R-c*B) :
    Real.sqrt (2 * weightedEnergy c (coneWeight k c a R B) (u B) (v B)) ≤
      Real.sqrt (2 * weightedEnergy c (coneWeight k c a R 0) (u 0) (v 0)) +
        ∫ s in (0 : ℝ)..B, localForcingNorm c a R f s := by
  by_cases hB0 : B = 0
  · subst B
    simp only [intervalIntegral.integral_same, add_zero, le_refl]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let T := B + 1
  have hBT : B < T := by dsimp [T]; linarith
  have hT : 0 < T := hB.trans_lt hBT
  have hfT := hf T hT.le
  have hfB := hf B hB
  have hF : Integrable ((Ioo 0 T).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hfT.mono_set Ioo_subset_Icc_self)
  have hw (s : ℝ) : Measurable (coneWeight k c a R s) :=
    (coneWeight_slice_contDiff k c a R s).continuous.measurable
  have hA := localForcing_integrableOn c a R f hfB
  apply weightedEstimate_of_timeAverages hz hB hBT hfT (coneWeight k c a R) hw
    (coneWeight_nonneg k c a R) (coneWeight_le_one k c a R)
    (localForcingNorm c a R f) hA
  have hεbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hεbound] with ε hεpos hεlt
  have hε : 0 ≤ ε := hεpos.le
  have hBε : B+ε < T := by dsimp [T]; linarith
  have hgraphs := timeAverage_state_graphs hz T B ε hT.le hB hε hBε.le
  let Fε := timeAverage ((Ioo 0 T).indicator f) ε
  let M : ℝ → ℝ := fun s => localForcingNorm c a R f s + ‖Fε s - f s‖
  have hMi : IntegrableOn M (Icc 0 B) :=
    hA.add (((timeAverage_continuous _ hF ε).continuousOn.integrableOn_Icc.sub hfB).norm)
  apply coneWeight_strongEstimate k c a R B hBpos hc.le hr
    (timeAverage u ε) (velocityAverageH1 u ε) (timeAverage v ε)
    (fun s => ε⁻¹ • (v (s+ε)-v s)) Fε
    hgraphs.1 hgraphs.2.1 hgraphs.2.2.1 hgraphs.2.2.2.1 hgraphs.2.2.2.2
    (fun s hs => by
      have heq := timeAverage_dual_equation hf hz T ε s hT hε hs.1 (by linarith [hs.2])
      rw [← timeAverage_zeroExtension_eq f hε hs hBε] at heq
      exact heq)
    M ((intervalIntegrable_iff_integrableOn_Icc_of_le hB).mpr hMi)
  · exact ae_of_all _ (fun s => add_nonneg (norm_nonneg _) (norm_nonneg _))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hrs : 0 < R-c*s := by nlinarith [mul_le_mul_of_nonneg_left hs.2 hc.le]
    exact (weighted_sqrt_sq_le_add_error (coneWeight k c a R s) (hw s)
      (coneWeight_nonneg k c a R s) (coneWeight_le_one k c a R s) (Fε s) (f s)).trans
        (add_le_add_left (coneWeight_forcing_le k c a R s hrs f) _)


end OriginalWeakEstimate

/-- The original sharp weak cone estimate, without sphere traces or extra forcing regularity. -/
theorem localEnergyEstimate : P201Specs.Wave.Cone.localEnergyEstimateStatement := by
  apply localEnergyEstimate_of_coneWeightedEstimates
  intro n 𝕜 _ hn c g h f u v hc hf hz a R t hR ht htc k
  have hrt : 0 < R-c*t := by
    have hh := (lt_div_iff₀ hc).mp htc
    nlinarith
  exact coneWeightedEstimate k c g h f u v hc hf hz a R t ht hrt

/-- Both initial traces and the source determine vanishing on the backward cone. -/
theorem vanishing : P201Specs.Wave.Cone.vanishingStatement :=
  vanishing_of_localEnergyEstimate localEnergyEstimate

/-- Equal data and source on a backward cone give equal solutions on its slices. -/
theorem domainOfDependence : P201Specs.Wave.Cone.domainOfDependenceStatement :=
  domainOfDependence_of_vanishing vanishing

/-- Essential finite propagation for the initial displacement and velocity. -/
theorem finiteSpeed : P201Specs.Wave.Cone.finiteSpeedStatement :=
  finiteSpeed_of_vanishing vanishing

end P201.Wave.Cone
