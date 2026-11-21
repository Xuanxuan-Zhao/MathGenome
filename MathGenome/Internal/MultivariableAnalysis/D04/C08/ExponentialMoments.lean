import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ExponentialMoments
import MathGenome.Internal.MultivariableAnalysis.D04.C06.SlicingAndMoments
import MathGenome.Internal.MultivariableAnalysis.D04.C08.ProperDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff
namespace D04.ExponentialMoments
open JordanRegions SlicingAndMoments
abbrev tiltedDensity := @Specs.D04.C08.ExponentialMoments.Model.tiltedDensity
abbrev partition := @Specs.D04.C08.ExponentialMoments.Model.partition
abbrev momentDensity := @Specs.D04.C08.ExponentialMoments.Model.momentDensity
abbrev logPartition := @Specs.D04.C08.ExponentialMoments.Model.logPartition
abbrev directionalMean := @Specs.D04.C08.ExponentialMoments.Model.directionalMean
variable {n : ℕ} {S : Set (E n)}

lemma tilted_integrable (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) (p : E n) : RegionIntegrable (tiltedDensity ρ p) := by
  exact weighted_integrable hb ρ hρ _ (Real.continuous_exp.comp (continuous_const.inner continuous_id))

lemma moment_integrable (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) {j : ℕ} (v : Fin j → E n) :
    RegionIntegrable (momentDensity ρ v) := by
  exact weighted_integrable hb ρ hρ _ (continuous_finsetProd _ (fun i _ => continuous_const.inner continuous_id))

 theorem moments_integrable : Specs.D04.C08.ExponentialMoments.moments_integrableType := by
  intro n S hS ρ hρ j v p
  exact weighted_integrable (jordan_bounded hS) _ (tilted_integrable (jordan_bounded hS) ρ hρ p)
    _ (continuous_finsetProd _ (fun i _ => continuous_const.inner continuous_id))

private def scalarEmbedding : ℝ →L[ℝ] E 1 :=
  (1 : ℝ →L[ℝ] ℝ).smulRight (standardBasis 1 0)

@[simp] private lemma scalarEmbedding_apply (t : ℝ) (i : Fin 1) : scalarEmbedding t i = t := by
  fin_cases i
  simp [scalarEmbedding, standardBasis_apply]

private def scalarProjection : E 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 1 => ℝ) 0

@[simp] private lemma scalarProjection_apply (v : E 1) : scalarProjection v = v 0 := rfl

private def kernelDeriv (ρ : S → ℝ) (x : S) (p : E n) : E n →L[ℝ] ℝ :=
  tiltedDensity ρ p x • innerSL ℝ (x : E n)

private lemma kernel_deriv (ρ : S → ℝ) (x : S) (p : E n) :
    HasFDerivAt (fun q => tiltedDensity ρ q x) (kernelDeriv ρ x p) p := by
  have h := (((innerSL ℝ (x : E n)).hasFDerivAt (x := p)).exp).mul_const (ρ x)
  convert h using 1
  · funext q; simp [tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity, real_inner_comm]
  · ext h; simp [kernelDeriv, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity, real_inner_comm]; ring

/-- Compactness is used only for the smooth factor, before multiplication by
an arbitrary bounded (possibly discontinuous) density. -/
private lemma kernel_uniform (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionBounded ρ) (R : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ p q : E n, ‖p‖ ≤ R → ‖q‖ ≤ R → ‖q-p‖ < δ →
      ∀ x : S, ‖kernelDeriv ρ x q - kernelDeriv ρ x p‖ ≤ ε := by
  obtain ⟨M, hM⟩ := hρ
  let N := max M 0 + 1
  have hN : 0 < N := by dsimp [N]; positivity
  let H : E n × E n → E n →L[ℝ] ℝ :=
    fun z => Real.exp (inner ℝ z.2 z.1) • innerSL ℝ z.1
  have hH : Continuous H := by
    exact (Real.continuous_exp.comp (continuous_snd.inner continuous_fst)).smul
      ((innerSL ℝ : E n →L[ℝ] E n →L[ℝ] ℝ).continuous.comp continuous_fst)
  have hc := (hb.isCompact_closure.prod (isCompact_closedBall (0 : E n) R)).uniformContinuousOn_of_continuous hH.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.mp hc (ε / N) (div_pos hε hN)
  refine ⟨δ, hδ, fun p q hp hq hpq x => ?_⟩
  have hh := hd ((x : E n), q) ⟨subset_closure x.property, by simpa using hq⟩
    ((x : E n), p) ⟨subset_closure x.property, by simpa using hp⟩
    (by simpa [Prod.dist_eq, dist_eq_norm] using hpq)
  rw [dist_eq_norm] at hh
  have he : kernelDeriv ρ x q - kernelDeriv ρ x p = ρ x • (H (x,q) - H (x,p)) := by
    simp only [kernelDeriv, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity,
      H, smul_sub, smul_smul]
    congr 1 <;> ring
  rw [he, norm_smul]
  have hm : ‖ρ x‖ ≤ N := (hM x).trans (by dsimp [N]; linarith [le_max_left M 0])
  calc
    ‖ρ x‖ * ‖H (x,q) - H (x,p)‖ ≤ N * (ε / N) :=
      mul_le_mul hm hh.le (norm_nonneg _) hN.le
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hN)

private lemma kernel_uniform_local (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionBounded ρ) (p : E n) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ Metric.ball p δ, ∀ x : S,
      ‖kernelDeriv ρ x q - kernelDeriv ρ x p‖ ≤ ε := by
  obtain ⟨δ,hδ,hd⟩ := kernel_uniform hb ρ hρ (‖p‖+1) ε hε
  refine ⟨min δ 1, lt_min hδ zero_lt_one, fun q hq x => ?_⟩
  have hqp : ‖q-p‖ < min δ 1 := by simpa [dist_eq_norm] using hq
  apply hd p q (by linarith) _ (hqp.trans_le (min_le_left _ _)) x
  have hh := norm_add_le (q-p) p
  rw [sub_add_cancel] at hh
  linarith [hqp.trans_le (min_le_right δ 1)]

private lemma first_derivative (hS : Jordan S) (ρ : S → ℝ) (hρ : RegionIntegrable ρ)
    (p : E n) : DifferentiableAt ℝ (partition ρ) p ∧ ∀ h : E n,
      fderiv ℝ (partition ρ) p h =
        regionIntegral (fun x => inner ℝ h (x : E n) * tiltedDensity ρ p x) := by
  let f : S → E n → E 1 := fun x q => scalarEmbedding (tiltedDensity ρ q x)
  let A : S → E n → E n →L[ℝ] E 1 := fun x q => scalarEmbedding.comp (kernelDeriv ρ x q)
  have hb := jordan_bounded hS
  have hf (q : E n) : VectorRegionIntegrable (fun x => f x q) :=
    ⟨hb, fun i => by simpa [f] using tilted_integrable hb ρ hρ q⟩
  have hA (q : E n) : ProperDerivative.OperatorRegionIntegrable (fun x => A x q) := by
    refine ⟨hb, fun j => ⟨hb, fun i => ?_⟩⟩
    have hw := weighted_integrable hb ρ hρ
      (fun x => Real.exp (inner ℝ q x) * inner ℝ x (standardBasis n j))
      ((Real.continuous_exp.comp (continuous_const.inner continuous_id)).mul
        (continuous_id.inner continuous_const))
    convert hw using 1
    funext x
    simp [A, kernelDeriv, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity]
    change Real.exp (inner ℝ q (x : E n)) * ρ x * inner ℝ (x : E n) (standardBasis n j) = _
    ring
  have hd (x : S) (q : E n) : HasFDerivAt (f x) (A x q) q :=
    scalarEmbedding.hasFDerivAt.comp q (kernel_deriv ρ x q)
  have hu : ∀ ε > 0, ∃ r > 0, Metric.ball p r ⊆ (univ : Set (E n)) ∧
      ∀ q ∈ Metric.ball p r, ∀ x, ‖A x q - A x p‖ ≤ ε := by
    intro ε hε
    have he : 0 < ‖scalarEmbedding‖+1 := by positivity
    obtain ⟨r,hr,hh⟩ := kernel_uniform_local hb ρ hρ.1 p (ε/(‖scalarEmbedding‖+1)) (div_pos hε he)
    refine ⟨r,hr,subset_univ _, fun q hq x => ?_⟩
    have hbnd := ContinuousLinearMap.opNorm_comp_le scalarEmbedding (kernelDeriv ρ x q - kernelDeriv ρ x p)
    rw [ContinuousLinearMap.comp_sub] at hbnd
    change ‖A x q - A x p‖ ≤ _ at hbnd
    apply hbnd.trans
    calc
      ‖scalarEmbedding‖ * ‖kernelDeriv ρ x q - kernelDeriv ρ x p‖ ≤
        ‖scalarEmbedding‖ * (ε/(‖scalarEmbedding‖+1)) := mul_le_mul_of_nonneg_left (hh q hq x) (norm_nonneg _)
      _ ≤ ε := by
        have ht := div_mul_cancel₀ ε (ne_of_gt he)
        nlinarith [div_pos hε he, norm_nonneg scalarEmbedding]
  have hD := ProperDerivative.integral_hasFDerivAt (P := univ) hS f A
    (fun q _ => hf q) (fun q _ => hA q) (fun x q _ => hd x q) p (mem_univ _) hu
  have hscalar := scalarProjection.hasFDerivAt.comp p hD
  have heF : (fun q => scalarProjection (vectorRegionIntegral (fun x => f x q))) = partition ρ := by
    funext q
    change regionIntegral (fun x => f x q 0) = partition ρ q
    simp [f, partition, Specs.D04.C08.ExponentialMoments.Model.partition]
  change HasFDerivAt (fun q => scalarProjection (vectorRegionIntegral (fun x => f x q))) _ p at hscalar
  rw [heF] at hscalar
  refine ⟨hscalar.differentiableAt, fun h => ?_⟩
  rw [hscalar.fderiv]
  have hi := (ProperDerivative.integral_apply (fun x => A x p) (hA p) h).2
  change scalarProjection (ProperDerivative.operatorRegionIntegral (fun x => A x p) h) = _
  rw [hi]
  change regionIntegral (fun x => (A x p h) 0) = _
  congr 1
  funext x
  simp [A, kernelDeriv, real_inner_comm]
  ring


private lemma direction_integrable (hb : Bornology.IsBounded S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) (h : E n) :
    RegionIntegrable (fun x => inner ℝ h (x : E n) * ρ x) :=
  weighted_integrable hb ρ hρ _ (continuous_const.inner continuous_id)

private lemma derivative_as_partition (hS : Jordan S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) (p h : E n) :
    fderiv ℝ (partition ρ) p h = partition (fun x => inner ℝ h (x : E n) * ρ x) p := by
  rw [(first_derivative hS ρ hρ p).2]
  congr 1
  funext x
  dsimp [partition, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.partition,
    Specs.D04.C08.ExponentialMoments.Model.tiltedDensity]
  ring

theorem smooth : Specs.D04.C08.ExponentialMoments.smoothType := by
  intro n S hS ρ hρ r
  induction r generalizing ρ with
  | zero =>
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun p => (first_derivative hS ρ hρ p).1.continuousAt))
  | succ r ih =>
    rw [show ((r+1 : ℕ) : ℕ∞ω) = (r : ℕ∞ω) + 1 by simp]
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨fun p => (first_derivative hS ρ hρ p).1, ?_, fun h => ?_⟩
    · simp
    · have hh := ih (fun x => inner ℝ h (x : E n) * ρ x)
        (direction_integrable (jordan_bounded hS) ρ hρ h)
      convert hh using 1
      funext p
      exact derivative_as_partition hS ρ hρ p h

private lemma derivatives_partition (hS : Jordan S) (ρ : S → ℝ) (hρ : RegionIntegrable ρ)
    (j : ℕ) (v : Fin j → E n) (p : E n) :
    iteratedFDeriv ℝ j (partition ρ) p v = partition (momentDensity ρ v) p := by
  induction j generalizing p with
  | zero =>
    have he : momentDensity ρ v = ρ := by
      funext x
      simp [momentDensity, Specs.D04.C08.ExponentialMoments.Model.momentDensity]
    rw [he]
    simp
  | succ j ih =>
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j (partition ρ)) p :=
      (smooth hS ρ hρ (j+1)).differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j) p
    rw [hd.iteratedFDeriv_succ_apply_left']
    have he : (fun q => iteratedFDeriv ℝ j (partition ρ) q (Fin.tail v)) =
        partition (momentDensity ρ (Fin.tail v)) := funext (fun q => ih (Fin.tail v) q)
    rw [he, derivative_as_partition hS _ (moment_integrable (jordan_bounded hS) ρ hρ _)]
    congr 1
    funext x
    simp [momentDensity, Specs.D04.C08.ExponentialMoments.Model.momentDensity, Fin.prod_univ_succ, Fin.tail]
    ring

theorem derivatives : Specs.D04.C08.ExponentialMoments.derivativesType := by
  intro n S hS ρ hρ j v p
  rw [derivatives_partition hS ρ hρ]
  unfold partition Specs.D04.C08.ExponentialMoments.Model.partition
  congr 1
  funext x
  dsimp [tiltedDensity, momentDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity,
    Specs.D04.C08.ExponentialMoments.Model.momentDensity]
  ring

theorem first_second : Specs.D04.C08.ExponentialMoments.first_secondType := by
  intro n S hS ρ hρ p h k
  refine ⟨(first_derivative hS ρ hρ p).2 h, ?_⟩
  simpa [Fin.prod_univ_succ, mul_assoc] using derivatives hS ρ hρ 2 ![h,k] p

theorem uniform_estimates : Specs.D04.C08.ExponentialMoments.uniform_estimatesType := by
  intro n S hS ρ hρ j v R hR ε hε
  let σ := momentDensity ρ v
  have hb := jordan_bounded hS
  have hσ := moment_integrable hb ρ hρ v
  obtain ⟨δ,hδ,hd⟩ := kernel_uniform hb σ hσ.1 R ε hε
  refine ⟨δ,hδ,fun p q hp hq hpq x => ⟨?_, ?_⟩⟩
  · intro h
    have hh := (kernelDeriv σ x q - kernelDeriv σ x p).le_opNorm h
    have he : (kernelDeriv σ x q - kernelDeriv σ x p) h =
        inner ℝ h (x : E n) * (tiltedDensity σ q x - tiltedDensity σ p x) := by
      simp [kernelDeriv, real_inner_comm]; ring
    rw [he, Real.norm_eq_abs] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hd p q hp hq hpq x) (norm_nonneg _))
  · let T := Metric.closedBall (0 : E n) R ∩ Metric.ball p δ
    have hconv : Convex ℝ T := (convex_closedBall (0 : E n) R).inter (convex_ball p δ)
    have hpT : p ∈ T := ⟨by simpa using hp, Metric.mem_ball_self hδ⟩
    have hqT : q ∈ T := ⟨by simpa using hq, by simpa [dist_eq_norm] using hpq⟩
    have hh := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun u => tiltedDensity σ u x - kernelDeriv σ x p u)
      (f' := fun u => kernelDeriv σ x u - kernelDeriv σ x p)
      (fun u _ => ((kernel_deriv σ x u).sub (kernelDeriv σ x p).hasFDerivAt).hasFDerivWithinAt)
      (fun u hu => hd p u hp (by simpa using hu.1) (by simpa [dist_eq_norm] using hu.2) x)
      hpT hqT
    rw [Real.norm_eq_abs] at hh
    convert hh using 1
    congr 1
    simp [kernelDeriv, inner_sub_left, real_inner_comm]
    ring


private lemma region_mono (hb : Bornology.IsBounded S) (f g : S → ℝ)
    (hf : RegionIntegrable f) (hg : RegionIntegrable g) (hfg : ∀ x, f x ≤ g x) :
    regionIntegral f ≤ regionIntegral g := by
  have hs := region_sub hb g f hg hf
  have hh := region_nonneg hb _ hs.1 (fun x => sub_nonneg.mpr (hfg x))
  rw [hs.2] at hh
  linarith

theorem positive : Specs.D04.C08.ExponentialMoments.positiveType := by
  intro n S hS ρ hρ hpos hm p
  have hb := jordan_bounded hS
  obtain ⟨B,hB,hBx⟩ := hb.exists_pos_norm_le
  let a := Real.exp (- (‖p‖ * B))
  have ha : 0 < a := Real.exp_pos _
  have hlow (x : S) : a ≤ Real.exp (inner ℝ p (x : E n)) := by
    apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp (abs_real_inner_le_norm p (x : E n))).1
    have hx := mul_le_mul_of_nonneg_left (hBx x x.property) (norm_nonneg p)
    linarith
  have hs := region_smul hb ρ hρ a
  have hle := region_mono hb _ _ hs.1 (tilted_integrable hb ρ hρ p)
    (fun x => mul_le_mul_of_nonneg_right (hlow x) (hpos x))
  rw [hs.2] at hle
  exact (mul_pos ha hm).trans_le hle

private lemma log_derivative (hS : Jordan S) (ρ : S → ℝ) (hρ : RegionIntegrable ρ)
    (hne : ∀ p, partition ρ p ≠ 0) (p h : E n) :
    fderiv ℝ (logPartition ρ) p h =
      partition (fun x => inner ℝ h (x : E n) * ρ x) p / partition ρ p := by
  change fderiv ℝ (fun q => Real.log (partition ρ q)) p h = _
  rw [fderiv.log (first_derivative hS ρ hρ p).1 (hne p)]
  simp only [smul_apply, smul_eq_mul, derivative_as_partition hS ρ hρ]
  ring

private lemma center_inner (hb : Bornology.IsBounded S) (σ : S → ℝ)
    (hσ : RegionIntegrable σ) (h : E n) :
    inner ℝ (center σ) h =
      regionIntegral (fun x => inner ℝ h (x : E n) * σ x) / regionIntegral σ := by
  let f : S → E n := fun x => σ x • (x : E n)
  have hf : VectorRegionIntegrable f := by
    refine ⟨hb, fun i => ?_⟩
    have hw := weighted_integrable hb σ hσ _ (PiLp.continuous_apply 2 _ i)
    convert hw using 1
    funext x
    simp [f, mul_comm]
  have hi := (vector_integral_linear f (scalarEmbedding.comp (innerSL ℝ h)).toLinearMap hf).2
  have hh := congrArg (fun z : E 1 => z 0) hi
  change regionIntegral (fun x => scalarEmbedding (inner ℝ h (f x)) 0) =
    scalarEmbedding (inner ℝ h (vectorRegionIntegral f)) 0 at hh
  simp only [scalarEmbedding_apply] at hh
  have hfun : (fun x : S => inner ℝ h (f x)) = (fun x : S => inner ℝ h (x : E n) * σ x) := by
    funext x
    simp [f, inner_smul_right, mul_comm]
  rw [hfun] at hh
  have hc : center σ = (regionIntegral σ)⁻¹ • vectorRegionIntegral f := by
    ext i
    change regionIntegral (fun x => (x : E n) i * σ x) / regionIntegral σ =
      (regionIntegral σ)⁻¹ * regionIntegral (fun x => σ x * (x : E n) i)
    simp [mul_comm, div_eq_mul_inv]
  rw [hc, real_inner_smul_left, real_inner_comm, ← hh]
  ring

theorem log_gradient : Specs.D04.C08.ExponentialMoments.log_gradientType := by
  intro n S hS ρ hρ hpos hm
  have hne : ∀ p, partition ρ p ≠ 0 := fun p => ne_of_gt (positive hS ρ hρ hpos hm p)
  refine ⟨fun r => (smooth hS ρ hρ r).log hne, fun p h => ⟨?_, ?_⟩⟩
  · rw [log_derivative hS ρ hρ hne, center_inner (jordan_bounded hS) _
      (tilted_integrable (jordan_bounded hS) ρ hρ p)]
    congr 1
    dsimp [partition, Specs.D04.C08.ExponentialMoments.Model.partition]
    congr 1
    funext x
    dsimp [tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity]
    ring
  · exact center_inner (jordan_bounded hS) _ (tilted_integrable (jordan_bounded hS) ρ hρ p) h

private lemma region_add (hb : Bornology.IsBounded S) (f g : S → ℝ)
    (hf : RegionIntegrable f) (hg : RegionIntegrable g) :
    RegionIntegrable (fun x => f x + g x) ∧
    regionIntegral (fun x => f x + g x) = regionIntegral f + regionIntegral g := by
  have hn := region_smul hb g hg (-1)
  simp only [neg_one_mul] at hn
  have hs := region_sub hb f (fun x => -g x) hf hn.1
  rw [hn.2] at hs
  simpa only [sub_neg_eq_add] using hs

private lemma centered_square (hb : Bornology.IsBounded S) (σ : S → ℝ)
    (hσ : RegionIntegrable σ) (h : E n) (c : ℝ) :
    RegionIntegrable (fun x => (inner ℝ h (x : E n)-c)^2 * σ x) ∧
    regionIntegral (fun x => (inner ℝ h (x : E n)-c)^2 * σ x) =
      regionIntegral (fun x => inner ℝ h (x : E n)^2 * σ x) -
        2*c*regionIntegral (fun x => inner ℝ h (x : E n) * σ x) + c^2*regionIntegral σ := by
  have hi := direction_integrable hb σ hσ h
  have hi2 := weighted_integrable hb σ hσ (fun x => inner ℝ h x ^ 2) ((continuous_const.inner continuous_id).pow 2)
  have hc := region_smul hb σ hσ (c^2)
  have hc1 := region_smul hb _ hi (2*c)
  have hs := region_sub hb _ _ hi2 hc1.1
  have ha := region_add hb _ _ hs.1 hc.1
  have he : (fun x : S => (inner ℝ h (x : E n)-c)^2 * σ x) =
      (fun x : S => (inner ℝ h (x : E n)^2 * σ x - 2*c*(inner ℝ h (x : E n)*σ x)) + c^2*σ x) := by
    funext x; ring
  rw [he]
  exact ⟨ha.1, by rw [ha.2,hs.2,hc1.2,hc.2]⟩


private lemma log_hessian_calculation (hS : Jordan S) (ρ : S → ℝ)
    (hρ : RegionIntegrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hm : 0 < regionIntegral ρ)
    (p h : E n) :
    iteratedFDeriv ℝ 2 (logPartition ρ) p ![h,h] =
      regionIntegral (fun x => inner ℝ h (x : E n)^2 * tiltedDensity ρ p x) / partition ρ p -
        directionalMean ρ p h ^ 2 := by
  have hne : ∀ q, partition ρ q ≠ 0 := fun q => ne_of_gt (positive hS ρ hρ hpos hm q)
  let τ : S → ℝ := fun x => inner ℝ h (x : E n) * ρ x
  have hτ := direction_integrable (jordan_bounded hS) ρ hρ h
  have hZ := (first_derivative hS ρ hρ p).1.hasFDerivAt
  have hN := (first_derivative hS τ hτ p).1.hasFDerivAt
  have hI := (hasDerivAt_inv (hne p)).comp_hasFDerivAt p hZ
  have hD := hN.mul hI
  have hfun : (fun q => fderiv ℝ (logPartition ρ) q h) =
      (fun q => partition τ q * (partition ρ q)⁻¹) := by
    funext q
    rw [log_derivative hS ρ hρ hne]
    rfl
  have hL : ContDiff ℝ 2 (logPartition ρ) := (smooth hS ρ hρ 2).log hne
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 (logPartition ρ)) p :=
    hL.differentiable_iteratedFDeriv (by norm_num) p
  rw [hd.iteratedFDeriv_succ_apply_left']
  simp only [iteratedFDeriv_one_apply]
  change fderiv ℝ (fun q => fderiv ℝ (logPartition ρ) q h) p h = _
  rw [hfun]
  change fderiv ℝ (partition τ * ((fun y : ℝ => y⁻¹) ∘ partition ρ)) p h = _
  rw [hD.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply]
  have hnum : fderiv ℝ (partition τ) p h =
      regionIntegral (fun x => inner ℝ h (x : E n)^2 * tiltedDensity ρ p x) := by
    rw [(first_derivative hS τ hτ p).2]
    congr 1
    funext x
    dsimp [τ, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity]
    ring
  have hmean : partition τ p =
      regionIntegral (fun x => inner ℝ h (x : E n) * tiltedDensity ρ p x) := by
    dsimp [partition, Specs.D04.C08.ExponentialMoments.Model.partition]
    congr 1
    funext x
    dsimp [τ, tiltedDensity, Specs.D04.C08.ExponentialMoments.Model.tiltedDensity]
    ring
  rw [hnum, (first_derivative hS ρ hρ p).2, hmean]
  dsimp [directionalMean, Specs.D04.C08.ExponentialMoments.Model.directionalMean]
  ring

theorem log_hessian : Specs.D04.C08.ExponentialMoments.log_hessianType := by
  intro n S hS ρ hρ hpos hm p h
  have hb := jordan_bounded hS
  have hσ := tilted_integrable hb ρ hρ p
  have hZ := positive hS ρ hρ hpos hm p
  have hsq := centered_square hb _ hσ h (directionalMean ρ p h)
  have hvariance : iteratedFDeriv ℝ 2 (logPartition ρ) p ![h,h] =
      regionIntegral (fun x : S => (inner ℝ h (x : E n) - directionalMean ρ p h)^2 * tiltedDensity ρ p x) / partition ρ p := by
    rw [log_hessian_calculation hS ρ hρ hpos hm, hsq.2]
    dsimp [directionalMean, Specs.D04.C08.ExponentialMoments.Model.directionalMean]
    change _ = (_ - 2 * (_ / partition ρ p) * _ + (_ / partition ρ p)^2 * partition ρ p) / partition ρ p
    field_simp [ne_of_gt hZ]
    ring
  refine ⟨hsq.1, hvariance, ?_⟩
  rw [hvariance]
  apply div_nonneg _ hZ.le
  exact region_nonneg hb _ hsq.1 (fun x =>
    mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos _).le (hpos x)))

end D04.ExponentialMoments
