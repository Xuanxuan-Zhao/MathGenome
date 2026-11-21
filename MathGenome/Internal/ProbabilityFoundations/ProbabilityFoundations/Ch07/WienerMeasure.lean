import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.WienerMeasure
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.KolmogorovExtension
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.KolmogorovChentsov
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.ContinuousProcessLaw
import Mathlib.Probability.BrownianMotion.Basic

open MeasureTheory ProbabilityTheory Set
open ProbabilityFoundations.Ch05
open scoped NNReal ENNReal Topology

namespace ProbabilityFoundations.Ch07

/-- The covariance-minimum family is consistent on the original cylinder
sigma-algebra, including the empty finite support and the zero coordinate. -/
theorem exists_preWiener :
    ∃ P : Measure (ℝ≥0 → ℝ), IsProbabilityMeasure P ∧
      IsPreBrownianReal (fun t ω => ω t) P := by
  have hstd : ∀ _ : ℝ≥0, Ch04.IsStandardBorel ℝ :=
    fun _ => (Ch04.isStandardBorel_iff ℝ).2 inferInstance
  have hprob : CylinderFramework.IsProbabilityFamily (fun _ : ℝ≥0 => ℝ)
      BrownianReal.projectiveFamily := fun _ => inferInstance
  have hcons : CylinderFramework.Consistent (fun _ : ℝ≥0 => ℝ)
      BrownianReal.projectiveFamily := by
    intro E F hEF
    exact (BrownianReal.isProjectiveMeasureFamily_projectiveFamily F E hEF).symm
  obtain ⟨P, ⟨hP, hm⟩, _⟩ := KolmogorovExtension.kolmogorov_extension
    (fun _ : ℝ≥0 => ℝ) hstd BrownianReal.projectiveFamily hprob hcons
  exact ⟨P, hP, ⟨fun I => ⟨(measurable_pi_iff.mpr fun _ => measurable_pi_apply _).aemeasurable,
    hm I⟩⟩⟩

/-- A finite constant suffices for continuity; evaluating it as three is
unnecessary. It is the fourth absolute moment of a standard normal. -/
noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 1

lemma gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg (fun _ => by positivity)

lemma integral_norm_fourth_gaussianReal (v : ℝ≥0) :
    (∫ x : ℝ, ‖x‖ ^ 4 ∂gaussianReal 0 v) = gaussianFourthMoment * (v : ℝ) ^ 2 := by
  have hscale : (gaussianReal 0 1).map (fun x => Real.sqrt (v : ℝ) * x) =
      gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero, mul_one]
    congr 1
    exact Subtype.ext (Real.sq_sqrt v.coe_nonneg)
  rw [← hscale, integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_mul, mul_pow]
  rw [integral_const_mul]
  have hs : ‖Real.sqrt (v : ℝ)‖ ^ 4 = (v : ℝ) ^ 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      show 4 = 2 * 2 from rfl, pow_mul, Real.sq_sqrt v.coe_nonneg]
  rw [hs, mul_comm]
  rfl

lemma preWiener_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {T : ℝ} (s t : Time T) :
    ((∫⁻ ω, ENNReal.ofReal
      (dist (B (nonnegativeTime t) ω) (B (nonnegativeTime s) ω) ^ (4 : ℝ)) ∂P) : EReal) ≤
      ((gaussianFourthMoment * dist t s ^ (1 + (1 : ℝ)) : ℝ) : EReal) := by
  have hLaw : HasLaw (fun ω => B (nonnegativeTime t) ω - B (nonnegativeTime s) ω)
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) P :=
    hB.hasLaw_sub (nonnegativeTime t) (nonnegativeTime s)
  have hi : Integrable (fun x : ℝ => ‖x‖ ^ 4)
      (gaussianReal 0 (nndist (t : ℝ) (s : ℝ))) :=
    (memLp_id_gaussianReal (μ := 0) (v := nndist (t : ℝ) (s : ℝ)) 4).integrable_norm_pow (by norm_num)
  have heq : (∫⁻ ω, ENNReal.ofReal
      (dist (B (nonnegativeTime t) ω) (B (nonnegativeTime s) ω) ^ (4 : ℝ)) ∂P) =
      ENNReal.ofReal (gaussianFourthMoment * dist t s ^ (2 : ℕ)) := by
    simp only [show (4 : ℝ) = (4 : ℕ) from rfl, Real.rpow_natCast,
      dist_eq_norm]
    rw [hLaw.lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (‖x‖ ^ 4)) (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => by positivity)),
      integral_norm_fourth_gaussianReal]
    rfl
  rw [heq, show (1 + (1 : ℝ)) = (2 : ℕ) from by norm_num, Real.rpow_natCast,
    EReal.coe_ennreal_ofReal, max_eq_left]
  exact mul_nonneg gaussianFourthMoment_nonneg (sq_nonneg _)

/-- Every finite list of the product process has the prescribed Gaussian law. -/
lemma preWiener_tuple_law {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {T : ℝ} {n : ℕ} (τ : Fin n → Time T) :
    HasLaw (fun ω i => B (nonnegativeTime (τ i)) ω) (wienerMarginal τ) P := by
  classical
  let I := Finset.univ.image (fun i => nonnegativeTime (τ i))
  let R : (I → ℝ) → Fin n → ℝ := fun x i =>
    x ⟨nonnegativeTime (τ i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hR : Measurable R := measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  exact (hasLaw_map hR.aemeasurable).comp (hB.hasLaw I)

lemma preWiener_tuple_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {T : ℝ} {n : ℕ} (τ : Fin n → Time T) :
    HasGaussianLaw (fun ω i => B (nonnegativeTime (τ i)) ω) P := by
  classical
  let I := Finset.univ.image (fun i => nonnegativeTime (τ i))
  let L : (I → ℝ) →L[ℝ] Fin n → ℝ :=
    { toFun x i := x ⟨nonnegativeTime (τ i),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact (hB.isGaussianProcess.hasGaussianLaw I).map L

/-- Joint laws transfer mutual independence, not only pairwise independence. -/
lemma iIndepFun_of_joint_law {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Fintype ι] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ι → Ω → ℝ} {Y : ι → Ω' → ℝ}
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hjoint : P.map (fun ω i => X i ω) = Q.map (fun ω i => Y i ω))
    (h : iIndepFun X P) : iIndepFun Y Q := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).2
  rw [← hjoint, h.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
  congr 1
  funext i
  have hh := congrArg (Measure.map (fun x : ι → ℝ => x i)) hjoint
  simpa only [Measure.map_map (measurable_pi_apply i)
    (measurable_pi_iff.mpr hX), Measure.map_map (measurable_pi_apply i)
    (measurable_pi_iff.mpr hY), Function.comp_def] using hh

/-- Applying a measurable function to matching finite laws preserves equality. -/
lemma map_finite_transform {Ω Ω' E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace E] {P : Measure Ω} {Q : Measure Ω'}
    {n : ℕ} {X : Ω → Fin n → ℝ} {Y : Ω' → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (h : P.map X = Q.map Y)
    (g : (Fin n → ℝ) → E) (hg : Measurable g) :
    P.map (fun ω => g (X ω)) = Q.map (fun ω => g (Y ω)) := by
  rw [← Function.comp_def, ← Function.comp_def,
    ← Measure.map_map hg hX, ← Measure.map_map hg hY, h]

/-- The finite laws of the constructed cylinder process imply all the
coordinate assertions in the theorem, after passage to continuous paths. -/
lemma isWienerMeasure_of_finite_laws {T : ℝ}
    (P : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal (fun t ω => ω t) P)
    (W : Measure C(Time T, ℝ)) [IsProbabilityMeasure W]
    (hfinite : ∀ (n : ℕ) (τ : Fin n → Time T),
      W.map (fun f i => f (τ i)) =
        P.map (fun ω i => ω (nonnegativeTime (τ i)))) : IsWienerMeasure T W := by
  have hW (n : ℕ) (τ : Fin n → Time T) :
      Measurable (fun f : C(Time T, ℝ) => fun i => f (τ i)) :=
    measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval (τ i)
  have hP (n : ℕ) (τ : Fin n → Time T) :
      Measurable (fun ω : ℝ≥0 → ℝ => fun i => ω (nonnegativeTime (τ i))) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  have heval (t : Time T) : W.map (fun f => f t) = P.map (fun ω => ω (nonnegativeTime t)) := by
    exact map_finite_transform (hW 1 (fun _ => t)) (hP 1 (fun _ => t))
      (hfinite 1 (fun _ => t)) (fun x => x 0) (measurable_pi_apply _)
  have hlaw (t : Time T) : HasLaw (fun f : C(Time T, ℝ) => f t)
      (gaussianReal 0 (nonnegativeTime t)) W :=
    ⟨(ContinuousMap.measurable_eval t).aemeasurable, (heval t).trans (hB.hasLaw_eval _).map_eq⟩
  have hgauss (n : ℕ) (τ : Fin n → Time T) :
      HasGaussianLaw (fun f : C(Time T, ℝ) => fun i => f (τ i)) W := by
    refine ⟨(hW n τ).aemeasurable, ?_⟩
    rw [hfinite]
    exact (preWiener_tuple_gaussian hB τ).isGaussian_map
  have hcenter (t : Time T) : (∫ f, f t ∂W) = 0 := by
    rw [(hlaw t).integral_eq, integral_id_gaussianReal]
  have hcov (s t : Time T) : covariance (fun f => f s) (fun f => f t) W =
      min (s : ℝ) (t : ℝ) := by
    let τ : Fin 2 → Time T := ![s, t]
    have hm := hfinite 2 τ
    have hh : HasLaw (fun f : C(Time T, ℝ) => fun i => f (τ i))
        (P.map (fun ω i => ω (nonnegativeTime (τ i)))) W :=
      ⟨(hW 2 τ).aemeasurable, hm⟩
    have hp := hasLaw_map (P := P) (hP 2 τ).aemeasurable
    have h1 := hh.covariance_fun_comp
      (f := fun x : Fin 2 → ℝ => x 0) (g := fun x : Fin 2 → ℝ => x 1)
      (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
    have h2 := hp.covariance_fun_comp
      (f := fun x : Fin 2 → ℝ => x 0) (g := fun x : Fin 2 → ℝ => x 1)
      (measurable_pi_apply 0).aemeasurable (measurable_pi_apply 1).aemeasurable
    calc
      _ = covariance (fun ω => ω (nonnegativeTime s))
          (fun ω => ω (nonnegativeTime t)) P := by
        simpa only [τ, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons] using h1.trans h2.symm
      _ = _ := hB.covariance_eval (nonnegativeTime s) (nonnegativeTime t)
  refine ⟨inferInstance, ?_, hgauss, ?_, ?_, ?_, ?_, ?_⟩
  · intro n τ
    exact (hfinite n τ).trans (preWiener_tuple_law hB τ).map_eq
  · intro t ht
    have ht' : nonnegativeTime t = 0 := Subtype.ext ht
    have hh := hlaw t
    rw [ht', gaussianReal_zero_var] at hh
    exact hh.ae_eq_of_dirac
  · intro t
    exact ⟨(hlaw t).hasGaussianLaw.integrable, hcenter t⟩
  · intro s t
    have hs := (hlaw s).hasGaussianLaw.memLp_two
    have ht := (hlaw t).hasGaussianLaw.memLp_two
    refine ⟨hs.integrable_mul ht, ?_⟩
    have hh := hcov s t
    rw [covariance_eq_sub hs ht, hcenter s, hcenter t, zero_mul, sub_zero] at hh
    exact hh
  · intro n τ hτ
    have hn : Monotone (fun i => nonnegativeTime (τ i)) := fun i j hij => hτ hij
    apply iIndepFun_of_joint_law
      (X := fun (i : Fin n) (ω : ℝ≥0 → ℝ) =>
        ω (nonnegativeTime (τ i.succ)) - ω (nonnegativeTime (τ i.castSucc)))
      (fun _ => (measurable_pi_apply _).sub (measurable_pi_apply _))
      (fun _ => (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _))
      (h := hB.hasIndepIncrements n _ hn)
    exact (map_finite_transform (hW (n+1) τ) (hP (n+1) τ) (hfinite (n+1) τ)
      (fun x (i : Fin n) => x i.succ - x i.castSucc) (by fun_prop)).symm
  · intro s t hst
    let τ : Fin 2 → Time T := ![s, t]
    have hm := map_finite_transform (hW 2 τ) (hP 2 τ) (hfinite 2 τ)
      (fun x => x 1 - x 0) (by fun_prop)
    refine ⟨((ContinuousMap.measurable_eval t).sub (ContinuousMap.measurable_eval s)).aemeasurable,
      hm.trans ?_⟩
    have hh := (hB.hasLaw_sub (nonnegativeTime t) (nonnegativeTime s)).map_eq
    have hv : nndist (t : ℝ) (s : ℝ) =
        Real.toNNReal ((t : ℝ) - (s : ℝ)) := by
      have hstR : (s : ℝ) ≤ (t : ℝ) := hst
      apply Subtype.ext
      change |(t : ℝ) - (s : ℝ)| = max ((t : ℝ) - (s : ℝ)) 0
      rw [abs_of_nonneg (sub_nonneg.mpr hstR), max_eq_left (sub_nonneg.mpr hstR)]
    change P.map (fun ω => ω (nonnegativeTime t) - ω (nonnegativeTime s)) =
      gaussianReal 0 (nndist (t : ℝ) (s : ℝ)) at hh
    simpa only [hv, τ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using hh

/-- The construction verifies consistency first, then the continuity moment
hypothesis, and only then pushes the continuous modification to path space. -/
theorem exists_wiener_measure (T : ℝ) (hT : 0 < T) :
    ∃ W : Measure C(Time T, ℝ), IsWienerMeasure T W := by
  obtain ⟨P, hP, hB⟩ := exists_preWiener
  let := hP
  let X : Time T → (ℝ≥0 → ℝ) → ℝ := fun t ω => ω (nonnegativeTime t)
  have hXm (t : Time T) : Measurable (X t) := measurable_pi_apply _
  obtain ⟨Y, hYm, hmod, hYc, _⟩ := kolmogorov_chentsov P T 4 1 gaussianFourthMoment
    hT (by norm_num) (by norm_num) X hXm (preWiener_moment_bound hB)
  let F := continuousProcessPath Y hYc
  have hFm : Measurable F := ContinuousMap.measurable_iff_eval.mpr hYm
  let W := P.map F
  have : IsProbabilityMeasure W :=
    (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance
  refine ⟨W, isWienerMeasure_of_finite_laws P hB W ?_⟩
  intro n τ
  rw [show W = P.map F from rfl,
    Measure.map_map (measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval (τ i)) hFm]
  apply Measure.map_congr
  have heq (i : Fin n) : ∀ᵐ ω ∂P, X (τ i) ω = Y (τ i) ω :=
    (mem_ae_iff_prob_eq_one (measurableSet_eq_fun (hXm _) (hYm _))).2 (hmod _)
  filter_upwards [ae_all_iff.mpr heq] with ω hω
  exact funext fun i => (hω i).symm

/-- Finite time laws uniquely determine a Borel probability on the exact
continuous-path space, with its uniform metric. -/
theorem wiener_measure_unique {T : ℝ} (hT : 0 < T)
    {W V : Measure C(Time T, ℝ)} (hW : IsWienerMeasure T W)
    (hV : IsWienerMeasure T V) : W = V := by
  classical
  let := hW.probability
  let := hV.probability
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Time T)
  have hh := continuousProcessLaw_unique T hT D hDc hDd W V
    (id : C(Time T, ℝ) → C(Time T, ℝ)) id measurable_id measurable_id
    (fun n τ => (hW.marginals n (fun i => (τ i).1)).trans
      (hV.marginals n (fun i => (τ i).1)).symm)
  simpa only [Measure.map_id] using hh

/-- Wiener existence and uniqueness, including singular finite marginals,
time zero, and repeated times in ordered lists of increments. -/
theorem exists_unique_wiener_measure :
    Specs.ProbabilityFoundations.Ch07.WienerMeasure.wienerMeasureType := by
  intro T hT
  obtain ⟨W, hW⟩ := exists_wiener_measure T hT
  exact ⟨W, hW, fun V hV => wiener_measure_unique hT hV hW⟩

end ProbabilityFoundations.Ch07
