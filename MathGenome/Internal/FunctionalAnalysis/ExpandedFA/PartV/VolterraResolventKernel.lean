import Specs.ExpandedFA.PartV.VolterraResolventKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraResolvent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV

/-- Banach-valued interchange over `c ≤ q ≤ r ≤ t`. The function is genuinely
integrable on the compact triangle; no scalar or finite-dimensional reduction
is imposed on its values. -/
lemma integral_triangle_swap {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (c t : ℝ) (hct : c ≤ t) (F : ℝ → ℝ → X)
    (hF : Continuous (Function.uncurry F)) :
    (∫ r in c..t, ∫ q in c..r, F r q) =
      ∫ q in c..t, ∫ r in q..t, F r q := by
  classical
  let T := volterraTriangle c t
  let G := T.indicator (Function.uncurry F)
  have hT : IsCompact T := isCompact_iff_compactSpace.mpr inferInstance
  have hi : Integrable G (volume.prod volume) :=
    (integrable_indicator_iff hT.measurableSet).mpr (hF.continuousOn.integrableOn_compact hT)
  have hleft : ∀ r : ℝ, (∫ q, G (r, q)) =
      (Icc c t).indicator (fun r => ∫ q in c..r, F r q) r := by
    intro r
    by_cases hr : r ∈ Icc c t
    · rw [Set.indicator_of_mem hr, intervalIntegral.integral_of_le hr.1,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator measurableSet_Icc]
      congr 1
      funext q
      simp only [G, T, volterraTriangle, Set.indicator, Set.mem_ofPred_eq, Function.uncurry_apply_pair,
        Set.mem_Icc, hr.2, and_true]
    · rw [Set.indicator_of_notMem hr]
      have hz : (fun q => G (r, q)) = 0 := by
        funext q
        apply Set.indicator_of_notMem
        intro h
        exact hr ⟨h.1.trans h.2.1, h.2.2⟩
      rw [hz]
      simp
  have hright : ∀ q : ℝ, (∫ r, G (r, q)) =
      (Icc c t).indicator (fun q => ∫ r in q..t, F r q) q := by
    intro q
    by_cases hq : q ∈ Icc c t
    · rw [Set.indicator_of_mem hq, intervalIntegral.integral_of_le hq.2,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← MeasureTheory.integral_indicator measurableSet_Icc]
      congr 1
      funext r
      simp only [G, T, volterraTriangle, Set.indicator, Set.mem_ofPred_eq, Function.uncurry_apply_pair,
        Set.mem_Icc, hq.1, true_and]
    · rw [Set.indicator_of_notMem hq]
      have hz : (fun r => G (r, q)) = 0 := by
        funext r
        apply Set.indicator_of_notMem
        intro h
        exact hq ⟨h.1, h.2.1.trans h.2.2⟩
      rw [hz]
      simp
  have hs := integral_integral_swap (f := fun r q => G (r, q)) hi
  simp_rw [hleft, hright] at hs
  simpa only [MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hct] using hs

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {a b : ℝ}
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : SMulCommClass ℝ 𝕜 E where
  smul_comm r c x := by
    change (algebraMap ℝ 𝕜 r) • (c • x) = c • ((algebraMap ℝ 𝕜 r) • x)
    simp only [smul_smul, mul_comm]

lemma kernelIntegrationPoint_eq (p : volterraTriangle a b) (r : ℝ)
    (hr : r ∈ Icc p.val.2 p.val.1) : kernelIntegrationPoint p r = r := by
  simp [kernelIntegrationPoint, min_eq_right hr.2, max_eq_right hr.1]

lemma continuous_kernelLeftPoint :
    Continuous (fun q : volterraTriangle a b × ℝ => kernelLeftPoint q.1 q.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_fst.comp continuous_subtype_val).comp continuous_fst).prodMk
    (((continuous_snd.comp continuous_subtype_val).comp continuous_fst).max
      (((continuous_fst.comp continuous_subtype_val).comp continuous_fst).min continuous_snd))

lemma continuous_kernelRightPoint :
    Continuous (fun q : volterraTriangle a b × ℝ => kernelRightPoint q.1 q.2) := by
  apply Continuous.subtype_mk
  exact (((continuous_snd.comp continuous_subtype_val).comp continuous_fst).max
      (((continuous_fst.comp continuous_subtype_val).comp continuous_fst).min continuous_snd)).prodMk
    ((continuous_snd.comp continuous_subtype_val).comp continuous_fst)

omit [CompleteSpace E] in
lemma continuous_kernelConvolution_integrand
    {h g : volterraTriangle a b → E →L[𝕜] E} (hh : Continuous h) (hg : Continuous g) :
    Continuous (fun q : volterraTriangle a b × ℝ =>
      (h (kernelLeftPoint q.1 q.2)).comp (g (kernelRightPoint q.1 q.2))) := by
  exact (hh.comp continuous_kernelLeftPoint).clm_comp (hg.comp continuous_kernelRightPoint)

omit [CompleteSpace E] in
lemma continuous_kernelConvolution
    {h g : volterraTriangle a b → E →L[𝕜] E} (hh : Continuous h) (hg : Continuous g) :
    Continuous (kernelConvolution h g) := by
  let f := fun (p : volterraTriangle a b) (r : ℝ) =>
    (h (kernelLeftPoint p r)).comp (g (kernelRightPoint p r))
  have hc : Continuous f.uncurry := continuous_kernelConvolution_integrand hh hg
  have ht := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := a) hc (continuous_fst.comp continuous_subtype_val)
  have hs := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := volume) (a₀ := a) hc (continuous_snd.comp continuous_subtype_val)
  convert ht.sub hs using 1
  funext p
  exact (intervalIntegral.integral_interval_sub_left
    ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)).symm

lemma integral_comp_left (A : E →L[𝕜] E) {f : ℝ → E →L[𝕜] E} {c t : ℝ}
    (hf : IntervalIntegrable f volume c t) :
    A.comp (∫ r in c..t, f r) = ∫ r in c..t, A.comp (f r) := by
  exact ((ContinuousLinearMap.compL 𝕜 E E E A).intervalIntegral_comp_comm hf).symm

lemma integral_comp_right (A : E →L[𝕜] E) {f : ℝ → E →L[𝕜] E} {c t : ℝ}
    (hf : IntervalIntegrable f volume c t) :
    (∫ r in c..t, f r).comp A = ∫ r in c..t, (f r).comp A := by
  exact (((ContinuousLinearMap.compL 𝕜 E E E).flip A).intervalIntegral_comp_comm hf).symm

/-- Associativity preserves the order of three possibly noncommuting kernels. -/
lemma kernelConvolution_assoc
    {h g j : volterraTriangle a b → E →L[𝕜] E}
    (hh : Continuous h) (hg : Continuous g) (hj : Continuous j)
    (p : volterraTriangle a b) :
    kernelConvolution h (kernelConvolution g j) p =
      kernelConvolution (kernelConvolution h g) j p := by
  let F := fun r q : ℝ => (h (kernelLeftPoint p r)).comp
    ((g (kernelLeftPoint (kernelRightPoint p r) q)).comp (j (kernelRightPoint p q)))
  have hc : Continuous (Function.uncurry F) := by
    have hl : Continuous (fun x : ℝ × ℝ => kernelLeftPoint p x.1) :=
      continuous_kernelLeftPoint.comp (continuous_const.prodMk continuous_fst)
    have hr : Continuous (fun x : ℝ × ℝ => kernelRightPoint p x.1) :=
      continuous_kernelRightPoint.comp (continuous_const.prodMk continuous_fst)
    have hq : Continuous (fun x : ℝ × ℝ => kernelRightPoint p x.2) :=
      continuous_kernelRightPoint.comp (continuous_const.prodMk continuous_snd)
    exact (hh.comp hl).clm_comp
      ((hg.comp (continuous_kernelLeftPoint.comp (hr.prodMk continuous_snd))).clm_comp (hj.comp hq))
  have hswap := integral_triangle_swap p.val.2 p.val.1 p.property.2.1 F hc
  calc
    kernelConvolution h (kernelConvolution g j) p =
        ∫ r in p.val.2..p.val.1, ∫ q in p.val.2..r, F r q := by
      unfold kernelConvolution
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le p.property.2.1] at hr
      have he := kernelIntegrationPoint_eq p r hr
      dsimp only
      have hi : IntervalIntegrable
          (fun q : ℝ => (g (kernelLeftPoint (kernelRightPoint p r) q)).comp
            (j (kernelRightPoint (kernelRightPoint p r) q))) volume
          (kernelRightPoint p r).val.2 (kernelRightPoint p r).val.1 :=
        ((continuous_kernelConvolution_integrand hg hj).comp
          ((continuous_const : Continuous (fun _ : ℝ => kernelRightPoint p r)).prodMk continuous_id)).intervalIntegrable _ _
      rw [integral_comp_left (h (kernelLeftPoint p r)) hi]
      simp only [kernelRightPoint, he]
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hr.1] at hq
      simp [F, kernelLeftPoint, kernelRightPoint, kernelIntegrationPoint,
        min_eq_right hr.2, max_eq_right hr.1, min_eq_right hq.2,
        max_eq_right hq.1, min_eq_right (hq.2.trans hr.2)]
    _ = ∫ q in p.val.2..p.val.1, ∫ r in q..p.val.1, F r q := hswap
    _ = kernelConvolution (kernelConvolution h g) j p := by
      unfold kernelConvolution
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le p.property.2.1] at hq
      have he := kernelIntegrationPoint_eq p q hq
      dsimp only
      have hi : IntervalIntegrable
          (fun r : ℝ => (h (kernelLeftPoint (kernelLeftPoint p q) r)).comp
            (g (kernelRightPoint (kernelLeftPoint p q) r))) volume
          (kernelLeftPoint p q).val.2 (kernelLeftPoint p q).val.1 :=
        ((continuous_kernelConvolution_integrand hh hg).comp
          ((continuous_const : Continuous (fun _ : ℝ => kernelLeftPoint p q)).prodMk continuous_id)).intervalIntegrable _ _
      rw [integral_comp_right (j (kernelRightPoint p q)) hi]
      simp only [kernelLeftPoint, he]
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hq.2] at hr
      simp [F, kernelLeftPoint, kernelRightPoint, kernelIntegrationPoint,
        min_eq_right hq.2, max_eq_right hq.1, min_eq_right hr.2,
        max_eq_right (hq.1.trans hr.1), min_eq_right hr.1, max_eq_right hr.1,
        ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] in
lemma continuous_iteratedVolterraKernel (k : C(volterraTriangle a b, E →L[𝕜] E))
    (n : ℕ) : Continuous (iteratedVolterraKernel k n) := by
  induction n with
  | zero => exact k.continuous
  | succ n ih => exact continuous_kernelConvolution k.continuous ih

omit [CompleteSpace E] in
lemma norm_iteratedVolterraKernel (k : C(volterraTriangle a b, E →L[𝕜] E))
    (n : ℕ) (p : volterraTriangle a b) :
    ‖iteratedVolterraKernel k n p‖ ≤
      ‖k‖ ^ (n + 1) * (p.val.1 - p.val.2) ^ n / (n.factorial : ℝ) := by
  induction n generalizing p with
  | zero => simpa [iteratedVolterraKernel] using k.norm_coe_le_norm p
  | succ n ih =>
    change ‖∫ r in p.val.2..p.val.1,
      (k (kernelLeftPoint p r)).comp (iteratedVolterraKernel k n (kernelRightPoint p r))‖ ≤ _
    calc
      _ ≤ ∫ r in p.val.2..p.val.1,
          ‖k‖ * (‖k‖ ^ (n + 1) * (r - p.val.2) ^ n / (n.factorial : ℝ)) := by
        apply intervalIntegral.norm_integral_le_of_norm_le p.property.2.1
        · apply Eventually.of_forall
          intro r hr
          have he := kernelIntegrationPoint_eq p r ⟨hr.1.le, hr.2⟩
          have hb := (ContinuousLinearMap.opNorm_comp_le (k (kernelLeftPoint p r))
            (iteratedVolterraKernel k n (kernelRightPoint p r))).trans
            (mul_le_mul (k.norm_coe_le_norm (kernelLeftPoint p r)) (ih (kernelRightPoint p r))
              (norm_nonneg _) (norm_nonneg k))
          simpa only [kernelRightPoint, he] using hb
        · exact (by fun_prop : Continuous (fun r : ℝ =>
            ‖k‖ * (‖k‖ ^ (n + 1) * (r - p.val.2) ^ n / (n.factorial : ℝ)))).intervalIntegrable _ _
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
          intervalIntegral.integral_const_mul, integral_sub_pow]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          pow_succ, div_eq_mul_inv, mul_inv_rev]
        ring

omit [CompleteSpace E] in
/-- The scalar exponential majorant is independent of the triangle point. -/
lemma norm_scaled_iteratedVolterraKernel (_hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜) (n : ℕ)
    (p : volterraTriangle a b) :
    ‖lam ^ n • iteratedVolterraKernel k n p‖ ≤
      ‖k‖ * ((‖lam‖ * ‖k‖ * (b - a)) ^ n / (n.factorial : ℝ)) := by
  rw [norm_smul, norm_pow]
  calc
    _ ≤ ‖lam‖ ^ n * (‖k‖ ^ (n + 1) * (p.val.1 - p.val.2) ^ n / (n.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (norm_iteratedVolterraKernel k n p) (by positivity)
    _ ≤ ‖lam‖ ^ n * (‖k‖ ^ (n + 1) * (b - a) ^ n / (n.factorial : ℝ)) := by
      gcongr
      · exact sub_nonneg.mpr p.property.2.1
      · exact p.property.2.2
      · exact p.property.1
    _ = _ := by simp only [mul_pow, pow_succ]; ring

lemma volterra_kernel_series (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜) :
    Continuous (volterraReducedResolventKernel k lam) ∧
    (∀ p, Summable (fun n : ℕ => ‖lam ^ n • iteratedVolterraKernel k n p‖) ∧
      HasSum (fun n : ℕ => lam ^ n • iteratedVolterraKernel k n p)
        (volterraReducedResolventKernel k lam p)) ∧
    TendstoUniformly
      (fun N p => ∑ n ∈ Finset.range N, lam ^ n • iteratedVolterraKernel k n p)
      (volterraReducedResolventKernel k lam) atTop := by
  have hsum := (Real.summable_pow_div_factorial (‖lam‖ * ‖k‖ * (b - a))).mul_left ‖k‖
  have hb := norm_scaled_iteratedVolterraKernel hab k lam
  refine ⟨?_, ?_, tendstoUniformly_tsum_nat hsum hb⟩
  · exact continuous_tsum (fun n => (continuous_iteratedVolterraKernel k n).const_smul (lam ^ n)) hsum hb
  · intro p
    have hn := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb n p)
    exact ⟨hn, hn.of_norm.hasSum⟩

/-- Composition of Volterra operators is integration against the ordered kernel
convolution. This is the action-valued triangular interchange. -/
lemma volterra_operator_composition (hab : a ≤ b)
    (h g : C(volterraTriangle a b, E →L[𝕜] E))
    (f : C(VolterraInterval a b, E)) (t : VolterraInterval a b) :
    let H : C(volterraTriangle a b, E →L[𝕜] E) :=
      ⟨kernelConvolution h g, continuous_kernelConvolution h.continuous g.continuous⟩
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab h
      (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab g f) t =
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab H f t := by
  dsimp only
  let p : volterraTriangle a b := ⟨((t : ℝ), a), le_rfl, t.property.1, t.property.2⟩
  let F := fun r q : ℝ => (h (kernelLeftPoint p r))
    ((g (kernelLeftPoint (kernelRightPoint p r) q)) (f (Set.projIcc a b hab q)))
  have hc : Continuous (Function.uncurry F) := by
    have hl : Continuous (fun x : ℝ × ℝ => kernelLeftPoint p x.1) :=
      continuous_kernelLeftPoint.comp (continuous_const.prodMk continuous_fst)
    have hr : Continuous (fun x : ℝ × ℝ => kernelRightPoint p x.1) :=
      continuous_kernelRightPoint.comp (continuous_const.prodMk continuous_fst)
    exact (h.continuous.comp hl).clm_apply
      ((g.continuous.comp (continuous_kernelLeftPoint.comp (hr.prodMk continuous_snd))).clm_apply
        (f.continuous.comp (continuous_projIcc.comp continuous_snd)))
  have hswap := integral_triangle_swap a (t : ℝ) t.property.1 F hc
  rw [volterra_apply_integral, volterra_apply_integral]
  change (∫ r in a..(t : ℝ), volterraIntegrand hab h
    (VolterraOperatorSpec.OperatorValue 𝕜 E a b hab g f) t r) =
      ∫ q in a..(t : ℝ), (kernelConvolution h g (volterraRetraction t q))
        (f (Set.projIcc a b hab q))
  calc
    _ = ∫ r in a..(t : ℝ), ∫ q in a..r, F r q := by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le t.property.1] at hr
      rw [volterraIntegrand_eq hab h _ t r hr, volterra_apply_integral]
      unfold volterraIntegralValue
      dsimp only
      have hi : IntervalIntegrable
          (volterraIntegrand hab g f (⟨r, hr.1, hr.2.trans t.property.2⟩ : VolterraInterval a b)) volume a r :=
        ((continuous_volterraIntegrand hab g f).comp
          ((continuous_const : Continuous (fun _ : ℝ => (⟨r, hr.1, hr.2.trans t.property.2⟩ : VolterraInterval a b))).prodMk
            continuous_id)).intervalIntegrable a r
      rw [← (h ⟨((t : ℝ), r), hr.1, hr.2, t.property.2⟩).intervalIntegral_comp_comm hi]
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le hr.1] at hq
      dsimp only
      rw [volterraIntegrand_eq hab g f _ q hq]
      simp [F, p, kernelLeftPoint, kernelRightPoint, kernelIntegrationPoint,
        min_eq_right hr.2, max_eq_right hr.1, min_eq_right hq.2,
        max_eq_right hq.1, Set.projIcc_of_mem hab ⟨hq.1, hq.2.trans (hr.2.trans t.property.2)⟩]
    _ = ∫ q in a..(t : ℝ), ∫ r in q..(t : ℝ), F r q := hswap
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le t.property.1] at hq
      have hret : volterraRetraction t q = kernelLeftPoint p q := by
        apply Subtype.ext
        rfl
      dsimp only
      rw [hret]
      unfold kernelConvolution
      have hi : IntervalIntegrable
          (fun r : ℝ => (h (kernelLeftPoint (kernelLeftPoint p q) r)).comp
            (g (kernelRightPoint (kernelLeftPoint p q) r))) volume
          (kernelLeftPoint p q).val.2 (kernelLeftPoint p q).val.1 :=
        ((continuous_kernelConvolution_integrand h.continuous g.continuous).comp
          ((continuous_const : Continuous (fun _ : ℝ => kernelLeftPoint p q)).prodMk continuous_id)).intervalIntegrable _ _
      rw [ContinuousLinearMap.intervalIntegral_apply hi]
      simp only [kernelLeftPoint, p, kernelIntegrationPoint, min_eq_right hq.2, max_eq_right hq.1]
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le hq.2] at hr
      simp [F, p, kernelLeftPoint, kernelRightPoint, kernelIntegrationPoint,
        max_eq_right hq.1, min_eq_right hr.2,
        max_eq_right (hq.1.trans hr.1), min_eq_right hr.1, max_eq_right hr.1,
        ContinuousLinearMap.comp_apply]

lemma iteratedVolterraKernel_convolution_right
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (n : ℕ) (p : volterraTriangle a b) :
    kernelConvolution (iteratedVolterraKernel k n) k p = iteratedVolterraKernel k (n + 1) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    change kernelConvolution (kernelConvolution k (iteratedVolterraKernel k n)) k p = _
    rw [← kernelConvolution_assoc k.continuous (continuous_iteratedVolterraKernel k n) k.continuous]
    rw [show kernelConvolution (iteratedVolterraKernel k n) k = iteratedVolterraKernel k (n + 1) from funext ih]
    rfl

omit [CompleteSpace E] in
lemma kernelConvolution_smul_right (h g : volterraTriangle a b → E →L[𝕜] E)
    (c : 𝕜) (p : volterraTriangle a b) :
    kernelConvolution h (fun p => c • g p) p = c • kernelConvolution h g p := by
  simp only [kernelConvolution, ContinuousLinearMap.comp_smul, intervalIntegral.integral_smul]

omit [CompleteSpace E] in
lemma kernelConvolution_smul_left (h g : volterraTriangle a b → E →L[𝕜] E)
    (c : 𝕜) (p : volterraTriangle a b) :
    kernelConvolution (fun p => c • h p) g p = c • kernelConvolution h g p := by
  simp only [kernelConvolution, ContinuousLinearMap.smul_comp, intervalIntegral.integral_smul]

omit [CompleteSpace E] in
/-- Summable uniform bounds justify integrating a series on either side of a
fixed continuous kernel. -/
lemma hasSum_kernelConvolution
    (h : C(volterraTriangle a b, E →L[𝕜] E))
    (f : ℕ → volterraTriangle a b → E →L[𝕜] E)
    (R : volterraTriangle a b → E →L[𝕜] E)
    (hf : ∀ n, Continuous (f n)) (u : ℕ → ℝ) (hu : Summable u)
    (hb : ∀ n p, ‖f n p‖ ≤ u n) (hs : ∀ p, HasSum (fun n => f n p) (R p))
    (p : volterraTriangle a b) :
    HasSum (fun n => kernelConvolution h (f n) p) (kernelConvolution h R p) ∧
    HasSum (fun n => kernelConvolution (f n) h p) (kernelConvolution R h p) := by
  constructor
  · apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖h‖ * u n)
    · intro n
      exact ((continuous_kernelConvolution_integrand h.continuous (hf n)).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro n
      apply Eventually.of_forall
      intro r _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (h.norm_coe_le_norm _) (hb n _) (norm_nonneg _) (norm_nonneg h))
    · exact Eventually.of_forall (fun _ _ => hu.mul_left ‖h‖)
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro r _
      exact (hs (kernelRightPoint p r)).mapL
        (ContinuousLinearMap.compL 𝕜 E E E (h (kernelLeftPoint p r)))
  · apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => u n * ‖h‖)
    · intro n
      exact ((continuous_kernelConvolution_integrand (hf n) h.continuous).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro n
      apply Eventually.of_forall
      intro r _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hb n _) (h.norm_coe_le_norm _) (norm_nonneg _) (by
          exact (norm_nonneg (f n (kernelLeftPoint p r))).trans (hb n _)))
    · exact Eventually.of_forall (fun _ _ => hu.mul_right ‖h‖)
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro r _
      exact (hs (kernelLeftPoint p r)).mapL
        ((ContinuousLinearMap.compL 𝕜 E E E).flip (h (kernelRightPoint p r)))

lemma volterra_resolvent_kernel_identities (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜) :
    (∀ p, volterraReducedResolventKernel k lam p =
      k p + lam • kernelConvolution k (volterraReducedResolventKernel k lam) p) ∧
    (∀ p, volterraReducedResolventKernel k lam p =
      k p + lam • kernelConvolution (volterraReducedResolventKernel k lam) k p) := by
  let f := fun n p => lam ^ n • iteratedVolterraKernel k n p
  let u := fun n : ℕ => ‖k‖ * ((‖lam‖ * ‖k‖ * (b - a)) ^ n / (n.factorial : ℝ))
  have hu : Summable u := (Real.summable_pow_div_factorial _).mul_left _
  have hf : ∀ n, Continuous (f n) := fun n => (continuous_iteratedVolterraKernel k n).const_smul (lam ^ n)
  have hs := (volterra_kernel_series hab k lam).2.1
  have hc (p : volterraTriangle a b) := hasSum_kernelConvolution k f (volterraReducedResolventKernel k lam)
    hf u hu (norm_scaled_iteratedVolterraKernel hab k lam) (fun p => (hs p).2) p
  have hshift (p : volterraTriangle a b) :
      HasSum (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k (n + 1) p)
        (volterraReducedResolventKernel k lam p - k p) := by
    simpa [f, iteratedVolterraKernel] using ((hasSum_nat_add_iff' 1).mpr (hs p).2)
  constructor
  · intro p
    have hc' := (hc p).1.const_smul lam
    have he : (fun n : ℕ => lam • kernelConvolution k (f n) p) =
        (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k (n + 1) p) := by
      funext n
      simp only [f, kernelConvolution_smul_right, smul_smul, pow_succ', iteratedVolterraKernel]
    rw [he] at hc'
    have heq := (hshift p).unique hc'
    exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)
  · intro p
    have hc' := (hc p).2.const_smul lam
    have he : (fun n : ℕ => lam • kernelConvolution (f n) k p) =
        (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k (n + 1) p) := by
      funext n
      simp only [f, kernelConvolution_smul_left, iteratedVolterraKernel_convolution_right,
        smul_smul, pow_succ']
    rw [he] at hc'
    have heq := (hshift p).unique hc'
    exact (sub_eq_iff_eq_add.mp heq).trans (add_comm _ _)

lemma volterra_operator_add_kernel (hab : a ≤ b)
    (h g : C(volterraTriangle a b, E →L[𝕜] E)) :
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (h + g) =
      VolterraOperatorSpec.OperatorValue 𝕜 E a b hab h +
      VolterraOperatorSpec.OperatorValue 𝕜 E a b hab g := by
  ext f t
  simp only [add_apply, ContinuousMap.add_apply]
  rw [volterra_apply_integral, volterra_apply_integral, volterra_apply_integral]
  unfold volterraIntegralValue
  simp only [volterraIntegrand, ContinuousMap.add_apply, add_apply]
  apply intervalIntegral.integral_add
  · exact ((continuous_volterraIntegrand hab h f).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact ((continuous_volterraIntegrand hab g f).comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

lemma volterra_operator_smul_kernel (hab : a ≤ b) (c : 𝕜)
    (h : C(volterraTriangle a b, E →L[𝕜] E)) :
    VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (c • h) =
      c • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab h := by
  ext f t
  simp only [smul_apply, ContinuousMap.smul_apply]
  rw [volterra_apply_integral, volterra_apply_integral]
  simp only [volterraIntegralValue, volterraIntegrand, ContinuousMap.smul_apply,
    smul_apply, intervalIntegral.integral_smul]

lemma volterra_solution_kernel_formula (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜)
    (f u : C(VolterraInterval a b, E))
    (hu : u - lam • VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k u = f)
    (t : VolterraInterval a b) :
    u t = f t + lam • ∫ s in a..(t : ℝ),
      volterraReducedResolventKernel k lam (volterraRetraction t s) (f (Set.projIcc a b hab s)) := by
  let R : C(volterraTriangle a b, E →L[𝕜] E) :=
    ⟨volterraReducedResolventKernel k lam, (volterra_kernel_series hab k lam).1⟩
  let H : C(volterraTriangle a b, E →L[𝕜] E) :=
    ⟨kernelConvolution R k, continuous_kernelConvolution R.continuous k.continuous⟩
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let W := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab R
  have hR : R = k + lam • H := by
    apply ContinuousMap.ext
    intro p
    exact (volterra_resolvent_kernel_identities hab k lam).2 p
  have hcomp : VolterraOperatorSpec.OperatorValue 𝕜 E a b hab H = W * V := by
    ext v x
    exact (volterra_operator_composition hab R k v x).symm
  have hw : W = V + lam • (W * V) := by
    change VolterraOperatorSpec.OperatorValue 𝕜 E a b hab R = _
    rw [hR, volterra_operator_add_kernel, volterra_operator_smul_kernel, hcomp]
  have hwf : W f = V u := by
    rw [← hu, map_sub, map_smul]
    have he : W u = V u + lam • W (V u) := by
      conv_lhs => rw [hw]
      rfl
    rw [he]
    abel
  have hf : u = f + lam • W f := by
    rw [hwf]
    exact sub_eq_iff_eq_add.mp hu
  have ht := congrArg (fun v : C(VolterraInterval a b, E) => v t) hf
  simpa only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
    W, volterra_apply_integral, volterraIntegralValue, volterraIntegrand, R, ContinuousMap.coe_mk] using ht

end

theorem volterra_kernel_recursion : ResolventKernelSpec.Recursion := by
  intro 𝕜 E _ _ _ _ a b hab k
  refine ⟨fun _ => rfl, fun _ _ => rfl, ?_⟩
  intro p r hr
  constructor <;> apply Subtype.ext <;>
    simp [kernelLeftPoint, kernelRightPoint, kernelIntegrationPoint_eq p r hr]

theorem volterra_kernel_regularity_estimate : ResolventKernelSpec.RegularityEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k n
  exact ⟨continuous_iteratedVolterraKernel k n, norm_iteratedVolterraKernel k n⟩

theorem volterra_reduced_kernel_uniform_series : ResolventKernelSpec.ReducedUniformSeries := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  exact volterra_kernel_series hab k lam

theorem volterra_reduced_kernel_identities : ResolventKernelSpec.ReducedKernelIdentities := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  exact volterra_resolvent_kernel_identities hab k lam

theorem volterra_kernel_solution_representation : ResolventKernelSpec.SolutionRepresentation := by
  intro 𝕜 E _ _ _ _ a b hab k lam f u hu t
  exact volterra_solution_kernel_formula hab k lam f u hu t

section
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] {a b : ℝ}
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
local instance : SMulCommClass ℝ 𝕜 E where
  smul_comm r c x := by
    change (algebraMap ℝ 𝕜 r) • (c • x) = c • ((algebraMap ℝ 𝕜 r) • x)
    simp only [smul_smul, mul_comm]

/-- Passing from the reduced kernel to the kernel of the inverse minus I. -/
lemma volterraResolventKernel_eq_smul (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜)
    (p : volterraTriangle a b) :
    volterraResolventKernel k lam p = lam • volterraReducedResolventKernel k lam p := by
  have hs := ((volterra_kernel_series hab k lam).2.1 p).2.const_smul lam
  have ht : HasSum (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k n p)
      (lam • volterraReducedResolventKernel k lam p) := by
    simpa only [smul_smul, pow_succ'] using hs
  exact ht.tsum_eq

lemma volterra_full_kernel_series (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜) :
    Continuous (volterraResolventKernel k lam) ∧
    (∀ p, Summable (fun n : ℕ => ‖lam ^ (n + 1) • iteratedVolterraKernel k n p‖) ∧
      HasSum (fun n : ℕ => lam ^ (n + 1) • iteratedVolterraKernel k n p)
        (volterraResolventKernel k lam p)) ∧
    TendstoUniformly
      (fun N p => ∑ n ∈ Finset.range N, lam ^ (n + 1) • iteratedVolterraKernel k n p)
      (volterraResolventKernel k lam) atTop := by
  let u := fun n : ℕ => ‖lam‖ * (‖k‖ *
    ((‖lam‖ * ‖k‖ * (b - a)) ^ n / (n.factorial : ℝ)))
  have hu : Summable u := ((Real.summable_pow_div_factorial _).mul_left ‖k‖).mul_left ‖lam‖
  have hb (n : ℕ) (p : volterraTriangle a b) :
      ‖lam ^ (n + 1) • iteratedVolterraKernel k n p‖ ≤ u n := by
    rw [pow_succ', mul_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_scaled_iteratedVolterraKernel hab k lam n p)
      (norm_nonneg lam)
  refine ⟨?_, ?_, tendstoUniformly_tsum_nat hu hb⟩
  · exact continuous_tsum
      (fun n => (continuous_iteratedVolterraKernel k n).const_smul (lam ^ (n + 1))) hu hb
  · intro p
    have hn := hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hb n p)
    exact ⟨hn, hn.of_norm.hasSum⟩

lemma volterra_full_kernel_identities (hab : a ≤ b)
    (k : C(volterraTriangle a b, E →L[𝕜] E)) (lam : 𝕜) :
    (∀ p, volterraResolventKernel k lam p =
      lam • k p + lam • kernelConvolution k (volterraResolventKernel k lam) p) ∧
    (∀ p, volterraResolventKernel k lam p =
      lam • k p + lam • kernelConvolution (volterraResolventKernel k lam) k p) := by
  have he : volterraResolventKernel k lam =
      fun p => lam • volterraReducedResolventKernel k lam p :=
    funext (volterraResolventKernel_eq_smul hab k lam)
  obtain ⟨hl, hr⟩ := volterra_resolvent_kernel_identities hab k lam
  constructor
  · intro p
    rw [he, kernelConvolution_smul_right]
    exact (congrArg (fun A => lam • A) (hl p)).trans (smul_add _ _ _)
  · intro p
    rw [he, kernelConvolution_smul_left]
    exact (congrArg (fun A => lam • A) (hr p)).trans (smul_add _ _ _)

end

theorem volterra_kernel_uniform_estimate : ResolventKernelSpec.UniformKernelEstimate := by
  intro 𝕜 E _ _ _ _ a b hab k M hM n p
  have hM0 : 0 ≤ M := (norm_nonneg (k ⟨(a,a), le_rfl, le_rfl, hab⟩)).trans
    (hM ⟨(a,a), le_rfl, le_rfl, hab⟩)
  have hk : ‖k‖ ≤ M := (ContinuousMap.norm_le k hM0).mpr hM
  apply (norm_iteratedVolterraKernel k n p).trans
  gcongr
  · exact pow_nonneg (sub_nonneg.mpr p.property.2.1) _

theorem volterra_kernel_uniform_series : ResolventKernelSpec.UniformSeries := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  exact volterra_full_kernel_series hab k lam

theorem volterra_kernel_identities : ResolventKernelSpec.KernelIdentities := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  exact volterra_full_kernel_identities hab k lam

theorem volterra_kernel_inverse_representation : ResolventKernelSpec.InverseRepresentation := by
  intro 𝕜 E _ _ _ _ a b hab k lam
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let S := Ring.inverse (1 - lam • V)
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  dsimp only
  intro f t
  have hinv : (1 - lam • V) * S = 1 :=
    Ring.mul_inverse_cancel _ (volterra_inverse_series 𝕜 E a b hab k lam).1
  have hu : S f - lam • V (S f) = f := by
    have h := congrArg (fun A : C(VolterraInterval a b, E) →L[𝕜]
      C(VolterraInterval a b, E) => A f) hinv
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, smul_apply] using h
  have ht := volterra_solution_kernel_formula hab k lam f (S f) hu t
  change (S f) t - f t = _
  rw [ht, add_sub_cancel_left]
  rw [← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s hs
  dsimp only
  rw [volterraResolventKernel_eq_smul hab k lam]
  rfl

theorem volterra_kernel_iterate_representation : ResolventKernelSpec.IterateRepresentation := by
  intro 𝕜 E _ _ _ _ a b hab k n
  let V := VolterraOperatorSpec.OperatorValue 𝕜 E a b hab k
  let K : ℕ → C(volterraTriangle a b, E →L[𝕜] E) :=
    fun n => ⟨iteratedVolterraKernel k n, continuous_iteratedVolterraKernel k n⟩
  have hp (n : ℕ) : V ^ (n + 1) = VolterraOperatorSpec.OperatorValue 𝕜 E a b hab (K n) := by
    induction n with
    | zero =>
      have h0 : K 0 = k := ContinuousMap.ext (fun _ => rfl)
      simp only [Nat.zero_add, pow_one, h0]
      rfl
    | succ n ih =>
      rw [pow_succ', ih]
      ext f t
      exact volterra_operator_composition hab k (K n) f t
  dsimp only
  intro f t
  change ((V ^ (n + 1)) f) t = _
  rw [hp n, volterra_apply_integral hab (K n)]
  rfl

end ExpandedFA.PartV
