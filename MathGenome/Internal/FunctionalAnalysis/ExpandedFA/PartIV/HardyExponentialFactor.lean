import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyExponentialFactor
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyCayley
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyFactorization
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology Real ENNReal
namespace ExpandedFA.PartIV.HardyExponentialFactor
open HardyDiskSpec HardyLogModulus HardyFactorization HardyCayleySpec

lemma inverseWeight_eval (w : ℂ) (hw : w ∈ disk) :
    eval cayleyInverseWeight w = 1 - w := by
  have hn : eval (-(lp.single 2 1 (1 : ℂ) : H2)) w =
      -eval (lp.single 2 1 (1 : ℂ) : H2) w := by
    simpa using HardyDisk.evaluation_smul (-1) (lp.single 2 1 (1 : ℂ) : H2) w
  calc
    eval cayleyInverseWeight w =
        eval (lp.single 2 0 (1 : ℂ) : H2) w + eval (-(lp.single 2 1 (1 : ℂ) : H2)) w := by
      exact HardyDisk.evaluation_add (lp.single 2 0 (1 : ℂ) : H2)
        (-(lp.single 2 1 (1 : ℂ) : H2)) w hw
    _ = 1 - w := by
      rw [hn, HardyDisk.monomial_evaluation, HardyDisk.monomial_evaluation]
      simp [sub_eq_add_neg]

lemma herglotz_add (μ ν : Measure _root_.Circle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {w : ℂ} (hw : w ∈ disk) :
    Herglotz.herglotzTransform (μ + ν) 0 w =
      Herglotz.herglotzTransform μ 0 w + Herglotz.herglotzTransform ν 0 w := by
  simp only [Herglotz.herglotzTransform, ofReal_zero, mul_zero, zero_add]
  have hk (ρ : Measure _root_.Circle) [IsFiniteMeasure ρ] :
      Integrable (fun ζ : _root_.Circle => ((ζ : ℂ) + w) / ((ζ : ℂ) - w)) ρ := by
    apply (PositiveHarmonic.integrable_circleHerglotzKernel ρ
      (disk_eq_unitDisk ▸ hw)).congr
    filter_upwards with ζ
    simp [PositiveHarmonic.circleHerglotzKernel, herglotzRieszKernel]
  exact integral_add_measure (hk μ) (hk ν)

lemma singularFactor_add (μ ν : Measure _root_.Circle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c : ℂ) {w : ℂ} (hw : w ∈ disk) :
    singularFactor (μ + ν) c w = singularFactor μ 1 w * singularFactor ν c w := by
  rw [singularFactor, herglotz_add μ ν hw, neg_add, Complex.exp_add]
  simp only [singularFactor, one_mul]
  ring

theorem atom_factor : Spec.AtomFactor := by
  intro a ha w hw
  simp only [singularFactor, Herglotz.herglotzTransform, ofReal_zero, mul_zero,
    zero_add, one_mul, integral_smul_measure, integral_dirac, Circle.coe_one]
  rw [ENNReal.toReal_ofReal ha]
  congr 1
  simp only [cayley]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem disk_product : Spec.DiskProduct := by
  intro F G w hw
  dsimp [transform]
  field_simp [HardyCayley.one_sub_ne_zero hw, HardyCayley.normalization_ne_zero]

lemma atom_decomposition (μ : Measure _root_.Circle) [IsFiniteMeasure μ] :
    μ = ENNReal.ofReal (atomMass μ) • Measure.dirac (1 : _root_.Circle) + atomRemainder μ := by
  have h := μ.restrict_add_restrict_compl (measurableSet_singleton (1 : _root_.Circle))
  rw [Measure.restrict_singleton] at h
  simpa [atomRemainder, atomMass, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    using h.symm

theorem atom_removal : Spec.AtomRemoval := by
  intro μ hμ
  let := hμ.1
  let : IsFiniteMeasure (atomRemainder μ) := by
    unfold atomRemainder
    infer_instance
  let : IsFiniteMeasure (ENNReal.ofReal (atomMass μ) • Measure.dirac (1 : _root_.Circle)) :=
    isFiniteMeasure_of_le μ (by
      rw [atomMass, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _),
        ← Measure.restrict_singleton]
      exact Measure.restrict_le_self)
  have hrem : SingularMeasure (atomRemainder μ) :=
    ⟨inferInstance, hμ.2.mono (Measure.restrict_le_self) le_rfl⟩
  have hzero : atomRemainder μ {1} = 0 := by
    simp [atomRemainder, Measure.restrict_apply]
  refine ⟨measureReal_nonneg, hrem, hzero, atom_decomposition μ, ?_⟩
  intro c w hw
  have he := congrArg (fun ν => singularFactor ν c w) (atom_decomposition μ)
  rw [singularFactor_add _ _ c hw, atom_factor (atomMass μ) measureReal_nonneg w hw] at he
  exact he

lemma inverseWeight_nonzero : cayleyInverseWeight ≠ 0 := by
  intro h
  have hv := inverseWeight_eval 0 HardyInnerOuter.zero_mem_disk
  rw [h] at hv
  simp [HardyDiskSpec.eval] at hv

lemma shift_inverseWeight (n : ℕ) :
    (shift^[n]) cayleyInverseWeight = lp.single 2 n 1 - lp.single 2 (n + 1) 1 := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [Function.iterate_succ_apply', hn, map_sub]
    congr 1 <;> apply lp.ext <;> funext k <;> cases k <;>
      simp [HardyDisk.shift_zero, HardyDisk.shift_succ, lp.single_apply, Pi.single_apply,
        eq_comm]

lemma inverseWeight_outer : IsOuter cayleyInverseWeight := by
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  have hs (n : ℕ) : f n = f (n + 1) := by
    have h : inner ℂ ((shift^[n]) cayleyInverseWeight) f = 0 :=
      hf _ (Submodule.subset_span ⟨n, rfl⟩)
    rw [shift_inverseWeight, inner_sub_left, lp.inner_single_left, lp.inner_single_left] at h
    simpa [RCLike.inner_apply] using sub_eq_zero.mp h
  have hc (n : ℕ) : f n = f 0 := by
    induction n with
    | zero => rfl
    | succ n hn => exact (hs n).symm.trans hn
  have hsum := (HardyDisk.coefficient_norm f).summable
  simp only [hc, summable_const_iff] at hsum
  have h0 : f 0 = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsum)
  apply lp.ext
  funext n
  simpa [hc n] using h0

lemma inverseWeight_formula : ∃ c : ℂ, ‖c‖ = 1 ∧
    Set.EqOn (eval cayleyInverseWeight)
      (exponentialFactor (boundaryLog cayleyInverseWeight) c) disk := by
  let e : H2 := lp.single 2 0 1
  have he : IsInner e := by
    refine ⟨⟨1, fun w hw => ?_⟩, ?_⟩
    · change ‖eval (lp.single 2 0 1) w‖ ≤ 1
      rw [HardyDisk.monomial_evaluation]
      simp
    · exact (BlaschkeProducts.inner_of_bound_and_norm
        (fun w hw => by
          change ‖eval (lp.single 2 0 1) w‖ ≤ 1
          rw [HardyDisk.monomial_evaluation]
          simp)
        (by simp [e, lp.norm_single])).2
  exact HardyInnerOuter.outer_formula cayleyInverseWeight e cayleyInverseWeight
    inverseWeight_nonzero he inverseWeight_outer (by
      intro w hw
      change eval cayleyInverseWeight w = eval (lp.single 2 0 1) w * _
      rw [HardyDisk.monomial_evaluation]
      simp)


theorem prefactor : Spec.Prefactor := by
  have hi := (boundary_log_integrable cayleyInverseWeight inverseWeight_nonzero).1
  refine ⟨inverseWeight_eval, inverseWeight_outer, hi, ?_⟩
  intro w hw
  obtain ⟨c, hc, he⟩ := inverseWeight_formula
  have hn := exponential_norm _ hi c hc w hw
  rw [← he hw, inverseWeight_eval w hw] at hn
  rw [norm_inv, Real.log_inv, hn, Real.log_exp]
  unfold poissonLog
  simp only [mul_neg, integral_neg]

lemma singular_measure_exists (g : H2) (hg : g ≠ 0) :
    ∃ μ : Measure _root_.Circle, HasSingularMeasure g μ := by
  obtain ⟨i, o, hi, ho, he, _⟩ := HardyFactorization.factorization g hg 1 (by simp)
  obtain ⟨μ, c, hμ, hc, hm⟩ := HardyFactorization.inner_representation i hi
  exact ⟨μ, i, o, c, hi, ho, hμ, hc, he, hm⟩

theorem coefficient_existence : Spec.CoefficientExistence := by
  intro F hF hne
  obtain ⟨g, he, _⟩ := (HardyCayley.correspondence F).mp hF
  have hg : g ≠ 0 := by
    intro hg
    obtain ⟨z, hz, hn⟩ := hne
    have hv := HardyCayley.inverse_transform he hz
    rw [hg] at hv
    apply hn
    rw [← hv]
    simp [inverseTransform, HardyDiskSpec.eval]
  obtain ⟨μ, hμ⟩ := singular_measure_exists g hg
  exact ⟨atomMass μ, measureReal_nonneg, g, he, μ, hμ, rfl⟩


lemma constant_one_inner : IsInner (lp.single 2 0 (1 : ℂ)) := by
  apply BlaschkeProducts.inner_of_bound_and_norm
  · intro w hw
    rw [HardyDisk.monomial_evaluation]
    simp
  · simp [lp.norm_single]

lemma outer_nonzero {o : H2} (ho : IsOuter o) : o ≠ 0 := by
  intro he
  subst o
  have hz (n : ℕ) : (shift^[n]) (0 : H2) = 0 := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply', hn, map_zero]
  have hbot : (Submodule.span ℂ (range (fun n : ℕ => (shift^[n]) (0 : H2)))) = ⊥ := by
    simp only [hz, range_const, Submodule.span_singleton_eq_bot]
  rw [IsOuter, hbot] at ho
  have hb : (⊥ : Submodule ℂ H2).topologicalClosure = ⊥ :=
    (show IsClosed ((⊥ : Submodule ℂ H2) : Set H2) from isClosed_singleton).submodule_topologicalClosure_eq
  rw [hb] at ho
  have hm : (lp.single 2 0 (1 : ℂ) : H2) ∈ (⊥ : Submodule ℂ H2) := by
    rw [ho]
    trivial
  have hz' : (lp.single 2 0 (1 : ℂ) : H2) = 0 := hm
  have hc := congrArg (fun x : H2 => x 0) hz' 
  simp at hc

lemma outer_self_formula (o : H2) (ho : IsOuter o) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ EqOn (eval o) (exponentialFactor (boundaryLog o) c) disk := by
  apply HardyInnerOuter.outer_formula o (lp.single 2 0 1) o (outer_nonzero ho)
    constant_one_inner ho
  intro w hw
  rw [HardyDisk.monomial_evaluation]
  simp

lemma outer_smul {o : H2} (ho : IsOuter o) {c : ℂ} (hc : c ≠ 0) : IsOuter (c • o) := by
  have hm : o ∈ HardyInnerOuter.cyclicSubspace (c • o) := by
    have h := (HardyInnerOuter.cyclicSubspace (c • o)).smul_mem c⁻¹
      (HardyInnerOuter.mem_cyclicSubspace (c • o))
    simpa [smul_smul, hc] using h
  have hs := HardyInnerOuter.cyclicSubspace_minimal
    (Submodule.isClosed_topologicalClosure _)
    (HardyInnerOuter.cyclicSubspace_invariant (c • o)) hm
  change HardyInnerOuter.cyclicSubspace o = ⊤ at ho
  change HardyInnerOuter.cyclicSubspace (c • o) = ⊤
  exact top_unique (ho ▸ hs)

lemma logarithmicIntegral_add {h k : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) (hk : Integrable k circleMeasure)
    {w : ℂ} (hw : w ∈ disk) :
    logarithmicIntegral (h + k) w = logarithmicIntegral h w + logarithmicIntegral k w := by
  simp only [logarithmicIntegral, Pi.add_apply, ofReal_add, mul_add]
  exact integral_add (integrable_kernel_mul hh hw) (integrable_kernel_mul hk hw)

lemma exponentialFactor_add {h k : BoundaryCircle → ℝ}
    (hh : Integrable h circleMeasure) (hk : Integrable k circleMeasure)
    (c d : ℂ) {w : ℂ} (hw : w ∈ disk) :
    exponentialFactor (h + k) (c * d) w = exponentialFactor h c w * exponentialFactor k d w := by
  rw [exponentialFactor, logarithmicIntegral_add hh hk hw, Complex.exp_add]
  simp only [exponentialFactor]
  ring

lemma exponentialFactor_congr {h k : BoundaryCircle → ℝ}
    (he : h =ᵐ[circleMeasure] k) (c w : ℂ) :
    exponentialFactor h c w = exponentialFactor k c w := by
  unfold exponentialFactor logarithmicIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

lemma factor_nonzero {f i o : H2} (hi : IsInner i) (ho : IsOuter o)
    (he : ∀ w ∈ disk, eval f w = eval i w * eval o w) : f ≠ 0 := by
  have hf : Beurling.innerMul i hi o = f :=
    HardyDisk.evaluation_injective _ _ (fun w hw =>
      (Beurling.innerMul_evaluation i hi o w hw).trans (he w hw).symm)
  intro hz
  apply outer_nonzero ho
  apply (Beurling.innerMul i hi).injective
  rw [hf, hz, map_zero]


lemma evaluation_sub (f g : H2) {w : ℂ} (hw : w ∈ disk) :
    eval (f - g) w = eval f w - eval g w := by
  have hn : eval (-g) w = -eval g w := by
    simpa using HardyDisk.evaluation_smul (-1) g w
  calc
    eval (f - g) w = eval f w + eval (-g) w := HardyDisk.evaluation_add f (-g) w hw
    _ = _ := by rw [hn]; rfl

/-- The L² hypothesis is used through the actual product f. The two outer
factors need not have an H² product before inserting the Cayley weight. -/
theorem product_outer : Spec.ProductOuter := by
  intro f₁ f₂ f i₁ o₁ i₂ o₂ hi₁ ho₁ hi₂ ho₂ he₁ he₂ he
  let b : H2 := normalization⁻¹ • cayleyInverseWeight
  let s : H2 := normalization⁻¹ • (f₁ - shift f₁)
  have hb : IsOuter b := outer_smul inverseWeight_outer (inv_ne_zero HardyCayley.normalization_ne_zero)
  have hbe (w : ℂ) (hw : w ∈ disk) : eval b w = (1 - w) / normalization := by
    have hs : eval b w = normalization⁻¹ * eval cayleyInverseWeight w :=
      HardyDisk.evaluation_smul normalization⁻¹ cayleyInverseWeight w
    rw [hs, inverseWeight_eval w hw]
    simp [div_eq_mul_inv, mul_comm]
  have hse (w : ℂ) (hw : w ∈ disk) : eval s w = eval b w * eval f₁ w := by
    have hs : eval s w = normalization⁻¹ * eval (f₁ - shift f₁) w :=
      HardyDisk.evaluation_smul normalization⁻¹ (f₁ - shift f₁) w
    have hz : eval (shift f₁) w = w * eval f₁ w := HardyDisk.shift_evaluation f₁ w hw
    rw [hs, evaluation_sub _ _ hw, hz, hbe w hw]
    ring
  have hfe (w : ℂ) (hw : w ∈ disk) : eval f w = eval s w * eval f₂ w := by
    rw [hse w hw, hbe w hw, he w hw]
    ring
  have hf₁ := factor_nonzero hi₁ ho₁ he₁
  have hf₂ := factor_nonzero hi₂ ho₂ he₂
  have hbb := (boundary_log_integrable b (outer_nonzero hb)).2
  have hbn₁ := (boundary_log_integrable f₁ hf₁).2
  have hbn₂ := (boundary_log_integrable f₂ hf₂).2
  have hsb := boundary_mul_of_eval_mul hse
  have hfb := boundary_mul_of_eval_mul hfe
  have hbn : ∀ᵐ t ∂circleMeasure, boundary f t ≠ 0 := by
    filter_upwards [hsb, hfb, hbb, hbn₁, hbn₂] with t hst hft hbt h₁ h₂
    rw [hft, hst]
    exact mul_ne_zero (mul_ne_zero hbt h₁) h₂
  have hf : f ≠ 0 := by
    intro hz
    have hzero : ∀ᵐ t ∂circleMeasure, boundary f t = 0 := by
      simpa [hz] using (Lp.coeFn_zero ℂ circleMeasure 2)
    obtain ⟨t, ht, hn⟩ := (hzero.and hbn).exists
    exact hn ht
  have hlogs : boundaryLog f =ᵐ[circleMeasure]
      (boundaryLog b + boundaryLog f₁) + boundaryLog f₂ := by
    filter_upwards [hsb, hfb, hbb, hbn₁, hbn₂] with t hst hft hbt h₁ h₂
    simp only [boundaryLog, Pi.add_apply, hft, hst, norm_mul]
    rw [Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hbt) (norm_ne_zero_iff.mpr h₁))
      (norm_ne_zero_iff.mpr h₂),
      Real.log_mul (norm_ne_zero_iff.mpr hbt) (norm_ne_zero_iff.mpr h₁)]
  obtain ⟨cb, hcb, heb⟩ := outer_self_formula b hb
  obtain ⟨c₁, hc₁, heo₁⟩ := HardyInnerOuter.outer_formula f₁ i₁ o₁ hf₁ hi₁ ho₁ he₁
  obtain ⟨c₂, hc₂, heo₂⟩ := HardyInnerOuter.outer_formula f₂ i₂ o₂ hf₂ hi₂ ho₂ he₂
  have hc : ‖cb * c₁ * c₂‖ = 1 := by simp [norm_mul, hcb, hc₁, hc₂]
  obtain ⟨_, _, o, heo, _, _⟩ := factor_construction f hf (cb * c₁ * c₂) hc
  refine ⟨o, HardyInnerOuter.exponential_cyclicity f hf _ hc o heo, ?_⟩
  intro w hw
  rw [heo hw, exponentialFactor_congr hlogs,
    exponentialFactor_add
      (((boundary_log_integrable b (outer_nonzero hb)).1).add
        (boundary_log_integrable f₁ hf₁).1)
      (boundary_log_integrable f₂ hf₂).1 _ _ hw,
    exponentialFactor_add (boundary_log_integrable b (outer_nonzero hb)).1
      (boundary_log_integrable f₁ hf₁).1 _ _ hw,
    ← heb hw, ← heo₁ hw, ← heo₂ hw, hbe w hw]
  ring


/-- Identical vanishing orders identify the actual zero-occurrence index sets. -/
def zeroOccurrenceEquiv {f g : H2}
    (he : ∀ z ∈ disk, analyticOrderNatAt (eval f) z = analyticOrderNatAt (eval g) z) :
    BlaschkeProducts.ZeroOccurrence f ≃ BlaschkeProducts.ZeroOccurrence g where
  toFun j := ⟨j.val, j.property.1, by rw [← he _ j.property.1]; exact j.property.2⟩
  invFun j := ⟨j.val, j.property.1, by rw [he _ j.property.1]; exact j.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma canonicalProduct_eq_of_orders {f g : H2}
    (he : ∀ z ∈ disk, analyticOrderNatAt (eval f) z = analyticOrderNatAt (eval g) z)
    (w : ℂ) : BlaschkeProducts.canonicalProduct f w = BlaschkeProducts.canonicalProduct g w := by
  exact (zeroOccurrenceEquiv he).tprod_eq
    (fun j => BlaschkeProducts.factor (BlaschkeProducts.zeroPoint j) w)

lemma canonicalProduct_smul (i : H2) {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    BlaschkeProducts.canonicalProduct (a • i) w = BlaschkeProducts.canonicalProduct i w := by
  apply canonicalProduct_eq_of_orders _ w
  intro z hz
  have he : eval (a • i) =ᶠ[𝓝 z] (fun t => a * eval i t) :=
    Eventually.of_forall (HardyDisk.evaluation_smul a i)
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr he]
  have ho := analyticOrderAt_mul (show AnalyticAt ℂ (fun _ : ℂ => a) z from analyticAt_const)
    (HardyDisk.analytic_evaluation i z hz)
  change analyticOrderAt (fun t => a * eval i t) z = _ at ho
  rw [ho, analyticOrderAt_eq_zero.mpr (Or.inr ha), zero_add]

lemma singular_measure_unique {f : H2} {μ ν : Measure _root_.Circle}
    (hμ : HasSingularMeasure f μ) (hν : HasSingularMeasure f ν) : μ = ν := by
  obtain ⟨i, o, c, hi, ho, hμ, hc, hfi, hmi⟩ := hμ
  obtain ⟨j, p, d, hj, hp, hν, hd, hfj, hmj⟩ := hν
  obtain ⟨a, ha, hja, _⟩ := HardyInnerOuter.uniqueness f i o j p
    (factor_nonzero hi ho hfi) hi ho hj hp hfi hfj
  have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; exact one_ne_zero)
  have hμj (w : ℂ) (hw : w ∈ disk) :
      eval j w = BlaschkeProducts.canonicalProduct j w * singularFactor μ (a * c) w := by
    have hjs : eval j w = a * eval i w := by
      rw [hja]
      exact HardyDisk.evaluation_smul a i w
    rw [hjs, hmi w hw, hja, canonicalProduct_smul i ha0 w]
    simp only [singularFactor]
    ring
  exact (HardyFactorization.inner_measure_uniqueness j hj μ ν (a * c) d hμ hν
    (by rw [norm_mul, ha, hc, mul_one]) hd hμj hmj).1

theorem coefficient_uniqueness : Spec.CoefficientUniqueness := by
  intro F a b ha hb
  obtain ⟨f, hf, μ, hμ, rfl⟩ := ha
  obtain ⟨g, hg, ν, hν, rfl⟩ := hb
  have hfg : f = g := HardyDisk.evaluation_injective f g (hf.trans hg.symm)
  subst g
  rw [singular_measure_unique hμ hν]

/-- A sigma presentation separates the zero location from its multiplicity. -/
def zeroOccurrenceSigma (f : H2) : BlaschkeProducts.ZeroOccurrence f ≃
    (Σ z : Disk, Fin (analyticOrderNatAt (eval f) z)) where
  toFun j := ⟨⟨j.val.1, j.property.1⟩, ⟨j.val.2, j.property.2⟩⟩
  invFun j := ⟨(j.1.val, j.2.val), j.1.property, j.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma orders_mul {f g h : H2} (hf : f ≠ 0) (hg : g ≠ 0)
    (he : ∀ z ∈ disk, eval h z = eval f z * eval g z) (z : ℂ) (hz : z ∈ disk) :
    analyticOrderNatAt (eval h) z = analyticOrderNatAt (eval f) z + analyticOrderNatAt (eval g) z := by
  have hlocal : eval h =ᶠ[𝓝 z] eval f * eval g :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) (fun t ht => he t ht)
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr hlocal,
    analyticOrderAt_mul (HardyDisk.analytic_evaluation f z hz) (HardyDisk.analytic_evaluation g z hz),
    ENat.toNat_add (BlaschkeProducts.zero_orders_finite f hf z hz)
      (BlaschkeProducts.zero_orders_finite g hg z hz)]

/-- A product has the disjoint union of the two zero multisets. -/
def productZeroEquiv {f g h : H2}
    (he : ∀ z ∈ disk, analyticOrderNatAt (eval h) z =
      analyticOrderNatAt (eval f) z + analyticOrderNatAt (eval g) z) :
    BlaschkeProducts.ZeroOccurrence h ≃
      BlaschkeProducts.ZeroOccurrence f ⊕ BlaschkeProducts.ZeroOccurrence g :=
  (zeroOccurrenceSigma h).trans
    ((Equiv.sigmaCongrRight (fun z : Disk => (finCongr (he z z.property)).trans
      finSumFinEquiv.symm)).trans
      ((Equiv.sigmaSumDistrib _ _).trans
        (Equiv.sumCongr (zeroOccurrenceSigma f).symm (zeroOccurrenceSigma g).symm)))

lemma productZeroEquiv_point {f g h : H2}
    (he : ∀ z ∈ disk, analyticOrderNatAt (eval h) z =
      analyticOrderNatAt (eval f) z + analyticOrderNatAt (eval g) z)
    (j : BlaschkeProducts.ZeroOccurrence h) :
    Sum.elim BlaschkeProducts.zeroPoint BlaschkeProducts.zeroPoint (productZeroEquiv he j) =
      BlaschkeProducts.zeroPoint j := by
  change Sum.elim _ _ (Equiv.sumCongr (zeroOccurrenceSigma f).symm
    (zeroOccurrenceSigma g).symm (Equiv.sigmaSumDistrib _ _
      ⟨(⟨j.val.1, j.property.1⟩ : Disk),
        finSumFinEquiv.symm (finCongr (he j.val.1 j.property.1) ⟨j.val.2, j.property.2⟩)⟩)) = _
  generalize finSumFinEquiv.symm (finCongr (he _ j.property.1) ⟨j.val.2, j.property.2⟩) = k
  cases k <;> rfl

lemma canonicalProduct_mul {i j k : H2} (hi : IsInner i) (hj : IsInner j)
    (hk : IsInner k) (he : ∀ w ∈ disk, eval k w = eval i w * eval j w)
    (w : ℂ) (hw : w ∈ disk) :
    BlaschkeProducts.canonicalProduct k w =
      BlaschkeProducts.canonicalProduct i w * BlaschkeProducts.canonicalProduct j w := by
  let e := productZeroEquiv (orders_mul (BlaschkeProducts.inner_nonzero i hi)
    (BlaschkeProducts.inner_nonzero j hj) he)
  let factors : BlaschkeProducts.ZeroOccurrence i ⊕ BlaschkeProducts.ZeroOccurrence j → ℂ :=
    fun x => BlaschkeProducts.factor (Sum.elim BlaschkeProducts.zeroPoint BlaschkeProducts.zeroPoint x) w
  have hp : HasProd factors
      (BlaschkeProducts.canonicalProduct i w * BlaschkeProducts.canonicalProduct j w) :=
    (BlaschkeProducts.family_hasProd (@BlaschkeProducts.zeroPoint i)
      (fun q => q.property.1) (BlaschkeProducts.zero_summability i hi) hw).sum
    (BlaschkeProducts.family_hasProd (@BlaschkeProducts.zeroPoint j)
      (fun q => q.property.1) (BlaschkeProducts.zero_summability j hj) hw)
  have hcomp : factors ∘ e =
      (fun q : BlaschkeProducts.ZeroOccurrence k => BlaschkeProducts.factor (BlaschkeProducts.zeroPoint q) w) := by
    funext q
    dsimp [factors, Function.comp_def, e]
    rw [productZeroEquiv_point]
  have hprod := e.hasProd_iff.mpr hp
  rw [hcomp] at hprod
  exact (BlaschkeProducts.family_hasProd (@BlaschkeProducts.zeroPoint k)
    (fun q => q.property.1) (BlaschkeProducts.zero_summability k hk) hw).unique hprod


lemma inner_product {i j : H2} (hi : IsInner i) (hj : IsInner j) :
    IsInner (Beurling.innerMul i hi j) := by
  let k := Beurling.innerMul i hi j
  have he (w : ℂ) (hw : w ∈ disk) : eval k w = eval i w * eval j w :=
    Beurling.innerMul_evaluation i hi j w hw
  refine ⟨⟨1, ?_⟩, ?_⟩
  · intro w hw
    rw [he w hw, norm_mul]
    exact (mul_le_mul_of_nonneg_right (HardyInnerOuter.inner_bound hi hw)
      (norm_nonneg _)).trans (by simpa using HardyInnerOuter.inner_bound hj hw)
  · filter_upwards [boundary_mul_of_eval_mul he, hi.2, hj.2] with t ht hit hjt
    rw [ht, norm_mul, hit, hjt, mul_one]

lemma singularFactor_mul (μ ν : Measure _root_.Circle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (c d : ℂ) {w : ℂ} (hw : w ∈ disk) :
    singularFactor (μ + ν) (c * d) w = singularFactor μ c w * singularFactor ν d w := by
  rw [singularFactor, herglotz_add μ ν hw, neg_add, Complex.exp_add]
  simp only [singularFactor]
  ring

lemma singular_measure_product {f₁ f₂ f : H2} {μ ν : Measure _root_.Circle}
    (hμ : HasSingularMeasure f₁ μ) (hν : HasSingularMeasure f₂ ν)
    (he : ∀ w ∈ disk, eval f w = (1 - w) * eval f₁ w * eval f₂ w / normalization) :
    HasSingularMeasure f (μ + ν) := by
  obtain ⟨i₁, o₁, c₁, hi₁, ho₁, hμ, hc₁, he₁, hm₁⟩ := hμ
  obtain ⟨i₂, o₂, c₂, hi₂, ho₂, hν, hc₂, he₂, hm₂⟩ := hν
  let := hμ.1
  let := hν.1
  obtain ⟨o, ho, heo⟩ := product_outer f₁ f₂ f i₁ o₁ i₂ o₂ hi₁ ho₁ hi₂ ho₂ he₁ he₂ he
  let k := Beurling.innerMul i₁ hi₁ i₂
  have hk : IsInner k := inner_product hi₁ hi₂
  have hke (w : ℂ) (hw : w ∈ disk) : eval k w = eval i₁ w * eval i₂ w :=
    Beurling.innerMul_evaluation i₁ hi₁ i₂ w hw
  refine ⟨k, o, c₁ * c₂, hk, ho, ⟨inferInstance, hμ.2.add_left hν.2⟩,
    by simp [norm_mul, hc₁, hc₂], ?_, ?_⟩
  · intro w hw
    rw [he w hw, he₁ w hw, he₂ w hw, hke w hw, heo w hw]
    ring
  · intro w hw
    rw [hke w hw, hm₁ w hw, hm₂ w hw,
      canonicalProduct_mul hi₁ hi₂ hk hke w hw, singularFactor_mul μ ν c₁ c₂ hw]
    ring

theorem coefficient_additivity : Spec.CoefficientAdditivity := by
  intro F G _ _ _ a b c ha hb hc
  obtain ⟨f₁, hf₁, μ, hμ, rfl⟩ := ha
  obtain ⟨f₂, hf₂, ν, hν, rfl⟩ := hb
  obtain ⟨f, hf, ρ, hρ, rfl⟩ := hc
  have he (w : ℂ) (hw : w ∈ disk) :
      eval f w = (1 - w) * eval f₁ w * eval f₂ w / normalization := by
    rw [hf hw, disk_product F G w hw, ← hf₁ hw, ← hf₂ hw]
  have hρeq := singular_measure_unique hρ (singular_measure_product hμ hν he)
  obtain ⟨i₁, o₁, c₁, _, _, hμf, _⟩ := hμ
  obtain ⟨i₂, o₂, c₂, _, _, hνf, _⟩ := hν
  let := hμf.1
  let := hνf.1
  rw [hρeq]
  unfold atomMass
  simp [measureReal_def, ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top ν _)]


lemma canonicalProduct_zero_free_factor {b s k i : H2} (hb : IsInner b) (hs : IsInner s)
    (hsn : ZeroFree s)
    (hbe : EqOn (eval b) (BlaschkeProducts.canonicalProduct i) disk)
    (hi : IsInner i) (hke : ∀ w ∈ disk, eval k w = eval b w * eval s w) (w : ℂ) :
    BlaschkeProducts.canonicalProduct k w = BlaschkeProducts.canonicalProduct i w := by
  apply canonicalProduct_eq_of_orders _ w
  intro z hz
  rw [orders_mul (BlaschkeProducts.inner_nonzero b hb)
    (BlaschkeProducts.inner_nonzero s hs) hke z hz]
  have hzord : analyticOrderNatAt (eval s) z = 0 := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (hsn z hz))]
    rfl
  rw [hzord, add_zero]
  unfold analyticOrderNatAt
  congr 1
  have hl : eval b =ᶠ[𝓝 z] BlaschkeProducts.canonicalProduct i :=
    eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) (fun t ht => hbe ht)
  rw [analyticOrderAt_congr hl, BlaschkeProducts.canonical_orders i hi z hz]

theorem exponential_extraction : Spec.ExponentialExtraction := by
  intro F a ha
  obtain ⟨f, hf, μ, hμf, rfl⟩ := ha
  obtain ⟨i, o, c, hi, ho, hμ, hc, hfi, hmi⟩ := hμf
  obtain ⟨ha, hν, hνzero, _, hsplit⟩ := atom_removal μ hμ
  obtain ⟨b, hb, hbe⟩ := BlaschkeProducts.canonical_inner i hi
  obtain ⟨s, hs, hsn, hse⟩ := HardyFactorization.singular_converse (atomRemainder μ) hν c hc
  let k := Beurling.innerMul b hb s
  have hk : IsInner k := inner_product hb hs
  have hke (w : ℂ) (hw : w ∈ disk) : eval k w = eval b w * eval s w :=
    Beurling.innerMul_evaluation b hb s w hw
  have hmk (w : ℂ) (hw : w ∈ disk) :
      eval k w = BlaschkeProducts.canonicalProduct k w * singularFactor (atomRemainder μ) c w := by
    rw [hke w hw, hbe hw, hse hw,
      canonicalProduct_zero_free_factor hb hs hsn hbe hi hke w]
  let g := Beurling.innerMul k hk o
  have hge (w : ℂ) (hw : w ∈ disk) : eval g w = eval k w * eval o w :=
    Beurling.innerMul_evaluation k hk o w hw
  have hμg : HasSingularMeasure g (atomRemainder μ) :=
    ⟨k, o, c, hk, ho, hν, hc, hge, hmk⟩
  let H := inverseTransform g
  have hH : HardyHalfPlaneRepresentationSpec.IsH2 H := (HardyCayley.onto g).1
  have hcoeff : HasCoefficient H 0 := by
    refine ⟨g, ?_, atomRemainder μ, hμg, ?_⟩
    · intro w hw
      exact (HardyCayley.transform_inverse g hw).symm
    · simp [atomMass, measureReal_def, hνzero]
  have hsplitF (w : ℂ) (hw : w ∈ disk) :
      eval f w = exponentialInner (atomMass μ) (cayley w) * eval g w := by
    rw [hfi w hw, hmi w hw, hsplit c w hw, hge w hw, hke w hw, hbe hw, hse hw]
    ring
  refine ⟨ha, H, hH, hcoeff, ?_⟩
  intro z hz
  rw [← HardyCayley.inverse_transform hf hz]
  change (1 - uncayley z) * eval f (uncayley z) / normalization =
    exponentialInner (atomMass μ) z * ((1 - uncayley z) * eval g (uncayley z) / normalization)
  rw [hsplitF (uncayley z) (HardyCayley.uncayley_mem hz)]
  have hcz : cayley (uncayley z) = z := HardyCayley.cayley_uncayley hz
  rw [hcz]
  ring


/-- Exact boundary logarithms leave no positive singular term. In particular,
the reciprocal weight cannot insert an atom at the point corresponding to ∞. -/
theorem prefactor_singular_measure_zero : Spec.PrefactorSingularMeasureZero := by
  intro μ hμ c d hc hd he
  let := hμ.1
  have hz : (0 : ℂ) ∈ disk := HardyInnerOuter.zero_mem_disk
  have hp : poissonLog (fun t => -boundaryLog cayleyInverseWeight t) 0 = 0 := by
    have h := prefactor.2.2.2 0 hz
    simpa using h.symm
  have ho : ‖exponentialFactor (fun t => -boundaryLog cayleyInverseWeight t) d 0‖ =
      Real.exp (poissonLog (fun t => -boundaryLog cayleyInverseWeight t) 0) :=
    exponential_norm _ prefactor.2.2.1.neg d hd 0 hz
  rw [hp, Real.exp_zero] at ho
  have hm := congrArg norm (he 0 hz)
  simp only [sub_zero, inv_one, norm_one, norm_mul, ho, mul_one] at hm
  rw [singularFactor_norm μ hc hz, PositiveHarmonic.poissonExtension_zero] at hm
  have hmass : μ.real univ = 0 := neg_eq_zero.mp (Real.exp_injective (hm.symm.trans Real.exp_zero.symm))
  exact Measure.measure_univ_eq_zero.mp ((measureReal_eq_zero_iff (measure_ne_top μ _)).mp hmass)

end ExpandedFA.PartIV.HardyExponentialFactor
