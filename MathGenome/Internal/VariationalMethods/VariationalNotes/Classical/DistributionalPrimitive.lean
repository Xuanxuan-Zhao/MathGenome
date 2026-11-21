import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.DistributionalPrimitive
import MathGenome.Internal.VariationalMethods.VariationalNotes.Classical.FundamentalLemma
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DistributionPrimitive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import Mathlib.Analysis.Distribution.Distribution

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace VariationalNotes.Classical

private theorem enclose_compact {a b c : ℝ} (hc : c ∈ Ioo a b)
    {K : Set ℝ} (hK : IsCompact K) (hs : K ⊆ Ioo a b) :
    ∃ l ∈ Ioo a b, ∃ r ∈ Ioo a b, c ∈ Ioo l r ∧ K ⊆ Ioo l r := by
  obtain ⟨l, hl, r, hr, hsub⟩ :=
    ExpandedFA.Sobolev.OneDimensional.compact_interval_enclosure isOpen_Ioo
      ordConnected_Ioo ⟨c, hc⟩ (hK.union isCompact_singleton)
      (union_subset hs (singleton_subset_iff.mpr hc))
  exact ⟨l, hl, r, hr, hsub (Or.inr rfl), fun t ht => hsub (Or.inl ht)⟩

/-- Compact truncation is integrable even when q is singular at a or b. -/
private theorem primitive_localization {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b c l r : ℝ} {q : ℝ → E}
    (hq : LocallyIntegrableOn q (Ioo a b)) (hl : l ∈ Ioo a b)
    (hr : r ∈ Ioo a b) (hc : c ∈ Icc l r) :
    Integrable ((Icc l r).indicator q) ∧
      EqOn (fun t => ∫ s in c..t, q s)
        (fun t => ∫ s in c..t, (Icc l r).indicator q s) (Icc l r) := by
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mpr
    (hq.integrableOn_compact_subset (ordConnected_Ioo.out hl hr) isCompact_Icc), ?_⟩
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  exact (indicator_of_mem ((ordConnected_Icc.uIcc_subset hc ht) hs) q).symm

private theorem primitive_locallyAC {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b c : ℝ} {q : ℝ → E}
    (hq : LocallyIntegrableOn q (Ioo a b)) (hc : c ∈ Ioo a b) :
    LocallyACInterval (fun t => ∫ s in c..t, q s) a b := by
  intro x hx y hy
  obtain ⟨l, hl, r, hr, hcl, hxy⟩ := enclose_compact hc isCompact_uIcc
    (ordConnected_Ioo.uIcc_subset hx hy)
  obtain ⟨hgi, heq⟩ := primitive_localization hq hl hr (Ioo_subset_Icc_self hcl)
  have hac := ExpandedFA.Sobolev.OneDimensional.integral_primitive_absolutelyContinuous
    (fun u v => hgi.intervalIntegrable) x y c
  exact hac.congr (fun t ht => (heq (Ioo_subset_Icc_self (hxy ht))).symm)

private theorem locallyAC_continuousOn {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} {f : ℝ → E} (hf : LocallyACInterval f a b) :
    ContinuousOn f (Ioo a b) := by
  intro t ht
  let l := (a + t) / 2
  let r := (t + b) / 2
  have hl : l ∈ Ioo a b := by constructor <;> dsimp [l] <;> linarith [ht.1, ht.2]
  have hr : r ∈ Ioo a b := by constructor <;> dsimp [r] <;> linarith [ht.1, ht.2]
  have hlt : l < t := by dsimp [l]; linarith [ht.1]
  have htr : t < r := by dsimp [r]; linarith [ht.2]
  have hcont : ContinuousOn f (Icc l r) := by
    simpa only [uIcc_of_le (hlt.trans htr).le] using
      (AbsolutelyContinuousOnInterval.continuousOn (hf l hl r hr))
  have hwithin : ContinuousWithinAt f (Icc l r) t := hcont t ⟨hlt.le, htr.le⟩
  have hat : ContinuousAt f t := hwithin.continuousAt (Icc_mem_nhds hlt htr)
  exact hat.continuousWithinAt

private theorem primitive_ae_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b c : ℝ} {q : ℝ → E}
    (hq : LocallyIntegrableOn q (Ioo a b)) (hc : c ∈ Ioo a b) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      HasDerivAt (fun t => ∫ s in c..t, q s) (q t) t := by
  apply ExpandedFA.Sobolev.Lines.ae_on_set_of_locally_ae
  intro t ht
  obtain ⟨l, hl, r, hr, hcl, htl⟩ := enclose_compact hc isCompact_singleton
    (singleton_subset_iff.mpr ht)
  have htI := htl (mem_singleton t)
  obtain ⟨hgi, heq⟩ := primitive_localization hq hl hr (Ioo_subset_Icc_self hcl)
  refine ⟨⟨Ioo l r, isOpen_Ioo⟩, htI, ?_⟩
  filter_upwards [ae_restrict_of_ae (_root_.LocallyIntegrable.ae_hasDerivAt_integral hgi.locallyIntegrable),
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  have hd := hx c
  rw [indicator_of_mem (Ioo_subset_Icc_self hxI) q] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
  exact heq (Ioo_subset_Icc_self hy)

private theorem primitive_test_identity {a b c : ℝ} {q ψ : ℝ → ℝ}
    (hq : LocallyIntegrableOn q (Ioo a b)) (hc : c ∈ Ioo a b)
    (hψ : ContDiff ℝ ∞ ψ) (hk : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo a b) :
    (∫ t, ψ t * q t) = -(∫ t, deriv ψ t * (∫ s in c..t, q s)) := by
  obtain ⟨l, hl, r, hr, hcl, hψl⟩ := enclose_compact hc hk hs
  obtain ⟨hgi, heq⟩ := primitive_localization hq hl hr (Ioo_subset_Icc_self hcl)
  have hleft : (fun t => ψ t * q t) =
      (fun t => ψ t * (Icc l r).indicator q t) := by
    funext t
    by_cases ht : t ∈ tsupport ψ
    · rw [indicator_of_mem (Ioo_subset_Icc_self (hψl ht)) q]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hright : (fun t => deriv ψ t * (∫ s in c..t, q s)) =
      (fun t => deriv ψ t * (∫ s in c..t, (Icc l r).indicator q s)) := by
    funext t
    by_cases ht : t ∈ tsupport ψ
    · exact congrArg (fun z => deriv ψ t * z) (heq (Ioo_subset_Icc_self (hψl ht)))
    · simp [deriv_of_notMem_tsupport ht]
  rw [hleft, hright]
  exact ExpandedFA.Sobolev.OneDimensional.integral_test_mul_primitive
    hgi.locallyIntegrable c hψ hk

/-- The distribution-kernel theorem applies to locally integrable functions on
this interval; it does not require an integrable zero extension at its endpoints. -/
private theorem ae_constant_of_test_deriv {a b : ℝ} (hab : a < b) {h : ℝ → ℝ}
    (hh : LocallyIntegrableOn h (Ioo a b))
    (htest : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t * h t) = 0) :
    ∃ c, h =ᵐ[volume.restrict (Ioo a b)] fun _ => c := by
  let Ω : TopologicalSpace.Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
  let u : ExpandedFA.PartIV.DistributionPrimitive.LineDistribution ℝ Ω :=
    TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℝ ℝ) volume h
  have hu (ψ : ExpandedFA.PartIV.DistributionPrimitive.LineTests ℝ Ω) :
      u ψ = ∫ t, ψ t * h t :=
    TestFunction.integralAgainstBilinCLM_eq_integral hh
  have hd : ExpandedFA.PartIV.DistributionPrimitive.lineDerivative u = 0 := by
    ext ψ
    change -u (TestFunction.lineDerivCLM ℝ (1 : ℝ) ψ) = 0
    rw [hu]
    simp_rw [ExpandedFA.PartIV.DistributionPrimitive.lineDeriv_apply]
    exact neg_eq_zero.mpr (htest ψ ψ.contDiff ψ.hasCompactSupport ψ.tsupport_subset)
  obtain ⟨c, hc⟩ := (ExpandedFA.PartIV.DistributionPrimitive.kernel ℝ Ω
    (nonempty_Ioo.mpr hab) ordConnected_Ioo u).mp hd
  refine ⟨c, Distribution.ofFun_injective (Ω := Ω) (n := ⊤) hh
    (locallyIntegrableOn_const c) ?_⟩
  ext ψ
  rw [Distribution.ofFun_apply hh, Distribution.ofFun_apply (locallyIntegrableOn_const c)]
  change (∫ t, ψ t * h t) = ∫ t, ψ t * c
  rw [← hu, hc ψ, integral_mul_const, mul_comm]

private theorem test_mul_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {h : ℝ → E}
    (hh : LocallyIntegrableOn h (Ioo a b)) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hk : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo a b) : Integrable (fun t => ψ t • h t) := by
  let φ : TestFunction (⟨Ioo a b, isOpen_Ioo⟩ : TopologicalSpace.Opens ℝ) ℝ ⊤ :=
    ⟨ψ, hψ, hk, hs⟩
  exact φ.integrable_smul hh

private theorem scalar_primitive_normal_form {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Ioo a b) (p q : ℝ → ℝ)
    (hp : LocallyIntegrableOn p (Ioo a b)) (hq : LocallyIntegrableOn q (Ioo a b))
    (hw : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, p t * deriv φ t + q t * φ t = 0) :
    ∃ k : ℝ, p =ᵐ[volume.restrict (Ioo a b)]
      (fun t => (∫ s in c..t, q s) + k) := by
  let Q : ℝ → ℝ := fun t => ∫ s in c..t, q s
  have hQac : LocallyACInterval Q a b := primitive_locallyAC hq hc
  have hQli : LocallyIntegrableOn Q (Ioo a b) :=
    (locallyAC_continuousOn hQac).locallyIntegrableOn measurableSet_Ioo
  have hz : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t * (p t - Q t)) = 0 := by
    intro ψ hψ hk hs
    have hip : Integrable (fun t => deriv ψ t * p t) :=
      test_mul_integrable hp ((contDiff_infty_iff_deriv.mp hψ).2) hk.deriv (tsupport_deriv_subset.trans hs)
    have hiq : Integrable (fun t => ψ t * q t) := test_mul_integrable hq hψ hk hs
    have hiQ : Integrable (fun t => deriv ψ t * Q t) :=
      test_mul_integrable hQli ((contDiff_infty_iff_deriv.mp hψ).2) hk.deriv (tsupport_deriv_subset.trans hs)
    have hglobal : (∫ t, deriv ψ t * p t + ψ t * q t) = 0 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo a b) ?_]
      · simpa only [mul_comm] using hw ψ hψ hk hs
      · intro t ht
        have hn : t ∉ tsupport ψ := fun hm => ht (hs hm)
        simp [image_eq_zero_of_notMem_tsupport hn, deriv_of_notMem_tsupport hn]
    have hQtest := primitive_test_identity hq hc hψ hk hs
    change (∫ t, ψ t * q t) = -(∫ t, deriv ψ t * Q t) at hQtest
    rw [integral_add hip hiq, hQtest] at hglobal
    simp_rw [mul_sub]
    rw [integral_sub hip hiQ]
    linarith
  obtain ⟨k, hk⟩ := ae_constant_of_test_deriv hab (hp.sub hQli) hz
  refine ⟨k, ?_⟩
  filter_upwards [hk] with t ht
  exact sub_eq_iff_eq_add'.mp (show p t - Q t = k from ht)

/-- Scalar primitive, with no endpoint integrability assumption. -/
theorem distributionalPrimitiveScalar :
    Specs.VariationalNotes.Classical.distributionalPrimitiveScalar := by
  intro a b hab p q hp hq hw
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by constructor <;> dsimp [c] <;> linarith
  obtain ⟨k, hk⟩ := scalar_primitive_normal_form hab hc p q hp hq hw
  refine ⟨fun t => (∫ s in c..t, q s) + k, hk, ?_, ?_⟩
  · intro x hx y hy
    exact (primitive_locallyAC hq hc x hx y hy).add
      (LipschitzWith.const k).lipschitzOnWith.absolutelyContinuousOnInterval
  · filter_upwards [primitive_ae_hasDerivAt hq hc] with t ht
    exact ht.add_const k

private theorem vector_primitive_normal_form {m : ℕ} {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Ioo a b) (p q : ℝ → EuclideanSpace ℝ (Fin m))
    (hp : LocallyIntegrableOn p (Ioo a b)) (hq : LocallyIntegrableOn q (Ioo a b))
    (hw : WeakDerivativeInterval m a b p q) :
    ∃ k : EuclideanSpace ℝ (Fin m), p =ᵐ[volume.restrict (Ioo a b)]
      (fun t => (∫ s in c..t, q s) + k) := by
  classical
  have hcoord (i : Fin m) : ∃ k : ℝ,
      (fun t => p t i) =ᵐ[volume.restrict (Ioo a b)]
        (fun t => (∫ s in c..t, q s i) + k) := by
    apply scalar_primitive_normal_form hab hc (fun t => p t i) (fun t => q t i)
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).locallyIntegrableOn_comp hp
    · exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).locallyIntegrableOn_comp hq
    intro ψ hψ hk hs
    let e : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i 1
    have hd (t : ℝ) : deriv (fun s => ψ s • e) t = deriv ψ t • e :=
      ((hψ.differentiable (by simp) t).hasDerivAt.smul_const e).deriv
    have ht := hw (fun t => ψ t • e) (hψ.smul contDiff_const) hk.smul_right
      ((tsupport_smul_subset_left ψ (fun _ => e)).trans hs)
    simp_rw [hd] at ht
    simpa [e, inner_smul_right, EuclideanSpace.inner_single_right, mul_comm] using ht
  choose k hk using hcoord
  refine ⟨WithLp.toLp 2 k, ?_⟩
  filter_upwards [ae_all_iff.mpr hk, ae_restrict_mem measurableSet_Ioo] with t ht hti
  have hi : IntervalIntegrable q volume c t :=
    (hq.integrableOn_compact_subset (ordConnected_Ioo.uIcc_subset hc hti)
      isCompact_uIcc).intervalIntegrable
  ext i
  have he := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).intervalIntegral_comp_comm hi
  exact (ht i).trans (congrArg (fun v : ℝ => v + k i) he)

/-- The Euclidean version uses one vector constant and one vector primitive.
The coordinate argument also includes the zero-dimensional space. -/
theorem distributionalPrimitive :
    Specs.VariationalNotes.Classical.distributionalPrimitive := by
  intro m a b hab p q hp hq hw
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by constructor <;> dsimp [c] <;> linarith
  obtain ⟨k, hk⟩ := vector_primitive_normal_form hab hc p q hp hq hw
  refine ⟨fun t => (∫ s in c..t, q s) + k, hk, ?_, ?_⟩
  · intro x hx y hy
    exact (primitive_locallyAC hq hc x hx y hy).add
      (LipschitzWith.const k).lipschitzOnWith.absolutelyContinuousOnInterval
  · filter_upwards [primitive_ae_hasDerivAt hq hc] with t ht
    exact ht.add_const k

/-- Any two local representatives of the given class agree at every point of
an overlap. Their absolute continuity supplies the necessary continuity. -/
theorem primitiveRepresentativesAgree :
    Specs.VariationalNotes.Classical.primitiveRepresentativesAgree := by
  intro m a b c d p q f g hf hg
  have hfe : p =ᵐ[volume.restrict (Ioo a b ∩ Ioo c d)] f :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hf.1
  have hge : p =ᵐ[volume.restrict (Ioo a b ∩ Ioo c d)] g :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_right hg.1
  exact Measure.eqOn_open_of_ae_eq (hfe.symm.trans hge) (isOpen_Ioo.inter isOpen_Ioo)
    ((locallyAC_continuousOn hf.2.1).mono inter_subset_left)
    ((locallyAC_continuousOn hg.2.1).mono inter_subset_right)

private theorem continuous_of_ae_primitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {a b c : ℝ} {p q : ℝ → E}
    (hc : c ∈ Ioo a b) (hq : LocallyIntegrableOn q (Ioo a b))
    (hpc : ContinuousOn p (Ioo a b)) (hqc : ContinuousOn q (Ioo a b)) (k : E)
    (hk : p =ᵐ[volume.restrict (Ioo a b)] (fun t => (∫ s in c..t, q s) + k)) :
    ContDiffOn ℝ 1 p (Ioo a b) ∧ ∀ t ∈ Ioo a b, HasDerivAt p (q t) t := by
  let f : ℝ → E := fun t => (∫ s in c..t, q s) + k
  have hfc : ContinuousOn f (Ioo a b) :=
    (locallyAC_continuousOn (primitive_locallyAC hq hc)).add continuousOn_const
  have heq : EqOn p f (Ioo a b) := Measure.eqOn_open_of_ae_eq hk isOpen_Ioo hpc hfc
  have hd : ∀ t ∈ Ioo a b, HasDerivAt p (q t) t := by
    intro t ht
    have hi : IntervalIntegrable q volume c t :=
      (hq.integrableOn_compact_subset (ordConnected_Ioo.uIcc_subset hc ht)
        isCompact_uIcc).intervalIntegrable
    have hQ := intervalIntegral.integral_hasDerivAt_right hi
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hqc t ht)
      (hqc.continuousAt (isOpen_Ioo.mem_nhds ht))
    apply (hQ.add_const k).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact heq hs
  refine ⟨?_, hd⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun t ht => (hd t ht).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  exact hqc.congr (fun t ht => (hd t ht).deriv)

/-- With continuous data, the original p itself is the C¹ representative. -/
theorem distributionalPrimitiveContinuous :
    Specs.VariationalNotes.Classical.distributionalPrimitiveContinuous := by
  intro m a b hab p q hp hq hw hpc hqc
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by constructor <;> dsimp [c] <;> linarith
  obtain ⟨k, hk⟩ := vector_primitive_normal_form hab hc p q hp hq hw
  exact continuous_of_ae_primitive hc hq hpc hqc k hk

/-- The continuous scalar statement uses literal real-valued functions. -/
theorem distributionalPrimitiveScalarContinuous :
    Specs.VariationalNotes.Classical.distributionalPrimitiveScalarContinuous := by
  intro a b hab p q hp hq hw hpc hqc
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := by constructor <;> dsimp [c] <;> linarith
  obtain ⟨k, hk⟩ := scalar_primitive_normal_form hab hc p q hp hq hw
  exact continuous_of_ae_primitive hc hq hpc hqc k hk

/-- Aggregate version of paper.tex, Lemma `variation-fundamental`, together
with its continuous-data conclusion used immediately afterwards. -/
theorem fundamentalLemmaAndDistributionalDerivative :
    Specs.VariationalNotes.Classical.fundamentalLemmaAndDistributionalDerivative :=
  ⟨fundamentalLemmaAE, fundamentalLemmaContinuous,
    fundamentalLemmaVectorAE, fundamentalLemmaVectorContinuous,
    distributionalPrimitiveScalar, distributionalPrimitive,
    primitiveRepresentativesAgree, distributionalPrimitiveContinuous,
    distributionalPrimitiveScalarContinuous⟩

end VariationalNotes.Classical
