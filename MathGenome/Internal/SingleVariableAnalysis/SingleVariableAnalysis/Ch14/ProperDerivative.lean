import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch14.ProperDerivative
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch14.ProperContinuity
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiation under a proper Riemann integral

K03.14.proper_derivative, paper.tex:3274–3304. The uniform remainder estimate
is first proved in the supremum norm on continuous spatial sections. The
Darboux integral is then proved to be a bounded real linear functional on those
sections, using the accepted proper integrability, linearity and norm estimates.
Composition gives the derivative formula; joint continuity of the partial
derivative gives continuity of that derivative. All comparisons to the canonical
parameter families are proved explicitly, in both real and complex cases.
-/

namespace SingleVariableAnalysis.ParameterIntegral
open Set Filter
open scoped Topology ContDiff

/-- A continuous family of pointwise derivatives is a derivative in the uniform norm.
The mean inequality is a norm estimate and applies equally to complex targets. -/
theorem continuous_sections_hasDerivAt {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → C(X, E)} {J : Set ℝ} (hJ : IsOpen J)
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t)
    {t : ℝ} (ht : t ∈ J) (hg : ContinuousAt g t) : HasDerivAt f (g t) t := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have he : ∀ᶠ s in 𝓝 t, ‖g s - g t‖ < ε := by
    simpa only [dist_eq_norm] using (hg.eventually (Metric.ball_mem_nhds (g t) hε))
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.mp (inter_mem (hJ.mem_nhds ht) he)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hder (u : ℝ) (hu : u ∈ Metric.ball t δ) :
      HasDerivWithinAt (fun u => f u x - u • g t x) (g u x - g t x)
        (Metric.ball t δ) u :=
    by
      convert ((hd u (hb hu).1 x).sub
        ((hasDerivAt_id u).smul_const (g t x))).hasDerivWithinAt using 1 <;> simp
      funext y
      rfl
  have hbound (u : ℝ) (hu : u ∈ Metric.ball t δ) : ‖g u x - g t x‖ ≤ ε :=
    ((g u - g t).norm_coe_le_norm x).trans (hb hu).2.le
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    (convex_ball t δ) (Metric.mem_ball_self hδ) hs
  have heq : (f s - f t - (s - t) • g t) x =
      (f s x - s • g t x) - (f t x - t • g t x) := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, sub_smul]
    abel
  simpa only [heq] using hm

namespace D
export Specs.SingleVariableAnalysis.Ch14.ProperDefinition (sectionValue)
end D
open Riemann

noncomputable def realExtension {a b : ℝ} (v : C(Icc a b, ℝ)) : ℝ → ℝ :=
  parameterSection .real (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩

noncomputable def complexExtension {a b : ℝ} (v : C(Icc a b, ℂ)) : ℝ → ℂ :=
  parameterSection .complex (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩

lemma realExtension_integrable {a b : ℝ} (hab : a ≤ b) (v : C(Icc a b, ℝ)) :
    RealIntegrable (realExtension v) a b := by
  apply real_integrable_of_continuousOn hab
  apply continuousOn_of_section_agreement v.continuous
  intro x
  exact section_on_interval .real (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩ x

lemma complexExtension_integrable {a b : ℝ} (hab : a ≤ b) (v : C(Icc a b, ℂ)) :
    ComplexIntegrable (complexExtension v) a b := by
  have hv : ContinuousOn (complexExtension v) (Icc a b) := by
    apply continuousOn_of_section_agreement v.continuous
    intro x
    exact section_on_interval .complex (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩ x
  exact ⟨real_integrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hv),
    real_integrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hv)⟩

noncomputable def realContinuousIntegral {a b : ℝ} (hab : a ≤ b) :
    C(Icc a b, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => realIntegral (realExtension v) (realExtension_integrable hab v)
      map_add' := by
        intro v w
        have he : realExtension (v + w) = fun x => realExtension v x + realExtension w x := by
          classical
          funext x
          by_cases hx : x ∈ Icc a b <;>
            simp [realExtension, parameterSection, S.sectionValue, D.sectionValue, hx]
        obtain ⟨h, hh⟩ := real_add_value (realExtension_integrable hab v)
          (realExtension_integrable hab w)
        simpa only [he] using hh
      map_smul' := by
        intro r v
        have he : realExtension (r • v) = fun x => r * realExtension v x := by
          classical
          funext x
          by_cases hx : x ∈ Icc a b <;>
            simp [realExtension, parameterSection, S.sectionValue, D.sectionValue, hx]
        obtain ⟨h, hh⟩ := real_mul_value (realExtension_integrable hab v) r
        simpa only [he, smul_eq_mul, RingHom.id_apply] using hh }
    (b - a) (by
      intro v
      obtain ⟨hn, hi, _⟩ := real_norm_estimate _ (realExtension_integrable hab v)
      apply hi.trans (realIntegral_le_mul_bound hn ?_)
      intro x hx
      have he := section_on_interval .real
        (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩ ⟨x, hx⟩
      change ‖realExtension v x‖ ≤ ‖v‖
      rw [show realExtension v x = v ⟨x, hx⟩ from he]
      exact v.norm_coe_le_norm _)

noncomputable def complexContinuousIntegral {a b : ℝ} (hab : a ≤ b) :
    C(Icc a b, ℂ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => complexIntegral (complexExtension v) (complexExtension_integrable hab v)
      map_add' := by
        intro v w
        have he : complexExtension (v + w) = fun x => complexExtension v x + complexExtension w x := by
          classical
          funext x
          by_cases hx : x ∈ Icc a b <;>
            simp [complexExtension, parameterSection, S.sectionValue, D.sectionValue, hx]
        obtain ⟨h, hh⟩ := complex_add_value (complexExtension_integrable hab v)
          (complexExtension_integrable hab w)
        simpa only [he] using hh
      map_smul' := by
        intro r v
        have he : complexExtension (r • v) = fun x => (r : ℂ) * complexExtension v x := by
          classical
          funext x
          by_cases hx : x ∈ Icc a b <;>
            simp [complexExtension, parameterSection, S.sectionValue, D.sectionValue, hx,
              Complex.real_smul]
        obtain ⟨h, hh⟩ := complex_mul_value (complexExtension_integrable hab v) (r : ℂ)
        simpa only [he, Complex.real_smul, RingHom.id_apply] using hh }
    (b - a) (by
      intro v
      obtain ⟨hn, hi, _⟩ := complex_norm_estimate _ (complexExtension_integrable hab v)
      apply hi.trans (realIntegral_le_mul_bound hn ?_)
      intro x hx
      have he := section_on_interval .complex
        (fun x (_ : (Set.univ : Set ℝ)) => v x) ⟨0, trivial⟩ ⟨x, hx⟩
      change ‖complexExtension v x‖ ≤ ‖v‖
      rw [show complexExtension v x = v ⟨x, hx⟩ from he]
      exact v.norm_coe_le_norm _)

/-- Bundle spatial sections only where joint continuity is given, and use the
zero continuous map elsewhere. This imposes no regularity outside J. -/
noncomputable def sectionsOn {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] [Zero E] (J : Set ℝ) (f : ℝ → X → E)
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ)) : ℝ → C(X, E) := by
  classical
  intro t
  exact if ht : t ∈ J then
    ⟨f t, hf.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨ht, mem_univ _⟩)⟩ else 0

lemma sectionsOn_apply {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] [Zero E] {J : Set ℝ} {f : ℝ → X → E}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ)) {t : ℝ} (ht : t ∈ J) (x : X) :
    sectionsOn J f hf t x = f t x := by
  classical
  simp only [sectionsOn, dite_eq_left ht]
  rfl

lemma sectionsOn_continuousOn {X E : Type*} [TopologicalSpace X]
    [TopologicalSpace E] [Zero E] [LocallyCompactSpace X]
    {J : Set ℝ} {f : ℝ → X → E}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ)) :
    ContinuousOn (sectionsOn J f hf) J := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  apply hf.congr
  intro p hp
  exact sectionsOn_apply hf hp.1 p.2

/-- Differentiating the bundled sections does not differentiate a zero extension
at the boundary: every point under consideration is interior to J. -/
theorem sectionsOn_hasDerivAt {X E : Type*} [TopologicalSpace X]
    [CompactSpace X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Set ℝ} (hJ : IsOpen J) {f g : ℝ → X → E}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (sectionsOn J f hf) (sectionsOn J g hg t) t := by
  apply continuous_sections_hasDerivAt hJ (t := t) ?_ ht
    ((sectionsOn_continuousOn hg t ht).continuousAt (hJ.mem_nhds ht))
  intro u hu x
  rw [sectionsOn_apply hg hu]
  apply (hd u hu x).congr_of_eventuallyEq
  filter_upwards [hJ.mem_nhds hu] with s hs
  exact sectionsOn_apply hf hs x

/-- Applying any bounded real linear functional to the section family preserves
its derivative and gives a continuous derivative. -/
theorem integral_of_sections {X E V : Type*} [TopologicalSpace X]
    [CompactSpace X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {J : Set ℝ} (hJ : IsOpen J) {f g : ℝ → X → E}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ))
    (hg : ContinuousOn (Function.uncurry g) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => f s x) (g t x) t)
    (I : C(X, E) →L[ℝ] V) (F G : ℝ → V)
    (hF : ∀ t ∈ J, F t = I (sectionsOn J f hf t))
    (hG : ∀ t ∈ J, G t = I (sectionsOn J g hg t)) :
    ContDiffOn ℝ 1 F J ∧ ContinuousOn G J ∧ ∀ t ∈ J, HasDerivAt F (G t) t := by
  have hder (t : ℝ) (ht : t ∈ J) : HasDerivAt F (G t) t := by
    rw [hG t ht]
    apply (I.hasFDerivAt.comp_hasDerivAt t (sectionsOn_hasDerivAt hJ hf hg hd ht)).congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact hF s hs
  have hcont : ContinuousOn G J :=
    (I.continuous.comp_continuousOn (sectionsOn_continuousOn hg)).congr
      (fun t ht => hG t ht)
  refine ⟨?_, hcont, hder⟩
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hJ]
  refine ⟨fun t ht => (hder t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · simp
  · apply contDiffOn_zero.mpr
    exact hcont.congr (fun t ht => (hder t ht).deriv)

/-- Integral values are independent of a presentation of the same function. -/
lemma realIntegral_eq_of_eq {a b : ℝ} {f g : ℝ → ℝ}
    (hf : RealIntegrable f a b) (hg : RealIntegrable g a b) (he : f = g) :
    realIntegral f hf = realIntegral g hg := by
  subst g
  rfl

/-- Integral values are independent of a presentation of the same function. -/
lemma complexIntegral_eq_of_eq {a b : ℝ} {f g : ℝ → ℂ}
    (hf : ComplexIntegrable f a b) (hg : ComplexIntegrable g a b) (he : f = g) :
    complexIntegral f hf = complexIntegral g hg := by
  subst g
  rfl

/-- Identify the continuous-map construction with the original parameter section. -/
lemma real_section_extension_eq {a b : ℝ} {J : Set ℝ}
    {f : ℝ → Icc a b → ℝ}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ)) (t : J) :
    parameterSection .real (fun x t => f t.val x) t =
      realExtension (sectionsOn J f hf t.val) := by
  classical
  funext x
  change (if hx : x ∈ Icc a b then f t.val ⟨x, hx⟩ else (0 : ℝ)) =
    (if hx : x ∈ Icc a b then sectionsOn J f hf t.val ⟨x, hx⟩ else (0 : ℝ))
  split_ifs with hx
  · exact (sectionsOn_apply hf t.property ⟨x, hx⟩).symm
  · rfl

/-- K03.14.proper_derivative for real values and real parameter increments. -/
theorem real_proper_derivative :
    Specs.SingleVariableAnalysis.Ch14.ProperDerivative.realProperDerivative := by
  intro a b hab J hJ f g hf hg hd
  have hi (t : J) : SectionIntegrable .real (fun x t => f t.val x) t := by
    change RealIntegrable (parameterSection .real (fun x t => f t.val x) t) a b
    rw [real_section_extension_eq hf t]
    exact realExtension_integrable hab _
  have hgi (t : J) : SectionIntegrable .real (fun x t => g t.val x) t := by
    change RealIntegrable (parameterSection .real (fun x t => g t.val x) t) a b
    rw [real_section_extension_eq hg t]
    exact realExtension_integrable hab _
  refine ⟨hi, hgi, ?_⟩
  intro F G hF hG
  have hIv (t : J) :
      properFamily .real (fun x t => f t.val x) ⟨t, hi t⟩ =
        realContinuousIntegral hab (sectionsOn J f hf t.val) := by
    change realIntegral (parameterSection .real (fun x t => f t.val x) t) (hi t) =
      realIntegral (realExtension (sectionsOn J f hf t.val))
        (realExtension_integrable hab (sectionsOn J f hf t.val))
    exact realIntegral_eq_of_eq _ _ (real_section_extension_eq hf t)
  have hIgv (t : J) :
      properFamily .real (fun x t => g t.val x) ⟨t, hgi t⟩ =
        realContinuousIntegral hab (sectionsOn J g hg t.val) := by
    change realIntegral (parameterSection .real (fun x t => g t.val x) t) (hgi t) =
      realIntegral (realExtension (sectionsOn J g hg t.val))
        (realExtension_integrable hab (sectionsOn J g hg t.val))
    exact realIntegral_eq_of_eq _ _ (real_section_extension_eq hg t)
  exact integral_of_sections hJ hf hg hd (realContinuousIntegral hab) F G
    (fun t ht => (hF ⟨t, ht⟩).trans (hIv ⟨t, ht⟩))
    (fun t ht => (hG ⟨t, ht⟩).trans (hIgv ⟨t, ht⟩))

/-- The assumptions need only hold on the compact parameter neighborhood. -/
theorem real_compact_neighborhood_derivative :
    Specs.SingleVariableAnalysis.Ch14.ProperDerivative.realCompactNeighborhoodDerivative := by
  intro a b c d hab _hcd f g hf hg hd
  exact real_proper_derivative hab (Ioo c d) isOpen_Ioo f g
    (hf.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl))
    (hg.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)) hd

/-- Identify the continuous-map construction with the original parameter section. -/
lemma complex_section_extension_eq {a b : ℝ} {J : Set ℝ}
    {f : ℝ → Icc a b → ℂ}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ univ)) (t : J) :
    parameterSection .complex (fun x t => f t.val x) t =
      complexExtension (sectionsOn J f hf t.val) := by
  classical
  funext x
  change (if hx : x ∈ Icc a b then f t.val ⟨x, hx⟩ else (0 : ℂ)) =
    (if hx : x ∈ Icc a b then sectionsOn J f hf t.val ⟨x, hx⟩ else (0 : ℂ))
  split_ifs with hx
  · exact (sectionsOn_apply hf t.property ⟨x, hx⟩).symm
  · rfl

/-- K03.14.proper_derivative for complex values and real parameter increments. -/
theorem complex_proper_derivative :
    Specs.SingleVariableAnalysis.Ch14.ProperDerivative.complexProperDerivative := by
  intro a b hab J hJ f g hf hg hd
  have hi (t : J) : SectionIntegrable .complex (fun x t => f t.val x) t := by
    change ComplexIntegrable (parameterSection .complex (fun x t => f t.val x) t) a b
    rw [complex_section_extension_eq hf t]
    exact complexExtension_integrable hab _
  have hgi (t : J) : SectionIntegrable .complex (fun x t => g t.val x) t := by
    change ComplexIntegrable (parameterSection .complex (fun x t => g t.val x) t) a b
    rw [complex_section_extension_eq hg t]
    exact complexExtension_integrable hab _
  refine ⟨hi, hgi, ?_⟩
  intro F G hF hG
  have hIv (t : J) :
      properFamily .complex (fun x t => f t.val x) ⟨t, hi t⟩ =
        complexContinuousIntegral hab (sectionsOn J f hf t.val) := by
    change complexIntegral (parameterSection .complex (fun x t => f t.val x) t) (hi t) =
      complexIntegral (complexExtension (sectionsOn J f hf t.val))
        (complexExtension_integrable hab (sectionsOn J f hf t.val))
    exact complexIntegral_eq_of_eq _ _ (complex_section_extension_eq hf t)
  have hIgv (t : J) :
      properFamily .complex (fun x t => g t.val x) ⟨t, hgi t⟩ =
        complexContinuousIntegral hab (sectionsOn J g hg t.val) := by
    change complexIntegral (parameterSection .complex (fun x t => g t.val x) t) (hgi t) =
      complexIntegral (complexExtension (sectionsOn J g hg t.val))
        (complexExtension_integrable hab (sectionsOn J g hg t.val))
    exact complexIntegral_eq_of_eq _ _ (complex_section_extension_eq hg t)
  exact integral_of_sections hJ hf hg hd (complexContinuousIntegral hab) F G
    (fun t ht => (hF ⟨t, ht⟩).trans (hIv ⟨t, ht⟩))
    (fun t ht => (hG ⟨t, ht⟩).trans (hIgv ⟨t, ht⟩))

/-- The assumptions need only hold on the compact parameter neighborhood. -/
theorem complex_compact_neighborhood_derivative :
    Specs.SingleVariableAnalysis.Ch14.ProperDerivative.complexCompactNeighborhoodDerivative := by
  intro a b c d hab _hcd f g hf hg hd
  exact complex_proper_derivative hab (Ioo c d) isOpen_Ioo f g
    (hf.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl))
    (hg.mono (Set.prod_mono Ioo_subset_Icc_self Subset.rfl)) hd

end SingleVariableAnalysis.ParameterIntegral
