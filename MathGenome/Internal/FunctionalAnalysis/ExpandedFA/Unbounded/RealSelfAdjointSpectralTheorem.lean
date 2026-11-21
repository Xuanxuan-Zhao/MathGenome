import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealOperatorComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.RealMeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem

/-! The unrestricted real self-adjoint spectral theorem. The complex theorem
is descended to the original real Hilbert space through conjugation invariance.
The transport lemmas preserve every bounded real integral and the entire maximal
integral graph, including its domain. No separability or sign condition is used. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ENNReal
namespace ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
open SpectralMeasure
universe u v

/-- Self-adjointness includes the exact domain equality, so closedness follows
from closedness of the densely defined adjoint. -/
theorem selfAdjoint_isClosed : Spec.Closedness.{u} := by
  intro H _ _ _ A hd hs
  have hc := hilbertAdjoint_isClosed A hd
  change (HilbertAdjointSpec.adjointValue A).IsClosed at hc
  rwa [hs] at hc

/-- No self-adjointness assumption is needed for the real/complex real-axis
resolvent bridge. It uses actual two-sided inverses on the original domain. -/
theorem spectrum_complexification : Spec.SpectrumBridge.{u} := by
  intro H _ _ _ A
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  ext r
  change (¬ Nonempty (ResolventInverse A r)) ↔
    ¬ Nonempty (ResolventInverse (RealOperatorComplexification.complexify A) (r : ℂ))
  exact not_congr (RealOperatorComplexification.resolvent_equivalence A r)

/-- The intrinsic real spectrum is closed even if the resolvent is empty. -/
theorem isClosed_operatorSpectrum : Spec.SpectrumClosed.{u} := by
  intro H _ _ _ A
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  rw [spectrum_complexification H A]
  exact (UnboundedNormalSpectralTheorem.isClosed_operatorSpectrum
    (RealOperatorComplexification.complexify A)).preimage Complex.continuous_ofReal

/-- The accepted complex spectral theorem applies to the actual exact-domain
complexification. This intermediate result acts on H_C, not on H. -/
theorem complexification_representation : Spec.ComplexificationRepresentation.{u} := by
  intro H _ _ _ A hd hs
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  have hdc : Dense ((RealOperatorComplexification.complexify A).domain :
      Set (TraceIdeals.RealComplexification.Space H)) :=
    (RealOperatorComplexification.denselyDefined_iff A).mpr hd
  have hsc : HilbertAdjointSpec.adjointValue (RealOperatorComplexification.complexify A) =
      RealOperatorComplexification.complexify A :=
    (RealOperatorComplexification.selfAdjoint_iff A hd).mpr hs
  have hcc : (RealOperatorComplexification.complexify A).IsClosed :=
    (RealOperatorComplexification.isClosed_iff A).mpr (selfAdjoint_isClosed H A hd hs)
  exact (UnboundedNormalSpectralTheorem.selfadjoint_spectral
    (TraceIdeals.RealComplexification.Space H) (RealOperatorComplexification.complexify A)
    hdc hcc hsc).1

/-- Regularity is automatic for each finite Borel measure on the real line;
there is no common scalar control measure or separability assumption on H. -/
theorem regularity_for_every_realization : Spec.RegularityForEveryRealization.{u} := by
  intro H _ _ _ E C
  constructor
  · intro x
    letI := C.scalar_finite x
    infer_instance
  · intro x y
    have hfin : (C.coefficient x y).variation univ < ∞ :=
      (C.variation_bound x y).trans_lt ENNReal.ofReal_lt_top
    letI : IsFiniteMeasure (C.coefficient x y).variation := ⟨hfin⟩
    infer_instance

/-- The moment and norm-limit parts follow for any exact integral
representation from the existing real maximal-domain calculus. -/
theorem representation_consequences : Spec.RepresentationConsequences.{u} := by
  intro H _ _ _ A E C he
  refine ⟨he, ?_, ?_⟩
  · intro x
    rw [← he]
    simpa only [RealMeasurableSpectralCalculus.measurableIntegral,
      RealMeasurableSpectralCalculus.squareMoment, sq_abs] using
      RealMeasurableSpectralCalculus.maximal_domain C (fun t : ℝ => t) measurable_id x
  · intro x
    subst A
    exact RealMeasurableSpectralCalculus.truncations_converge C (fun t : ℝ => t)
      measurable_id x

section RealizationIndependence
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {E F : RealProjectionValuedMeasure S H}

/-- Only Borel values enter simple spectral integration. -/
theorem simpleIntegral_eq_of_same_measurable_values
    (h : ∀ B : Set S, MeasurableSet B → E B = F B) (f : SimpleFunc S ℝ) :
    realSimpleSpectralIntegral E f = realSimpleSpectralIntegral F f := by
  unfold realSimpleSpectralIntegral
  apply Finset.sum_congr rfl
  intro c hc
  rw [h (f ⁻¹' {c}) (f.measurableSet_fiber c)]

/-- Uniform simple approximation makes the bounded realization canonical
on every bounded measurable function, independently of all witness choices. -/
theorem boundedIntegral_eq_of_same_measurable_values
    (h : ∀ B : Set S, MeasurableSet B → E B = F B)
    (C : RealBoundedRealization E) (D : RealBoundedRealization F)
    (f : RealBoundedFunction S) : C.integral f = D.integral f := by
  obtain ⟨a, ha⟩ := C.simple_approximation f
  apply tendsto_nhds_unique (C.integral_uniform_limit f a ha)
  have he : (fun n => realSimpleSpectralIntegral E (a n)) =
      (fun n => realSimpleSpectralIntegral F (a n)) :=
    funext fun n => simpleIntegral_eq_of_same_measurable_values h (a n)
  rw [he]
  exact D.integral_uniform_limit f a ha

/-- Equality holds as partial operators, hence includes the convergence domain,
not just the values at already square-integrable vectors. -/
theorem measurableIntegral_eq_of_same_measurable_values
    (h : ∀ B : Set S, MeasurableSet B → E B = F B)
    (C : RealBoundedRealization E) (D : RealBoundedRealization F)
    (f : S → ℝ) (hf : Measurable f) :
    RealMeasurableSpectralCalculus.measurableIntegral C f hf =
      RealMeasurableSpectralCalculus.measurableIntegral D f hf := by
  have ht : RealMeasurableSpectralCalculus.truncatedOperator C f hf =
      RealMeasurableSpectralCalculus.truncatedOperator D f hf :=
    funext fun n => boundedIntegral_eq_of_same_measurable_values h C D _
  apply LinearPMap.ext
  · ext x
    change (∃ y, Tendsto (fun n => RealMeasurableSpectralCalculus.truncatedOperator C f hf n x)
      atTop (𝓝 y)) ↔ (∃ y, Tendsto
        (fun n => RealMeasurableSpectralCalculus.truncatedOperator D f hf n x) atTop (𝓝 y))
    rw [ht]
  · intro x hx hy
    change limUnder atTop (fun n => RealMeasurableSpectralCalculus.truncatedOperator C f hf n x) =
      limUnder atTop (fun n => RealMeasurableSpectralCalculus.truncatedOperator D f hf n x)
    rw [ht]

end RealizationIndependence
section Descent
open TraceIdeals.RealComplexification
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

/-- The canonical restriction uses the original inclusion and real projection. -/
def restrictOperator (T : Space H →L[ℂ] Space H) : H →L[ℝ] H :=
  realPart.comp ((T.restrictScalars ℝ).comp inclusion.toContinuousLinearMap)

/-- Commutation with conjugation is exactly what makes this a genuine
restriction, rather than an arbitrary compression. -/
theorem restriction_inclusion (T : Space H →L[ℂ] Space H)
    (hT : ∀ p, conjugation (T p) = T (conjugation p)) (x : H) :
    inclusion (restrictOperator T x) = T (inclusion x) := by
  have hfix : conjugation (T (inclusion x)) = T (inclusion x) := by
    rw [hT, (coordinates H).2.1 (inclusion x) |>.mpr ⟨x, rfl⟩]
  obtain ⟨y, hy⟩ := ((coordinates H).2.1 (T (inclusion x))).mp hfix
  have hr := congrArg TraceIdeals.RealComplexification.realPart hy
  change y = restrictOperator T x at hr
  exact (congrArg TraceIdeals.RealComplexification.inclusion hr).symm.trans hy

/-- Reconstruction on every complex vector, not only the included real vectors. -/
theorem restriction_complexifies (T : Space H →L[ℂ] Space H)
    (hT : ∀ p, conjugation (T p) = T (conjugation p)) :
    operator (restrictOperator T) = T :=
  (operator_unique (restrictOperator T) T fun x => (restriction_inclusion T hT x).symm).symm

/-- Descent of any conjugation invariant complex PVM. In a spectral-theorem
application its invariance still has to be proved from the original operator. -/
def descendPVM (E : ProjectionValuedMeasure S (Space H))
    (hE : ∀ B, MeasurableSet B → ∀ p, conjugation (E B p) = E B (conjugation p)) :
    RealProjectionValuedMeasure S H where
  toFun B := restrictOperator (E B)
  univ := by
    ext x
    change realPart (E univ (inclusion x)) = x
    rw [E.univ]
    rfl
  selfAdjoint B hB x y := by
    have h := ContinuousLinearMap.adjoint_inner_left (E B) (inclusion y) (inclusion x)
    have hstar : (E B).adjoint = E B := E.selfAdjoint B hB
    rw [hstar, ← restriction_inclusion (E B) (hE B hB) x,
      ← restriction_inclusion (E B) (hE B hB) y, inner_inclusion, inner_inclusion] at h
    exact congrArg Complex.re h
  inter B C hB hC := by
    ext x
    apply inclusion.injective
    change inclusion (restrictOperator (E B) (restrictOperator (E C) x)) =
      inclusion (restrictOperator (E (B ∩ C)) x)
    rw [restriction_inclusion (E B) (hE B hB),
      restriction_inclusion (E C) (hE C hC),
      restriction_inclusion (E (B ∩ C)) (hE _ (hB.inter hC))]
    exact congrArg (fun T : Space H →L[ℂ] Space H => T (inclusion x)) (E.inter B C hB hC)
  countablyAdditive B hB hd x := by
    change HasSum (fun n => TraceIdeals.RealComplexification.realPart (E (B n) (inclusion x)))
      (TraceIdeals.RealComplexification.realPart (E (⋃ n, B n) (inclusion x)))
    exact TraceIdeals.RealComplexification.realPart.hasSum (E.iUnion B hB hd (inclusion x))

theorem descendPVM_inclusion (E : ProjectionValuedMeasure S (Space H))
    (hE : ∀ B, MeasurableSet B → ∀ p, conjugation (E B p) = E B (conjugation p))
    (B : Set S) (hB : MeasurableSet B) (x : H) :
    inclusion (descendPVM E hE B x) = E B (inclusion x) :=
  restriction_inclusion (E B) (hE B hB) x

end Descent

section IntegralTransport
open TraceIdeals.RealComplexification MeasurableSpectralCalculus
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

theorem operator_decomposition (T : H →L[ℝ] H) (p : Space H) :
    operator T p = inclusion (T p.1) + Complex.I • inclusion (T p.2) :=
  decomposition (operator T p)

/-- Complexification of an arbitrary real PVM preserves strong additivity. -/
def complexifyPVM (E : RealProjectionValuedMeasure S H) :
    ProjectionValuedMeasure S (Space H) where
  toFun B := operator (E B)
  univ := by rw [E.univ]; exact operator_id
  selfAdjoint B hB := by
    change (operator (E B)).adjoint = operator (E B)
    rw [operator_adjoint, show (E B).adjoint = E B from E.star_eq hB]
  inter B C hB hC := by
    change (operator (E B)).comp (operator (E C)) = operator (E (B ∩ C))
    rw [← operator_comp]
    exact congrArg operator (E.inter B C hB hC)
  iUnion B hB hd p := by
    have h₁ := inclusion.toContinuousLinearMap.hasSum (E.countablyAdditive B hB hd p.1)
    have h₂ := inclusion.toContinuousLinearMap.hasSum (E.countablyAdditive B hB hd p.2)
    have hh := h₁.add (h₂.const_smul Complex.I)
    change HasSum (fun n => inclusion (E (B n) p.1) + Complex.I • inclusion (E (B n) p.2))
      (inclusion (E (⋃ n, B n) p.1) + Complex.I • inclusion (E (⋃ n, B n) p.2)) at hh
    simpa only [← operator_decomposition] using hh

/-- Real simple functions in a complex spectral integral have the same finite
fibre expansion, including their zero fibre. -/
theorem complex_simpleIntegral_ofReal (E : ProjectionValuedMeasure S (Space H))
    (f : SimpleFunc S ℝ) :
    SpectralMeasure.Spec.SimpleIntegralValue E (f.map Complex.ofReal) =
      ∑ c ∈ f.range, (c : ℂ) • E (f ⁻¹' {c}) :=
  E.simpleIntegral_map_of_zero f Complex.ofReal Complex.ofReal_zero

/-- Any compatible real/complex pair of PVMs has compatible simple integrals. -/
theorem simpleIntegral_inclusion {E : RealProjectionValuedMeasure S H}
    {F : ProjectionValuedMeasure S (Space H)}
    (h : ∀ B, MeasurableSet B → ∀ x, inclusion (E B x) = F B (inclusion x))
    (f : SimpleFunc S ℝ) (x : H) :
    inclusion (realSimpleSpectralIntegral E f x) =
      SpectralMeasure.Spec.SimpleIntegralValue F (f.map Complex.ofReal) (inclusion x) := by
  rw [complex_simpleIntegral_ofReal]
  simp only [realSimpleSpectralIntegral, sum_apply,
    smul_apply, map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [inclusion.map_smul, h _ (f.measurableSet_fiber c)]
  exact (IsScalarTower.algebraMap_smul ℂ c (F (f ⁻¹' {c}) (inclusion x))).symm

/-- Uniform approximation transports every bounded real symbol. Neither
realization has to be the canonical choice. -/
theorem boundedIntegral_inclusion {E : RealProjectionValuedMeasure S H}
    {F : ProjectionValuedMeasure S (Space H)}
    (h : ∀ B, MeasurableSet B → ∀ x, inclusion (E B x) = F B (inclusion x))
    (C : RealBoundedRealization E) (D : BoundedRealization F)
    (f : RealBoundedFunction S) (x : H) :
    inclusion (C.integral f x) = D.integral (fun s => (f s : ℂ)) (inclusion x) := by
  obtain ⟨a, ha⟩ := C.simple_approximation f
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (f s : ℂ)) := by
    obtain ⟨M, hM, hb⟩ := f.bounded
    exact ⟨Complex.measurable_ofReal.comp f.measurable, M, by simpa using hb⟩
  have hu : TendstoUniformly (fun n s => (a n s : ℂ)) (fun s => (f s : ℂ)) atTop := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.uniformContinuous.comp_tendstoUniformly ha
  have hr := inclusion.continuous.tendsto (C.integral f x) |>.comp
    ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _ |>.comp
      (C.integral_uniform_limit f a ha))
  have hc := (ContinuousLinearMap.apply ℂ (Space H) (inclusion x)).continuous.tendsto _ |>.comp
    (D.uniform_limit _ hf (fun n => (a n).map Complex.ofReal) hu)
  change Tendsto (fun n => inclusion (realSimpleSpectralIntegral E (a n) x)) atTop
    (𝓝 (inclusion (C.integral f x))) at hr
  change Tendsto (fun n => SpectralMeasure.Spec.SimpleIntegralValue F ((a n).map Complex.ofReal)
    (inclusion x)) atTop (𝓝 (D.integral (fun s => (f s : ℂ)) (inclusion x))) at hc
  have he : (fun n => inclusion (realSimpleSpectralIntegral E (a n) x)) =
      (fun n => SpectralMeasure.Spec.SimpleIntegralValue F ((a n).map Complex.ofReal)
        (inclusion x)) := funext fun n => simpleIntegral_inclusion h (a n) x
  rw [he] at hr
  exact tendsto_nhds_unique hr hc

/-- Inclusion compatibility on real vectors determines the complex operator
on every vector of the complexification. -/
theorem boundedIntegral_complexifies {E : RealProjectionValuedMeasure S H}
    {F : ProjectionValuedMeasure S (Space H)}
    (h : ∀ B, MeasurableSet B → ∀ x, inclusion (E B x) = F B (inclusion x))
    (C : RealBoundedRealization E) (D : BoundedRealization F)
    (f : RealBoundedFunction S) :
    operator (C.integral f) = D.integral (fun s => (f s : ℂ)) :=
  (operator_unique (C.integral f) _ (fun x => (boundedIntegral_inclusion h C D f x).symm)).symm

/-- Truncation commutes with the scalar embedding, with precisely the same
absolute-value cutoff on the original base. -/
theorem truncation_ofReal (f : S → ℝ) (hf : Measurable f) (n : ℕ) :
    (fun s => (RealMeasurableSpectralCalculus.truncation f hf n s : ℂ)) =
      MeasurableSpectralCalculus.truncation (fun s => (f s : ℂ)) n := by
  funext s
  simp only [RealMeasurableSpectralCalculus.truncation,
    RealMeasurableSpectralCalculus.truncationSet, MeasurableSpectralCalculus.truncation,
    Complex.norm_real, Real.norm_eq_abs]
  by_cases hs : |f s| ≤ (n : ℝ) <;> simp [hs]

/-- The maximal integral graph, including its entire domain, complexifies.
This assertion is conditional only on the proved bounded PVM intertwining,
not on an unbounded spectral witness or a graph certificate. -/
theorem measurableIntegral_complexifies {E : RealProjectionValuedMeasure S H}
    {F : ProjectionValuedMeasure S (Space H)}
    (h : ∀ B, MeasurableSet B → ∀ x, inclusion (E B x) = F B (inclusion x))
    (C : RealBoundedRealization E) (D : BoundedRealization F)
    (f : S → ℝ) (hf : Measurable f) :
    RealOperatorComplexification.complexify
        (RealMeasurableSpectralCalculus.measurableIntegral C f hf) =
      MeasurableSpectralCalculus.measurableIntegral D (fun s => (f s : ℂ)) := by
  let T := RealMeasurableSpectralCalculus.truncatedOperator C f hf
  let U := fun n => D.integral (MeasurableSpectralCalculus.truncation (fun s => (f s : ℂ)) n)
  have ht (n : ℕ) : operator (T n) = U n := by
    dsimp [T, U, RealMeasurableSpectralCalculus.truncatedOperator]
    rw [boundedIntegral_complexifies h C D, truncation_ofReal]
  have hcoord (n : ℕ) (p : Space H) : U n p =
      inclusion (T n p.1) + Complex.I • inclusion (T n p.2) := by
    rw [← ht n, operator_decomposition]
  have hdom (p : Space H) : (∃ y, Tendsto (fun n => U n p) atTop (𝓝 y)) ↔
      (∃ a, Tendsto (fun n => T n p.1) atTop (𝓝 a)) ∧
      (∃ b, Tendsto (fun n => T n p.2) atTop (𝓝 b)) := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨⟨realPart y, ?_⟩, ⟨imagPart y, ?_⟩⟩
      · change Tendsto (fun n => T n p.1) atTop (𝓝 y.1)
        have hh := realPart.continuous.tendsto y |>.comp hy
        change Tendsto (fun n => (U n p).1) atTop (𝓝 y.1) at hh
        simpa only [← ht, operator_apply, Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair] using hh
      · change Tendsto (fun n => T n p.2) atTop (𝓝 y.2)
        have hh := imagPart.continuous.tendsto y |>.comp hy
        change Tendsto (fun n => (U n p).2) atTop (𝓝 y.2) at hh
        simpa only [← ht, operator_apply, Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair] using hh
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨inclusion a + Complex.I • inclusion b, ?_⟩
      simpa only [hcoord, Function.comp_def] using (inclusion.continuous.tendsto a |>.comp ha).add
        ((inclusion.continuous.tendsto b |>.comp hb).const_smul Complex.I)
  apply LinearPMap.ext
  · ext p
    exact (hdom p).symm
  · intro p hp hq
    apply tendsto_nhds_unique (l := (atTop : Filter ℕ))
    · have hh := (inclusion.continuous.tendsto _ |>.comp
        (tendsto_nhds_limUnder hp.1)).add
        ((inclusion.continuous.tendsto _ |>.comp
          (tendsto_nhds_limUnder hp.2)).const_smul Complex.I)
      change Tendsto (fun n => U n p) atTop (𝓝
        (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair H
          (limUnder atTop (fun n => T n p.1)) (limUnder atTop (fun n => T n p.2))))
      rw [decomposition (Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair H _ _)]
      simpa only [hcoord, Function.comp_def, T, Hilbert.PreHilbertCompactSpectral.Spec.Complexification.complexPair] using hh
    · exact tendsto_nhds_limUnder hq

/-- Actual descended and complex scalar measures agree at the original real
vectors, so square integrability refers to the original real domain. -/
theorem scalarMeasure_inclusion {E : RealProjectionValuedMeasure S H}
    {F : ProjectionValuedMeasure S (Space H)}
    (h : ∀ B, MeasurableSet B → ∀ x, inclusion (E B x) = F B (inclusion x))
    (C : RealBoundedRealization E) (D : BoundedRealization F) (x : H) :
    C.scalar x = D.measure (inclusion x) := by
  apply Measure.ext
  intro B hB
  rw [C.scalar_apply x B hB, D.measure_apply _ B hB, ← h B hB, inclusion.norm_map]

end IntegralTransport


section Conjugation
open TraceIdeals.RealComplexification MeasurableSpectralCalculus
open Hilbert.PreHilbertCompactSpectral.Spec.Complexification (complexPair ip)
variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

@[simp] theorem conjugation_involutive (p : Space H) : conjugation (conjugation p) = p :=
  (coordinates H).2.2.1 p

theorem conjugation_smul (a : ℂ) (p : Space H) :
    conjugation (a • p) = star a • conjugation p := (coordinates H).2.2.2.1 a p

theorem inner_conjugation (p q : Space H) :
    inner ℂ (conjugation p) (conjugation q) = star (inner ℂ p q) := by
  change ip H (complexPair H p.1 (-p.2)) (complexPair H q.1 (-q.2)) = star (ip H p q)
  apply Complex.ext <;> simp [ip, complexPair, sub_eq_add_neg, add_comm]

/-- Conjugating twice by the canonical real conjugation is complex linear. -/
def conjugateOperator (T : Space H →L[ℂ] Space H) : Space H →L[ℂ] Space H :=
  ({ toFun := fun p => conjugation (T (conjugation p))
     map_add' := by intro p q; simp only [map_add]
     map_smul' := by
       intro a p
       simp only [conjugation_smul, map_smul, star_star, RingHom.id_apply]
    } : Space H →ₗ[ℂ] Space H).mkContinuous ‖T‖ (fun p => by
      change ‖conjugation (T (conjugation p))‖ ≤ ‖T‖ * ‖p‖
      rw [conjugation.norm_map, ← conjugation.norm_map p]
      exact T.le_opNorm _)

@[simp] theorem conjugateOperator_apply (T : Space H →L[ℂ] Space H) (p : Space H) :
    conjugateOperator T p = conjugation (T (conjugation p)) := rfl

/-- Conjugation of a complex PVM uses only its PVM axioms. -/
def conjugatePVM (E : ProjectionValuedMeasure S (Space H)) :
    ProjectionValuedMeasure S (Space H) where
  toFun B := conjugateOperator (E B)
  univ := by
    ext p
    change conjugation (E univ (conjugation p)) = p
    rw [E.univ]
    exact conjugation_involutive p
  selfAdjoint B hB := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro p q
    change inner ℂ (conjugation (E B (conjugation p))) q =
      inner ℂ p (conjugation (E B (conjugation q)))
    rw [← conjugation_involutive q, inner_conjugation,
      conjugation_involutive q, ← conjugation_involutive p, inner_conjugation,
      conjugation_involutive p]
    exact congrArg star ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (E.selfAdjoint B hB)) _ _)
  inter B C hB hC := by
    ext p
    change conjugation (E B (conjugation (conjugation (E C (conjugation p))))) =
      conjugation (E (B ∩ C) (conjugation p))
    rw [conjugation_involutive]
    exact congrArg conjugation (congrArg (fun T : Space H →L[ℂ] Space H => T (conjugation p))
      (E.inter B C hB hC))
  iUnion B hB hd p := conjugation.toContinuousLinearMap.hasSum (E.iUnion B hB hd (conjugation p))

/-- Real-linear intertwiners suffice for integrals of real symbols. -/
theorem boundedIntegral_intertwines_real
    {E F : ProjectionValuedMeasure S (Space H)}
    (L : Space H →L[ℝ] Space H)
    (h : ∀ B, MeasurableSet B → ∀ p, L (E B p) = F B (L p))
    (C : BoundedRealization E) (D : BoundedRealization F)
    (f : RealBoundedFunction S) (p : Space H) :
    L (C.integral (fun s => (f s : ℂ)) p) = D.integral (fun s => (f s : ℂ)) (L p) := by
  let a := f.floorApprox
  have ha := f.tendstoUniformly_floorApprox
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable (fun s => (f s : ℂ)) := by
    obtain ⟨M, hM, hb⟩ := f.bounded
    exact ⟨Complex.measurable_ofReal.comp f.measurable, M, by simpa using hb⟩
  have hu : TendstoUniformly (fun n s => (a n s : ℂ)) (fun s => (f s : ℂ)) atTop := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.uniformContinuous.comp_tendstoUniformly ha
  have he (n : ℕ) :
      L (SpectralMeasure.Spec.SimpleIntegralValue E ((a n).map Complex.ofReal) p) =
      SpectralMeasure.Spec.SimpleIntegralValue F ((a n).map Complex.ofReal) (L p) := by
    rw [complex_simpleIntegral_ofReal, complex_simpleIntegral_ofReal]
    simp only [sum_apply, smul_apply]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have hs (r : ℝ) (q : Space H) : (r : ℂ) • q = r • q :=
      IsScalarTower.algebraMap_smul (R := ℝ) ℂ r q
    rw [hs, hs, L.map_smul, h _ ((a n).measurableSet_fiber c)]
  have hc := L.continuous.tendsto _ |>.comp
    ((ContinuousLinearMap.apply ℂ (Space H) p).continuous.tendsto _ |>.comp
      (C.uniform_limit _ hf (fun n => (a n).map Complex.ofReal) hu))
  have hd := (ContinuousLinearMap.apply ℂ (Space H) (L p)).continuous.tendsto _ |>.comp
    (D.uniform_limit _ hf (fun n => (a n).map Complex.ofReal) hu)
  change Tendsto (fun n => L (SpectralMeasure.Spec.SimpleIntegralValue E ((a n).map Complex.ofReal) p))
    atTop (𝓝 (L (C.integral (fun s => (f s : ℂ)) p))) at hc
  change Tendsto (fun n => SpectralMeasure.Spec.SimpleIntegralValue F ((a n).map Complex.ofReal) (L p))
    atTop (𝓝 (D.integral (fun s => (f s : ℂ)) (L p))) at hd
  simp only [he] at hc
  exact tendsto_nhds_unique hc hd


/-- The maximal real-symbol integral is transported by conjugation, including
both implications of convergence, not merely values on a proposed domain. -/
theorem conjugate_integral_graph
    {E : ProjectionValuedMeasure S (Space H)}
    (C : BoundedRealization E) (D : BoundedRealization (conjugatePVM E))
    (f : S → ℝ) (hf : Measurable f) (p q : Space H) :
    (p, q) ∈ (measurableIntegral D (fun s => (f s : ℂ))).graph ↔
      (conjugation p, conjugation q) ∈
        (measurableIntegral C (fun s => (f s : ℂ))).graph := by
  have hb (n : ℕ) : ∀ p, conjugation
      (C.integral (truncation (fun s => (f s : ℂ)) n) p) =
      D.integral (truncation (fun s => (f s : ℂ)) n) (conjugation p) := by
    intro p
    rw [← truncation_ofReal f hf n]
    exact boundedIntegral_intertwines_real conjugation.toContinuousLinearMap
      (fun B hB p => by
        change conjugation (E B p) = conjugation (E B (conjugation (conjugation p)))
        rw [conjugation_involutive])
      C D (RealMeasurableSpectralCalculus.truncation f hf n) p
  have hb' (n : ℕ) (p : Space H) : conjugation
      (D.integral (truncation (fun s => (f s : ℂ)) n) p) =
      C.integral (truncation (fun s => (f s : ℂ)) n) (conjugation p) := by
    have hh := congrArg conjugation (hb n (conjugation p))
    simpa only [conjugation_involutive] using hh.symm
  change (p, q) ∈ (limitOperator _).graph ↔ (conjugation p, conjugation q) ∈ (limitOperator _).graph
  rw [mem_limitOperator_graph_iff, mem_limitOperator_graph_iff]
  constructor
  · intro h
    have h' := conjugation.continuous.tendsto q |>.comp h
    simpa only [Function.comp_def, hb', conjugation_involutive] using h'
  · intro h
    have h' := conjugation.continuous.tendsto (conjugation q) |>.comp h
    simpa only [Function.comp_def, hb, conjugation_involutive] using h'

/-- Conjugation invariance of every real-base spectral representation of the
complexification follows from complex uniqueness after pushforward. -/
theorem spectralProjections_conjugation
    (A : Operator ℝ H H) (hd : Dense (A.domain : Set H))
    (hs : HilbertAdjointSpec.adjointValue A = A)
    (E : ProjectionValuedMeasure ℝ (Space H))
    (hE : UnboundedNormalSpectralTheorem.RealResolves (RealOperatorComplexification.complexify A) E) :
    ∀ B, MeasurableSet B → ∀ p, conjugation (E B p) = E B (conjugation p) := by
  obtain ⟨C, heq, _⟩ := hE
  obtain ⟨D⟩ := exists_boundedRealization (conjugatePVM E)
  have heqD : measurableIntegral D (fun t : ℝ => (t : ℂ)) =
      RealOperatorComplexification.complexify A := by
    apply LinearPMap.eq_of_eq_graph
    ext ⟨p, q⟩
    rw [conjugate_integral_graph C D (fun t : ℝ => t) measurable_id p q, heq]
    rw [RealOperatorComplexification.graph_iff, RealOperatorComplexification.graph_iff]
    change ((p.1, q.1) ∈ A.graph ∧ (-p.2, -q.2) ∈ A.graph) ↔
      ((p.1, q.1) ∈ A.graph ∧ (p.2, q.2) ∈ A.graph)
    simp only [show (-p.2, -q.2) = -(p.2, q.2) from rfl, neg_mem_iff]
  let N := RealOperatorComplexification.complexify A
  let F := E.map Complex.ofReal Complex.measurable_ofReal
  let G := (conjugatePVM E).map Complex.ofReal Complex.measurable_ofReal
  have hf : UnboundedNormalSpectralTheorem.Resolves N F :=
    UnboundedNormalSpectralTheorem.resolves_of_integral_eq N F (C.map _ Complex.measurable_ofReal) heq
  have hg : UnboundedNormalSpectralTheorem.Resolves N G :=
    UnboundedNormalSpectralTheorem.resolves_of_integral_eq N G (D.map _ Complex.measurable_ofReal) heqD
  have hdc : Dense (N.domain : Set (Space H)) := (RealOperatorComplexification.denselyDefined_iff A).mpr hd
  have hsc : HilbertAdjointSpec.adjointValue N = N := (RealOperatorComplexification.selfAdjoint_iff A hd).mpr hs
  have hcc : N.IsClosed := (RealOperatorComplexification.isClosed_iff A).mpr (selfAdjoint_isClosed H A hd hs)
  have hu := (UnboundedNormalSpectralTheorem.spectral_uniqueness_and_support
    (Space H) N hdc hcc (by rw [hsc]) F hf).2 G hg
  intro B hB p
  have hb := hu (Complex.re ⁻¹' B) (Complex.continuous_re.measurable hB)
  have hbset : Complex.ofReal ⁻¹' (Complex.re ⁻¹' B) = B := by ext t; simp
  have hb' : E B = conjugatePVM E B := by
    change E (Complex.ofReal ⁻¹' (Complex.re ⁻¹' B)) =
      conjugatePVM E (Complex.ofReal ⁻¹' (Complex.re ⁻¹' B)) at hb
    rwa [hbset] at hb
  have hh := congrArg (fun T : Space H →L[ℂ] Space H => T (conjugation p)) hb'
  simpa only [conjugatePVM, conjugateOperator_apply, conjugation_involutive] using hh.symm

/-- All bounded real integrals of the spectral PVM preserve the real form,
for every choice of bounded realization. -/
theorem spectralBoundedIntegral_conjugation
    (A : Operator ℝ H H) (hd : Dense (A.domain : Set H))
    (hs : HilbertAdjointSpec.adjointValue A = A)
    (E : ProjectionValuedMeasure ℝ (Space H))
    (hE : UnboundedNormalSpectralTheorem.RealResolves
      (RealOperatorComplexification.complexify A) E)
    (C : BoundedRealization E) (f : RealBoundedFunction ℝ) (p : Space H) :
    conjugation (C.integral (fun t => (f t : ℂ)) p) =
      C.integral (fun t => (f t : ℂ)) (conjugation p) :=
  boundedIntegral_intertwines_real conjugation.toContinuousLinearMap
    (spectralProjections_conjugation A hd hs E hE) C C f p

end Conjugation

section Assembly
open TraceIdeals.RealComplexification MeasurableSpectralCalculus
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace

/-- Every self-adjoint operator on the original real Hilbert space has an
unrestricted real spectral representation on its exact original domain. -/
theorem spectral_existence : Spec.SpectralExistence.{u} := by
  intro H _ _ _ A hd hs
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  obtain ⟨F, C, heq, hdom⟩ := complexification_representation H A hd hs
  let hF := spectralProjections_conjugation A hd hs F ⟨C, heq, hdom⟩
  let E := descendPVM F hF
  let D := E.boundedRealization
  have ht := measurableIntegral_complexifies (descendPVM_inclusion F hF) D C
    (fun t : ℝ => t) measurable_id
  have he : RealMeasurableSpectralCalculus.measurableIntegral D (fun t : ℝ => t)
      measurable_id = A := RealOperatorComplexification.complexify_injective (ht.trans heq)
  exact ⟨E, D, representation_consequences H A E D he⟩

/-- Complexifying a real maximal representation and pushing its base to ℂ
produces an exact maximal complex representation. -/
theorem complex_resolves_of_real_resolves (A : Operator ℝ H H)
    (E : RealProjectionValuedMeasure ℝ H) (hE : Resolves A E) :
    UnboundedNormalSpectralTheorem.Resolves (RealOperatorComplexification.complexify A)
      ((complexifyPVM E).map Complex.ofReal Complex.measurable_ofReal) := by
  obtain ⟨C, hC⟩ := hE
  obtain ⟨D⟩ := exists_boundedRealization (complexifyPVM E)
  apply UnboundedNormalSpectralTheorem.resolves_of_integral_eq _ _
    (D.map Complex.ofReal Complex.measurable_ofReal)
  change measurableIntegral D (fun t : ℝ => (t : ℂ)) = _
  rw [← measurableIntegral_complexifies
    (fun B hB x => (operator_inclusion (E B) x).symm) C D (fun t : ℝ => t) measurable_id]
  exact congrArg RealOperatorComplexification.complexify hC

/-- Complexification is faithful on bounded operators on the original space. -/
theorem operator_injective : Function.Injective (operator (H := H) (K := H)) := by
  intro T U h
  ext x
  apply inclusion.injective
  exact (operator_inclusion T x).symm.trans
    ((congrArg (fun V : Space H →L[ℂ] Space H => V (inclusion x)) h).trans (operator_inclusion U x))

/-- Intrinsic support and Borel uniqueness hold for all independently chosen
maximal real representations. -/
theorem spectral_uniqueness_and_support : Spec.SpectralUniquenessAndSupport.{u} := by
  intro H _ _ _ A hd hs E hE
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  let N := RealOperatorComplexification.complexify A
  let G := (complexifyPVM E).map Complex.ofReal Complex.measurable_ofReal
  have hg := complex_resolves_of_real_resolves A E hE
  have hdc : Dense (N.domain : Set (Space H)) := (RealOperatorComplexification.denselyDefined_iff A).mpr hd
  have hsc : HilbertAdjointSpec.adjointValue N = N := (RealOperatorComplexification.selfAdjoint_iff A hd).mpr hs
  have hcc : N.IsClosed := (RealOperatorComplexification.isClosed_iff A).mpr (selfAdjoint_isClosed H A hd hs)
  obtain ⟨hclosed, hnull, hopen⟩ := (UnboundedNormalSpectralTheorem.spectral_uniqueness_and_support
    (Space H) N hdc hcc (by rw [hsc]) G hg).1
  refine ⟨⟨isClosed_operatorSpectrum H A, ?_, ?_⟩, ?_⟩
  · apply operator_injective
    have hb : Complex.ofReal ⁻¹' (UnboundedNormalSpectralTheorem.operatorSpectrum N)ᶜ =
        (operatorSpectrum A)ᶜ := by rw [spectrum_complexification H A]; rfl
    change operator (E _) = operator 0
    rw [show operator (0 : H →L[ℝ] H) = 0 from by ext p; rfl]
    simpa only [G, ProjectionValuedMeasure.map_apply, complexifyPVM, hb] using hnull
  · intro U hU hmeet hn
    obtain ⟨r, hrU, hrS⟩ := hmeet
    have hmeet' : ((Complex.re ⁻¹' U) ∩ UnboundedNormalSpectralTheorem.operatorSpectrum N).Nonempty := by
      refine ⟨(r : ℂ), ?_, ?_⟩
      · simpa using hrU
      · have hb := congrArg (fun s : Set ℝ => r ∈ s) (spectrum_complexification H A)
        exact (Iff.of_eq hb).mp hrS
    apply hopen (Complex.re ⁻¹' U) (hU.preimage Complex.continuous_re) hmeet'
    change operator (E (Complex.ofReal ⁻¹' (Complex.re ⁻¹' U))) = 0
    have hb : Complex.ofReal ⁻¹' (Complex.re ⁻¹' U) = U := by ext t; simp
    rw [hb, hn]
    ext p
    rfl
  · intro F hF B hB
    have hf := complex_resolves_of_real_resolves A F hF
    have hu := (UnboundedNormalSpectralTheorem.spectral_uniqueness_and_support
      (Space H) N hdc hcc (by rw [hsc]) G hg).2 _ hf
    apply operator_injective
    have hb : Complex.ofReal ⁻¹' (Complex.re ⁻¹' B) = B := by ext t; simp
    simpa only [G, ProjectionValuedMeasure.map_apply, complexifyPVM, hb] using
      hu (Complex.re ⁻¹' B) (Complex.continuous_re.measurable hB)

/-- Complete real theorem, including regularity for every bounded realization. -/
theorem real_selfadjoint_spectral : Spec.RealTheorem.{u} :=
  ⟨selfAdjoint_isClosed, spectral_existence, spectral_uniqueness_and_support,
    regularity_for_every_realization⟩

/-- Both scalar fields, with the existing complex theorem unchanged. -/
theorem full_scalar_selfadjoint_spectral : Spec.FullScalarSelfAdjointTheorem.{u} :=
  ⟨UnboundedNormalSpectralTheorem.selfadjoint_spectral, real_selfadjoint_spectral⟩

end Assembly

end ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem
