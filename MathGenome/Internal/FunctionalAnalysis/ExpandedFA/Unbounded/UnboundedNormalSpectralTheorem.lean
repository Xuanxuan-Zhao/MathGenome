import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.NormalBoundedSpectralPieces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.ArbitraryCyclicSum
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.FugledeIntertwining
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal

namespace ExpandedFA.SpectralMeasure.ProjectionValuedMeasure
universe u v w
variable {S : Type u} {T : Type v} {H : Type w}
  [MeasurableSpace S] [MeasurableSpace T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pushforward of a PVM along a measurable map. Countable additivity is
strong (vectorwise); no operator-norm sum or scalar control measure is used. -/
def map (E : ProjectionValuedMeasure S H) (f : S → T) (hf : Measurable f) :
    ProjectionValuedMeasure T H where
  toFun B := E (f ⁻¹' B)
  univ := by simpa only [preimage_univ] using E.univ
  selfAdjoint B hB := E.selfAdjoint _ (hf hB)
  inter B C hB hC := by
    simpa only [preimage_inter] using E.inter _ _ (hf hB) (hf hC)
  iUnion B hB hdisj x := by
    have hd : Pairwise (fun n m => Disjoint (f ⁻¹' B n) (f ⁻¹' B m)) :=
      fun n m hnm => (hdisj hnm).preimage f
    simpa only [preimage_iUnion] using E.iUnion (fun n => f ⁻¹' B n)
      (fun n => hf (hB n)) hd x

@[simp] theorem map_apply (E : ProjectionValuedMeasure S H) (f : S → T)
    (hf : Measurable f) (B : Set T) : E.map f hf B = E (f ⁻¹' B) := rfl

end ExpandedFA.SpectralMeasure.ProjectionValuedMeasure

namespace ExpandedFA.SpectralMeasure.ProjectionValuedMeasure
universe u v w
variable {S : Type u} {T : Type v} {H : Type w}
  [MeasurableSpace S] [MeasurableSpace T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem simpleIntegral_map (E : ProjectionValuedMeasure S H)
    (p : S → T) (hp : Measurable p) (f : SimpleFunc T ℂ) :
    Spec.SimpleIntegralValue (E.map p hp) f =
      Spec.SimpleIntegralValue E (f.comp p hp) := by
  classical
  unfold Spec.SimpleIntegralValue
  symm
  apply Finset.sum_subset (f.range_comp_subset_range hp)
  intro c hc hnc
  have he : (f.comp p hp) ⁻¹' {c} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact hnc (SimpleFunc.mem_range.mpr ⟨s, hs⟩)
  change c • E (p ⁻¹' (f ⁻¹' {c})) = 0
  change c • E ((f.comp p hp) ⁻¹' {c}) = 0
  rw [he, E.map_empty, smul_zero]
end ExpandedFA.SpectralMeasure.ProjectionValuedMeasure

namespace ExpandedFA.Unbounded.MeasurableSpectralCalculus.BoundedRealization
universe u v w
variable {S : Type u} {T : Type v} {H : Type w}
  [MeasurableSpace S] [MeasurableSpace T]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SpectralMeasure
variable {E : ProjectionValuedMeasure S H}

def map (C : BoundedRealization E) (p : S → T) (hp : Measurable p) :
    BoundedRealization (E.map p hp) where
  measure x := Measure.map p (C.measure x)
  integral f := C.integral (f ∘ p)
  finite x := by have := C.finite x; infer_instance
  measure_apply x B hB := by
    rw [Measure.map_apply hp hB, C.measure_apply x _ (hp hB)]
    rfl
  simple f := by
    rw [E.simpleIntegral_map p hp f, ← C.simple]
    rfl
  uniform_limit f hf a ha := by
    have hfc : Spec.IsBoundedMeasurable (f ∘ p) :=
      ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩
    have h := C.uniform_limit (f ∘ p) hfc (fun n => (a n).comp p hp) (ha.comp p)
    simpa only [← E.simpleIntegral_map p hp] using h
  one := C.one
  add f g hf hg := C.add _ _ ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩
    ⟨hg.1.comp hp, hg.2.imp (fun C hC s => hC (p s))⟩
  smul c f hf := C.smul c _ ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩
  mul f g hf hg := C.mul _ _ ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩
    ⟨hg.1.comp hp, hg.2.imp (fun C hC s => hC (p s))⟩
  map_star f hf := C.map_star _ ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩
  bound f A hf hA hb := C.bound _ A
    ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩ hA (fun s => hb (p s))
  norm_sq f hf x := by
    rw [integral_map hp.aemeasurable (hf.1.norm.pow_const 2).aestronglyMeasurable]
    exact C.norm_sq _ ⟨hf.1.comp hp, hf.2.imp (fun C hC s => hC (p s))⟩ x

@[simp] theorem map_integral (C : BoundedRealization E) (p : S → T) (hp : Measurable p)
    (f : T → ℂ) : (C.map p hp).integral f = C.integral (f ∘ p) := rfl

theorem measurableIntegral_map (C : BoundedRealization E) (p : S → T)
    (hp : Measurable p) (f : T → ℂ) :
    measurableIntegral (C.map p hp) f = measurableIntegral C (f ∘ p) := rfl


theorem integral_apply_congr_ae (C : BoundedRealization E) (f g : S → ℂ)
    (hf : Spec.IsBoundedMeasurable f) (hg : Spec.IsBoundedMeasurable g) (x : H)
    (heq : f =ᵐ[C.measure x] g) : C.integral f x = C.integral g x := by
  have hd : Spec.IsBoundedMeasurable (f-g) := by
    simpa only [sub_eq_add_neg] using hf.add (by simpa using hg.smul (-1))
  have hz : (∫ s, ‖(f-g) s‖ ^ 2 ∂C.measure x) = 0 := by
    calc
      _ = ∫ _, (0 : ℝ) ∂C.measure x := integral_congr_ae (by
        filter_upwards [heq] with s hs
        simp [hs])
      _ = 0 := by simp
  rw [← C.norm_sq _ hd, C.sub f g hf hg] at hz
  have he : ‖C.integral f x - C.integral g x‖ = 0 := by
    change ‖C.integral f x - C.integral g x‖ ^ 2 = 0 at hz
    nlinarith [norm_nonneg (C.integral f x - C.integral g x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

theorem measurableIntegral_congr_ae (C : BoundedRealization E)
    (f g : S → ℂ) (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ x, f =ᵐ[C.measure x] g) : measurableIntegral C f = measurableIntegral C g := by
  unfold measurableIntegral
  congr 1
  funext n
  ext x
  apply C.integral_apply_congr_ae _ _ (boundedMeasurable_truncation hf n)
    (boundedMeasurable_truncation hg n) x
  filter_upwards [heq x] with s hs
  change (if ‖f s‖ ≤ (n : ℝ) then f s else 0) = (if ‖g s‖ ≤ (n : ℝ) then g s else 0)
  rw [hs]


theorem integral_truncation_star_of_selfAdjoint (C : BoundedRealization E)
    (f : S → ℂ) (hf : Measurable f)
    (hsa : (measurableIntegral C f).adjoint = measurableIntegral C f) (n : ℕ) :
    C.integral (truncation (star f) n) = C.integral (truncation f n) := by
  have hstar : measurableIntegral C (star f) = measurableIntegral C f :=
    (measurableIntegral_adjoint C hf).symm.trans hsa
  have hcut : ∀ n, cutoffIndicator (star f) n = cutoffIndicator f n := by
    intro n
    funext s
    simp [cutoffIndicator]
  let P := fun n => C.integral (cutoffIndicator f n)
  let T := fun n => C.integral (truncation f n)
  let Ps := fun n => C.integral (cutoffIndicator (star f) n)
  let Ts := fun n => C.integral (truncation (star f) n)
  ext x
  have hmem : (P n x, T n x) ∈ (measurableIntegral C (star f)).graph := by
    rw [hstar]
    exact (limitOperator T).mem_graph_iff.mpr
      ⟨⟨P n x, projection_mem_limitOperator_domain P T (C.cutoff_right hf) n x⟩,
        rfl, limitOperator_apply_projection P T (C.cutoff_right hf) n x⟩
  obtain ⟨a, ha, hb⟩ := (measurableIntegral C (star f)).mem_graph_iff.mp hmem
  have ha' : a = ⟨Ps n x, projection_mem_limitOperator_domain Ps Ts
      (C.cutoff_right (Complex.continuous_conj.measurable.comp hf)) n x⟩ := by
    apply Subtype.ext
    exact ha.trans (by simp only [P, Ps, hcut])
  rw [ha'] at hb
  exact (limitOperator_apply_projection Ps Ts (C.cutoff_right (Complex.continuous_conj.measurable.comp hf)) n x).symm.trans hb

theorem symbol_real_ae_of_selfAdjoint (C : BoundedRealization E)
    (f : S → ℂ) (hf : Measurable f)
    (hsa : (measurableIntegral C f).adjoint = measurableIntegral C f) (x : H) :
    ∀ᵐ s ∂C.measure x, (f s).im = 0 := by
  have hfs : Measurable (star f) := Complex.continuous_conj.measurable.comp hf
  have ht (n : ℕ) : truncation (star f) n =ᵐ[C.measure x] truncation f n := by
    have hs := boundedMeasurable_truncation hfs n
    have hn := boundedMeasurable_truncation hf n
    have hd : Spec.IsBoundedMeasurable (truncation (star f) n - truncation f n) := by
      simpa only [sub_eq_add_neg] using hs.add (by simpa using hn.smul (-1))
    have hInt : (∫ s, ‖(truncation (star f) n - truncation f n) s‖ ^ 2 ∂C.measure x) = 0 := by
      rw [← C.norm_sq _ hd, C.sub _ _ hs hn,
        C.integral_truncation_star_of_selfAdjoint f hf hsa n, sub_self, zero_apply, norm_zero,
        zero_pow (by decide)]
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun s => sq_nonneg ‖(truncation (star f) n - truncation f n) s‖)
      (C.integrable_norm_sq _ hd x)).mp hInt
    filter_upwards [hae] with s hs
    have hz : ‖(truncation (star f) n - truncation f n) s‖ = 0 := by
      change ‖(truncation (star f) n - truncation f n) s‖ ^ 2 = 0 at hs
      nlinarith [norm_nonneg ((truncation (star f) n - truncation f n) s)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hall : ∀ᵐ s ∂C.measure x, ∀ n, truncation (star f) n s = truncation f n s :=
    ae_all_iff.mpr ht
  filter_upwards [hall] with s hs
  obtain ⟨n, hn⟩ := exists_nat_ge ‖f s‖
  have he : star (f s) = f s := by
    have hh := hs n
    simpa only [truncation, Set.indicator_apply, Set.mem_ofPred_eq, Pi.star_apply,
      norm_star, hn, ite_eq_left] using hh
  have hi := congrArg Complex.im he
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

end ExpandedFA.Unbounded.MeasurableSpectralCalculus.BoundedRealization


namespace ExpandedFA.SpectralMeasure.ProjectionValuedMeasure
universe u v w
variable {S : Type u} [MeasurableSpace S]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Transport of a PVM by an actual unitary, preserving strong additivity. -/
def conjugate (E : ProjectionValuedMeasure S H) (U : H ≃ₗᵢ[ℂ] K) :
    ProjectionValuedMeasure S K where
  toFun B := U.conjStarAlgEquiv (E B)
  univ := by rw [E.univ, map_one]
  selfAdjoint B hB := by
    change star (U.conjStarAlgEquiv (E B)) = U.conjStarAlgEquiv (E B)
    rw [← map_star, E.selfAdjoint B hB]
  inter B C hB hC := by
    rw [← map_mul, E.inter B C hB hC]
  iUnion B hB hd x := by
    change HasSum (fun n => U (E (B n) (U.symm x))) (U (E (⋃ n, B n) (U.symm x)))
    exact (E.iUnion B hB hd (U.symm x)).map U.toContinuousLinearEquiv.toContinuousLinearMap
      U.continuous

@[simp] theorem conjugate_apply (E : ProjectionValuedMeasure S H)
    (U : H ≃ₗᵢ[ℂ] K) (B : Set S) :
    E.conjugate U B = U.conjStarAlgEquiv (E B) := rfl

@[simp] theorem simpleIntegral_conjugate (E : ProjectionValuedMeasure S H)
    (U : H ≃ₗᵢ[ℂ] K) (f : SimpleFunc S ℂ) :
    Spec.SimpleIntegralValue (E.conjugate U) f =
      U.conjStarAlgEquiv (Spec.SimpleIntegralValue E f) := by
  simp only [Spec.SimpleIntegralValue, map_sum, map_smul, conjugate_apply]

end ExpandedFA.SpectralMeasure.ProjectionValuedMeasure

namespace ExpandedFA.Unbounded.MeasurableSpectralCalculus.BoundedRealization
open SpectralMeasure
universe u v w
variable {S : Type u} [MeasurableSpace S]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {E : ProjectionValuedMeasure S H}

/-- Unitary transport preserves the bounded spectral calculus. -/
def conjugate (C : BoundedRealization E) (U : H ≃ₗᵢ[ℂ] K) :
    BoundedRealization (E.conjugate U) where
  measure x := C.measure (U.symm x)
  integral h := U.conjStarAlgEquiv (C.integral h)
  finite x := C.finite (U.symm x)
  measure_apply x B hB := by
    rw [C.measure_apply _ B hB]
    simp only [ProjectionValuedMeasure.conjugate_apply,
      LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U.norm_map]
  simple f := by
    rw [C.simple, ProjectionValuedMeasure.simpleIntegral_conjugate]
  uniform_limit f hf a ha := by
    have h := (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.tendsto
      (C.integral f)).comp (C.uniform_limit f hf a ha)
    change Tendsto (fun n => U.conjStarAlgEquiv (SpectralMeasure.Spec.SimpleIntegralValue E (a n)))
      atTop (nhds (U.conjStarAlgEquiv (C.integral f))) at h
    simpa only [ProjectionValuedMeasure.simpleIntegral_conjugate] using h
  one := by rw [C.one, map_one]
  add f g hf hg := by rw [C.add f g hf hg, map_add]
  smul c f hf := by rw [C.smul c f hf, map_smul]
  mul f g hf hg := by rw [C.mul f g hf hg, map_mul]
  map_star f hf := by
    rw [C.map_star f hf]
    exact StarHomClass.map_star _ _
  bound f r hf hr hfr := by
    apply ContinuousLinearMap.opNorm_le_bound _ hr
    intro x
    change ‖U (C.integral f (U.symm x))‖ ≤ r * ‖x‖
    rw [U.norm_map]
    calc
      _ ≤ ‖C.integral f‖ * ‖U.symm x‖ := (C.integral f).le_opNorm _
      _ ≤ r * ‖x‖ := by
        rw [U.symm.norm_map]
        exact mul_le_mul_of_nonneg_right (C.bound f r hf hr hfr) (norm_nonneg x)
  norm_sq f hf x := by
    change ‖U (C.integral f (U.symm x))‖ ^ 2 = _
    rw [U.norm_map]
    exact C.norm_sq f hf _

@[simp] theorem conjugate_integral (C : BoundedRealization E)
    (U : H ≃ₗᵢ[ℂ] K) (f : S → ℂ) :
    (C.conjugate U).integral f = U.conjStarAlgEquiv (C.integral f) := rfl

end ExpandedFA.Unbounded.MeasurableSpectralCalculus.BoundedRealization

namespace ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
open SpectralMeasure MeasurableSpectralCalculus
open NormalBoundedSpectralPiecesSpec OperatorDomainsSpec HilbertAdjointSpec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A local resolvent inverse obtained by a bounded invertible perturbation.
The inverse continues to land in the original operator domain. -/
def perturbResolvent {N : Operator ℂ H H} {z w : ℂ}
    (R : ResolventInverse N z) (a : (H →L[ℂ] H)ˣ)
    (ha : (a : H →L[ℂ] H) = 1 + (w - z) • R.inverse) :
    ResolventInverse N w where
  inverse := R.inverse.comp (↑(a⁻¹) : H →L[ℂ] H)
  mem_domain y := R.mem_domain _
  right_inverse y := by
    let t := (↑(a⁻¹) : H →L[ℂ] H) y
    have hR := R.right_inverse t
    have ha' : (a : H →L[ℂ] H) t = t + (w - z) • R.inverse t := by
      rw [ha]
      rfl
    have hay : (a : H →L[ℂ] H) t = y := by
      change ((a : H →L[ℂ] H) * (↑(a⁻¹) : H →L[ℂ] H)) y = y
      simp
    change w • R.inverse t - N ⟨R.inverse t, R.mem_domain t⟩ = y
    calc
      _ = (z • R.inverse t - N ⟨R.inverse t, R.mem_domain t⟩) +
          (w - z) • R.inverse t := by module
      _ = t + (w - z) • R.inverse t := by rw [hR]
      _ = y := by rw [← ha', hay]
  left_inverse x := by
    have hax : (a : H →L[ℂ] H) (z • (x : H) - N x) = w • (x : H) - N x := by
      rw [ha]
      change z • (x : H) - N x + (w - z) • R.inverse (z • (x : H) - N x) = _
      rw [R.left_inverse]
      module
    change R.inverse ((↑(a⁻¹) : H →L[ℂ] H) (w • (x : H) - N x)) = (x : H)
    rw [← hax]
    have hinv : (↑(a⁻¹) : H →L[ℂ] H) ((a : H →L[ℂ] H) (z • (x : H) - N x)) =
        z • (x : H) - N x := by
      change ((↑(a⁻¹) : H →L[ℂ] H) * (a : H →L[ℂ] H)) _ = _
      simp
    rw [hinv, R.left_inverse]

/-- The unbounded resolvent set is open, even when it is empty. -/
theorem isOpen_resolventSet (N : Operator ℂ H H) :
    IsOpen (resolventSetValue N) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨R⟩ := hz
  let F : ℂ → (H →L[ℂ] H) := fun w => 1 + (w - z) • R.inverse
  have hF : Continuous F := by fun_prop
  have hO : IsOpen {w | IsUnit (F w)} := Units.isOpen.preimage hF
  have hzO : z ∈ {w | IsUnit (F w)} := by simp [F]
  apply Filter.mem_of_superset (hO.mem_nhds hzO)
  rintro w ⟨a, ha⟩
  exact ⟨perturbResolvent R a ha⟩

/-- Closedness of the spectrum does not require a nonempty resolvent. -/
theorem isClosed_operatorSpectrum (N : Operator ℂ H H) :
    _root_.IsClosed (operatorSpectrum N) :=
  (isOpen_resolventSet N).isClosed_compl

/-- Extract the direct-sum representation from the accepted bounded-piece
construction. Each component is a closed reducing Hilbert subspace. -/
theorem bounded_normal_decomposition : Spec.BoundedDecompositionExists.{u} := by
  intro H _ _ _ N hd hc hn
  obtain ⟨B, C, P, _, _, _, _, R, hp, ho, hs, hdom, hg⟩ :=
    NormalBoundedSpectralPieces.bounded_spectral_pieces H N hd hc hn
  choose p heval using hp
  refine ⟨{
    Q := fun n => P (band B n)
    piece := p
    projection := ?_
    R := R
    evaluation := heval
    orthogonal := ho
    complete := hs
    domain := hdom
    graph := hg }⟩
  intro n
  have hm := NormalBoundedSpectralPieces.measurable_band B n
  exact ⟨P.selfAdjoint _ hm, by simpa only [inter_self] using P.inter _ _ hm hm⟩

/-- The direct-sum graph representation is an actual Hilbert direct sum,
with its canonical unitary onto H. The empty/zero summands require no exception. -/
theorem BoundedDecomposition.unitary {N : Operator ℂ H H}
    (d : BoundedDecomposition N) :
    ∃ U : lp (fun n => (d.Q n).range) 2 ≃ₗᵢ[ℂ] H,
      ∀ f, U f = ∑' n, ((f n : (d.Q n).range) : H) := by
  let D (n : ℕ) := (d.Q n).range
  letI : ∀ n, CompleteSpace (D n) := fun n =>
    (d.piece n).closed_range.isComplete.completeSpace_coe
  have hfam : OrthogonalFamily ℂ (fun n => D n) (fun n => (D n).subtypeₗᵢ) := by
    intro n m hnm x y
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := y.property
    change inner ℂ (x : H) (y : H) = 0
    rw [← ha, ← hb]
    exact d.orthogonal n m hnm a b
  have htotal : ⊤ ≤ (⨆ n, D n).topologicalClosure := by
    intro x _
    rw [← (d.complete x).tsum_eq]
    apply tsum_mem (Submodule.isClosed_topologicalClosure _)
    intro n
    exact Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem n ⟨x, rfl⟩)
  let hsum := IsHilbertSum.mkInternal D hfam htotal
  exact ⟨hsum.linearIsometryEquiv.symm, hsum.linearIsometryEquiv_symm_apply⟩

/-- A spectral representation's convergence domain is exactly the source's
square-integrability domain, independent of any choice of bounded realization. -/
theorem resolves_of_integral_eq (N : Operator ℂ H H)
    (E : ProjectionValuedMeasure ℂ H) (C : BoundedRealization E)
    (h : measurableIntegral C (fun z : ℂ => z) = N) : Resolves N E := by
  refine ⟨C, h, ?_⟩
  intro x
  rw [← h]
  exact measurableIntegral_domain C measurable_id x

/-- The same exact-domain bridge for the real-base specialization. -/
theorem realResolves_of_integral_eq (N : Operator ℂ H H)
    (E : ProjectionValuedMeasure ℝ H) (C : BoundedRealization E)
    (h : measurableIntegral C (fun t : ℝ => (t : ℂ)) = N) : RealResolves N E := by
  refine ⟨C, h, ?_⟩
  intro x
  rw [← h]
  exact measurableIntegral_domain C Complex.measurable_ofReal x

/-- The two source support assertions identify every spectral point by
nonvanishing on all its open neighborhoods. -/
theorem mem_spectrum_iff (N : Operator ℂ H H) (E : ProjectionValuedMeasure ℂ H)
    (h : SpectralSupport N E) (z : ℂ) :
    z ∈ operatorSpectrum N ↔
      ∀ U : Set ℂ, IsOpen U → z ∈ U → E U ≠ 0 := by
  obtain ⟨hc, hz, ho⟩ := h
  constructor
  · intro hmem U hU hzU
    exact ho U hU ⟨z, hzU, hmem⟩
  · intro hall
    by_contra hnot
    exact hall (operatorSpectrum N)ᶜ hc.isOpen_compl hnot hz

/-- The source's truncation construction follows from the representation,
with convergence in the ambient Hilbert norm for every domain vector. -/
theorem resolves_truncations (N : Operator ℂ H H)
    (E : ProjectionValuedMeasure ℂ H) (h : Resolves N E) :
    ∃ C : BoundedRealization E,
      (∀ x, x ∈ N.domain ↔ SquareIntegrable C (fun z : ℂ => z) x) ∧
      ∀ x : N.domain,
        Tendsto (fun n => C.integral (truncation (fun z : ℂ => z) n) x)
          atTop (nhds (N x)) := by
  obtain ⟨C, heq, hdom⟩ := h
  refine ⟨C, hdom, ?_⟩
  subst N
  intro x
  exact measurableIntegral_tendsto C _ x

/-! The multiplication representation is assembled from arbitrary families,
not only from countable or sigma-finite scalar measure spaces. -/

namespace OrthogonalMultiplication
universe v w
variable {I : Type v} {G : I → Type w}
  [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
  [∀ i, CompleteSpace (G i)]

theorem inner_component (A : ∀ i, G i →ₗᵢ[ℂ] H)
    (hA : IsHilbertSum ℂ G A) (i : I) (y : G i) (x : H) :
    inner ℂ (A i y) x = inner ℂ y (hA.linearIsometryEquiv x i) := by
  classical
  rw [← hA.linearIsometryEquiv_symm_apply_single y,
    ← hA.linearIsometryEquiv.symm_apply_apply x,
    hA.linearIsometryEquiv.symm.inner_map_map, lp.inner_single_left]
  simp

/-- Closedness supplies the full direct-sum graph, rather than merely
intertwining on finite-support vectors. The adjoint inclusions give the
reverse inclusion, without assuming summability of the component images. -/
theorem graph_iff (N : Operator ℂ H H) (hd : Dense (N.domain : Set H))
    (hc : N.IsClosed) (A : ∀ i, G i →ₗᵢ[ℂ] H) (hA : IsHilbertSum ℂ G A)
    (M : ∀ i, G i →L[ℂ] G i)
    (hN : ∀ i y, (A i y, A i (M i y)) ∈ N.graph)
    (hstar : ∀ i y, (A i y, A i ((M i).adjoint y)) ∈ (adjointValue N).graph)
    (x y : H) :
    (x, y) ∈ N.graph ↔
      ∀ i, hA.linearIsometryEquiv y i = M i (hA.linearIsometryEquiv x i) := by
  classical
  constructor
  · intro hxy i
    obtain ⟨hx, hNx⟩ := (ExpandedFA.Unbounded.mem_graph_iff N (x, y)).mp hxy
    apply ext_inner_left ℂ
    intro z
    obtain ⟨hz, hNz⟩ :=
      (ExpandedFA.Unbounded.mem_graph_iff (adjointValue N) _).mp (hstar i z)
    have heval := hilbertAdjoint_inner N hd
      (⟨A i z, hz⟩ : (adjointValue N).domain) ⟨x, hx⟩
    change inner ℂ (N ⟨x, hx⟩) (A i z) =
      inner ℂ x (adjointValue N ⟨A i z, hz⟩) at heval
    rw [hNx, hNz] at heval
    calc
      inner ℂ z (hA.linearIsometryEquiv y i) = inner ℂ (A i z) y :=
        (inner_component A hA i z y).symm
      _ = inner ℂ (A i ((M i).adjoint z)) x := by
        simpa only [Complex.star_def, inner_conj_symm] using congrArg star heval
      _ = inner ℂ ((M i).adjoint z) (hA.linearIsometryEquiv x i) :=
        inner_component A hA i _ x
      _ = inner ℂ z (M i (hA.linearIsometryEquiv x i)) :=
        (M i).adjoint_inner_left _ _
  · intro h
    have hs := (hA.hasSum_linearIsometryEquiv_symm (hA.linearIsometryEquiv x)).prodMk
      (hA.hasSum_linearIsometryEquiv_symm (hA.linearIsometryEquiv y))
    simp only [LinearIsometryEquiv.symm_apply_apply] at hs
    rw [← hs.tsum_eq]
    apply tsum_mem hc
    intro i
    rw [h i]
    exact hN i _

end OrthogonalMultiplication

namespace DisjointMultiplication
open ArbitraryCyclicSum
universe v w
variable {I : Type v} {S : I → Type w} [∀ i, MeasurableSpace (S i)]
  (μ : ∀ i, Measure (S i))

theorem inverse_component (f : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ))
    (i : I) :
    (DisjointL2.equivalence μ).symm f i = DisjointL2.component μ f i := by
  classical
  let v : lp (fun i => Lp ℂ 2 (μ i)) 2 :=
    ⟨DisjointL2.component μ f, DisjointL2.component_memℓp μ f⟩
  have hv : DisjointL2.equivalence μ v = f := by
    apply Lp.ext
    apply (DisjointL2.toUnion_ae μ v).trans
    apply (DisjointL2.ae_iff μ (measurableSet_eq_fun
      (DisjointL2.measurable_glue μ _) (Lp.stronglyMeasurable f).measurable)).mpr
    exact DisjointL2.component_ae μ f
  have heq : (DisjointL2.equivalence μ).symm f = v :=
    (DisjointL2.equivalence μ).symm_apply_eq.mpr hv.symm
  exact congrArg (fun a : lp (fun i => Lp ℂ 2 (μ i)) 2 => a i) heq

theorem inverse_ae (f : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ))
    (i : I) :
    (DisjointL2.equivalence μ).symm f i =ᵐ[μ i] fun s => f ⟨i, s⟩ := by
  rw [inverse_component]
  exact DisjointL2.component_ae μ f i

/-- For locally bounded multipliers the maximal domain is precisely the
square-summability of their component L² classes. No global bound is used. -/
theorem memLp_iff (g : Sigma S → ℂ) (hg : Measurable g)
    (M : ∀ i, Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
    (hM : ∀ i f, M i f =ᵐ[μ i] fun s => g ⟨i, s⟩ * f s)
    (f : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ)) :
    MemLp (fun s => g s * f s) 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ) ↔
      Memℓp (fun i => M i ((DisjointL2.equivalence μ).symm f i)) 2 := by
  classical
  let v := (DisjointL2.equivalence μ).symm f
  have hprod (i : I) : M i (v i) =ᵐ[μ i] fun s => g ⟨i, s⟩ * f ⟨i, s⟩ := by
    filter_upwards [hM i (v i), inverse_ae μ f i] with s hs ht
    rw [hs, ht]
  constructor
  · intro hf
    let k := hf.toLp (fun s => g s * f s)
    have hk (i : I) : DisjointL2.component μ k i = M i (v i) := by
      apply Lp.ext
      have hkae : k =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ] fun s => g s * f s :=
        MemLp.coeFn_toLp hf
      have hki : ∀ᵐ s ∂μ i, k ⟨i, s⟩ = g ⟨i, s⟩ * f ⟨i, s⟩ :=
        ((DisjointL2.ae_iff μ (measurableSet_eq_fun
        (Lp.stronglyMeasurable k).measurable
        (hg.mul (Lp.stronglyMeasurable f).measurable))).mp hkae) i
      filter_upwards [DisjointL2.component_ae μ k i, hki, hprod i] with s hs ht hu
      exact hs.trans (ht.trans hu.symm)
    have hfun : DisjointL2.component μ k = fun i => M i (v i) := funext hk
    rw [← hfun]
    exact DisjointL2.component_memℓp μ k
  · intro hf
    let w : lp (fun i => Lp ℂ 2 (μ i)) 2 := ⟨_, hf⟩
    have hae : DisjointL2.toUnion μ w =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ]
        fun s => g s * f s := by
      apply (DisjointL2.toUnion_ae μ w).trans
      apply (DisjointL2.ae_iff μ (measurableSet_eq_fun
        (DisjointL2.measurable_glue μ _) (hg.mul (Lp.stronglyMeasurable f).measurable))).mpr
      exact hprod
    exact (memLp_congr_ae hae).mp (Lp.memLp (DisjointL2.toUnion μ w))

end DisjointMultiplication

namespace NativeL2
universe v
variable {S : Type v} [MeasurableSpace S] (μ : Measure S)

/-- Multiplication by a bounded measurable function on arbitrary native L².
The measure need not be finite or sigma-finite. -/
def boundedMul (h : S → ℂ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := by
  classical
  exact if hh : SpectralMeasure.Spec.IsBoundedMeasurable h then
    (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2
      ((memLp_top_of_bound hh.1.aestronglyMeasurable hh.2.choose
        (Eventually.of_forall hh.2.choose_spec)).toLp h)
  else 0

theorem boundedMul_apply {h : S → ℂ}
    (hh : SpectralMeasure.Spec.IsBoundedMeasurable h) (f : Lp ℂ 2 μ) :
    boundedMul μ h f =ᵐ[μ] fun s => h s * f s := by
  let hlp := memLp_top_of_bound (μ := μ) hh.1.aestronglyMeasurable hh.2.choose
    (Eventually.of_forall hh.2.choose_spec)
  have hmul := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hlp.toLp h) f
  filter_upwards [hmul, MemLp.coeFn_toLp hlp] with s hs ht
  simpa only [boundedMul, dif_pos hh, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ht] using hs

theorem boundedMul_bound {h : S → ℂ}
    (hh : SpectralMeasure.Spec.IsBoundedMeasurable h) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s, ‖h s‖ ≤ K) : ‖boundedMul μ h‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_bound _ hK
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMul_apply μ hh f] with s hs
  rw [hs, norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound s) (norm_nonneg _)

theorem boundedMul_adjoint {h : S → ℂ}
    (hh : SpectralMeasure.Spec.IsBoundedMeasurable h) :
    (boundedMul μ h).adjoint = boundedMul μ (star h) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f k
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedMul_apply μ hh.star f, boundedMul_apply μ hh k] with s hs ht
  rw [hs, ht]
  simp [RCLike.inner_apply, mul_assoc, mul_comm, mul_left_comm]

/-- A version of dominated convergence stated on the actual L² classes.
The single dominating L² vector makes no assumption about the total measure. -/
theorem tendsto_of_dominated (F : ℕ → Lp ℂ 2 μ) (f b : Lp ℂ 2 μ)
    (hbound : ∀ n, ∀ᵐ s ∂μ, ‖F n s - f s‖ ≤ ‖b s‖)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (nhds (f s))) :
    Tendsto F atTop (nhds f) := by
  have hb : Integrable (fun s => ‖b s‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable b)).mp (Lp.memLp b)
  have ht : Tendsto (fun n => ∫ s, ‖F n s - f s‖ ^ 2 ∂μ) atTop (nhds 0) := by
    simpa only [Pi.pow_apply, Pi.sub_apply, integral_zero] using tendsto_integral_of_dominated_convergence (f := fun _ : S => (0 : ℝ))
      (fun s => ‖b s‖ ^ 2)
      (fun n => ((Lp.aestronglyMeasurable (F n)).sub
        (Lp.aestronglyMeasurable f)).norm.pow 2)
      hb (fun n => (hbound n).mono (fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) hs 2))
      (hlim.mono (fun s hs => by simpa using (hs.sub_const (f s)).norm.pow 2))
  have hn : Tendsto (fun n => ‖F n - f‖ ^ 2) atTop (nhds 0) := by
    convert ht using 1
    funext n
    rw [CyclicModel.l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F n) f] with s hs
    rw [hs]
    rfl
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn.sqrt

def projection (B : Set S) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  boundedMul μ (B.indicator (fun _ => 1))

theorem bounded_indicator (B : Set S) (hB : MeasurableSet B) :
    SpectralMeasure.Spec.IsBoundedMeasurable (B.indicator (fun _ => (1 : ℂ))) := by
  refine ⟨measurable_const.indicator hB, 1, fun s => ?_⟩
  classical
  by_cases hs : s ∈ B <;> simp [hs]

theorem projection_apply (B : Set S) (hB : MeasurableSet B) (f : Lp ℂ 2 μ) :
    projection μ B f =ᵐ[μ] B.indicator f := by
  filter_upwards [boundedMul_apply μ (bounded_indicator B hB) f] with s hs
  change boundedMul μ (B.indicator (fun _ => 1)) f s = _
  classical
  by_cases h : s ∈ B <;> simpa [h] using hs

theorem projection_univ : projection μ Set.univ = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  simpa using projection_apply μ Set.univ MeasurableSet.univ f

theorem projection_selfadjoint (B : Set S) (hB : MeasurableSet B) :
    IsSelfAdjoint (projection μ B) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  rw [projection, boundedMul_adjoint μ (bounded_indicator B hB)]
  congr 1
  funext s
  classical
  by_cases hs : s ∈ B <;> simp [hs]

theorem projection_inter (B C : Set S) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    projection μ B * projection μ C = projection μ (B ∩ C) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [projection_apply μ B hB (projection μ C f),
    projection_apply μ C hC f, projection_apply μ (B ∩ C) (hB.inter hC) f] with s hs ht hu
  change (projection μ B (projection μ C f)) s = _
  rw [hs, hu]
  classical
  by_cases hb : s ∈ B <;> by_cases hc : s ∈ C <;> simp_all

theorem projection_finite_sum (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun n m => Disjoint (B n) (B m))) (t : Finset ℕ)
    (f : Lp ℂ 2 μ) :
    (∑ n ∈ t, projection μ (B n) f) =ᵐ[μ] (⋃ n ∈ t, B n).indicator f := by
  classical
  apply (Lp.coeFn_finsetSum t (fun n => projection μ (B n) f)).trans
  have hproj := eventuallyEq_sum (s := t) (fun n _ => projection_apply μ (B n) (hB n) f)
  apply hproj.trans
  apply Eventually.of_forall
  intro s
  simp only [Finset.sum_apply]
  by_cases hex : ∃ n ∈ t, s ∈ B n
  · obtain ⟨n, hn, hs⟩ := hex
    rw [Finset.sum_eq_single n]
    · simp [hs, show s ∈ ⋃ n ∈ t, B n from mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, hs⟩⟩]
    · intro k hk hkn
      have hks : s ∉ B k := fun h => Set.disjoint_left.mp (hd hkn) h hs
      simp [hks]
    · exact fun h => (h hn).elim
  · have hnot : s ∉ ⋃ n ∈ t, B n := by simpa using hex
    rw [Set.indicator_of_notMem hnot]
    apply Finset.sum_eq_zero
    intro n hn
    exact Set.indicator_of_notMem (fun hs => hex ⟨n, hn, hs⟩) _

theorem projection_countable_sum (B : ℕ → Set S) (hB : ∀ n, MeasurableSet (B n))
    (hd : Pairwise (fun n m => Disjoint (B n) (B m))) (f : Lp ℂ 2 μ) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, projection μ (B n) f) atTop
      (nhds (projection μ (⋃ n, B n) f)) := by
  classical
  let F (N : ℕ) := ∑ n ∈ Finset.range N, projection μ (B n) f
  let k := projection μ (⋃ n, B n) f
  have hF (n : ℕ) := projection_finite_sum μ B hB hd (Finset.range n) f
  have hk := projection_apply μ (⋃ n, B n) (MeasurableSet.iUnion hB) f
  apply tendsto_of_dominated μ F k f
  · intro n
    filter_upwards [hF n, hk] with s hs ht
    rw [hs, ht]
    by_cases hsn : s ∈ ⋃ k ∈ Finset.range n, B k
    · have hsU : s ∈ ⋃ k, B k := by
        obtain ⟨k, hk, hsk⟩ := mem_iUnion₂.mp hsn
        exact mem_iUnion.mpr ⟨k, hsk⟩
      simp only [Set.indicator_of_mem hsn, Set.indicator_of_mem hsU, sub_self, norm_zero, norm_nonneg]
    · rw [Set.indicator_of_notMem hsn]
      by_cases hsU : s ∈ ⋃ k, B k
      · simp only [Set.indicator_of_mem hsU, zero_sub, norm_neg, le_refl]
      · simp only [Set.indicator_of_notMem hsU, sub_self, norm_zero, norm_nonneg]
  · have hfall : ∀ᵐ s ∂μ, ∀ n, F n s = (⋃ k ∈ Finset.range n, B k).indicator f s :=
      ae_all_iff.mpr hF
    filter_upwards [hfall, hk] with s hs ht
    apply tendsto_const_nhds.congr'
    by_cases hsU : s ∈ ⋃ k, B k
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hsU
      filter_upwards [eventually_gt_atTop j] with n hn
      have hsn : s ∈ ⋃ k ∈ Finset.range n, B k :=
        mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hn, hj⟩
      change (projection μ (⋃ n, B n) f) s = F n s
      rw [ht, hs n, Set.indicator_of_mem hsU, Set.indicator_of_mem hsn]
    · filter_upwards with n
      have hsn : s ∉ ⋃ k ∈ Finset.range n, B k := by
        intro h
        obtain ⟨k, _, hsk⟩ := mem_iUnion₂.mp h
        exact hsU (mem_iUnion.mpr ⟨k, hsk⟩)
      change (projection μ (⋃ n, B n) f) s = F n s
      rw [ht, hs n, Set.indicator_of_notMem hsU, Set.indicator_of_notMem hsn]

def projectionValuedMeasure : SpectralMeasure.ProjectionValuedMeasure S (Lp ℂ 2 μ) := by
  refine { toFun := projection μ
           univ := projection_univ μ
           selfAdjoint := projection_selfadjoint μ
           inter := projection_inter μ
           iUnion := ?_ }
  obtain ⟨E, hE⟩ := (SpectralMeasure.source_realization (projection μ)).mp
    ⟨projection_univ μ, projection_selfadjoint μ, projection_inter μ,
      projection_countable_sum μ⟩
  intro B hB hd x
  have h := E.iUnion B hB hd x
  change HasSum (fun n => E.toFun (B n) x) (E.toFun (⋃ n, B n) x) at h
  simpa only [hE] using h

@[simp] theorem projectionValuedMeasure_apply (B : Set S) :
    projectionValuedMeasure μ B = projection μ B := rfl

theorem simpleIntegral_eq_boundedMul (a : SimpleFunc S ℂ) :
    SpectralMeasure.Spec.SimpleIntegralValue (projectionValuedMeasure μ) a =
      boundedMul μ a := by
  classical
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hterm (c : ℂ) : (c • projection μ (a ⁻¹' {c}) f : Lp ℂ 2 μ) =ᵐ[μ]
      fun s => c * (a ⁻¹' {c}).indicator f s := by
    filter_upwards [Lp.coeFn_smul c (projection μ (a ⁻¹' {c}) f),
      projection_apply μ (a ⁻¹' {c}) (a.measurableSet_fiber c) f] with s hs ht
    simpa only [Pi.smul_apply, smul_eq_mul, ht] using hs
  have hsum := (Lp.coeFn_finsetSum a.range (fun c => c • projection μ (a ⁻¹' {c}) f)).trans
    (eventuallyEq_sum (fun c (_ : c ∈ a.range) => hterm c))
  have heq : SpectralMeasure.Spec.SimpleIntegralValue (projectionValuedMeasure μ) a f =
      ∑ c ∈ a.range, c • projection μ (a ⁻¹' {c}) f := by
    simp [SpectralMeasure.Spec.SimpleIntegralValue, ContinuousLinearMap.sum_apply]
  rw [heq]
  filter_upwards [hsum, boundedMul_apply μ (SpectralMeasure.Spec.IsBoundedMeasurable.simple a) f]
    with s hs ht
  rw [hs, ht]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single (a s)]
  · simp
  · intro c hc hne
    have hnot : s ∉ a ⁻¹' {c} := fun h => hne (Set.mem_singleton_iff.mp h).symm
    simp [hnot]
  · exact fun hn => (hn (a.mem_range_self s)).elim

theorem boundedMul_sub (f g : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g) :
    boundedMul μ (f - g) = boundedMul μ f - boundedMul μ g := by
  have hfg : SpectralMeasure.Spec.IsBoundedMeasurable (f-g) := by
    simpa only [sub_eq_add_neg] using hf.add (by simpa using hg.smul (-1))
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [boundedMul_apply μ hfg x, boundedMul_apply μ hf x,
    boundedMul_apply μ hg x, Lp.coeFn_sub (boundedMul μ f x) (boundedMul μ g x)]
    with s hs ht hu hv
  change boundedMul μ (f-g) x s = (boundedMul μ f x - boundedMul μ g x) s
  rw [hs, hv]
  simp only [Pi.sub_apply]
  rw [ht, hu]
  exact sub_mul _ _ _

theorem boundedMul_tendsto (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) (a : ℕ → SimpleFunc S ℂ)
    (ha : TendstoUniformly (fun n => a n) f atTop) :
    Tendsto (fun n => boundedMul μ (a n)) atTop (nhds (boundedMul μ f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have heps : 0 < ε / 2 := half_pos hε
  rw [Metric.tendstoUniformly_iff] at ha
  filter_upwards [ha (ε / 2) heps] with n hn
  rw [dist_eq_norm, ← boundedMul_sub μ _ _ (SpectralMeasure.Spec.IsBoundedMeasurable.simple _) hf]
  have hdiff : SpectralMeasure.Spec.IsBoundedMeasurable ((a n : S → ℂ) - f) := by
    simpa only [sub_eq_add_neg] using
      (SpectralMeasure.Spec.IsBoundedMeasurable.simple (a n)).add (by simpa using hf.smul (-1))
  apply lt_of_le_of_lt (boundedMul_bound μ hdiff (le_of_lt heps) ?_) (half_lt_self hε)
  intro s
  simpa only [Pi.sub_apply, dist_eq_norm, norm_sub_rev] using (hn s).le

theorem integral_eq_boundedMul (C : MeasurableSpectralCalculus.BoundedRealization
    (projectionValuedMeasure μ)) (f : S → ℂ)
    (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    C.integral f = boundedMul μ f := by
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx f hf
  have hleft := C.uniform_limit f hf a ha
  simp only [simpleIntegral_eq_boundedMul] at hleft
  exact tendsto_nhds_unique hleft (boundedMul_tendsto μ f hf a ha)

end NativeL2

namespace BoundedCyclicMultiplication
open ArbitraryCyclicSum
universe v
variable {S : Type v} [TopologicalSpace S] [CompactSpace S]
  [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]

theorem multiplier_adjoint (g : C(S, ℂ)) :
    (CyclicModel.Spec.multiplier μ g).adjoint =
      CyclicModel.Spec.multiplier μ (star g) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f k
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [CyclicModel.multiplier_apply μ (star g) f,
    CyclicModel.multiplier_apply μ g k] with s hs ht
  rw [hs, ht]
  simp [RCLike.inner_apply, mul_assoc, mul_comm, mul_left_comm]

theorem multiplier_normal (g : C(S, ℂ)) :
    IsStarNormal (CyclicModel.Spec.multiplier μ g) := by
  constructor
  rw [ContinuousLinearMap.star_eq_adjoint, multiplier_adjoint]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [CyclicModel.multiplier_apply μ (star g) (CyclicModel.Spec.multiplier μ g f),
    CyclicModel.multiplier_apply μ g (CyclicModel.Spec.multiplier μ (star g) f),
    CyclicModel.multiplier_apply μ g f,
    CyclicModel.multiplier_apply μ (star g) f] with s h1 h2 h3 h4
  change (CyclicModel.Spec.multiplier μ (star g) (CyclicModel.Spec.multiplier μ g f)) s =
    (CyclicModel.Spec.multiplier μ g (CyclicModel.Spec.multiplier μ (star g) f)) s
  rw [h1, h2, h3, h4]
  ring

end BoundedCyclicMultiplication

/-- Keep the finite cyclic measures of a bounded normal model separate.
This interface also records adjoint intertwining, which is needed to identify
the maximal domain after an unbounded family of such models is assembled. -/
theorem bounded_multiplication_family (T : H →L[ℂ] H) (hT : IsStarNormal T) :
    ∃ (I : Type u) (S : I → Type) (m : ∀ i, MeasurableSpace (S i))
      (μ : ∀ i, @Measure (S i) (m i)),
      letI := m
      (∀ i, IsFiniteMeasure (μ i)) ∧
      ∃ g : Sigma S → ℂ, Measurable g ∧
      ∃ (M : ∀ i, Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
        (A : ∀ i, Lp ℂ 2 (μ i) →ₗᵢ[ℂ] H),
        IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ i)) A ∧
        (∀ i f, M i f =ᵐ[μ i] fun s => g ⟨i, s⟩ * f s) ∧
        (∀ i f, A i (M i f) = T (A i f)) ∧
        (∀ i f, A i ((M i).adjoint f) = T.adjoint (A i f)) := by
  classical
  obtain ⟨E, hE, _⟩ := NormalPVM.normal_spectral_theorem H T hT
  obtain ⟨s, _, horth, _, htotal, _⟩ := ArbitraryCyclicSum.orthogonal_decomposition H T hT
  let μ : s → Measure (spectrum ℂ T) := fun e => E.diagonalMeasure e
  letI (e : s) : IsFiniteMeasure (μ e) := by dsimp [μ]; infer_instance
  choose U hU using fun e : s => ArbitraryCyclicSum.local_cyclic_model T hT E hE e
  let A (e : s) : Lp ℂ 2 (μ e) →ₗᵢ[ℂ] H :=
    (ArbitraryCyclicSum.Spec.cyclicSpace T e).subtypeₗᵢ.comp (U e).toLinearIsometry
  let M (e : s) : Lp ℂ 2 (μ e) →L[ℂ] Lp ℂ 2 (μ e) :=
    CyclicModel.Spec.multiplier (μ e) (CyclicModel.Spec.coordinate T)
  have hAorth : OrthogonalFamily ℂ (fun e : s => Lp ℂ 2 (μ e)) A := by
    intro e f hef x y
    exact (horth e.property f.property (fun h => hef (Subtype.ext h))).inner_eq
      (U e x).property (U f y).property
  have hArange (e : s) : LinearMap.range (A e).toLinearMap =
      ArbitraryCyclicSum.Spec.cyclicSpace T e := by
    ext x
    constructor
    · rintro ⟨f, rfl⟩
      exact (U e f).property
    · intro hx
      exact ⟨(U e).symm ⟨x, hx⟩,
        congrArg Subtype.val ((U e).apply_symm_apply ⟨x, hx⟩)⟩
  have hsum : IsHilbertSum ℂ (fun e : s => Lp ℂ 2 (μ e)) A :=
    IsHilbertSum.mk hAorth (by simp_rw [hArange]; exact le_of_eq htotal.symm)
  let g : (Σ _ : s, spectrum ℂ T) → ℂ := fun x => (x.2 : ℂ)
  have hg : Measurable g :=
    (ArbitraryCyclicSum.DisjointL2.measurable_iff _).mpr
      (fun _ => continuous_subtype_val.measurable)
  refine ⟨s, (fun _ => spectrum ℂ T), (fun _ => inferInstance), μ,
    (fun _ => inferInstance), g, hg, M, A, hsum, ?_, hU, ?_⟩
  · intro i f
    exact CyclicModel.multiplier_apply (μ i) (CyclicModel.Spec.coordinate T) f
  · intro i f
    have hinter : T.comp (A i).toContinuousLinearMap =
        (A i).toContinuousLinearMap.comp (M i) := by
      ext x
      exact (hU i x).symm
    have hadj := FugledeIntertwining.adjoint_intertwining H (Lp ℂ 2 (μ i))
      T (M i) (A i).toContinuousLinearMap
      (by
        apply ContinuousLinearMap.ext
        intro x
        change T.adjoint (T x) = T (T.adjoint x)
        simpa only [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using
          congrArg (fun B : H →L[ℂ] H => B x) hT.star_comm_self.eq)
      (by
        apply ContinuousLinearMap.ext
        intro x
        change (M i).adjoint (M i x) = M i ((M i).adjoint x)
        simpa only [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using
          congrArg (fun B : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i) => B x)
            (BoundedCyclicMultiplication.multiplier_normal (μ i)
              (CyclicModel.Spec.coordinate T)).star_comm_self.eq) hinter
    exact (congrArg (fun B : Lp ℂ 2 (μ i) →L[ℂ] H => B f) hadj).symm

/-- Convert an orthogonal family of finite-measure multiplication pieces
into a single maximal-domain multiplication model. -/
theorem multiplicationModel_of_family (N : Operator ℂ H H)
    (hd : Dense (N.domain : Set H)) (hc : N.IsClosed)
    {I : Type u} {S : I → Type} [m : ∀ i, MeasurableSpace (S i)]
    (μ : ∀ i, Measure (S i)) (hfinite : ∀ i, IsFiniteMeasure (μ i))
    (g : Sigma S → ℂ) (hg : Measurable g)
    (M : ∀ i, Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
    (A : ∀ i, Lp ℂ 2 (μ i) →ₗᵢ[ℂ] H)
    (hA : IsHilbertSum ℂ (fun i => Lp ℂ 2 (μ i)) A)
    (hM : ∀ i f, M i f =ᵐ[μ i] fun s => g ⟨i, s⟩ * f s)
    (hN : ∀ i f, (A i f, A i (M i f)) ∈ N.graph)
    (hstar : ∀ i f, (A i f, A i ((M i).adjoint f)) ∈ (adjointValue N).graph) :
    MultiplicationModel N := by
  classical
  let Q := ArbitraryCyclicSum.DisjointL2.equivalence μ
  let W := hA.linearIsometryEquiv
  let U : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ) ≃ₗᵢ[ℂ] H :=
    Q.symm.trans W.symm
  have hu (f : Lp ℂ 2 (ArbitraryCyclicSum.Spec.disjointMeasure μ)) :
      W (U f) = Q.symm f := W.apply_symm_apply _
  have hgraph := OrthogonalMultiplication.graph_iff N hd hc A hA M hN hstar
  refine ⟨I, S, m, μ, hfinite, g, hg, U, ?_, ?_⟩
  · intro f
    rw [DisjointMultiplication.memLp_iff μ g hg M hM f]
    constructor
    · intro hf
      have hx : (U f, N ⟨U f, hf⟩) ∈ N.graph :=
        N.mem_graph_iff.mpr ⟨⟨U f, hf⟩, rfl, rfl⟩
      have h := (hgraph _ _).mp hx
      change ∀ i, W (N ⟨U f, hf⟩) i = M i (W (U f) i) at h
      rw [hu] at h
      have heq : (fun i => M i (Q.symm f i)) = fun i => W (N ⟨U f, hf⟩) i :=
        funext (fun i => (h i).symm)
      rw [heq]
      exact lp.memℓp _
    · intro hf
      let w : lp (fun i => Lp ℂ 2 (μ i)) 2 := ⟨_, hf⟩
      have hx : (U f, W.symm w) ∈ N.graph := by
        apply (hgraph _ _).mpr
        intro i
        change W (W.symm w) i = M i (W (U f) i)
        rw [W.apply_symm_apply, hu]
      exact ((ExpandedFA.Unbounded.mem_graph_iff N _).mp hx).choose
  · intro x
    have hx : ((x : H), N x) ∈ N.graph := N.mem_graph_iff.mpr ⟨x, rfl, rfl⟩
    have h := (hgraph _ _).mp hx
    change ∀ i, W (N x) i = M i (W x i) at h
    have hprod : ArbitraryCyclicSum.DisjointL2.glue μ (fun i => W (N x) i)
        =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ]
        fun s => g s * ArbitraryCyclicSum.DisjointL2.glue μ (fun i => W x i) s := by
      apply (ArbitraryCyclicSum.DisjointL2.ae_iff μ (measurableSet_eq_fun
        (ArbitraryCyclicSum.DisjointL2.measurable_glue μ _)
        (hg.mul (ArbitraryCyclicSum.DisjointL2.measurable_glue μ _)))).mpr
      intro i
      change W (N x) i =ᵐ[μ i] fun s => g ⟨i, s⟩ * (W x i) s
      rw [h i]
      exact hM i _
    have h1 := ArbitraryCyclicSum.DisjointL2.toUnion_ae μ (W (N x))
    have h2 := ArbitraryCyclicSum.DisjointL2.toUnion_ae μ (W (x : H))
    change U.symm (N x) =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ] _ at h1
    change U.symm (x : H) =ᵐ[ArbitraryCyclicSum.Spec.disjointMeasure μ] _ at h2
    filter_upwards [h1, h2, hprod] with s hs ht hu
    rw [hs, hu, ← ht]

/-- Assembly of the possibly uncountable disjoint-union multiplication model. -/
theorem multiplication_model : Spec.MultiplicationTheorem.{u} := by
  classical
  intro H _ _ _ N hd hc hn
  obtain ⟨d⟩ := bounded_normal_decomposition H N hd hc hn
  letI (n : ℕ) : CompleteSpace (d.Q n).range :=
    (d.piece n).closed_range.isComplete.completeSpace_coe
  choose I S m μ hfinite g hg M A hA hM hT hstar using fun n : ℕ =>
    bounded_multiplication_family (d.piece n).T (d.piece n).normal
  letI (n : ℕ) (i : I n) : MeasurableSpace (S n i) := m n i
  let AA (i : Σ n, I n) : Lp ℂ 2 (μ i.1 i.2) →ₗᵢ[ℂ] H :=
    (d.Q i.1).range.subtypeₗᵢ.comp (A i.1 i.2)
  let gg : (Σ i : Σ n, I n, S i.1 i.2) → ℂ := fun s => g s.1.1 ⟨s.1.2, s.2⟩
  have hgg : Measurable gg := by
    apply (ArbitraryCyclicSum.DisjointL2.measurable_iff _).mpr
    intro i
    exact (hg i.1).comp (ArbitraryCyclicSum.DisjointL2.measurable_mk i.2)
  have horth : OrthogonalFamily ℂ (fun i : Σ n, I n => Lp ℂ 2 (μ i.1 i.2)) AA := by
    rintro ⟨n, i⟩ ⟨k, j⟩ hne x y
    by_cases hnk : n = k
    · subst k
      change inner ℂ (A n i x) (A n j y) = 0
      exact (hA n).OrthogonalFamily (fun hij => hne (by cases hij; rfl)) x y
    · obtain ⟨a, ha⟩ := (A n i x).property
      obtain ⟨b, hb⟩ := (A k j y).property
      change inner ℂ (A n i x : H) (A k j y : H) = 0
      rw [← ha, ← hb]
      exact d.orthogonal n k hnk a b
  let V : Submodule ℂ H :=
    (⨆ i, LinearMap.range (AA i).toLinearMap).topologicalClosure
  have hlocal (n : ℕ) : (d.Q n).range ≤ V := by
    intro x hx
    let f := (hA n).linearIsometryEquiv ⟨x, hx⟩
    have hs := ((hA n).hasSum_linearIsometryEquiv_symm f).map
      (d.Q n).range.subtypeₗᵢ.toContinuousLinearMap
      (d.Q n).range.subtypeₗᵢ.continuous
    have hs' : HasSum (fun i => AA ⟨n, i⟩ (f i)) x := by
      change HasSum (fun i => (A n i (f i) : H)) x
      change HasSum (fun i => (A n i (f i) : H))
        ((hA n).linearIsometryEquiv.symm f : H) at hs
      simpa only [f, LinearIsometryEquiv.symm_apply_apply] using hs
    rw [← hs'.tsum_eq]
    apply tsum_mem (Submodule.isClosed_topologicalClosure _)
    intro i
    exact Submodule.le_topologicalClosure _
      (Submodule.mem_iSup_of_mem (⟨n, i⟩ : Σ n, I n) ⟨f i, rfl⟩)
  have htotal : ⊤ ≤ V := by
    intro x _
    rw [← (d.complete x).tsum_eq]
    apply tsum_mem (Submodule.isClosed_topologicalClosure _)
    intro n
    exact hlocal n ⟨x, rfl⟩
  have hsum : IsHilbertSum ℂ (fun i : Σ n, I n => Lp ℂ 2 (μ i.1 i.2)) AA :=
    IsHilbertSum.mk horth htotal
  apply multiplicationModel_of_family N hd hc (fun i : Σ n, I n => μ i.1 i.2)
    (fun i => hfinite i.1 i.2) gg hgg (fun i => M i.1 i.2) AA hsum
  · intro i f
    exact hM i.1 i.2 f
  · intro i f
    apply (ExpandedFA.Unbounded.mem_graph_iff N _).mpr
    refine ⟨(d.piece i.1).domain (A i.1 i.2 f).property, ?_⟩
    change N ⟨(A i.1 i.2 f : H), _⟩ = (A i.1 i.2 (M i.1 i.2 f) : H)
    rw [← (d.piece i.1).evaluation, hT]
  · intro i f
    apply (ExpandedFA.Unbounded.mem_graph_iff (adjointValue N) _).mpr
    refine ⟨(d.piece i.1).adjoint_domain (A i.1 i.2 f).property, ?_⟩
    change adjointValue N ⟨(A i.1 i.2 f : H), _⟩ =
      (A i.1 i.2 ((M i.1 i.2).adjoint f) : H)
    rw [← (d.piece i.1).adjoint_evaluation, hstar]


universe v

/-- The coordinate integral has exactly the maximal multiplication graph. -/
theorem coordinateIntegral_graph_iff {S : Type v} [MeasurableSpace S]
    (μ : Measure S) (g : S → ℂ) (hg : Measurable g)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H)
    {E : ProjectionValuedMeasure ℂ H} (C : BoundedRealization E)
    (hC : ∀ h : ℂ → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable h →
      ∀ f : Lp ℂ 2 μ, C.integral h (U f) = U (NativeL2.boundedMul μ (h ∘ g) f))
    (x y : H) :
    (x, y) ∈ (measurableIntegral C id).graph ↔
      U.symm y =ᵐ[μ] fun s => g s * U.symm x s := by
  classical
  rw [measurableIntegral, mem_limitOperator_graph_iff_localized
    (fun n => C.integral (cutoffIndicator id n))
    (fun n => C.integral (truncation id n))
    (C.cutoff_tendsto measurable_id) (C.cutoff_left measurable_id)]
  have hbounded (h : ℂ → ℂ) (hh : SpectralMeasure.Spec.IsBoundedMeasurable h) :
      SpectralMeasure.Spec.IsBoundedMeasurable (h ∘ g) :=
    ⟨hh.1.comp hg, hh.2.choose, fun s => hh.2.choose_spec (g s)⟩
  have heq (h : ℂ → ℂ) (hh : SpectralMeasure.Spec.IsBoundedMeasurable h) (z : H) :
      U.symm (C.integral h z) = NativeL2.boundedMul μ (h ∘ g) (U.symm z) := by
    calc
      U.symm (C.integral h z) = U.symm (C.integral h (U (U.symm z))) := by
        rw [U.apply_symm_apply]
      _ = _ := by rw [hC h hh, U.symm_apply_apply]
  constructor
  · intro h
    have ha (n : ℕ) : ∀ᵐ s ∂μ,
        (truncation id n) (g s) * U.symm x s =
          (cutoffIndicator id n) (g s) * U.symm y s := by
      have hn := congrArg U.symm (h n)
      rw [heq _ (boundedMeasurable_truncation measurable_id n),
        heq _ (boundedMeasurable_cutoffIndicator measurable_id n)] at hn
      filter_upwards [NativeL2.boundedMul_apply μ
        (hbounded _ (boundedMeasurable_truncation measurable_id n)) (U.symm x),
        NativeL2.boundedMul_apply μ
        (hbounded _ (boundedMeasurable_cutoffIndicator measurable_id n)) (U.symm y)]
        with s hs ht
      simp only [Function.comp_apply] at hs ht
      rw [← hs, hn, ht]
    filter_upwards [ae_all_iff.mpr ha] with s hs
    obtain ⟨n, hn⟩ := exists_nat_ge ‖g s‖
    simpa [truncation, cutoffIndicator, hn] using (hs n).symm
  · intro h n
    apply U.symm.injective
    rw [heq _ (boundedMeasurable_truncation measurable_id n),
      heq _ (boundedMeasurable_cutoffIndicator measurable_id n)]
    apply Lp.ext
    filter_upwards [h, NativeL2.boundedMul_apply μ
      (hbounded _ (boundedMeasurable_truncation measurable_id n)) (U.symm x),
      NativeL2.boundedMul_apply μ
      (hbounded _ (boundedMeasurable_cutoffIndicator measurable_id n)) (U.symm y)]
      with s hs ht hu
    rw [ht, hu, hs]
    change ({z : ℂ | ‖z‖ ≤ (n : ℝ)}.indicator (fun z => z) (g s)) * U.symm x s =
      ({z : ℂ | ‖z‖ ≤ (n : ℝ)}.indicator (fun _ => 1) (g s)) * (g s * U.symm x s)
    by_cases hn : ‖g s‖ ≤ (n : ℝ) <;> simp [hn]

/-- The exact multiplication-domain and value assertions identify the full graph. -/
theorem graph_iff_of_multiplication {S : Type v} [MeasurableSpace S]
    (μ : Measure S) (g : S → ℂ) (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H)
    (N : Operator ℂ H H)
    (hdom : ∀ f : Lp ℂ 2 μ, U f ∈ N.domain ↔
      MemLp (fun s => g s * f s) 2 μ)
    (hval : ∀ x : N.domain, U.symm (N x) =ᵐ[μ]
      fun s => g s * (U.symm (x : H)) s) (x y : H) :
    (x, y) ∈ N.graph ↔ U.symm y =ᵐ[μ] fun s => g s * U.symm x s := by
  constructor
  · intro h
    obtain ⟨z, rfl, rfl⟩ := N.mem_graph_iff.mp h
    exact hval z
  · intro h
    have hmem : x ∈ N.domain := by
      have hm := (hdom (U.symm x)).mpr ((memLp_congr_ae h).mp (Lp.memLp (U.symm y)))
      simpa only [U.apply_symm_apply] using hm
    apply N.mem_graph_iff.mpr
    refine ⟨⟨x, hmem⟩, rfl, ?_⟩
    apply U.symm.injective
    exact Lp.ext ((hval ⟨x, hmem⟩).trans h.symm)

/-- A bounded-calculus intertwiner identifies the coordinate integral,
including its maximal domain, with the prescribed multiplication operator. -/
theorem coordinateIntegral_eq_of_multiplication {S : Type v} [MeasurableSpace S]
    (μ : Measure S) (g : S → ℂ) (hg : Measurable g)
    (U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] H)
    {E : ProjectionValuedMeasure ℂ H} (C : BoundedRealization E)
    (hC : ∀ h : ℂ → ℂ, SpectralMeasure.Spec.IsBoundedMeasurable h →
      ∀ f : Lp ℂ 2 μ, C.integral h (U f) = U (NativeL2.boundedMul μ (h ∘ g) f))
    (N : Operator ℂ H H)
    (hdom : ∀ f : Lp ℂ 2 μ, U f ∈ N.domain ↔
      MemLp (fun s => g s * f s) 2 μ)
    (hval : ∀ x : N.domain, U.symm (N x) =ᵐ[μ]
      fun s => g s * (U.symm (x : H)) s) :
    measurableIntegral C id = N := by
  apply LinearPMap.eq_of_eq_graph
  ext ⟨x, y⟩
  exact (coordinateIntegral_graph_iff μ g hg U C hC x y).trans
    (graph_iff_of_multiplication μ g U N hdom hval x y).symm


namespace SpectralRepresentation
variable {S : Type v} [MeasurableSpace S]
  {E : ProjectionValuedMeasure S H} (C : BoundedRealization E)

/-- The uniform approximation axiom fixes every bounded integral canonically. -/
theorem integral_eq (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    C.integral f = E.spectralIntegral f := by
  obtain ⟨a, ha⟩ := SpectralMeasure.exists_uniform_simple_approx f hf
  exact tendsto_nhds_unique (C.uniform_limit f hf a ha)
    (E.spectralIntegral_tendsto f hf a ha)

theorem integral_indicator_one (B : Set S) (hB : MeasurableSet B) :
    C.integral (B.indicator (fun _ => 1)) = E B := by
  rw [integral_eq C _ (BorelNormSpectrum.bounded_indicator B hB
    (BorelNormSpectrum.bounded_const 1)), BorelNormSpectrum.integral_indicator_one E B hB]

theorem integral_indicator (B : Set S) (hB : MeasurableSet B)
    (f : S → ℂ) (hf : SpectralMeasure.Spec.IsBoundedMeasurable f) :
    C.integral (B.indicator f) = C.integral f * E B := by
  rw [integral_eq C _ (BorelNormSpectrum.bounded_indicator B hB hf),
    integral_eq C _ hf, BorelNormSpectrum.integral_indicator E B hB hf]

/-- A bounded region of a measurable symbol maps every vector into the
maximal spectral domain, and its action is the bounded localized integral. -/
theorem localized_graph {f : S → ℂ} (hf : Measurable f)
    {B : Set S} (hB : MeasurableSet B) {M : ℝ} (hM : ∀ s ∈ B, ‖f s‖ ≤ M)
    (x : H) :
    (E B x, C.integral (B.indicator f) x) ∈ (measurableIntegral C f).graph := by
  rw [measurableIntegral, mem_limitOperator_graph_iff]
  obtain ⟨k, hk⟩ := exists_nat_ge M
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  have heq : B.indicator (truncation f n) = B.indicator f := by
    classical
    funext s
    by_cases hs : s ∈ B
    · have hb : ‖f s‖ ≤ (n : ℝ) := (hM s hs).trans (hk.trans (by exact_mod_cast hn))
      simp [hs, truncation, hb]
    · simp [hs]
  have hm := integral_indicator C B hB _ (boundedMeasurable_truncation hf n)
  rw [heq] at hm
  exact congrArg (fun T : H →L[ℂ] H => T x) hm


/-- Bounded pointwise convergence is strong convergence for each realization. -/
theorem strong_convergence (g : S → ℂ) (a : ℕ → S → ℂ)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    (ha : ∀ n, SpectralMeasure.Spec.IsBoundedMeasurable (a n))
    (hb : ∃ M : ℝ, ∀ n s, ‖a n s‖ ≤ M)
    (hl : ∀ s, Tendsto (fun n => a n s) atTop (nhds (g s))) (x : H) :
    Tendsto (fun n => C.integral (a n) x) atTop (nhds (C.integral g x)) := by
  simp_rw [integral_eq C g hg, integral_eq C _ (ha _)]
  apply NormalSpectral.strong_convergence E g a hg ha hb
  exact ⟨∅, MeasurableSet.empty, E.map_empty, fun s _ => hl s⟩

/-- Multiplying by a bounded symbol whose product is bounded lands in the
maximal domain. This is the local algebra needed for spectral inverses. -/
theorem bounded_product_graph {f g : S → ℂ} (hf : Measurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    (hfg : SpectralMeasure.Spec.IsBoundedMeasurable (f * g)) (x : H) :
    (C.integral g x, C.integral (f * g) x) ∈ (measurableIntegral C f).graph := by
  rw [measurableIntegral, mem_limitOperator_graph_iff]
  have heq (n : ℕ) : truncation f n * g =
      {s | ‖f s‖ ≤ (n : ℝ)}.indicator (f * g) := by
    classical
    funext s
    by_cases hs : ‖f s‖ ≤ (n : ℝ) <;> simp [truncation, hs]
  have ha (n : ℕ) := (boundedMeasurable_truncation hf n).mul hg
  have hh := strong_convergence C (f * g) (fun n => truncation f n * g) hfg ha
  have hbound : ∃ M : ℝ, ∀ n s, ‖(truncation f n * g) s‖ ≤ M := by
    obtain ⟨M, hM, hb⟩ := hfg.nonneg_bound
    refine ⟨M, fun n s => ?_⟩
    rw [heq]
    classical
    by_cases hs : ‖f s‖ ≤ (n : ℝ)
    · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hs] using hb s
    · simp [hs, hM]
  have hlim (s : S) : Tendsto (fun n => (truncation f n * g) s) atTop
      (nhds ((f * g) s)) := (truncation_tendsto f s).mul_const (g s)
  have hh' := hh hbound hlim x
  simpa only [C.mul _ _ (boundedMeasurable_truncation hf _) hg,
    mul_apply_eq_comp] using hh'

/-- A bounded spectral multiplier commutes with the unbounded integral on
its maximal domain whenever its product with the symbol is bounded. -/
theorem bounded_product_commutes {f g : S → ℂ} (hf : Measurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    (hfg : SpectralMeasure.Spec.IsBoundedMeasurable (f * g))
    (x : (measurableIntegral C f).domain) :
    C.integral g (measurableIntegral C f x) = C.integral (f * g) x := by
  have heq (n : ℕ) : C.integral g (C.integral (truncation f n) x) =
      C.integral (truncation f n) (C.integral g x) := by
    change (C.integral g * C.integral (truncation f n)) x =
      (C.integral (truncation f n) * C.integral g) x
    rw [← C.mul _ _ hg (boundedMeasurable_truncation hf n),
      ← C.mul _ _ (boundedMeasurable_truncation hf n) hg, mul_comm]
  have h1 := (C.integral g).continuous.tendsto
      (measurableIntegral C f x) |>.comp (measurableIntegral_tendsto C f x)
  have h2 := (mem_limitOperator_graph_iff _ _ _).mp
      (bounded_product_graph C hf hg hfg (x : H))
  exact tendsto_nhds_unique h1 (h2.congr' (Eventually.of_forall fun n => (heq n).symm))



/-- Every bounded spectral multiplier preserves the full integral domain and
commutes there. This applies in particular to every Borel projection. -/
theorem bounded_commutes {f g : S → ℂ} (hf : Measurable f)
    (hg : SpectralMeasure.Spec.IsBoundedMeasurable g)
    (x : (measurableIntegral C f).domain) :
    (C.integral g (x : H), C.integral g (measurableIntegral C f x)) ∈
      (measurableIntegral C f).graph := by
  change (C.integral g (x : H), C.integral g (measurableIntegral C f x)) ∈
    (limitOperator (fun n => C.integral (truncation f n))).graph
  rw [mem_limitOperator_graph_iff]
  have heq (n : ℕ) : C.integral (truncation f n) (C.integral g x) =
      C.integral g (C.integral (truncation f n) x) := by
    change (C.integral (truncation f n) * C.integral g) x =
      (C.integral g * C.integral (truncation f n)) x
    rw [← C.mul _ _ (boundedMeasurable_truncation hf n) hg,
      ← C.mul _ _ hg (boundedMeasurable_truncation hf n), mul_comm]
  simpa only [heq, Function.comp_def] using (C.integral g).continuous.tendsto
      (measurableIntegral C f x) |>.comp (measurableIntegral_tendsto C f x)

/-- Projection-valued localization has its exact domain meaning. -/
theorem projection_commutes {f : S → ℂ} (hf : Measurable f)
    (B : Set S) (hB : MeasurableSet B) (x : (measurableIntegral C f).domain) :
    (E B (x : H), E B (measurableIntegral C f x)) ∈ (measurableIntegral C f).graph := by
  simpa only [integral_indicator_one C B hB] using
    bounded_commutes C hf (BorelNormSpectrum.bounded_indicator B hB
      (BorelNormSpectrum.bounded_const 1)) x

/-- A vector localized in a closed disk has a full shifted-operator orbit
with the quantitative power bound used to identify spectral disks. -/
theorem disk_sequence {E : ProjectionValuedMeasure ℂ H} (C : BoundedRealization E)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (x : H)
    (hx : E (Metric.closedBall z r) x = x) :
    ∃ a : ℕ → H, a 0 = x ∧
      (∀ n, a n ∈ (measurableIntegral C (fun w : ℂ => w)).domain) ∧
      (∀ n, (a n, z • a n + a (n + 1)) ∈
        (measurableIntegral C (fun w : ℂ => w)).graph) ∧
      ∀ n, ‖a n‖ ≤ r ^ n * ‖x‖ := by
  classical
  let B := Metric.closedBall z r
  have hB : MeasurableSet B := measurableSet_closedBall
  have hb (w : ℂ) (hw : w ∈ B) : ‖w - z‖ ≤ r := by
    simpa only [B, Metric.mem_closedBall, dist_eq_norm] using hw
  have hcoord (w : ℂ) (hw : w ∈ B) : ‖w‖ ≤ ‖z‖ + r := by
    linarith [norm_sub_norm_le w z, hb w hw]
  let g : ℂ → ℂ := B.indicator (fun w => w - z)
  have hgb (w : ℂ) : ‖g w‖ ≤ r := by
    by_cases hw : w ∈ B
    · simpa [g, hw] using hb w hw
    · simp [g, hw, hr]
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
    ⟨(measurable_id.sub measurable_const).indicator hB, r, hgb⟩
  let T := C.integral g
  have hT : ‖T‖ ≤ r := C.bound g r hg hr hgb
  have hPT : E B * T = T := by
    rw [← integral_indicator_one C B hB, ← C.mul _ _
      (BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)) hg]
    congr 1
    funext w
    by_cases hw : w ∈ B <;> simp [g, hw]
  let a : ℕ → H := fun n => (T ^ n) x
  have ha (n : ℕ) : E B (a n) = a n := by
    induction n with
    | zero => simpa [a] using hx
    | succ n ih =>
      change (E B * T ^ (n + 1)) x = (T ^ (n + 1)) x
      rw [pow_succ', ← mul_assoc, hPT]
  have hm (n : ℕ) : a n ∈ (measurableIntegral C (fun w : ℂ => w)).domain := by
    have hh := localized_graph C measurable_id hB hcoord (a n)
    rw [ha n] at hh
    exact LinearPMap.mem_domain_of_mem_graph hh
  have hfun : B.indicator (fun w : ℂ => w) = z • B.indicator (fun _ => 1) + g := by
    funext w
    by_cases hw : w ∈ B <;> simp [g, hw]
  have hi : C.integral (B.indicator (fun w : ℂ => w)) = z • E B + T := by
    rw [hfun, C.add _ _ ((BorelNormSpectrum.bounded_indicator B hB
      (BorelNormSpectrum.bounded_const 1)).smul z) hg,
      C.smul z _ (BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)),
      integral_indicator_one C B hB]
  refine ⟨a, by simp [a], hm, ?_, ?_⟩
  · intro n
    have hh := localized_graph C measurable_id hB hcoord (a n)
    change (E B (a n), C.integral (B.indicator (fun w : ℂ => w)) (a n)) ∈
      (measurableIntegral C (fun w : ℂ => w)).graph at hh
    rw [ha n, hi] at hh
    convert hh using 1
    change (_, z • a n + (T ^ (n + 1)) x) = (_, z • E B (a n) + T (a n))
    rw [ha n, pow_succ']
    rfl
  · intro n
    induction n with
    | zero => simp [a]
    | succ n ih =>
      have hnext : a (n + 1) = T (a n) := by simp only [a, pow_succ', mul_apply_eq_comp]
      calc
        ‖a (n + 1)‖ = ‖T (a n)‖ := congrArg norm hnext
        _ ≤ ‖T‖ * ‖a n‖ := T.le_opNorm _
        _ ≤ r * (r ^ n * ‖x‖) := mul_le_mul hT ih (norm_nonneg _) hr
        _ = r ^ (n + 1) * ‖x‖ := by rw [pow_succ']; ring

/-- A spectral gap produces a bounded two-sided inverse, without any
preexisting resolvent point and without a scalar control measure. -/
theorem resolvent_of_gap {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) (r : ℝ) (hr : 0 < r)
    (hnull : E (Metric.ball z r) = 0) :
    Nonempty (ResolventInverse (measurableIntegral C (fun w : ℂ => w)) z) := by
  classical
  let B := Metric.ball z r
  have hB : MeasurableSet B := measurableSet_ball
  let g : ℂ → ℂ := Bᶜ.indicator (fun w => (z - w)⁻¹)
  let a : ℂ → ℂ := Bᶜ.indicator (fun _ => 1)
  have ha : SpectralMeasure.Spec.IsBoundedMeasurable a :=
    BorelNormSpectrum.bounded_indicator _ hB.compl (BorelNormSpectrum.bounded_const 1)
  have hdist (w : ℂ) (hw : w ∉ B) : r ≤ ‖z - w‖ := by
    apply le_of_not_gt
    intro hh
    exact hw (by simpa [B, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hh)
  have hne (w : ℂ) (hw : w ∉ B) : z - w ≠ 0 :=
    norm_pos_iff.mp (hr.trans_le (hdist w hw))
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g := by
    refine ⟨(measurable_const.sub measurable_id).inv.indicator hB.compl, r⁻¹, ?_⟩
    intro w
    by_cases hw : w ∈ B
    · simp [g, hw, hr.le]
    · simpa [g, hw, norm_inv] using inv_anti₀ hr (hdist w hw)
  have hprod : (fun w : ℂ => w) * g = z • g - a := by
    funext w
    by_cases hw : w ∈ B
    · simp [g, a, hw]
    · simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        g, a, Set.indicator_of_mem (mem_compl hw)]
      field_simp [hne w hw]
      ring
  have hfg : SpectralMeasure.Spec.IsBoundedMeasurable ((fun w : ℂ => w) * g) := by
    rw [hprod]
    exact BorelNormSpectrum.bounded_sub (hg.smul z) ha
  have hia : C.integral a = 1 := by
    rw [integral_eq C _ ha, ← E.spectralIntegral_one]
    exact BorelNormSpectrum.integral_congr_of_null E hB hnull ha
      (BorelNormSpectrum.bounded_const 1) (fun w hw => by simp [a, hw])
  have hifg : C.integral ((fun w : ℂ => w) * g) = z • C.integral g - 1 := by
    rw [hprod, C.sub _ _ (hg.smul z) ha, C.smul z g hg, hia]
  let A := measurableIntegral C (fun w : ℂ => w)
  have hgraph (y : H) : (C.integral g y, C.integral ((fun w : ℂ => w) * g) y) ∈ A.graph :=
    bounded_product_graph C measurable_id hg hfg y
  have hmem (y : H) : C.integral g y ∈ A.domain :=
    LinearPMap.mem_domain_of_mem_graph (hgraph y)
  have heval (y : H) : A ⟨C.integral g y, hmem y⟩ =
      z • C.integral g y - y := by
    have hh := A.mem_graph_snd_inj (A.mem_graph ⟨_, hmem y⟩) (hgraph y) rfl
    rw [hh, hifg]
    rfl
  refine ⟨{
    inverse := C.integral g
    mem_domain := hmem
    right_inverse := fun y => by rw [heval y]; module
    left_inverse := ?_ }⟩
  intro x
  have hc := bounded_product_commutes C measurable_id hg hfg x
  change C.integral g (A x) = C.integral ((fun w : ℂ => w) * g) x at hc
  have hh := congrArg (fun T : H →L[ℂ] H => T (x : H)) hifg
  change C.integral g (z • (x : H) - A x) = (x : H)
  rw [map_sub, map_smul, hc, hh]
  change z • C.integral g (x : H) - (z • C.integral g (x : H) - (x : H)) = _
  module


/-- A bounded resolvent rules out spectral mass in a sufficiently small ball. -/
theorem ball_null_of_resolvent {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ)
    (R : ResolventInverse (measurableIntegral C (fun w : ℂ => w)) z)
    (r : ℝ) (hr : 0 < r) (hsmall : ‖R.inverse‖ * r < 1) :
    E (Metric.ball z r) = 0 := by
  classical
  let B := Metric.ball z r
  have hB : MeasurableSet B := measurableSet_ball
  have hb (w : ℂ) (hw : w ∈ B) : ‖w‖ ≤ ‖z‖ + r := by
    have hh : ‖w - z‖ < r := by simpa only [B, Metric.mem_ball, dist_eq_norm] using hw
    linarith [norm_sub_norm_le w z]
  let f : ℂ → ℂ := B.indicator (fun w => w)
  have hf : SpectralMeasure.Spec.IsBoundedMeasurable f := by
    refine ⟨measurable_id.indicator hB, ‖z‖ + r, fun w => ?_⟩
    by_cases hw : w ∈ B
    · simpa [f, hw] using hb w hw
    · simp [f, hw, add_nonneg (norm_nonneg z) hr.le]
  let g : ℂ → ℂ := B.indicator (fun w => z - w)
  have hg0 (w : ℂ) : ‖g w‖ ≤ r := by
    by_cases hw : w ∈ B
    · have hh : ‖z - w‖ < r := by
        simpa only [B, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hw
      simpa [g, hw] using hh.le
    · simp [g, hw, hr.le]
  have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
    ⟨(measurable_const.sub measurable_id).indicator hB, r, hg0⟩
  have heq : g = z • B.indicator (fun _ => 1) - f := by
    funext w
    by_cases hw : w ∈ B <;> simp [g, f, hw]
  have hig : C.integral g = z • E B - C.integral f := by
    rw [heq, C.sub _ _ ((BorelNormSpectrum.bounded_indicator B hB
      (BorelNormSpectrum.bounded_const 1)).smul z) hf,
      C.smul z _ (BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)),
      integral_indicator_one C B hB]
  let A := measurableIntegral C (fun w : ℂ => w)
  have hgraph (y : H) : (E B y, C.integral f y) ∈ A.graph :=
    localized_graph C measurable_id hB hb y
  have hmem (y : H) : E B y ∈ A.domain := LinearPMap.mem_domain_of_mem_graph (hgraph y)
  have heval (y : H) : A ⟨E B y, hmem y⟩ = C.integral f y :=
    A.mem_graph_snd_inj (A.mem_graph ⟨_, hmem y⟩) (hgraph y) rfl
  have hprod : R.inverse * C.integral g = E B := by
    ext y
    have hh := R.left_inverse ⟨E B y, hmem y⟩
    rw [heval y] at hh
    simpa only [hig, mul_apply_eq_comp, sub_apply,
      smul_apply] using hh
  by_contra hne
  have hp : ‖E B‖ = 1 := BorelNormSpectrum.projection_norm_eq_one E hB hne
  have hi : ‖C.integral g‖ ≤ r := C.bound g r hg hr.le hg0
  have hnorm := norm_mul_le R.inverse (C.integral g)
  rw [hprod, hp] at hnorm
  have := mul_le_mul_of_nonneg_left hi (norm_nonneg R.inverse)
  linarith


theorem null_subset {E : ProjectionValuedMeasure S H} {B D : Set S}
    (hB : MeasurableSet B) (hD : MeasurableSet D) (hDB : D ⊆ B) (hnull : E B = 0) :
    E D = 0 := by
  have hh := E.inter D B hD hB
  rw [hnull, mul_zero, inter_eq_left.mpr hDB] at hh
  exact hh.symm

/-- The resolvent is precisely the set of centers of PVM-null balls. -/
theorem resolvent_iff_gap {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) :
    z ∈ resolventSetValue (measurableIntegral C (fun w : ℂ => w)) ↔
      ∃ r : ℝ, 0 < r ∧ E (Metric.ball z r) = 0 := by
  constructor
  · rintro ⟨R⟩
    obtain ⟨r, hr, hsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1) ‖R.inverse‖
    exact ⟨r, hr, ball_null_of_resolvent C z R r hr hsmall⟩
  · rintro ⟨r, hr, hnull⟩
    exact resolvent_of_gap C z r hr hnull

/-- All support assertions follow for every spectral representation. The
closedness input is supplied by the general resolvent perturbation lemma. -/
theorem support_of_resolves (N : Operator ℂ H H) (E : ProjectionValuedMeasure ℂ H)
    (hc : _root_.IsClosed (operatorSpectrum N)) (h : Resolves N E) :
    SpectralSupport N E := by
  classical
  obtain ⟨C, heq, _⟩ := h
  subst N
  let A := measurableIntegral C (fun w : ℂ => w)
  let I := resolventSetValue A
  have hI : MeasurableSet I := by
    simpa only [operatorSpectrum, compl_compl] using hc.isOpen_compl.measurableSet
  have hgap : ∀ z : I, ∃ r : ℝ, 0 < r ∧ E (Metric.ball (z : ℂ) r) = 0 :=
    fun z => (resolvent_iff_gap C z).mp z.property
  choose r hr hnull using hgap
  have hcover : I ⊆ ⋃ z : I, Metric.ball (z : ℂ) (r z) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, Metric.mem_ball_self (hr ⟨z, hz⟩)⟩
  obtain ⟨t, ht, htc⟩ := (HereditarilyLindelofSpace.isLindelof I).elim_countable_subcover
    (fun z : I => Metric.ball (z : ℂ) (r z)) (fun _ => Metric.isOpen_ball) hcover
  have hzero : E I = 0 := by
    ext x
    have hballs : ∀ z : I, C.measure x (Metric.ball (z : ℂ) (r z)) = 0 := by
      intro z
      rw [C.measure_apply x _ measurableSet_ball, hnull]
      simp
    have hm : C.measure x I = 0 := measure_mono_null htc
      ((measure_biUnion_null_iff ht).mpr (fun z _ => hballs z))
    rw [C.measure_apply x I hI, ENNReal.ofReal_eq_zero] at hm
    have hn : ‖E I x‖ = 0 := by nlinarith [sq_nonneg ‖E I x‖, norm_nonneg (E I x)]
    exact norm_eq_zero.mp hn
  refine ⟨hc, ?_, ?_⟩
  · simpa only [operatorSpectrum, compl_compl] using hzero
  · intro U hU hmeet hnullU
    obtain ⟨z, hzU, hzspec⟩ := hmeet
    obtain ⟨s, hs, hsub⟩ := Metric.isOpen_iff.mp hU z hzU
    have hball := null_subset hU.measurableSet measurableSet_ball hsub hnullU
    exact hzspec ((resolvent_iff_gap C z).mpr ⟨s, hs, hball⟩)

/-- A contracting inverse combined with a geometric growth bound kills the
corresponding spectral component. -/
theorem projected_zero_of_growth (M Q : H →L[ℂ] H)
    (a r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (har : a * r < 1)
    (hM : ‖M‖ ≤ a) (hQ : ∀ y, ‖Q y‖ ≤ ‖y‖) (hMQ : M * Q = M)
    (x : ℕ → H) (hstep : ∀ n, M (x (n + 1)) = Q (x n))
    (hbound : ∀ n, ‖x n‖ ≤ r ^ n * ‖x 0‖) : Q (x 0) = 0 := by
  have heq (n : ℕ) : Q (x 0) = (M ^ n) (Q (x n)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply]
      have h := congrArg (fun T : H →L[ℂ] H => T (x (n + 1))) hMQ
      change M (Q (x (n + 1))) = M (x (n + 1)) at h
      rw [h, hstep n]
      exact ih
  have hMn (n : ℕ) (y : H) : ‖(M ^ n) y‖ ≤ a ^ n * ‖y‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc
        _ ≤ ‖M‖ * ‖(M ^ n) y‖ := M.le_opNorm _
        _ ≤ a * (a ^ n * ‖y‖) := mul_le_mul hM ih (norm_nonneg _) ha
        _ = a ^ (n + 1) * ‖y‖ := by rw [pow_succ]; ring
  have hb (n : ℕ) : ‖Q (x 0)‖ ≤ (a * r) ^ n * ‖x 0‖ := by
    rw [heq n]
    calc
      _ ≤ a ^ n * ‖Q (x n)‖ := hMn n _
      _ ≤ a ^ n * (r ^ n * ‖x 0‖) := mul_le_mul_of_nonneg_left
        ((hQ _).trans (hbound n)) (pow_nonneg ha n)
      _ = (a * r) ^ n * ‖x 0‖ := by rw [mul_pow]; ring
  have ht : Tendsto (fun n : ℕ => (a * r) ^ n * ‖x 0‖) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg ha hr) har).mul_const ‖x 0‖
  have hn : ‖Q (x 0)‖ ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))


/-- A geometrically bounded full orbit determines its closed spectral disk.
This is the intrinsic direction of Bernau's disk characterization. -/
theorem disk_fixed_of_sequence {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (x : ℕ → H)
    (hx : ∀ n, x n ∈ (measurableIntegral C (fun w : ℂ => w)).domain)
    (hstep : ∀ n, measurableIntegral C (fun w : ℂ => w) ⟨x n, hx n⟩ =
      z • x n + x (n + 1))
    (hbound : ∀ n, ‖x n‖ ≤ r ^ n * ‖x 0‖) :
    E (Metric.closedBall z r) (x 0) = x 0 := by
  classical
  have hout (s : ℝ) (hrs : r < s) : E (Metric.closedBall z s)ᶜ (x 0) = 0 := by
    have hs : 0 < s := hr.trans_lt hrs
    let B := (Metric.closedBall z s)ᶜ
    have hB : MeasurableSet B := measurableSet_closedBall.compl
    let g : ℂ → ℂ := B.indicator (fun w => (w - z)⁻¹)
    let b : ℂ → ℂ := B.indicator (fun _ => 1)
    have hb : SpectralMeasure.Spec.IsBoundedMeasurable b :=
      BorelNormSpectrum.bounded_indicator B hB (BorelNormSpectrum.bounded_const 1)
    have hdist (w : ℂ) (hw : w ∈ B) : s ≤ ‖w - z‖ := by
      have hnot : ¬ ‖w - z‖ ≤ s := by simpa [B, Metric.mem_closedBall, dist_eq_norm] using hw
      exact (lt_of_not_ge hnot).le
    have hne (w : ℂ) (hw : w ∈ B) : w - z ≠ 0 :=
      norm_pos_iff.mp (hs.trans_le (hdist w hw))
    have hgb (w : ℂ) : ‖g w‖ ≤ s⁻¹ := by
      by_cases hw : w ∈ B
      · simpa [g, hw, norm_inv] using inv_anti₀ hs (hdist w hw)
      · simp [g, hw, hs.le]
    have hg : SpectralMeasure.Spec.IsBoundedMeasurable g :=
      ⟨(measurable_id.sub measurable_const).inv.indicator hB, s⁻¹, hgb⟩
    have hprod : (fun w : ℂ => w) * g = z • g + b := by
      funext w
      by_cases hw : w ∈ B
      · simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          g, b, Set.indicator_of_mem hw]
        field_simp [hne w hw]
        ring
      · simp [g, b, hw]
    have hfg : SpectralMeasure.Spec.IsBoundedMeasurable ((fun w : ℂ => w) * g) := by
      rw [hprod]
      exact (hg.smul z).add hb
    let M := C.integral g
    let Q := E B
    have hi : C.integral ((fun w : ℂ => w) * g) = z • M + Q := by
      rw [hprod, C.add _ _ (hg.smul z) hb, C.smul z _ hg,
        integral_indicator_one C B hB]
    have hMQ : M * Q = M := by
      have hgg : B.indicator g = g := by
        funext w
        by_cases hw : w ∈ B <;> simp [g, hw]
      exact (integral_indicator C B hB g hg).symm.trans (congrArg C.integral hgg)
    have hrec (n : ℕ) : M (x (n + 1)) = Q (x n) := by
      have hh := bounded_product_commutes C measurable_id hg hfg ⟨x n, hx n⟩
      change M ((measurableIntegral C (fun w : ℂ => w)) ⟨x n, hx n⟩) =
        C.integral ((fun w : ℂ => w) * g) (x n) at hh
      rw [hstep n, map_add, map_smul, hi] at hh
      change z • M (x n) + M (x (n + 1)) = z • M (x n) + Q (x n) at hh
      exact add_left_cancel hh
    have har : s⁻¹ * r < 1 := by
      calc
        s⁻¹ * r = r / s := by rw [div_eq_mul_inv]; ring
        _ < 1 := (div_lt_one hs).mpr hrs
    exact projected_zero_of_growth M Q s⁻¹ r (inv_nonneg.mpr hs.le) hr har
      (C.bound g s⁻¹ hg (inv_nonneg.mpr hs.le) hgb)
      (fun y => E.norm_apply_le B hB y) hMQ x hrec hbound
  let D := (Metric.closedBall z r)ᶜ
  let I := {s : ℝ // r < s}
  let B (s : I) := (Metric.closedBall z (s : ℝ))ᶜ
  have hcover : D ⊆ ⋃ s : I, B s := by
    intro w hw
    have hdist : r < dist w z := by simpa [D, Metric.mem_closedBall] using hw
    obtain ⟨s, hrs, hsw⟩ := exists_between hdist
    exact mem_iUnion.mpr ⟨⟨s, hrs⟩, by simpa [B, Metric.mem_closedBall] using hsw⟩
  obtain ⟨t, ht, htc⟩ := (HereditarilyLindelofSpace.isLindelof D).elim_countable_subcover
    B (fun _ => Metric.isClosed_closedBall.isOpen_compl) hcover
  have hnull (s : I) : C.measure (x 0) (B s) = 0 := by
    rw [C.measure_apply _ _ measurableSet_closedBall.compl, hout s s.property]
    simp
  have hm : C.measure (x 0) D = 0 := measure_mono_null htc
    ((measure_biUnion_null_iff ht).mpr (fun s _ => hnull s))
  rw [C.measure_apply _ _ measurableSet_closedBall.compl, ENNReal.ofReal_eq_zero] at hm
  have hzero : E D (x 0) = 0 := by
    have hn : ‖E D (x 0)‖ = 0 := by
      nlinarith [sq_nonneg ‖E D (x 0)‖, norm_nonneg (E D (x 0))]
    exact norm_eq_zero.mp hn
  let A := Metric.closedBall z r
  have hA : MeasurableSet A := measurableSet_closedBall
  have hind : A.indicator (fun _ => (1 : ℂ)) + D.indicator (fun _ => 1) = fun _ => 1 := by
    funext w
    by_cases hw : w ∈ A <;> simp [D, A] at hw ⊢
  have hsum := C.add _ _ (BorelNormSpectrum.bounded_indicator A hA
    (BorelNormSpectrum.bounded_const 1)) (BorelNormSpectrum.bounded_indicator D hA.compl
      (BorelNormSpectrum.bounded_const 1))
  rw [hind, C.one, integral_indicator_one C A hA, integral_indicator_one C D hA.compl] at hsum
  have hh := congrArg (fun T : H →L[ℂ] H => T (x 0)) hsum
  change x 0 = E A (x 0) + E D (x 0) at hh
  rw [hzero, add_zero] at hh
  exact hh.symm

/-- Graph-form version for intrinsic disk comparisons. -/
theorem disk_fixed_of_graph_sequence {E : ProjectionValuedMeasure ℂ H}
    (C : BoundedRealization E) (z : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (x : ℕ → H)
    (hgraph : ∀ n, (x n, z • x n + x (n + 1)) ∈
      (measurableIntegral C (fun w : ℂ => w)).graph)
    (hbound : ∀ n, ‖x n‖ ≤ r ^ n * ‖x 0‖) :
    E (Metric.closedBall z r) (x 0) = x 0 := by
  let A := measurableIntegral C (fun w : ℂ => w)
  have hx (n : ℕ) : x n ∈ A.domain :=
    LinearPMap.mem_domain_of_mem_graph (hgraph n)
  have hstep (n : ℕ) : A ⟨x n, hx n⟩ = z • x n + x (n + 1) :=
    A.mem_graph_snd_inj (A.mem_graph ⟨x n, hx n⟩) (hgraph n) rfl
  exact disk_fixed_of_sequence C z r hr x hx hstep hbound


/-- A representation by the same operator fixes every vector in a spectral
closed disk of the first representation. -/
theorem disk_fixed_of_other_representation
    {E F : ProjectionValuedMeasure ℂ H} (C : BoundedRealization E)
    (D : BoundedRealization F)
    (heq : measurableIntegral C (fun w : ℂ => w) =
      measurableIntegral D (fun w : ℂ => w))
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (x : H)
    (hx : E (Metric.closedBall z r) x = x) :
    F (Metric.closedBall z r) x = x := by
  obtain ⟨a, ha0, _, hgraph, hbound⟩ := disk_sequence C z r hr x hx
  have hg (n : ℕ) : (a n, z • a n + a (n + 1)) ∈
      (measurableIntegral D (fun w : ℂ => w)).graph := by
    rw [← heq]
    exact hgraph n
  have hb (n : ℕ) : ‖a n‖ ≤ r ^ n * ‖a 0‖ := by
    simpa only [ha0] using hbound n
  simpa only [ha0] using disk_fixed_of_graph_sequence D z r hr a hg hb

/-- Closed spectral disks are determined intrinsically by the operator. -/
theorem closedBall_eq_of_integral_eq
    {E F : ProjectionValuedMeasure ℂ H} (C : BoundedRealization E)
    (D : BoundedRealization F)
    (heq : measurableIntegral C (fun w : ℂ => w) =
      measurableIntegral D (fun w : ℂ => w))
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    E (Metric.closedBall z r) = F (Metric.closedBall z r) := by
  let B := Metric.closedBall z r
  have hB : MeasurableSet B := measurableSet_closedBall
  have hFE : F B * E B = E B := by
    ext x
    have hh := congrArg (fun T : H →L[ℂ] H => T x) (E.idempotent B hB)
    exact disk_fixed_of_other_representation C D heq z r hr (E B x) hh
  have hEF : E B * F B = F B := by
    ext x
    have hh := congrArg (fun T : H →L[ℂ] H => T x) (F.idempotent B hB)
    exact disk_fixed_of_other_representation D C heq.symm z r hr (F B x) hh
  have hstar := congrArg star hFE
  rw [star_mul, (E.selfAdjoint B hB).star_eq, (F.selfAdjoint B hB).star_eq] at hstar
  exact hstar.symm.trans hEF

end SpectralRepresentation

/-- The complex spectral PVM, obtained from the maximal multiplication model. -/
theorem spectral_existence : Spec.SpectralExistence.{u} := by
  intro H _ _ _ N hd hc hn
  obtain ⟨I, S, m, μ, hfinite, g, hg, U, hdom, hval⟩ :=
    multiplication_model H N hd hc hn
  letI := m
  let ν := ArbitraryCyclicSum.Spec.disjointMeasure μ
  obtain ⟨C₀⟩ := exists_boundedRealization (NativeL2.projectionValuedMeasure ν)
  let C := (C₀.map g hg).conjugate U
  refine ⟨_, resolves_of_integral_eq N _ C ?_⟩
  apply coordinateIntegral_eq_of_multiplication ν g hg U C ?_ N hdom hval
  intro h hh f
  change U (C₀.integral (h ∘ g) (U.symm (U f))) =
    U (NativeL2.boundedMul ν (h ∘ g) f)
  rw [U.symm_apply_apply, NativeL2.integral_eq_boundedMul ν C₀ _
    ⟨hh.1.comp hg, hh.2.imp (fun r hr s => hr (g s))⟩]

private def closedBalls : Set (Set ℂ) := {B | ∃ z r, B = Metric.closedBall z r}

private theorem borel_generateFrom_closedBalls : borel ℂ = MeasurableSpace.generateFrom closedBalls := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    intro U hU
    change IsOpen U at hU
    have hball (z : ℂ) (r : ℝ) :
        MeasurableSet[MeasurableSpace.generateFrom closedBalls] (Metric.ball z r) := by
      have heq : Metric.ball z r = ⋃ (q : ℚ) (_ : (q : ℝ) < r), Metric.closedBall z (q : ℝ) := by
        ext x
        constructor
        · intro hx
          obtain ⟨q, hq, hqr⟩ := exists_rat_btwn (Metric.mem_ball.mp hx)
          exact mem_iUnion.mpr ⟨q, mem_iUnion.mpr ⟨hqr, Metric.mem_closedBall.mpr hq.le⟩⟩
        · intro hx
          obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
          exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hxq).trans_lt hq)
      rw [heq]
      exact MeasurableSet.iUnion (fun q => MeasurableSet.iUnion (fun _ =>
        MeasurableSpace.measurableSet_generateFrom ⟨z, (q : ℝ), rfl⟩))
    let B : Set (Set ℂ) := {V | ∃ z r, 0 < r ∧ V = Metric.ball z r ∧ V ⊆ U}
    have hBU : ⋃₀ B = U := by
      ext x
      constructor
      · rintro ⟨V, hV, hx⟩
        exact hV.choose_spec.choose_spec.2.2 hx
      · intro hx
        obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
        exact mem_sUnion.mpr ⟨Metric.ball x r, ⟨x, r, hr, rfl, hsub⟩, Metric.mem_ball_self hr⟩
    have hBo : ∀ V ∈ B, IsOpen V := by
      rintro V ⟨z, r, _, rfl, _⟩
      exact Metric.isOpen_ball
    obtain ⟨T, hTc, hTB, hT⟩ := TopologicalSpace.isOpen_sUnion_countable B hBo
    rw [← hBU, ← hT]
    apply MeasurableSet.sUnion hTc
    intro V hV
    obtain ⟨z, r, _, rfl, _⟩ := hTB hV
    exact hball z r
  · apply MeasurableSpace.generateFrom_le
    rintro B ⟨z, r, rfl⟩
    exact Metric.isClosed_closedBall.measurableSet

theorem sameBorelValues_of_closedBall_eq (E F : ProjectionValuedMeasure ℂ H)
    (hballs : ∀ z : ℂ, ∀ r : ℝ, 0 ≤ r → E (Metric.closedBall z r) = F (Metric.closedBall z r)) :
    SameBorelValues E F := by
  have hbase (B : Set ℂ) (hB : B ∈ closedBalls) : E B = F B := by
    obtain ⟨z, r, rfl⟩ := hB
    by_cases hr : 0 ≤ r
    · exact hballs z r hr
    · rw [Metric.closedBall_of_neg (not_le.mp hr), E.map_empty, F.map_empty]
  have hmeas (B : Set ℂ) (hB : B ∈ closedBalls) : MeasurableSet B := by
    obtain ⟨z, r, rfl⟩ := hB
    exact measurableSet_closedBall
  have hpi (B : Set ℂ) (hB : B ∈ generatePiSystem closedBalls) : E B = F B := by
    induction hB using generatePiSystem_induction with
    | base B hB => exact hbase B hB
    | inter A B hA hB _ ihA ihB =>
      have hmA := generatePiSystem_measurableSet hmeas A hA
      have hmB := generatePiSystem_measurableSet hmeas B hB
      rw [← E.inter A B hmA hmB, ← F.inter A B hmA hmB, ihA, ihB]
  have hgen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom (generatePiSystem closedBalls) := by
    rw [generateFrom_generatePiSystem_eq]
    exact borel_generateFrom_closedBalls
  have hcoeff (x y : H) : E.coefficientMeasure x y = F.coefficientMeasure x y := by
    refine VectorMeasure.ext_of_generateFrom (generatePiSystem closedBalls) ?_ hgen
      (isPiSystem_generatePiSystem closedBalls) ?_
    · intro B hB
      have hm := generatePiSystem_measurableSet hmeas B hB
      rw [E.coefficientMeasure_apply x y B hm, F.coefficientMeasure_apply x y B hm]
      exact congrArg (fun P : H →L[ℂ] H => inner ℂ x (P y)) (hpi B hB)
    · rw [E.coefficientMeasure_apply x y univ MeasurableSet.univ,
        F.coefficientMeasure_apply x y univ MeasurableSet.univ]
      simp only [coefficient, Spec.CoefficientValue, E.univ, F.univ]
  intro B hB
  ext y
  apply ext_inner_left ℂ
  intro x
  have h := congrArg (fun ν : ComplexMeasure ℂ => ν B) (hcoeff x y)
  simpa only [E.coefficientMeasure_apply x y B hB, F.coefficientMeasure_apply x y B hB,
    coefficient, Spec.CoefficientValue] using h


/-- Uniqueness on Borel sets and both spectral support assertions. -/
theorem spectral_uniqueness_and_support : Spec.SpectralUniquenessAndSupport.{u} := by
  intro H _ _ _ N _ _ _ E hE
  refine ⟨SpectralRepresentation.support_of_resolves N E
    (isClosed_operatorSpectrum N) hE, ?_⟩
  intro F hF
  obtain ⟨C, hC, _⟩ := hE
  obtain ⟨D, hD, _⟩ := hF
  apply sameBorelValues_of_closedBall_eq E F
  intro z r hr
  exact SpectralRepresentation.closedBall_eq_of_integral_eq C D (hC.trans hD.symm) z r hr

theorem real_support_of_selfAdjoint_resolves (N : Operator ℂ H H)
    (ha : adjointValue N = N) (E : ProjectionValuedMeasure ℂ H) (h : Resolves N E) :
    E {z | z.im ≠ 0} = 0 := by
  obtain ⟨C, heq, _⟩ := h
  have hsa : (measurableIntegral C (fun z : ℂ => z)).adjoint =
      measurableIntegral C (fun z : ℂ => z) := by
    rw [heq]
    exact ha
  have hB : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isClosed_eq Complex.continuous_im continuous_const).isOpen_compl.measurableSet
  ext x
  have hae := C.symbol_real_ae_of_selfAdjoint (fun z : ℂ => z) measurable_id hsa x
  have hm : C.measure x {z | z.im ≠ 0} = 0 := ae_iff.mp hae
  rw [C.measure_apply x _ hB] at hm
  have hn : ‖E {z | z.im ≠ 0} x‖ = 0 := by
    have := ENNReal.ofReal_eq_zero.mp hm
    nlinarith [norm_nonneg (E {z | z.im ≠ 0} x)]
  exact norm_eq_zero.mp hn

theorem realResolves_of_selfAdjoint_resolves (N : Operator ℂ H H)
    (ha : adjointValue N = N) (E : ProjectionValuedMeasure ℂ H) (h : Resolves N E) :
    ∃ F : ProjectionValuedMeasure ℝ H, RealResolves N F := by
  obtain ⟨C, heq, _⟩ := h
  have hsa : (measurableIntegral C (fun z : ℂ => z)).adjoint =
      measurableIntegral C (fun z : ℂ => z) := by
    rw [heq]
    exact ha
  let C' := C.map Complex.re Complex.continuous_re.measurable
  have hInt : measurableIntegral C' (fun t : ℝ => (t : ℂ)) = N := by
    rw [C.measurableIntegral_map]
    apply Eq.trans _ heq
    apply C.measurableIntegral_congr_ae _ _
      (Complex.measurable_ofReal.comp Complex.continuous_re.measurable) measurable_id
    intro x
    filter_upwards [C.symbol_real_ae_of_selfAdjoint (fun z : ℂ => z) measurable_id hsa x] with z hz
    apply Complex.ext
    · rfl
    · simpa using hz.symm
  refine ⟨E.map Complex.re Complex.continuous_re.measurable, C', hInt, ?_⟩
  intro x
  rw [← hInt]
  exact measurableIntegral_domain C' Complex.measurable_ofReal x

theorem selfadjoint_spectral_of_existence (hex : Spec.SpectralExistence.{u}) :
    Spec.SelfAdjointSpectralTheorem.{u} := by
  intro H _ _ _ N hd hc ha
  obtain ⟨E, hE⟩ := hex H N hd hc (by rw [ha])
  exact ⟨realResolves_of_selfAdjoint_resolves N ha E hE,
    fun F hF => real_support_of_selfAdjoint_resolves N ha F hF⟩


/-- The real-support specialization, including an actual PVM on ℝ. -/
theorem selfadjoint_spectral : Spec.SelfAdjointSpectralTheorem.{u} :=
  selfadjoint_spectral_of_existence spectral_existence

/-- The complete source statement, assembled from the five component results. -/
theorem unbounded_normal_spectral : Spec.FullTheorem.{u} :=
  ⟨spectral_existence, spectral_uniqueness_and_support, selfadjoint_spectral,
    bounded_normal_decomposition, multiplication_model⟩

end ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
