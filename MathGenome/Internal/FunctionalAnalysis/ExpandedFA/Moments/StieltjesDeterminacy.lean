import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.StieltjesDeterminacy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.StieltjesExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.HamburgerDeterminacy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.FriedrichsKreinResolventBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Multiplication.MultiplierTranspose
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace ExpandedFA.Moments.StieltjesDeterminacy
open Unbounded PolynomialMomentHilbertSpaceSpec StieltjesExistence
open FriedrichsExtension ClosedNonnegativeForms KreinNonnegativeExtension
open FriedrichsKreinResolventBounds HamburgerDeterminacy

/-- The zero-mass case requires no normalization of the constant vector. -/
theorem zero_mass : Spec.ZeroMass := by
  intro m h h0
  obtain ⟨hzero, hu⟩ := StieltjesExistence.zero_mass m h h0
  exact ⟨0, hzero, hu⟩

/-- Pass from the half-line representation to the unrestricted moment
predicate, retaining absolute integrability. -/
theorem represents_hamburger {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : Represents μ m) : RepresentsHamburgerMoments m μ := by
  refine ⟨hμ.1, ?_, fun n => (hμ.2.2 n).2⟩
  intro n
  simpa only [← abs_pow, Real.norm_eq_abs] using (hμ.2.2 n).1.norm

/-- The scalar spectral measure of a chosen nonnegative extension is a
Stieltjes representing measure; the chosen spectral realization is retained. -/
theorem spectral_measure_represents_nonnegative (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : NonnegativeExtension m h A)
    {E : SpectralMeasure.ProjectionValuedMeasure ℝ (MomentHilbertSpace m h)}
    (C : MeasurableSpectralCalculus.BoundedRealization E)
    (hCA : MeasurableSpectralCalculus.measurableIntegral C (fun t : ℝ => (t : ℂ)) = A) :
    Represents (C.measure (constantValue m h)) m := by
  have hm := HamburgerDeterminacy.spectral_measure_represents m h A hA.1
    ⟨hA.2.1, hA.2.2.2.1⟩ C hCA
  refine ⟨hm.1, ?_, fun n => ⟨HamburgerExistenceProof.RepresentsHamburgerMoments.integrable_pow hm n, hm.2.2 n⟩⟩
  exact (NonnegativeSpectralSupport.nonnegative_support A E C hCA hA.2.2.2.2).2 _

/-- Equality of Stieltjes measures forces equality of the nonnegative
extensions. Cyclicity is supplied by the canonical polynomial vectors, rather
than by a density assertion in an arbitrary representing L² space. -/
theorem nonnegative_extension_unique_of_determinate (m : ℕ → ℝ)
    (h : HankelNonnegative m) (hd : Determinate m)
    (A B : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : NonnegativeExtension m h A) (hB : NonnegativeExtension m h B) : A = B := by
  obtain ⟨⟨EA, C, hCA, _⟩, _⟩ :=
    UnboundedNormalSpectralTheorem.selfadjoint_spectral _ A
      hA.2.1 hA.2.2.1 hA.2.2.2.1.symm
  obtain ⟨⟨EB, D, hDB, _⟩, _⟩ :=
    UnboundedNormalSpectralTheorem.selfadjoint_spectral _ B
      hB.2.1 hB.2.2.1 hB.2.2.2.1.symm
  have he : C.measure (constantValue m h) = D.measure (constantValue m h) :=
    hd.unique (spectral_measure_represents_nonnegative m h A hA C hCA)
      (spectral_measure_represents_nonnegative m h B hB D hDB)
  obtain ⟨R, hR⟩ := spectral_resolvent_coefficient C A hCA Complex.I (by simp)
    (constantValue m h)
  obtain ⟨Q, hQ⟩ := spectral_resolvent_coefficient D B hDB Complex.I (by simp)
    (constantValue m h)
  apply extension_eq_of_resolvent_coefficient m h A B
    ⟨hA.2.1, hA.2.2.2.1⟩ ⟨hB.2.1, hB.2.2.2.1⟩ hA.1 hB.1 Complex.I R Q
  rw [hR, hQ, he]

/-- The measure-to-extension half of the exact Stieltjes criterion. -/
theorem measure_implies_extension : Spec.MeasureImpliesExtension := by
  intro m h hs hd
  obtain ⟨A, hA, _⟩ := nonnegative_extension m h hs
  exact ⟨A, hA, fun B hB => nonnegative_extension_unique_of_determinate m h hd B A hB hA⟩

section ResolventOrder
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Transport preserves the bounded inverse underlying a positive resolvent. -/
theorem positive_resolvent_transport {A B : Operator ℂ H H} {a : ℝ}
    (he : A = B) (R : PositiveResolvent A a) : (he ▸ R).inverse = R.inverse := by
  cases he
  rfl

/-- A positive resolvent is unique, including its action on the full space. -/
theorem positive_resolvent_unique {A : Operator ℂ H H} {a : ℝ}
    (R Q : PositiveResolvent A a) : R.inverse = Q.inverse := by
  ext f
  have hh := Q.left_inverse ⟨R.inverse f, R.mem_domain f⟩
  rw [R.right_inverse f] at hh
  exact hh.symm

/-- One inverse determines both the operator's action and its entire domain. -/
theorem operator_eq_of_positive_resolvent {A B : Operator ℂ H H} {a : ℝ}
    (R : PositiveResolvent A a) (Q : PositiveResolvent B a)
    (he : R.inverse = Q.inverse) : A = B := by
  have hle {A B : Operator ℂ H H} (R : PositiveResolvent A a)
      (Q : PositiveResolvent B a) (he : R.inverse = Q.inverse) : A ≤ B := by
    apply LinearPMap.le_of_le_graph
    rintro ⟨x, y⟩ hxy
    obtain ⟨z, rfl, rfl⟩ := A.mem_graph_iff.mp hxy
    let f := A z + (a : ℂ) • (z : H)
    have hz : Q.inverse f = (z : H) := by rw [← he]; exact R.left_inverse z
    have hact := Q.right_inverse f
    conv_lhs at hact => rhs; rw [hz]
    have hval : B ⟨Q.inverse f, Q.mem_domain f⟩ = A z := by
      change B ⟨Q.inverse f, Q.mem_domain f⟩ + (a : ℂ) • (z : H) =
        A z + (a : ℂ) • (z : H) at hact
      exact add_right_cancel hact
    have hg := B.mem_graph ⟨Q.inverse f, Q.mem_domain f⟩
    rw [hval] at hg
    simpa only [hz] using hg
  exact le_antisymm (hle R Q he) (hle Q R he.symm)

/-- Antisymmetry of quadratic-form order for bounded symmetric operators. -/
theorem formLE_antisymm (A B : H →L[ℂ] H)
    (hA : ∀ x y, inner ℂ (A x) y = inner ℂ x (A y))
    (hB : ∀ x y, inner ℂ (B x) y = inner ℂ x (B y))
    (hab : FormLE A B) (hba : FormLE B A) : A = B := by
  have he : A.toLinearMap = B.toLinearMap := (ext_inner_map _ _).mp (fun x => by
    have hsa : A.toLinearMap.IsSymmetric := hA
    have hsb : B.toLinearMap.IsSymmetric := hB
    rw [← hsa.coe_re_inner_apply_self, ← hsb.coe_re_inner_apply_self]
    congr 1
    change RCLike.re (inner ℂ (A x) x) = RCLike.re (inner ℂ (B x) x)
    rw [hA, hB]
    exact le_antisymm (hab x) (hba x))
  ext x
  exact congrArg (fun f : H →ₗ[ℂ] H => f x) he

end ResolventOrder

/-- Every closed extension contains the closure of the polynomial graph. -/
theorem closure_le_of_extension (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : NonnegativeExtension m h A) : minimalClosure m h ≤ A := by
  have hs : IsSymmetric (multiplicationValue m h) :=
    ⟨minimalMultiplication_dense m h,
      LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
        (minimalMultiplication_symmetric m h)⟩
  apply LinearPMap.le_of_le_graph
  rw [← hs.isClosable.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hA.1) hA.2.2.1

/-- The closed canonical polynomial operator is still nonnegative, including
in the degenerate moment space. -/
theorem closure_semibounded (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelNonnegative (shiftedMoments m)) :
    SemiboundedSymmetric (minimalClosure m h) 0 := by
  obtain ⟨A, hA, _⟩ := nonnegative_extension m h hs
  have hle := closure_le_of_extension m h A hA
  have hS : IsSymmetric (multiplicationValue m h) :=
    ⟨minimalMultiplication_dense m h,
      LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
        (minimalMultiplication_symmetric m h)⟩
  have hc := HamburgerExistenceProof.symmetric_closure _ hS
  have ha : A.IsFormalAdjoint A := by
    have hh := LinearPMap.adjoint_isFormalAdjoint hA.2.1
    change (HilbertAdjointSpec.adjointValue A).IsFormalAdjoint A at hh
    rwa [← hA.2.2.2.1] at hh
  refine ⟨hc.1, ?_, ?_⟩
  · intro x y
    let ax : A.domain := ⟨x, hle.1 x.property⟩
    let ay : A.domain := ⟨y, hle.1 y.property⟩
    have hx : A ax = minimalClosure m h x := (hle.2 rfl).symm
    have hy : A ay = minimalClosure m h y := (hle.2 rfl).symm
    have hh := ha ax ay
    rw [hx, hy] at hh
    exact hh
  · intro x
    have hh := hA.2.2.2.2 ⟨x, hle.1 x.property⟩
    rw [← hle.2 (x := x) rfl] at hh
    simpa only [zero_mul, RCLike.re_to_complex] using hh

/-- The metadata in `NonnegativeExtension` supplies the precise form
hypotheses used by the order theorem. -/
theorem extension_semibounded (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : NonnegativeExtension m h A) : SemiboundedSymmetric A 0 := by
  refine ⟨hA.2.1, ?_, fun x => by simpa only [zero_mul, RCLike.re_to_complex] using hA.2.2.2.2 x⟩
  have hh := LinearPMap.adjoint_isFormalAdjoint hA.2.1
  change (HilbertAdjointSpec.adjointValue A).IsFormalAdjoint A at hh
  rwa [← hA.2.2.2.1] at hh

/-- Turn an extension of the closed canonical graph into the upstream
extension predicate, which is phrased on the initial polynomial graph. -/
theorem nonnegativeExtension_of_closure (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hle : minimalClosure m h ≤ A) (hd : Dense (A.domain : Set (MomentHilbertSpace m h)))
    (ha : A = HilbertAdjointSpec.adjointValue A)
    (hn : ∀ x : A.domain, 0 ≤ (inner ℂ (x : MomentHilbertSpace m h) (A x)).re) :
    NonnegativeExtension m h A := by
  refine ⟨(multiplicationValue m h).le_closure.trans hle, hd, ?_, ha, hn⟩
  rw [ha]
  exact LinearPMap.adjoint_isClosed hd

/-- The actual Friedrichs and Krein constructions both qualify as
nonnegative extensions of the original polynomial operator. -/
theorem extremal_extensions (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : SemiboundedSymmetric (minimalClosure m h) 0)
    (F : FormClosure (operatorForm (minimalClosure m h) 0 hs))
    (K : Construction (minimalClosure m h) hs) :
    NonnegativeExtension m h F.closedForm.associatedOperator ∧
      NonnegativeExtension m h K.extension := by
  constructor
  · exact nonnegativeExtension_of_closure m h _ (friedrichs_le _ hs F)
      (F.closedForm.associated_dense F.closed) (F.closedForm.associated_selfAdjoint F.closed)
      F.closedForm.associated_nonnegative
  · exact nonnegativeExtension_of_closure m h _ K.extends_operator
      K.extension_dense K.selfAdjoint K.nonnegative

/-- If the extremal operators coincide, every nonnegative extension has the
same positive resolvent and hence exactly the same graph. -/
theorem extension_unique_of_extremalsEqual (m : ℕ → ℝ) (h : HankelNonnegative m)
    (he : ExtremalsEqual m h) : ∃! A, NonnegativeExtension m h A := by
  obtain ⟨hs, F, K, hFK⟩ := he
  have heq : F.closedForm.associatedOperator = K.extension :=
    F.closedForm.associated_unique F.closedForm.associated hFK
  have hExt := extremal_extensions m h hs F K
  refine ⟨K.extension, hExt.2, ?_⟩
  intro A hA
  obtain ⟨R⟩ := selfAdjoint_resolvent A (extension_semibounded m h A hA)
    hA.2.2.2.1 1 (by norm_num)
  obtain ⟨RF⟩ := form_resolvent F.closedForm F.closed 1 (by norm_num)
  let RK : PositiveResolvent K.extension 1 := heq ▸ RF
  let i : MomentHilbertSpace m h →ₗᵢ[ℂ] MomentHilbertSpace m h := LinearIsometry.id
  have hAlong : ExtendsAlong i (minimalClosure m h) A := by
    intro y
    have hle := closure_le_of_extension m h A hA
    exact ⟨hle.1 y.property, (hle.2 rfl).symm⟩
  have hl := friedrichs_bound i _ hs F 1 (by norm_num) RF A
    (extension_semibounded m h A hA) hAlong R
  have hu := krein_bound i _ hs K 1 (by norm_num) RK A
    (extension_semibounded m h A hA) hAlong R
  have hc : compression i R.inverse = R.inverse := by
    ext x
    simp [compression, i]
  rw [hc] at hl hu
  have hRK : RK.inverse = RF.inverse := positive_resolvent_transport heq RF
  rw [hRK] at hu
  have hR := formLE_antisymm RF.inverse R.inverse RF.selfAdjoint R.selfAdjoint hl hu
  have hRR : R.inverse = RK.inverse := hR.symm.trans hRK.symm
  exact operator_eq_of_positive_resolvent R RK hRR

/-- Exact extension uniqueness is equivalent to equality of the Friedrichs
and Krein extensions; no unrestricted uniqueness claim is used. -/
theorem extremal_criterion : Spec.ExtremalCriterion := by
  intro m h hs
  constructor
  · intro hu
    let hc := closure_semibounded m h hs
    let F := formClosure (minimalClosure m h) 0 hc
    let K := construction (minimalClosure m h) hc
    have he := extremal_extensions m h hc F K
    have heq := hu.unique he.1 he.2
    exact ⟨hc, F, K, heq ▸ F.closedForm.associated⟩
  · exact extension_unique_of_extremalsEqual m h

section TransformUniqueness
open HamburgerDeterminacySpec

/-- Nonnegative support expressed as an almost-everywhere inequality. -/
theorem nonnegative_ae {μ : Measure ℝ} (hμ : μ (Set.Iio 0) = 0) :
    ∀ᵐ t : ℝ ∂μ, 0 ≤ t := by
  have hh : ∀ᵐ t : ℝ ∂μ, t ∉ Set.Iio 0 := by
    apply ae_iff.mpr
    have he : {t : ℝ | ¬ t ∉ Set.Iio 0} = Set.Iio 0 := by ext t; simp
    rw [he]
    exact hμ
  exact hh.mono fun t ht => le_of_not_gt ht

/-- Reflecting the variable puts the analytic transform on the usual slit
plane. The only support assumption is concentration on [0,∞). -/
theorem analytic_reflected_transform (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    AnalyticOnNhd ℂ (fun z : ℂ => MeasureTheory.resolventTransform μ (-z))
      Complex.slitPlane := by
  have hs : μ.support ⊆ Set.Ici 0 :=
    MeasureTheory.Measure.support_subset_of_isClosed isClosed_Ici (nonnegative_ae hμ)
  intro z hz
  have hz' : -z ∉ algebraMap ℝ ℂ '' μ.support := by
    rintro ⟨t, ht, he⟩
    have hnt : 0 ≤ t := hs ht
    have hre : -z.re = t := by simpa using (congrArg Complex.re he).symm
    have him : z.im = 0 := by simpa using congrArg Complex.im he
    rcases hz with hz | hz
    · linarith
    · exact hz him
  have hopen : IsOpen (algebraMap ℝ ℂ '' μ.support)ᶜ := by
    rw [isOpen_compl_iff]
    change IsClosed (Complex.ofReal '' μ.support)
    exact Complex.isUniformEmbedding_ofReal.isClosedEmbedding.isClosedMap _ MeasureTheory.Measure.isClosed_support
  have ha := (MeasureTheory.analyticOn_resolventTransform (μ := μ)).analyticAt
    (hopen.mem_nhds hz')
  exact ha.comp (by fun_prop)

/-- At positive real parameters the complex resolvent transform is precisely
the real Stieltjes transform, embedded into ℂ. -/
theorem reflected_transform_ofReal (μ : Measure ℝ) (a : ℝ) :
    MeasureTheory.resolventTransform μ (-(a : ℂ)) = (stieltjesTransform μ a : ℂ) := by
  rw [MeasureTheory.resolventTransform, stieltjesTransform, ← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    simp [_root_.resolvent, Ring.inverse_eq_inv', sub_neg_eq_add, ← Complex.ofReal_add]

/-- A finite positive measure on the half-line is determined by all its
negative-axis resolvent values. Analytic continuation on the reflected slit
plane reduces this to the upstream Cauchy-transform injectivity theorem. -/
theorem stieltjes_transform_injectivity : Spec.TransformInjectivity := by
  intro μ ν _ _ hμ hν he
  have hreal : ∀ a : ℝ, 0 < a →
      MeasureTheory.resolventTransform μ (-(a : ℂ)) =
        MeasureTheory.resolventTransform ν (-(a : ℂ)) := by
    intro a ha
    rw [reflected_transform_ofReal, reflected_transform_ofReal, he a ha]
  have hacc : (1 : ℂ) ∈ closure
      ({z : ℂ | MeasureTheory.resolventTransform μ (-z) =
          MeasureTheory.resolventTransform ν (-z)} \ {1}) := by
    have hcl : (1 : ℝ) ∈ closure (Set.Ioi (1 : ℝ)) := by simp
    have hc := mem_closure_image Complex.continuous_ofReal.continuousAt hcl
    apply closure_mono (s := Complex.ofReal '' Set.Ioi (1 : ℝ)) _ hc
    rintro z ⟨a, ha, rfl⟩
    refine ⟨hreal a (lt_trans zero_lt_one ha), ?_⟩
    simpa only [Set.mem_singleton_iff, Complex.ofReal_eq_one] using ne_of_gt ha
  have heq := (analytic_reflected_transform μ hμ).eqOn_of_preconnected_of_mem_closure
    (analytic_reflected_transform ν hν)
    (Complex.starConvex_one_slitPlane.isPathConnected Complex.one_mem_slitPlane).isConnected.isPreconnected
    Complex.one_mem_slitPlane hacc
  apply cauchy_transform_injectivity μ ν
  intro z hz
  have hh := heq (show -z ∈ Complex.slitPlane from Or.inr (by simpa))
  simp only [neg_neg] at hh
  have hconv (ρ : Measure ℝ) : MeasureTheory.resolventTransform ρ z =
      -cauchyTransform ρ z := by
    rw [MeasureTheory.resolventTransform, cauchyTransform, ← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [_root_.resolvent, Ring.inverse_eq_inv', Complex.coe_algebraMap]
      change ((t : ℂ) - z)⁻¹ = -(z - (t : ℂ))⁻¹
      rw [← neg_sub, inv_neg]
  rw [hconv, hconv] at hh
  exact neg_injective hh
end TransformUniqueness

section RepresentingResolvents
open Multiplication Polynomial

/-- Polynomial evaluation in the representing space, with no completeness
claim for the polynomial image. -/
theorem representing_class_ae {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : Represents μ m) (h : HankelNonnegative m) (p : MomentPolynomials m h) :
    (representingIsometry (represents_hamburger hμ) h (polynomialClass m h p) : ℝ → ℂ)
      =ᵐ[μ] fun t => (rawPolynomial p).eval (t : ℂ) := by
  rw [representingIsometry_class]
  exact (memLp_polynomial_eval (represents_hamburger hμ) (rawPolynomial p)).coeFn_toLp

/-- The full real-coordinate multiplier is nonnegative for a measure
concentrated on [0,∞). This refers to its maximal L² domain. -/
theorem representing_multiplier_semibounded (μ : Measure ℝ)
    (hμ : μ (Set.Iio 0) = 0) :
    SemiboundedSymmetric (maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))) 0 := by
  let T := maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))
  have hd : Dense (T.domain : Set (Lp ℂ 2 μ)) :=
    maximalLpMultiplier_denselyDefined μ 2 (by norm_num) _ Complex.continuous_ofReal.measurable
  have ha : T = HilbertAdjointSpec.adjointValue T := by
    exact (LinearPMap.isSelfAdjoint_def.mp (multiplier_real_selfAdjoint μ _
      Complex.continuous_ofReal.measurable (Filter.Eventually.of_forall (by simp)))).symm
  refine ⟨hd, ?_, ?_⟩
  · have hh := LinearPMap.adjoint_isFormalAdjoint hd
    change (HilbertAdjointSpec.adjointValue T).IsFormalAdjoint T at hh
    rwa [← ha] at hh
  · intro x
    change 0 * _ ≤ (inner ℂ (x : Lp ℂ 2 μ) (T x)).re
    rw [zero_mul, L2.inner_def]
    change 0 ≤ RCLike.re (∫ t : ℝ, inner ℂ ((x : Lp ℂ 2 μ) t) ((T x) t) ∂μ)
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (x : Lp ℂ 2 μ) (T x))]
    apply integral_nonneg_of_ae
    filter_upwards [maximalLpMultiplier_apply μ 2 (fun t : ℝ => (t : ℂ)) x,
      nonnegative_ae hμ] with t ht hnt
    change 0 ≤ (inner ℂ ((x : Lp ℂ 2 μ) t) ((T x) t)).re
    rw [ht]
    have he : inner ℂ ((x : Lp ℂ 2 μ) t) ((t : ℂ) * (x : Lp ℂ 2 μ) t) =
        (t : ℂ) * inner ℂ ((x : Lp ℂ 2 μ) t) ((x : Lp ℂ 2 μ) t) :=
      inner_smul_right _ _ _
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply mul_nonneg hnt
    simpa only [RCLike.re_to_complex] using
      (inner_self_nonneg (𝕜 := ℂ) (x := (x : Lp ℂ 2 μ) t))

/-- Polynomial multiplication intertwines with the full L² multiplier. The
closed-graph argument passes from the polynomial core to its graph closure. -/
theorem representing_multiplier_extends {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : Represents μ m) (h : HankelNonnegative m) :
    ExtendsAlong (representingIsometry (represents_hamburger hμ) h)
      (minimalClosure m h) (maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))) := by
  let J := representingIsometry (represents_hamburger hμ) h
  let T := maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))
  have hS : IsSymmetric (multiplicationValue m h) :=
    ⟨minimalMultiplication_dense m h,
      LinearPMap.IsFormalAdjoint.le_adjoint (minimalMultiplication_dense m h)
        (minimalMultiplication_symmetric m h)⟩
  have hcore : ∀ y : (multiplicationValue m h).domain,
      (J (y : MomentHilbertSpace m h), J (multiplicationValue m h y)) ∈ T.graph := by
    intro y
    obtain ⟨p, hp⟩ := y.property
    have hy : y = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ := Subtype.ext hp.symm
    subst y
    rw [minimalMultiplication_apply]
    apply (mem_maximalMultiplier_graph_iff μ 2 _ _ _).mpr
    filter_upwards [representing_class_ae hμ h p,
      representing_class_ae hμ h (ofPolynomial (X * rawPolynomial p))] with t ht htp
    change J (polynomialClass m h (ofPolynomial (X * rawPolynomial p))) t =
      (t : ℂ) * J (polynomialClass m h p) t
    rw [ht, htp]
    simp
  intro y
  have hg := graph_closure_intertwining _ hS.isClosable T
    (maximalLpMultiplier_isClosed μ 2 _) J hcore y
  refine ⟨LinearPMap.mem_domain_of_mem_graph hg, ?_⟩
  exact T.mem_graph_snd_inj (T.mem_graph _) hg rfl

/-- The coefficient of any positive resolvent of the ambient multiplier is
exactly the Stieltjes transform, at the original unnormalized constant vector. -/
theorem ambient_resolvent_coefficient {m : ℕ → ℝ} {μ : Measure ℝ}
    (hμ : Represents μ m) (h : HankelNonnegative m)
    (a : ℝ) (ha : 0 < a)
    (R : PositiveResolvent (maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))) a) :
    (inner ℂ (constantValue m h)
      (compression (representingIsometry (represents_hamburger hμ) h) R.inverse
        (constantValue m h))).re = stieltjesTransform μ a := by
  let J := representingIsometry (represents_hamburger hμ) h
  let e := constantValue m h
  let T := maximalMultiplier μ 2 (fun t : ℝ => (t : ℂ))
  let w := R.inverse (J e)
  let x : T.domain := ⟨w, R.mem_domain (J e)⟩
  have he : (J e : ℝ → ℂ) =ᵐ[μ] fun _ => (1 : ℂ) := by
    have hh := representing_class_ae hμ h 1
    change (J e : ℝ → ℂ) =ᵐ[μ] fun t => (1 : ℂ[X]).eval (t : ℂ) at hh
    simpa only [Polynomial.eval_one] using hh
  have hsum : (T x + (a : ℂ) • w : Lp ℂ 2 μ) = J e := R.right_inverse (J e)
  have hw : (w : ℝ → ℂ) =ᵐ[μ] fun t => ((t + a : ℝ) : ℂ)⁻¹ := by
    filter_upwards [Lp.coeFn_add (T x) ((a : ℂ) • w),
      Lp.coeFn_smul (a : ℂ) w, maximalLpMultiplier_apply μ 2 (fun t : ℝ => (t : ℂ)) x,
      he, nonnegative_ae hμ.2.1] with t hadd hsmul hmul he hnt
    have ht : (t : ℂ) * w t + (a : ℂ) * w t = 1 := by
      have hh := congrFun (congrArg (fun f : Lp ℂ 2 μ => (f : ℝ → ℂ)) hsum) t
      rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hmul, he] at hh
      exact hh
    have hne : ((t + a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith))
    apply (mul_left_cancel₀ hne)
    rw [mul_inv_cancel₀ hne]
    simpa only [Complex.ofReal_add, add_mul] using ht
  change (inner ℂ e (J.toContinuousLinearMap.adjoint (R.inverse (J e)))).re = _
  rw [J.toContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  change RCLike.re (∫ t : ℝ, inner ℂ ((J e) t) (w t) ∂μ) = stieltjesTransform μ a
  rw [← integral_re (L2.integrable_inner (𝕜 := ℂ) (J e) w)]
  unfold stieltjesTransform
  apply integral_congr_ae
  filter_upwards [he, hw] with t ht hu
  change (inner ℂ ((J e) t) (w t)).re = (t + a)⁻¹
  rw [ht, hu, ← Complex.ofReal_inv]
  simp only [RCLike.inner_apply, map_one, mul_one, Complex.ofReal_re]
end RepresentingResolvents

section CompressionOrder
universe u v
variable {H : Type u} {G : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Equality of the extremal operators fixes compressed resolvents in every
Hilbert enlargement. This does not assert that the embedded subspace reduces
the ambient operator. -/
theorem compression_eq_of_equal_extremals (S : Operator ℂ H H)
    (hs : SemiboundedSymmetric S 0)
    (F : FormClosure (operatorForm S 0 hs)) (K : Construction S hs)
    (hFK : F.closedForm.associatedOperator = K.extension)
    (i : H →ₗᵢ[ℂ] G) (T : Operator ℂ G G) (hT : SemiboundedSymmetric T 0)
    (hAlong : ExtendsAlong i S T)
    (a : ℝ) (ha : 0 < a) (RF : PositiveResolvent F.closedForm.associatedOperator a)
    (RT : PositiveResolvent T a) : compression i RT.inverse = RF.inverse := by
  let RK : PositiveResolvent K.extension a := hFK ▸ RF
  have hl := friedrichs_bound i S hs F a ha RF T hT hAlong RT
  have hu := krein_bound i S hs K a ha RK T hT hAlong RT
  have hRK : RK.inverse = RF.inverse := positive_resolvent_transport hFK RF
  rw [hRK] at hu
  exact formLE_antisymm _ _ (compression_symmetric i T a RT) RF.selfAdjoint hu hl
end CompressionOrder

/-- The order bounds force the same scalar resolvent values for all
representing measures, including those with nondense polynomial subspaces. -/
theorem compressed_coefficient : Spec.CompressedCoefficient := by
  intro m h _hs he μ ν hμ hν a ha
  obtain ⟨hs, F, K, hFK⟩ := he
  have hFK' : F.closedForm.associatedOperator = K.extension :=
    F.closedForm.associated_unique F.closedForm.associated hFK
  obtain ⟨RF⟩ := form_resolvent F.closedForm F.closed a ha
  have hvalue (ρ : Measure ℝ) (hρ : Represents ρ m) :
      stieltjesTransform ρ a =
        (inner ℂ (constantValue m h) (RF.inverse (constantValue m h))).re := by
    let J := representingIsometry (represents_hamburger hρ) h
    let T := Multiplication.maximalMultiplier ρ 2 (fun t : ℝ => (t : ℂ))
    have hT : SemiboundedSymmetric T 0 := representing_multiplier_semibounded ρ hρ.2.1
    have ht : T = HilbertAdjointSpec.adjointValue T := by
      exact (LinearPMap.isSelfAdjoint_def.mp (Multiplication.multiplier_real_selfAdjoint ρ _
        Complex.continuous_ofReal.measurable (Filter.Eventually.of_forall (by simp)))).symm
    obtain ⟨RT⟩ := selfAdjoint_resolvent T hT ht a ha
    have hc := compression_eq_of_equal_extremals _ hs F K hFK' J T hT
      (representing_multiplier_extends hρ h) a ha RF RT
    have hv := ambient_resolvent_coefficient hρ h a ha RT
    rw [hc] at hv
    exact hv.symm
  exact (hvalue μ hμ).trans (hvalue ν hν).symm

/-- Equality of Friedrichs and Krein extensions implies uniqueness among all
finite positive half-line representing measures. -/
theorem determinate_of_extremalsEqual (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelNonnegative (shiftedMoments m)) (he : ExtremalsEqual m h) :
    Determinate m := by
  obtain ⟨μ, hμ⟩ := stieltjes_sufficiency m h hs
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  let := hμ.1
  let := hν.1
  exact stieltjes_transform_injectivity ν μ hν.2.1 hμ.2.1
    (compressed_coefficient m h hs he ν μ hν hμ)

/-- The exact Stieltjes uniqueness criterion, in the original polynomial
Hilbert space. No essential-self-adjointness condition is introduced. -/
theorem stieltjes_determinacy : Spec.Determinacy := by
  intro m h hs
  exact ⟨measure_implies_extension m h hs,
    fun hu => determinate_of_extremalsEqual m h hs ((extremal_criterion m h hs).mp hu)⟩

/-- Equality is valid for every realization of the extremal constructions,
not only for the witnesses used to express `ExtremalsEqual`. -/
theorem chosen_extremal_criterion : Spec.ChosenExtremalCriterion := by
  intro m h hs hc F K SF hSF
  have heq : F.closedForm.associatedOperator = SF :=
    F.closedForm.associated_unique F.closedForm.associated hSF
  constructor
  · intro hd
    have hu := (stieltjes_determinacy m h hs).mp hd
    have hext := extremal_extensions m h hc F K
    rw [heq] at hext
    exact hu.unique hext.1 hext.2
  · intro he
    exact determinate_of_extremalsEqual m h hs ⟨hc, F, K, he ▸ hSF⟩

end ExpandedFA.Moments.StieltjesDeterminacy
