import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.RealExteriorDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.RealComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceBasisCyclicity

noncomputable section
open scoped InnerProductSpace lp
universe v w
namespace ExpandedFA.FredholmDeterminant.RealExteriorDefinitions

abbrev realCoordinateSpace := @Spec.RealCoordinateSpaceValue
abbrev realCoordinateWedge := @Spec.RealCoordinateWedgeValue
abbrev realCoordinateEmbedding := @Spec.RealCoordinateEmbeddingValue
abbrev realPrincipalMinor := @Spec.RealPrincipalMinorValue
abbrev realCoordinateOperator := @Spec.RealCoordinateOperatorValue
abbrev realExteriorOperator := @Spec.RealExteriorOperatorValue
abbrev realExteriorTrace := @Spec.RealExteriorTraceValue
abbrev realDeterminant := @Spec.RealDeterminantValue
abbrev complexParameterDeterminant := @Spec.ComplexParameterDeterminantValue

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma realPrincipalMinor_empty {α : Type w} (b : HilbertBasis α ℝ H) (T : H →L[ℝ] H) :
    realPrincipalMinor b T ∅ = 1 := by
  classical
  exact Matrix.det_isEmpty

lemma realPrincipalMinor_singleton {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (i : α) :
    realPrincipalMinor b T {i} = inner ℝ (b i) (T (b i)) := by
  classical
  let : Unique ({i} : Finset α) := {
    default := ⟨i, Finset.mem_singleton_self i⟩
    uniq := by intro j; apply Subtype.ext; exact Finset.mem_singleton.mp j.property }
  exact Matrix.det_unique _

lemma coefficient_zero (T : H →L[ℝ] H) [CompleteSpace H] : realExteriorTrace T 0 = 1 := by
  classical
  let e : Set.powersetCard (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℝ) (H := H)) 0 := ⟨∅, rfl⟩
  have he (s : Set.powersetCard (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℝ) (H := H)) 0) : s = e := by
    apply Subtype.ext
    exact Finset.card_eq_zero.mp s.property
  change (∑' s : Set.powersetCard _ 0, realPrincipalMinor ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T s.val) = 1
  rw [tsum_eq_single e (fun s hs => (hs (he s)).elim)]
  exact realPrincipalMinor_empty _ T

lemma coefficient_one (T : H →L[ℝ] H) [CompleteSpace H] :
    realExteriorTrace T 1 = ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue T := by
  classical
  let b := ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℝ) (H := H)
  let e := Set.powersetCard.ofSingleton (α := ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℝ) (H := H))
  change (∑' s : Set.powersetCard _ 1, realPrincipalMinor b T s.val) =
    ∑' i, inner ℝ (b i) (T (b i))
  rw [← e.tsum_eq (fun s => realPrincipalMinor b T s.val)]
  exact tsum_congr (realPrincipalMinor_singleton b T)

theorem coefficient_low_degrees : Spec.RealCoefficientLowDegrees.{v} := by
  intro H _ _ _ T
  exact ⟨coefficient_zero T, coefficient_one T⟩

variable [CompleteSpace H]
local instance : CompleteSpace (ExpandedFA.TraceIdeals.RealComplexification.Space H) := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace

lemma principalMinor_complexification {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (s : Finset α) :
    ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue (ExpandedFA.TraceIdeals.RealComplexification.basis b) (ExpandedFA.TraceIdeals.RealComplexification.operator T) s =
      (realPrincipalMinor b T s : ℂ) := by
  classical
  unfold ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue realPrincipalMinor Spec.RealPrincipalMinorValue
  simp only [ExpandedFA.TraceIdeals.RealComplexification.basis_apply, ExpandedFA.TraceIdeals.RealComplexification.operator_inclusion, ExpandedFA.TraceIdeals.RealComplexification.inner_inclusion]
  exact (RingHom.map_det Complex.ofRealHom _).symm

theorem principal_minor_bound : Spec.RealPrincipalMinorBound.{v,w} := by
  intro H _ _ _ T hT α b n
  letI : CompleteSpace (ExpandedFA.TraceIdeals.RealComplexification.Space H) := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace
  have hC := ExpandedFA.FredholmDeterminant.TraceClassDefinitions.principal_minor_traceNorm_bound (ExpandedFA.TraceIdeals.RealComplexification.operator T)
    ((ExpandedFA.TraceIdeals.RealComplexification.trace_ideal H H T).1.mp hT) (ExpandedFA.TraceIdeals.RealComplexification.basis b) n
  simpa only [principalMinor_complexification, Complex.norm_real,
    (ExpandedFA.TraceIdeals.RealComplexification.trace_ideal H H T).2 hT] using hC

/-- Compute the same complex exterior trace on the exterior basis induced by
any Hilbert basis, instead of identifying two chosen Hilbert bases. -/
lemma complex_minor_hasSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (T : E →L[ℂ] E) (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T)
    {α : Type w} (b : HilbertBasis α ℂ E) (n : ℕ) :
    HasSum (fun s : Set.powersetCard α n => ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.PrincipalMinorValue b T s.val)
      (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue T n) := by
  classical
  let c := ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℂ) (H := E)
  let A := ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorOperatorValue T n
  have hn := (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.exterior_construction T hT n).1
  simp only [ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.CoordinateWedgeValue] at hn
  have ht := (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.exterior_construction T hT n).2.1
  have htrace := (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.exterior_construction T hT n).2.2.2
  have hd := (TraceIdeals.TraceBasisCyclicity.diagonal_trace ℂ _ A ht _
    (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.ExteriorCoordinates.inducedBasis (n := n) c b)).2
  rw [htrace] at hd
  convert hd using 1
  funext s
  rw [ExpandedFA.FredholmDeterminant.TraceClassDefinitions.ExteriorCoordinates.inducedBasis_apply]
  dsimp only [A, c]
  rw [hn, ExpandedFA.FredholmDeterminant.TraceClassDefinitions.ExteriorCoordinates.inner_wedge]
  let e : Fin n ≃ s.val := (Finset.equivFinOfCardEq s.property).symm
  let M : Matrix s.val s.val ℂ := fun i j => inner ℂ (b i.val) (T (b j.val))
  change Matrix.det M = Matrix.det (M.submatrix e e)
  exact (Matrix.det_submatrix_equiv_self e M).symm

lemma real_minor_sum_cast {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    ((∑' s : Set.powersetCard α n, realPrincipalMinor b T s.val : ℝ) : ℂ) =
      ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue (ExpandedFA.TraceIdeals.RealComplexification.operator T) n := by
  have hs := ((principal_minor_bound T hT b n).1.of_norm.hasSum).mapL Complex.ofRealCLM
  have hc := complex_minor_hasSum (ExpandedFA.TraceIdeals.RealComplexification.operator T) ((ExpandedFA.TraceIdeals.RealComplexification.trace_ideal H H T).1.mp hT)
    (ExpandedFA.TraceIdeals.RealComplexification.basis b) n
  simp only [principalMinor_complexification] at hc
  exact HasSum.unique hs hc

lemma coefficient_cast (T : H →L[ℝ] H) (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    (realExteriorTrace T n : ℂ) = ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue (ExpandedFA.TraceIdeals.RealComplexification.operator T) n :=
  real_minor_sum_cast ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T hT n

lemma real_minor_hasSum {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    HasSum (fun s : Set.powersetCard α n => realPrincipalMinor b T s.val)
      (realExteriorTrace T n) := by
  have he : (∑' s : Set.powersetCard α n, realPrincipalMinor b T s.val) =
      realExteriorTrace T n := by
    apply Complex.ofReal_injective
    rw [real_minor_sum_cast b T hT n, coefficient_cast T hT n]
  rw [← he]
  exact (principal_minor_bound T hT b n).1.of_norm.hasSum

theorem coefficient_transport : Spec.RealCoefficientTransport.{v,w} := by
  intro H _ _ _ T hT n
  exact ⟨coefficient_cast T hT n, fun b => real_minor_hasSum b T hT n⟩

theorem coefficient_bound : Spec.RealExteriorCoefficientBound.{v} := by
  intro H _ _ _ T hT n
  exact (norm_tsum_le_tsum_norm (principal_minor_bound T hT ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n).1).trans
    (principal_minor_bound T hT ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n).2


lemma complex_series_summable (T : H →L[ℝ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (z : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n * (realExteriorTrace T n : ℂ)‖) := by
  have hn : 0 ≤ ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T := by
    exact (norm_nonneg _).trans (ExpandedFA.TraceIdeals.TraceBasisCyclicity.trace_bound ℝ H T hT)
  apply (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.factorial_series_majorant
    (fun n => (realExteriorTrace T n : ℂ)) _ hn ?_ z).1
  intro n
  simpa only [Complex.norm_real] using coefficient_bound T hT n

lemma real_series_summable (T : H →L[ℝ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (r : ℝ) :
    Summable (fun n : ℕ => ‖r ^ n * realExteriorTrace T n‖) := by
  have h := complex_series_summable T hT (r : ℂ)
  simpa only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.norm_real] using h

theorem determinant_series : Spec.RealDeterminantSeries.{v} := by
  intro H _ _ _ T hT
  exact ⟨real_series_summable T hT, complex_series_summable T hT⟩

lemma determinant_real_parameter (T : H →L[ℝ] H) (r : ℝ) :
    complexParameterDeterminant T r = (realDeterminant T r : ℂ) := by
  change (∑' n : ℕ, (r : ℂ) ^ n * (realExteriorTrace T n : ℂ)) =
    ((∑' n : ℕ, r ^ n * realExteriorTrace T n : ℝ) : ℂ)
  rw [Complex.ofReal_tsum]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]

lemma determinant_complexification (T : H →L[ℝ] H)
    (hT : ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (z : ℂ) :
    complexParameterDeterminant T z =
      ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue
        (ExpandedFA.TraceIdeals.RealComplexification.operator T) z := by
  apply tsum_congr
  intro n
  rw [coefficient_cast T hT n]

lemma determinant_conjugation (T : H →L[ℝ] H) (z : ℂ) :
    complexParameterDeterminant T (star z) = star (complexParameterDeterminant T z) := by
  change (∑' n : ℕ, (star z) ^ n * (realExteriorTrace T n : ℂ)) =
    star (∑' n : ℕ, z ^ n * (realExteriorTrace T n : ℂ))
  rw [tsum_star]
  apply tsum_congr
  intro n
  simp

lemma real_determinant_zero (T : H →L[ℝ] H) : realDeterminant T 0 = 1 := by
  change (∑' n : ℕ, (0 : ℝ) ^ n * realExteriorTrace T n) = 1
  rw [tsum_eq_single 0]
  · simpa using coefficient_zero T
  · intro n hn
    simp [zero_pow hn]

lemma complex_determinant_zero (T : H →L[ℝ] H) : complexParameterDeterminant T 0 = 1 := by
  rw [← Complex.ofReal_zero, determinant_real_parameter, real_determinant_zero, Complex.ofReal_one]

theorem determinant_identifications : Spec.RealDeterminantIdentifications.{v} := by
  intro H _ _ _ T hT
  exact ⟨determinant_real_parameter T, determinant_complexification T hT,
    determinant_conjugation T, real_determinant_zero T, complex_determinant_zero T⟩


namespace CoordinateGeometry
open ExpandedFA.TraceIdeals.RealComplexification
open Spec.RealCoordinates
variable {α : Type w} {n : ℕ}

private def realBasis (α : Type w) (n : ℕ) :
    HilbertBasis (Set.powersetCard α n) ℝ (Spec.RealCoordinateSpaceValue α n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

private def complexCoordinates (α : Type w) (n : ℕ) :
    ExpandedFA.TraceIdeals.RealComplexification.Space (Spec.RealCoordinateSpaceValue α n) ≃ₗᵢ[ℂ]
      TraceClassDefinitions.Spec.CoordinateSpaceValue α n :=
  (basis (realBasis α n)).repr

private def coordinateInclusion (α : Type w) (n : ℕ) :
    Spec.RealCoordinateSpaceValue α n →ₗᵢ[ℝ]
      TraceClassDefinitions.Spec.CoordinateSpaceValue α n :=
  { toLinearMap := ((complexCoordinates α n).toLinearEquiv.toLinearMap.restrictScalars ℝ).comp
      (inclusion : Spec.RealCoordinateSpaceValue α n →ₗᵢ[ℝ] _).toLinearMap
    norm_map' := fun f => by
      change ‖complexCoordinates α n (inclusion f)‖ = ‖f‖
      rw [(complexCoordinates α n).norm_map, inclusion.norm_map] }

private lemma coordinateInclusion_apply (f : Spec.RealCoordinateSpaceValue α n)
    (s : Set.powersetCard α n) : coordinateInclusion α n f s = (f s : ℂ) := by
  change (basis (realBasis α n)).repr (inclusion f) s = _
  rw [HilbertBasis.repr_apply_apply, basis_apply, inner_inclusion]
  congr 1
  exact ((realBasis α n).repr_apply_apply f s).symm

private lemma wedge_complexification (b : HilbertBasis α ℝ H) (x : Fin n → H) :
    coordinateInclusion α n (realCoordinateWedge b x) =
      TraceClassDefinitions.Spec.CoordinateWedgeValue (basis b) n
        (fun i => inclusion (x i)) := by
  apply lp.ext
  funext s
  rw [coordinateInclusion_apply]
  simp only [realCoordinateWedge, Spec.RealCoordinateWedgeValue,
    TraceClassDefinitions.Spec.CoordinateWedgeValue,
    TraceClassDefinitions.Spec.ExteriorCoordinates.wedgeAlternating_apply]
  change ((Matrix.det (fun i j : Fin n => b.repr (x i) (enumeration s j)) : ℝ) : ℂ) =
    Matrix.det (fun i j : Fin n => (basis b).repr (inclusion (x i)) (enumeration s j))
  calc
    _ = Matrix.det (fun i j : Fin n => (b.repr (x i) (enumeration s j) : ℂ)) :=
      RingHom.map_det Complex.ofRealHom _
    _ = _ := by
      congr 1
      ext i j
      simp only [HilbertBasis.repr_apply_apply, basis_apply, inner_inclusion]


private lemma real_inner_wedge (b : HilbertBasis α ℝ H) (x y : Fin n → H) :
    inner ℝ (realCoordinateWedge b x) (realCoordinateWedge b y) =
      Matrix.det (fun i j => inner ℝ (x i) (y j)) := by
  apply Complex.ofReal_injective
  calc
    _ = inner ℂ (coordinateInclusion α n (realCoordinateWedge b x))
        (coordinateInclusion α n (realCoordinateWedge b y)) := by
      exact (inner_inclusion _ _).symm.trans
        ((complexCoordinates α n).inner_map_map _ _).symm
    _ = _ := by
      rw [wedge_complexification, wedge_complexification]
      simp only [TraceClassDefinitions.Spec.CoordinateWedgeValue]
      rw [TraceClassDefinitions.ExteriorCoordinates.inner_wedge]
      simp only [inner_inclusion]
      exact (RingHom.map_det Complex.ofRealHom _).symm

private lemma real_basis_wedge (b : HilbertBasis α ℝ H) (s : Set.powersetCard α n) :
    realBasis α n s = realCoordinateWedge b (fun j => b (enumeration s j)) := by
  classical
  apply (coordinateInclusion α n).injective
  rw [wedge_complexification]
  apply lp.ext
  funext t
  rw [coordinateInclusion_apply]
  have he := congrArg (fun f : TraceClassDefinitions.Spec.CoordinateSpaceValue α n => f t)
    (TraceClassDefinitions.ExteriorCoordinates.wedge_basis (basis b) s)
  simp only [basis_apply] at he
  simp only [TraceClassDefinitions.Spec.CoordinateWedgeValue, enumeration] at *
  rw [he]
  have hb : realBasis α n s = lp.single 2 s (1 : ℝ) := by
    change (LinearIsometryEquiv.refl ℝ (Spec.RealCoordinateSpaceValue α n)).symm _ = _
    apply (LinearIsometryEquiv.refl ℝ (Spec.RealCoordinateSpaceValue α n)).symm_apply_eq.mpr
    apply lp.ext
    funext i
    by_cases hi : i = s <;> simp [lp.single_apply, hi]
  rw [hb]
  classical
  by_cases h : t = s <;> simp [lp.single_apply, h]

private lemma real_dense_wedges (b : HilbertBasis α ℝ H) :
    (Submodule.span ℝ (Set.range (fun x : Fin n → H => realCoordinateWedge b x))).topologicalClosure = ⊤ := by
  apply top_unique
  rw [← (realBasis α n).dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨(fun j => b (enumeration s j)), (real_basis_wedge b s).symm⟩

private lemma real_wedge_continuous (b : HilbertBasis α ℝ H) :
    Continuous (realCoordinateWedge (n := n) b) := by
  apply (coordinateInclusion α n).isometry.isEmbedding.isInducing.continuous_iff.mpr
  have hh := (TraceClassDefinitions.coordinate_wedge_continuous (basis b) n).comp
    (continuous_pi (fun i => inclusion.continuous.comp (continuous_apply i)))
  convert hh using 1
  funext x
  exact wedge_complexification b x

private lemma real_coordinate_operator_construction (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T)
    (n : ℕ) :
    (∀ x : Fin n → H, realCoordinateOperator b T n (realCoordinateWedge b x) =
      realCoordinateWedge b (T ∘ x)) ∧
    TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (realCoordinateOperator b T n) ∧
    TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (realCoordinateOperator b T n) ≤
      TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ) ∧
    (complexCoordinates α n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (operator (realCoordinateOperator b T n)) =
      (TraceClassDefinitions.coordinateOperator (basis b) (basis b) (operator T) n).comp
        (complexCoordinates α n).toContinuousLinearEquiv.toContinuousLinearMap := by
  classical
  letI : CompleteSpace (ExpandedFA.TraceIdeals.RealComplexification.Space
    (Spec.RealCoordinateSpaceValue α n)) :=
      ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace
  let q := complexCoordinates α n
  let M := coordinateInclusion α n
  let A := TraceClassDefinitions.coordinateOperator (basis b) (basis b) (operator T) n
  have hTC := (trace_ideal H H T).1.mp hT
  obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ _ _ (operator T) hTC.1
  obtain ⟨hs, hnorm⟩ := TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ _ _ (operator T) hTC S
  obtain ⟨hAn, hAc, hAs⟩ := TraceClassDefinitions.coordinateOperator_singular
    (basis b) (basis b) (operator T) S hs n
  have hA (x : Fin n → H) : A (M (realCoordinateWedge b x)) =
      M (realCoordinateWedge b (T ∘ x)) := by
    dsimp only [A, M]
    rw [wedge_complexification, hAn, wedge_complexification]
    congr 1
    funext i
    exact operator_inclusion T (x i)
  let B : Spec.RealCoordinateSpaceValue α n →L[ℝ] Spec.RealCoordinateSpaceValue α n :=
    (realPart : ExpandedFA.TraceIdeals.RealComplexification.Space
        (Spec.RealCoordinateSpaceValue α n) →L[ℝ] Spec.RealCoordinateSpaceValue α n).comp
      ((q.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
        ((A.restrictScalars ℝ).comp M.toContinuousLinearMap))
  have hBn (x : Fin n → H) : B (realCoordinateWedge b x) =
      realCoordinateWedge b (T ∘ x) := by
    change realPart (q.symm (A (M (realCoordinateWedge b x)))) = _
    rw [hA]
    change realPart (q.symm (q (inclusion (realCoordinateWedge b (T ∘ x))))) = _
    rw [q.symm_apply_apply]
    rfl
  have hex : ∃ C : Spec.RealCoordinateSpaceValue α n →L[ℝ] Spec.RealCoordinateSpaceValue α n,
      ∀ x : Fin n → H, C (realCoordinateWedge b x) = realCoordinateWedge b (T ∘ x) :=
    ⟨B, hBn⟩
  have hQ (x : Fin n → H) : realCoordinateOperator b T n (realCoordinateWedge b x) =
      realCoordinateWedge b (T ∘ x) := by
    unfold realCoordinateOperator Spec.RealCoordinateOperatorValue
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex x
  have hint : q.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (operator (realCoordinateOperator b T n)) =
      A.comp q.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply TraceClassDefinitions.ExteriorCoordinates.clm_ext_hilbertBasis (basis (realBasis α n))
    intro s
    simp only [ContinuousLinearMap.comp_apply, basis_apply, operator_inclusion]
    change M (realCoordinateOperator b T n (realBasis α n s)) = A (M (realBasis α n s))
    rw [real_basis_wedge b s, hQ, hA]
  have heq : operator (realCoordinateOperator b T n) =
      q.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (A.comp q.toContinuousLinearEquiv.toContinuousLinearMap) := by
    ext p
    apply q.injective
    have hh := congrArg (fun F => F p) hint
    change q (operator (realCoordinateOperator b T n) p) = q (q.symm (A (q p)))
    rw [q.apply_symm_apply]
    exact hh
  have hi := TraceIdeals.TraceNormIdeal.two_sided_ideal ℂ _ _ _ _ A
    q.symm.toContinuousLinearEquiv.toContinuousLinearMap
    q.toContinuousLinearEquiv.toContinuousLinearMap hAc
  have hqc : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (realCoordinateOperator b T n) :=
    (trace_ideal _ _ (realCoordinateOperator b T n)).1.mpr (by
      change TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
        (operator (realCoordinateOperator b T n))
      rw [heq]
      exact hi.1)
  have hnon := TraceIdeals.TraceNormIdeal.traceNorm_nonneg A hAc
  refine ⟨hQ, hqc, ?_, hint⟩
  rw [← (trace_ideal _ _ (realCoordinateOperator b T n)).2 hqc]
  change TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue
    (operator (realCoordinateOperator b T n)) ≤ _
  rw [heq]
  calc
    _ ≤ ‖q.symm.toContinuousLinearEquiv.toContinuousLinearMap‖ *
        TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue A *
        ‖q.toContinuousLinearEquiv.toContinuousLinearMap‖ := hi.2
    _ ≤ 1 * TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue A * 1 := by
      gcongr
      · exact q.symm.toLinearIsometry.norm_toContinuousLinearMap_le
      · exact q.toLinearIsometry.norm_toContinuousLinearMap_le
    _ = TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue A := by ring
    _ = ∑' s : Set.powersetCard S.Index n, ∏ j ∈ s.val, S.sigma j := hAs
    _ ≤ (∑' j, S.sigma j) ^ n / (n.factorial : ℝ) :=
      (TraceClassDefinitions.subset_product_bound S.Index S.sigma
        (fun j => (S.positive j).le) hs n).2
    _ = TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ) := by
      rw [hnorm, (trace_ideal H H T).2 hT]

private lemma real_diagonal_minor (b : HilbertBasis α ℝ H) (T : H →L[ℝ] H)
    (A : Spec.RealCoordinateSpaceValue α n →L[ℝ] Spec.RealCoordinateSpaceValue α n)
    (hA : ∀ x : Fin n → H, A (realCoordinateWedge b x) = realCoordinateWedge b (T ∘ x))
    (s : Set.powersetCard α n) :
    inner ℝ (realBasis α n s) (A (realBasis α n s)) = realPrincipalMinor b T s.val := by
  classical
  rw [real_basis_wedge b s, hA, real_inner_wedge]
  let e : Fin n ≃ s.val := (Finset.equivFinOfCardEq s.property).symm
  let M : Matrix s.val s.val ℝ := fun i j => inner ℝ (b i.val) (T (b j.val))
  change Matrix.det (M.submatrix e e) = Matrix.det M
  exact Matrix.det_submatrix_equiv_self e M

private lemma real_trace_coordinate_operator (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    TraceIdeals.TraceClassDefinitions.Spec.TraceValue (realCoordinateOperator b T n) =
      realExteriorTrace T n := by
  obtain ⟨hn,hc,_,_⟩ := real_coordinate_operator_construction b T hT n
  have hh := (TraceIdeals.TraceBasisCyclicity.diagonal_trace ℝ _
    (realCoordinateOperator b T n) hc _ (realBasis α n)).2
  simp only [real_diagonal_minor b T _ hn] at hh
  exact HasSum.unique hh (real_minor_hasSum b T hT n)

private lemma real_algebraic_compatibility (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) (n : ℕ) :
    (realCoordinateOperator b T n).toLinearMap.comp (realCoordinateEmbedding (n := n) b) =
      (realCoordinateEmbedding b).comp (exteriorPower.map n T.toLinearMap) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    realCoordinateEmbedding, Spec.RealCoordinateEmbeddingValue,
    Spec.RealCoordinates.embed, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.map_apply_ιMulti, ContinuousLinearMap.coe_coe]
  exact (real_coordinate_operator_construction b T hT n).1 x

private lemma change_complex_exterior_basis
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {β : Type*} (b : HilbertBasis α ℂ E) (c : HilbertBasis β ℂ E) (n : ℕ) :
    ∃ e : TraceClassDefinitions.Spec.CoordinateSpaceValue α n ≃ₗᵢ[ℂ]
        TraceClassDefinitions.Spec.CoordinateSpaceValue β n,
      ∀ x : Fin n → E, e (TraceClassDefinitions.Spec.CoordinateWedgeValue b n x) =
        TraceClassDefinitions.Spec.CoordinateWedgeValue c n x := by
  let d := TraceClassDefinitions.ExteriorCoordinates.inducedBasis (n := n) c b
  refine ⟨d.repr.symm, ?_⟩
  intro x
  apply d.repr.injective
  rw [d.repr.apply_symm_apply]
  apply lp.ext
  funext s
  dsimp only [d]
  simp only [TraceClassDefinitions.Spec.CoordinateWedgeValue]
  rw [TraceClassDefinitions.ExteriorCoordinates.inducedBasis_repr_wedge]
  change Matrix.det (fun i j : Fin n => b.repr (x i) (Spec.RealCoordinates.enumeration s j)) =
    Matrix.det (fun i j : Fin n => inner ℂ (b (Spec.RealCoordinates.enumeration s i)) (x j))
  simp only [HilbertBasis.repr_apply_apply]
  exact Matrix.det_transpose _

private lemma real_exterior_complexification (n : ℕ) :
    ∃ e : ExpandedFA.TraceIdeals.RealComplexification.Space (Spec.RealExteriorSpace H n) ≃ₗᵢ[ℂ]
        TraceClassDefinitions.Spec.CoordinateSpaceValue
          (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
            (𝕜 := ℂ) (H := ExpandedFA.TraceIdeals.RealComplexification.Space H)) n,
      (∀ x : Fin n → H, e (inclusion (realCoordinateWedge
        TraceIdeals.TraceClassDefinitions.Spec.chosenBasis x)) =
        TraceClassDefinitions.Spec.CoordinateWedgeValue
          TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n (fun i => inclusion (x i))) ∧
      ∀ (T : H →L[ℝ] H), TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
        e.toContinuousLinearEquiv.toContinuousLinearMap.comp (operator (realExteriorOperator T n)) =
          (TraceClassDefinitions.Spec.ExteriorOperatorValue (operator T) n).comp
            e.toContinuousLinearEquiv.toContinuousLinearMap := by
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℝ) (H := H)
  let c := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis
    (𝕜 := ℂ) (H := ExpandedFA.TraceIdeals.RealComplexification.Space H)
  obtain ⟨d, hd⟩ := change_complex_exterior_basis (basis b) c n
  let q := complexCoordinates (TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex
    (𝕜 := ℝ) (H := H)) n
  let e := q.trans d
  refine ⟨e, ?_, ?_⟩
  · intro x
    change d (coordinateInclusion _ n (realCoordinateWedge b x)) = _
    rw [wedge_complexification, hd]
  · intro T hT
    let A := TraceClassDefinitions.coordinateOperator (basis b) (basis b) (operator T) n
    let C := TraceClassDefinitions.Spec.ExteriorOperatorValue (operator T) n
    have hp := real_coordinate_operator_construction b T hT n
    have hTC := (trace_ideal H H T).1.mp hT
    have hC := (TraceClassDefinitions.exterior_construction (operator T) hTC n).1
    have hAn (x : Fin n → ExpandedFA.TraceIdeals.RealComplexification.Space H) :
        A (TraceClassDefinitions.Spec.CoordinateWedgeValue (basis b) n x) =
          TraceClassDefinitions.Spec.CoordinateWedgeValue (basis b) n (operator T ∘ x) := by
      obtain ⟨S⟩ := CompactSpectral.SingularExpansion.compact_singular_system ℂ _ _ (operator T) hTC.1
      exact (TraceClassDefinitions.coordinateOperator_singular _ _ _ S
        (TraceIdeals.TraceClassDefinitions.singularSystem_sum ℂ _ _ _ hTC S).1 n).1 x
    have hint : d.toContinuousLinearEquiv.toContinuousLinearMap.comp A =
        C.comp d.toContinuousLinearEquiv.toContinuousLinearMap := by
      apply TraceClassDefinitions.ExteriorCoordinates.clm_ext_hilbertBasis
        (TraceClassDefinitions.Spec.ExteriorCoordinates.basis _ n)
      intro s
      rw [TraceClassDefinitions.ExteriorCoordinates.basis_eq_wedge (basis b) s]
      change d (A (TraceClassDefinitions.Spec.CoordinateWedgeValue (basis b) n _)) =
        C (d (TraceClassDefinitions.Spec.CoordinateWedgeValue (basis b) n _))
      rw [hAn, hd, hd, hC]
    apply ContinuousLinearMap.ext
    intro p
    change d (q (operator (realExteriorOperator T n) p)) = C (d (q p))
    have hq := congrArg (fun F => F p) hp.2.2.2
    change q (operator (realExteriorOperator T n) p) = A (q p) at hq
    rw [hq]
    exact congrArg (fun F => F (q p)) hint

private lemma surjective_of_wedges {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [CompleteSpace X]
    (b : HilbertBasis α ℝ H) (U : X →ₗᵢ[ℝ] Spec.RealCoordinateSpaceValue α n)
    (hw : ∀ x : Fin n → H, ∃ y, U y = realCoordinateWedge b x) :
    Function.Surjective U := by
  have hc : IsClosed (U.toLinearMap.range : Set (Spec.RealCoordinateSpaceValue α n)) :=
    U.isometry.isClosedEmbedding.isClosed_range
  have hspan : Submodule.span ℝ (Set.range (fun x : Fin n → H => realCoordinateWedge b x)) ≤
      U.toLinearMap.range := Submodule.span_le.mpr (by rintro _ ⟨x,rfl⟩; exact hw x)
  have hh := (Submodule.span ℝ (Set.range (fun x : Fin n → H => realCoordinateWedge b x))).topologicalClosure_minimal hspan hc
  rw [real_dense_wedges b] at hh
  exact LinearMap.range_eq_top.mp (le_antisymm le_top hh)

private lemma real_low_degrees (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T) :
    (∃ e : Spec.RealCoordinateSpaceValue α 0 ≃ₗᵢ[ℝ] ℝ,
      (∀ x : Fin 0 → H, e (realCoordinateWedge b x) = 1) ∧
      ∀ r : ℝ, e (realCoordinateOperator b T 0 (e.symm r)) = r) ∧
    (∃ e : Spec.RealCoordinateSpaceValue α 1 ≃ₗᵢ[ℝ] H,
      (∀ x : H, e (realCoordinateWedge b (fun _ : Fin 1 => x)) = x) ∧
      ∀ x : H, e (realCoordinateOperator b T 1 (e.symm x)) = T x) := by
  have hn0 := (real_coordinate_operator_construction b T hT 0).1
  have hn1 := (real_coordinate_operator_construction b T hT 1).1
  constructor
  · let vacuum := realCoordinateWedge b (Fin.elim0 : Fin 0 → H)
    have hv : inner ℝ vacuum vacuum = 1 := by
      rw [real_inner_wedge]
      exact Matrix.det_isEmpty
    let L : ℝ →ₗ[ℝ] Spec.RealCoordinateSpaceValue α 0 :=
      (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight vacuum
    let U : ℝ →ₗᵢ[ℝ] Spec.RealCoordinateSpaceValue α 0 := L.isometryOfInner (by
      intro r s
      change inner ℝ (r • vacuum) (s • vacuum) = inner ℝ r s
      rw [real_inner_smul_left, real_inner_smul_right, hv]
      simp [RCLike.inner_apply, mul_comm])
    have hU (x : Fin 0 → H) : U 1 = realCoordinateWedge b x := by
      change (1 : ℝ) • vacuum = _
      rw [one_smul]
      exact congrArg (realCoordinateWedge b) (funext (fun i => Fin.elim0 i))
    let F := LinearIsometryEquiv.ofSurjective U (surjective_of_wedges b U (fun x => ⟨1,hU x⟩))
    refine ⟨F.symm, ?_, ?_⟩
    · intro x
      rw [← hU x]
      exact F.symm_apply_apply 1
    · intro r
      have hw : F r = r • vacuum := rfl
      change F.symm (realCoordinateOperator b T 0 (F r)) = r
      rw [hw, map_smul]
      have h0 : realCoordinateOperator b T 0 vacuum = vacuum := by
        change realCoordinateOperator b T 0 (realCoordinateWedge b _) = _
        rw [hn0]
        exact congrArg (realCoordinateWedge b) (funext (fun i => Fin.elim0 i))
      rw [h0]
      exact F.symm_apply_apply r
  · let L : H →ₗ[ℝ] Spec.RealCoordinateSpaceValue α 1 :=
      (AlternatingMap.ofSubsingleton ℝ H (Spec.RealCoordinateSpaceValue α 1) (0 : Fin 1)).symm
        (realCoordinateWedge b)
    have hL (x : H) : L x = realCoordinateWedge b (fun _ : Fin 1 => x) := rfl
    let U : H →ₗᵢ[ℝ] Spec.RealCoordinateSpaceValue α 1 := L.isometryOfInner (by
      intro x y
      rw [hL,hL,real_inner_wedge]
      exact Matrix.det_unique _)
    have hU (x : Fin 1 → H) : U (x 0) = realCoordinateWedge b x := by
      change L (x 0) = _
      rw [hL]
      congr 1
      funext i
      exact congrArg x (Subsingleton.elim _ _)
    let F := LinearIsometryEquiv.ofSurjective U (surjective_of_wedges b U (fun x => ⟨x 0,hU x⟩))
    refine ⟨F.symm, ?_, ?_⟩
    · intro x
      change F.symm (F x) = x
      exact F.symm_apply_apply x
    · intro x
      change F.symm (realCoordinateOperator b T 1 (L x)) = T x
      rw [hL,hn1]
      change F.symm (F (T x)) = T x
      exact F.symm_apply_apply (T x)

end CoordinateGeometry

theorem exterior_geometry : Spec.RealExteriorGeometry.{v,w} := by
  intro H _ _ _ α b n
  exact ⟨CoordinateGeometry.real_inner_wedge b,
    CoordinateGeometry.real_dense_wedges b, CoordinateGeometry.real_wedge_continuous b⟩

theorem exterior_construction : Spec.RealExteriorConstruction.{v} := by
  intro H _ _ _ T hT n
  let b := TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (𝕜 := ℝ) (H := H)
  obtain ⟨hn,hc,hb,_⟩ := CoordinateGeometry.real_coordinate_operator_construction b T hT n
  exact ⟨hn,hc,hb,CoordinateGeometry.real_trace_coordinate_operator b T hT n,
    CoordinateGeometry.real_algebraic_compatibility b T hT n⟩

theorem exterior_complexification : Spec.RealExteriorComplexification.{v} := by
  intro H _ _ _ n
  exact CoordinateGeometry.real_exterior_complexification n

theorem exterior_low_degrees : Spec.RealExteriorLowDegrees.{v} := by
  intro H _ _ _ T hT
  obtain ⟨h0,h1⟩ := CoordinateGeometry.real_low_degrees
    TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T hT
  exact ⟨h0,h1,coefficient_zero T,coefficient_one T⟩

end ExpandedFA.FredholmDeterminant.RealExteriorDefinitions
