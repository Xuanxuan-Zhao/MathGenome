import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.TraceClassDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.RealComplexification

/-! Real Hilbert exterior powers in subset coordinates. The coefficients below
are real principal-minor sums, independently of complex exterior coefficients.
The existence, geometry and trace assertions are propositions, not certificates
assumed by any of these definitions. -/
noncomputable section
open scoped lp
universe u v w
namespace ExpandedFA.FredholmDeterminant.RealExteriorDefinitions.Spec

namespace RealCoordinates
abbrev Space (α : Type*) (n : ℕ) := ℓ²(Set.powersetCard α n, ℝ)
abbrev enumeration := @ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorCoordinates.enumeration

lemma memℓp_tuple_prod {α : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℝ)) :
    Memℓp (fun a : Fin n → α => ∏ i, f i (a i)) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_prod, ← Finset.prod_pow]
  apply ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorCoordinates.summable_fin_prod n (fun i a => ‖f i a‖ ^ 2)
  · intro i a; positivity
  · intro i
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (f i).property.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

lemma memℓp_det_coordinates {α : Type*} {n : ℕ} (f : Fin n → ℓ²(α, ℝ)) :
    Memℓp (fun s : Set.powersetCard α n =>
      Matrix.det (fun i j : Fin n => f j (enumeration s i))) 2 := by
  have hterm (σ : Equiv.Perm (Fin n)) :
      Memℓp (fun s : Set.powersetCard α n => ∏ i, f i (enumeration s (σ i))) 2 := by
    have h := memℓp_tuple_prod f
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    have hs := h.summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    apply hs.comp_injective
    intro s t hst
    apply ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorCoordinates.enumeration_injective
    funext i
    have hh := congrFun hst (σ.symm i)
    simpa using hh
  have hsum := Memℓp.finsetSum Finset.univ
    (fun σ _ => (hterm σ).const_mul ((Equiv.Perm.sign σ : ℤ) : ℝ))
  convert hsum using 1
  funext s
  exact Matrix.det_apply' _

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {α : Type w} {n : ℕ}

def finiteCoordinates (b : HilbertBasis α ℝ H) (s : Set.powersetCard α n) :
    H →ₗ[ℝ] (Fin n → ℝ) where
  toFun x j := b.repr x (enumeration s j)
  map_add' x y := by funext j; simp
  map_smul' c x := by funext j; simp

def wedgeAlternating (b : HilbertBasis α ℝ H) : H [⋀^Fin n]→ₗ[ℝ] Space α n :=
  (AlternatingMap.pi (fun s : Set.powersetCard α n =>
    Matrix.detRowAlternating.compLinearMap (finiteCoordinates b s))).codRestrict
      (lpSubmodule ℝ (fun _ : Set.powersetCard α n => ℝ) 2) (fun x => by
        change Memℓp (fun s : Set.powersetCard α n =>
          Matrix.det (fun i j : Fin n => b.repr (x i) (enumeration s j))) 2
        have h := memℓp_det_coordinates (fun j => b.repr (x j))
        convert h using 1
        funext s
        exact Matrix.det_transpose _)

def embed (b : HilbertBasis α ℝ H) : ⋀[ℝ]^n H →ₗ[ℝ] Space α n :=
  exteriorPower.alternatingMapLinearEquiv (wedgeAlternating b)
end RealCoordinates

abbrev RealCoordinateSpaceValue (α : Type w) (n : ℕ) : Type w := RealCoordinates.Space α n
abbrev RealCoordinateWedgeValue := @RealCoordinates.wedgeAlternating
abbrev RealCoordinateEmbeddingValue := @RealCoordinates.embed

def RealCoordinateSpaceType := (α : Type w) → ℕ → Type w

def RealCoordinateWedgeType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {α : Type w} {n : ℕ}, HilbertBasis α ℝ H →
  (H [⋀^Fin n]→ₗ[ℝ] RealCoordinateSpaceValue α n)

def RealCoordinateEmbeddingType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {α : Type w} {n : ℕ}, HilbertBasis α ℝ H →
  (⋀[ℝ]^n H →ₗ[ℝ] RealCoordinateSpaceValue α n)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def RealPrincipalMinorValue {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (s : Finset α) : ℝ := by
  classical
  exact Matrix.det (fun i j : s => inner ℝ (b i.val) (T (b j.val)))

def RealPrincipalMinorType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {α : Type w}, HilbertBasis α ℝ H →
  (H →L[ℝ] H) → Finset α → ℝ

/-- A total definition of the continuous exterior functor; its existence and
agreement with decomposable wedges are required conclusions below. -/
def RealCoordinateOperatorValue {α : Type w} (b : HilbertBasis α ℝ H)
    (T : H →L[ℝ] H) (n : ℕ) :
    RealCoordinateSpaceValue α n →L[ℝ] RealCoordinateSpaceValue α n := by
  classical
  exact if h : ∃ A : RealCoordinateSpaceValue α n →L[ℝ] RealCoordinateSpaceValue α n,
      ∀ x : Fin n → H, A (RealCoordinateWedgeValue b x) =
        RealCoordinateWedgeValue b (T ∘ x)
    then Classical.choose h else 0

def RealCoordinateOperatorType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] {α : Type w}, HilbertBasis α ℝ H →
  (H →L[ℝ] H) → (n : ℕ) →
  (RealCoordinateSpaceValue α n →L[ℝ] RealCoordinateSpaceValue α n)

variable [CompleteSpace H]
abbrev RealExteriorSpace (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (n : ℕ) :=
  RealCoordinateSpaceValue (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℝ) (H := H)) n

def RealExteriorOperatorValue (T : H →L[ℝ] H) (n : ℕ) :
    RealExteriorSpace H n →L[ℝ] RealExteriorSpace H n :=
  RealCoordinateOperatorValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T n

def RealExteriorOperatorType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H], (H →L[ℝ] H) → (n : ℕ) →
  (RealExteriorSpace H n →L[ℝ] RealExteriorSpace H n)

def RealExteriorTraceValue (T : H →L[ℝ] H) (n : ℕ) : ℝ :=
  ∑' s : Set.powersetCard (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℝ) (H := H)) n,
    RealPrincipalMinorValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis T s.val

def RealExteriorTraceType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H], (H →L[ℝ] H) → ℕ → ℝ

def RealDeterminantValue (T : H →L[ℝ] H) (r : ℝ) : ℝ :=
  ∑' n : ℕ, r ^ n * RealExteriorTraceValue T n

def ComplexParameterDeterminantValue (T : H →L[ℝ] H) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n * (RealExteriorTraceValue T n : ℂ)

def RealDeterminantType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H], (H →L[ℝ] H) → ℝ → ℝ

def ComplexParameterDeterminantType := ∀ {H : Type v} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H], (H →L[ℝ] H) → ℂ → ℂ

/-- Full real Gram normalization, dense decomposable wedges and continuity. -/
def RealExteriorGeometry : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {α : Type w} (b : HilbertBasis α ℝ H) (n : ℕ),
    (∀ x y : Fin n → H, inner ℝ (RealCoordinateWedgeValue b x)
      (RealCoordinateWedgeValue b y) = Matrix.det (fun i j => inner ℝ (x i) (y j))) ∧
    (Submodule.span ℝ (Set.range (fun x : Fin n → H =>
      RealCoordinateWedgeValue b x))).topologicalClosure = ⊤ ∧
    Continuous (RealCoordinateWedgeValue (n := n) b)

def RealPrincipalMinorBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    ∀ {α : Type w} (b : HilbertBasis α ℝ H) (n : ℕ),
    Summable (fun s : Set.powersetCard α n => ‖RealPrincipalMinorValue b T s.val‖) ∧
    (∑' s : Set.powersetCard α n, ‖RealPrincipalMinorValue b T s.val‖) ≤
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ)

/-- Basis independence, with actual complexification of the operator. -/
def RealCoefficientTransport : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T → ∀ n : ℕ,
    letI := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
    (RealExteriorTraceValue T n : ℂ) = ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorTraceValue (ExpandedFA.TraceIdeals.RealComplexification.Spec.operator T) n ∧
    ∀ {α : Type w} (b : HilbertBasis α ℝ H),
      HasSum (fun s : Set.powersetCard α n => RealPrincipalMinorValue b T s.val)
        (RealExteriorTraceValue T n)

def RealExteriorConstruction : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T → ∀ n : ℕ,
    (∀ x : Fin n → H, RealExteriorOperatorValue T n
      (RealCoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis x) =
        RealCoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (T ∘ x)) ∧
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (RealExteriorOperatorValue T n) ∧
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue (RealExteriorOperatorValue T n) ≤
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ) ∧
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue (RealExteriorOperatorValue T n) = RealExteriorTraceValue T n ∧
    (RealExteriorOperatorValue T n).toLinearMap.comp
      (RealCoordinateEmbeddingValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis) =
    (RealCoordinateEmbeddingValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis).comp (exteriorPower.map n T.toLinearMap)

def RealExteriorLowDegrees : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    (∃ e : RealExteriorSpace H 0 ≃ₗᵢ[ℝ] ℝ,
      (∀ x : Fin 0 → H, e (RealCoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis x) = 1) ∧
      ∀ r : ℝ, e (RealExteriorOperatorValue T 0 (e.symm r)) = r) ∧
    (∃ e : RealExteriorSpace H 1 ≃ₗᵢ[ℝ] H,
      (∀ x : H, e (RealCoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis (fun _ : Fin 1 => x)) = x) ∧
      ∀ x : H, e (RealExteriorOperatorValue T 1 (e.symm x)) = T x) ∧
    RealExteriorTraceValue T 0 = 1 ∧ RealExteriorTraceValue T 1 = ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue T

/-- The actual completed exterior/complexification identification, including
its decomposable-wedge normalization and operator intertwining. -/
def RealExteriorComplexification : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (n : ℕ),
    letI := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
    ∃ e : TraceIdeals.RealComplexification.Space (RealExteriorSpace H n) ≃ₗᵢ[ℂ]
        ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.CoordinateSpaceValue (ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasisIndex (𝕜 := ℂ) (H := TraceIdeals.RealComplexification.Space H)) n,
      (∀ x : Fin n → H,
        e (ExpandedFA.TraceIdeals.RealComplexification.Spec.inclusion (RealCoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis x)) =
          ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.CoordinateWedgeValue ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.chosenBasis n (fun i => ExpandedFA.TraceIdeals.RealComplexification.Spec.inclusion (x i))) ∧
      ∀ (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
        e.toContinuousLinearEquiv.toContinuousLinearMap.comp
            (ExpandedFA.TraceIdeals.RealComplexification.Spec.operator (RealExteriorOperatorValue T n)) =
          (ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.ExteriorOperatorValue (ExpandedFA.TraceIdeals.RealComplexification.Spec.operator T) n).comp
            e.toContinuousLinearEquiv.toContinuousLinearMap

def RealExteriorCoefficientBound : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T → ∀ n : ℕ,
    ‖RealExteriorTraceValue T n‖ ≤ ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceNormValue T ^ n / (n.factorial : ℝ)

def RealCoefficientLowDegrees : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H),
    RealExteriorTraceValue T 0 = 1 ∧ RealExteriorTraceValue T 1 = ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.TraceValue T

def RealDeterminantSeries : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    (∀ r : ℝ, Summable (fun n : ℕ => ‖r ^ n * RealExteriorTraceValue T n‖)) ∧
    ∀ z : ℂ, Summable (fun n : ℕ => ‖z ^ n * (RealExteriorTraceValue T n : ℂ)‖)

def RealDeterminantIdentifications : Prop :=
  ∀ {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H), ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T →
    letI := ExpandedFA.TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
    (∀ r : ℝ, ComplexParameterDeterminantValue T r = (RealDeterminantValue T r : ℂ)) ∧
    (∀ z : ℂ, ComplexParameterDeterminantValue T z = ExpandedFA.FredholmDeterminant.TraceClassDefinitions.Spec.FredholmDeterminantValue (ExpandedFA.TraceIdeals.RealComplexification.Spec.operator T) z) ∧
    (∀ z : ℂ, ComplexParameterDeterminantValue T (star z) =
      star (ComplexParameterDeterminantValue T z)) ∧
    RealDeterminantValue T 0 = 1 ∧ ComplexParameterDeterminantValue T 0 = 1

end ExpandedFA.FredholmDeterminant.RealExteriorDefinitions.Spec
