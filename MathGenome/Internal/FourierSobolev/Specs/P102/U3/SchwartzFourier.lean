import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-! Canonical coordinate model and independent statements for paper.tex:1043–1064.
The coordinate derivatives are indexed by ordered lists of coordinate directions
(Fin n → Fin d); for smooth functions repeated mixed partials commute. This
representation includes every multi-index and allows repetitions. -/
noncomputable section
open scoped SchwartzMap FourierTransform ContDiff NNReal
open MeasureTheory LineDeriv

namespace P102.Specs.U3
abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Test (d : ℕ) := SchwartzMap (Euclidean d) ℂ
/-- The strong dual, with uniform convergence on bounded sets. -/
abbrev Tempered (d : ℕ) := Test d →L[ℂ] ℂ
/-- The same continuous functionals with the topology of pointwise testing. -/
abbrev WeakTempered (d : ℕ) := Test d →Lₚₜ[ℂ] ℂ
end P102.Specs.U3

namespace P102.U3
open P102.Specs.U3 (Euclidean Test Tempered WeakTempered)

def coordinateVector {d : ℕ} (j : Fin d) : Euclidean d :=
  EuclideanSpace.basisFun (Fin d) ℝ j

def coordinatePartial {d n : ℕ} (β : Fin n → Fin d) : Test d →L[ℂ] Test d :=
  iteratedLineDerivOpCLM ℂ (Test d) (coordinateVector ∘ β)

def coordinateMul {d : ℕ} (j : Fin d) : Test d →L[ℂ] Test d :=
  SchwartzMap.smulLeftCLM ℂ (inner ℝ · (coordinateVector j))

/-- Multiplication by ∏ᵢ(c x_{βᵢ}), bundled on Schwartz space. -/
def polynomialMul {d : ℕ} (c : ℂ) : {n : ℕ} → (Fin n → Fin d) → Test d →L[ℂ] Test d
  | 0, _ => ContinuousLinearMap.id ℂ _
  | _ + 1, β => (c • coordinateMul (β 0)).comp (polynomialMul c (Fin.tail β))

/-- Point evaluation on scalar Schwartz functions. -/
def pointEval {d : ℕ} (x : Euclidean d) : Test d →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Euclidean d) ℂ)

/-- A single coordinate derivative, evaluated at a point, with radial weight. -/
def radialPoint {d n : ℕ} (N : ℕ) (β : Fin n → Fin d) (x : Euclidean d) :
    Seminorm ℂ (Test d) :=
  (Real.toNNReal ((1 + ‖x‖) ^ N)) •
    (normSeminorm ℂ ℂ).comp
      ((pointEval x).comp (coordinatePartial β)).toLinearMap

/-- Exactly the supremum of (1+|x|)^N |∂^β φ(x)| over |β|≤k and x. -/
def manuscriptSeminorm {d : ℕ} (N k : ℕ) : Seminorm ℂ (Test d) :=
  ⨆ (n : Fin (k + 1)) (β : Fin n.val → Fin d) (x : Euclidean d), radialPoint N β x

def manuscriptFamily (d : ℕ) : SeminormFamily ℂ (Test d) (ℕ × ℕ) :=
  fun p => manuscriptSeminorm p.1 p.2

/-- The manuscript's smooth rapidly decreasing functions, before bundling.
All coordinate derivatives of orders up to k are bounded with weight (1+|x|)^N. -/
def ManuscriptSchwartz {d : ℕ} (f : Euclidean d → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ N k : ℕ, ∃ C : ℝ, ∀ (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d),
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n.val f x (coordinateVector ∘ β)‖ ≤ C

/-- The usual coordinate monomial x^α (real valued before multiplication). -/
def coordinateMonomial {d : ℕ} (α : Fin d → ℕ) (x : Euclidean d) : ℝ :=
  ∏ j, x j ^ α j

def monomialPoint {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d) (x : Euclidean d) :
    Seminorm ℂ (Test d) :=
  (Real.toNNReal |coordinateMonomial α x|) •
    (normSeminorm ℂ ℂ).comp ((pointEval x).comp (coordinatePartial β)).toLinearMap

/-- The usual coordinate-monomial seminorm sup_x |x^α ∂^β φ(x)|. -/
def monomialSeminorm {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d) : Seminorm ℂ (Test d) :=
  ⨆ x : Euclidean d, monomialPoint α β x

/-- An index records a monomial exponent and an ordered coordinate derivative. -/
abbrev MonomialIndex (d : ℕ) := (Fin d → ℕ) × (Σ n : ℕ, Fin n → Fin d)
def monomialFamily (d : ℕ) : SeminormFamily ℂ (Test d) (MonomialIndex d) :=
  fun p => monomialSeminorm p.1 p.2.2

end P102.U3

namespace P102.Specs.U3
open P102.U3

-- These expected values fix the Euclidean model and the two distinct dual topologies.
def Euclidean_type : Type 1 := ℕ → Type
def Euclidean_value : Euclidean_type := fun d => EuclideanSpace ℝ (Fin d)
def Test_type : Type 1 := ℕ → Type
def Test_value : Test_type := fun d => SchwartzMap (Euclidean d) ℂ
def Tempered_type : Type 1 := ℕ → Type
def Tempered_value : Tempered_type := fun d => Test d →L[ℂ] ℂ
def WeakTempered_type : Type 1 := ℕ → Type
def WeakTempered_value : WeakTempered_type := fun d => Test d →Lₚₜ[ℂ] ℂ

def fourierType : Type := (d : ℕ) → Test d →L[ℂ] Test d
def fourierValue : fourierType := fun d => FourierTransform.fourierCLM ℂ (Test d)
def checkType : Type := (d : ℕ) → Test d →L[ℂ] Test d
def checkValue : checkType := fun d => FourierTransform.fourierInvCLM ℂ (Test d)

def coordinatePartial_apply_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d) (f : Test d) (x : Euclidean d),
    coordinatePartial β f x = iteratedFDeriv ℝ n f x (coordinateVector ∘ β)

def coordinateMul_apply_type : Prop :=
  ∀ {d : ℕ} (j : Fin d) (f : Test d) (x : Euclidean d),
    coordinateMul j f x = (x j : ℂ) * f x

def coordinateMul_eq_real_type : Prop :=
  ∀ {d : ℕ} (j : Fin d) (f : Test d),
    coordinateMul j f = SchwartzMap.smulLeftCLM ℂ (inner ℝ · (coordinateVector j)) f

def polynomialMul_apply_type : Prop :=
  ∀ {d n : ℕ} (c : ℂ) (β : Fin n → Fin d)
    (f : Test d) (x : Euclidean d),
    polynomialMul c β f x = (∏ i, c * (x (β i) : ℂ)) * f x

def fourier_integral_type : Prop :=
  ∀ {d : ℕ} (f : Test d) (ξ : Euclidean d),
    fourierValue d f ξ = ∫ x : Euclidean d,
      Complex.exp ((-2 * Real.pi * inner ℝ x ξ : ℝ) * Complex.I) * f x

def check_integral_type : Prop :=
  ∀ {d : ℕ} (f : Test d) (x : Euclidean d),
    checkValue d f x = ∫ ξ : Euclidean d,
      Complex.exp ((2 * Real.pi * inner ℝ ξ x : ℝ) * Complex.I) * f ξ

def fourier_continuous_type : Prop :=
  ∀ (d : ℕ),
    Continuous (fourierValue d)

def check_continuous_type : Prop :=
  ∀ (d : ℕ),
    Continuous (checkValue d)

def partial_fourier_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d) (f : Test d),
    coordinatePartial β (fourierValue d f) = fourierValue d (polynomialMul (-(2 * Real.pi * Complex.I)) β f)

def fourier_partial_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d) (f : Test d),
    fourierValue d (coordinatePartial β f) = polynomialMul (2 * Real.pi * Complex.I) β (fourierValue d f)

def partial_check_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d) (f : Test d),
    coordinatePartial β (checkValue d f) = checkValue d (polynomialMul (2 * Real.pi * Complex.I) β f)

def check_partial_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d) (f : Test d),
    checkValue d (coordinatePartial β f) = polynomialMul (-(2 * Real.pi * Complex.I)) β (checkValue d f)

def norm_coordinateVector_type : Prop :=
  ∀ {d : ℕ} (j : Fin d),
    ‖coordinateVector j‖ = 1

def coordinate_eval_le_norm_type : Prop :=
  ∀ {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ)
    (β : Fin n → Fin d),
    ‖A (coordinateVector ∘ β)‖ ≤ ‖A‖

def multilinear_norm_le_coordinate_sum_type : Prop :=
  ∀ {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ),
    ‖A‖ ≤ ∑ β : Fin n → Fin d, ‖A (coordinateVector ∘ β)‖

def multilinear_norm_le_coordinate_bound_type : Prop :=
  ∀ {d n : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclidean d) ℂ) {C : ℝ}
    (hC : ∀ β : Fin n → Fin d, ‖A (coordinateVector ∘ β)‖ ≤ C),
    ‖A‖ ≤ (d : ℝ) ^ n * C

def radialPoint_apply_type : Prop :=
  ∀ {d n : ℕ} (N : ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) (f : Test d),
    radialPoint N β x f = (1 + ‖x‖) ^ N * ‖coordinatePartial β f x‖

def radialPoint_le_native_type : Prop :=
  ∀ {d k : ℕ} (N : ℕ) (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d),
    radialPoint N β x ≤ (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)

def manuscriptSeminorm_le_native_type : Prop :=
  ∀ {d : ℕ} (N k : ℕ),
    manuscriptSeminorm (d := d) N k ≤ (2 : ℝ≥0) ^ N •
      (Finset.Iic (N, k)).sup (schwartzSeminormFamily ℂ (Euclidean d) ℂ)

def radialPoint_le_manuscript_type : Prop :=
  ∀ {d : ℕ} (N k : ℕ) (n : Fin (k + 1))
    (β : Fin n.val → Fin d) (x : Euclidean d),
    radialPoint N β x ≤ manuscriptSeminorm N k

def nativeSeminorm_le_manuscript_type : Prop :=
  ∀ {d : ℕ} (N n : ℕ),
    SchwartzMap.seminorm ℂ N n ≤ (d : ℝ≥0) ^ n • manuscriptSeminorm (d := d) N n

def manuscript_withSeminorms_type : Prop :=
  ∀ (d : ℕ),
    WithSeminorms (manuscriptFamily d)

def schwartz_is_manuscript_type : Prop :=
  ∀ {d : ℕ} (f : Test d),
    ManuscriptSchwartz (f : Euclidean d → ℂ)

def manuscript_iff_exists_schwartz_type : Prop :=
  ∀ {d : ℕ} (f : Euclidean d → ℂ),
    ManuscriptSchwartz f ↔ ∃ φ : Test d, (φ : Euclidean d → ℂ) = f

def coordinateMonomial_bound_type : Prop :=
  ∀ {d : ℕ} (α : Fin d → ℕ) (x : Euclidean d),
    |coordinateMonomial α x| ≤ (1 + ‖x‖) ^ (∑ j, α j)

def monomialPoint_apply_type : Prop :=
  ∀ {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d) (f : Test d),
    monomialPoint α β x f = |coordinateMonomial α x| * ‖coordinatePartial β f x‖

def monomialPoint_le_radialPoint_type : Prop :=
  ∀ {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d),
    monomialPoint α β x ≤ radialPoint (∑ j, α j) β x

def monomialSeminorm_le_manuscript_type : Prop :=
  ∀ {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d),
    monomialSeminorm α β ≤ manuscriptSeminorm (∑ j, α j) n

def monomialPoint_le_monomialSeminorm_type : Prop :=
  ∀ {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d)
    (x : Euclidean d),
    monomialPoint α β x ≤ monomialSeminorm α β

def monomial_withSeminorms_type : Prop :=
  ∀ (d : ℕ),
    WithSeminorms (monomialFamily d)

def fourier_zero_dimension_type : Prop :=
  ∀ (f : Test 0),
    fourierValue 0 f = f

def check_zero_dimension_type : Prop :=
  ∀ (f : Test 0),
    checkValue 0 f = f

def test_pairing_bilinear_type : Prop :=
  ∀ {d : ℕ} (U V : Tempered d) (f g : Test d) (a b : ℂ),
    (U + V) (f + g) = U f + U g + V f + V g ∧ (a • U) (b • f) = a * b * U f

def weak_dual_pointwise_type : Prop :=
  ∀ {d : ℕ} {ι : Type*} (l : Filter ι)
    (U : ι → WeakTempered d) (V : WeakTempered d),
    Filter.Tendsto U l (nhds V) ↔ ∀ f : Test d, Filter.Tendsto (fun i => U i f) l (nhds (V f))

def strong_dual_bounded_basis_type : Prop :=
  ∀ (d : ℕ),
    (nhds (0 : Tempered d)).HasBasis
      (fun BV : Set (Test d) × Set ℂ => Bornology.IsVonNBounded ℂ BV.1 ∧ BV.2 ∈ nhds (0 : ℂ))
      (fun BV => {U : Tempered d | ∀ f ∈ BV.1, U f ∈ BV.2})

def strong_to_weak_continuous_type : Prop :=
  ∀ (d : ℕ),
    Continuous (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) (Test d) ℂ)

def orthonormal_coordinates_type : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d),
    MeasurePreserving A ∧ ∀ v w : V, inner ℝ (A v) (A w) = inner ℝ v w

def orthonormal_fourier_type : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d) (f : Test d),
    𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (fourierValue d f)

def orthonormal_check_type : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {d : ℕ}
    (A : V ≃ₗᵢ[ℝ] Euclidean d) (f : Test d),
    𝓕⁻ (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f) =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv (checkValue d f)

def coordinatePartial_permutation_type : Prop :=
  ∀ {d n : ℕ} (β : Fin n → Fin d)
    (σ : Equiv.Perm (Fin n)) (f : Test d),
    coordinatePartial (β ∘ σ) f = coordinatePartial β f

def manuscriptSeminorm_apply_type : Prop :=
  ∀ {d : ℕ} (N k : ℕ) (f : Test d),
    manuscriptSeminorm N k f = ⨆ (n : Fin (k + 1)) (β : Fin n.val → Fin d) (x : Euclidean d),
      (1 + ‖x‖) ^ N * ‖coordinatePartial β f x‖

def monomialSeminorm_apply_type : Prop :=
  ∀ {d n : ℕ} (α : Fin d → ℕ) (β : Fin n → Fin d) (f : Test d),
    monomialSeminorm α β f = ⨆ x : Euclidean d,
      |coordinateMonomial α x| * ‖coordinatePartial β f x‖

def test_integrable_type : Prop :=
  ∀ {d : ℕ} (f : Test d),
    Integrable (f : Euclidean d → ℂ) ∧ Integrable (fourierValue d f : Euclidean d → ℂ) ∧
      Integrable (checkValue d f : Euclidean d → ℂ)

end P102.Specs.U3
