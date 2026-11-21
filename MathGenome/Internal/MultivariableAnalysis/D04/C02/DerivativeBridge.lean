import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C01.CoordinateEstimates
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open Set Filter Topology
namespace D04

def TotalDifferentiableAt : Specs.D04.C02.DerivativeBridge.TotalDifferentiableAtType :=
  @Specs.D04.C02.DerivativeBridge.TotalDifferentiableAtValue

def jacobian : Specs.D04.C02.DerivativeBridge.jacobianType :=
  @Specs.D04.C02.DerivativeBridge.jacobianValue

def scalarPartialDerivative : Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeType :=
  @Specs.D04.C02.DerivativeBridge.scalarPartialDerivativeValue

def scalarGradient : Specs.D04.C02.DerivativeBridge.scalarGradientType :=
  @Specs.D04.C02.DerivativeBridge.scalarGradientValue

section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Existence of the paper's open-domain remainder is ordinary total differentiability. -/
theorem totalDifferentiableAt_iff_differentiableAt (U : Set X) (f : X → Y) (a : X)
    (hU : IsOpen U) (ha : a ∈ U) :
    TotalDifferentiableAt U f a ↔ DifferentiableAt ℝ f a := by
  change (∃ A, HasTotalDerivative U f A a) ↔ _
  simp only [hasTotalDerivative_iff_hasFDerivAt U f _ a hU ha]
  rfl

theorem totalDerivative_unique (U : Set X) (f : X → Y) (a : X)
    (A B : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a)
    (hB : HasTotalDerivative U f B a) : A = B := by
  exact ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).unique
    ((hasTotalDerivative_iff_hasFDerivAt U f B a hB.1 hB.2.1).mp hB)

theorem totalDerivative_continuousAt (U : Set X) (f : X → Y) (a : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a) : ContinuousAt f a := by
  exact ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA).continuousAt

/-- The line restriction includes the zero direction without any exception. -/
theorem totalDerivative_hasDirectionalDerivative (U : Set X) (f : X → Y) (a v : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a) :
    HasDirectionalDerivative f a v (A v) := by
  apply (hasDirectionalDerivative_iff_hasDerivAt f a v (A v)).mpr
  have hf := (hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA
  have hl : HasDerivAt (fun t : ℝ => a + t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add a
  simpa [Function.comp_def] using hf.comp_hasDerivAt_of_eq 0 hl (by simp)

theorem totalDerivative_directionalDerivative (U : Set X) (f : X → Y) (a v : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a) :
    directionalDerivative f a v = A v :=
  directionalDerivative_eq f a v (A v)
    (totalDerivative_hasDirectionalDerivative U f a v A hA)

theorem hasDirectionalDerivative_zero (f : X → Y) (a : X) :
    HasDirectionalDerivative f a 0 0 := by
  apply (hasDirectionalDerivative_iff_hasDerivAt f a 0 0).mpr
  simpa using (hasDerivAt_const (0 : ℝ) (f a))

end Generic

/-- Every component has the projected derivative, and component differentiability
is sufficient, including when the family of components is empty. -/
theorem totalDifferentiableAt_iff_components {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (hU : IsOpen U) (ha : a ∈ U) :
    TotalDifferentiableAt U f a ↔
      ∀ i : Fin m, TotalDifferentiableAt U (fun x => f x i) a := by
  simp only [totalDifferentiableAt_iff_differentiableAt U _ a hU ha]
  exact differentiableAt_piLp 2

theorem component_hasTotalDerivative {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (i : Fin m) :
    HasTotalDerivative U (fun x => f x i) ((PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp A) a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U _ _ a hA.1 hA.2.1).mpr
  exact (PiLp.hasFDerivAt_apply 2 (f a) i).comp a
    ((hasTotalDerivative_iff_hasFDerivAt U f A a hA.1 hA.2.1).mp hA)

theorem totalDerivative_hasPartialDerivative {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (j : Fin n) :
    HasPartialDerivative f a j (A (standardBasis n j)) :=
  totalDerivative_hasDirectionalDerivative U f a (standardBasis n j) A hA

theorem totalDerivative_partialDerivative {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (j : Fin n) :
    partialDerivative f a j = A (standardBasis n j) :=
  totalDerivative_directionalDerivative U f a (standardBasis n j) A hA

theorem scalarPartialDerivative_eq {n : ℕ} (U : Set (E n))
    (f : E n → ℝ) (a : E n) (A : E n →L[ℝ] ℝ)
    (hA : HasTotalDerivative U f A a) (j : Fin n) :
    scalarPartialDerivative f a j = A (standardBasis n j) :=
  totalDerivative_directionalDerivative U f a (standardBasis n j) A hA

/-- The standard column matrix has scalar component partials as its entries. -/
theorem jacobian_apply {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hf : TotalDifferentiableAt U f a) (i : Fin m) (j : Fin n) :
    jacobian f a i j = scalarPartialDerivative (fun x => f x i) a j := by
  obtain ⟨A, hA⟩ := hf
  change matrixOfLinearMap (totalDerivative f a).toLinearMap i j = _
  rw [totalDerivative_eq U f A a hA, matrixOfLinearMap_apply]
  exact (scalarPartialDerivative_eq U (fun x => f x i) a _
    (component_hasTotalDerivative U f a A hA i) j).symm

/-- A matrix represents the total derivative precisely when it is the selected
Jacobian and differentiability really holds. Selector values alone assert no existence. -/
theorem jacobian_characterization {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a : E n) (J : Matrix (Fin m) (Fin n) ℝ) (hU : IsOpen U) (ha : a ∈ U) :
    HasTotalDerivative U f (LinearMap.toContinuousLinearMap (matrixLinearEquiv m n J)) a ↔
      TotalDifferentiableAt U f a ∧ jacobian f a = J := by
  constructor
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    change matrixOfLinearMap (totalDerivative f a).toLinearMap = J
    rw [totalDerivative_eq U f _ a h]
    exact (matrixLinearEquiv m n).symm_apply_apply J
  · rintro ⟨⟨A, hA⟩, hJ⟩
    have he : LinearMap.toContinuousLinearMap (matrixLinearEquiv m n J) = A := by
      rw [← hJ]
      change LinearMap.toContinuousLinearMap
        (matrixLinearEquiv m n (matrixOfLinearMap (totalDerivative f a).toLinearMap)) = A
      rw [matrix_linear_roundtrip, totalDerivative_eq U f A a hA]
      rfl
    rwa [he]

/-- The full proposed-matrix test, with the small remainder and its normalization
at zero explicitly quantified. No existence of partial derivatives is assumed. -/
theorem jacobian_iff_remainder {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a : E n) (J : Matrix (Fin m) (Fin n) ℝ) (hU : IsOpen U) (ha : a ∈ U) :
    (TotalDifferentiableAt U f a ∧ jacobian f a = J) ↔
      ∃ r : E n → E m, r 0 = 0 ∧
        (∀ h, a + h ∈ U → f (a + h) = f a + matrixLinearEquiv m n J h + r h) ∧
        Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0) := by
  rw [← jacobian_characterization U f a J hU ha]
  exact hasTotalDerivative_iff_remainder U f _ a hU ha

/-- The gradient is a column vector representing the scalar differential. -/
theorem scalarGradient_represents {n : ℕ} (f : E n → ℝ) (a h : E n) :
    totalDerivative f a h = inner ℝ (scalarGradient f a) h := by
  exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := a) (y := h)).symm

theorem scalarGradient_unique {n : ℕ} (f : E n → ℝ) (a : E n) :
    ∃! g : E n, ∀ h : E n, totalDerivative f a h = inner ℝ g h := by
  refine ⟨scalarGradient f a, scalarGradient_represents f a, ?_⟩
  intro g hg
  apply ext_inner_right ℝ
  intro h
  exact (hg h).symm.trans (scalarGradient_represents f a h)

theorem scalarGradient_apply {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TotalDifferentiableAt U f a) (j : Fin n) :
    scalarGradient f a j = scalarPartialDerivative f a j := by
  obtain ⟨A, hA⟩ := hf
  have h := scalarGradient_represents f a (standardBasis n j)
  rw [totalDerivative_eq U f A a hA] at h
  have hi : inner ℝ (scalarGradient f a) (standardBasis n j) = scalarGradient f a j :=
    EuclideanSpace.inner_basisFun_real (Fin n) _ j
  rw [hi] at h
  exact h.symm.trans (scalarPartialDerivative_eq U f a A hA j).symm

/-- The zero-dimensional source causes no missing uniqueness or existence case. -/
theorem hasTotalDerivative_from_zero {m : ℕ} (U : Set (E 0)) (f : E 0 → E m)
    (a : E 0) (hU : IsOpen U) (ha : a ∈ U) : HasTotalDerivative U f 0 a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U f 0 a hU ha).mpr
  exact hasFDerivAt_of_subsingleton f a

/-- A zero-dimensional target is the constant zero map. -/
theorem hasTotalDerivative_to_zero {n : ℕ} (U : Set (E n)) (f : E n → E 0)
    (a : E n) (hU : IsOpen U) (ha : a ∈ U) : HasTotalDerivative U f 0 a := by
  apply (hasTotalDerivative_iff_hasFDerivAt U f 0 a hU ha).mpr
  have he : f = fun _ => (0 : E 0) := funext fun x => vector_dimension_zero (f x)
  rw [he]
  exact hasFDerivAt_const (0 : E 0) a

end D04
