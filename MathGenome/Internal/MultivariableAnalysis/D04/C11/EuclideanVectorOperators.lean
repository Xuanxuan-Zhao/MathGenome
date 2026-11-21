import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The Euclidean operators of d04:11:operators. The gradient is reused from
Chapter 2. The definitions are total derivative selectors, as in that chapter;
the coordinate identifications assert C¹ or C² regularity on the open domain.
Curl uses the standard orientation. The exterior-form orientation bridge is
allocated to d04:13:dictionary. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04

/-- Divergence is the basis-independent trace of the total derivative. -/
def divergence : Specs.D04.C11.EuclideanVectorOperators.divergenceType :=
  @Specs.D04.C11.EuclideanVectorOperators.divergenceValue

/-- Standard oriented curl in the ordered coordinates x,y,z. -/
def curl : Specs.D04.C11.EuclideanVectorOperators.curlType :=
  Specs.D04.C11.EuclideanVectorOperators.curlValue

/-- The scalar Laplacian is divergence of the existing scalar gradient. -/
def laplacian : Specs.D04.C11.EuclideanVectorOperators.laplacianType :=
  @Specs.D04.C11.EuclideanVectorOperators.laplacianValue

/-- The vector Laplacian applies the scalar operator to each component. -/
def vectorLaplacian : Specs.D04.C11.EuclideanVectorOperators.vectorLaplacianType :=
  @Specs.D04.C11.EuclideanVectorOperators.vectorLaplacianValue

theorem gradient_characterization {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (_hU : IsOpen U) (_hf : CrOn 1 U f) (_hx : x ∈ U) :
    (∀ v, totalDerivative f x v = inner ℝ (scalarGradient f x) v) ∧
    (∀ g : E n, (∀ v, totalDerivative f x v = inner ℝ g v) → g = scalarGradient f x) := by
  refine ⟨scalarGradient_represents f x, ?_⟩
  intro g hg
  apply ext_inner_right ℝ
  intro v
  exact (hg v).symm.trans (scalarGradient_represents f x v)

theorem gradient_coordinates {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (hx : x ∈ U) (i : Fin n) :
    scalarGradient f x i = scalarPartialDerivative f x i :=
  scalarGradient_apply U f x (hf.1 x hx) i

theorem divergence_eq_trace {n : ℕ} (F : E n → E n) (x : E n) :
    divergence F x = LinearMap.trace ℝ (E n) (totalDerivative F x).toLinearMap := rfl

theorem divergence_eq_jacobian_trace {n : ℕ} (F : E n → E n) (x : E n) :
    divergence F x = Matrix.trace (jacobian F x) := by
  rw [divergence_eq_trace, LinearMap.trace_eq_matrix_trace ℝ (standardBasis n)]
  congr 1

theorem divergence_coordinates {n : ℕ} (U : Set (E n)) (F : E n → E n) (x : E n)
    (_hU : IsOpen U) (hF : CrOn 1 U F) (hx : x ∈ U) :
    divergence F x = ∑ i, scalarPartialDerivative (fun y => F y i) x i := by
  rw [divergence_eq_jacobian_trace]
  exact Finset.sum_congr rfl fun i _ => jacobian_apply U F x (hF.1 x hx) i i

theorem curl_coordinates (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (_hU : IsOpen U) (hF : CrOn 1 U F) (hx : x ∈ U) :
    curl F x = WithLp.toLp 2
      ![scalarPartialDerivative (fun y => F y 2) x 1 - scalarPartialDerivative (fun y => F y 1) x 2,
        scalarPartialDerivative (fun y => F y 0) x 2 - scalarPartialDerivative (fun y => F y 2) x 0,
        scalarPartialDerivative (fun y => F y 1) x 0 - scalarPartialDerivative (fun y => F y 0) x 1] := by
  change WithLp.toLp 2 ![jacobian F x 2 1 - jacobian F x 1 2,
    jacobian F x 0 2 - jacobian F x 2 0, jacobian F x 1 0 - jacobian F x 0 1] = _
  simp only [jacobian_apply U F x (hF.1 x hx)]

theorem laplacian_eq_divergence_gradient {n : ℕ} (f : E n → ℝ) (x : E n) :
    laplacian f x = divergence (scalarGradient f) x := rfl

/-- Raising a scalar differential by the Euclidean metric preserves C¹ regularity. -/
theorem gradient_crOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) : CrOn 1 U (scalarGradient f) := by
  apply (crOn_iff_contDiffOn 1 U (scalarGradient f) hU).mpr
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
    (crOn_iff_contDiffOn 1 U (totalDerivative f) hU).mp hf.2
  exact (InnerProductSpace.toDual ℝ (E n)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hd

/-- Coordinate line derivatives depend only on the germ in the open domain. -/
private theorem scalarPartialDerivative_eqOn {n : ℕ} (U : Set (E n))
    (f g : E n → ℝ) (x : E n) (hU : IsOpen U) (hx : x ∈ U)
    (hfg : EqOn f g U) (i : Fin n) :
    scalarPartialDerivative f x i = scalarPartialDerivative g x i := by
  have he : f =ᶠ[𝓝 x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hfg
  have hl : Tendsto (fun t : ℝ => x + t • standardBasis n i) (𝓝 0) (𝓝 x) := by
    convert (continuous_const.add (continuous_id.smul continuous_const) :
      Continuous (fun t : ℝ => x + t • standardBasis n i)).continuousAt.tendsto (x := 0) using 1
    simp
  change deriv (fun t : ℝ => f (x + t • standardBasis n i)) 0 =
    deriv (fun t : ℝ => g (x + t • standardBasis n i)) 0
  exact (he.comp_tendsto hl).deriv_eq

theorem laplacian_coordinates {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U) :
    laplacian f x = ∑ i, scalarPartialDerivative (fun y => scalarPartialDerivative f y i) x i := by
  have hf1 : CrOn 1 U f := (crOn_iff_contDiffOn 1 U f hU).mpr
    (((crOn_iff_contDiffOn 2 U f hU).mp hf).of_le (by norm_num))
  rw [laplacian_eq_divergence_gradient,
    divergence_coordinates U (scalarGradient f) x hU (gradient_crOn U f hU hf) hx]
  apply Finset.sum_congr rfl
  intro i _
  exact scalarPartialDerivative_eqOn U _ _ x hU hx
    (fun y hy => gradient_coordinates U f y hU hf1 hy i) i

theorem vectorLaplacian_apply {n m : ℕ} (F : E n → E m) (x : E n) (i : Fin m) :
    vectorLaplacian F x i = laplacian (fun y => F y i) x := rfl

theorem vectorLaplacian_coordinates {n m : ℕ} (U : Set (E n)) (F : E n → E m) (x : E n)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin m) :
    vectorLaplacian F x j =
      ∑ i, scalarPartialDerivative (fun y => scalarPartialDerivative (fun z => F z j) y i) x i := by
  rw [vectorLaplacian_apply]
  apply laplacian_coordinates U _ x hU _ hx
  apply (crOn_iff_contDiffOn 2 U _ hU).mpr
  exact (PiLp.proj 2 (fun _ : Fin m => ℝ) j).contDiff.comp_contDiffOn
    ((crOn_iff_contDiffOn 2 U F hU).mp hF)

theorem gradient_dimension_zero (f : E 0 → ℝ) (x : E 0) : scalarGradient f x = 0 :=
  vector_dimension_zero _

theorem divergence_dimension_zero (F : E 0 → E 0) (x : E 0) : divergence F x = 0 := by
  rw [divergence_eq_jacobian_trace]
  simp [Matrix.trace]

theorem laplacian_dimension_zero (f : E 0 → ℝ) (x : E 0) : laplacian f x = 0 :=
  divergence_dimension_zero _ _

theorem vectorLaplacian_dimension_zero {m : ℕ} (F : E 0 → E m) (x : E 0) :
    vectorLaplacian F x = 0 := by
  ext i
  exact laplacian_dimension_zero _ _

end D04
