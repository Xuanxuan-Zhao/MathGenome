import MathGenome.Internal.MultivariableAnalysis.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.D04.C02.BilinearRules
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.VectorDifferentialIdentities
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The seven identities of d04:11:identities, for the canonical Euclidean
operators. Product identities follow from the Chapter 2 bilinear rules.
Second-order identities follow by coordinate expansion and symmetry of the
second total derivative; all local replacements are justified on the open domain. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04
namespace VectorIdentities

/-- Evaluate the scalar differential on the i-th coordinate vector. -/
private def d {n : ℕ} (f : E n → ℝ) (i : Fin n) (x : E n) : ℝ :=
  totalDerivative f x (standardBasis n i)

private theorem gradient_component {n : ℕ} (f : E n → ℝ) (x : E n) (i : Fin n) :
    scalarGradient f x i = d f i x := by
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) (scalarGradient f x) i]
  exact (scalarGradient_represents f x (standardBasis n i)).symm

private theorem jacobian_entry {n m : ℕ} (F : E n → E m) (x : E n)
    (i : Fin m) (j : Fin n) :
    jacobian F x i j = (totalDerivative F x (standardBasis n j)) i := by
  exact matrixOfLinearMap_apply _ i j

private theorem divergence_sum {n : ℕ} (F : E n → E n) (x : E n) :
    divergence F x = ∑ i, (totalDerivative F x (standardBasis n i)) i := by
  rw [divergence_eq_jacobian_trace]
  exact Finset.sum_congr rfl fun i _ => jacobian_entry F x i i

@[simp] private theorem curl_0 (F : E 3 → E 3) (x : E 3) :
    curl F x 0 = (totalDerivative F x (standardBasis 3 1)) 2 -
      (totalDerivative F x (standardBasis 3 2)) 1 := by
  change jacobian F x 2 1 - jacobian F x 1 2 = _
  simp only [jacobian_entry]

@[simp] private theorem curl_1 (F : E 3 → E 3) (x : E 3) :
    curl F x 1 = (totalDerivative F x (standardBasis 3 2)) 0 -
      (totalDerivative F x (standardBasis 3 0)) 2 := by
  change jacobian F x 0 2 - jacobian F x 2 0 = _
  simp only [jacobian_entry]

@[simp] private theorem curl_2 (F : E 3 → E 3) (x : E 3) :
    curl F x 2 = (totalDerivative F x (standardBasis 3 0)) 1 -
      (totalDerivative F x (standardBasis 3 1)) 0 := by
  change jacobian F x 1 0 - jacobian F x 0 1 = _
  simp only [jacobian_entry]

@[simp] private theorem cross_0 (u v : E 3) : cross u v 0 = u 1 * v 2 - u 2 * v 1 := rfl
@[simp] private theorem cross_1 (u v : E 3) : cross u v 1 = u 2 * v 0 - u 0 * v 2 := rfl
@[simp] private theorem cross_2 (u v : E 3) : cross u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

/-- Projection commutes with a derivative that exists. -/
private theorem component_d {n m : ℕ} (F : E n → E m) (x : E n)
    (hF : DifferentiableAt ℝ F x) (i : Fin m) (j : Fin n) :
    d (fun y => F y i) j x = (totalDerivative F x (standardBasis n j)) i := by
  have hd := (PiLp.hasFDerivAt_apply 2 (F x) i).comp x hF.hasFDerivAt
  change fderiv ℝ (fun y => F y i) x (standardBasis n j) = _
  have he : fderiv ℝ (fun y => F y i) x =
      (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ F x) := by
    simpa only [Function.comp_def] using hd.fderiv
  rw [he]
  rfl

private theorem divergence_d {n : ℕ} (F : E n → E n) (x : E n)
    (hF : DifferentiableAt ℝ F x) :
    divergence F x = ∑ i, d (fun y => F y i) i x := by
  simp only [divergence_sum, component_d F x hF]

private theorem curl_d (F : E 3 → E 3) (x : E 3)
    (hF : DifferentiableAt ℝ F x) :
    curl F x = WithLp.toLp 2
      ![d (fun y => F y 2) 1 x - d (fun y => F y 1) 2 x,
        d (fun y => F y 0) 2 x - d (fun y => F y 2) 0 x,
        d (fun y => F y 1) 0 x - d (fun y => F y 0) 1 x] := by
  ext i
  fin_cases i <;> simp [component_d F x hF]

private theorem cr_differentiable {n : ℕ} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set (E n)) (f : E n → Y) (x : E n)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  (totalDifferentiableAt_iff_differentiableAt U f x hU hx).mp (hf.1 x hx)

private theorem component_cr {n m : ℕ} (r : ℕ) (U : Set (E n))
    (F : E n → E m) (hU : IsOpen U) (hF : CrOn r U F) (i : Fin m) :
    CrOn r U (fun y => F y i) := by
  apply (crOn_iff_contDiffOn r U _ hU).mpr
  exact (PiLp.proj 2 (fun _ : Fin m => ℝ) i).contDiff.comp_contDiffOn
    ((crOn_iff_contDiffOn r U F hU).mp hF)

private theorem cr_lower {n : ℕ} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set (E n)) (f : E n → Y) (hU : IsOpen U) (hf : CrOn 2 U f) :
    CrOn 1 U f := by
  apply (crOn_iff_contDiffOn 1 U f hU).mpr
  exact ((crOn_iff_contDiffOn 2 U f hU).mp hf).of_le (by norm_num)

private theorem d_cr {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f) (i : Fin n) : CrOn 1 U (d f i) := by
  apply (crOn_iff_contDiffOn 1 U (d f i) hU).mpr
  have hd := (crOn_iff_contDiffOn 1 U (totalDerivative f) hU).mp hf.2
  exact (ContinuousLinearMap.apply ℝ ℝ (standardBasis n i)).contDiff.comp_contDiffOn hd

private theorem d_sub {n : ℕ} (f g : E n → ℝ) (x : E n) (i : Fin n)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    d (fun y => f y - g y) i x = d f i x - d g i x := by
  change fderiv ℝ (fun y => f y - g y) x (standardBasis n i) = _
  rw [fderiv_fun_sub hf hg]
  rfl

private theorem d_sum {n : ℕ} {ι : Type} [Fintype ι] (f : ι → E n → ℝ)
    (x : E n) (i : Fin n) (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    d (fun y => ∑ j, f j y) i x = ∑ j, d (f j) i x := by
  change fderiv ℝ (fun y => ∑ j, f j y) x (standardBasis n i) = _
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp only [sum_apply, d]
  rfl

private theorem d_congr {n : ℕ} (U : Set (E n)) (f g : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hx : x ∈ U) (hfg : EqOn f g U) (i : Fin n) :
    d f i x = d g i x := by
  exact congrArg (fun A : E n →L[ℝ] ℝ => A (standardBasis n i))
    (totalDerivative_congr U f x g hU hx hfg)

private theorem d_twice {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U) (i j : Fin n) :
    d (d f j) i x = fderiv ℝ (fderiv ℝ f) x (standardBasis n i) (standardBasis n j) := by
  have hd := cr_differentiable U (totalDerivative f) x hU hf.2 hx
  have he := ((ContinuousLinearMap.apply ℝ ℝ (standardBasis n j)).hasFDerivAt.comp x
    hd.hasFDerivAt).fderiv
  exact congrArg (fun A : E n →L[ℝ] ℝ => A (standardBasis n i)) he

private theorem d_commute {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U) (i j : Fin n) :
    d (d f j) i x = d (d f i) j x := by
  rw [d_twice U f x hU hf hx, d_twice U f x hU hf hx]
  have hd := cr_differentiable U (totalDerivative f) x hU hf.2 hx
  have hnear : ∀ᶠ y in 𝓝 x, HasFDerivAt f (fderiv ℝ f y) y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (totalDifferentiableAt_iff_differentiableAt U f y hU hy).mp (hf.1 y hy)
      |>.hasFDerivAt
  exact second_derivative_symmetric_of_eventually hnear hd.hasFDerivAt _ _

private theorem curl_cr {U : Set (E 3)} {F : E 3 → E 3}
    (hU : IsOpen U) (hF : CrOn 2 U F) : CrOn 1 U (curl F) := by
  have hc (i j : Fin 3) : ContDiffOn ℝ 1 (d (fun y => F y i) j) U :=
    (crOn_iff_contDiffOn 1 U _ hU).mp (d_cr U _ hU (component_cr 2 U F hU hF i) j)
  apply (crOn_iff_contDiffOn 1 U _ hU).mpr
  have he : ContDiffOn ℝ 1 (fun y => WithLp.toLp 2
      ![d (fun z => F z 2) 1 y - d (fun z => F z 1) 2 y,
        d (fun z => F z 0) 2 y - d (fun z => F z 2) 0 y,
        d (fun z => F z 1) 0 y - d (fun z => F z 0) 1 y]) U := by
    apply (contDiffOn_piLp 2).mpr
    intro i
    fin_cases i
    · exact (hc 2 1).sub (hc 1 2)
    · exact (hc 0 2).sub (hc 2 0)
    · exact (hc 1 0).sub (hc 0 1)
  apply he.congr
  intro y hy
  exact curl_d F y (cr_differentiable U F y hU (cr_lower U F hU hF) hy)

private theorem d_curl_0 (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin 3) :
    d (fun y => curl F y 0) j x =
      d (d (fun y => F y 2) 1) j x - d (d (fun y => F y 1) 2) j x := by
  calc
    _ = d (fun y => d (fun z => F z 2) 1 y - d (fun z => F z 1) 2 y) j x := by
      apply d_congr U _ _ x hU hx
      intro y hy
      have he := congrArg (fun v : E 3 => v 0)
        (curl_d F y (cr_differentiable U F y hU (cr_lower U F hU hF) hy))
      exact he
    _ = _ := d_sub _ _ x j
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 2) 1) hx)
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 1) 2) hx)

private theorem d_curl_1 (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin 3) :
    d (fun y => curl F y 1) j x =
      d (d (fun y => F y 0) 2) j x - d (d (fun y => F y 2) 0) j x := by
  calc
    _ = d (fun y => d (fun z => F z 0) 2 y - d (fun z => F z 2) 0 y) j x := by
      apply d_congr U _ _ x hU hx
      intro y hy
      have he := congrArg (fun v : E 3 => v 1)
        (curl_d F y (cr_differentiable U F y hU (cr_lower U F hU hF) hy))
      exact he
    _ = _ := d_sub _ _ x j
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 0) 2) hx)
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 2) 0) hx)

private theorem d_curl_2 (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin 3) :
    d (fun y => curl F y 2) j x =
      d (d (fun y => F y 1) 0) j x - d (d (fun y => F y 0) 1) j x := by
  calc
    _ = d (fun y => d (fun z => F z 1) 0 y - d (fun z => F z 0) 1 y) j x := by
      apply d_congr U _ _ x hU hx
      intro y hy
      have he := congrArg (fun v : E 3 => v 2)
        (curl_d F y (cr_differentiable U F y hU (cr_lower U F hU hF) hy))
      exact he
    _ = _ := d_sub _ _ x j
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 1) 0) hx)
      (cr_differentiable U _ x hU (d_cr U _ hU (component_cr 2 U F hU hF 0) 1) hx)

private theorem d_divergence {n : ℕ} (U : Set (E n)) (F : E n → E n) (x : E n)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin n) :
    d (divergence F) j x = ∑ i, d (d (fun y => F y i) i) j x := by
  calc
    _ = d (fun y => ∑ i, d (fun z => F z i) i y) j x := by
      apply d_congr U _ _ x hU hx
      intro y hy
      exact divergence_d F y (cr_differentiable U F y hU (cr_lower U F hU hF) hy)
    _ = _ := d_sum _ x j (fun i => cr_differentiable U _ x hU
      (d_cr U _ hU (component_cr 2 U F hU hF i) i) hx)

private theorem laplacian_d {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U) :
    laplacian f x = ∑ i, d (d f i) i x := by
  rw [laplacian_eq_divergence_gradient,
    divergence_d _ x (cr_differentiable U _ x hU (gradient_crOn U f hU hf) hx)]
  simp only [gradient_component]

private theorem vectorLaplacian_d {n m : ℕ} (U : Set (E n)) (F : E n → E m) (x : E n)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin m) :
    vectorLaplacian F x j = ∑ i, d (d (fun y => F y j) i) i x := by
  rw [vectorLaplacian_apply]
  exact laplacian_d U _ x hU (component_cr 2 U F hU hF j) hx

end VectorIdentities
open VectorIdentities

theorem gradient_product {n : ℕ} (U : Set (E n)) (f g : E n → ℝ) (x : E n)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (hg : CrOn 1 U g) (hx : x ∈ U) :
    scalarGradient (fun y => f y * g y) x =
      f x • scalarGradient g x + g x • scalarGradient f x := by
  have hd := (scalar_mul_totalDerivative U f g x (hf.1 x hx) (hg.1 x hx)).2
  ext i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, gradient_component]
  change totalDerivative (fun y => f y * g y) x (standardBasis n i) = _
  rw [hd]
  simp only [d]
  ring

theorem divergence_smul {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (F : E n → E n) (x : E n)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (hF : CrOn 1 U F) (hx : x ∈ U) :
    divergence (fun y => f y • F y) x =
      inner ℝ (scalarGradient f x) (F x) + f x * divergence F x := by
  have hd := (smul_totalDerivative U f F x (hf.1 x hx) (hF.1 x hx)).2
  simp only [divergence_sum, hd, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    inner_coordinates, gradient_component, Finset.sum_add_distrib, Finset.mul_sum]
  rfl

theorem curl_smul (U : Set (E 3)) (f : E 3 → ℝ) (F : E 3 → E 3) (x : E 3)
    (_hU : IsOpen U) (hf : CrOn 1 U f) (hF : CrOn 1 U F) (hx : x ∈ U) :
    curl (fun y => f y • F y) x =
      cross (scalarGradient f x) (F x) + f x • curl F x := by
  have hd := (smul_totalDerivative U f F x (hf.1 x hx) (hF.1 x hx)).2
  ext i
  fin_cases i <;> simp [hd, gradient_component, d] <;> ring

theorem divergence_cross (U : Set (E 3)) (F G : E 3 → E 3) (x : E 3)
    (_hU : IsOpen U) (hF : CrOn 1 U F) (hG : CrOn 1 U G) (hx : x ∈ U) :
    divergence (fun y => cross (F y) (G y)) x =
      inner ℝ (G x) (curl F x) - inner ℝ (F x) (curl G x) := by
  have hd := (cross_totalDerivative U F G x (hF.1 x hx) (hG.1 x hx)).2
  simp [divergence_sum, inner_coordinates, Fin.sum_univ_succ, hd]
  ring

theorem curl_gradient (U : Set (E 3)) (f : E 3 → ℝ) (x : E 3)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U) :
    curl (scalarGradient f) x = 0 := by
  rw [curl_d _ x (cr_differentiable U _ x hU (gradient_crOn U f hU hf) hx)]
  simp only [gradient_component]
  have hc := d_commute U f x hU hf hx
  ext i
  fin_cases i <;> simp [hc]

theorem divergence_curl (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) :
    divergence (curl F) x = 0 := by
  rw [divergence_d _ x (cr_differentiable U _ x hU (curl_cr hU hF) hx)]
  rw [Fin.sum_univ_three]
  erw [d_curl_0 U F x hU hF hx, d_curl_1 U F x hU hF hx, d_curl_2 U F x hU hF hx]
  have hc (i j k : Fin 3) := d_commute U (fun y => F y i) x hU
    (component_cr 2 U F hU hF i) hx j k
  rw [hc 2 0 1, hc 1 0 2, hc 0 1 2]
  ring

theorem curl_curl (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) :
    curl (curl F) x = scalarGradient (divergence F) x - vectorLaplacian F x := by
  rw [curl_d _ x (cr_differentiable U _ x hU (curl_cr hU hF) hx)]
  have hc (i j k : Fin 3) := d_commute U (fun y => F y i) x hU
    (component_cr 2 U F hU hF i) hx j k
  ext i
  fin_cases i <;>
    simp only [PiLp.sub_apply, gradient_component, d_divergence U F x hU hF hx,
      vectorLaplacian_d U F x hU hF hx, Fin.sum_univ_three,
      d_curl_0 U F x hU hF hx, d_curl_1 U F x hU hF hx, d_curl_2 U F x hU hF hx]
  · change d (d (fun y => F y 1) 0) 1 x - d (d (fun y => F y 0) 1) 1 x -
        (d (d (fun y => F y 0) 2) 2 x - d (d (fun y => F y 2) 0) 2 x) =
      d (d (fun y => F y 0) 0) 0 x + d (d (fun y => F y 1) 1) 0 x +
        d (d (fun y => F y 2) 2) 0 x -
        (d (d (fun y => F y 0) 0) 0 x + d (d (fun y => F y 0) 1) 1 x +
          d (d (fun y => F y 0) 2) 2 x)
    rw [hc 1 1 0, hc 2 2 0]
    ring
  · change d (d (fun y => F y 2) 1) 2 x - d (d (fun y => F y 1) 2) 2 x -
        (d (d (fun y => F y 1) 0) 0 x - d (d (fun y => F y 0) 1) 0 x) =
      d (d (fun y => F y 0) 0) 1 x + d (d (fun y => F y 1) 1) 1 x +
        d (d (fun y => F y 2) 2) 1 x -
        (d (d (fun y => F y 1) 0) 0 x + d (d (fun y => F y 1) 1) 1 x +
          d (d (fun y => F y 1) 2) 2 x)
    rw [hc 0 0 1, hc 2 2 1]
    ring
  · change d (d (fun y => F y 0) 2) 0 x - d (d (fun y => F y 2) 0) 0 x -
        (d (d (fun y => F y 2) 1) 1 x - d (d (fun y => F y 1) 2) 1 x) =
      d (d (fun y => F y 0) 0) 2 x + d (d (fun y => F y 1) 1) 2 x +
        d (d (fun y => F y 2) 2) 2 x -
        (d (d (fun y => F y 2) 0) 0 x + d (d (fun y => F y 2) 1) 1 x +
          d (d (fun y => F y 2) 2) 2 x)
    rw [hc 0 0 2, hc 1 1 2]
    ring

end D04
