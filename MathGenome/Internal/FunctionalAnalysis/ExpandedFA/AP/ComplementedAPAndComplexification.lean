import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.ComplementedAPAndComplexification
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Normed.Operator.Mul

namespace ExpandedFA.AP

universe u v w
noncomputable section
open ComplementedAPAndComplexificationSpec

/-- The range of a composition through a finite-dimensional range is finite-dimensional. -/
theorem finiteRank_comp {𝕜 : Type*} [RCLike 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [NormedSpace 𝕜 Z]
    (F : Y →L[𝕜] Y) (hF : FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap))
    (i : X →L[𝕜] Y) (p : Y →L[𝕜] Z) :
    FiniteDimensional 𝕜 (LinearMap.range (p.comp (F.comp i)).toLinearMap) := by
  let := hF
  apply FiniteDimensional.of_injective
    (Submodule.inclusion (show LinearMap.range (p.comp (F.comp i)).toLinearMap ≤
      (LinearMap.range F.toLinearMap).map p.toLinearMap from by
        rintro _ ⟨x, rfl⟩
        exact ⟨F (i x), ⟨i x, rfl⟩, rfl⟩))
  exact Submodule.inclusion_injective _

/-- Compose compact-set approximants with inclusion and projection. -/
theorem hasApproximationProperty_of_retraction : ComplementedAP := by
  intro 𝕜 _ X Y _ _ _ _ i p hpi hY
  apply (Compactness.hasApproximationProperty_iff_pointwise 𝕜 X).mpr
  intro K hK ε hε
  let C : ℝ := ‖p‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hpC : ‖p‖ ≤ C := by dsimp [C]; linarith
  obtain ⟨F, hF, herr⟩ :=
    (Compactness.hasApproximationProperty_iff_pointwise 𝕜 Y).mp hY
      (i '' K) (hK.image i.continuous) (ε / C) (div_pos hε hC)
  refine ⟨p.comp (F.comp i), finiteRank_comp F hF i p, ?_⟩
  intro x hx
  have h := herr (i x) ⟨x, hx, rfl⟩
  calc
    ‖(p.comp (F.comp i)) x - x‖ = ‖p (F (i x) - i x)‖ := by
      simp only [ContinuousLinearMap.comp_apply, map_sub, hpi]
    _ ≤ ‖p‖ * ‖F (i x) - i x‖ := p.le_opNorm _
    _ ≤ C * ‖F (i x) - i x‖ := mul_le_mul_of_nonneg_right hpC (norm_nonneg _)
    _ < C * (ε / C) := mul_lt_mul_of_pos_left h hC
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hC)

/-- In particular, every boundedly complemented subspace inherits AP. -/
theorem hasApproximationProperty_of_closedComplemented : ClosedComplementedAP := by
  intro 𝕜 _ Y _ _ M hM hY
  obtain ⟨p, hp⟩ := hM
  exact hasApproximationProperty_of_retraction 𝕜 M Y M.subtypeL p hp hY

/-- Restricting scalars on a finite complex-rank map gives finite real rank. -/
theorem finiteRank_restrictScalars {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedSpace ℝ Y] [IsScalarTower ℝ ℂ Y]
    (F : Y →L[ℂ] Y)
    (hF : FiniteDimensional ℂ (LinearMap.range F.toLinearMap)) :
    FiniteDimensional ℝ (LinearMap.range (F.restrictScalars ℝ).toLinearMap) := by
  let := hF
  let : FiniteDimensional ℝ (LinearMap.range F.toLinearMap) :=
    FiniteDimensional.trans ℝ ℂ _
  let j : LinearMap.range F.toLinearMap →ₗ[ℝ] Y :=
    (LinearMap.range F.toLinearMap).subtype.restrictScalars ℝ
  have heq : LinearMap.range (F.restrictScalars ℝ).toLinearMap = LinearMap.range j := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨F x, ⟨x, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨y, x, hx⟩, rfl⟩
      exact ⟨x, hx⟩
  rw [heq]
  infer_instance

/-- Restriction of scalars with any compatible real normed-space structure. -/
theorem hasApproximationProperty_restrictScalars (Y : Type*) [NormedAddCommGroup Y]
    [NormedSpace ℂ Y] [NormedSpace ℝ Y] [IsScalarTower ℝ ℂ Y]
    (h : AP ℂ Y) : AP ℝ Y := by
  intro K hK ε hε
  obtain ⟨F, hF, herr⟩ := h K hK ε hε
  exact ⟨F.restrictScalars ℝ, finiteRank_restrictScalars F hF, herr⟩

/-- Complex AP implies AP of the underlying real normed space. -/
theorem hasApproximationProperty_real_of_complex : ComplexAPImpliesRealAP := by
  intro Y _ _ h K hK ε hε
  obtain ⟨F, hF, herr⟩ := h K hK ε hε
  exact ⟨F.restrictScalars ℝ, finiteRank_restrictScalars F hF, herr⟩

/-- A real-linear map `f : ℂ → X` represents `f 1 - i f I`.
Its operator norm is the Taylor complexification norm. -/
def TaylorComplexification (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] :=
  ℂ →L[ℝ] X

namespace TaylorComplexification

variable (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]

instance : CoeFun (TaylorComplexification X) (fun _ => ℂ → X) :=
  ⟨fun f => DFunLike.coe (F := ℂ →L[ℝ] X) f⟩

@[ext] theorem ext {f g : TaylorComplexification X} (h : ∀ z, f z = g z) : f = g :=
  ContinuousLinearMap.ext h

instance : NormedAddCommGroup (TaylorComplexification X) :=
  inferInstanceAs (NormedAddCommGroup (ℂ →L[ℝ] X))

instance : NormedSpace ℝ (TaylorComplexification X) :=
  inferInstanceAs (NormedSpace ℝ (ℂ →L[ℝ] X))

instance [CompleteSpace X] : CompleteSpace (TaylorComplexification X) :=
  inferInstanceAs (CompleteSpace (ℂ →L[ℝ] X))

instance : SMul ℂ (TaylorComplexification X) where
  smul c f := (f : ℂ →L[ℝ] X).comp ((ContinuousLinearMap.mul ℝ ℂ) c)

@[simp] theorem complex_smul_apply (c : ℂ) (f : TaylorComplexification X) (z : ℂ) :
    (c • f : ℂ →L[ℝ] X) z = (f : ℂ →L[ℝ] X) (c * z) := rfl

instance : Module ℂ (TaylorComplexification X) where
  one_smul f := by ext z; change f (1 * z) = f z; rw [one_mul]
  mul_smul a b f := by
    ext z
    change f ((a * b) * z) = f (b * (a * z))
    congr 1
    ring
  smul_add c f g := by ext z; rfl
  smul_zero c := by ext z; rfl
  add_smul a b f := by
    ext z
    change f ((a + b) * z) = f (a * z) + f (b * z)
    rw [add_mul]
    exact (f : ℂ →L[ℝ] X).map_add _ _
  zero_smul f := by
    ext z
    change f (0 * z) = 0
    rw [zero_mul]
    exact (f : ℂ →L[ℝ] X).map_zero

instance : IsScalarTower ℝ ℂ (TaylorComplexification X) where
  smul_assoc r c f := by
    ext z
    change f ((r • c) * z) = r • f (c * z)
    rw [smul_mul_assoc]
    exact (f : ℂ →L[ℝ] X).map_smul r _

instance : NormedSpace ℂ (TaylorComplexification X) where
  norm_smul_le c f := by
    change ‖(f : ℂ →L[ℝ] X).comp ((ContinuousLinearMap.mul ℝ ℂ) c)‖ ≤ ‖c‖ * ‖f‖
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro z
    change ‖f (c * z)‖ ≤ ‖c‖ * ‖f‖ * ‖z‖
    calc
      ‖f (c * z)‖ ≤ ‖f‖ * ‖c * z‖ := f.le_opNorm _
      _ = ‖c‖ * ‖f‖ * ‖z‖ := by rw [norm_mul]; ring

/-- Real coordinates `x + i y` are sent to `z ↦ re z • x - im z • y`. -/
def coordinatesLinear : (X × X) ≃ₗ[ℝ] TaylorComplexification X where
  toFun q := Complex.reCLM.smulRight q.1 - Complex.imCLM.smulRight q.2
  invFun f := (f 1, -f Complex.I)
  left_inv q := by simp
  right_inv f := by
    change ℂ →L[ℝ] X at f
    ext z
    change z.re • f 1 - z.im • (-f Complex.I) = f z
    rw [smul_neg, sub_neg_eq_add, ← map_smul, ← map_smul, ← map_add]
    congr 1
    simpa only [Complex.real_smul, mul_one] using Complex.re_add_im z
  map_add' q r := by
    ext z
    change z.re • (q.1 + r.1) - z.im • (q.2 + r.2) =
      (z.re • q.1 - z.im • q.2) + (z.re • r.1 - z.im • r.2)
    simp only [smul_add]
    abel
  map_smul' r q := by
    ext z
    change z.re • (r • q.1) - z.im • (r • q.2) =
      r • (z.re • q.1 - z.im • q.2)
    simp only [smul_sub, smul_comm r]

@[simp] theorem coordinatesLinear_apply (x y : X) (z : ℂ) :
    (coordinatesLinear X (x,y) : ℂ →L[ℝ] X) z = z.re • x - z.im • y := rfl

/-- The product norm is bounded by the Taylor norm (tests at `1` and `I`). -/
theorem norm_coordinates_lower (x y : X) :
    ‖(x, y)‖ ≤ ‖coordinatesLinear X (x, y)‖ := by
  change max ‖x‖ ‖y‖ ≤ ‖Complex.reCLM.smulRight x - Complex.imCLM.smulRight y‖
  apply max_le
  · have h := (Complex.reCLM.smulRight x - Complex.imCLM.smulRight y).le_opNorm 1
    simpa using h
  · have h := (Complex.reCLM.smulRight x - Complex.imCLM.smulRight y).le_opNorm Complex.I
    simpa using h

/-- An upper bound by twice the product norm. -/
theorem norm_coordinates_upper (x y : X) :
    ‖coordinatesLinear X (x, y)‖ ≤ 2 * ‖(x, y)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  change ‖z.re • x - z.im • y‖ ≤ (2 * ‖(x, y)‖) * ‖z‖
  have hx : ‖x‖ ≤ ‖(x, y)‖ := le_max_left _ _
  have hy : ‖y‖ ≤ ‖(x, y)‖ := le_max_right _ _
  calc
    ‖z.re • x - z.im • y‖ ≤ ‖z.re • x‖ + ‖z.im • y‖ := norm_sub_le _ _
    _ = |z.re| * ‖x‖ + |z.im| * ‖y‖ := by rw [norm_smul, norm_smul]; rfl
    _ ≤ ‖z‖ * ‖(x,y)‖ + ‖z‖ * ‖(x,y)‖ :=
      add_le_add
        (mul_le_mul (Complex.abs_re_le_norm z) hx (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (Complex.abs_im_le_norm z) hy (norm_nonneg _) (norm_nonneg _))
    _ = (2 * ‖(x,y)‖) * ‖z‖ := by ring

/-- The Taylor complexification is linearly homeomorphic to the real product. -/
def coordinates : (X × X) ≃L[ℝ] TaylorComplexification X :=
  (coordinatesLinear X).toContinuousLinearEquivOfBounds 2 1
    (fun q => norm_coordinates_upper X q.1 q.2)
    (fun f => by
      simpa using norm_coordinates_lower X ((coordinatesLinear X).symm f).1
        ((coordinatesLinear X).symm f).2)

@[simp] theorem coordinates_apply (x y : X) (z : ℂ) :
    coordinates X (x,y) z = z.re • x - z.im • y := rfl

/-- In these coordinates the scalar action is the usual complex one. -/
theorem scalar_coordinates (c : ℂ) (x y : X) :
    c • coordinates X (x,y) =
      coordinates X (c.re • x - c.im • y, c.im • x + c.re • y) := by
  ext z
  change (c * z).re • x - (c * z).im • y =
    z.re • (c.re • x - c.im • y) - z.im • (c.im • x + c.re • y)
  simp only [Complex.mul_re, Complex.mul_im, sub_smul, add_smul,
    smul_sub, smul_add, smul_smul]
  module

/-- The operator norm is exactly the manuscript's supremum over rotations. -/
theorem norm_coordinates (x y : X) :
    ‖coordinates X (x,y)‖ = sSup (Set.range
      (fun θ : ℝ => ‖Real.cos θ • x - Real.sin θ • y‖)) := by
  let S : Set ℝ := Set.range (fun θ : ℝ => ‖Real.cos θ • x - Real.sin θ • y‖)
  have hbound (θ : ℝ) : ‖Real.cos θ • x - Real.sin θ • y‖ ≤
      ‖coordinates X (x,y)‖ := by
    let z : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I
    have hz : ‖z‖ = 1 := by
      simpa only [z, Complex.ofReal_cos, Complex.ofReal_sin] using
        Complex.norm_cos_add_sin_mul_I θ
    change ‖Real.cos θ • x - Real.sin θ • y‖ ≤
      ‖Complex.reCLM.smulRight x - Complex.imCLM.smulRight y‖
    have h := (Complex.reCLM.smulRight x - Complex.imCLM.smulRight y).le_opNorm z
    change ‖z.re • x - z.im • y‖ ≤ _ at h
    simpa only [z, hz, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add] using h
  have hbdd : BddAbove S := ⟨‖coordinates X (x,y)‖, by
    rintro _ ⟨θ, rfl⟩
    exact hbound θ⟩
  apply le_antisymm
  · change ‖(coordinates X (x,y) : ℂ →L[ℝ] X)‖ ≤ sSup S
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
    · exact (norm_nonneg _).trans (le_csSup hbdd (Set.mem_range_self 0))
    · intro z hz
      have hne : z ≠ 0 := by intro h; simp [h] at hz
      have hc := Complex.cos_arg hne
      have hs := Complex.sin_arg z
      rw [hz, div_one] at hc hs
      change ‖z.re • x - z.im • y‖ ≤ sSup S
      rw [← hc, ← hs]
      exact le_csSup hbdd (Set.mem_range_self z.arg)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨θ, rfl⟩
    exact hbound θ

/-- The real copy is the first-coordinate inclusion. -/
def inclusion : X →L[ℝ] TaylorComplexification X :=
  (coordinates X).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X X)

/-- Bounded projection onto the real copy. -/
def projection : TaylorComplexification X →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X X).comp (coordinates X).symm.toContinuousLinearMap

@[simp] theorem inclusion_coordinates (x : X) :
    inclusion X x = coordinates X (x, 0) := rfl

@[simp] theorem projection_coordinates (x y : X) :
    projection X (coordinates X (x,y)) = x := by
  simp [projection]

@[simp] theorem retraction (x : X) : projection X (inclusion X x) = x := by
  rw [inclusion_coordinates, projection_coordinates]

/-- The isometric real copy is a boundedly complemented real subspace. -/
theorem real_copy_complemented : (inclusion X).range.ClosedComplemented :=
  ((inclusion X).isTopCompl_range_ker_of_leftInverse (projection X)
    (retraction X)).closedComplemented

/-- The real inclusion preserves the original norm. -/
theorem inclusion_isometry (x : X) : ‖inclusion X x‖ = ‖x‖ := by
  apply le_antisymm
  · change ‖(coordinates X (x,0) : ℂ →L[ℝ] X)‖ ≤ ‖x‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro z
    change ‖z.re • x - z.im • (0 : X)‖ ≤ ‖x‖ * ‖z‖
    simp only [smul_zero, sub_zero, norm_smul, Real.norm_eq_abs]
    calc
      |z.re| * ‖x‖ ≤ ‖z‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (norm_nonneg _)
      _ = ‖x‖ * ‖z‖ := mul_comm _ _
  · change ‖x‖ ≤ ‖coordinatesLinear X (x,0)‖
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)] using
      norm_coordinates_lower X x 0

end TaylorComplexification

/-- Every real Banach space has the complete Taylor complexification. -/
theorem exists_completeComplexification : CompleteComplexification := by
  intro X _ _ _
  exact ⟨{
    carrier := TaylorComplexification X
    normedAddCommGroup := inferInstance
    complexNormedSpace := inferInstance
    realNormedSpace := inferInstance
    scalarTower := inferInstance
    completeSpace := inferInstance
    coordinates := TaylorComplexification.coordinates X
    scalar_coordinates := TaylorComplexification.scalar_coordinates X
    norm_coordinates := TaylorComplexification.norm_coordinates X
    norm_lower := TaylorComplexification.norm_coordinates_lower X
    norm_upper := TaylorComplexification.norm_coordinates_upper X
    inclusion := TaylorComplexification.inclusion X
    projection := TaylorComplexification.projection X
    inclusion_coordinates := TaylorComplexification.inclusion_coordinates X
    projection_coordinates := TaylorComplexification.projection_coordinates X
    inclusion_isometry := TaylorComplexification.inclusion_isometry X
    retraction := TaylorComplexification.retraction X
    complemented_real_copy := TaylorComplexification.real_copy_complemented X
    ap_implies := fun h =>
      hasApproximationProperty_of_retraction ℝ X (TaylorComplexification X)
        (TaylorComplexification.inclusion X) (TaylorComplexification.projection X)
        (TaylorComplexification.retraction X)
        (hasApproximationProperty_restrictScalars (TaylorComplexification X) h)
  }⟩

end
end ExpandedFA.AP
