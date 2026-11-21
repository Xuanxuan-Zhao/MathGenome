import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C10.PatchGeometryGram
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C07.LinearVolume
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

noncomputable section
open Set Function
open scoped RealInnerProductSpace Matrix
namespace D04.PatchGeometryGram

def RegularPatch : Specs.D04.C10.PatchGeometryGram.RegularPatchType :=
  @Specs.D04.C10.PatchGeometryGram.RegularPatchValue

def EmbeddedPatch : Specs.D04.C10.PatchGeometryGram.EmbeddedPatchType :=
  @Specs.D04.C10.PatchGeometryGram.EmbeddedPatchValue

def tangentPlane : Specs.D04.C10.PatchGeometryGram.tangentPlaneType :=
  @Specs.D04.C10.PatchGeometryGram.tangentPlaneValue

def columns : Specs.D04.C10.PatchGeometryGram.columnsType :=
  @Specs.D04.C10.PatchGeometryGram.columnsValue

def gramMatrix : Specs.D04.C10.PatchGeometryGram.gramMatrixType :=
  @Specs.D04.C10.PatchGeometryGram.gramMatrixValue

def gramFactor : Specs.D04.C10.PatchGeometryGram.gramFactorType :=
  @Specs.D04.C10.PatchGeometryGram.gramFactorValue

def patchGram : Specs.D04.C10.PatchGeometryGram.patchGramType :=
  @Specs.D04.C10.PatchGeometryGram.patchGramValue

def patchJacobian : Specs.D04.C10.PatchGeometryGram.patchJacobianType :=
  @Specs.D04.C10.PatchGeometryGram.patchJacobianValue

def cross : Specs.D04.C10.PatchGeometryGram.crossType :=
  @Specs.D04.C10.PatchGeometryGram.crossValue

def unitNormal : Specs.D04.C10.PatchGeometryGram.unitNormalType :=
  @Specs.D04.C10.PatchGeometryGram.unitNormalValue

def IsUnitNormal : Specs.D04.C10.PatchGeometryGram.IsUnitNormalType :=
  @Specs.D04.C10.PatchGeometryGram.IsUnitNormalValue

def imageCoordinates : Specs.D04.C10.PatchGeometryGram.imageCoordinatesType :=
  @Specs.D04.C10.PatchGeometryGram.imageCoordinatesValue

def flatVolume : Specs.D04.C10.PatchGeometryGram.flatVolumeType :=
  @Specs.D04.C10.PatchGeometryGram.flatVolumeValue


def unitCube : Specs.D04.C10.PatchGeometryGram.unitCubeType :=
  @Specs.D04.C10.PatchGeometryGram.unitCubeValue

def flatAffineVolume : Specs.D04.C10.PatchGeometryGram.flatAffineVolumeType :=
  @Specs.D04.C10.PatchGeometryGram.flatAffineVolumeValue

variable {k n : ℕ}

lemma columns_independent (A : E k →ₗ[ℝ] E n) :
    LinearIndependent ℝ (columns A) ↔ Function.Injective A := by
  change LinearIndependent ℝ (fun j => A (standardBasis k j)) ↔ _
  constructor
  · intro h
    have hi := (standardBasis k).injective_constr_of_linearIndependent (R₂ := ℝ) h
    have he : (standardBasis k).constr ℝ (fun j => A (standardBasis k j)) = A := by
      apply (standardBasis k).ext
      intro j
      simp
    rwa [he] at hi
  · intro h
    exact (standardBasis k).linearIndependent.map' A (LinearMap.ker_eq_bot.mpr h)

lemma gram_entries (A : E k →ₗ[ℝ] E n) :
    gramMatrix A = Matrix.gram ℝ (columns A) := by
  ext i j
  change ∑ l, matrixOfLinearMap A l i * matrixOfLinearMap A l j = _
  simp only [matrixOfLinearMap_apply, Matrix.gram_apply, columns,
    Specs.D04.C10.PatchGeometryGram.columnsValue,
    Specs.D04.C10.PatchGeometryGram.Model.columns]
  rw [inner_coordinates]
  rfl

lemma gram_positive (A : E k →ₗ[ℝ] E n) (hA : Function.Injective A) :
    0 < gramFactor A := by
  change 0 < Real.sqrt (gramMatrix A).det
  rw [gram_entries]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent
    ((columns_independent A).mpr hA)).det_pos

lemma gram_top (A : E n →ₗ[ℝ] E n) : gramFactor A = |A.det| := by
  change Real.sqrt ((matrixOfLinearMap A).transpose * matrixOfLinearMap A).det = _
  rw [Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  have hd : (matrixOfLinearMap A).det = A.det := by
    have h := LinearMap.det_toLin (standardBasis n) (matrixOfLinearMap A)
    change (matrixLinearEquiv n n (matrixOfLinearMap A)).det = _ at h
    simpa only [matrix_linear_roundtrip] using h.symm
  rw [hd]

lemma gram_zero (A : E 0 →ₗ[ℝ] E n) : gramFactor A = 1 := by
  change Real.sqrt (gramMatrix A).det = 1
  simp [Matrix.det_isEmpty]

lemma gram_one (A : E 1 →ₗ[ℝ] E n) : gramFactor A = ‖columns A 0‖ := by
  change Real.sqrt (gramMatrix A).det = _
  rw [gram_entries]
  simp

lemma gram_two (A : E 2 →ₗ[ℝ] E n) :
    gramFactor A = Real.sqrt (‖columns A 0‖ ^ 2 * ‖columns A 1‖ ^ 2 -
      ⟪columns A 0, columns A 1⟫ ^ 2) := by
  change Real.sqrt (gramMatrix A).det = _
  rw [gram_entries, Matrix.det_fin_two]
  simp [real_inner_comm, pow_two]

lemma image_basis_exists (A : E k →ₗ[ℝ] E n) (hA : Function.Injective A) :
    Nonempty (OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) := by
  have hd : Module.finrank ℝ (LinearMap.range A) = k := by
    rw [LinearMap.finrank_range_of_inj hA]
    exact finrank_euclideanSpace_fin
  exact ⟨(stdOrthonormalBasis ℝ (LinearMap.range A)).reindex (finCongr hd)⟩
lemma rank_iff_injective (A : E k →ₗ[ℝ] E n) :
    Module.finrank ℝ (LinearMap.range A) = k ↔ Injective A := by
  constructor
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    have hr := A.finrank_range_add_finrank_ker
    rw [h, finrank_euclideanSpace_fin] at hr
    omega
  · intro h
    rw [LinearMap.finrank_range_of_inj h, finrank_euclideanSpace_fin]

lemma regular_rank : Specs.D04.C10.PatchGeometryGram.regular_rankType := by
  intro k n U φ
  change (IsOpen U ∧ ContDiffOn ℝ 1 φ U ∧ ∀ x ∈ U, Injective (fderiv ℝ φ x)) ↔
    (IsOpen U ∧ ContDiffOn ℝ 1 φ U ∧
      ∀ x ∈ U, Module.finrank ℝ (LinearMap.range (fderiv ℝ φ x).toLinearMap) = k)
  simp only [rank_iff_injective]
  rfl

lemma gram_image_coordinates (A : E k →ₗ[ℝ] E n)
    (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) :
    gramMatrix A = (matrixOfLinearMap (imageCoordinates A b)).transpose *
      matrixOfLinearMap (imageCoordinates A b) := by
  change gramMatrix A = gramMatrix (imageCoordinates A b)
  rw [gram_entries, gram_entries]
  ext i j
  change ⟪A (standardBasis k i), A (standardBasis k j)⟫ =
    ⟪b.repr (A.rangeRestrict (standardBasis k i)),
      b.repr (A.rangeRestrict (standardBasis k j))⟫
  exact (b.repr.inner_map_map (A.rangeRestrict (standardBasis k i))
    (A.rangeRestrict (standardBasis k j))).symm

lemma gram_image_factor (A : E k →ₗ[ℝ] E n)
    (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) :
    gramFactor A = |(imageCoordinates A b).det| := by
  change Real.sqrt (gramMatrix A).det = _
  rw [gram_image_coordinates A b]
  exact gram_top (imageCoordinates A b)

lemma image_basis_independent (A : E k →ₗ[ℝ] E n)
    (b c : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) :
    |(imageCoordinates A b).det| = |(imageCoordinates A c).det| := by
  rw [← gram_image_factor, ← gram_image_factor]

lemma flat_volume_scaling : Specs.D04.C10.PatchGeometryGram.flat_volume_scalingType := by
  intro k n A b S hS
  have h := LinearVolume.linear_volume (imageCoordinates A b) S hS
  rw [← gram_image_factor A b] at h
  change JordanRegions.Jordan (b.repr '' (A.rangeRestrict '' S)) ∧
    JordanRegions.volume (b.repr '' (A.rangeRestrict '' S)) =
      gramFactor A * JordanRegions.volume S
  rw [image_image]
  exact h

lemma affine_jacobian (A : E k →ₗ[ℝ] E n) (c : E n) (x : E k) :
    patchJacobian (fun u => c + A u) x = gramFactor A := by
  have hd := (A.toContinuousLinearMap.hasFDerivAt (x := x)).const_add c
  change gramFactor (fderiv ℝ (fun u => c + A u) x).toLinearMap = _
  have hd' : HasFDerivAt (fun u => c + A u) A.toContinuousLinearMap x := by
    convert hd using 1
    funext u
    rfl
  rw [hd'.fderiv]
  rfl

lemma cross_independent (a b : E 3) :
    cross a b ≠ 0 ↔ LinearIndependent ℝ ![a, b] := by
  have hc : cross a b ≠ 0 ↔ crossProduct (WithLp.ofLp a) (WithLp.ofLp b) ≠ 0 := by
    change WithLp.toLp 2 _ ≠ 0 ↔ _
    simp only [ne_eq, WithLp.toLp_eq_zero]
  rw [hc, crossProduct_ne_zero_iff_linearIndependent]
  have h := (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.linearIndependent_iff
    (v := ![a,b]) (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ _).injective)
  have he : ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap ∘ ![a,b]) =
      ![WithLp.ofLp a, WithLp.ofLp b] := by
    ext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

lemma cross_rank (A : E 2 →ₗ[ℝ] E 3) :
    cross (columns A 0) (columns A 1) ≠ 0 ↔ Injective A := by
  rw [cross_independent, ← columns_independent]
  have he : ![columns A 0, columns A 1] = columns A := by
    ext i
    fin_cases i <;> rfl
  rw [he]

lemma cross_sq (a b : E 3) :
    ‖cross a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - ⟪a,b⟫ ^ 2 := by
  simp only [norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct,
    cross, Specs.D04.C10.PatchGeometryGram.crossValue,
    Specs.D04.C10.PatchGeometryGram.Model.cross,
    star_trivial, RCLike.re_to_real, cross_dot_cross, dotProduct_comm, pow_two]

lemma gram_cross (A : E 2 →ₗ[ℝ] E 3) :
    gramFactor A = ‖cross (columns A 0) (columns A 1)‖ := by
  rw [gram_two, ← cross_sq, Real.sqrt_sq (norm_nonneg _)]

lemma inner_cross_left (a b : E 3) : ⟪a, cross a b⟫ = 0 := by
  change ⟪a, WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))⟫ = 0
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma inner_cross_right (a b : E 3) : ⟪b, cross a b⟫ = 0 := by
  change ⟪b, WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))⟫ = 0
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

lemma cross_cross_normal (a b v : E 3) (ha : ⟪v,a⟫ = 0) (hb : ⟪v,b⟫ = 0) :
    cross (cross a b) v = 0 := by
  apply (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).injective
  change crossProduct (crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) (WithLp.ofLp v) = 0
  rw [cross_cross_eq_smul_sub_smul]
  have ha' : WithLp.ofLp a ⬝ᵥ WithLp.ofLp v = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct] using ha
  have hb' : WithLp.ofLp b ⬝ᵥ WithLp.ofLp v = 0 := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct] using hb
  rw [ha', hb', zero_smul, zero_smul, sub_self]

/-- Orthogonality to a derivative image is exactly orthogonality to its columns. -/
lemma normal_range_iff (A : E k →ₗ[ℝ] E n) (v : E n) :
    (∀ w ∈ LinearMap.range A, ⟪v,w⟫ = 0) ↔ ∀ j, ⟪v,columns A j⟫ = 0 := by
  constructor
  · intro h j
    exact h _ ⟨standardBasis k j, rfl⟩
  · intro h w hw
    obtain ⟨x, rfl⟩ := hw
    rw [← (standardBasis k).sum_repr x, map_sum, inner_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, inner_smul_right]
    change _ * ⟪v,columns A j⟫ = 0
    rw [h, mul_zero]

lemma normal_choices_linear (A : E 2 →ₗ[ℝ] E 3) (hA : Injective A) (v : E 3) :
    IsUnitNormal (LinearMap.range A) v ↔
      v = ‖cross (columns A 0) (columns A 1)‖⁻¹ • cross (columns A 0) (columns A 1) ∨
      v = -(‖cross (columns A 0) (columns A 1)‖⁻¹ • cross (columns A 0) (columns A 1)) := by
  let c := cross (columns A 0) (columns A 1)
  have hc : c ≠ 0 := (cross_rank A).mpr hA
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hN : IsUnitNormal (LinearMap.range A) (‖c‖⁻¹ • c) := by
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hcn]
    · apply (normal_range_iff A _).mpr
      intro j
      rw [inner_smul_left]
      suffices ⟪c,columns A j⟫ = 0 by simp [this]
      fin_cases j
      · exact (real_inner_comm _ _).trans (inner_cross_left _ _)
      · exact (real_inner_comm _ _).trans (inner_cross_right _ _)
  constructor
  · intro hv
    have hp := (normal_range_iff A v).mp hv.2
    have hz : cross c v = 0 := cross_cross_normal _ _ _ (hp 0) (hp 1)
    have hd : ¬ LinearIndependent ℝ ![c,v] := by
      intro hi
      exact ((cross_independent c v).mpr hi) hz
    have ht : ∃ t : ℝ, t • c = v := by
      simpa only [LinearIndependent.pair_iff' hc, not_forall, ne_eq, not_not] using hd
    obtain ⟨t, rfl⟩ := ht
    have he : |t| * ‖c‖ = 1 := by
      simpa only [norm_smul, Real.norm_eq_abs] using hv.1
    have ht' : |t| = ‖c‖⁻¹ := by
      apply (mul_right_cancel₀ hcn)
      rw [he, inv_mul_cancel₀ hcn]
    obtain ht | ht := (abs_eq (inv_nonneg.mpr (norm_nonneg c))).mp ht'
    · exact Or.inl (by rw [ht])
    · exact Or.inr (by rw [ht, neg_smul])
  · rintro (rfl | rfl)
    · exact hN
    · refine ⟨by simpa using hN.1, ?_⟩
      intro w hw
      rw [inner_neg_left, hN.2 w hw, neg_zero]

lemma normal_choices : Specs.D04.C10.PatchGeometryGram.normal_choicesType := by
  intro U φ hφ x hx v
  exact normal_choices_linear (fderiv ℝ φ x).toLinearMap (hφ.2.2 x hx) v

lemma unitCube_succ (p : ℕ) : unitCube (p+1) =
    SlicingAndMoments.between (unitCube p) (fun _ => 0) (fun _ => 1) := by
  ext z
  change (∀ i : Fin (p+1), 0 ≤ z i ∧ z i ≤ 1) ↔
    (SlicingAndMoments.basePoint z ∈ unitCube p ∧ 0 ≤ z (Fin.last p) ∧
      z (Fin.last p) ≤ 1)
  constructor
  · intro h
    exact ⟨fun i => h i.castSucc, (h (Fin.last p)).1, (h (Fin.last p)).2⟩
  · rintro ⟨hb, hl, hu⟩ i
    induction i using Fin.lastCases with
    | last => exact ⟨hl, hu⟩
    | cast j => exact hb j

lemma unitCube_volume (k : ℕ) : JordanRegions.Jordan (unitCube k) ∧
    JordanRegions.volume (unitCube k) = 1 := by
  induction k with
  | zero =>
    have h := JordanRegions.zero_dimension (unitCube 0)
    exact ⟨h.1, h.2.1.trans (by simp [unitCube,
      Specs.D04.C10.PatchGeometryGram.unitCubeValue,
      Specs.D04.C10.PatchGeometryGram.Model.unitCube])⟩
  | succ k ih =>
    rw [unitCube_succ]
    refine ⟨SlicingAndMoments.between_jordan _ ih.1 _ _
      continuousOn_const continuousOn_const (by intros; norm_num), ?_⟩
    have hv := (SlicingAndMoments.between_volume (unitCube k) (fun _ => 0) (fun _ => 1)
      ih.1 continuousOn_const continuousOn_const (by intros; norm_num)).2
    simpa only [sub_zero, JordanRegions.regionIntegral_one, ih.2] using hv

/-- Centering a translated linear image recovers the image in its tangent space. -/
lemma affine_image_center (A : E k →ₗ[ℝ] E n) (c : E n) (S : Set (E k)) :
    ((fun v : A.range => c + (v : E n)) ⁻¹' ((fun u => c + A u) '' S)) =
      A.rangeRestrict '' S := by
  ext v
  constructor
  · rintro ⟨u, hu, he⟩
    exact ⟨u, hu, Subtype.ext (add_left_cancel he)⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

lemma flat_parallelepiped (A : E k →ₗ[ℝ] E n)
    (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) (c : E n) :
    flatAffineVolume A b c ((fun u => c + A u) '' unitCube k) = gramFactor A := by
  change flatVolume A.range b ((fun v : A.range => c + (v : E n)) ⁻¹'
    ((fun u => c + A u) '' unitCube k)) = _
  rw [affine_image_center]
  have hv := (flat_volume_scaling A b (unitCube k) (unitCube_volume k).1).2
  change flatVolume A.range b (A.rangeRestrict '' unitCube k) =
    gramFactor A * JordanRegions.volume (unitCube k) at hv
  simpa only [(unitCube_volume k).2, mul_one] using hv

lemma flat_parallelepiped_independent (A : E k →ₗ[ℝ] E n)
    (b d : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) (c : E n) :
    flatAffineVolume A b c ((fun u => c + A u) '' unitCube k) =
      flatAffineVolume A d c ((fun u => c + A u) '' unitCube k) := by
  rw [flat_parallelepiped, flat_parallelepiped]


end D04.PatchGeometryGram
