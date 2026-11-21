import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Topology.Algebra.ContinuousAffineEquiv
import Mathlib.Data.Subtype
import Mathlib.MeasureTheory.Constructions.Pi
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Comparison.AmbientSimplexStokes
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Comparison.SmoothSingularComplex
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.Stokes
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Calculus.FDeriv.Affine

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators Topology
namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData SmoothSingularData LocalStokesData IntegrationCochainData
  AmbientSimplexData Set MeasureTheory Filter

/-- Concrete frames used to compute the determinant, in the ambient coordinate order. -/
private def oppositeZeroFrame (q : ℕ) : Fin (q+1) → Euclidean (q+1) :=
  Fin.cons (Pi.single 0 1) (fun i : Fin q => Pi.single i.succ 1 - Pi.single 0 1)

private def coordinateFaceFrame {q : ℕ} (i : Fin (q+1)) : Fin (q+1) → Euclidean (q+1) :=
  Fin.cons (-(Pi.single i 1)) (fun k : Fin q => Pi.single (i.succAbove k) 1)

private theorem oppositeZeroFrame_det (q : ℕ) :
    (Matrix.of (fun r k : Fin (q+1) => oppositeZeroFrame q k r)).det = 1 := by
  rw [Matrix.det_succ_column_zero]
  have hm : (Matrix.of (fun r k : Fin (q+1) => oppositeZeroFrame q k r)).submatrix
      (Fin.succ : Fin q → Fin (q+1)) (Fin.succ : Fin q → Fin (q+1)) =
      (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext i j
    simp [oppositeZeroFrame, Matrix.submatrix_apply, Pi.single_apply, Matrix.one_apply]
  simp only [oppositeZeroFrame, Fin.cons_zero, Matrix.of_apply, Pi.single_apply]
  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single 0]
  · simpa only [oppositeZeroFrame, Matrix.det_one, ite_true, Fin.val_zero, pow_zero,
      one_mul, Fin.succAbove_zero] using congrArg Matrix.det hm
  · intro i hi hne
    simp [hne]
  · simp

private theorem coordinateFaceFrame_det {q : ℕ} (i : Fin (q+1)) :
    (Matrix.of (fun r k : Fin (q+1) => coordinateFaceFrame i k r)).det = (-1 : ℝ)^(i.val+1) := by
  rw [Matrix.det_succ_column_zero]
  have hm : (Matrix.of (fun r k : Fin (q+1) => coordinateFaceFrame i k r)).submatrix
      i.succAbove (Fin.succ : Fin q → Fin (q+1)) = (1 : Matrix (Fin q) (Fin q) ℝ) := by
    ext r k
    simp [coordinateFaceFrame, Matrix.submatrix_apply, Pi.single_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · rw [hm, Matrix.det_one, mul_one]
    simp [coordinateFaceFrame, pow_succ]
  · intro k hk hne
    simp [coordinateFaceFrame, hne]
  · simp

private theorem orderedFaceFrame_zero (q : ℕ) :
    orderedFaceFrame (0 : Fin (q+2)) = oppositeZeroFrame q := by
  unfold orderedFaceFrame oppositeZeroFrame faceOutward
  funext k r
  refine Fin.cases (by rfl) (fun k => ?_) k
  simp only [Fin.cons_succ]
  refine Fin.cases ?_ (fun s => ?_) r <;>
    simp [faceAmbient, simplexBarycentric, Pi.single_apply]

private theorem orderedFaceFrame_succ {q : ℕ} (i : Fin (q+1)) :
    orderedFaceFrame i.succ = coordinateFaceFrame i := by
  unfold orderedFaceFrame coordinateFaceFrame faceOutward
  funext k r
  refine Fin.cases (by rfl) (fun k => ?_) k
  simp only [Fin.cons_succ]
  refine Fin.succAboveCases i ?_ (fun s => ?_) r <;>
    simp [faceAmbient, simplexBarycentric, Pi.single_apply]

/-- The jth face has outward-first sign (-1)^j relative to its ordered affine map. -/
theorem face_orientation :
    Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.face_orientationType := by
  intro q j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [orderedFaceFrame_zero, oppositeZeroFrame_det]
    simp
  · rw [orderedFaceFrame_succ, coordinateFaceFrame_det]
    rfl

theorem face_outward :
    Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.face_outwardType := by
  intro q j
  refine Fin.cases ?_ (fun i => ?_) j <;>
    simp [faceOutward, simplexBarycentric]

/-- The standard simplex is compact in every dimension, including zero. -/
theorem simplex_isCompact (q : ℕ) : IsCompact (simplexSet q) := by
  have hc : IsClosed (simplexSet q) := by
    have hcoord (i : Fin q) : IsClosed {x : Euclidean q | 0 ≤ x i} :=
      isClosed_le continuous_const (continuous_apply i)
    have hsum : IsClosed {x : Euclidean q | ∑ i, x i ≤ 1} :=
      isClosed_le (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const
    have heq : simplexSet q = (⋂ i : Fin q, {x : Euclidean q | 0 ≤ x i}) ∩
        {x : Euclidean q | ∑ i, x i ≤ 1} := by
      ext x
      simp [simplexSet]
    rw [heq]
    exact (isClosed_iInter hcoord).inter hsum
  apply (isCompact_Icc : IsCompact (Icc (0 : Euclidean q) 1)).of_isClosed_subset hc
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  exact le_trans (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)) hx.2

/-- Zero insertion into barycentric coordinates followed by taking the tail. -/
def insertTailLinear {q : ℕ} (j : Fin (q+2)) : Euclidean (q+1) →ₗ[ℝ] Euclidean (q+1) where
  toFun v := Fin.tail (j.insertNth (α := fun _ => ℝ) (0 : ℝ) v)
  map_add' := by
    intro v w
    funext r
    change j.insertNth (α := fun _ => ℝ) 0 (v+w) r.succ =
      j.insertNth (α := fun _ => ℝ) 0 v r.succ + j.insertNth (α := fun _ => ℝ) 0 w r.succ
    refine Fin.succAboveCases j ?_ (fun i => ?_) r.succ <;> simp
  map_smul' := by
    intro a v
    funext r
    change j.insertNth (α := fun _ => ℝ) 0 (a • v) r.succ = a * j.insertNth (α := fun _ => ℝ) 0 v r.succ
    refine Fin.succAboveCases j ?_ (fun i => ?_) r.succ <;> simp

/-- A bundled affine representative of exactly the given faceAmbient. -/
def faceAffine {q : ℕ} (j : Fin (q+2)) : Euclidean q →ᴬ[ℝ] Euclidean (q+1) where
  toAffineMap := (insertTailLinear j).toAffineMap.comp (CornerExamples.barycentricAffine q)
  cont := (SmoothSingular.faceAmbient_smooth j).continuous

@[simp] theorem faceAffine_apply {q : ℕ} (j : Fin (q+2)) (y : Euclidean q) :
    faceAffine j y = faceAmbient j y := rfl

/-- The affine derivative is independent of the base point. -/
theorem face_fderiv {q : ℕ} (j : Fin (q+2)) (y : Euclidean q) :
    fderiv ℝ (faceAmbient j) y = (faceAffine j).contLinear :=
  (faceAffine j).fderiv

theorem face_derivative :
    Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.face_derivativeType := by
  intro q j y i
  rw [face_fderiv]
  simpa [frame] using (faceAffine j).contLinear_apply_vsub (Pi.single i 1) 0

/-- Convexity is used for unique within differentiation at all corner points. -/
theorem simplex_convex (n : ℕ) : Convex ℝ (simplexSet n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · have hsum : ∑ i, (a • x + b • y) i = a * (∑ i, x i) + b * (∑ i, y i) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsum]
    calc
      a * (∑ i, x i) + b * (∑ i, y i) ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa using hab

/-- The simplex has nonempty ambient interior, even in the zero vector space. -/
theorem simplex_interior_nonempty (n : ℕ) : (interior (simplexSet n)).Nonempty := by
  let U : Set (Euclidean n) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hpos : IsOpen {x : Euclidean n | ∀ i, 0 < x i} := by
    convert isOpen_iInter_of_finite (fun i : Fin n => isOpen_lt
      (continuous_const : Continuous (fun _ : Euclidean n => (0 : ℝ))) (continuous_apply i)) using 1
    ext x
    simp
  have hU : IsOpen U := hpos.inter
    (isOpen_lt (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)
  have hsub : U ⊆ simplexSet n := fun x hx => ⟨fun i => (hx.1 i).le, hx.2.le⟩
  let x : Euclidean n := fun _ => 1 / ((n : ℝ) + 1)
  have hx : x ∈ U := by
    constructor
    · intro i
      dsimp [x]
      positivity
    · change (∑ _ : Fin n, 1 / ((n : ℝ) + 1)) < 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_one_div]
      exact (div_lt_one (by positivity)).mpr (by linarith)
  exact ⟨x, mem_interior_iff_mem_nhds.mpr (mem_of_superset (hU.mem_nhds hx) hsub)⟩

theorem simplex_uniqueDiffOn (n : ℕ) : UniqueDiffOn ℝ (simplexSet n) :=
  uniqueDiffOn_convex (simplex_convex n) (simplex_interior_nonempty n)

/-- Exterior derivative coefficients are continuous all the way to every face. -/
theorem bulk_continuousOn {q : ℕ} (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val)) :
    ContinuousOn (AmbientSimplexData.bulkCoefficient α) (simplexSet (q+1)) := by
  have h := LocalStokesResults.localExtensions_contDiffOn hα
  have hd := h.continuousOn_fderivWithin (simplex_uniqueDiffOn (q+1)) (by norm_num)
  exact (ContinuousAlternatingMap.apply ℝ (Euclidean (q+1)) ℝ (frame (q+1))).continuous.comp_continuousOn
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean (q+1)) ℝ).continuous.comp_continuousOn hd)

theorem face_continuousOn {q : ℕ} (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (j : Fin (q+2)) : ContinuousOn (faceCoefficient α j) (simplexSet q) := by
  have h := (LocalStokesResults.localExtensions_contDiffOn hα).continuousOn
  have hmap : Set.MapsTo (faceAmbient j) (simplexSet q) (simplexSet (q+1)) :=
    fun x hx => (face j ⟨x,hx⟩).property
  have hc := h.comp (SmoothSingular.faceAmbient_smooth j).continuous.continuousOn hmap
  have heq : faceCoefficient α j = fun y =>
      α (faceAmbient j y) (fun i => (faceAffine j).contLinear (frame q i)) := by
    funext y
    simp only [faceCoefficient, face_fderiv]
  rw [heq]
  exact (ContinuousAlternatingMap.apply ℝ (Euclidean (q+1)) ℝ
    (fun i => (faceAffine j).contLinear (frame q i))).continuous.comp_continuousOn hc

/-- No relative compact support hypothesis is needed on a compact simplex. -/
theorem integrability : Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.integrabilityType := by
  intro q α hα
  exact ⟨(bulk_continuousOn α hα).integrableOn_compact (simplex_isCompact (q+1)),
    fun j => (face_continuousOn α hα j).integrableOn_compact (simplex_isCompact q)⟩

section Resolved
variable {n : ℕ} {S : CornerManifold n (CornerData.Simplex n)}
  {c : Fin (n+1) → CornerChart n (CornerData.Simplex n)}
  (h : IsSimplexChartFamily S c)
include h

/-- On an affine simplex chart, deleting barycentric coordinate k makes the
remaining coordinate faces precisely the other barycentric faces. -/
theorem chart_germ_eq (k : Fin (n+1)) (p : CornerData.Simplex n)
    (hp : p ∈ (c k).2.source) (i : Fin n) :
    chartFaceGerm (c k) p i = simplexFaceGerm p (k.succAbove i) := by
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [(c k).2.open_source.mem_nhds hp] with x hx
  apply propext
  simp only [hx, true_and, h.apply k x hx, simplexOmitBarycentric, Fin.removeNth]

/-- Every active barycentric face supplies a genuine local face germ. -/
theorem simplexFaceGerm_mem (p : CornerData.Simplex n) (j : Fin (n+1))
    (hj : simplexBarycentric p.val j = 0) :
    ∃ d ∈ S.atlas, p ∈ d.2.source ∧ ∃ i : Fin n,
      i.val < d.1.val ∧ (d.2 p).val i = 0 ∧ simplexFaceGerm p j = chartFaceGerm d p i := by
  obtain ⟨k,hk⟩ := CornerExamples.exists_positive_barycentric p
  have hjk : j ≠ k := by intro he; subst j; rw [hj] at hk; exact (lt_irrefl 0 hk)
  obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hjk
  have hp : p ∈ (c k).2.source := by rw [h.source]; exact hk
  refine ⟨c k,h.mem_atlas k,hp,i,?_,?_,?_⟩
  · rw [h.constraints]
    exact i.isLt
  · rw [h.apply k p hp]
    change simplexBarycentric p.val (k.succAbove i) = 0
    rw [hi,hj]
  · rw [chart_germ_eq h k p hp i,hi]

/-- The global barycentric face is retained as the underlying subset germ. -/
def simplexFaceAt (p : CornerData.Simplex n) (j : {j : Fin (n+1) // simplexBarycentric p.val j = 0}) :
    LocalFaceGerm S p :=
  ⟨simplexFaceGerm p j.val,simplexFaceGerm_mem h p j.val j.property⟩

theorem simplexFaceAt_bijective (p : CornerData.Simplex n) :
    Function.Bijective (simplexFaceAt h p) := by
  obtain ⟨k,hk⟩ := CornerExamples.exists_positive_barycentric p
  have hp : p ∈ (c k).2.source := by rw [h.source]; exact hk
  constructor
  · intro i j hij
    have hik : i.val ≠ k := by intro he; have := i.property; rw [he] at this; linarith
    have hjk : j.val ≠ k := by intro he; have := j.property; rw [he] at this; linarith
    obtain ⟨a,ha⟩ := Fin.exists_succAbove_eq hik
    obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hjk
    have haz : ((c k).2 p).val a = 0 := by
      rw [h.apply k p hp]
      change simplexBarycentric p.val (k.succAbove a) = 0
      rw [ha]; exact i.property
    have hbz : ((c k).2 p).val b = 0 := by
      rw [h.apply k p hp]
      change simplexBarycentric p.val (k.succAbove b) = 0
      rw [hb]; exact j.property
    let a' : activeCoordinates ((c k).2 p) := ⟨a, by
      simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [h.constraints]; exact a.isLt, haz⟩⟩
    let b' : activeCoordinates ((c k).2 p) := ⟨b, by
      simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by rw [h.constraints]; exact b.isLt, hbz⟩⟩
    have he : chartFaceGerm (c k) p a = chartFaceGerm (c k) p b := by
      rw [chart_germ_eq h k p hp a,chart_germ_eq h k p hp b,ha,hb]
      exact congrArg Subtype.val hij
    have hab : a' = b' := Corners.chart_coordinate_germs_injective (c k) p hp he
    apply Subtype.ext
    rw [← ha,← hb,show a = b from congrArg Subtype.val hab]
  · intro g
    obtain ⟨i,hi⟩ := Corners.localFaceGerm_chart_surjective S (c k) (h.mem_atlas k) p hp g
    have hiz : ((c k).2 p).val i.val = 0 := (Finset.mem_filter.mp i.property).2.2
    have hj : simplexBarycentric p.val (k.succAbove i.val) = 0 := by
      rw [h.apply k p hp] at hiz
      exact hiz
    refine ⟨⟨k.succAbove i.val,hj⟩,Subtype.ext ?_⟩
    exact (chart_germ_eq h k p hp i.val).symm.trans hi.symm

end Resolved

section ResolvedGlobal
variable {q : ℕ} {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
  {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
  (h : IsSimplexChartFamily S c)

/-- Ordered face inclusion lifted to the genuine resolved boundary. -/
def simplexFaceLift (j : Fin (q+2)) (y : CornerData.Simplex q) : ResolvedFaceSpace S :=
  ⟨face j y,simplexFaceAt h (face j y) ⟨j, by
    rw [SmoothSingular.face_barycentric]
    simp⟩⟩

@[simp] theorem simplexFaceLift_base (j : Fin (q+2)) (y : CornerData.Simplex q) :
    (simplexFaceLift h j y).1 = face j y := rfl

/-- The topology remembers the germ label; continuity therefore includes corners. -/
theorem simplexFaceLift_continuous (j : Fin (q+2)) : Continuous (simplexFaceLift h j) := by
  apply continuous_generateFrom_iff.mpr
  rintro V ⟨d,hd,i,hi,U,hU,rfl⟩
  have heq : simplexFaceLift h j ⁻¹' faceSheet S d i U =
      face j ⁻¹' (U ∩ {p | simplexFaceGerm p j = chartFaceGerm d p i}) := by
    ext y
    constructor
    · rintro ⟨hyU,_,_,hg⟩
      exact ⟨hyU,hg⟩
    · rintro ⟨hyU,hg⟩
      have he := (Filter.Germ.coe_eq.mp hg).eq_of_nhds
      have hz : simplexBarycentric (face j y).val j = 0 := by
        rw [SmoothSingular.face_barycentric]; simp
      have hm : face j y ∈ d.2.source ∧ (d.2 (face j y)).val i = 0 := he ▸ hz
      exact ⟨hyU,hm.1,hm.2,hg⟩
  rw [heq]
  exact (hU.inter (Corners.isOpen_germ_eq
    (fun p : CornerData.Simplex (q+1) => simplexBarycentric p.val j = 0)
    (fun p => p ∈ d.2.source ∧ (d.2 p).val i = 0))).preimage
      (SmoothSingular.face_continuous j)

/-- A point on face j is recovered by deleting its zero barycentric coordinate. -/
def facePreimage (p : CornerData.Simplex (q+1)) (j : Fin (q+2))
    (hj : simplexBarycentric p.val j = 0) : CornerData.Simplex q :=
  fromBarycentric (j.removeNth (simplexBarycentric p.val))
    (fun i => CornerExamples.barycentric_nonneg.mp p.property (j.succAbove i))
    (by
      have hs := Fin.add_sum_removeNth j (simplexBarycentric p.val)
      rw [hj,zero_add,CornerExamples.sum_barycentric] at hs
      exact hs)

@[simp] theorem face_facePreimage (p : CornerData.Simplex (q+1)) (j : Fin (q+2))
    (hj : simplexBarycentric p.val j = 0) : face j (facePreimage p j hj) = p := by
  apply Subtype.ext
  have hb : simplexBarycentric (facePreimage p j hj).val = j.removeNth (simplexBarycentric p.val) := by
    change simplexBarycentric (Fin.tail (j.removeNth (simplexBarycentric p.val))) = _
    exact CornerExamples.barycentric_tail_of_sum _ (by
      have hs := Fin.add_sum_removeNth j (simplexBarycentric p.val)
      rw [hj,zero_add,CornerExamples.sum_barycentric] at hs
      exact hs)
  have hh : simplexBarycentric (face j (facePreimage p j hj)).val = simplexBarycentric p.val := by
    rw [SmoothSingular.face_barycentric,hb,← hj,Fin.insertNth_removeNth]
    simp
  exact congrArg Fin.tail hh

@[simp] theorem facePreimage_face (j : Fin (q+2)) (y : CornerData.Simplex q)
    (hj : simplexBarycentric (face j y).val j = 0) : facePreimage (face j y) j hj = y := by
  apply Subtype.ext
  change Fin.tail (j.removeNth (simplexBarycentric (face j y).val)) = y.val
  rw [SmoothSingular.face_barycentric,Fin.removeNth_insertNth]
  rfl

/-- No two face labels are identified above a common base point. -/
theorem simplexFaceLift_bijective :
    Function.Bijective (fun z : Fin (q+2) × CornerData.Simplex q => simplexFaceLift h z.1 z.2) := by
  let A := Σ p : CornerData.Simplex (q+1), {j : Fin (q+2) // simplexBarycentric p.val j = 0}
  let E : A ≃ ResolvedFaceSpace S := Equiv.sigmaCongrRight
    (fun p => Equiv.ofBijective (simplexFaceAt h p) (simplexFaceAt_bijective h p))
  let F : (Fin (q+2) × CornerData.Simplex q) ≃ A := {
    toFun z := ⟨face z.1 z.2,⟨z.1,by rw [SmoothSingular.face_barycentric]; simp⟩⟩
    invFun z := (z.2.val,facePreimage z.1 z.2.val z.2.property)
    left_inv := by rintro ⟨j,y⟩; simp
    right_inv := by
      rintro ⟨p,j,hj⟩
      apply Sigma.ext (face_facePreimage p j hj)
      exact (Subtype.heq_iff_coe_eq (by intro r; simp only [face_facePreimage])).mpr rfl }
  exact (F.trans E).bijective

end ResolvedGlobal

/-- A continuous bijection from the finite union of compact faces identifies
all resolved sheets, including every point above a face intersection. -/
theorem resolved_faces : Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.resolved_facesType := by
  intro q S c h
  let : CompactSpace (CornerData.Simplex q) := isCompact_iff_compactSpace.mp (simplex_isCompact q)
  let : T2Space (ResolvedFaceSpace S) := Corners.resolved_face_hausdorff S
  let e : (Fin (q+2) × CornerData.Simplex q) ≃ ResolvedFaceSpace S :=
    Equiv.ofBijective (fun z => simplexFaceLift h z.1 z.2) (simplexFaceLift_bijective h)
  have he : Continuous e := continuous_prod_of_discrete_left.mpr
    (fun j => simplexFaceLift_continuous h j)
  let E := e.toHomeomorphOfContinuousClosed he he.isClosedMap
  exact ⟨E,fun _ _ => rfl,fun _ _ => rfl⟩

/-- Zero-dimensional volume gives unsigned evaluation on a parametrized endpoint. -/
theorem endpoint_integral (α : CoordinateForm 1 0) (j : Fin 2) :
    (∫ y in simplexSet 0, faceCoefficient α j y) =
      α (faceAmbient j 0) (fun i : Fin 0 => Fin.elim0 i) := by
  rw [CornerExamples.simplexSet_zero, MeasureTheory.setIntegral_univ]
  have heq : faceCoefficient α j =
      fun _ : Euclidean 0 => α (faceAmbient j 0) (fun i : Fin 0 => Fin.elim0 i) := by
    funext y
    have hy : y = 0 := Subsingleton.elim _ _
    subst y
    unfold faceCoefficient
    congr 1
    funext i
    exact Fin.elim0 i
  rw [heq, integral_const]
  have hv : (volume : Measure (Euclidean 0)) univ = 1 :=
    Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
  simp [Measure.real, hv]

/-- The ordered interval has right-positive and left-negative endpoints. -/
theorem endpoint_sum (α : CoordinateForm 1 0) :
    (∑ j : Fin 2, (-1 : ℝ)^j.val * ∫ y in simplexSet 0, faceCoefficient α j y) =
      α 1 (fun i : Fin 0 => Fin.elim0 i) - α 0 (fun i : Fin 0 => Fin.elim0 i) := by
  simp only [endpoint_integral]
  rw [Fin.sum_univ_two]
  have hright : faceAmbient (0 : Fin 2) (0 : Euclidean 0) = 1 := by
    ext i
    fin_cases i
    simp [faceAmbient, SmoothSingularData.faceAmbient, simplexBarycentric, Fin.tail]
  have hleft : faceAmbient (1 : Fin 2) (0 : Euclidean 0) = 0 := by
    ext i
    fin_cases i
    simp [faceAmbient, SmoothSingularData.faceAmbient, simplexBarycentric, Fin.tail]
  rw [hright,hleft]
  norm_num [sub_eq_add_neg]

/-- The chart-family interface is instantiated by the upstream simplex geometry
and its actual source coordinate orientation. -/
theorem source_geometry (n : ℕ) :
    ∃ (S : CornerManifold n (CornerData.Simplex n))
      (c : Fin (n+1) → CornerChart n (CornerData.Simplex n)),
      IsSimplexChartFamily S c ∧
      ∃ o : CornerOrientationData.CornerOrientation S,
        ∀ j (hc : c j ∈ S.atlas) (p : (c j).2.source),
          OrientationData.signValue (o.sign (c j) hc p) = (-1 : ℝ)^j.val := by
  obtain ⟨S,c,ha,hc,_,_,_,o,ho,_⟩ := CornerFaceOrientations.simplex_source_orientation n
  refine ⟨S,c,?_,o,ho⟩
  exact ⟨ha,fun j => (hc j).1,fun j => (hc j).2.1,fun j => (hc j).2.2.1,
    fun j => (hc j).2.2.2.1,fun j => (hc j).2.2.2.2.1,fun j => (hc j).2.2.2.2.2⟩

/-- A coordinate-compatible corner realization turns the supplied corner Stokes
theorem into the ambient formula. The realization is constructed below. -/
theorem stokes_of_corner_integral_bridge
    (hbridge : Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.corner_integral_bridgeType) :
    Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.stokesType := by
  intro q α hα
  obtain ⟨S,c,o,_,_,ω,hω,hcompact,_,T,b,I,J,hb,hI,hJ,hcompare⟩ := hbridge q α hα
  obtain ⟨η,β,hd,_,hr,_,hst⟩ :=
    CornerStokesResults.stokes S o T b hb I J hI hJ ω hω hcompact
  obtain ⟨hbulk,hface⟩ := hcompare η β hd hr
  exact ⟨(integrability q α hα).1,(integrability q α hα).2,
    hbulk.symm.trans (hst.trans hface)⟩

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples Set

/-- Continuous affine representative of the exact barycentric deletion chart. -/
def omitAffine {n : ℕ} (j : Fin (n+1)) : Euclidean n →ᴬ[ℝ] Euclidean n where
  toAffineMap := (omitBarycentricAffineEquiv j).toAffineMap
  cont := (contDiff_omitBarycentric j).continuous

/-- Continuous affine representative of the exact inverse barycentric chart. -/
def restoreAffine {n : ℕ} (j : Fin (n+1)) : Euclidean n →ᴬ[ℝ] Euclidean n where
  toAffineMap := (omitBarycentricAffineEquiv j).symm.toAffineMap
  cont := by
    change Continuous (fun x => (omitBarycentricAffineEquiv j).symm x)
    simpa only [omitBarycentricAffineEquiv_symm_apply] using
      (contDiff_restoreBarycentric j).continuous

@[simp] theorem omitAffine_apply {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    omitAffine j x = simplexOmitBarycentric j x := rfl

@[simp] theorem restoreAffine_apply {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    restoreAffine j x = simplexRestoreBarycentric j x :=
  omitBarycentricAffineEquiv_symm_apply j x

theorem omit_fderiv {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    fderiv ℝ (simplexOmitBarycentric j) x = (omitAffine j).contLinear :=
  (omitAffine j).fderiv

theorem restore_fderiv {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    fderiv ℝ (simplexRestoreBarycentric j) x = (restoreAffine j).contLinear := by
  have he : (restoreAffine j : Euclidean n → Euclidean n) = simplexRestoreBarycentric j :=
    funext (restoreAffine_apply j)
  rw [← he]
  exact (restoreAffine j).fderiv

theorem omit_contLinear_det {n : ℕ} (j : Fin (n+1)) :
    LinearMap.det (omitAffine j).contLinear.toLinearMap = (-1 : ℝ)^j.val :=
  CornerFaceOrientations.omitBarycentricAffineEquiv_det j

theorem restore_contLinear_det {n : ℕ} (j : Fin (n+1)) :
    LinearMap.det (restoreAffine j).contLinear.toLinearMap = (-1 : ℝ)^j.val := by
  change LinearMap.det (omitBarycentricAffineEquiv j).linear.symm.toLinearMap = _
  rw [LinearEquiv.det_coe_symm, CornerFaceOrientations.omitBarycentricAffineEquiv_det]
  rw [← inv_pow]
  norm_num

theorem abs_omit_fderiv_det {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    |LinearMap.det (fderiv ℝ (simplexOmitBarycentric j) x).toLinearMap| = 1 := by
  rw [omit_fderiv, omit_contLinear_det, abs_pow]
  simp

theorem abs_restore_fderiv_det {n : ℕ} (j : Fin (n+1)) (x : Euclidean n) :
    |LinearMap.det (fderiv ℝ (simplexRestoreBarycentric j) x).toLinearMap| = 1 := by
  rw [restore_fderiv, restore_contLinear_det, abs_pow]
  simp

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ContinuousAlternatingMap Set

/-- Affine pullback commutes with exterior differentiation within arbitrary sets,
assuming only the differentiability needed for the chain rule. -/
theorem affine_extDerivWithin_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (f : E →ᴬ[ℝ] F) (ω : F → F [⋀^Fin q]→L[ℝ] ℝ)
    {s : Set E} {t : Set F} {x : E}
    (hω : DifferentiableWithinAt ℝ ω t (f x))
    (hs : UniqueDiffWithinAt ℝ s x) (hst : MapsTo f s t) :
    extDerivWithin (fun z => (ω (f z)).compContinuousLinearMap f.contLinear) s x =
      (extDerivWithin ω t (f x)).compContinuousLinearMap f.contLinear := by
  change alternatizeUncurryFin (fderivWithin ℝ
    ((compContinuousLinearMapCLM f.contLinear) ∘ (ω ∘ f)) s x) = _
  rw [fderiv_comp_fderivWithin x
    (compContinuousLinearMapCLM f.contLinear).differentiableAt
    (hω.comp x f.differentiableWithinAt hst) hs,
    ContinuousLinearMap.fderiv,
    fderivWithin_comp x hω f.differentiableWithinAt hst hs,
    f.fderivWithin hs, extDerivWithin]
  ext v
  simp [alternatizeUncurryFin_apply, Fin.removeNth, Function.comp_def]
  rfl

/-- The unrestricted affine pullback identity. -/
theorem affine_extDeriv_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (f : E →ᴬ[ℝ] F) (ω : F → F [⋀^Fin q]→L[ℝ] ℝ)
    {x : E} (hω : DifferentiableAt ℝ ω (f x)) :
    extDeriv (fun z => (ω (f z)).compContinuousLinearMap f.contLinear) x =
      (extDeriv ω (f x)).compContinuousLinearMap f.contLinear := by
  simpa using affine_extDerivWithin_pullback f ω hω.differentiableWithinAt
    uniqueDiffWithinAt_univ (mapsTo_univ _ _)

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerStokesData Set Filter
universe u

/-- A local formula on a chart gives an ambient extension after shrinking its domain. -/
theorem chartField_extension_of_eventual {n : ℕ} {M : Type u} [TopologicalSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : CornerChart n M) {s : ℕ∞} (f : c.2.source → F) (p : c.2.source)
    (U : Set (Euclidean n)) (hU : IsOpen U) (hpU : (c.2 p.val).val ∈ U)
    (G : Euclidean n → F) (hG : ContDiffOn ℝ s G U)
    (he : ∀ᶠ y in 𝓝 p.val, ∀ hy : y ∈ c.2.source, G (c.2 y).val = f ⟨y,hy⟩) :
    HasLocalContDiffExtensionAt s (fun q : c.2.source => (c.2 q.val).val) f p := by
  obtain ⟨W,hWsub,hWo,hpW⟩ := mem_nhds_iff.mp he
  let Q := c.2.symm ⁻¹' W ∩ c.2.target
  have hQo : IsOpen Q := by
    simpa [Q,inter_comm] using c.2.symm.isOpen_inter_preimage hWo
  obtain ⟨V,hVo,hVQ⟩ := isOpen_induced_iff.mp hQo
  have hpQ : c.2 p.val ∈ Q :=
    ⟨by simpa [c.2.left_inv p.property] using hpW,c.2.map_source p.property⟩
  have hpV : (c.2 p.val).val ∈ V := by
    change c.2 p.val ∈ Subtype.val ⁻¹' V
    rwa [hVQ]
  refine ⟨U ∩ V,hU.inter hVo,⟨hpU,hpV⟩,G,hG.mono inter_subset_left,?_⟩
  intro q hq
  have hqQ : c.2 q.val ∈ Q := by rw [← hVQ]; exact hq.2
  have hqW : q.val ∈ W := by
    have hh := hqQ.1
    change c.2.symm (c.2 q.val) ∈ W at hh
    rwa [c.2.left_inv q.property] at hh
  exact hWsub hqW q.property

/-- C¹ ambient extension regularity can be checked on a covering subatlas. -/
theorem regularForm_of_subatlas {n r : ℕ} {M : Type u} [TopologicalSpace M]
    (S : CornerManifold n M) (A : Set (CornerChart n M)) (hsub : A ⊆ S.atlas)
    (hcover : ∀ p : M, ∃ d ∈ A, p ∈ d.2.source) (ω : Form S r)
    (hω : ∀ d (hd : d ∈ A), LocallyContDiffAlong 1
      (fun p : d.2.source => (d.2 p.val).val) (ω.field d (hsub hd))) :
    IsRegularForm 1 ω := by
  intro c hc p
  obtain ⟨d,hd,hpd⟩ := hcover p.val
  let compat := S.maximal.1.2 c hc d (hsub hd)
  have hpt : c.2 p.val ∈ (c.2.symm.trans d.2).source := by
    refine ⟨c.2.map_source p.property,?_⟩
    change c.2.symm (c.2 p.val) ∈ d.2.source
    rwa [c.2.left_inv p.property]
  obtain ⟨W,hW,hpW,Hmap,hHmap,hHagree⟩ := compat.1 ⟨c.2 p.val,hpt⟩
  let H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p.val) :=
    ⟨W,hW,hpW,Hmap,hHmap,fun z hz hzW => hHagree ⟨z,hz⟩ hzW⟩
  obtain ⟨V,hV,hpV,G,hG,hGe⟩ := hω d hd ⟨p.val,hpd⟩
  let U := H.domain ∩ H.map ⁻¹' V
  have hU : IsOpen U := H.smooth.continuousOn.isOpen_inter_preimage H.isOpen_domain hV
  have hHp : H.map (c.2 p.val).val = (d.2 p.val).val := by
    have he := H.agrees (c.2 p.val) ⟨c.2.map_source p.property,by
      change c.2.symm (c.2 p.val) ∈ d.2.source
      rwa [c.2.left_inv p.property]⟩ H.mem_domain
    simpa only [OpenPartialHomeomorph.trans_apply,c.2.left_inv p.property] using he
  have hpU : (c.2 p.val).val ∈ U := ⟨H.mem_domain,by simpa [hHp] using hpV⟩
  let F : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ :=
    fun x => (G (H.map x)).compContinuousLinearMap (fderiv ℝ H.map x)
  have hcomp : ContDiffOn ℝ 1 (fun x => G (H.map x)) U :=
    hG.comp ((H.smooth.of_le (by simp)).mono inter_subset_left) (fun _ hx => hx.2)
  have hD : ContDiffOn ℝ 1 (fderiv ℝ H.map) U :=
    (H.smooth.fderiv_of_isOpen H.isOpen_domain (by simp)).mono inter_subset_left
  have hF : ContDiffOn ℝ 1 F U := by
    exact ((ContinuousAlternatingMap.cpolynomialOn_compContinuousLinearMapCLM
      (𝕜 := ℝ) (E := Euclidean n) (F := Euclidean n) (G := ℝ) (ι := Fin r) univ).contDiffOn.comp
        hD (fun _ _ => mem_univ _)).clm_apply hcomp
  apply chartField_extension_of_eventual c (ω.field c hc) p U hU hpU F hF
  have hcoord : ContinuousAt (fun y : M => (c.2 y).val) p.val :=
    continuous_subtype_val.continuousAt.comp (c.2.continuousAt p.property)
  filter_upwards [c.2.open_source.mem_nhds p.property,d.2.open_source.mem_nhds hpd,
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with y hyc hyd hyU
  intro hy
  have hyt : c.2 y ∈ (c.2.symm.trans d.2).source := by
    refine ⟨c.2.map_source hyc,?_⟩
    change c.2.symm (c.2 y) ∈ d.2.source
    rwa [c.2.left_inv hyc]
  have hHy : H.map (c.2 y).val = (d.2 y).val := by
    simpa only [OpenPartialHomeomorph.trans_apply,c.2.left_inv hyc]
      using H.agrees (c.2 y) hyt hyU.1
  have hydV : (d.2 y).val ∈ V := by rw [← hHy]; exact hyU.2
  let H' : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 y) :=
    ⟨H.domain,H.isOpen_domain,hyU.1,H.map,H.smooth,H.agrees⟩
  dsimp only [F]
  rw [hHy,hGe ⟨y,hyd⟩ hydV]
  exact (ω.compatible c d hc (hsub hd) y hy hyd H').symm
end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientFormBridge
open ModelData CornerData CornerStokesData CornerFaceOrientations CornerFormDescent
  CornerExamples AmbientSimplexData LocalStokesData Set Filter

private theorem simplexChartFamily_injective {n : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c) : Function.Injective c := by
  intro i j hij
  let v : Euclidean n := Fin.tail (Pi.single i (1 : ℝ) : Euclidean (n+1))
  have hb : simplexBarycentric v = Pi.single i 1 :=
    barycentric_tail_of_sum _ (by simp)
  have hv : v ∈ simplexSet n := barycentric_nonneg.mpr (by
    intro k
    rw [hb]
    simp only [Pi.single_apply]
    split_ifs <;> norm_num)
  let p : Simplex n := ⟨v,hv⟩
  have hpi : p ∈ (c i).2.source := by
    rw [hc.source]
    change 0 < simplexBarycentric v i
    rw [hb]
    simp
  have hpj : p ∈ (c j).2.source := hij ▸ hpi
  rw [hc.source] at hpj
  change 0 < simplexBarycentric v j at hpj
  rw [hb] at hpj
  by_contra hne
  simp [Pi.single_apply, Ne.symm hne] at hpj

private theorem simplex_restore_at {n : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c) (j : Fin (n+1)) (p : (c j).2.source) :
    simplexRestoreBarycentric j ((c j).2 p.val).val = p.val.val := by
  rw [hc.apply j p.val p.property, restore_omit]

/-- The explicit affine coordinate transition is an ambient extension of the
actual transition of the given generating simplex charts. -/
private def simplex_transition_extension {n : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c) (i j : Fin (n+1))
    (p : Simplex n) (hp : p ∈ (c i).2.source) :
    OrthantExtension ((c i).2.symm.trans (c j).2).source
      ((c i).2.symm.trans (c j).2) ((c i).2 p) where
  domain := univ
  isOpen_domain := isOpen_univ
  mem_domain := mem_univ _
  map := simplexOmitBarycentric j ∘ simplexRestoreBarycentric i
  smooth := ((contDiff_omitBarycentric j).comp (contDiff_restoreBarycentric i)).contDiffOn
  agrees := by
    intro z hz _
    change z ∈ (c i).2.target ∧ (c i).2.symm z ∈ (c j).2.source at hz
    rw [OpenPartialHomeomorph.trans_apply, hc.apply j _ hz.2, hc.symm_apply i _ hz.1]
    rfl

/-- The actual derivative pullback law for ambient alternating forms on the
generating affine simplex charts; all smooth extensions have this derivative. -/
theorem simplex_chart_fields_compatible {n r : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c)
    (α : CoordinateForm n r) (i j : Fin (n+1))
    (p : Simplex n) (hp : p ∈ (c i).2.source) (hq : p ∈ (c j).2.source)
    (H : OrthantExtension ((c i).2.symm.trans (c j).2).source
      ((c i).2.symm.trans (c j).2) ((c i).2 p)) :
    (α p.val).compContinuousLinearMap
      (fderiv ℝ (simplexRestoreBarycentric i) ((c i).2 p).val) =
    ((α p.val).compContinuousLinearMap
      (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p).val)).compContinuousLinearMap
        (fderiv ℝ H.map ((c i).2 p).val) := by
  let G := simplex_transition_extension S c hc i j p hp
  have hx : (c i).2 p ∈ ((c i).2.symm.trans (c j).2).source := by
    refine ⟨(c i).2.map_source hp, ?_⟩
    change (c i).2.symm ((c i).2 p) ∈ (c j).2.source
    rwa [(c i).2.left_inv hp]
  have hder := orthant_extension_derivative_unique _ _ hx H G
  have hG : G.map ((c i).2 p).val = ((c j).2 p).val := by
    simpa only [OpenPartialHomeomorph.trans_apply, (c i).2.left_inv hp] using
      G.agrees ((c i).2 p) hx G.mem_domain
  have hcomp : simplexRestoreBarycentric j ∘ G.map = simplexRestoreBarycentric i := by
    funext x
    exact restore_omit j _
  have hDj := (contDiff_restoreBarycentric j).differentiable (by simp)
  have hDG := ((contDiff_omitBarycentric j).comp
    (contDiff_restoreBarycentric i)).differentiable (by simp)
  have hchain : (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p).val).comp
      (fderiv ℝ H.map ((c i).2 p).val) =
      fderiv ℝ (simplexRestoreBarycentric i) ((c i).2 p).val := by
    rw [hder, ← hG, ← fderiv_comp (f := G.map) _ (hDj _) (hDG _), hcomp]
  ext v
  change α p.val (fun k => fderiv ℝ (simplexRestoreBarycentric i) ((c i).2 p).val (v k)) =
    α p.val (fun k => fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p).val
      (fderiv ℝ H.map ((c i).2 p).val (v k)))
  congr 1
  funext k
  exact congrArg (fun L : Euclidean n →L[ℝ] Euclidean n => L (v k)) hchain.symm

/-- Local C¹ extension in a generating affine chart. -/
theorem simplex_chart_field_regular {n r : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c)
    (α : CoordinateForm n r)
    (hα : LocallyContDiffOn 1 (simplexSet n) (fun x => α x.val))
    (j : Fin (n+1)) :
    LocallyContDiffAlong 1 (fun p : (c j).2.source => ((c j).2 p.val).val)
      (fun p => (α p.val.val).compContinuousLinearMap
        (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p.val).val)) := by
  intro p
  obtain ⟨U,hU,hpU,F,hF,heF⟩ := hα p.val
  let R := simplexRestoreBarycentric j
  let V := R ⁻¹' U
  have hV : IsOpen V := hU.preimage (contDiff_restoreBarycentric j).continuous
  have hpV : ((c j).2 p.val).val ∈ V := by
    change R ((c j).2 p.val).val ∈ U
    simpa only [R, simplex_restore_at S c hc j p] using hpU
  let P : Euclidean n → (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ := fun x =>
    (F (R x)).compContinuousLinearMap (fderiv ℝ R x)
  have hFR : ContDiffOn ℝ 1 (fun x => F (R x)) V :=
    hF.comp ((contDiff_restoreBarycentric j).of_le (by simp)).contDiffOn (fun _ hx => hx)
  have hDR : ContDiff ℝ 1 (fderiv ℝ R) :=
    (contDiff_restoreBarycentric j).fderiv_right (by simp)
  have hPoly : ContDiff ℝ 1 (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclidean n →L[ℝ] Euclidean n) →
        ((Euclidean n) [⋀^Fin r]→L[ℝ] ℝ) →L[ℝ]
          ((Euclidean n) [⋀^Fin r]→L[ℝ] ℝ)) := by
    rw [← contDiffOn_univ]
    exact (ContinuousAlternatingMap.cpolynomialOn_compContinuousLinearMapCLM univ).contDiffOn
  have hP : ContDiffOn ℝ 1 P V :=
    (hPoly.comp hDR).contDiffOn.clm_apply hFR
  refine ⟨V,hV,hpV,P,hP,?_⟩
  intro q hqV
  dsimp only [P]
  have hR : R ((c j).2 q.val).val = q.val.val := simplex_restore_at S c hc j q
  have hqU : q.val.val ∈ U := by simpa only [V, mem_preimage, hR] using hqV
  rw [hR, heF q.val hqU]

/-- Continuous generating chart fields descend to a genuine form on the fixed
maximal simplex atlas, with the required exact affine pullback formula. -/
theorem ambient_form_exists {n r : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c)
    (α : CoordinateForm n r)
    (hα : LocallyContDiffOn 1 (simplexSet n) (fun x => α x.val)) :
    ∃ ω : Form S r, (∀ d hd, Continuous (ω.field d hd)) ∧
      ∀ j (hj : c j ∈ S.atlas) (p : (c j).2.source),
        ω.field (c j) hj p = (α p.val.val).compContinuousLinearMap
          (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p.val).val) := by
  let A := range c
  have hsub : A ⊆ S.atlas := by rintro _ ⟨j,rfl⟩; exact hc.mem_atlas j
  have hcover : ∀ p : Simplex n, ∃ d ∈ A, p ∈ d.2.source := by
    intro p
    obtain ⟨j,hj⟩ := exists_positive_barycentric p
    refine ⟨c j, mem_range_self _, ?_⟩
    simpa only [hc.source, mem_setOf_eq] using hj
  let index : ∀ d : CornerChart n (Simplex n), d ∈ A → Fin (n+1) :=
    fun d hd => Classical.choose hd
  have hindex : ∀ d (hd : d ∈ A), c (index d hd) = d :=
    fun d hd => Classical.choose_spec hd
  let F : ∀ d : CornerChart n (Simplex n), d ∈ A → d.2.source →
      (Euclidean n) [⋀^Fin r]→L[ℝ] ℝ := fun d hd p =>
    (α p.val.val).compContinuousLinearMap
      (fderiv ℝ (simplexRestoreBarycentric (index d hd)) (d.2 p.val).val)
  have hFcont : ∀ d hd, Continuous (F d hd) := by
    intro d hd
    rcases hd with ⟨j,rfl⟩
    have hEq : index (c j) (mem_range_self j) = j :=
      simplexChartFamily_injective S c hc (hindex _ _)
    dsimp only [F]
    simp only [hEq]
    have hreg := simplex_chart_field_regular S c hc α hα j
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨U,hU,hpU,G,hG,heG⟩ := hreg p
    have hcoord : ContinuousAt (fun q : (c j).2.source => ((c j).2 q.val).val) p :=
      (continuous_subtype_val.continuousAt.comp ((c j).2.continuousAt p.property)).comp
        continuousAt_subtype_val
    apply ((hG.continuousOn.continuousAt (hU.mem_nhds hpU)).comp
      (f := fun q : (c j).2.source => ((c j).2 q.val).val) hcoord).congr
    filter_upwards [hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq
    exact heG q hq
  have hFcomp : ∀ (d e : CornerChart n (Simplex n)) (hd : d ∈ A) (he : e ∈ A)
      (p : Simplex n) (hp : p ∈ d.2.source) (hq : p ∈ e.2.source)
      (H : OrthantExtension (d.2.symm.trans e.2).source (d.2.symm.trans e.2) (d.2 p)),
      F d hd ⟨p,hp⟩ = (F e he ⟨p,hq⟩).compContinuousLinearMap
        (fderiv ℝ H.map (d.2 p).val) := by
    intro d e hd he p hp hq H
    rcases hd with ⟨i,rfl⟩
    rcases he with ⟨j,rfl⟩
    have hi : index (c i) (mem_range_self i) = i :=
      simplexChartFamily_injective S c hc (hindex _ _)
    have hj : index (c j) (mem_range_self j) = j :=
      simplexChartFamily_injective S c hc (hindex _ _)
    simpa only [F,hi,hj] using simplex_chart_fields_compatible S c hc α i j p hp hq H
  obtain ⟨ω,hωcont,hωF⟩ := form_extension S A hsub hcover F hFcont hFcomp
  refine ⟨ω,hωcont,?_⟩
  intro j hj p
  have hEq : index (c j) (mem_range_self j) = j :=
    simplexChartFamily_injective S c hc (hindex _ _)
  simpa only [F,hEq] using hωF (c j) (mem_range_self j) p

end SmoothManifolds.AmbientFormBridge

namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerStokesData CornerExamples AmbientSimplexData
  LocalStokesData AmbientFormBridge Set Filter

/-- Every locally C¹ ambient alternating form on the compact simplex realizes a
regular genuine corner form, with exactly the actual affine pullback fields. -/
theorem ambient_regular_form_exists {n r : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c)
    (α : CoordinateForm n r)
    (hα : LocallyContDiffOn 1 (simplexSet n) (fun x => α x.val)) :
    ∃ ω : Form S r, IsRegularForm 1 ω ∧ IsCompact (formSupport ω) ∧
      ∀ j (hj : c j ∈ S.atlas) (p : (c j).2.source),
        ω.field (c j) hj p = (α p.val.val).compContinuousLinearMap
          (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p.val).val) := by
  obtain ⟨ω,_hωcont,hω⟩ := ambient_form_exists S c hc α hα
  have hsub : range c ⊆ S.atlas := by rintro _ ⟨j,rfl⟩; exact hc.mem_atlas j
  have hcover : ∀ p : Simplex n, ∃ d ∈ range c, p ∈ d.2.source := by
    intro p
    obtain ⟨j,hj⟩ := exists_positive_barycentric p
    refine ⟨c j, mem_range_self _, ?_⟩
    simpa only [hc.source, mem_ofPred_eq] using hj
  have hregular : IsRegularForm 1 ω := by
    apply regularForm_of_subatlas S (range c) hsub hcover ω
    rintro d ⟨j,rfl⟩
    have heq : ω.field (c j) (hsub (mem_range_self j)) =
        (fun p => (α p.val.val).compContinuousLinearMap
          (fderiv ℝ (simplexRestoreBarycentric j) ((c j).2 p.val).val)) :=
      funext (hω j _)
    rw [heq]
    exact simplex_chart_field_regular S c hc α hα j
  letI : CompactSpace (Simplex n) := isCompact_iff_compactSpace.mp (simplex_isCompact n)
  exact ⟨ω,hregular,isClosed_closure.isCompact,hω⟩

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples SmoothSingularData Set

/-- Restricting an affine simplex chart to one sheet gives the corresponding
ordered face chart, in the exact ambient coordinates. -/
theorem restore_insert_face {q : ℕ} (k : Fin (q+2)) (i : Fin (q+1)) (y : Euclidean q) :
    simplexRestoreBarycentric k (i.insertNth (0 : ℝ) y) =
      faceAmbient (k.succAbove i) (simplexRestoreBarycentric (i.predAbove k) y) := by
  apply (Function.LeftInverse.injective (restore_omit k))
  rw [omit_restore]
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp [simplexOmitBarycentric,Fin.removeNth,SmoothSingular.barycentric_faceAmbient]
  · change y = i.removeNth (k.removeNth (simplexBarycentric
      (faceAmbient (k.succAbove i) (simplexRestoreBarycentric (i.predAbove k) y))))
    rw [Fin.removeNth_removeNth_eq_swap,SmoothSingular.barycentric_faceAmbient,
      Fin.removeNth_insertNth,barycentric_restore,Fin.removeNth_insertNth]

theorem face_chart_sign {q : ℕ} (k : Fin (q+2)) (i : Fin (q+1)) :
    (-1 : ℝ)^k.val * (-1 : ℝ)^(i.val+1) =
      (-1 : ℝ)^(k.succAbove i).val * (-1 : ℝ)^(i.predAbove k).val := by
  rw [← pow_add,← pow_add]
  by_cases h : i.castSucc < k
  · rw [Fin.succAbove_of_castSucc_lt _ _ h,Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc,Fin.val_pred]
    have hi : i.val < k.val := h
    have he : k.val + (i.val+1) = i.val + (k.val-1) + 2 := by omega
    rw [he,pow_add]
    norm_num
  · have hki : k ≤ i.castSucc := le_of_not_gt h
    rw [Fin.succAbove_of_le_castSucc _ _ hki,Fin.predAbove_of_le_castSucc _ _ hki]
    congr 1
    simp
    omega
end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples AmbientSimplexData CornerStokesData
  CornerOrientationData OrientationData LocalStokesData CornerStokesResults
  Set MeasureTheory Filter

theorem restore_mem_simplex {n : ℕ} (j : Fin (n+1)) {y : Euclidean n}
    (hy : y ∈ simplexSet n) : simplexRestoreBarycentric j y ∈ simplexSet n := by
  apply barycentric_nonneg.mpr
  intro i
  rw [barycentric_restore]
  refine Fin.succAboveCases j ?_ (fun r => ?_) i
  · simpa using sub_nonneg.mpr hy.2
  · simpa using hy.1 r

theorem omit_mem_simplex {n : ℕ} (j : Fin (n+1)) {x : Euclidean n}
    (hx : x ∈ simplexSet n) : simplexOmitBarycentric j x ∈ simplexSet n := by
  have hb := barycentric_nonneg.mp hx
  refine ⟨fun i => hb (j.succAbove i), ?_⟩
  have hsum := Fin.add_sum_removeNth j (simplexBarycentric x)
  rw [sum_barycentric] at hsum
  change simplexBarycentric x j + ∑ i, simplexOmitBarycentric j x i = 1 at hsum
  linarith [hb j]

theorem restore_image_simplex {n : ℕ} (j : Fin (n+1)) :
    simplexRestoreBarycentric j '' simplexSet n = simplexSet n := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact restore_mem_simplex j hy
  · intro x hx
    exact ⟨simplexOmitBarycentric j x, omit_mem_simplex j hx, restore_omit j x⟩

theorem omit_image_simplex {n : ℕ} (j : Fin (n+1)) :
    simplexOmitBarycentric j '' simplexSet n = simplexSet n := by
  apply Set.Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact omit_mem_simplex j hy
  · intro x hx
    exact ⟨simplexRestoreBarycentric j x, restore_mem_simplex j hx, omit_restore j x⟩

/-- The exact affine restoration is a volume-preserving substitution on the
closed simplex. No regularity or support condition on the integrand occurs. -/
theorem integral_simplex_restore {n : ℕ} (j : Fin (n+1))
    (hclosed : IsClosed (simplexSet n))
    (hdet : ∀ x : Euclidean n, |(fderiv ℝ (simplexRestoreBarycentric j) x).det| = 1)
    (f : Euclidean n → ℝ) :
    (∫ x in simplexSet n, f x) =
      ∫ y in simplexSet n, f (simplexRestoreBarycentric j y) := by
  have hD : ∀ y ∈ simplexSet n,
      HasFDerivWithinAt (simplexRestoreBarycentric j)
        (fderiv ℝ (simplexRestoreBarycentric j) y) (simplexSet n) y := by
    intro y hy
    exact ((contDiff_restoreBarycentric j).differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt
  have hinj : Set.InjOn (simplexRestoreBarycentric j) (simplexSet n) :=
    (Function.LeftInverse.injective (omit_restore j)).injOn
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    hclosed.measurableSet hD hinj f
  rw [restore_image_simplex] at h
  simpa only [hdet,one_smul] using h

/-- A supported coordinate top form whose signed generating-chart coefficients
are f has its prescribed ambient integral. -/
theorem chartIntegral_eq_simplex_of_signed_field {n : ℕ}
    {S : CornerManifold n (CornerData.Simplex n)}
    {c : Fin (n+1) → CornerChart n (CornerData.Simplex n)}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (η : Form S n) (f : Euclidean n → ℝ)
    (hfield : ∀ k (p : (c k).2.source),
      signValue (o.sign (c k) (h.mem_atlas k) p) *
        η.field (c k) (h.mem_atlas k) p (frame n) = f p.val.val)
    (j : Fin (n+1)) (hsupport : formSupport η ⊆ (c j).2.source)
    (hclosed : IsClosed (simplexSet n))
    (hdet : ∀ x : Euclidean n, |(fderiv ℝ (simplexRestoreBarycentric j) x).det| = 1) :
    chartIntegral o (c j) (h.mem_atlas j) η = ∫ x in simplexSet n, f x := by
  have hzero (p : CornerData.Simplex n) (hp : p ∉ (c j).2.source) : f p.val = 0 := by
    obtain ⟨k,hk⟩ := exists_positive_barycentric p
    have hpk : p ∈ (c k).2.source := by rw [h.source]; exact hk
    have hz : η.field (c k) (h.mem_atlas k) ⟨p,hpk⟩ = 0 := by
      by_contra hn
      exact hp (hsupport (subset_closure ⟨c k,h.mem_atlas k,hpk,hn⟩))
    simpa [hz] using
      (hfield k ⟨p,hpk⟩).symm
  have hinside (y : Euclidean n) (hy : y ∈ simplexSet n) :
      chartCoefficient o (c j) (h.mem_atlas j) η y = f (simplexRestoreBarycentric j y) := by
    let p : CornerData.Simplex n := ⟨simplexRestoreBarycentric j y,restore_mem_simplex j hy⟩
    by_cases hp : p ∈ (c j).2.source
    · have hcoord : ((c j).2 p).val = y := by
        rw [h.apply j p hp]
        exact omit_restore j y
      calc
        chartCoefficient o (c j) (h.mem_atlas j) η y =
            chartCoefficient o (c j) (h.mem_atlas j) η ((c j).2 p).val := congrArg _ hcoord.symm
        _ = signValue (o.sign (c j) (h.mem_atlas j) ⟨p,hp⟩) *
              η.field (c j) (h.mem_atlas j) ⟨p,hp⟩ (frame n) :=
            chartCoefficient_at o (c j) (h.mem_atlas j) η p hp
        _ = f p.val := hfield j ⟨p,hp⟩
        _ = f (simplexRestoreBarycentric j y) := rfl
    · have hm : y ∈ orthantSet n (c j).1 := by
        rw [h.constraints]
        exact fun i _ => hy.1 i
      have ht : ¬(⟨y,hm⟩ : Orthant n (c j).1) ∈ (c j).2.target := by
        intro ht
        have hsum : ∑ r, y r < 1 := by simpa only [h.target,Set.mem_ofPred_eq] using ht
        apply hp
        rw [h.source]
        change 0 < simplexBarycentric (simplexRestoreBarycentric j y) j
        rw [barycentric_restore]
        simpa using sub_pos.mpr hsum
      rw [show f (simplexRestoreBarycentric j y) = 0 from hzero p hp]
      simp only [chartCoefficient,hm,dite_true,ht,dite_false]
  have houtside (y : Euclidean n) (hy : y ∉ simplexSet n) :
      chartCoefficient o (c j) (h.mem_atlas j) η y = 0 := by
    by_cases hm : y ∈ orthantSet n (c j).1
    · have ht : ¬(⟨y,hm⟩ : Orthant n (c j).1) ∈ (c j).2.target := by
        intro ht
        apply hy
        have hm' : ∀ i, 0 ≤ y i := by
          intro i
          exact hm i (by rw [h.constraints]; exact i.isLt)
        exact ⟨hm',le_of_lt (by simpa only [h.target,Set.mem_ofPred_eq] using ht)⟩
      simp only [chartCoefficient,hm,dite_true,ht,dite_false]
    · simp only [chartCoefficient,hm,dite_false]
  unfold chartIntegral
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero houtside]
  rw [integral_simplex_restore j hclosed hdet f]
  exact setIntegral_congr_fun hclosed.measurableSet hinside

/-- A continuous weight on the closed simplex is extended by zero in ambient
space. Only the restriction, never this artificial extension, is differentiated. -/
def simplexWeight {n : ℕ} (ρ : CornerData.Simplex n → ℝ) (f : Euclidean n → ℝ)
    (x : Euclidean n) : ℝ :=
  if hx : x ∈ simplexSet n then ρ ⟨x,hx⟩ * f x else 0

theorem simplexWeight_continuousOn {n : ℕ} {ρ : CornerData.Simplex n → ℝ}
    (hρ : Continuous ρ) {f : Euclidean n → ℝ} (hf : ContinuousOn f (simplexSet n)) :
    ContinuousOn (simplexWeight ρ f) (simplexSet n) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hcf : Continuous (fun p : CornerData.Simplex n => f p.val) :=
    continuousOn_iff_continuous_domRestrict.mp hf
  change Continuous (fun p : CornerData.Simplex n => simplexWeight ρ f p.val)
  convert hρ.mul hcf using 1
  funext p
  simp [simplexWeight,p.property]

/-- Canonical corner integration equals the ambient simplex integral whenever
the signed top coefficients agree on the actual affine generating charts. -/
theorem integral_eq_simplex_of_signed_field {n : ℕ}
    {S : CornerManifold n (CornerData.Simplex n)}
    {c : Fin (n+1) → CornerChart n (CornerData.Simplex n)}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (η : CompactTopForm S) (f : Euclidean n → ℝ)
    (hfield : ∀ k (p : (c k).2.source),
      signValue (o.sign (c k) (h.mem_atlas k) p) *
        η.form.field (c k) (h.mem_atlas k) p (frame n) = f p.val.val)
    (hcompact : IsCompact (simplexSet n))
    (hf : ContinuousOn f (simplexSet n))
    (hdet : ∀ (j : Fin (n+1)) (x : Euclidean n),
      |(fderiv ℝ (simplexRestoreBarycentric j) x).det| = 1) :
    I η = ∫ x in simplexSet n, f x := by
  letI : CompactSpace (CornerData.Simplex n) := isCompact_iff_compactSpace.mp hcompact
  have hcover : (Set.univ : Set (CornerData.Simplex n)) ⊆ ⋃ j : Fin (n+1), (c j).2.source := by
    intro p _
    obtain ⟨j,hj⟩ := exists_positive_barycentric p
    exact mem_iUnion.mpr ⟨j,by rw [h.source]; exact hj⟩
  obtain ⟨ρ,hsub,hsum,_,_⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun j : Fin (n+1) => (c j).2.open_source) isCompact_univ hcover
  let ζ (j : Fin (n+1)) := weightTopForm (fun p => ρ j p) (ρ j).continuous η
  have hζsupport (j : Fin (n+1)) : formSupport (ζ j).form ⊆ (c j).2.source := by
    intro p hp
    exact hsub j (weightForm_support (fun p => ρ j p) η.form hp).1
  have hζfield (j k : Fin (n+1)) (p : (c k).2.source) :
      signValue (o.sign (c k) (h.mem_atlas k) p) *
        (ζ j).form.field (c k) (h.mem_atlas k) p (frame n) =
        simplexWeight (fun p => ρ j p) f p.val.val := by
    change signValue (o.sign (c k) (h.mem_atlas k) p) *
      (ρ j p.val • η.form.field (c k) (h.mem_atlas k) p) (frame n) = _
    rw [ContinuousAlternatingMap.smul_apply]
    simp only [simplexWeight,p.val.property,dite_true,smul_eq_mul]
    rw [←hfield k p]
    ring
  have hζintegral (j : Fin (n+1)) : I (ζ j) =
      ∫ x in simplexSet n, simplexWeight (fun p => ρ j p) f x := by
    rw [hI.2.2 (c j) (h.mem_atlas j) (ζ j) (hζsupport j)]
    exact chartIntegral_eq_simplex_of_signed_field h o (ζ j).form _
      (hζfield j) j (hζsupport j) hcompact.isClosed (hdet j)
  have hsumfield : ∀ e he p, η.form.field e he p =
      ∑ j ∈ (Finset.univ : Finset (Fin (n+1))), (ζ j).form.field e he p := by
    intro e he p
    change η.form.field e he p = ∑ j ∈ (Finset.univ : Finset (Fin (n+1))),
      ρ j p.val • η.form.field e he p
    rw [←Finset.sum_smul]
    have hs : ∑ j : Fin (n+1), ρ j p.val = 1 := by
      simpa only [Finset.sum_apply,Pi.one_apply] using hsum (Set.mem_univ p.val)
    rw [hs,one_smul]
  calc
    I η = ∑ j ∈ (Finset.univ : Finset (Fin (n+1))), I (ζ j) :=
      integral_sum I hI Finset.univ ζ η hsumfield
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (n+1))),
        ∫ x in simplexSet n, simplexWeight (fun p => ρ j p) f x := by
      apply Finset.sum_congr rfl
      intro j _
      exact hζintegral j
    _ = ∫ x in simplexSet n, ∑ j ∈ (Finset.univ : Finset (Fin (n+1))),
          simplexWeight (fun p => ρ j p) f x := by
      symm
      apply integral_finsetSum
      intro j _
      exact (simplexWeight_continuousOn (ρ j).continuous hf).integrableOn_compact hcompact
    _ = ∫ x in simplexSet n, f x := by
      apply setIntegral_congr_fun hcompact.isClosed.measurableSet
      intro x hx
      simp only [simplexWeight,hx,dite_true]
      have hs : ∑ j : Fin (n+1), ρ j ⟨x,hx⟩ = 1 := by
        simpa only [Finset.sum_apply,Pi.one_apply] using hsum (Set.mem_univ (⟨x,hx⟩ : CornerData.Simplex n))
      rw [←Finset.sum_mul,hs,one_mul]


end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples CornerStokesData AmbientSimplexData
  LocalStokesData Set Filter
open scoped Topology

/-- The supplied corner derivative of an ambient form is the genuine ambient
exterior derivative in every affine simplex chart, including at corners. -/
theorem simplex_derivative_field {n r : ℕ}
    {S : CornerManifold n (CornerData.Simplex n)}
    {c : Fin (n+1) → CornerChart n (CornerData.Simplex n)}
    (hchart : IsSimplexChartFamily S c)
    (α : CoordinateForm n r) (hα : DifferentiableOn ℝ α (simplexSet n))
    (ω : Form S r)
    (hω : ∀ j (p : (c j).2.source),
      ω.field (c j) (hchart.mem_atlas j) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine j).contLinear)
    (η : Form S (r+1)) (hη : HasDerivative ω η)
    (j : Fin (n+1)) (p : (c j).2.source) :
    η.field (c j) (hchart.mem_atlas j) p =
      (extDerivWithin α (simplexSet n) p.val.val).compContinuousLinearMap
        (restoreAffine j).contLinear := by
  let d := c j
  let hc := hchart.mem_atlas j
  let f := restoreAffine j
  have hmem : (d.2 p.val).val ∈ Subtype.val '' d.2.target :=
    ⟨d.2 p.val,d.2.map_source p.property,rfl⟩
  have hmap : MapsTo f (Subtype.val '' d.2.target) (simplexSet n) := by
    rintro x ⟨y,hy,rfl⟩
    change restoreAffine j y.val ∈ simplexSet n
    rw [restoreAffine_apply, ← hchart.symm_apply j y hy]
    exact (d.2.symm y).property
  have heq : ambientForm ω d hc =ᶠ[𝓝[Subtype.val '' d.2.target] (d.2 p.val).val]
      (fun z => (α (f z)).compContinuousLinearMap f.contLinear) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨y,hy,rfl⟩ := hx
    simp only [ambientForm,y.property,dite_true,hy]
    rw [hω j]
    congr 1
    simpa only [f, restoreAffine_apply] using congrArg α (hchart.symm_apply j y hy)
  have hrestore : f (d.2 p.val).val = p.val.val := by
    change restoreAffine j ((c j).2 p.val).val = p.val.val
    rw [restoreAffine_apply, hchart.apply j p.val p.property, restore_omit]
  rw [hη (c j) (hchart.mem_atlas j) p, heq.extDerivWithin_eq_of_mem hmem]
  rw [affine_extDerivWithin_pullback f α (hα _ (hmap hmem))
    (CornerStokesResults.uniqueDiffOn_orthantDomain d.2.open_target _ hmem) hmap, hrestore]


/-- The source orientation and affine chart Jacobian recover the ambient bulk
coefficient pointwise. -/
theorem simplex_derivative_signed_field {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (hchart : IsSimplexChartFamily S c)
    (o : CornerOrientationData.CornerOrientation S)
    (hsign : ∀ j (p : (c j).2.source),
      OrientationData.signValue (o.sign (c j) (hchart.mem_atlas j) p) = (-1 : ℝ)^j.val)
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (ω : Form S q)
    (hω : ∀ j (p : (c j).2.source),
      ω.field (c j) (hchart.mem_atlas j) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine j).contLinear)
    (η : Form S (q+1)) (hη : HasDerivative ω η)
    (j : Fin (q+2)) (p : (c j).2.source) :
    OrientationData.signValue (o.sign (c j) (hchart.mem_atlas j) p) *
      η.field (c j) (hchart.mem_atlas j) p (frame (q+1)) =
      AmbientSimplexData.bulkCoefficient α p.val.val := by
  rw [simplex_derivative_field hchart α
    ((LocalStokesResults.localExtensions_contDiffOn hα).differentiableOn (by norm_num))
    ω hω η hη j p]
  change OrientationData.signValue (o.sign (c j) (hchart.mem_atlas j) p) *
    (extDerivWithin α (simplexSet (q+1)) p.val.val)
      (fun i => (restoreAffine j).contLinear (frame (q+1) i)) = _
  rw [CornerStokesResults.evaluate_frame_comp, hsign]
  change (-1 : ℝ)^j.val *
    (AmbientSimplexData.bulkCoefficient α p.val.val *
      LinearMap.det (restoreAffine j).contLinear.toLinearMap) = _
  rw [restore_contLinear_det]
  calc
    (-1 : ℝ)^j.val * (AmbientSimplexData.bulkCoefficient α p.val.val * (-1)^j.val) =
        AmbientSimplexData.bulkCoefficient α p.val.val * ((-1)^j.val * (-1)^j.val) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerStokesData AmbientSimplexData LocalStokesData Set MeasureTheory
/-- Corner integration of the derivative is the actual ambient bulk integral. -/
theorem simplex_bulk_integral {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (hchart : IsSimplexChartFamily S c)
    (o : CornerOrientationData.CornerOrientation S)
    (hsign : ∀ j (p : (c j).2.source),
      OrientationData.signValue (o.sign (c j) (hchart.mem_atlas j) p) = (-1 : ℝ)^j.val)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (ω : Form S q)
    (hω : ∀ j (p : (c j).2.source),
      ω.field (c j) (hchart.mem_atlas j) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine j).contLinear)
    (η : CompactTopForm S) (hη : HasDerivative ω η.form) :
    I η = ∫ x in simplexSet (q+1), AmbientSimplexData.bulkCoefficient α x := by
  exact integral_eq_simplex_of_signed_field hchart o I hI η
    (AmbientSimplexData.bulkCoefficient α)
    (simplex_derivative_signed_field hchart o hsign α hα ω hω η.form hη)
    (simplex_isCompact (q+1)) (bulk_continuousOn α hα) abs_restore_fderiv_det

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples AmbientSimplexData CornerStokesData
  CornerOrientationData OrientationData LocalStokesData CornerStokesResults SmoothSingularData
  Set MeasureTheory Filter

/-- An ambient representative of scalar weighting on the full simplex. -/
def simplexWeightedForm {n r : ℕ} (ρ : CornerData.Simplex n → ℝ)
    (α : CoordinateForm n r) : CoordinateForm n r :=
  fun x => if hx : x ∈ simplexSet n then ρ ⟨x,hx⟩ • α x else 0

/-- Scalar multiplication of the ambient form induces exactly multiplication
by the pulled-back scalar on each genuine ordered affine face. -/
theorem faceCoefficient_simplexWeightedForm {q : ℕ}
    (ρ : CornerData.Simplex (q+1) → ℝ) (α : CoordinateForm (q+1) q)
    (j : Fin (q+2)) (y : Euclidean q) (hy : y ∈ simplexSet q) :
    faceCoefficient (simplexWeightedForm ρ α) j y =
      ρ (face j ⟨y,hy⟩) * faceCoefficient α j y := by
  have hp : faceAmbient j y ∈ simplexSet (q+1) := (face j ⟨y,hy⟩).property
  simp only [faceCoefficient,simplexWeightedForm,hp,dite_true,
    ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  rfl

theorem faceCoefficient_weight_continuousOn {q : ℕ}
    (ρ : CornerData.Simplex (q+1) → ℝ) (hρ : Continuous ρ)
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (j : Fin (q+2)) :
    ContinuousOn (faceCoefficient (simplexWeightedForm ρ α) j) (simplexSet q) := by
  apply ContinuousOn.congr
    (simplexWeight_continuousOn (hρ.comp (SmoothSingular.face_continuous j))
      (face_continuousOn α hα j))
  intro y hy
  simp only [simplexWeight,hy,dite_true,faceCoefficient_simplexWeightedForm ρ α j y hy,Function.comp_apply]

theorem faceCoefficient_weight_integrableOn {q : ℕ}
    (ρ : CornerData.Simplex (q+1) → ℝ) (hρ : Continuous ρ)
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (j : Fin (q+2)) :
    IntegrableOn (faceCoefficient (simplexWeightedForm ρ α) j) (simplexSet q) :=
  (faceCoefficient_weight_continuousOn ρ hρ α hα j).integrableOn_compact (simplex_isCompact q)

/-- A localization subordinate to c_k vanishes on the face opposite vertex k. -/
theorem weight_zero_on_own_face {q : ℕ}
    (ρ : CornerData.Simplex (q+1) → ℝ) (k : Fin (q+2))
    (hsource : sectionSupport ρ ⊆ {p | 0 < simplexBarycentric p.val k})
    (y : CornerData.Simplex q) : ρ (face k y) = 0 := by
  by_contra hn
  have hp := hsource (subset_closure hn)
  change 0 < simplexBarycentric (face k y).val k at hp
  rw [SmoothSingular.face_barycentric] at hp
  simpa only [Fin.insertNth_apply_same,lt_self_iff_false] using hp

/-- Deleting an identically zero entry leaves the finite sum unchanged. -/
theorem sum_succAbove_eq_of_eq_zero {n : ℕ} (f : Fin (n+1) → ℝ)
    (k : Fin (n+1)) (hk : f k = 0) :
    (∑ i : Fin n, f (k.succAbove i)) = ∑ j : Fin (n+1), f j := by
  rw [Fin.sum_univ_succAbove f k,hk,zero_add]

/-- The sum of the chartwise ordered boundary integrals collapses to each
ordered face exactly once. The missing diagonal term vanishes by subordination. -/
theorem weighted_ordered_face_sum {q : ℕ}
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (ρ : Fin (q+2) → CornerData.Simplex (q+1) → ℝ)
    (hρ : ∀ k, Continuous (ρ k))
    (hsource : ∀ k, sectionSupport (ρ k) ⊆ {p | 0 < simplexBarycentric p.val k})
    (hsum : ∀ p : CornerData.Simplex (q+1), ∑ k, ρ k p = 1) :
    (∑ k : Fin (q+2), ∑ i : Fin (q+1), (-1 : ℝ)^(k.succAbove i).val *
      ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm (ρ k) α) (k.succAbove i) y) =
    ∑ j : Fin (q+2), (-1 : ℝ)^j.val * ∫ y in simplexSet q, faceCoefficient α j y := by
  have hdiag (k : Fin (q+2)) :
      (-1 : ℝ)^k.val * ∫ y in simplexSet q,
        faceCoefficient (simplexWeightedForm (ρ k) α) k y = 0 := by
    rw [show (∫ y in simplexSet q,
      faceCoefficient (simplexWeightedForm (ρ k) α) k y) = 0 from ?_,mul_zero]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    rw [faceCoefficient_simplexWeightedForm _ _ _ _ hy,
      weight_zero_on_own_face (ρ k) k (hsource k) ⟨y,hy⟩,zero_mul]
  have hsumint (j : Fin (q+2)) :
      (∑ k : Fin (q+2), ∫ y in simplexSet q,
        faceCoefficient (simplexWeightedForm (ρ k) α) j y) =
      ∫ y in simplexSet q, faceCoefficient α j y := by
    rw [← integral_finsetSum Finset.univ (fun k _ =>
      faceCoefficient_weight_integrableOn (ρ k) (hρ k) α hα j)]
    apply setIntegral_congr_fun (simplex_isCompact q).isClosed.measurableSet
    intro y hy
    simp only [faceCoefficient_simplexWeightedForm _ _ _ _ hy]
    rw [← Finset.sum_mul,hsum (face j ⟨y,hy⟩),one_mul]
  calc
    _ = ∑ k : Fin (q+2), ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
        ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm (ρ k) α) j y := by
      apply Finset.sum_congr rfl
      intro k _
      exact sum_succAbove_eq_of_eq_zero (fun j : Fin (q+2) =>
        (-1 : ℝ)^j.val * ∫ y in simplexSet q,
          faceCoefficient (simplexWeightedForm (ρ k) α) j y) k (hdiag k)
    _ = ∑ j : Fin (q+2), ∑ k : Fin (q+2), (-1 : ℝ)^j.val *
        ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm (ρ k) α) j y :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [←Finset.mul_sum,hsumint j]

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples CornerOrientationData SmoothSingularData Set LocalStokesData
/-- Tangent maps of the actual face/chart coordinate factorization. -/
theorem restore_face_linear {q : ℕ} (k : Fin (q+2)) (i : Fin (q+1))
    (v : Euclidean q) :
    (restoreAffine k).contLinear (faceInsertion i v) =
      (faceAffine (k.succAbove i)).contLinear ((restoreAffine (i.predAbove k)).contLinear v) := by
  calc
    (restoreAffine k).contLinear (faceInsertion i v) =
        simplexRestoreBarycentric k (i.insertNth (0 : ℝ) v) -
          simplexRestoreBarycentric k (i.insertNth (0 : ℝ) (0 : Euclidean q)) := by
      have hd := (restoreAffine k).contLinear_apply_vsub (faceInsertion i v) (faceInsertion i 0)
      rw [(faceInsertion i).map_zero, vsub_eq_sub, sub_zero] at hd
      have hz : i.insertNth (0 : ℝ) (0 : Euclidean q) = (0 : Euclidean (q+1)) :=
        (faceInsertion i).map_zero
      simpa only [faceInsertion, LinearMap.coe_mk, AddHom.coe_mk, restoreAffine_apply,
        vsub_eq_sub, hz] using hd
    _ = faceAmbient (k.succAbove i) (simplexRestoreBarycentric (i.predAbove k) v) -
        faceAmbient (k.succAbove i) (simplexRestoreBarycentric (i.predAbove k) 0) := by
      rw [restore_insert_face k i v,restore_insert_face k i 0]
    _ = (faceAffine (k.succAbove i)).contLinear
        (simplexRestoreBarycentric (i.predAbove k) v -
          simplexRestoreBarycentric (i.predAbove k) 0) := by
      simpa only [vsub_eq_sub, faceAffine_apply] using
        ((faceAffine (k.succAbove i)).contLinear_apply_vsub
          (simplexRestoreBarycentric (i.predAbove k) v)
          (simplexRestoreBarycentric (i.predAbove k) 0)).symm
    _ = _ := by
      congr 1
      simpa only [sub_zero, vsub_eq_sub, restoreAffine_apply] using
        ((restoreAffine (i.predAbove k)).contLinear_apply_vsub v 0).symm

/-- The local outward coefficient in a simplex chart is the ordered face
coefficient with its alternating simplex sign. -/
theorem simplex_local_face_coefficient {q : ℕ} (k : Fin (q+2)) (i : Fin (q+1))
    (A : (Euclidean (q+1)) [⋀^Fin q]→L[ℝ] ℝ) :
    (-1 : ℝ)^k.val * (-1 : ℝ)^(i.val+1) *
        A (fun r => (restoreAffine k).contLinear (i.removeNth (frame (q+1)) r)) =
      (-1 : ℝ)^(k.succAbove i).val *
        (A.compContinuousLinearMap (faceAffine (k.succAbove i)).contLinear) (frame q) := by
  have heq : (fun r => (restoreAffine k).contLinear (i.removeNth (frame (q+1)) r)) =
      (fun r => (faceAffine (k.succAbove i)).contLinear
        ((restoreAffine (i.predAbove k)).contLinear (frame q r))) := by
    rw [← CornerStokesResults.faceInsertion_frame]
    funext r
    exact restore_face_linear k i (frame q r)
  rw [heq]
  change (-1 : ℝ)^k.val * (-1 : ℝ)^(i.val+1) *
    (A.compContinuousLinearMap (faceAffine (k.succAbove i)).contLinear)
      (fun r => (restoreAffine (i.predAbove k)).contLinear (frame q r)) = _
  rw [CornerStokesResults.evaluate_frame_comp]
  change (-1 : ℝ)^k.val * (-1 : ℝ)^(i.val+1) *
    ((A.compContinuousLinearMap (faceAffine (k.succAbove i)).contLinear) (frame q) *
      LinearMap.det (restoreAffine (i.predAbove k)).contLinear.toLinearMap) = _
  rw [restore_contLinear_det, face_chart_sign]
  calc
    ((-1 : ℝ)^(k.succAbove i).val * (-1 : ℝ)^(i.predAbove k).val) *
        ((A.compContinuousLinearMap (faceAffine (k.succAbove i)).contLinear) (frame q) *
          (-1 : ℝ)^(i.predAbove k).val) =
      (-1 : ℝ)^(k.succAbove i).val *
        (A.compContinuousLinearMap (faceAffine (k.succAbove i)).contLinear) (frame q) *
          ((-1 : ℝ)^(i.predAbove k).val * (-1 : ℝ)^(i.predAbove k).val) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

/-- Exact local coefficient for an ambient form along its ordered affine face. -/
theorem simplex_local_face_coefficient_alpha {q : ℕ}
    (α : CoordinateForm (q+1) q) (k : Fin (q+2)) (i : Fin (q+1)) (y : Euclidean q) :
    (-1 : ℝ)^k.val * (-1 : ℝ)^(i.val+1) *
        α (simplexRestoreBarycentric k (i.insertNth (0 : ℝ) y))
          (fun r => (restoreAffine k).contLinear (i.removeNth (frame (q+1)) r)) =
      (-1 : ℝ)^(k.succAbove i).val *
        AmbientSimplexData.faceCoefficient α (k.succAbove i)
          (simplexRestoreBarycentric (i.predAbove k) y) := by
  rw [restore_insert_face]
  simpa only [AmbientSimplexData.faceCoefficient, face_fderiv,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using
    simplex_local_face_coefficient k i
      (α (faceAmbient (k.succAbove i) (simplexRestoreBarycentric (i.predAbove k) y)))

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerStokesData CornerStokesResults
  CornerOrientationData AmbientSimplexData LocalStokesData Set MeasureTheory Filter

/-- The complete resolved integral of a form supported over a generating
simplex chart is exactly the sum of all its local orthant face terms. -/
theorem resolved_integral_over_simplex_chart {q : ℕ}
    (S : CornerManifold (q+1) (Simplex (q+1)))
    (c : Fin (q+2) → CornerChart (q+1) (Simplex (q+1)))
    (hc : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (T : CornerManifold q (ResolvedFaceSpace S)) (b : CornerOrientation T)
    (hb : IsResolvedOrientation o b)
    (J : CompactTopForm T → ℝ) (hJ : IsIntegral b J)
    (ω : Form S q) (β : CompactTopForm T)
    (hβ : CornerStokesData.IsFaceRestriction ω β.form) (k : Fin (q+2))
    (hβsupport : formSupport β.form ⊆ faceProjection S ⁻¹' (c k).2.source) :
    J β = ∑ i : Fin (q+1), ∫ y in orthantFaceSet (c k).1 i,
      orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (hc.mem_atlas k)) i y := by
  have hi (i : Fin (q+1)) : i.val < (c k).1.val := by
    rw [hc.constraints]
    exact i.isLt
  let q0 : ResolvedFaceSpace S := simplexFaceLift hc 0 ⟨0,by simp [simplexSet]⟩
  choose e he hek hes hecoord using
    (fun i : Fin (q+1) => exists_resolved_chart_in_canonical_atlas S T hb.1 q0
      (c k) (hc.mem_atlas k) i (hi i))
  have hresolved := resolved_integral_over_chart S (c k) (hc.mem_atlas k)
    T b J hJ (c k).2.source Subset.rfl β hβsupport
    (fun i => e i.val) (fun i => he i.val) (fun i => hes i.val)
  rw [hresolved]
  have hterm (i : {i : Fin (q+1) // i.val < (c k).1.val}) :
      chartIntegral b (e i.val) (he i.val) β.form =
        ∫ y in orthantFaceSet (c k).1 i.val,
          orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (hc.mem_atlas k)) i.val y :=
    chartIntegral_face_eq_orthant o b hb ω β.form hβ (c k) (hc.mem_atlas k)
      i.val (hi i.val) (e i.val) (he i.val) (hek i.val) (hes i.val) (hecoord i.val)
  simp_rw [hterm]
  simpa only [hi,Finset.filter_true_of_mem] using
    (Finset.sum_subtype (Finset.univ : Finset (Fin (q+1)))
      (p := fun i => i.val < (c k).1.val) (by intro i; simp [hi i]) (fun i =>
        ∫ y in orthantFaceSet (c k).1 i,
          orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (hc.mem_atlas k)) i y)).symm


/-- A continuous partition over the actual finite generating affine charts.
The sum is one everywhere on the compact full simplex. -/
theorem simplex_chart_partition {n : ℕ}
    (S : CornerManifold n (Simplex n))
    (c : Fin (n+1) → CornerChart n (Simplex n))
    (hc : IsSimplexChartFamily S c) :
    ∃ ρ : Fin (n+1) → Simplex n → ℝ,
      (∀ k, Continuous (ρ k)) ∧
      (∀ k, sectionSupport (ρ k) ⊆ (c k).2.source) ∧
      ∀ p : Simplex n, ∑ k, ρ k p = 1 := by
  letI : CompactSpace (Simplex n) := isCompact_iff_compactSpace.mp (simplex_isCompact n)
  have hcov : (univ : Set (Simplex n)) ⊆ ⋃ k, (c k).2.source := by
    intro p _
    obtain ⟨k,hk⟩ := CornerExamples.exists_positive_barycentric p
    refine mem_iUnion.mpr ⟨k,?_⟩
    simpa only [hc.source,mem_ofPred_eq] using hk
  obtain ⟨ρ,hρsupport,hρsum,_,_⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun k => (c k).2.open_source) isCompact_univ hcov
  refine ⟨fun k p => ρ k p,fun k => (ρ k).continuous,hρsupport,?_⟩
  intro p
  simpa only [Finset.sum_apply,Pi.one_apply] using hρsum (mem_univ p)

/-- The genuine resolved boundary integral is a finite sum of the local orthant
face integrals of bulk-chart localizations. No face-orientation certificate or
Stokes equality is assumed. -/
theorem resolved_boundary_localization {q : ℕ}
    (S : CornerManifold (q+1) (Simplex (q+1)))
    (c : Fin (q+2) → CornerChart (q+1) (Simplex (q+1)))
    (hc : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (T : CornerManifold q (ResolvedFaceSpace S)) (b : CornerOrientation T)
    (hb : IsResolvedOrientation o b)
    (J : CompactTopForm T → ℝ) (hJ : IsIntegral b J)
    (ω : Form S q) (β : CompactTopForm T)
    (hβ : CornerStokesData.IsFaceRestriction ω β.form) :
    ∃ ρ : Fin (q+2) → Simplex (q+1) → ℝ,
      (∀ k, Continuous (ρ k)) ∧
      (∀ k, sectionSupport (ρ k) ⊆ (c k).2.source) ∧
      (∀ p : Simplex (q+1), ∑ k, ρ k p = 1) ∧
      J β = ∑ k : Fin (q+2), ∑ i : Fin (q+1),
        ∫ y in orthantFaceSet (c k).1 i,
          orthantBoundaryCoefficient
            (signedAmbientForm o (weightForm (ρ k) ω) (c k) (hc.mem_atlas k)) i y := by
  obtain ⟨ρ,hρ,hρsupport,hρsum⟩ := simplex_chart_partition S c hc
  let γ (k : Fin (q+2)) : CompactTopForm T :=
    weightTopForm (fun q => ρ k (faceProjection S q))
      ((hρ k).comp (Corners.face_projection_continuous S)) β
  have hγ (k : Fin (q+2)) :
      CornerStokesData.IsFaceRestriction (weightForm (ρ k) ω) (γ k).form :=
    weight_face_restriction (ρ k) ω β.form hβ
  have hγsource (k : Fin (q+2)) :
      formSupport (γ k).form ⊆ faceProjection S ⁻¹' (c k).2.source := by
    intro q hq
    exact hρsupport k (scalar_comp_support (Corners.face_projection_continuous S)
      (ρ k) (weightForm_support _ _ hq).1)
  have hβsum : ∀ e he p, β.form.field e he p =
      ∑ k ∈ (Finset.univ : Finset (Fin (q+2))), (γ k).form.field e he p := by
    intro e he p
    change β.form.field e he p =
      ∑ k ∈ (Finset.univ : Finset (Fin (q+2))),
        ρ k (faceProjection S p.val) • β.form.field e he p
    rw [← Finset.sum_smul]
    rw [hρsum,one_smul]
  refine ⟨ρ,hρ,hρsupport,hρsum,?_⟩
  calc
    J β = ∑ k ∈ (Finset.univ : Finset (Fin (q+2))), J (γ k) :=
      integral_sum J hJ Finset.univ γ β hβsum
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact resolved_integral_over_simplex_chart S c hc o T b hb J hJ
        (weightForm (ρ k) ω) (γ k) (hγ k) k (hγsource k)

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerExamples LocalStokesData SmoothSingularData
  AmbientSimplexData CornerStokesData CornerStokesResults CornerOrientationData OrientationData
  Set MeasureTheory Filter

/-- The coordinate image of any simplex face contains no contribution outside
the full lower-dimensional simplex, including artificial chart edges. -/
theorem orthant_face_zero_off_simplex {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S) (ω : Form S q)
    (k : Fin (q+2)) (i : Fin (q+1)) (y : Euclidean q) (hy : y ∉ simplexSet q) :
    orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (h.mem_atlas k)) i y = 0 := by
  by_cases hz : i.insertNth (0 : ℝ) y ∈ orthantSet (q+1) (c k).1
  · have hypos : ∀ r, 0 ≤ y r := by
      intro r
      simpa using hz (i.succAbove r) (by rw [h.constraints]; exact (i.succAbove r).isLt)
    have hsum : ¬ ∑ r, y r < 1 := fun ht => hy ⟨hypos,ht.le⟩
    have ht : (⟨i.insertNth (0 : ℝ) y,hz⟩ : Orthant (q+1) (c k).1) ∉ (c k).2.target := by
      rw [h.target]
      simpa only [Set.mem_ofPred_eq,Fin.sum_insertNth,zero_add] using hsum
    simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hz,dite_true,ht,
      dite_false,smul_zero,mul_zero]
  · simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hz]

/-- The orthant face integral is the integral over the compact ordered simplex
in the deletion coordinates. This is independent of regularity of the form. -/
theorem orthant_face_integral_eq_simplex {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S) (ω : Form S q)
    (k : Fin (q+2)) (i : Fin (q+1)) :
    (∫ y in orthantFaceSet (c k).1 i,
      orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (h.mem_atlas k)) i y) =
    ∫ y in simplexSet q,
      orthantBoundaryCoefficient (signedAmbientForm o ω (c k) (h.mem_atlas k)) i y := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)]
  · exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (orthant_face_zero_off_simplex h o ω k i)).symm
  · change i.insertNth (0 : ℝ) y ∉ orthantSet (q+1) (c k).1 at hy
    simp [orthantBoundaryCoefficient,signedAmbientForm,ambientForm,hy]


/-- On the compact lower simplex, local weighted boundary coefficients are
exactly the ordered affine face coefficients in the restored face chart. -/
theorem weighted_local_face_pointwise {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (hsign : ∀ k (p : (c k).2.source),
      signValue (o.sign (c k) (h.mem_atlas k) p) = (-1 : ℝ)^k.val)
    (α : CoordinateForm (q+1) q) (ω : Form S q)
    (hω : ∀ k (p : (c k).2.source),
      ω.field (c k) (h.mem_atlas k) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine k).contLinear)
    (ρ : CornerData.Simplex (q+1) → ℝ) (k : Fin (q+2))
    (hsource : sectionSupport ρ ⊆ (c k).2.source)
    (i : Fin (q+1)) (y : Euclidean q) (hy : y ∈ simplexSet q) :
    orthantBoundaryCoefficient
        (signedAmbientForm o (weightForm ρ ω) (c k) (h.mem_atlas k)) i y =
      (-1 : ℝ)^(k.succAbove i).val *
        faceCoefficient (simplexWeightedForm ρ α) (k.succAbove i)
          (simplexRestoreBarycentric (i.predAbove k) y) := by
  have hx : i.insertNth (0 : ℝ) y ∈ orthantSet (q+1) (c k).1 := by
    rw [h.constraints]
    intro r hr
    refine Fin.succAboveCases i ?_ (fun s => ?_) r
    · simp
    · simpa using hy.1 s
  let x : Orthant (q+1) (c k).1 := ⟨i.insertNth (0 : ℝ) y,hx⟩
  have hyrest : simplexRestoreBarycentric (i.predAbove k) y ∈ simplexSet q :=
    restore_mem_simplex (i.predAbove k) hy
  let z : CornerData.Simplex q := ⟨simplexRestoreBarycentric (i.predAbove k) y,hyrest⟩
  have hpoint : (face (k.succAbove i) z).val =
      simplexRestoreBarycentric k (i.insertNth (0 : ℝ) y) :=
    (restore_insert_face k i y).symm
  rw [faceCoefficient_simplexWeightedForm ρ α _ _ hyrest]
  change _ = (-1 : ℝ)^(k.succAbove i).val *
    (ρ (face (k.succAbove i) z) * faceCoefficient α (k.succAbove i) z.val)
  by_cases hs : ∑ r, y r < 1
  · have ht : x ∈ (c k).2.target := by
      rw [h.target]
      simpa only [x,Set.mem_ofPred_eq,Fin.sum_insertNth,zero_add] using hs
    have hp : (c k).2.symm x = face (k.succAbove i) z := by
      apply Subtype.ext
      rw [h.symm_apply k x ht]
      exact hpoint.symm
    simp only [orthantBoundaryCoefficient,signedAmbientForm,chartSign,ambientForm,hx,
      dite_true,show (⟨i.insertNth (0 : ℝ) y,hx⟩ : Orthant (q+1) (c k).1) = x from rfl,ht]
    rw [hsign]
    simp only [weightForm]
    rw [hω]
    simp only [ContinuousAlternatingMap.smul_apply,smul_eq_mul,
      ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hp]
    have ha := simplex_local_face_coefficient_alpha α k i y
    rw [←hpoint] at ha
    change _ = (-1 : ℝ)^(k.succAbove i).val *
      (ρ (face (k.succAbove i) z) * faceCoefficient α (k.succAbove i) z.val)
    dsimp only [z] at ha
    simp only [Function.comp_def]
    dsimp only [z]
    linear_combination (ρ (face (k.succAbove i) z)) * ha
  · have heq : ∑ r, y r = 1 := le_antisymm hy.2 (le_of_not_gt hs)
    have hnt : x ∉ (c k).2.target := by
      rw [h.target]
      simp only [x,Set.mem_ofPred_eq,Fin.sum_insertNth,zero_add,heq,lt_self_iff_false,not_false_eq_true]
    have hrho : ρ (face (k.succAbove i) z) = 0 := by
      by_contra hn
      have hpos := hsource (subset_closure hn)
      rw [h.source] at hpos
      change 0 < simplexBarycentric (face (k.succAbove i) z).val k at hpos
      rw [hpoint,barycentric_restore,Fin.insertNth_apply_same,Fin.sum_insertNth,zero_add,heq] at hpos
      norm_num at hpos
    simp [orthantBoundaryCoefficient,signedAmbientForm,chartSign,ambientForm,hx,
      dite_true,show (⟨i.insertNth (0 : ℝ) y,hx⟩ : Orthant (q+1) (c k).1) = x from rfl,hnt,
      dite_false,zero_smul,mul_zero,hrho,zero_mul]

/-- A localized coordinate face integral is the corresponding ordered simplex
face integral with the exact outward-first alternating sign. -/
theorem simplex_local_face_integral {q : ℕ}
    {S : CornerManifold (q+1) (CornerData.Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (CornerData.Simplex (q+1))}
    (h : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (hsign : ∀ k (p : (c k).2.source),
      signValue (o.sign (c k) (h.mem_atlas k) p) = (-1 : ℝ)^k.val)
    (α : CoordinateForm (q+1) q) (ω : Form S q)
    (hω : ∀ k (p : (c k).2.source),
      ω.field (c k) (h.mem_atlas k) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine k).contLinear)
    (ρ : CornerData.Simplex (q+1) → ℝ) (k : Fin (q+2))
    (hsource : sectionSupport ρ ⊆ (c k).2.source) (i : Fin (q+1)) :
    (∫ y in orthantFaceSet (c k).1 i,
      orthantBoundaryCoefficient
        (signedAmbientForm o (weightForm ρ ω) (c k) (h.mem_atlas k)) i y) =
      (-1 : ℝ)^(k.succAbove i).val *
        ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm ρ α) (k.succAbove i) y := by
  rw [orthant_face_integral_eq_simplex h o (weightForm ρ ω) k i]
  calc
    (∫ y in simplexSet q, orthantBoundaryCoefficient
        (signedAmbientForm o (weightForm ρ ω) (c k) (h.mem_atlas k)) i y) =
      ∫ y in simplexSet q, (-1 : ℝ)^(k.succAbove i).val *
        faceCoefficient (simplexWeightedForm ρ α) (k.succAbove i)
          (simplexRestoreBarycentric (i.predAbove k) y) := by
      apply setIntegral_congr_fun (simplex_isCompact q).isClosed.measurableSet
      intro y hy
      exact weighted_local_face_pointwise h o hsign α ω hω ρ k hsource i y hy
    _ = (-1 : ℝ)^(k.succAbove i).val *
        ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm ρ α) (k.succAbove i)
          (simplexRestoreBarycentric (i.predAbove k) y) := integral_const_mul _ _
    _ = _ := by
      rw [← integral_simplex_restore (i.predAbove k) (simplex_isCompact q).isClosed
        (abs_restore_fderiv_det (i.predAbove k))]

end SmoothManifolds.AmbientSimplexStokes


namespace SmoothManifolds.AmbientSimplexStokes
open ModelData CornerData CornerStokesData CornerStokesResults CornerExamples
  CornerOrientationData OrientationData AmbientSimplexData LocalStokesData Set MeasureTheory Filter

/-- The resolved boundary integral is the alternating sum over exactly the
ordered affine faces of the simplex, including every point above intersections. -/
theorem simplex_boundary_integral {q : ℕ}
    {S : CornerManifold (q+1) (Simplex (q+1))}
    {c : Fin (q+2) → CornerChart (q+1) (Simplex (q+1))}
    (hchart : IsSimplexChartFamily S c) (o : CornerOrientation S)
    (hsign : ∀ k (p : (c k).2.source),
      signValue (o.sign (c k) (hchart.mem_atlas k) p) = (-1 : ℝ)^k.val)
    (T : CornerManifold q (ResolvedFaceSpace S)) (b : CornerOrientation T)
    (hb : IsResolvedOrientation o b) (J : CompactTopForm T → ℝ) (hJ : IsIntegral b J)
    (α : CoordinateForm (q+1) q)
    (hα : LocallyContDiffOn 1 (simplexSet (q+1)) (fun x => α x.val))
    (ω : Form S q)
    (hω : ∀ k (p : (c k).2.source),
      ω.field (c k) (hchart.mem_atlas k) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine k).contLinear)
    (β : CompactTopForm T) (hβ : CornerStokesData.IsFaceRestriction ω β.form) :
    J β = ∑ j : Fin (q+2), (-1 : ℝ)^j.val *
      ∫ y in simplexSet q, faceCoefficient α j y := by
  obtain ⟨ρ,hρ,hρsupport,hρsum,hJlocal⟩ :=
    resolved_boundary_localization S c hchart o T b hb J hJ ω β hβ
  calc
    J β = ∑ k : Fin (q+2), ∑ i : Fin (q+1),
        ∫ y in orthantFaceSet (c k).1 i,
          orthantBoundaryCoefficient
            (signedAmbientForm o (weightForm (ρ k) ω) (c k) (hchart.mem_atlas k)) i y := hJlocal
    _ = ∑ k : Fin (q+2), ∑ i : Fin (q+1), (-1 : ℝ)^(k.succAbove i).val *
        ∫ y in simplexSet q, faceCoefficient (simplexWeightedForm (ρ k) α) (k.succAbove i) y := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      exact simplex_local_face_integral hchart o hsign α ω hω (ρ k) k (hρsupport k) i
    _ = _ := weighted_ordered_face_sum α hα ρ hρ
      (fun k => by simpa only [hchart.source] using hρsupport k) hρsum

/-- Ambient locally C¹ forms realize genuine compact regular corner forms and
the supplied coordinate-compatible bulk and resolved-boundary integrals. -/
theorem corner_integral_bridge :
    Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.corner_integral_bridgeType := by
  intro q α hα
  obtain ⟨S,c,hchart,o,hsign⟩ := source_geometry (q+1)
  obtain ⟨ω,hωreg,hωcompact,hω⟩ := ambient_regular_form_exists S c hchart α hα
  obtain ⟨T,b,hb⟩ := CornerFaceOrientations.resolved_orientation o
  obtain ⟨I,hI,_⟩ := CornerStokesResults.exists_integral S o
  obtain ⟨J,hJ,_⟩ := CornerStokesResults.exists_integral T b
  refine ⟨S,c,o,hchart,hsign,ω,hωreg,hωcompact,hω,T,b,I,J,hb,hI,hJ,?_⟩
  intro η β hη hβ
  have hsign0 : ∀ j (p : (c j).2.source),
      signValue (o.sign (c j) (hchart.mem_atlas j) p) = (-1 : ℝ)^j.val :=
    fun j p => hsign j (hchart.mem_atlas j) p
  have hω0 : ∀ j (p : (c j).2.source),
      ω.field (c j) (hchart.mem_atlas j) p =
        (α p.val.val).compContinuousLinearMap (restoreAffine j).contLinear := by
    intro j p
    simpa only [restore_fderiv] using hω j (hchart.mem_atlas j) p
  exact ⟨simplex_bulk_integral hchart o hsign0 I hI α hα ω hω0 η hη,
    simplex_boundary_integral hchart o hsign0 T b hb J hJ α hα ω hω0 β hβ⟩

/-- The full ambient simplex Stokes identity, including degree zero, follows
from the supplied genuine corner Stokes theorem and the proved integral bridge. -/
theorem stokes : Specs.SmoothManifolds.Comparison.AmbientSimplexStokes.stokesType :=
  stokes_of_corner_integral_bridge corner_integral_bridge

end SmoothManifolds.AmbientSimplexStokes
