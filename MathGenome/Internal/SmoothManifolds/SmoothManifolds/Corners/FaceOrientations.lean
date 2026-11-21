import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Boundary
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Corners.FaceOrientations
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

noncomputable section
open scoped Classical
namespace SmoothManifolds.CornerFaceOrientations
open ModelData CornerData CornerOrientationData OrientationData BoundaryOrientationData
  Set Module Filter
open scoped Topology


@[simp] theorem mem_faceHyperplane {n : ℕ} (i : Fin n) (v : Euclidean n) :
    v ∈ faceHyperplane i ↔ v i = 0 := Iff.rfl

/-- Equality of quotient classes is exactly equality of normal coordinates. -/
theorem normal_class_eq_iff {n : ℕ} (i : Fin n) (v w : Euclidean n) :
    (Submodule.Quotient.mk v : FaceNormalLine i) = Submodule.Quotient.mk w ↔ v i = w i := by
  rw [Submodule.Quotient.eq]
  change v i - w i = 0 ↔ v i = w i
  exact sub_eq_zero

@[simp] theorem normal_class_mem_outward {n : ℕ} (i : Fin n) (v : Euclidean n) :
    (Submodule.Quotient.mk v : FaceNormalLine i) ∈ coordinateOutwardRay i ↔ v i < 0 := by
  constructor
  · rintro ⟨w, hw, he⟩
    rwa [← (normal_class_eq_iff i w v).mp he]
  · intro hv
    exact ⟨v, hv, rfl⟩

@[simp] theorem normal_class_mem_inward {n : ℕ} (i : Fin n) (v : Euclidean n) :
    (Submodule.Quotient.mk v : FaceNormalLine i) ∈ coordinateInwardRay i ↔ 0 < v i := by
  constructor
  · rintro ⟨w, hw, he⟩
    rwa [← (normal_class_eq_iff i w v).mp he]
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem normal_half_line :
    Specs.SmoothManifolds.Corners.FaceOrientations.normal_half_lineType := by
  intro n i v w hv hw
  let a := w i / v i
  have ha : 0 < a := div_pos_of_neg_of_neg hw hv
  have hn : (w - a • v) i = 0 := by
    change w i - a * v i = 0
    rw [div_mul_cancel₀ _ (ne_of_lt hv), sub_self]
  refine ⟨a, ha, hn, ?_⟩
  rw [← Submodule.Quotient.mk_smul, normal_class_eq_iff]
  change w i = a * v i
  exact (div_mul_cancel₀ _ (ne_of_lt hv)).symm

theorem faceInsertion_range {n : ℕ} (i : Fin (n+1)) :
    LinearMap.range (faceInsertion i) = faceHyperplane i := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    simp [faceInsertion]
  · intro hv
    refine ⟨i.removeNth v, ?_⟩
    exact Fin.insertNth_eq_iff.mpr ⟨hv.symm, rfl⟩

theorem outward_independent :
    Specs.SmoothManifolds.Corners.FaceOrientations.outward_independentType := by
  intro n i v w hv hw
  obtain ⟨a, ha, htan, _⟩ := normal_half_line i v w hv hw
  rw [← faceInsertion_range] at htan
  obtain ⟨z, hz⟩ := htan
  have hwz : w = faceInsertion i z + a • v := by
    rw [hz]
    exact (sub_add_cancel w (a • v)).symm
  refine ⟨a, ha, fun η => ?_⟩
  rw [hwz, BoundaryOrientations.normalWedge_add,
    BoundaryOrientations.normalWedge_tangent (by simp [Euclidean]),
    zero_add, BoundaryOrientations.normalWedge_smul]

theorem coordinate_face_sign :
    Specs.SmoothManifolds.Corners.FaceOrientations.coordinate_face_signType := by
  intro n i b
  have h := (ExteriorAlgebra.ιMulti ℝ (n+1) (M := Euclidean (n+1))).neg_one_pow_smul_map_insertNth
    i (b i) (i.removeNth b)
  rw [Fin.insertNth_self_removeNth] at h
  have h' : (-1 : ℝ)^i.val • ExteriorAlgebra.ιMulti ℝ (n+1) b =
      ExteriorAlgebra.ιMulti ℝ (n+1) (Matrix.vecCons (b i) (i.removeNth b)) := by
    simpa only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using h
  rw [map_neg, neg_mul]
  rw [show ExteriorAlgebra.ι ℝ (b i) * ExteriorAlgebra.ιMulti ℝ n (i.removeNth b) =
    ExteriorAlgebra.ιMulti ℝ (n+1) (Matrix.vecCons (b i) (i.removeNth b)) by simp]
  rw [← h']
  simp only [pow_succ, mul_neg_one, neg_smul]


/-- Signed cofactor expansion in the outward-first convention. -/
theorem determinant_outward_signed {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (i j : Fin (n+1)) (a : ℝ)
    (hai : A j i = a) (hzero : ∀ r, r ≠ i → A j r = 0) :
    faceSign 1 j * A.det = a *
      (faceSign 1 i * (A.submatrix j.succAbove i.succAbove).det) := by
  have h := Corners.determinant_single_row_signed A i j a hai hzero
  simp only [faceSign, one_mul, pow_succ, mul_neg_one]
  nlinarith [h]

theorem real_sign_neg_one_pow_mul (n : ℕ) (x : ℝ) :
    Real.sign ((-1 : ℝ)^n * x) = (-1 : ℝ)^n * Real.sign x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_neg_one, neg_mul, Real.sign_neg, ih, neg_mul]

theorem face_sign_gluing :
    Specs.SmoothManifolds.Corners.FaceOrientations.face_sign_gluingType := by
  intro n A i j a ε δ ha hai hz hδ
  have h := congrArg Real.sign (determinant_outward_signed A i j a hai hz)
  simp only [faceSign, one_mul] at h
  rw [real_sign_neg_one_pow_mul,
    Corners.real_sign_mul_of_pos ha, real_sign_neg_one_pow_mul] at h
  dsimp [faceSign]
  rw [hδ]
  calc
    ε * Real.sign A.det * (-1 : ℝ)^(j.val+1) =
        ε * ((-1 : ℝ)^(j.val+1) * Real.sign A.det) := by ring
    _ = ε * ((-1 : ℝ)^(i.val+1) * Real.sign (A.submatrix j.succAbove i.succAbove).det) := by rw [h]
    _ = _ := by ring

theorem faceInsertion_single {n : ℕ} (i : Fin (n+1)) (r : Fin n) :
    faceInsertion i (Pi.single r (1 : ℝ)) = Pi.single (i.succAbove r) 1 := by
  funext s
  refine Fin.succAboveCases i ?_ (fun t => ?_) s
  · simp [faceInsertion, Pi.single_apply, Fin.succAbove_ne]
  · simp [faceInsertion, Pi.single_apply, Fin.succAbove_inj]

theorem faceDerivative_matrix {n : ℕ}
    (L : Euclidean (n+1) →ₗ[ℝ] Euclidean (n+1)) (i j : Fin (n+1)) :
    LinearMap.toMatrix' (faceDerivative L i j) =
      (LinearMap.toMatrix' L).submatrix j.succAbove i.succAbove := by
  ext r s
  change L (faceInsertion i (Pi.single s 1)) (j.succAbove r) =
    L (Pi.single (i.succAbove s) 1) (j.succAbove r)
  rw [faceInsertion_single]

theorem cone_face_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.cone_face_orientationType := by
  intro n k l x y E hE
  obtain ⟨σ, a, ha, hcoord, _⟩ := Corners.cone_facets x y E hE
  refine ⟨σ, a, ha, hcoord, ?_, ?_, ?_⟩
  · intro v j
    change E v j.val = 0 ↔ v (σ j).val = 0
    rw [hcoord, mul_eq_zero]
    exact or_iff_right (ne_of_gt (ha j))
  · intro v j
    rw [hcoord]
    constructor
    · intro h
      nlinarith [ha j]
    · exact mul_neg_of_pos_of_neg (ha j)
  · intro j
    let A := LinearMap.toMatrix' E.toLinearMap
    have hai : A j.val (σ j).val = a j := by
      change E (Pi.single (σ j).val (1 : ℝ)) j.val = a j
      rw [hcoord]
      simp
    have hz : ∀ r, r ≠ (σ j).val → A j.val r = 0 := by
      intro r hr
      change E (Pi.single r (1 : ℝ)) j.val = 0
      rw [hcoord]
      simp [Pi.single_apply, Ne.symm hr]
    have h := determinant_outward_signed A (σ j).val j.val (a j) hai hz
    simpa only [A, LinearMap.det_toMatrix', ← faceDerivative_matrix] using h


theorem normal_quotient_transport :
    Specs.SmoothManifolds.Corners.FaceOrientations.normal_quotient_transportType := by
  intro n i j E a ha hcoord
  have hp : (faceHyperplane i).map E.toLinearMap = faceHyperplane j := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      change v i = 0 at hv
      change E v j = 0
      rw [hcoord, hv, mul_zero]
    · intro hw
      change w j = 0 at hw
      refine ⟨E.symm w, ?_, E.apply_symm_apply w⟩
      change E.symm w i = 0
      have h := hcoord (E.symm w)
      rw [E.apply_symm_apply, hw] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt ha)
  let Q := Submodule.Quotient.equiv (faceHyperplane i) (faceHyperplane j) E hp
  have hQ (v : Euclidean n) : Q (Submodule.Quotient.mk v) = Submodule.Quotient.mk (E v) := rfl
  refine ⟨Q, hQ, ?_, ?_⟩
  · ext q
    constructor
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      rw [hQ, normal_class_mem_outward, hcoord]
      exact mul_neg_of_pos_of_neg ha hv
    · rintro ⟨w, hw, rfl⟩
      refine ⟨Submodule.Quotient.mk (E.symm w), ?_, ?_⟩
      · rw [normal_class_mem_outward]
        change w j < 0 at hw
        have h := hcoord (E.symm w)
        rw [E.apply_symm_apply] at h
        nlinarith
      · rw [hQ, E.apply_symm_apply]
  · ext q
    constructor
    · rintro ⟨r, ⟨v, hv, rfl⟩, rfl⟩
      rw [hQ, normal_class_mem_inward, hcoord]
      exact mul_pos ha hv
    · rintro ⟨w, hw, rfl⟩
      refine ⟨Submodule.Quotient.mk (E.symm w), ?_, ?_⟩
      · rw [normal_class_mem_inward]
        change 0 < w j at hw
        have h := hcoord (E.symm w)
        rw [E.apply_symm_apply] at h
        nlinarith
      · rw [hQ, E.apply_symm_apply]

theorem signValue_injective : Function.Injective signValue := by
  intro b c h
  cases b <;> cases c <;> first | rfl | norm_num [signValue] at h

/-- Signs of a corner orientation on any covering chart family determine it. -/
theorem cornerOrientation_ext_on_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold n M} (o q : CornerOrientation S)
    (A : Set (CornerChart n M)) (hsub : A ⊆ S.atlas)
    (hcover : ∀ p : M, ∃ c ∈ A, p ∈ c.2.source)
    (hagree : ∀ c (hc : c ∈ A) (p : c.2.source),
      o.sign c (hsub hc) p = q.sign c (hsub hc) p) : o = q := by
  have hsign : o.sign = q.sign := by
    funext c hc p
    obtain ⟨d, hd, hpd⟩ := hcover p.val
    let e := c.2.symm.trans d.2
    have hxe : c.2 p.val ∈ e.source := by
      refine ⟨c.2.map_source p.property, ?_⟩
      change c.2.symm (c.2 p.val) ∈ d.2.source
      rwa [c.2.left_inv p.property]
    obtain ⟨U, hU, hxU, F, hF, heq⟩ := (S.maximal.1.2 c hc d (hsub hd)).1 ⟨c.2 p.val,hxe⟩
    let H : OrthantExtension e.source e (c.2 p.val) :=
      ⟨U,hU,hxU,F,hF,fun z hz hzU => heq ⟨z,hz⟩ hzU⟩
    have ho := o.compatible c d hc (hsub hd) p.val p.property hpd H
    have hq := q.compatible c d hc (hsub hd) p.val p.property hpd H
    rw [hagree d hd] at ho
    have ht : Real.sign (LinearMap.det (fderiv ℝ H.map (c.2 p.val).val).toLinearMap) ≠ 0 := by
      intro ht
      rw [ht, mul_zero] at ho
      exact OrientationResults.signValue_ne_zero _ ho
    have h := mul_right_cancel₀ ht (ho.symm.trans hq)
    exact signValue_injective h
  cases o
  cases q
  cases hsign
  rfl

theorem resolved_orientation_unique :
    Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientation_uniqueType := by
  intro n M _ S o T b b' hb hb'
  have hsub : {e | IsResolvedFaceChart S e} ⊆ T.atlas := by
    rw [hb.1]
    exact Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas S)
  apply cornerOrientation_ext_on_cover b b' {e | IsResolvedFaceChart S e} hsub
    (Corners.resolved_face_atlas S).1
  rintro e ⟨c,hc,i,hi,hk,hes,hec⟩ p
  have he : e ∈ T.atlas := hsub ⟨c,hc,i,hi,hk,hes,hec⟩
  have hs : p.val ∈ faceSheet S c i univ := by
    rw [← hes]
    exact p.property
  have hpc : p.val.1 ∈ c.2.source := hs.2.1
  exact signValue_injective ((hb.2 c hc i hi e he hk hes hec p.val p.property hpc).trans
    (hb'.2 c hc i hi e he hk hes hec p.val p.property hpc).symm)


theorem coordinateVolume_ne_zero (n : ℕ) : coordinateVolume n ≠ 0 := by
  intro hz
  let A := exteriorPower.alternatingMapLinearEquiv ((Pi.basisFun ℝ (Fin n)).det)
  have h := congrArg A hz
  dsimp [A] at h
  simp only [coordinateVolume, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_self, map_zero] at h
  exact one_ne_zero h

theorem coordinate_normalWedge {n : ℕ} (i : Fin (n+1)) :
    normalWedge (faceInsertion i) (-((Pi.basisFun ℝ (Fin (n+1))) i)) (coordinateVolume n) =
      (-1 : ℝ)^(i.val+1) • coordinateVolume (n+1) := by
  apply Subtype.ext
  simp only [BoundaryOrientations.coe_normalWedge, coordinateVolume,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti, Submodule.coe_smul_of_tower]
  have hb : (fun s : Fin n => faceInsertion i ((Pi.basisFun ℝ (Fin n)) s)) =
      i.removeNth (Pi.basisFun ℝ (Fin (n+1))) := by
    funext s
    simpa only [Pi.basisFun_apply, Fin.removeNth] using faceInsertion_single i s
  change ExteriorAlgebra.ι ℝ (-((Pi.basisFun ℝ (Fin (n+1))) i)) *
    ExteriorAlgebra.ιMulti ℝ n (fun s => faceInsertion i ((Pi.basisFun ℝ (Fin n)) s)) = _
  rw [hb]
  exact coordinate_face_sign i (Pi.basisFun ℝ (Fin (n+1)))

theorem local_face_ray :
    Specs.SmoothManifolds.Corners.FaceOrientations.local_face_rayType := by
  intro n i ε hε r hr
  let z := faceSign ε i • coordinateVolume n
  have hz : z ≠ 0 := smul_ne_zero
    (mul_ne_zero hε (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))) (coordinateVolume_ne_zero n)
  let s := rayOfNeZero ℝ z hz
  refine ⟨s, ⟨⟨hz,rfl⟩, ?_⟩, ?_⟩
  · intro v hv
    let v₀ : Euclidean (n+1) := -((Pi.basisFun ℝ (Fin (n+1))) i)
    have hv₀ : v₀ i < 0 := by simp [v₀]
    obtain ⟨a, ha, hw⟩ := outward_independent i v₀ v hv₀ hv
    have hstd : normalWedge (faceInsertion i) v z = a • (ε • coordinateVolume (n+1)) := by
      dsimp [z]
      rw [BoundaryOrientations.normalWedge_smul_right, hw]
      change faceSign ε i • (a • normalWedge (faceInsertion i)
        (-((Pi.basisFun ℝ (Fin (n+1))) i)) (coordinateVolume n)) = _
      rw [coordinate_normalWedge, smul_smul, smul_smul, smul_smul]
      congr 1
      dsimp [faceSign]
      have hp : (-1 : ℝ)^(i.val+1) * (-1 : ℝ)^(i.val+1) = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        ε * (-1 : ℝ)^(i.val+1) * a * (-1 : ℝ)^(i.val+1) =
          (a * ε) * ((-1 : ℝ)^(i.val+1) * (-1 : ℝ)^(i.val+1)) := by ring
        _ = a * ε := by rw [hp, mul_one]
    have hpos : IsPositive r (normalWedge (faceInsertion i) v z) := by
      rw [hstd]
      exact (BoundaryOrientations.positive_smul_iff r _ ha).mpr hr
    exact BoundaryOrientations.positive_linearMap_iff_of_generator
      (by rw [exteriorPower.finrank_eq]; simp [Euclidean])
      (BoundaryOrientations.faceWedgeMap rfl (faceInsertion i) v) s r z ⟨hz,rfl⟩ hpos
  · intro t ht
    exact ht.1.choose_spec.symm


theorem real_sign_eq_signType (x : ℝ) : Real.sign x = (SignType.sign x : ℝ) := by
  obtain h | rfl | h := lt_trichotomy x 0
  · simp [Real.sign_of_neg h, sign_neg h]
  · simp
  · simp [Real.sign_of_pos h, sign_pos h]

private def adjustSign (a : ℝ) (b : Bool) : Bool := if 0 < a then b else !b

private theorem signValue_adjustSign {a : ℝ} (ha : a ≠ 0) (b : Bool) :
    signValue (adjustSign a b) = signValue b * Real.sign a := by
  obtain h | h := ha.lt_or_gt
  · cases b <;> simp [adjustSign, signValue, Real.sign_of_neg h, h.not_gt]
  · simp [adjustSign, h, Real.sign_of_pos h]

/-- An ordinary transition extension induces a genuine extension of the
converted corner transition, with the conjugated derivative. -/
theorem ordinary_transition_extension {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (E : CornerProductData.ModelOrthantCoordinates n a)
    (c d : ModelChart n a M) (p : M) (hp : p ∈ c.source) (hq : p ∈ d.source)
    (U : Set (Euclidean n)) (F : Euclidean n → Euclidean n)
    (hU : IsOpen U) (hpU : (c p).val ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (heq : ∀ z ∈ (c.symm.trans d).source, z.val ∈ U → F z.val = ((c.symm.trans d) z).val) :
    ∃ H : OrthantExtension
      ((CornerProductData.ordinaryCornerChart E c).2.symm.trans
        (CornerProductData.ordinaryCornerChart E d).2).source
      ((CornerProductData.ordinaryCornerChart E c).2.symm.trans
        (CornerProductData.ordinaryCornerChart E d).2)
      ((CornerProductData.ordinaryCornerChart E c).2 p),
      (fderiv ℝ H.map ((CornerProductData.ordinaryCornerChart E c).2 p).val).toLinearMap.det =
        (fderiv ℝ F (c p).val).toLinearMap.det := by
  let L := E.linearEquiv
  let c' := CornerProductData.ordinaryCornerChart E c
  let d' := CornerProductData.ordinaryCornerChart E d
  let G : Euclidean n → Euclidean n := fun z => L (F (L.symm z))
  let V := L.symm ⁻¹' U
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G V :=
    L.contDiff.contDiffOn.comp (hF.comp L.symm.contDiff.contDiffOn (fun _ hz => hz))
      (mapsTo_univ _ _)
  have hpV : (c'.2 p).val ∈ V := by
    change L.symm (L (c p).val) ∈ U
    rwa [L.symm_apply_apply]
  let H : OrthantExtension (c'.2.symm.trans d'.2).source (c'.2.symm.trans d'.2) (c'.2 p) := {
    domain := V
    isOpen_domain := hU.preimage L.symm.continuous
    mem_domain := hpV
    map := G
    smooth := hG
    agrees := by
      intro z hz hzV
      let q := c'.2.symm z
      have hqc : q ∈ c.source := by
        rw [← CornerProducts.ordinaryCornerChart_source E c]
        exact c'.2.map_target hz.1
      have hqd : q ∈ d.source := by
        rw [← CornerProducts.ordinaryCornerChart_source E d]
        exact hz.2
      have hcz : L.symm z.val = (c q).val :=
        CornerProducts.ordinaryCornerChart_inverse E c z hz.1
      have hct : c q ∈ (c.symm.trans d).source :=
        ⟨c.map_source hqc, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hqc] using hqd⟩
      change L (F (L.symm z.val)) = L (d q).val
      rw [hcz]
      have hzU : L.symm z.val ∈ U := hzV
      rw [heq (c q) hct (by rw [← hcz]; exact hzU)]
      simp only [OpenPartialHomeomorph.trans_apply, c.left_inv hqc] }
  refine ⟨H, ?_⟩
  have hdF := (hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  have hdF' : HasFDerivAt F (fderiv ℝ F (c p).val) (L.symm (L (c p).val)) := by
    simpa only [L.symm_apply_apply] using hdF.hasFDerivAt
  have hdG := L.hasFDerivAt.comp (L (c p).val)
    ((hdF'.comp (L (c p).val) L.symm.hasFDerivAt))
  have hder : (fderiv ℝ G (L (c p).val)).toLinearMap =
      L.toLinearMap.comp ((fderiv ℝ F (c p).val).toLinearMap.comp L.symm.toLinearMap) :=
    congrArg ContinuousLinearMap.toLinearMap hdG.fderiv
  change (fderiv ℝ G (L (c p).val)).toLinearMap.det = _
  rw [hder]
  exact LinearMap.det_conj (fderiv ℝ F (c p).val).toLinearMap L.toLinearEquiv

theorem ordinary_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.ordinary_orientationType := by
  intro n a M _ S E R hsub o
  let D := LinearMap.det E.linearEquiv.toLinearMap
  have hD : D ≠ 0 := by simpa only [D, ← LinearEquiv.coe_det] using E.linearEquiv.toLinearEquiv.det.ne_zero
  let sg : ∀ c : ModelChart n a M, c ∈ S.smoothStructure.val → c.source → Bool :=
    fun c hc p => adjustSign D (o.sign (CornerProductData.ordinaryCornerChart E c)
      (hsub ⟨c,hc,rfl⟩) (ordinaryPoint E c p))
  have hsg : ∀ c hc (p : c.source), signValue (sg c hc p) =
      signValue (o.sign (CornerProductData.ordinaryCornerChart E c)
        (hsub ⟨c,hc,rfl⟩) (ordinaryPoint E c p)) * Real.sign D :=
    fun _ _ _ => signValue_adjustSign hD _
  let s : SignedCharts S := {
    sign := sg
    locallyConstant := by
      intro c hc
      have hcont : Continuous (ordinaryPoint E c) :=
        continuous_subtype_val.subtype_mk _
      exact ((o.locallyConstant _ _).comp_continuous hcont).comp (adjustSign D)
    compatible := by
      intro K c d hc hd p
      have hpt : c p.val ∈ (c.symm.trans d).source :=
        ⟨c.map_source p.property.1, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv p.property.1] using p.property.2⟩
      obtain ⟨U,hU,hpU,F,hF,heq⟩ :=
        (S.smoothStructure.property.1.2 c hc d hd).1 (c p.val) hpt
      obtain ⟨H,hH⟩ := ordinary_transition_extension E c d p.val p.property.1 p.property.2 U F hU hpU hF heq
      have hrep : (fun q => F (c q).val) =ᶠ[nhds p.val] (fun q => (d q).val) := by
        have hcU := ((continuous_subtype_val.continuousAt.comp
          (c.continuousAt p.property.1)).eventually (hU.mem_nhds hpU))
        filter_upwards [c.open_source.mem_nhds p.property.1,
          d.open_source.mem_nhds p.property.2,hcU] with q hqc hqd hqU
        have hqt : c q ∈ (c.symm.trans d).source :=
          ⟨c.map_source hqc, by simpa only [OpenPartialHomeomorph.symm_symm, mem_preimage, c.left_inv hqc] using hqd⟩
        simpa only [OpenPartialHomeomorph.trans_apply,c.left_inv hqc] using heq (c q) hqt hqU
      have hjac := OrientationResults.transition_jacobian S K c d hc hd p U F hU hpU hF hrep
      have hcompat := o.compatible (CornerProductData.ordinaryCornerChart E c)
        (CornerProductData.ordinaryCornerChart E d) (hsub ⟨c,hc,rfl⟩) (hsub ⟨d,hd,rfl⟩)
        p.val (ordinaryPoint E c ⟨p.val,p.property.1⟩).property
        (ordinaryPoint E d ⟨p.val,p.property.2⟩).property H
      rw [hH, ← hjac] at hcompat
      rw [hsg d hd ⟨p.val,p.property.2⟩,hsg c hc ⟨p.val,p.property.1⟩,← real_sign_eq_signType]
      calc
        _ = (signValue (o.sign (CornerProductData.ordinaryCornerChart E c)
          (hsub ⟨c,hc,rfl⟩) (ordinaryPoint E c ⟨p.val,p.property.1⟩)) *
            Real.sign (transitionDeterminant K c d hc hd p)) * Real.sign D :=
          congrArg (fun t : ℝ => t * Real.sign D) hcompat
        _ = _ := by ring }
  obtain ⟨r,hr,_⟩ := OrientationResults.signed_orientation_exists_unique S s
  exact ⟨r,s,hr,fun c hc p => hsg c hc p⟩


theorem local_product_ray :
    Specs.SmoothManifolds.Corners.FaceOrientations.local_product_rayType := by
  intro m n M N _ _ C c d
  let L := (C c.1 d.1).linearEquiv
  refine ⟨(CornerProducts.coordinate_tangent_sum C c d).1,
    (fun _ => L.symm.hasFDerivAt), ?_⟩
  intro r s
  let hm : finrank ℝ (Euclidean m) = m := by simp
  let hn : finrank ℝ (Euclidean n) = n := by simp
  let t := Module.Ray.map (OrientationProductData.determinantMap (m+n) L.toLinearEquiv)
    (OrientationProducts.orderedProductRay hm hn r s)
  have ht : ∀ v w, IsPositive r v → IsPositive s w →
      IsPositive t (coordinateProductVector (C c.1 d.1) v w) := by
    intro v w hv hw
    exact OrientationProducts.isPositive_map _
      (OrientationProducts.orderedProductRay_positive hm hn r s hv hw)
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  have hr : IsPositive r r.someVector := ⟨r.someVector_ne_zero,r.someVector_ray⟩
  have hs : IsPositive s s.someVector := ⟨s.someVector_ne_zero,s.someVector_ray⟩
  exact OrientationProducts.positive_ray_eq (ht' _ _ hr hs) (ht _ _ hr hs)

theorem product_left_wedge :
    Specs.SmoothManifolds.Corners.FaceOrientations.product_left_wedgeType := by
  intro m n k l C i v η θ
  let E := C.linearEquiv.toLinearEquiv
  let D := (faceInsertion i).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)
  let ξ := OrientationProductData.orderedWedge m n _ _ η θ
  have h := BoundaryOrientations.normalWedge_map D E (v,0) ξ
  calc
    _ = castExterior (Nat.add_right_comm m n 1)
        (OrientationProductData.determinantMap (m+n+1) E (normalWedge D (v,0) ξ)) :=
      congrArg (castExterior (Nat.add_right_comm m n 1)) h.symm
    _ = OrientationProductData.determinantMap ((m+1)+n) E
        (castExterior (Nat.add_right_comm m n 1) (normalWedge D (v,0) ξ)) :=
      (BoundaryOrientations.determinantMap_cast _ E _).symm
    _ = _ := congrArg (OrientationProductData.determinantMap ((m+1)+n) E)
      (BoundaryOrientations.normalWedge_ordered_left m n (faceInsertion i) v η θ)

theorem product_right_wedge :
    Specs.SmoothManifolds.Corners.FaceOrientations.product_right_wedgeType := by
  intro m n k l C j v η θ
  let E := C.linearEquiv.toLinearEquiv
  let D := (LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j)
  let ξ := OrientationProductData.orderedWedge m n _ _ η θ
  have h := BoundaryOrientations.normalWedge_map D E (0,v) ξ
  calc
    _ = castExterior (Nat.add_assoc m n 1)
        (OrientationProductData.determinantMap (m+n+1) E (normalWedge D (0,v) ξ)) :=
      congrArg (castExterior (Nat.add_assoc m n 1)) h.symm
    _ = OrientationProductData.determinantMap (m+(n+1)) E
        (castExterior (Nat.add_assoc m n 1) (normalWedge D (0,v) ξ)) :=
      (BoundaryOrientations.determinantMap_cast _ E _).symm
    _ = OrientationProductData.determinantMap (m+(n+1)) E
        ((-1 : ℝ)^m • OrientationProductData.orderedWedge m (n+1) _ _ η
          (normalWedge (faceInsertion j) v θ)) :=
      congrArg (OrientationProductData.determinantMap (m+(n+1)) E)
        (BoundaryOrientations.normalWedge_ordered_right m n (faceInsertion j) v η θ)
    _ = _ := map_smul _ _ _



open private uniqueDiffOn_orthantDomain from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.LocalAndResolvedGeometry

/-- Ambient derivatives are independent of the chosen smooth extension, even
at a corner: a relatively open orthant patch has unique derivatives. -/
theorem orthant_extension_derivative_unique {n : ℕ} {k l : Fin (n+1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (x : Orthant n k) (hx : x ∈ e.source)
    (H G : OrthantExtension e.source e x) :
    fderiv ℝ H.map x.val = fderiv ℝ G.map x.val := by
  have hH := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
    (by simp)
  have hG := (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).differentiableAt
    (by simp)
  have hHU : ∀ᶠ z in 𝓝 x.val, z ∈ H.domain := H.isOpen_domain.mem_nhds H.mem_domain
  have hGU : ∀ᶠ z in 𝓝 x.val, z ∈ G.domain := G.isOpen_domain.mem_nhds G.mem_domain
  have heq : H.map =ᶠ[𝓝[Subtype.val '' e.source] x.val] G.map := by
    filter_upwards [self_mem_nhdsWithin,
      hHU.filter_mono nhdsWithin_le_nhds,
      hGU.filter_mono nhdsWithin_le_nhds]
      with z hz hzH hzG
    obtain ⟨y, hy, rfl⟩ := hz
    exact (H.agrees y hy hzH).trans (G.agrees y hy hzG).symm
  exact (uniqueDiffOn_orthantDomain e.open_source x.val ⟨x,hx,rfl⟩).eq
    (hH.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq.symm
      ((H.agrees x hx H.mem_domain).trans (G.agrees x hx G.mem_domain).symm).symm)
    hG.hasFDerivAt.hasFDerivWithinAt

/-- Choose one ambient extension of a genuine chart transition. -/
def cornerTransitionExtension {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p) := by
  have hx : c.2 p ∈ (c.2.symm.trans d.2).source :=
    ⟨c.2.map_source hp, by simpa only [OpenPartialHomeomorph.symm_symm,
      mem_preimage, c.2.left_inv hp] using hq⟩
  let hloc := h.1 ⟨c.2 p,hx⟩
  let U := hloc.choose
  let F := hloc.choose_spec.2.2.choose
  exact ⟨U, hloc.choose_spec.1, hloc.choose_spec.2.1, F,
    hloc.choose_spec.2.2.choose_spec.1,
    fun z hz hzU => hloc.choose_spec.2.2.choose_spec.2 ⟨z,hz⟩ hzU⟩

/-- The transition derivative is canonical by extension uniqueness. -/
def cornerTransitionDerivative {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :=
  fderiv ℝ (cornerTransitionExtension c d h p hp hq).map (c.2 p).val

theorem cornerTransitionDerivative_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p)) :
    cornerTransitionDerivative c d h p hp hq = fderiv ℝ H.map (c.2 p).val := by
  apply orthant_extension_derivative_unique
  refine ⟨c.2.map_source hp, ?_⟩
  change c.2.symm (c.2 p) ∈ d.2.source
  rwa [c.2.left_inv hp]

theorem cornerTransitionDerivative_det_ne_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    LinearMap.det (cornerTransitionDerivative c d h p hp hq).toLinearMap ≠ 0 := by
  let H := cornerTransitionExtension c d h p hp hq
  have hx : c.2 p ∈ (c.2.symm.trans d.2).source :=
    ⟨c.2.map_source hp, by simpa only [OpenPartialHomeomorph.symm_symm,
      mem_preimage, c.2.left_inv hp] using hq⟩
  obtain ⟨E,hE,_,_⟩ := Corners.transition_cone _ h.1 h.2 (c.2 p) hx H
  change LinearMap.det (fderiv ℝ H.map (c.2 p).val).toLinearMap ≠ 0
  have hEn : LinearMap.det E.toLinearMap ≠ 0 := E.toLinearEquiv.isUnit_det'.ne_zero
  have heL : E.toLinearMap = (fderiv ℝ H.map (c.2 p).val).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap hE
  exact fun hz => hEn (heL.symm ▸ hz)


/-- Chain rule on overlaps, using uniqueness on relatively open orthants. -/
theorem cornerTransitionDerivative_comp {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d e : CornerChart n M) (hcd : CornerCompatible c d)
    (hde : CornerCompatible d e) (hce : CornerCompatible c e)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) (hr : p ∈ e.2.source) :
    cornerTransitionDerivative c e hce p hp hr =
      (cornerTransitionDerivative d e hde p hq hr).comp
        (cornerTransitionDerivative c d hcd p hp hq) := by
  let H := cornerTransitionExtension c d hcd p hp hq
  let G := cornerTransitionExtension d e hde p hq hr
  let f := c.2.symm.trans d.2
  have hx : c.2 p ∈ f.source :=
    ⟨c.2.map_source hp, by simpa only [OpenPartialHomeomorph.symm_symm,
      mem_preimage, c.2.left_inv hp] using hq⟩
  have hHx : H.map (c.2 p).val = (d.2 p).val := by
    simpa only [f, OpenPartialHomeomorph.trans_apply, c.2.left_inv hp] using
      H.agrees (c.2 p) hx H.mem_domain
  obtain ⟨W,hW,hWeq⟩ := isOpen_induced_iff.mp f.open_source
  have hxW : (c.2 p).val ∈ W := by rw [← hWeq] at hx; exact hx
  let J : OrthantExtension (c.2.symm.trans e.2).source (c.2.symm.trans e.2) (c.2 p) := {
    domain := (H.domain ∩ W) ∩ H.map ⁻¹' G.domain
    isOpen_domain := (H.smooth.mono inter_subset_left).continuousOn.isOpen_inter_preimage
      (H.isOpen_domain.inter hW) G.isOpen_domain
    mem_domain := ⟨⟨H.mem_domain,hxW⟩, by change H.map (c.2 p).val ∈ G.domain; rw [hHx]; exact G.mem_domain⟩
    map := G.map ∘ H.map
    smooth := G.smooth.comp (H.smooth.mono (inter_subset_left.trans inter_subset_left))
      (fun _ hz => hz.2)
    agrees := by
      intro z hz hzJ
      have hzf : z ∈ f.source := by rw [← hWeq]; exact hzJ.1.2
      have hzd : c.2.symm z ∈ d.2.source := hzf.2
      have hzg : f z ∈ (d.2.symm.trans e.2).source := by
        refine ⟨d.2.map_source hzd, ?_⟩
        change d.2.symm (d.2 (c.2.symm z)) ∈ e.2.source
        rw [d.2.left_inv hzd]
        exact hz.2
      have hHz := H.agrees z hzf hzJ.1.1
      change G.map (H.map z.val) = (e.2 (c.2.symm z)).val
      rw [hHz, G.agrees (f z) hzg (by rw [← hHz]; exact hzJ.2),
        OpenPartialHomeomorph.trans_apply]
      change (e.2 (d.2.symm (d.2 (c.2.symm z)))).val = _
      rw [d.2.left_inv hzd] }
  rw [cornerTransitionDerivative_eq c e hce p hp hr J]
  have hH := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
    (by simp)
  have hG := (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).differentiableAt
    (by simp)
  change fderiv ℝ (G.map ∘ H.map) (c.2 p).val = _
  rw [fderiv_comp _ (by rwa [hHx]) hH, hHx]
  rfl

/-- The Jacobian sign, regarded as a function on the actual chart overlap. -/
def cornerTransitionSign {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source}) : ℝ :=
  Real.sign (LinearMap.det (cornerTransitionDerivative c d h p.val p.property.1 p.property.2).toLinearMap)

theorem cornerTransitionSign_ne_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source}) :
    cornerTransitionSign c d h p ≠ 0 := by
  exact fun hz => cornerTransitionDerivative_det_ne_zero c d h _ _ _
    (Real.sign_eq_zero_iff.mp hz)

/-- Smoothness makes the sign locally constant up to every corner stratum. -/
theorem cornerTransitionSign_locallyConstant {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d) :
    IsLocallyConstant (cornerTransitionSign c d h) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  let H := cornerTransitionExtension c d h p.val p.property.1 p.property.2
  have hcoord : ContinuousAt (fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      (c.2 q.val).val) p :=
    continuous_subtype_val.continuousAt.comp
      ((c.2.continuousAt p.property.1).comp continuous_subtype_val.continuousAt)
  have hder : ContinuousAt (fderiv ℝ H.map) (c.2 p.val).val :=
    (H.smooth.continuousOn_fderiv_of_isOpen H.isOpen_domain (by simp)).continuousAt
      (H.isOpen_domain.mem_nhds H.mem_domain)
  have hdercoord : ContinuousAt (fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      fderiv ℝ H.map (c.2 q.val).val) p :=
    hder.comp (f := fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} => (c.2 q.val).val) hcoord
  have hdet : ContinuousAt (fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
      LinearMap.det (fderiv ℝ H.map (c.2 q.val).val).toLinearMap) p :=
    ContinuousLinearMap.continuous_det.continuousAt.comp
      (f := fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} => fderiv ℝ H.map (c.2 q.val).val) hdercoord
  have hn : LinearMap.det (fderiv ℝ H.map (c.2 p.val).val).toLinearMap ≠ 0 :=
    cornerTransitionDerivative_det_ne_zero c d h p.val p.property.1 p.property.2
  have he : ∀ᶠ q in 𝓝 p,
      SignType.sign (LinearMap.det (fderiv ℝ H.map (c.2 q.val).val).toLinearMap) =
        SignType.sign (LinearMap.det (fderiv ℝ H.map (c.2 p.val).val).toLinearMap) :=
    ((continuousAt_sign_of_ne_zero hn).comp
      (f := fun q : {p : M // p ∈ c.2.source ∧ p ∈ d.2.source} =>
        LinearMap.det (fderiv ℝ H.map (c.2 q.val).val).toLinearMap) hdet).eventually
      (by exact isOpen_discrete _ |>.mem_nhds (show SignType.sign _ ∈ {SignType.sign _} from rfl))
  filter_upwards [he, hcoord.eventually (H.isOpen_domain.mem_nhds H.mem_domain)] with q hq hqU
  let G : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 q.val) :=
    ⟨H.domain,H.isOpen_domain,hqU,H.map,H.smooth,H.agrees⟩
  unfold cornerTransitionSign
  rw [cornerTransitionDerivative_eq c d h q.val q.property.1 q.property.2 G]
  change Real.sign (LinearMap.det (fderiv ℝ H.map (c.2 q.val).val).toLinearMap) = _
  rw [real_sign_eq_signType, real_sign_eq_signType]
  exact congrArg (fun x : SignType => (x : ℝ)) hq


/-- The sign of a composite transition is the product of its signs. -/
theorem cornerTransitionSign_comp {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d e : CornerChart n M) (hcd : CornerCompatible c d)
    (hde : CornerCompatible d e) (hce : CornerCompatible c e)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) (hr : p ∈ e.2.source) :
    cornerTransitionSign c e hce ⟨p,hp,hr⟩ =
      cornerTransitionSign c d hcd ⟨p,hp,hq⟩ *
        cornerTransitionSign d e hde ⟨p,hq,hr⟩ := by
  unfold cornerTransitionSign
  rw [cornerTransitionDerivative_comp c d e hcd hde hce p hp hq hr]
  change Real.sign (LinearMap.det
    ((cornerTransitionDerivative d e hde p hq hr).toLinearMap.comp
      (cornerTransitionDerivative c d hcd p hp hq).toLinearMap)) = _
  rw [LinearMap.det_comp]
  simp only [real_sign_eq_signType, sign_mul, SignType.coe_mul]
  ring

set_option maxHeartbeats 1600000 in
/-- A compatible orientation on an arbitrary covering subatlas descends to
all smoothly compatible corner coordinates. -/
theorem orientation_extension :
    Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType := by
  intro n M _ S A hsub hcover a
  have hcover0 := hcover
  choose r hr hpr using hcover0
  let compat := fun c (hc : c ∈ S.atlas) d (hd : d ∈ S.atlas) =>
    S.maximal.1.2 c hc d hd
  let s : ∀ c : CornerChart n M, c ∈ S.atlas → c.2.source → Bool :=
    fun c hc p => adjustSign
      (LinearMap.det (cornerTransitionDerivative (r p.val) c
        (compat _ (hsub (hr p.val)) _ hc) p.val (hpr p.val) p.property).toLinearMap)
      (a.sign (r p.val) (hr p.val) ⟨p.val,hpr p.val⟩)
  have hs : ∀ (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source),
      signValue (s c hc p) =
        signValue (a.sign (r p.val) (hr p.val) ⟨p.val,hpr p.val⟩) *
        cornerTransitionSign (r p.val) c (compat _ (hsub (hr p.val)) _ hc)
          ⟨p.val,hpr p.val,p.property⟩ := by
    intro c hc p
    exact signValue_adjustSign (cornerTransitionDerivative_det_ne_zero _ _ _ _ _ _) _
  have hanchor : ∀ (c : CornerChart n M) (hc : c ∈ S.atlas) (p : c.2.source)
      (d : CornerChart n M) (hd : d ∈ A) (hpd : p.val ∈ d.2.source),
      signValue (s c hc p) = signValue (a.sign d hd ⟨p.val,hpd⟩) *
        cornerTransitionSign d c (compat _ (hsub hd) _ hc) ⟨p.val,hpd,p.property⟩ := by
    intro c hc p d hd hpd
    have had := a.compatible (r p.val) d (hr p.val) hd p.val (hpr p.val) hpd
      (cornerTransitionExtension (r p.val) d (compat _ (hsub (hr p.val)) _ (hsub hd))
        p.val (hpr p.val) hpd)
    change signValue (a.sign d hd ⟨p.val,hpd⟩) =
      signValue (a.sign (r p.val) (hr p.val) ⟨p.val,hpr p.val⟩) *
        cornerTransitionSign (r p.val) d
          (compat _ (hsub (hr p.val)) _ (hsub hd)) ⟨p.val,hpr p.val,hpd⟩ at had
    rw [hs c hc p, cornerTransitionSign_comp (r p.val) d c
      (compat _ (hsub (hr p.val)) _ (hsub hd)) (compat _ (hsub hd) _ hc)
      (compat _ (hsub (hr p.val)) _ hc) p.val (hpr p.val) hpd p.property,
      had, mul_assoc]
  have hlc : ∀ (c : CornerChart n M) (hc : c ∈ S.atlas), IsLocallyConstant (s c hc) := by
    intro c hc
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    obtain ⟨d,hd,hpd⟩ := hcover p.val
    let U : Set c.2.source := {q | q.val ∈ d.2.source}
    have hU : IsOpen U := d.2.open_source.preimage continuous_subtype_val
    let inc : U → {q : M // q ∈ d.2.source ∧ q ∈ c.2.source} :=
      fun q => ⟨q.val.val,q.property,q.val.property⟩
    have hinc : Continuous inc := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have hadlc : IsLocallyConstant
        (fun q : U => signValue (a.sign d hd ⟨q.val.val,q.property⟩)) :=
      ((a.locallyConstant d hd).comp signValue).comp_continuous
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    have ht : IsLocallyConstant
        (fun q : U => cornerTransitionSign d c (compat _ (hsub hd) _ hc) (inc q)) :=
      (cornerTransitionSign_locallyConstant d c (compat _ (hsub hd) _ hc)).comp_continuous hinc
    have hf : IsLocallyConstant (fun q : U => signValue (s c hc q.val)) := by
      have heq : (fun q : U => signValue (s c hc q.val)) =
          (fun q : U => signValue (a.sign d hd ⟨q.val.val,q.property⟩) *
            cornerTransitionSign d c (compat _ (hsub hd) _ hc) (inc q)) :=
        funext fun q => hanchor c hc q.val d hd q.property
      rw [heq]
      exact hadlc.comp₂ ht (· * ·)
    have hlocal : ∀ᶠ q : U in 𝓝 ⟨p,hpd⟩,
        s c hc q.val = s c hc p :=
      (hf.eventually_eq ⟨p,hpd⟩).mono fun _ h => signValue_injective h
    rw [← hU.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨p,hpd⟩]
    exact hlocal
  let o : CornerOrientation S := {
    sign := s
    locallyConstant := hlc
    compatible := by
      intro c d hc hd p hp hq H
      obtain ⟨e,he,hpe⟩ := hcover p
      rw [hanchor d hd ⟨p,hq⟩ e he hpe, hanchor c hc ⟨p,hp⟩ e he hpe,
        cornerTransitionSign_comp e c d (compat _ (hsub he) _ hc)
          (compat _ hc _ hd) (compat _ (hsub he) _ hd) p hpe hp hq]
      unfold cornerTransitionSign
      rw [cornerTransitionDerivative_eq c d (compat _ hc _ hd) p hp hq H]
      ring }
  have hagree : ∀ c (hc : c ∈ A) (p : c.2.source),
      o.sign c (hsub hc) p = a.sign c hc p := by
    intro c hc p
    apply signValue_injective
    have ha := a.compatible (r p.val) c (hr p.val) hc p.val (hpr p.val) p.property
      (cornerTransitionExtension (r p.val) c (compat _ (hsub (hr p.val)) _ (hsub hc))
        p.val (hpr p.val) p.property)
    exact (hs c (hsub hc) p).trans ha.symm
  refine ⟨o,hagree,?_⟩
  intro o' ho'
  exact cornerOrientation_ext_on_cover o' o A hsub hcover
    (fun c hc p => (ho' c hc p).trans (hagree c hc p).symm)



universe u
open Corners
/-- A direction tangent to the actual source face differentiates to a direction
with zero target normal coordinate, because the corresponding face germs agree. -/
theorem chart_face_germ_derivative_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p))
    (i : activeCoordinates (c.2 p)) (j : activeCoordinates (d.2 p))
    (hij : chartFaceGerm c p i.val = chartFaceGerm d p j.val)
    (r : Fin n) (hri : r ≠ i.val) :
    fderiv ℝ H.map (c.2 p).val (Pi.single r 1) j.val = 0 := by
  let x := c.2 p
  let v : Euclidean n := Pi.single r 1
  let z : ℝ → Orthant n c.1 := fun t => ⟨x.val + max t 0 • v, by
    intro a ha
    apply add_nonneg (x.property a ha)
    apply mul_nonneg (le_max_right t 0)
    by_cases har : a = r <;> simp [v,har]⟩
  have hz0 : z 0 = x := by apply Subtype.ext; simp [z]
  have hzc : Continuous z := by
    apply Continuous.subtype_mk
    exact continuous_const.add ((continuous_id.max continuous_const).smul continuous_const)
  have hx : x ∈ c.2.target := c.2.map_source hp
  have hztend : Tendsto z (𝓝 0) (𝓝 x) := by
    simpa only [hz0] using (hzc.continuousAt (x := 0)).tendsto
  have hqcont : Tendsto (fun t => c.2.symm (z t)) (𝓝 0) (𝓝 p) := by
    have hcs : ContinuousAt c.2.symm x := c.2.continuousOn_symm.continuousAt (c.2.open_target.mem_nhds hx)
    have hh := hcs.tendsto.comp hztend
    simpa only [x,c.2.left_inv hp,Function.comp_def] using hh
  have hgem : ∀ᶠ q in 𝓝 p,
      (q ∈ c.2.source ∧ (c.2 q).val i.val = 0) =
        (q ∈ d.2.source ∧ (d.2 q).val j.val = 0) := Filter.Germ.coe_eq.mp hij
  have hzt : ∀ᶠ t in 𝓝 (0 : ℝ), z t ∈ c.2.target :=
    hztend.eventually (c.2.open_target.mem_nhds hx)
  have hzH : ∀ᶠ t in 𝓝 (0 : ℝ), (z t).val ∈ H.domain :=
    ((continuous_subtype_val.continuousAt (x := x)).tendsto.comp hztend).eventually
      (H.isOpen_domain.mem_nhds H.mem_domain)
  have hconst : (fun t : ℝ => H.map (x.val + t • v) j.val) =ᶠ[𝓝[Ici 0] 0] (fun _ => 0) := by
    filter_upwards [hzt.filter_mono nhdsWithin_le_nhds,
      hzH.filter_mono nhdsWithin_le_nhds,
      (hqcont.eventually hgem).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htH htgem ht0
    have hzi : (z t).val i.val = 0 := by
      have hi0 := (Finset.mem_filter.mp i.property).2.2
      change x.val i.val + max t 0 * v i.val = 0
      simp [x,hi0,v,Ne.symm hri]
    have hsrc := c.2.map_target ht
    have hcoord : (c.2 (c.2.symm (z t))).val i.val = 0 := by rwa [c.2.right_inv ht]
    have hd : c.2.symm (z t) ∈ d.2.source ∧ (d.2 (c.2.symm (z t))).val j.val = 0 :=
      Eq.mp htgem ⟨hsrc,hcoord⟩
    have he : z t ∈ (c.2.symm.trans d.2).source := ⟨ht,hd.1⟩
    change (0 : ℝ) ≤ t at ht0
    have hztv : (z t).val = x.val + t • v := by simp only [z,max_eq_left ht0]
    rw [← hztv,H.agrees (z t) he htH]
    exact hd.2
  have hH : DifferentiableAt ℝ H.map x.val :=
    (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt (by simp)
  have hdray : HasDerivAt (fun t : ℝ => x.val + t • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add x.val
  have hHx : HasFDerivAt H.map (fderiv ℝ H.map x.val) (x.val + (0 : ℝ) • v) := by
    simpa using hH.hasFDerivAt
  have hdH := hHx.comp_hasDerivAt (0 : ℝ) hdray
  have hdj := (ContinuousLinearMap.proj j.val).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hdH
  have hzj : H.map x.val j.val = 0 := by
    have hxe : x ∈ (c.2.symm.trans d.2).source := ⟨hx,by change c.2.symm x ∈ d.2.source; simpa [x,c.2.left_inv hp] using hq⟩
    rw [H.agrees x hxe H.mem_domain]
    change (d.2 (c.2.symm x)).val j.val = 0
    rw [show c.2.symm x = p from c.2.left_inv hp]
    exact (Finset.mem_filter.mp j.property).2.2
  have hdzero := hdj.hasDerivWithinAt.congr_of_eventuallyEq hconst.symm (by simpa using hzj.symm)
  have heq := UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici 0)
    hdzero (hasDerivAt_const (0 : ℝ) (0 : ℝ)).hasDerivWithinAt
  simpa using heq

/-- Actual equal face germs determine the positive normal row directly by
one-sided differentiation along source-face coordinate rays. -/
theorem chart_face_germ_normal_row {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold n M) (c d : CornerChart n M)
    (hc : c ∈ S.atlas) (hd : d ∈ S.atlas) (p : M)
    (hp : p ∈ c.2.source) (hq : p ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 p))
    (i : activeCoordinates (c.2 p)) (j : activeCoordinates (d.2 p))
    (hij : chartFaceGerm c p i.val = chartFaceGerm d p j.val) :
    ∃ a : ℝ, 0 < a ∧ ∀ v,
      fderiv ℝ H.map (c.2 p).val v j.val = a * v i.val := by
  let e := c.2.symm.trans d.2
  have hcompat := S.maximal.1.2 c hc d hd
  have hxe : c.2 p ∈ e.source := by
    refine ⟨c.2.map_source hp,?_⟩
    change c.2.symm (c.2 p) ∈ d.2.source
    rwa [c.2.left_inv hp]
  obtain ⟨E,hE,hcone,_⟩ := Corners.transition_cone e hcompat.1 hcompat.2 (c.2 p) hxe H
  have hxeq : e (c.2 p) = d.2 p := by
    change d.2 (c.2.symm (c.2 p)) = d.2 p
    rw [c.2.left_inv hp]
  rw [hxeq] at hcone
  obtain ⟨σ,a,ha,hcoord,_⟩ := Corners.cone_facets (c.2 p) (d.2 p) E.toLinearEquiv hcone
  have hs : (σ j).val = i.val := by
    by_contra hne
    have hz := chart_face_germ_derivative_zero c d p hp hq H i j hij (σ j).val hne
    have hr := hcoord (Pi.single (σ j).val 1) j
    change E.toContinuousLinearMap (Pi.single (σ j).val 1) j.val = _ at hr
    rw [hE] at hr
    simp only [Pi.single_eq_same,mul_one] at hr
    exact (ha j).ne' (hr.symm.trans hz)
  refine ⟨a j,ha j,fun v => ?_⟩
  have hh := hcoord v j
  change E.toContinuousLinearMap v j.val = _ at hh
  rwa [hE,hs] at hh


theorem resolved_face_transition_derivative {n : ℕ} {M : Type*} [TopologicalSpace M]
    (S : CornerManifold (n+1) M)
    (c d : CornerChart (n+1) M)
    (i j : Fin (n+1))
    (e f : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : f.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ f.2.source, (f.2 q).val = j.removeNth ((d.2 q.1).val))
    (q : ResolvedFaceSpace S) (hqe : q ∈ e.2.source) (hqf : q ∈ f.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 q.1))
    (K : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 q)) :
    (fderiv ℝ K.map (e.2 q).val).toLinearMap =
      faceDerivative (fderiv ℝ H.map (c.2 q.1).val).toLinearMap i j := by
  let t := e.2.symm.trans f.2
  let T := c.2.symm.trans d.2
  have hrestore (z : t.source) :
      i.insertNth (0 : ℝ) z.val.val = (c.2 (e.2.symm z.val).1).val := by
    have hqe' : e.2.symm z.val ∈ e.2.source := e.2.map_target z.property.1
    have hqc : e.2.symm z.val ∈ faceSheet S c i univ := hes ▸ hqe'
    apply Fin.insertNth_eq_iff.mpr
    refine ⟨hqc.2.2.1.symm, ?_⟩
    have hh := hec (e.2.symm z.val) hqe'
    rw [e.2.right_inv z.property.1] at hh
    exact hh
  have hbase (z : t.source) : c.2 (e.2.symm z.val).1 ∈ T.source := by
    have hqe' : e.2.symm z.val ∈ e.2.source := e.2.map_target z.property.1
    have hqc : e.2.symm z.val ∈ faceSheet S c i univ := hes ▸ hqe'
    have hqd : e.2.symm z.val ∈ faceSheet S d j univ := hfs ▸ z.property.2
    refine ⟨c.2.map_source hqc.2.1, ?_⟩
    change c.2.symm (c.2 (e.2.symm z.val).1) ∈ d.2.source
    rw [c.2.left_inv hqc.2.1]
    exact hqd.2.1
  have htq : e.2 q ∈ t.source := by
    refine ⟨e.2.map_source hqe, ?_⟩
    change e.2.symm (e.2 q) ∈ f.2.source
    rwa [e.2.left_inv hqe]
  have hrestoreq : i.insertNth (0 : ℝ) (e.2 q).val = (c.2 q.1).val := by
    simpa only [e.2.left_inv hqe] using hrestore ⟨e.2 q, htq⟩
  let I : Euclidean n →L[ℝ] Euclidean (n+1) := (faceInsertion i).toContinuousLinearMap
  let D : Euclidean (n+1) →L[ℝ] Euclidean n := (faceDeletion j).toContinuousLinearMap
  let J : OrthantExtension t.source t (e.2 q) := {
    domain := I ⁻¹' H.domain
    isOpen_domain := H.isOpen_domain.preimage I.continuous
    mem_domain := by change i.insertNth 0 (e.2 q).val ∈ H.domain; rw [hrestoreq]; exact H.mem_domain
    map := D ∘ H.map ∘ I
    smooth := D.contDiff.comp_contDiffOn
      (H.smooth.comp I.contDiff.contDiffOn (fun z hz => hz))
    agrees := by
      intro z hz hzJ
      have hqc : e.2.symm z ∈ faceSheet S c i univ :=
        hes ▸ e.2.map_target hz.1
      have hcz : (c.2 (e.2.symm z).1).val ∈ H.domain := by
        change i.insertNth 0 z.val ∈ H.domain at hzJ
        rwa [← hrestore ⟨z,hz⟩]
      have hh := H.agrees (c.2 (e.2.symm z).1) (hbase ⟨z,hz⟩) hcz
      have hT : T (c.2 (e.2.symm z).1) = d.2 (e.2.symm z).1 := by
        dsimp [T]
        rw [c.2.left_inv hqc.2.1]
      change H.map (c.2 (e.2.symm z).1).val = (T (c.2 (e.2.symm z).1)).val at hh
      rw [hT] at hh
      change j.removeNth (H.map (i.insertNth 0 z.val)) = (f.2 (e.2.symm z)).val
      rw [hrestore ⟨z,hz⟩, hh, hfc (e.2.symm z) hz.2] }
  rw [orthant_extension_derivative_unique t (e.2 q) htq K J]
  have hH : DifferentiableAt ℝ H.map (I (e.2 q).val) := by
    change DifferentiableAt ℝ H.map (i.insertNth 0 (e.2 q).val)
    rw [hrestoreq]
    exact (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
      (by simp)
  change (fderiv ℝ (D ∘ H.map ∘ I) (e.2 q).val).toLinearMap = _
  rw [fderiv_comp _ D.differentiableAt (hH.comp _ I.differentiableAt),
    fderiv_comp _ hH I.differentiableAt, D.fderiv, I.fderiv]
  change (D.comp ((fderiv ℝ H.map (i.insertNth 0 (e.2 q).val)).comp I)).toLinearMap = _
  rw [hrestoreq]
  rfl


/-- Compatibility of outward-first signs under actual resolved-sheet transitions,
with sheets identified by actual local boundary germs. -/
theorem resolved_face_coordinate_sign_compatible {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e f : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : f.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ f.2.source, (f.2 q).val = j.removeNth ((d.2 q.1).val))
    (q : ResolvedFaceSpace S) (hqe : q ∈ e.2.source) (hqf : q ∈ f.2.source)
    (hp : q.1 ∈ c.2.source) (hq : q.1 ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 q.1))
    (K : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 q)) :
    faceSign (signValue (o.sign d hd ⟨q.1,hq⟩)) j =
      faceSign (signValue (o.sign c hc ⟨q.1,hp⟩)) i *
        Real.sign (LinearMap.det (fderiv ℝ K.map (e.2 q).val).toLinearMap) := by
  have hcs : q ∈ faceSheet S c i univ := hes ▸ hqe
  have hds : q ∈ faceSheet S d j univ := hfs ▸ hqf
  let ia : activeCoordinates (c.2 q.1) := ⟨i, by
    simp [activeCoordinates, hi, hcs.2.2.1]⟩
  let ja : activeCoordinates (d.2 q.1) := ⟨j, by
    simp [activeCoordinates, hj, hds.2.2.1]⟩
  obtain ⟨a,ha,hrow⟩ := chart_face_germ_normal_row S c d hc hd q.1 hp hq H ia ja
    (hcs.2.2.2.symm.trans hds.2.2.2)
  let A := LinearMap.toMatrix' (fderiv ℝ H.map (c.2 q.1).val).toLinearMap
  have hai : A j i = a := by
    simpa [A, ia, ja] using hrow (Pi.single i 1)
  have hz : ∀ r, r ≠ i → A j r = 0 := by
    intro r hr
    simpa [A, ia, ja, Pi.single_apply, Ne.symm hr] using hrow (Pi.single r 1)
  have hcompat : signValue (o.sign d hd ⟨q.1,hq⟩) =
      signValue (o.sign c hc ⟨q.1,hp⟩) * Real.sign A.det := by
    simpa only [A, LinearMap.det_toMatrix'] using o.compatible c d hc hd q.1 hp hq H
  have h := face_sign_gluing A i j a _ _ ha hai hz hcompat
  have hdK := resolved_face_transition_derivative S c d i j e f hes hfs hec hfc q hqe hqf H K
  rw [← faceDerivative_matrix, LinearMap.det_toMatrix', ← hdK] at h
  exact h

/-- The prescribed face sign is independent of the representation of a resolved chart. -/
theorem resolved_face_coordinate_sign_well_defined {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold (n+1) M} (o : CornerOrientation S)
    (c d : CornerChart (n+1) M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (i j : Fin (n+1)) (hi : i.val < c.1.val) (hj : j.val < d.1.val)
    (e : CornerChart n (ResolvedFaceSpace S))
    (hes : e.2.source = faceSheet S c i univ)
    (hfs : e.2.source = faceSheet S d j univ)
    (hec : ∀ q ∈ e.2.source, (e.2 q).val = i.removeNth ((c.2 q.1).val))
    (hfc : ∀ q ∈ e.2.source, (e.2 q).val = j.removeNth ((d.2 q.1).val))
    (q : ResolvedFaceSpace S) (hqe : q ∈ e.2.source)
    (hp : q.1 ∈ c.2.source) (hq : q.1 ∈ d.2.source)
    (H : OrthantExtension (c.2.symm.trans d.2).source (c.2.symm.trans d.2) (c.2 q.1)) :
    faceSign (signValue (o.sign d hd ⟨q.1,hq⟩)) j =
      faceSign (signValue (o.sign c hc ⟨q.1,hp⟩)) i := by
  let K : OrthantExtension (e.2.symm.trans e.2).source (e.2.symm.trans e.2) (e.2 q) := {
    domain := univ
    isOpen_domain := isOpen_univ
    mem_domain := mem_univ _
    map := id
    smooth := contDiff_id.contDiffOn
    agrees := by
      intro z hz _
      change z.val = (e.2 (e.2.symm z)).val
      rw [e.2.right_inv hz.1] }
  have h := resolved_face_coordinate_sign_compatible o c d hc hd i j hi hj
    e e hes hfs hec hfc q hqe hqe hp hq H K
  simpa [K, fderiv_id] using h

/-- The Boolean form of the outward-first coordinate sign. -/
def outwardFaceBool {n : ℕ} (i : Fin n) (b : Bool) : Bool :=
  if 0 < (-1 : ℝ)^(i.val+1) then b else !b

theorem signValue_outwardFaceBool {n : ℕ} (i : Fin n) (b : Bool) :
    signValue (outwardFaceBool i b) = faceSign (signValue b) i := by
  rcases neg_one_pow_eq_or ℝ (i.val+1) with h | h <;>
    cases b <;> norm_num [outwardFaceBool, faceSign, signValue, h]

/-- Once orientations descend from any generating atlas, genuine resolved-chart
sign gluing constructs the full canonical orientation of every resolved face. -/
theorem resolved_orientation_of_extension
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{u}) :
    Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientationType.{u} := by
  intro n M _ S o
  let A : Set (CornerChart n (ResolvedFaceSpace S)) := {e | IsResolvedFaceChart S e}
  choose c hc i hi hek hes hec using (fun e : A => e.property)
  let incl (e : A) : e.val.2.source → (c e).2.source :=
    fun q => ⟨q.val.1, by
      have hq' : q.val ∈ faceSheet S (c e) (i e) univ :=
        Eq.mp (congrArg (fun U : Set (ResolvedFaceSpace S) => q.val ∈ U) (hes e)) q.property
      exact hq'.2.1⟩
  let s : ∀ e : CornerChart n (ResolvedFaceSpace S), e ∈ A → e.2.source → Bool :=
    fun e he q => outwardFaceBool (i ⟨e,he⟩)
      (o.sign (c ⟨e,he⟩) (hc ⟨e,he⟩) (incl ⟨e,he⟩ q))
  have hs : ∀ e he (q : e.2.source), signValue (s e he q) =
      faceSign (signValue (o.sign (c ⟨e,he⟩) (hc ⟨e,he⟩) (incl ⟨e,he⟩ q)))
        (i ⟨e,he⟩) := by
    intro e he q
    exact signValue_outwardFaceBool _ _
  let a : CornerAtlasOrientation A := {
    sign := s
    locallyConstant := by
      intro e he
      have hinc : Continuous (incl ⟨e,he⟩) :=
        ((Corners.face_projection_continuous S).comp continuous_subtype_val).subtype_mk _
      exact ((o.locallyConstant _ _).comp_continuous hinc).comp (outwardFaceBool _)
    compatible := by
      intro e f he hf q hp hq K
      rw [hs, hs]
      let ee : A := ⟨e,he⟩
      let ff : A := ⟨f,hf⟩
      exact resolved_face_coordinate_sign_compatible o (c ee) (c ff) (hc ee) (hc ff)
        (i ee) (i ff) (hi ee) (hi ff) e f (hes ee) (hes ff) (hec ee) (hec ff)
        q hp hq (incl ee ⟨q,hp⟩).property (incl ff ⟨q,hq⟩).property
        (cornerTransitionExtension (c ee) (c ff) (S.maximal.1.2 _ (hc ee) _ (hc ff))
          q.1 (incl ee ⟨q,hp⟩).property (incl ff ⟨q,hq⟩).property) K }
  obtain ⟨T,hT⟩ := Corners.resolved_corner_structure S
  have hsub : A ⊆ T.atlas := by
    rw [hT]
    exact Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas S)
  obtain ⟨b,hb,_⟩ := extend T A hsub (Corners.resolved_face_atlas S).1 a
  refine ⟨T,b,hT,?_⟩
  intro d hd j hj e he hek' hes' hec' q hq hp
  have heA : e ∈ A := ⟨d,hd,j,hj,hek',hes',hec'⟩
  rw [hb e heA ⟨q,hq⟩]
  change signValue (s e heA ⟨q,hq⟩) = _
  rw [hs]
  let ee : A := ⟨e,heA⟩
  exact (resolved_face_coordinate_sign_well_defined o (c ee) d (hc ee) hd
    (i ee) j (hi ee) hj e (hes ee) hes' (hec ee) hec' q hq
    (incl ee ⟨q,hq⟩).property hp
    (cornerTransitionExtension (c ee) d (S.maximal.1.2 _ (hc ee) _ hd)
      q.1 (incl ee ⟨q,hq⟩).property hp)).symm


/-- Every oriented positive-dimensional corner manifold has its canonical
outward-normal-first orientation on the entire resolved codimension-one face space. -/
theorem resolved_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientationType :=
  resolved_orientation_of_extension orientation_extension

/-- Converting an ordinary chart does not identify distinct charts. -/
theorem ordinaryCornerChart_injective {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (E : CornerProductData.ModelOrthantCoordinates n a) :
    Function.Injective (CornerProductData.ordinaryCornerChart E (M := M)) := by
  intro c d h
  have hpair := (Sigma.mk.inj_iff.mp h).2
  have he : c.trans E.homeomorph.toOpenPartialHomeomorph =
      d.trans E.homeomorph.toOpenPartialHomeomorph := eq_of_heq hpair
  have hback := congrArg (fun e : OpenPartialHomeomorph M (Orthant n (CornerProductData.modelConstraintCount n a)) =>
    e.trans E.homeomorph.toOpenPartialHomeomorph.symm) he
  simpa only [OpenPartialHomeomorph.trans_assoc,
    Homeomorph.toOpenPartialHomeomorph_trans_symm_self,
    OpenPartialHomeomorph.trans_refl] using hback

/-- A genuine converted transition has the original ordinary Jacobian. -/
theorem converted_transition_jacobian {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a)
    (K : TangentBundleData.FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source))
    (H : OrthantExtension
      ((CornerProductData.ordinaryCornerChart E c).2.symm.trans
        (CornerProductData.ordinaryCornerChart E d).2).source
      ((CornerProductData.ordinaryCornerChart E c).2.symm.trans
        (CornerProductData.ordinaryCornerChart E d).2)
      ((CornerProductData.ordinaryCornerChart E c).2 p.val)) :
    transitionDeterminant K c d hc hd p =
      (fderiv ℝ H.map ((CornerProductData.ordinaryCornerChart E c).2 p.val).val).toLinearMap.det := by
  let L := E.linearEquiv
  let F : Euclidean n → Euclidean n := fun z => L.symm (H.map (L z))
  let U := L ⁻¹' H.domain
  have hU : IsOpen U := H.isOpen_domain.preimage L.continuous
  have hpU : (c p.val).val ∈ U := H.mem_domain
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F U :=
    L.symm.contDiff.contDiffOn.comp (H.smooth.comp L.contDiff.contDiffOn
      (fun _ hz => hz)) (mapsTo_univ _ _)
  have hrep : (fun q => F (c q).val) =ᶠ[𝓝 p.val] (fun q => (d q).val) := by
    have hcoord := (continuous_subtype_val.continuousAt.comp
      (c.continuousAt p.property.1)).eventually (hU.mem_nhds hpU)
    filter_upwards [c.open_source.mem_nhds p.property.1,
      d.open_source.mem_nhds p.property.2, hcoord] with q hqc hqd hqU
    let c' := CornerProductData.ordinaryCornerChart E c
    let d' := CornerProductData.ordinaryCornerChart E d
    have hqc' : q ∈ c'.2.source := by
      simpa only [c', CornerProducts.ordinaryCornerChart_source] using hqc
    have hqd' : q ∈ d'.2.source := by
      simpa only [d', CornerProducts.ordinaryCornerChart_source] using hqd
    have hqt : c'.2 q ∈ (c'.2.symm.trans d'.2).source :=
      ⟨c'.2.map_source hqc', by simpa only [OpenPartialHomeomorph.symm_symm,
        mem_preimage, c'.2.left_inv hqc'] using hqd'⟩
    have heq := H.agrees (c'.2 q) hqt hqU
    change H.map (L (c q).val) = (d'.2 (c'.2.symm (c'.2 q))).val at heq
    rw [c'.2.left_inv hqc'] at heq
    change L.symm (H.map (L (c q).val)) = (d q).val
    rw [heq]
    exact L.symm_apply_apply _
  rw [OrientationResults.transition_jacobian S K c d hc hd p U F hU hpU hF hrep]
  have hH := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt
    (by simp)
  have hder := L.symm.hasFDerivAt.comp (c p.val).val
    (hH.hasFDerivAt.comp (c p.val).val L.hasFDerivAt)
  have hdereq : (fderiv ℝ F (c p.val).val).toLinearMap =
      L.symm.toLinearMap.comp
        ((fderiv ℝ H.map (L (c p.val).val)).toLinearMap.comp L.toLinearMap) :=
    congrArg ContinuousLinearMap.toLinearMap hder.fderiv
  rw [hdereq]
  exact LinearMap.det_conj _ L.symm.toLinearEquiv

/-- Replacing the converted charts by equal actual charts preserves the Jacobian. -/
theorem converted_transition_jacobian_of_eq {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a)
    (K : TangentBundleData.FiberCoordinates S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) (e f : CornerChart n M)
    (he : CornerProductData.ordinaryCornerChart E c = e)
    (hf : CornerProductData.ordinaryCornerChart E d = f)
    (H : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 p.val)) :
    transitionDeterminant K c d hc hd p =
      (fderiv ℝ H.map (e.2 p.val).val).toLinearMap.det := by
  subst e
  subst f
  exact converted_transition_jacobian S E K c d hc hd p H

private theorem ordinary_sign_congr {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] {S : AtlasData.SmoothManifold n a M} (s : SignedCharts S)
    (c d : ModelChart n a M) (hcd : c = d) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : c.source) (q : d.source)
    (hpq : p.val = q.val) : s.sign c hc p = s.sign d hd q := by
  subst d
  congr 1
  exact Subtype.ext hpq

/-- Ordinary signed charts give compatible signs on the actual converted atlas. -/
theorem ordinary_generating_orientation {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a) (s : SignedCharts S) :
    ∃ b : CornerAtlasOrientation (CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val),
      ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
        signValue (b.sign (CornerProductData.ordinaryCornerChart E c) ⟨c,hc,rfl⟩
          (ordinaryPoint E c p)) = signValue (s.sign c hc p) *
            Real.sign (LinearMap.det E.linearEquiv.toLinearMap) := by
  let A := CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val
  let D := LinearMap.det E.linearEquiv.toLinearMap
  have hD : D ≠ 0 := by
    simpa only [D, ← LinearEquiv.coe_det] using E.linearEquiv.toLinearEquiv.det.ne_zero
  let chart (e : CornerChart n M) (he : e ∈ A) : ModelChart n a M := he.choose
  have hchart (e : CornerChart n M) (he : e ∈ A) : chart e he ∈ S.smoothStructure.val :=
    he.choose_spec.1
  have hconv (e : CornerChart n M) (he : e ∈ A) :
      CornerProductData.ordinaryCornerChart E (chart e he) = e := he.choose_spec.2
  have hsource (e : CornerChart n M) (he : e ∈ A) : (chart e he).source = e.2.source := by
    rw [← CornerProducts.ordinaryCornerChart_source E (chart e he), hconv]
  let point (e : CornerChart n M) (he : e ∈ A) (p : e.2.source) : (chart e he).source :=
    ⟨p.val, (hsource e he).symm ▸ p.property⟩
  let b : CornerAtlasOrientation A := {
    sign := fun e he p => adjustSign D (s.sign (chart e he) (hchart e he) (point e he p))
    locallyConstant := by
      intro e he
      exact ((s.locallyConstant _ _).comp_continuous
        (continuous_subtype_val.subtype_mk _)).comp (adjustSign D)
    compatible := by
      intro e f he hf p hp hq H
      obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
      let c := chart e he
      let d := chart f hf
      have hpc : p ∈ c.source := (hsource e he).symm ▸ hp
      have hpd : p ∈ d.source := (hsource f hf).symm ▸ hq
      have hjac' := converted_transition_jacobian_of_eq S E K c d
        (hchart e he) (hchart f hf) ⟨p,hpc,hpd⟩ e f (hconv e he) (hconv f hf) H
      have hs := s.compatible K c d (hchart e he) (hchart f hf) ⟨p,hpc,hpd⟩
      change signValue (adjustSign D _) = signValue (adjustSign D _) * _
      rw [signValue_adjustSign hD, signValue_adjustSign hD]
      rw [← hjac']
      simp only [real_sign_eq_signType]
      rw [hs]
      dsimp only [c, d, point]
      ring }
  refine ⟨b, ?_⟩
  intro c hc p
  let e := CornerProductData.ordinaryCornerChart E c
  have he : e ∈ A := ⟨c,hc,rfl⟩
  have hcc : chart e he = c := ordinaryCornerChart_injective E (hconv e he)
  change signValue (adjustSign D (s.sign _ _ _)) = _
  rw [signValue_adjustSign hD]
  congr 1
  exact congrArg signValue (ordinary_sign_congr s _ c hcc _ hc _ p rfl)


/-- The inverse bridge exists on the entire maximal corner atlas. -/
theorem ordinary_orientation_inverse {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a) (R : CornerManifold n M)
    (hsub : CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas)
    (r : Orientation S) : ∃! o : CornerOrientation R, IsOrdinaryOrientation S E R hsub o r := by
  obtain ⟨s, hs, hsu⟩ := (OrientationResults.signed_charts_equivalence S r.val).mp r.property
  obtain ⟨b, hb⟩ := ordinary_generating_orientation S E s
  have hcover := (CornerProducts.ordinary_atlas E S.smoothStructure.property.1).1
  obtain ⟨o, ho, _⟩ := orientation_extension R _ hsub hcover b
  let D := LinearMap.det E.linearEquiv.toLinearMap
  have hD : D ≠ 0 := by
    simpa only [D, ← LinearEquiv.coe_det] using E.linearEquiv.toLinearEquiv.det.ne_zero
  have hsignD : Real.sign D * Real.sign D = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero D hD with h | h <;> simp [h]
  have hor : IsOrdinaryOrientation S E R hsub o r := by
    refine ⟨s,hs,?_⟩
    intro c hc p
    rw [ho (CornerProductData.ordinaryCornerChart E c) ⟨c,hc,rfl⟩ (ordinaryPoint E c p), hb]
    change _ = (_ * Real.sign D) * Real.sign D
    rw [mul_assoc, hsignD, mul_one]
  refine ⟨o, hor, ?_⟩
  intro q hq
  obtain ⟨t,ht,hqt⟩ := hq
  have hts : t = s := hsu t ht
  subst t
  apply cornerOrientation_ext_on_cover q o _ hsub hcover
  rintro e ⟨c,hc,rfl⟩ p
  apply signValue_injective
  have hp : p.val ∈ c.source := by
    simpa only [CornerProducts.ordinaryCornerChart_source] using p.property
  have hq' := hqt c hc ⟨p.val,hp⟩
  obtain ⟨u,hu,hout⟩ := hor
  have hus : u = s := hsu u hu
  subst u
  have ho' := hout c hc ⟨p.val,hp⟩
  exact mul_right_cancel₀ ((mt Real.sign_eq_zero_iff.mp hD)) (hq'.symm.trans ho')

/-- A corner orientation has exactly one corresponding intrinsic ordinary ray field. -/
theorem ordinary_orientation_unique {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a) (R : CornerManifold n M)
    (hsub : CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas)
    (o : CornerOrientation R) (r t : Orientation S)
    (hr : IsOrdinaryOrientation S E R hsub o r)
    (ht : IsOrdinaryOrientation S E R hsub o t) : r = t := by
  obtain ⟨s,hs,hrs⟩ := hr
  obtain ⟨u,hu,htu⟩ := ht
  have hsu : s = u := by
    have hsign : s.sign = u.sign := by
      funext c hc p
      exact signValue_injective ((hrs c hc p).trans (htu c hc p).symm)
    cases s
    cases u
    cases hsign
    rfl
  subst u
  obtain ⟨v,hv,hvu⟩ := OrientationResults.signed_orientation_exists_unique S s
  exact (hvu r hs).trans (hvu t hu).symm

/-- Signed corner coordinates and the original intrinsic determinant rays are equivalent data. -/
theorem ordinary_orientation_equiv {n : ℕ} {a : ModelKind} {M : Type*}
    [TopologicalSpace M] (S : AtlasData.SmoothManifold n a M)
    (E : CornerProductData.ModelOrthantCoordinates n a) (R : CornerManifold n M)
    (hsub : CornerProductData.ordinaryCornerAtlas E S.smoothStructure.val ⊆ R.atlas) :
    ∃ e : CornerOrientation R ≃ Orientation S,
      ∀ o, IsOrdinaryOrientation S E R hsub o (e o) := by
  choose f hf using fun o : CornerOrientation R => ordinary_orientation S E R hsub o
  have hfi : Function.Injective f := by
    intro o q heq
    obtain ⟨v,hv,hvu⟩ := ordinary_orientation_inverse S E R hsub (f o)
    have hq : IsOrdinaryOrientation S E R hsub q (f o) := heq.symm ▸ hf q
    exact (hvu o (hf o)).trans (hvu q hq).symm
  have hfs : Function.Surjective f := by
    intro r
    obtain ⟨o,ho,_⟩ := ordinary_orientation_inverse S E R hsub r
    exact ⟨o, ordinary_orientation_unique S E R hsub o (f o) r (hf o) ho⟩
  exact ⟨Equiv.ofBijective f ⟨hfi,hfs⟩,hf⟩


end SmoothManifolds.CornerFaceOrientations


namespace SmoothManifolds.CornerFaceOrientations
open ModelData CornerData CornerOrientationData OrientationData Set Filter
open scoped Topology
open private uniqueDiffOn_orthantDomain from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Corners.LocalAndResolvedGeometry

def affineChartSign {n : ℕ} (E : Euclidean n ≃ᵃ[ℝ] Euclidean n) : Bool :=
  decide (0 < LinearMap.det E.linear.toLinearMap)

theorem affine_det_ne_zero {n : ℕ} (E : Euclidean n ≃ᵃ[ℝ] Euclidean n) :
    LinearMap.det E.linear.toLinearMap ≠ 0 :=
  E.linear.isUnit_det'.ne_zero

theorem affineChartSign_value {n : ℕ} (E : Euclidean n ≃ᵃ[ℝ] Euclidean n) :
    signValue (affineChartSign E) = Real.sign (LinearMap.det E.linear.toLinearMap) := by
  have hn := affine_det_ne_zero E
  obtain h | h := lt_or_gt_of_ne hn
  · simp [affineChartSign, signValue, Real.sign_of_neg h, not_lt_of_gt h]
  · simp [affineChartSign, signValue, Real.sign_of_pos h, h]

theorem affine_hasFDerivAt {n : ℕ} (E : Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (x : Euclidean n) :
    HasFDerivAt E (LinearMap.toContinuousLinearMap E.linear.toLinearMap) x := by
  rw [show (E : Euclidean n → Euclidean n) =
    fun z => (LinearMap.toContinuousLinearMap E.linear.toLinearMap) z + E 0 from E.toAffineMap.decomp]
  convert (LinearMap.toContinuousLinearMap E.linear.toLinearMap).hasFDerivAt.add_const (E 0) using 1

theorem affine_extension_derivative {n : ℕ} {k l : Fin (n+1)}
    (e : OpenPartialHomeomorph (Orthant n k) (Orthant n l))
    (x : Orthant n k) (hx : x ∈ e.source)
    (H : OrthantExtension e.source e x)
    (E : Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (heq : ∀ z ∈ e.source, (e z).val = E z.val) :
    (fderiv ℝ H.map x.val).toLinearMap = E.linear.toLinearMap := by
  have hd : DifferentiableAt ℝ H.map x.val :=
    (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt (by simp)
  have hHU : ∀ᶠ z in 𝓝 x.val, z ∈ H.domain := H.isOpen_domain.mem_nhds H.mem_domain
  have hevent : H.map =ᶠ[𝓝[Subtype.val '' e.source] x.val] E := by
    filter_upwards [self_mem_nhdsWithin, hHU.filter_mono nhdsWithin_le_nhds] with z hz hzH
    obtain ⟨y, hy, rfl⟩ := hz
    rw [H.agrees y hy hzH, heq y hy]
  have hh := hd.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq hevent.symm
    ((H.agrees x hx H.mem_domain).trans (heq x hx)).symm
  have hu := uniqueDiffOn_orthantDomain e.open_source x.val ⟨x,hx,rfl⟩
  have h := hu.eq hh (affine_hasFDerivAt E x.val).hasFDerivWithinAt
  exact congrArg ContinuousLinearMap.toLinearMap h

private theorem real_sign_mul_affine (x y : ℝ) :
    Real.sign (x*y) = Real.sign x * Real.sign y := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;>
    rcases lt_trichotomy y 0 with hy | rfl | hy
  all_goals try simp only [mul_zero, zero_mul, Real.sign_zero]
  all_goals first
  | simp [Real.sign_of_neg hx, Real.sign_of_neg hy, Real.sign_of_pos (mul_pos_of_neg_of_neg hx hy)]
  | simp [Real.sign_of_neg hx, Real.sign_of_pos hy, Real.sign_of_neg (mul_neg_of_neg_of_pos hx hy)]
  | simp [Real.sign_of_pos hx, Real.sign_of_neg hy, Real.sign_of_neg (mul_neg_of_pos_of_neg hx hy)]
  | simp [Real.sign_of_pos hx, Real.sign_of_pos hy, Real.sign_of_pos (mul_pos hx hy)]

/-- A source-coordinate orientation on any atlas of affine restrictions of a Euclidean subset. -/
def affineCoordinateAtlasOrientation {n : ℕ} {M : Type*} [TopologicalSpace M]
    (A : Set (CornerChart n M)) (q : M → Euclidean n)
    (F : ∀ c, c ∈ A → Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (hF : ∀ c hc (p : M), p ∈ c.2.source → (c.2 p).val = F c hc (q p)) :
    CornerAtlasOrientation A where
  sign c hc _ := affineChartSign (F c hc)
  locallyConstant _ _ := IsLocallyConstant.const _
  compatible c d hc hd p hp hq H := by
    let E := (F c hc).symm.trans (F d hd)
    have hE : ∀ z ∈ (c.2.symm.trans d.2).source,
        ((c.2.symm.trans d.2) z).val = E z.val := by
      intro z hz
      have hzc : z ∈ c.2.target := hz.1
      have hzd : c.2.symm z ∈ d.2.source := hz.2
      have hzc' : c.2.symm z ∈ c.2.source := c.2.map_target hzc
      have hcz : q (c.2.symm z) = (F c hc).symm z.val := by
        apply (F c hc).injective
        rw [← hF c hc _ hzc', c.2.right_inv hzc, AffineEquiv.apply_symm_apply]
      change (d.2 (c.2.symm z)).val = (F d hd) ((F c hc).symm z.val)
      rw [hF d hd _ hzd, hcz]
    have hder := affine_extension_derivative (c.2.symm.trans d.2) (c.2 p)
      ⟨c.2.map_source hp, by
        change c.2.symm (c.2 p) ∈ d.2.source
        rwa [c.2.left_inv hp]⟩ H E hE
    rw [affineChartSign_value, affineChartSign_value, hder]
    change Real.sign (LinearMap.det (F d hd).linear.toLinearMap) =
      Real.sign (LinearMap.det (F c hc).linear.toLinearMap) *
        Real.sign (LinearMap.det ((F d hd).linear.toLinearMap.comp
          (F c hc).linear.symm.toLinearMap))
    rw [LinearMap.det_comp, LinearEquiv.det_coe_symm, real_sign_mul_affine, Real.sign_inv]
    have hs : Real.sign (LinearMap.det (F c hc).linear.toLinearMap) *
        Real.sign (LinearMap.det (F c hc).linear.toLinearMap) = 1 := by
      rcases Real.sign_apply_eq_of_ne_zero _ (affine_det_ne_zero (F c hc)) with h | h <;> rw [h] <;> norm_num
    linear_combination -Real.sign (LinearMap.det (F d hd).linear.toLinearMap) * hs

/-- An affine chart's Jacobian is fixed by its restriction, including at corners. -/
theorem affine_chart_linear_unique {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (q : M → Euclidean n) (F G : Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (hF : ∀ p : M, p ∈ c.2.source → (c.2 p).val = F (q p))
    (hG : ∀ p : M, p ∈ c.2.source → (c.2 p).val = G (q p))
    (p : c.2.source) : F.linear.toLinearMap = G.linear.toLinearMap := by
  let E := G.symm.trans F
  have heq : ∀ z ∈ c.2.target, E z.val = z.val := by
    intro z hz
    have hz' := c.2.map_target hz
    have he : q (c.2.symm z) = G.symm z.val := by
      apply G.injective
      rw [← hG _ hz', c.2.right_inv hz, AffineEquiv.apply_symm_apply]
    change F (G.symm z.val) = z.val
    rw [← he, ← hF _ hz', c.2.right_inv hz]
  have hder := affine_hasFDerivAt E (c.2 p.val).val
  have hevent : E =ᶠ[𝓝[Subtype.val '' c.2.target] (c.2 p.val).val] id := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    obtain ⟨y,hy,rfl⟩ := hz
    exact heq y hy
  have hh := hder.hasFDerivWithinAt.congr_of_eventuallyEq hevent.symm
    (heq _ (c.2.map_source p.property)).symm
  have hu := uniqueDiffOn_orthantDomain c.2.open_target (c.2 p.val).val
    ⟨c.2 p.val,c.2.map_source p.property,rfl⟩
  have hd := congrArg ContinuousLinearMap.toLinearMap
    (hu.eq hh (hasFDerivAt_id _).hasFDerivWithinAt)
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun hd (G.linear v)
  change F.linear (G.linear.symm (G.linear v)) = G.linear v at hv
  simpa using hv

/-- The chosen affine representatives give the actual ambient coordinate signs. -/
theorem affineCoordinateAtlasOrientation_sign {n : ℕ} {M : Type*} [TopologicalSpace M]
    (A : Set (CornerChart n M)) (q : M → Euclidean n)
    (F : ∀ c, c ∈ A → Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (hF : ∀ c hc (p : M), p ∈ c.2.source → (c.2 p).val = F c hc (q p))
    (c : CornerChart n M) (hc : c ∈ A) (p : c.2.source)
    (G : Euclidean n ≃ᵃ[ℝ] Euclidean n)
    (hG : ∀ p : M, p ∈ c.2.source → (c.2 p).val = G (q p)) :
    signValue ((affineCoordinateAtlasOrientation A q F hF).sign c hc p) =
      Real.sign (LinearMap.det G.linear.toLinearMap) := by
  change signValue (affineChartSign (F c hc)) = _
  rw [affineChartSign_value, affine_chart_linear_unique c q _ G (hF c hc) hG p]

end SmoothManifolds.CornerFaceOrientations

namespace SmoothManifolds.CornerFaceOrientations
open ModelData CornerData CornerOrientationData OrientationData CornerExamples Set

def simplexAffineRepresentative {n : ℕ} (c : CornerChart n (Simplex n))
    (hc : c ∈ simplexAtlas n) : Euclidean n ≃ᵃ[ℝ] Euclidean n :=
  omitBarycentricAffineEquiv (Classical.choose hc)

theorem simplexAffineRepresentative_agrees {n : ℕ} (c : CornerChart n (Simplex n))
    (hc : c ∈ simplexAtlas n) (p : Simplex n) (hp : p ∈ c.2.source) :
    (c.2 p).val = simplexAffineRepresentative c hc p.val := by
  let j : Fin (n+1) := Classical.choose hc
  have hj : simplexChart j = c := Classical.choose_spec hc
  change (c.2 p).val = simplexOmitBarycentric j p.val
  rw [← hj] at hp ⊢
  exact simplexCornerChart_apply j p hp

def simplexAtlasOrientation (n : ℕ) : CornerAtlasOrientation (simplexAtlas n) :=
  affineCoordinateAtlasOrientation (simplexAtlas n) Subtype.val simplexAffineRepresentative
    simplexAffineRepresentative_agrees

theorem simplexAtlasOrientation_sign {n : ℕ} (j : Fin (n+1))
    (hc : simplexChart j ∈ simplexAtlas n) (p : (simplexChart j).2.source) :
    signValue ((simplexAtlasOrientation n).sign (simplexChart j) hc p) =
      Real.sign (LinearMap.det (omitBarycentricAffineEquiv j).linear.toLinearMap) := by
  apply affineCoordinateAtlasOrientation_sign
  exact simplexCornerChart_apply j

def boxAffineRepresentative {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (c : CornerChart n (ClosedBox a b)) (hc : c ∈ boxAtlas a b hab) :
    Euclidean n ≃ᵃ[ℝ] Euclidean n :=
  boxCoordinateAffineEquiv a b (Classical.choose hc)

theorem boxAffineRepresentative_agrees {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (c : CornerChart n (ClosedBox a b)) (hc : c ∈ boxAtlas a b hab)
    (p : ClosedBox a b) (_hp : p ∈ c.2.source) :
    (c.2 p).val = boxAffineRepresentative a b hab c hc p.val := by
  let ε : Fin n → Bool := Classical.choose hc
  have hε : (⟨Fin.last n, boxChart a b hab ε⟩ : CornerChart n (ClosedBox a b)) = c :=
    Classical.choose_spec hc
  change (c.2 p).val = boxCoordinate a b ε p.val
  rw [← hε]
  rfl

def boxAtlasOrientation {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i) :
    CornerAtlasOrientation (boxAtlas a b hab) :=
  affineCoordinateAtlasOrientation (boxAtlas a b hab) Subtype.val (boxAffineRepresentative a b hab)
    (boxAffineRepresentative_agrees a b hab)

theorem boxAtlasOrientation_sign {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (ε : Fin n → Bool)
    (hc : (⟨Fin.last n, boxChart a b hab ε⟩ : CornerChart n (ClosedBox a b)) ∈ boxAtlas a b hab)
    (p : (boxChart a b hab ε).source) :
    signValue ((boxAtlasOrientation a b hab).sign ⟨Fin.last n, boxChart a b hab ε⟩ hc p) =
      Real.sign (LinearMap.det (boxCoordinateAffineEquiv a b ε).linear.toLinearMap) := by
  apply affineCoordinateAtlasOrientation_sign
  intros
  rfl


theorem boxCoordinateAffineEquiv_det {n : ℕ} (a b : Euclidean n) (ε : Fin n → Bool) :
    LinearMap.det (boxCoordinateAffineEquiv a b ε).linear.toLinearMap =
      ∏ i, (if ε i then (-1 : ℝ) else 1) := by
  change LinearMap.det (boxCoordinateLinear ε) = _
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  have hmat : LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      (boxCoordinateLinear ε) = Matrix.diagonal (fun i => if ε i then (-1 : ℝ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      cases hε : ε i <;> simp [boxCoordinateLinear, hε]
    · cases hε : ε i <;> simp [boxCoordinateLinear, hε, hij]
  rw [hmat, Matrix.det_diagonal]

/-- The actual interval endpoint charts inherit the positive real-coordinate orientation. -/
def intervalAffineRepresentative {a b : ℝ} {I : CornerManifold 1 (Icc a b)}
    {c : Bool → CornerChart 1 (Icc a b)} (_hI : CornerProductData.IsIntervalChartPair a b I c)
    (d : CornerChart 1 (Icc a b)) (hd : d ∈ range c) : Euclidean 1 ≃ᵃ[ℝ] Euclidean 1 :=
  boxCoordinateAffineEquiv (fun _ => a) (fun _ => b) (fun _ => Classical.choose hd)

theorem intervalAffineRepresentative_agrees {a b : ℝ} {I : CornerManifold 1 (Icc a b)}
    {c : Bool → CornerChart 1 (Icc a b)} (hI : CornerProductData.IsIntervalChartPair a b I c)
    (d : CornerChart 1 (Icc a b)) (hd : d ∈ range c) (p : Icc a b) (_hp : p ∈ d.2.source) :
    (d.2 p).val = intervalAffineRepresentative hI d hd (fun _ => p.val) := by
  let t : Bool := Classical.choose hd
  have ht : c t = d := Classical.choose_spec hd
  change (d.2 p).val = boxCoordinate (fun _ => a) (fun _ => b) (fun _ => t) (fun _ => p.val)
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  rw [hi, ← ht, (hI.1 t).2.2.2 p]
  rfl

def intervalAtlasOrientation {a b : ℝ} {I : CornerManifold 1 (Icc a b)}
    {c : Bool → CornerChart 1 (Icc a b)} (hI : CornerProductData.IsIntervalChartPair a b I c) :
    CornerAtlasOrientation (range c) :=
  affineCoordinateAtlasOrientation (range c) (fun p _ => p.val) (intervalAffineRepresentative hI)
    (intervalAffineRepresentative_agrees hI)

theorem intervalAtlasOrientation_sign {a b : ℝ} {I : CornerManifold 1 (Icc a b)}
    {c : Bool → CornerChart 1 (Icc a b)} (hI : CornerProductData.IsIntervalChartPair a b I c)
    (s : Bool) (hc : c s ∈ range c) (p : (c s).2.source) :
    signValue ((intervalAtlasOrientation hI).sign (c s) hc p) = if s then (-1 : ℝ) else 1 := by
  have hsign := affineCoordinateAtlasOrientation_sign (range c) (fun p _ => p.val)
    (intervalAffineRepresentative hI) (intervalAffineRepresentative_agrees hI)
    (c s) hc p (boxCoordinateAffineEquiv (fun _ => a) (fun _ => b) (fun _ => s)) (by
      intro p hp
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi, (hI.1 s).2.2.2 p]
      rfl)
  change signValue ((intervalAtlasOrientation hI).sign (c s) hc p) = _ at hsign
  rw [boxCoordinateAffineEquiv_det] at hsign
  cases s <;> norm_num [Fin.prod_univ_one, Real.sign] at hsign ⊢ <;> exact hsign

theorem omitBarycentricAffineEquiv_det {n : ℕ} (j : Fin (n+1)) :
    LinearMap.det (omitBarycentricAffineEquiv j).linear.toLinearMap = (-1 : ℝ)^j.val := by
  let B : Matrix (Fin (n+1)) (Fin n) ℝ :=
    fun r i => (barycentricLinear n) (Pi.single i 1) r
  have hB : ∑ r, B r = 0 := by
    ext i
    simp [B, barycentricLinear, Fin.sum_univ_succ]
  have hzero : B.submatrix (Fin.succAbove 0) id = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i r
    change (Pi.single r (1 : ℝ) : Fin n → ℝ) i = if i = r then 1 else 0
    by_cases hir : i = r
    · subst r
      simp
    · simp [hir]
  have hmat : LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
      (omitBarycentricAffineEquiv j).linear.toLinearMap = B.submatrix j.succAbove id := by
    ext r i
    rfl
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n)), hmat]
  rw [Matrix.submatrix_succAbove_det_eq_negOnePow_submatrix_succAbove_det B hB j 0, hzero]
  simp only [Fin.val_zero, Nat.cast_zero, sub_zero, Matrix.det_one]
  rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul, mul_one]
  exact Int.cast_negOnePow_natCast ℝ j.val

theorem real_sign_neg_one_pow_affine (k : ℕ) : Real.sign ((-1 : ℝ)^k) = (-1 : ℝ)^k := by
  induction k with
  | zero => simp
  | succ k hk => simp only [pow_succ, mul_neg_one, Real.sign_neg, hk]

theorem simplexAtlasOrientation_sign_explicit {n : ℕ} (j : Fin (n+1))
    (hc : simplexChart j ∈ simplexAtlas n) (p : (simplexChart j).2.source) :
    signValue ((simplexAtlasOrientation n).sign (simplexChart j) hc p) = (-1 : ℝ)^j.val := by
  rw [simplexAtlasOrientation_sign, omitBarycentricAffineEquiv_det, real_sign_neg_one_pow_affine]

theorem real_sign_prod_bool {ι : Type*} [DecidableEq ι] (s : Finset ι) (ε : ι → Bool) :
    Real.sign (∏ i ∈ s, if ε i then (-1 : ℝ) else 1) =
      ∏ i ∈ s, if ε i then (-1 : ℝ) else 1 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, real_sign_mul_affine, ih]
    cases ε a <;> norm_num [Real.sign]

theorem boxAtlasOrientation_sign_explicit {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i ≤ b i)
    (ε : Fin n → Bool)
    (hc : (⟨Fin.last n, boxChart a b hab ε⟩ : CornerChart n (ClosedBox a b)) ∈ boxAtlas a b hab)
    (p : (boxChart a b hab ε).source) :
    signValue ((boxAtlasOrientation a b hab).sign ⟨Fin.last n, boxChart a b hab ε⟩ hc p) =
      ∏ i, (if ε i then (-1 : ℝ) else 1) := by
  rw [boxAtlasOrientation_sign, boxCoordinateAffineEquiv_det]
  exact real_sign_prod_bool Finset.univ ε

private theorem bool_sign_injective_affine : Function.Injective (signValue : Bool → ℝ) := by
  intro a b h
  cases a <;> cases b <;> norm_num [signValue] at *

universe u

/-- Descent also gives uniqueness when chart signs are stated as real signs. -/
theorem orientation_extension_indexed
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M] (S : CornerManifold n M)
    {ι : Type*} (c : ι → CornerChart n M) (hsub : range c ⊆ S.atlas)
    (hcover : ∀ p : M, ∃ j, p ∈ (c j).2.source)
    (a : CornerAtlasOrientation (range c)) (s : ι → ℝ)
    (ha : ∀ j (hc : c j ∈ range c) (p : (c j).2.source), signValue (a.sign (c j) hc p) = s j) :
    ∃! o : CornerOrientation S, ∀ j (hc : c j ∈ S.atlas) (p : (c j).2.source),
      signValue (o.sign (c j) hc p) = s j := by
  obtain ⟨o,ho,huniq⟩ := extend S (range c) hsub (by
    intro p
    obtain ⟨j,hj⟩ := hcover p
    exact ⟨c j,mem_range_self j,hj⟩) a
  refine ⟨o,?_,?_⟩
  · intro j hc p
    exact (congrArg (signValue : Bool → ℝ) (ho (c j) (mem_range_self j) p)).trans
      (ha j (mem_range_self j) p)
  · intro o' ho'
    apply huniq o'
    intro d hd p
    obtain ⟨j,hj⟩ := hd
    subst d
    apply bool_sign_injective_affine
    exact (ho' j _ p).trans (ha j (mem_range_self j) p).symm

end SmoothManifolds.CornerFaceOrientations




namespace SmoothManifolds.CornerFaceOrientations
open ModelData CornerData CornerOrientationData OrientationData CornerExamples Set

theorem simplex_source_orientation_of_extension
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{0}) :
    ∀ n : ℕ, ∃ S : CornerManifold n (Simplex n),
      S.atlas = cornerMaximalExtension (simplexAtlas n) ∧
      ∃! o : CornerOrientation S, ∀ j : Fin (n+1),
        ∀ (hc : simplexChart j ∈ S.atlas) (p : (simplexChart j).2.source),
          signValue (o.sign (simplexChart j) hc p) = (-1 : ℝ)^j.val := by
  intro n
  refine ⟨simplexCornerManifold n, rfl, ?_⟩
  exact orientation_extension_indexed extend (simplexCornerManifold n) simplexChart
    (by rintro _ ⟨j,rfl⟩; exact simplexChart_mem_atlas j)
    simplexCornerChart_cover (simplexAtlasOrientation n) (fun j => (-1 : ℝ)^j.val)
    simplexAtlasOrientation_sign_explicit

theorem box_source_orientation_of_extension
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{0}) :
    ∀ {n : ℕ} (a b : Euclidean n) (hab : ∀ i, a i < b i),
      ∃ S : CornerManifold n (ClosedBox a b),
        S.atlas = cornerMaximalExtension (boxAtlas a b (fun i => (hab i).le)) ∧
        ∃! o : CornerOrientation S, ∀ ε : Fin n → Bool,
          ∀ (hc : (⟨Fin.last n, boxChart a b (fun i => (hab i).le) ε⟩ :
            CornerChart n (ClosedBox a b)) ∈ S.atlas)
            (p : (boxChart a b (fun i => (hab i).le) ε).source),
            signValue (o.sign ⟨Fin.last n, boxChart a b (fun i => (hab i).le) ε⟩ hc p) =
              ∏ i, (if ε i then (-1 : ℝ) else 1) := by
  intro n a b hab
  let hle : ∀ i, a i ≤ b i := fun i => (hab i).le
  let S : CornerManifold n (ClosedBox a b) :=
    ⟨inferInstance, inferInstance, cornerMaximalExtension (boxAtlas a b hle),
      Corners.cornerMaximalExtension_isMaximal (boxAtlas_isSmooth a b hab)⟩
  let c : (Fin n → Bool) → CornerChart n (ClosedBox a b) :=
    fun ε => ⟨Fin.last n, boxChart a b hle ε⟩
  refine ⟨S,rfl,?_⟩
  refine orientation_extension_indexed extend S c
    (Corners.cornerAtlas_subset_maximalExtension (boxAtlas_isSmooth a b hab)) ?_
    (boxAtlasOrientation a b hle) (fun ε => ∏ i, if ε i then (-1 : ℝ) else 1)
    (boxAtlasOrientation_sign_explicit a b hle)
  intro p
  obtain ⟨d,⟨ε,rfl⟩,hp⟩ := boxAtlas_cover a b hab p
  exact ⟨ε,hp⟩

theorem interval_source_orientation_of_extension
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{0}) :
    Specs.SmoothManifolds.Corners.FaceOrientations.interval_source_orientationType := by
  intro a b hab I c hI
  obtain ⟨o,ho,huniq⟩ := orientation_extension_indexed extend I c
    (by rintro _ ⟨s,rfl⟩; exact (hI.1 s).1)
    hI.2.1 (intervalAtlasOrientation hI) (fun s => if s then (-1 : ℝ) else 1)
    (intervalAtlasOrientation_sign hI)
  refine ⟨o,⟨ho,?_⟩,fun o' ho' => huniq o' ho'.1⟩
  intro s
  let p : Icc a b := if s then ⟨b,hab.le,le_rfl⟩ else ⟨a,le_rfl,hab.le⟩
  have hp : p ∈ (c s).2.source := by
    rw [(hI.1 s).2.2.1]
    cases s <;> simpa [p] using hab
  refine ⟨⟨p,hp⟩,?_,?_⟩
  · cases s <;> rfl
  · rw [ho s (hI.1 s).1]
    cases s <;> norm_num [faceSign]

end SmoothManifolds.CornerFaceOrientations


namespace SmoothManifolds.CornerFaceOrientations
open ModelData CornerData CornerOrientationData OrientationData CornerExamples Set

theorem interval_resolved_endpoints_of_extension
    (extend : Specs.SmoothManifolds.Corners.FaceOrientations.orientation_extensionType.{0})
    (resolve : Specs.SmoothManifolds.Corners.FaceOrientations.resolved_orientationType.{0}) :
    Specs.SmoothManifolds.Corners.FaceOrientations.interval_resolved_endpointsType := by
  intro a b hab I c hI
  obtain ⟨o,ho,_⟩ := interval_source_orientation_of_extension extend a b hab I c hI
  obtain ⟨T,bdy,hbdy⟩ := resolve o
  refine ⟨o,T,bdy,ho.1,hbdy,?_⟩
  intro s
  obtain ⟨p,hpend,hpsign⟩ := ho.2 s
  have hzero : ((c s).2 p.val).val (0 : Fin 1) = 0 := by
    rw [(hI.1 s).2.2.2 p.val, hpend]
    cases s <;> simp
  have hi : (0 : Fin 1).val < (c s).1.val := by rw [(hI.1 s).2.1]; decide
  let r : ChartFacePatch (c s) (0 : Fin 1) := ⟨p.val,p.property,hzero⟩
  obtain ⟨f,hf,hfcoords⟩ := Corners.exists_resolvedFaceChart I (c s) (hI.1 s).1 0 hi r
  let e : CornerChart 0 (ResolvedFaceSpace I) := ⟨faceConstraintCount (c s).1,f⟩
  have he : e ∈ T.atlas := by
    rw [hbdy.1]
    apply Corners.cornerAtlas_subset_maximalExtension (Corners.resolved_face_atlas I)
    exact ⟨c s,(hI.1 s).1,0,hi,rfl,hf,hfcoords⟩
  let q := chartFaceLift I (c s) (hI.1 s).1 0 hi r
  have hq : q ∈ e.2.source := by
    change q ∈ f.source
    rw [hf]
    exact ⟨mem_univ _,p.property,hzero,rfl⟩
  refine ⟨e,he,⟨q,hq⟩,hpend,hf,?_⟩
  have hsign := hbdy.2 (c s) (hI.1 s).1 0 hi e he rfl hf hfcoords q hq p.property
  exact hsign.trans hpsign

end SmoothManifolds.CornerFaceOrientations

namespace SmoothManifolds.CornerFaceOrientations

open ModelData CornerData CornerOrientationData OrientationData CornerExamples Set

/-- The ordered standard simplex has its ambient source coordinate orientation. -/
theorem simplex_source_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.simplex_source_orientationType := by
  intro n
  obtain ⟨S,hS,ho⟩ := simplex_source_orientation_of_extension orientation_extension n
  refine ⟨S,simplexChart,hS,?_,simplexCornerChart_cover,?_,simplex_charts_affine n,ho⟩
  · intro j
    refine ⟨?_,rfl,simplexCornerChart_source j,simplexCornerChart_target j,
      simplexCornerChart_apply j,simplexCornerChart_symm_apply j⟩
    rw [hS]
    exact Corners.cornerAtlas_subset_maximalExtension (simplexAtlas_isSmooth n) (mem_range_self j)
  · intro j
    exact ⟨contDiff_omitBarycentric j,contDiff_restoreBarycentric j⟩

/-- Every nondegenerate standard box has its ambient source coordinate orientation. -/
theorem box_source_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.box_source_orientationType := by
  intro n a b hab
  obtain ⟨S,hS,ho⟩ := box_source_orientation_of_extension orientation_extension a b hab
  let hle : ∀ i, a i ≤ b i := fun i => (hab i).le
  let c : (Fin n → Bool) → CornerChart n (ClosedBox a b) :=
    fun ε => ⟨Fin.last n,boxChart a b hle ε⟩
  refine ⟨S,c,hS,?_,?_,?_,ho⟩
  · intro ε
    refine ⟨?_,rfl,rfl,rfl,fun _ => rfl,?_⟩
    · rw [hS]
      exact Corners.cornerAtlas_subset_maximalExtension (boxAtlas_isSmooth a b hab) (mem_range_self ε)
    · intro y hy
      exact boxInv_eq a b hle ε y hy
  · intro x
    obtain ⟨d,⟨ε,rfl⟩,hx⟩ := boxAtlas_cover a b hab x
    exact ⟨ε,hx⟩
  · intro ε
    refine ⟨boxCoordinateAffineEquiv a b ε,boxCoordinateAffineEquiv_apply a b ε,
      boxCoordinateAffineEquiv_symm_apply a b ε,boxCoordinate_smooth a b ε,?_⟩
    simpa only [boxCoordinateAffineEquiv_symm_apply] using boxInverseCoordinate_smooth a b ε

/-- The positive real interval has its standard chart and outward endpoint signs. -/
theorem interval_source_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.interval_source_orientationType :=
  interval_source_orientation_of_extension orientation_extension

/-- The canonical orientation on the actual resolved interval faces is negative at a and positive at b. -/
theorem interval_resolved_endpoints :
    Specs.SmoothManifolds.Corners.FaceOrientations.interval_resolved_endpointsType :=
  interval_resolved_endpoints_of_extension orientation_extension resolved_orientation

/-- The standard signed ray is exactly its positive coordinate multiples. -/
theorem standardRayEquiv_positive_iff {n : ℕ} (b : Bool)
    (v : ⋀[ℝ]^n (Euclidean n)) :
    IsPositive (OrientationResults.standardRayEquiv n b) v ↔
      CoordinatePositive b v := by
  have hz : signValue b • coordinateVolume n ≠ 0 :=
    smul_ne_zero (OrientationResults.signValue_ne_zero b) (coordinateVolume_ne_zero n)
  have he : OrientationResults.standardRayEquiv n b =
      rayOfNeZero ℝ (signValue b • coordinateVolume n) hz := by
    cases b
    · change -rayOfNeZero ℝ (coordinateVolume n) (coordinateVolume_ne_zero n) =
        rayOfNeZero ℝ ((-1 : ℝ) • coordinateVolume n) hz
      rw [neg_rayOfNeZero ℝ (coordinateVolume n) (coordinateVolume_ne_zero n)]
      apply (ray_eq_iff _ hz).mpr
      change SameRay ℝ (-coordinateVolume n) ((-1 : ℝ) • coordinateVolume n)
      rw [neg_one_smul ℝ (coordinateVolume n)]
    · change rayOfNeZero ℝ (coordinateVolume n) (coordinateVolume_ne_zero n) =
        rayOfNeZero ℝ ((1 : ℝ) • coordinateVolume n) hz
      apply (ray_eq_iff _ hz).mpr
      change SameRay ℝ (coordinateVolume n) ((1 : ℝ) • coordinateVolume n)
      rw [one_smul ℝ (coordinateVolume n)]

  rw [he]
  constructor
  · rintro ⟨hv,hv'⟩
    exact ((ray_eq_iff hv hz).mp hv').exists_pos_right hv hz
  · rintro ⟨a,ha,rfl⟩
    refine ⟨smul_ne_zero ha.ne' hz, ?_⟩
    exact (ray_eq_iff _ hz).mpr (SameRay.sameRay_pos_smul_left _ ha)



open CornerProductData OrientationProductData OrientationProducts

@[simp] theorem standardRayEquiv_not (n : ℕ) (b : Bool) :
    OrientationResults.standardRayEquiv n (!b) = -(OrientationResults.standardRayEquiv n b) := by
  cases b <;> simp [OrientationResults.standardRayEquiv, OrientationResults.raySignEquiv]

/-- Signed Euclidean determinant rays transform by the Jacobian sign. -/
theorem standardRayEquiv_map_iff {n : ℕ} (E : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (b c : Bool) :
    Module.Ray.map (determinantMap n E) (OrientationResults.standardRayEquiv n b) =
      OrientationResults.standardRayEquiv n c ↔
    signValue c = signValue b * Real.sign E.toLinearMap.det := by
  have hn := E.isUnit_det'.ne_zero
  rw [← signValue_adjustSign hn b, signValue_injective.eq_iff]
  rw [OrientationProducts.topExterior_ray_map]
  have he : (if 0 < E.toLinearMap.det then OrientationResults.standardRayEquiv n b
      else -(OrientationResults.standardRayEquiv n b)) =
      OrientationResults.standardRayEquiv n (adjustSign E.toLinearMap.det b) := by
    by_cases h : 0 < E.toLinearMap.det <;> simp [adjustSign, h]
  rw [he, Equiv.apply_eq_iff_eq]
  exact eq_comm

/-- Ambient invertible derivative realizing a genuine chart transition. -/
def cornerTransitionEquiv {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    Euclidean n ≃L[ℝ] Euclidean n := by
  let H := cornerTransitionExtension c d h p hp hq
  have hx : c.2 p ∈ (c.2.symm.trans d.2).source := by
    refine ⟨c.2.map_source hp, ?_⟩
    change c.2.symm (c.2 p) ∈ d.2.source
    rwa [c.2.left_inv hp]
  exact (Corners.transition_cone _ h.1 h.2 (c.2 p) hx H).choose

theorem cornerTransitionEquiv_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c d : CornerChart n M) (h : CornerCompatible c d)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    (cornerTransitionEquiv c d h p hp hq).toContinuousLinearMap =
      cornerTransitionDerivative c d h p hp hq := by
  exact (Corners.transition_cone _ h.1 h.2 (c.2 p)
    (show c.2 p ∈ (c.2.symm.trans d.2).source from
      ⟨c.2.map_source hp, by change c.2.symm (c.2 p) ∈ d.2.source; rwa [c.2.left_inv hp]⟩)
    (cornerTransitionExtension c d h p hp hq)).choose_spec.1

/-- Actual ambient extension of a product transition obtained from the two
factor extensions and the prescribed ordered coordinate identifications. -/
def productTransitionExtension {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m n) (c c' : CornerChart m M) (d d' : CornerChart n N)
    (p : M × N) (hp : p ∈ (productChart C c d).2.source)
    (hq : p ∈ (productChart C c' d').2.source)
    (H : OrthantExtension (c.2.symm.trans c'.2).source (c.2.symm.trans c'.2) (c.2 p.1))
    (G : OrthantExtension (d.2.symm.trans d'.2).source (d.2.symm.trans d'.2) (d.2 p.2)) :
    OrthantExtension ((productChart C c d).2.symm.trans (productChart C c' d').2).source
      ((productChart C c d).2.symm.trans (productChart C c' d').2)
      ((productChart C c d).2 p) := by
  let L := (C c.1 d.1).linearEquiv
  let L' := (C c'.1 d'.1).linearEquiv
  let U := L.symm ⁻¹' (H.domain ×ˢ G.domain)
  refine ⟨U,(H.isOpen_domain.prod G.isOpen_domain).preimage L.symm.continuous,?_,
    fun z => L' (H.map (L.symm z).1,G.map (L.symm z).2),?_,?_⟩
  · change L.symm (L ((c.2 p.1).val,(d.2 p.2).val)) ∈ H.domain ×ˢ G.domain
    rw [L.symm_apply_apply]
    exact ⟨H.mem_domain,G.mem_domain⟩
  · exact L'.contDiff.contDiffOn.comp
      ((H.smooth.comp L.symm.contDiff.fst.contDiffOn (fun _ hz => hz.1)).prodMk
       (G.smooth.comp L.symm.contDiff.snd.contDiffOn (fun _ hz => hz.2))) (mapsTo_univ _ _)
  · intro z hz hzU
    let q := (productChart C c d).2.symm z
    have hq0 : q ∈ c.2.source ×ˢ d.2.source := by
      rw [← CornerProducts.productChart_source C c d]
      exact (productChart C c d).2.map_target hz.1
    have hq1 : q ∈ c'.2.source ×ˢ d'.2.source := by
      rw [← CornerProducts.productChart_source C c' d']
      exact hz.2
    have hqH : c.2 q.1 ∈ (c.2.symm.trans c'.2).source := by
      refine ⟨c.2.map_source hq0.1,?_⟩
      change c.2.symm (c.2 q.1) ∈ c'.2.source
      rw [c.2.left_inv hq0.1]
      exact hq1.1
    have hqG : d.2 q.2 ∈ (d.2.symm.trans d'.2).source := by
      refine ⟨d.2.map_source hq0.2,?_⟩
      change d.2.symm (d.2 q.2) ∈ d'.2.source
      rw [d.2.left_inv hq0.2]
      exact hq1.2
    have hzL := CornerProducts.productChart_inverse C c d z hz.1
    change L.symm z.val = ((c.2 q.1).val,(d.2 q.2).val) at hzL
    change L.symm z.val ∈ H.domain ×ˢ G.domain at hzU
    rw [hzL] at hzU
    change L' (H.map (L.symm z.val).1,G.map (L.symm z.val).2) =
      ((productChart C c' d').2 q).val
    rw [hzL,H.agrees (c.2 q.1) hqH hzU.1,G.agrees (d.2 q.2) hqG hzU.2]
    change L' ((c'.2 (c.2.symm (c.2 q.1))).val,(d'.2 (d.2.symm (d.2 q.2))).val) = _
    rw [c.2.left_inv hq0.1,d.2.left_inv hq0.2]
    rfl

/-- Derivative of the genuine product transition extension is the ordered
factor derivative splitting in the actual product coordinates. -/
theorem productTransitionExtension_fderiv {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m n) (c c' : CornerChart m M) (d d' : CornerChart n N)
    (p : M × N) (hp : p ∈ (productChart C c d).2.source)
    (hq : p ∈ (productChart C c' d').2.source)
    (H : OrthantExtension (c.2.symm.trans c'.2).source (c.2.symm.trans c'.2) (c.2 p.1))
    (G : OrthantExtension (d.2.symm.trans d'.2).source (d.2.symm.trans d'.2) (d.2 p.2)) :
    fderiv ℝ (productTransitionExtension C c c' d d' p hp hq H G).map
        ((productChart C c d).2 p).val =
      (C c'.1 d'.1).linearEquiv.toContinuousLinearMap.comp
        (((fderiv ℝ H.map (c.2 p.1).val).prodMap
          (fderiv ℝ G.map (d.2 p.2).val)).comp
            (C c.1 d.1).linearEquiv.symm.toContinuousLinearMap) := by
  have hH := (H.smooth.contDiffAt (H.isOpen_domain.mem_nhds H.mem_domain)).differentiableAt (by simp)
  have hG := (G.smooth.contDiffAt (G.isOpen_domain.mem_nhds G.mem_domain)).differentiableAt (by simp)
  have hHx : HasFDerivAt H.map (fderiv ℝ H.map (c.2 p.1).val)
      ((C c.1 d.1).linearEquiv.symm ((productChart C c d).2 p).val).1 := by
    simpa only [CornerProducts.productChart_val, ContinuousLinearEquiv.symm_apply_apply] using hH.hasFDerivAt
  have hGx : HasFDerivAt G.map (fderiv ℝ G.map (d.2 p.2).val)
      ((C c.1 d.1).linearEquiv.symm ((productChart C c d).2 p).val).2 := by
    simpa only [CornerProducts.productChart_val, ContinuousLinearEquiv.symm_apply_apply] using hG.hasFDerivAt
  exact (CornerProducts.transition_derivative (C c.1 d.1) (C c'.1 d'.1)
    H.map G.map ((productChart C c d).2 p).val _ _ hHx hGx).fderiv


/-- Ordered factor rays transported by the actual product coordinate map. -/
def productCoordinateRay {m n : ℕ} {k : Fin (m+1)} {l : Fin (n+1)}
    (C : OrthantProductCoordinates m n k l) (b c : Bool) :
    Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean (m+n))) :=
  Module.Ray.map (determinantMap (m+n) C.linearEquiv.toLinearEquiv)
    (OrientationProducts.orderedProductRay (by simp) (by simp)
      (OrientationResults.standardRayEquiv m b) (OrientationResults.standardRayEquiv n c))

/-- The orientation compatibility law is equivalent to transport of the two
actual determinant rays in chart coordinates. -/
theorem cornerOrientation_coordinate_ray_transport {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : CornerManifold n M} (o : CornerOrientation S)
    (c d : CornerChart n M) (hc : c ∈ S.atlas) (hd : d ∈ S.atlas)
    (p : M) (hp : p ∈ c.2.source) (hq : p ∈ d.2.source) :
    Module.Ray.map (determinantMap n
      (cornerTransitionEquiv c d (S.maximal.1.2 c hc d hd) p hp hq).toLinearEquiv)
        (OrientationResults.standardRayEquiv n (o.sign c hc ⟨p,hp⟩)) =
      OrientationResults.standardRayEquiv n (o.sign d hd ⟨p,hq⟩) := by
  apply (standardRayEquiv_map_iff _ _ _).mpr
  have h := o.compatible c d hc hd p hp hq
    (cornerTransitionExtension c d (S.maximal.1.2 c hc d hd) p hp hq)
  have he := cornerTransitionEquiv_eq c d (S.maximal.1.2 c hc d hd) p hp hq
  have heL := congrArg ContinuousLinearMap.toLinearMap he
  change (cornerTransitionEquiv c d (S.maximal.1.2 c hc d hd) p hp hq).toLinearMap =
    (cornerTransitionDerivative c d (S.maximal.1.2 c hc d hd) p hp hq).toLinearMap at heL
  rw [heL]
  exact h

/-- The ambient derivative on products is the actual ordered factor splitting,
for every ambient representative of the given chart transition. -/
theorem productTransitionEquiv_derivative {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N) (C : ProductCoordinateFamily m n)
    (c c' : CornerChart m M) (d d' : CornerChart n N)
    (hc : c ∈ S.atlas) (hc' : c' ∈ S.atlas) (hd : d ∈ T.atlas) (hd' : d' ∈ T.atlas)
    (p : M × N) (hp : p ∈ (productChart C c d).2.source)
    (hq : p ∈ (productChart C c' d').2.source)
    (K : OrthantExtension ((productChart C c d).2.symm.trans (productChart C c' d').2).source
      ((productChart C c d).2.symm.trans (productChart C c' d').2)
      ((productChart C c d).2 p)) :
    let hp0 : p ∈ c.2.source ×ˢ d.2.source := (CornerProducts.productChart_source C c d) ▸ hp
    let hq0 : p ∈ c'.2.source ×ˢ d'.2.source := (CornerProducts.productChart_source C c' d') ▸ hq
    let E := cornerTransitionEquiv c c' (S.maximal.1.2 c hc c' hc') p.1 hp0.1 hq0.1
    let F := cornerTransitionEquiv d d' (T.maximal.1.2 d hd d' hd') p.2 hp0.2 hq0.2
    let A := (C c.1 d.1).linearEquiv.symm.trans
      ((E.prodCongr F).trans (C c'.1 d'.1).linearEquiv)
    A.toContinuousLinearMap = fderiv ℝ K.map ((productChart C c d).2 p).val := by
  dsimp only
  let hp0 : p ∈ c.2.source ×ˢ d.2.source := (CornerProducts.productChart_source C c d) ▸ hp
  let hq0 : p ∈ c'.2.source ×ˢ d'.2.source := (CornerProducts.productChart_source C c' d') ▸ hq
  let H := cornerTransitionExtension c c' (S.maximal.1.2 c hc c' hc') p.1 hp0.1 hq0.1
  let G := cornerTransitionExtension d d' (T.maximal.1.2 d hd d' hd') p.2 hp0.2 hq0.2
  let J := productTransitionExtension C c c' d d' p hp hq H G
  have hxp : (productChart C c d).2 p ∈
      ((productChart C c d).2.symm.trans (productChart C c' d').2).source := by
    refine ⟨(productChart C c d).2.map_source hp,?_⟩
    change (productChart C c d).2.symm ((productChart C c d).2 p) ∈ (productChart C c' d').2.source
    rwa [(productChart C c d).2.left_inv hp]
  rw [← orthant_extension_derivative_unique _ _ hxp J K,
    productTransitionExtension_fderiv C c c' d d' p hp hq H G]
  have hE := cornerTransitionEquiv_eq c c' (S.maximal.1.2 c hc c' hc') p.1 hp0.1 hq0.1
  have hF := cornerTransitionEquiv_eq d d' (T.maximal.1.2 d hd d' hd') p.2 hp0.2 hq0.2
  change (cornerTransitionEquiv c c' (S.maximal.1.2 c hc c' hc') p.1 hp0.1 hq0.1).toContinuousLinearMap =
    fderiv ℝ H.map (c.2 p.1).val at hE
  change (cornerTransitionEquiv d d' (T.maximal.1.2 d hd d' hd') p.2 hp0.2 hq0.2).toContinuousLinearMap =
    fderiv ℝ G.map (d.2 p.2).val at hF
  rw [← hE,← hF]
  rfl

theorem coordinate_product_ray_natural {m n : ℕ}
    (C0 C1 : (Euclidean m × Euclidean n) ≃ₗ[ℝ] Euclidean (m+n))
    (E : Euclidean m ≃ₗ[ℝ] Euclidean m) (F : Euclidean n ≃ₗ[ℝ] Euclidean n)
    (r : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
    (s : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n))) :
    let A := C0.symm.trans ((E.prodCongr F).trans C1)
    Module.Ray.map (determinantMap (m+n) A)
        (Module.Ray.map (determinantMap (m+n) C0)
          (orderedProductRay (by simp) (by simp) r s)) =
      Module.Ray.map (determinantMap (m+n) C1)
        (orderedProductRay (by simp) (by simp)
          (Module.Ray.map (determinantMap m E) r)
          (Module.Ray.map (determinantMap n F) s)) := by
  dsimp only
  rw [← rayMap_trans, ← determinantMap_trans]
  have he : C0.trans (C0.symm.trans ((E.prodCongr F).trans C1)) =
      (E.prodCongr F).trans C1 := by
    ext v
    simp
  rw [he, determinantMap_trans, rayMap_trans,
    orderedProductRay_natural (by simp) (by simp) (by simp) (by simp)]


/-- Product chart determinant rays transport under every genuine ambient
representative of the transition. -/
theorem productCoordinateRay_transport {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (c c' : CornerChart m M) (d d' : CornerChart n N)
    (hc : c ∈ S.atlas) (hc' : c' ∈ S.atlas) (hd : d ∈ T.atlas) (hd' : d' ∈ T.atlas)
    (p : M × N) (hp : p ∈ (productChart C c d).2.source)
    (hq : p ∈ (productChart C c' d').2.source)
    (K : OrthantExtension ((productChart C c d).2.symm.trans (productChart C c' d').2).source
      ((productChart C c d).2.symm.trans (productChart C c' d').2)
      ((productChart C c d).2 p)) :
    let hp0 : p ∈ c.2.source ×ˢ d.2.source := (CornerProducts.productChart_source C c d) ▸ hp
    let hq0 : p ∈ c'.2.source ×ˢ d'.2.source := (CornerProducts.productChart_source C c' d') ▸ hq
    ∃ A : Euclidean (m+n) ≃ₗ[ℝ] Euclidean (m+n),
      A.toLinearMap = (fderiv ℝ K.map ((productChart C c d).2 p).val).toLinearMap ∧
      Module.Ray.map (determinantMap (m+n) A)
        (productCoordinateRay (C c.1 d.1) (o.sign c hc ⟨p.1,hp0.1⟩) (q.sign d hd ⟨p.2,hp0.2⟩)) =
        productCoordinateRay (C c'.1 d'.1) (o.sign c' hc' ⟨p.1,hq0.1⟩)
          (q.sign d' hd' ⟨p.2,hq0.2⟩) := by
  dsimp only
  let hp0 : p ∈ c.2.source ×ˢ d.2.source := (CornerProducts.productChart_source C c d) ▸ hp
  let hq0 : p ∈ c'.2.source ×ˢ d'.2.source := (CornerProducts.productChart_source C c' d') ▸ hq
  let E := cornerTransitionEquiv c c' (S.maximal.1.2 c hc c' hc') p.1 hp0.1 hq0.1
  let F := cornerTransitionEquiv d d' (T.maximal.1.2 d hd d' hd') p.2 hp0.2 hq0.2
  let A := (C c.1 d.1).linearEquiv.symm.trans
    ((E.prodCongr F).trans (C c'.1 d'.1).linearEquiv)
  refine ⟨A.toLinearEquiv,?_,?_⟩
  · exact congrArg ContinuousLinearMap.toLinearMap
      (productTransitionEquiv_derivative S T C c c' d d' hc hc' hd hd' p hp hq K)
  · have hn := coordinate_product_ray_natural
      (C c.1 d.1).linearEquiv.toLinearEquiv (C c'.1 d'.1).linearEquiv.toLinearEquiv
      E.toLinearEquiv F.toLinearEquiv
      (OrientationResults.standardRayEquiv m (o.sign c hc ⟨p.1,hp0.1⟩))
      (OrientationResults.standardRayEquiv n (q.sign d hd ⟨p.2,hp0.2⟩))
    rw [cornerOrientation_coordinate_ray_transport o c c' hc hc' p.1 hp0.1 hq0.1,
      cornerOrientation_coordinate_ray_transport q d d' hd hd' p.2 hp0.2 hq0.2] at hn
    exact hn


private structure ProductChartRepresentative {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N) (C : ProductCoordinateFamily m n)
    (e : CornerChart (m+n) (M × N)) where
  left : CornerChart m M
  mem_left : left ∈ S.atlas
  right : CornerChart n N
  mem_right : right ∈ T.atlas
  eq_chart : e = productChart C left right

private def productChartRepresentative {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N) (C : ProductCoordinateFamily m n)
    (e : CornerChart (m+n) (M × N)) (he : e ∈ productAtlas C S.atlas T.atlas) :
    ProductChartRepresentative S T C e :=
  Classical.choice (show Nonempty (ProductChartRepresentative S T C e) from by
    obtain ⟨c,hc,d,hd,he⟩ := he
    exact ⟨⟨c,hc,d,hd,he⟩⟩)

private theorem ProductChartRepresentative.mem_source {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold m M} {T : CornerManifold n N} {C : ProductCoordinateFamily m n}
    {e : CornerChart (m+n) (M × N)} (r : ProductChartRepresentative S T C e)
    (p : e.2.source) : p.val ∈ r.left.2.source ×ˢ r.right.2.source := by
  have hs : e.2.source = r.left.2.source ×ˢ r.right.2.source :=
    (congrArg (fun f : CornerChart (m+n) (M × N) => f.2.source) r.eq_chart).trans
      (CornerProducts.productChart_source C r.left r.right)
  exact hs ▸ p.property

private def productAtlasChartRay {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (e : CornerChart (m+n) (M × N)) (he : e ∈ productAtlas C S.atlas T.atlas)
    (p : e.2.source) : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean (m+n))) :=
  let r := productChartRepresentative S T C e he
  productCoordinateRay (C r.left.1 r.right.1)
    (o.sign r.left r.mem_left ⟨p.val.1,(r.mem_source p).1⟩)
    (q.sign r.right r.mem_right ⟨p.val.2,(r.mem_source p).2⟩)

private theorem productAtlasChartRay_locallyConstant {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (e : CornerChart (m+n) (M × N)) (he : e ∈ productAtlas C S.atlas T.atlas) :
    IsLocallyConstant (productAtlasChartRay S T o q C e he) := by
  let r := productChartRepresentative S T C e he
  let f : e.2.source → r.left.2.source := fun p => ⟨p.val.1,(r.mem_source p).1⟩
  let g : e.2.source → r.right.2.source := fun p => ⟨p.val.2,(r.mem_source p).2⟩
  have hf : Continuous f := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hg : Continuous g := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  exact ((o.locallyConstant r.left r.mem_left).comp_continuous hf).comp₂
    ((q.locallyConstant r.right r.mem_right).comp_continuous hg)
      (productCoordinateRay (C r.left.1 r.right.1))

/-- Every pair of product chart representations has the same transport law,
even if different pairs represent an equal actual corner chart. -/
theorem productCoordinateRay_transport_of_eq {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (e f : CornerChart (m+n) (M × N))
    (c c' : CornerChart m M) (d d' : CornerChart n N)
    (hc : c ∈ S.atlas) (hc' : c' ∈ S.atlas) (hd : d ∈ T.atlas) (hd' : d' ∈ T.atlas)
    (he : e = productChart C c d) (hf : f = productChart C c' d')
    (p : M × N) (hp : p ∈ e.2.source) (hq : p ∈ f.2.source)
    (hp0 : p ∈ c.2.source ×ˢ d.2.source) (hq0 : p ∈ c'.2.source ×ˢ d'.2.source)
    (K : OrthantExtension (e.2.symm.trans f.2).source (e.2.symm.trans f.2) (e.2 p)) :
    ∃ A : Euclidean (m+n) ≃ₗ[ℝ] Euclidean (m+n),
      A.toLinearMap = (fderiv ℝ K.map (e.2 p).val).toLinearMap ∧
      Module.Ray.map (determinantMap (m+n) A)
        (productCoordinateRay (C c.1 d.1) (o.sign c hc ⟨p.1,hp0.1⟩) (q.sign d hd ⟨p.2,hp0.2⟩)) =
        productCoordinateRay (C c'.1 d'.1) (o.sign c' hc' ⟨p.1,hq0.1⟩)
          (q.sign d' hd' ⟨p.2,hq0.2⟩) := by
  subst e
  subst f
  exact productCoordinateRay_transport S T o q C c c' d d' hc hc' hd hd' p hp hq K

/-- Compatible orientation on the actual generating product atlas. -/
def productAtlasOrientation {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n) :
    CornerAtlasOrientation (productAtlas C S.atlas T.atlas) where
  sign := fun e he p => (OrientationResults.standardRayEquiv (m+n)).symm
    (productAtlasChartRay S T o q C e he p)
  locallyConstant := fun e he => (productAtlasChartRay_locallyConstant S T o q C e he).comp _
  compatible := by
    intro e f he hf p hp hq K
    let r := productChartRepresentative S T C e he
    let s := productChartRepresentative S T C f hf
    obtain ⟨A,hA,htransport⟩ := productCoordinateRay_transport_of_eq S T o q C e f
      r.left s.left r.right s.right r.mem_left s.mem_left r.mem_right s.mem_right
      r.eq_chart s.eq_chart p hp hq (r.mem_source ⟨p,hp⟩) (s.mem_source ⟨p,hq⟩) K
    have hray : Module.Ray.map (determinantMap (m+n) A)
        (OrientationResults.standardRayEquiv (m+n)
          ((OrientationResults.standardRayEquiv (m+n)).symm
            (productAtlasChartRay S T o q C e he ⟨p,hp⟩))) =
        OrientationResults.standardRayEquiv (m+n)
          ((OrientationResults.standardRayEquiv (m+n)).symm
            (productAtlasChartRay S T o q C f hf ⟨p,hq⟩)) := by
      simpa only [Equiv.apply_symm_apply,productAtlasChartRay,r,s] using htransport
    have hs := (standardRayEquiv_map_iff A _ _).mp hray
    rw [hA] at hs
    exact hs

/-- The identity ambient map extends an actual chart's identity transition. -/
def cornerIdentityExtension {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (p : M) (_hp : p ∈ c.2.source) :
    OrthantExtension (c.2.symm.trans c.2).source (c.2.symm.trans c.2) (c.2 p) where
  domain := univ
  isOpen_domain := isOpen_univ
  mem_domain := mem_univ _
  map := id
  smooth := contDiff_id.contDiffOn
  agrees z hz _ := by
    change z.val = (c.2 (c.2.symm z)).val
    exact congrArg Subtype.val (c.2.right_inv hz.1).symm

/-- Identity chart transitions induce the identity on the ambient tangent space. -/
theorem cornerTransitionDerivative_self {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (h : CornerCompatible c c)
    (p : M) (hp : p ∈ c.2.source) :
    cornerTransitionDerivative c c h p hp hp = ContinuousLinearMap.id ℝ (Euclidean n) := by
  rw [cornerTransitionDerivative_eq c c h p hp hp (cornerIdentityExtension c p hp)]
  exact fderiv_id

/-- Any ambient extension of a chart identity has the identity derivative. -/
theorem cornerIdentityExtension_derivative {n : ℕ} {M : Type*} [TopologicalSpace M]
    (c : CornerChart n M) (p : M) (hp : p ∈ c.2.source)
    (H : OrthantExtension (c.2.symm.trans c.2).source (c.2.symm.trans c.2) (c.2 p)) :
    fderiv ℝ H.map (c.2 p).val = ContinuousLinearMap.id ℝ (Euclidean n) := by
  have he : fderiv ℝ H.map (c.2 p).val =
      fderiv ℝ (cornerIdentityExtension c p hp).map (c.2 p).val := by
    apply orthant_extension_derivative_unique
    refine ⟨c.2.map_source hp, ?_⟩
    change c.2.symm (c.2 p) ∈ c.2.source
    rwa [c.2.left_inv hp]
  rw [he]
  exact fderiv_id



/-- The ordered product determinant ray is independent of every representation
of one actual product chart, including empty factors. -/
theorem productCoordinateRay_independent {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (e : CornerChart (m+n) (M × N))
    (c c' : CornerChart m M) (d d' : CornerChart n N)
    (hc : c ∈ S.atlas) (hc' : c' ∈ S.atlas) (hd : d ∈ T.atlas) (hd' : d' ∈ T.atlas)
    (he : e = productChart C c d) (hf : e = productChart C c' d')
    (p : M × N) (hp : p ∈ e.2.source)
    (hp0 : p ∈ c.2.source ×ˢ d.2.source) (hq0 : p ∈ c'.2.source ×ˢ d'.2.source) :
    productCoordinateRay (C c.1 d.1) (o.sign c hc ⟨p.1,hp0.1⟩) (q.sign d hd ⟨p.2,hp0.2⟩) =
      productCoordinateRay (C c'.1 d'.1) (o.sign c' hc' ⟨p.1,hq0.1⟩) (q.sign d' hd' ⟨p.2,hq0.2⟩) := by
  obtain ⟨A,hA,hray⟩ := productCoordinateRay_transport_of_eq S T o q C e e c c' d d'
    hc hc' hd hd' he hf p hp hp hp0 hq0 (cornerIdentityExtension e p hp)
  have hAi : A = LinearEquiv.refl ℝ (Euclidean (m+n)) := by
    apply LinearEquiv.toLinearMap_injective
    rw [hA,cornerIdentityExtension_derivative e p hp]
    rfl
  rw [hAi,topExterior_ray_map,LinearEquiv.refl_toLinearMap,LinearMap.det_id] at hray
  simpa using hray


/-- Project source membership through the exact product chart domain. -/
theorem productChart_mem_source {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m n) (c : CornerChart m M) (d : CornerChart n N)
    (p : (productChart C c d).2.source) : p.val ∈ c.2.source ×ˢ d.2.source :=
  Eq.mp (congrArg (fun U : Set (M × N) => p.val ∈ U)
    (CornerProducts.productChart_source C c d)) p.property

/-- Full maximal-atlas product orientation with the fixed ordered determinant
ray in every genuine product chart. -/
theorem product_orientation_exists {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (o : CornerOrientation S) (q : CornerOrientation T) (C : ProductCoordinateFamily m n)
    (P : CornerManifold (m+n) (M × N))
    (hsub : productAtlas C S.atlas T.atlas ⊆ P.atlas) :
    ∃ b : CornerOrientation P,
      ∀ (c : CornerChart m M) (hc : c ∈ S.atlas)
        (d : CornerChart n N) (hd : d ∈ T.atlas)
        (p : (productChart C c d).2.source),
        OrientationResults.standardRayEquiv (m+n)
          (b.sign (productChart C c d) (hsub ⟨c,hc,d,hd,rfl⟩) p) =
        productCoordinateRay (C c.1 d.1)
          (o.sign c hc ⟨p.val.1,(productChart_mem_source C c d p).1⟩)
          (q.sign d hd ⟨p.val.2,(productChart_mem_source C c d p).2⟩) := by
  let a := productAtlasOrientation S T o q C
  have hcover := (CornerProducts.product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1).1
  obtain ⟨b,hb,_⟩ := orientation_extension P (productAtlas C S.atlas T.atlas) hsub hcover a
  refine ⟨b,?_⟩
  intro c hc d hd p
  rw [hb (productChart C c d) ⟨c,hc,d,hd,rfl⟩ p]
  change OrientationResults.standardRayEquiv (m+n)
      ((OrientationResults.standardRayEquiv (m+n)).symm
        (productAtlasChartRay S T o q C (productChart C c d) ⟨c,hc,d,hd,rfl⟩ p)) = _
  rw [Equiv.apply_symm_apply]
  let r := productChartRepresentative S T C (productChart C c d) ⟨c,hc,d,hd,rfl⟩
  exact productCoordinateRay_independent S T o q C (productChart C c d)
    r.left c r.right d r.mem_left hc r.mem_right hd r.eq_chart rfl
    p.val p.property (r.mem_source p) ((CornerProducts.productChart_source C c d) ▸ p.property)


/-- Positivity of the fixed ordered determinant product in actual coordinates. -/
theorem productCoordinateRay_positive {m n : ℕ} {k : Fin (m+1)} {l : Fin (n+1)}
    (C : OrthantProductCoordinates m n k l) (b c : Bool)
    (v : ⋀[ℝ]^m (Euclidean m)) (w : ⋀[ℝ]^n (Euclidean n))
    (hv : IsPositive (OrientationResults.standardRayEquiv m b) v)
    (hw : IsPositive (OrientationResults.standardRayEquiv n c) w) :
    IsPositive (productCoordinateRay C b c) (coordinateProductVector C v w) :=
  OrientationProducts.isPositive_map _
    (OrientationProducts.orderedProductRay_positive (by simp) (by simp) _ _ hv hw)


/-- The ordered product orientation on the full maximal corner atlas is
constructed uniquely, including zero dimensions and empty factors. -/
theorem product_orientation :
    Specs.SmoothManifolds.Corners.FaceOrientations.product_orientationType := by
  intro m n M N _ _ S T C P hsub o q
  obtain ⟨b,hb⟩ := product_orientation_exists S T o q C P hsub
  have hbpos : IsCornerProductOrientation C o q b := by
    intro c hc d hd he p hp hP v w hv hw
    apply (standardRayEquiv_positive_iff _ _).mp
    rw [hb c hc d hd ⟨p,hP⟩]
    exact productCoordinateRay_positive _ _ _ v w
      ((standardRayEquiv_positive_iff _ _).mpr hv)
      ((standardRayEquiv_positive_iff _ _).mpr hw)
  refine ⟨b,hbpos,?_⟩
  intro b' hb'
  have hcover := (CornerProducts.product_atlas C S.atlas T.atlas S.maximal.1 T.maximal.1).1
  apply cornerOrientation_ext_on_cover b' b (productAtlas C S.atlas T.atlas) hsub hcover
  intro e he p
  obtain ⟨c,hc,d,hd,rfl⟩ := he
  apply (OrientationResults.standardRayEquiv (m+n)).injective
  have hp := productChart_mem_source C c d p
  let v := signValue (o.sign c hc ⟨p.val.1,hp.1⟩) • coordinateVolume m
  let w := signValue (q.sign d hd ⟨p.val.2,hp.2⟩) • coordinateVolume n
  have hv : CoordinatePositive (o.sign c hc ⟨p.val.1,hp.1⟩) v :=
    ⟨1,zero_lt_one,(one_smul ℝ v).symm⟩
  have hw : CoordinatePositive (q.sign d hd ⟨p.val.2,hp.2⟩) w :=
    ⟨1,zero_lt_one,(one_smul ℝ w).symm⟩
  have hpositive := (standardRayEquiv_positive_iff _ _).mpr
    (hb' c hc d hd (hsub ⟨c,hc,d,hd,rfl⟩) p.val hp p.property v w hv hw)
  have hproduct := productCoordinateRay_positive (C c.1 d.1) _ _ v w
    ((standardRayEquiv_positive_iff _ _).mpr hv)
    ((standardRayEquiv_positive_iff _ _).mpr hw)
  exact (OrientationProducts.positive_ray_eq hpositive hproduct).trans (hb c hc d hd p).symm



/-- Signed coordinate positivity transforms by the ordinary Jacobian sign. -/
theorem coordinatePositive_linearMap_of_sign {n : ℕ}
    (E : Euclidean n ≃ₗ[ℝ] Euclidean n) (b c : Bool)
    (h : signValue c = signValue b * Real.sign E.toLinearMap.det)
    (v : ⋀[ℝ]^n (Euclidean n)) (hv : CoordinatePositive b v) :
    CoordinatePositive c (determinantMap n E v) := by
  have hpos : 0 < signValue b * E.toLinearMap.det * signValue c :=
    (OrientationResults.scalar_sign_compatibility_iff _ E.isUnit_det'.ne_zero b c).mp
      (by rwa [← real_sign_eq_signType] )
  obtain ⟨a,ha,rfl⟩ := hv
  refine ⟨a * (signValue b * E.toLinearMap.det * signValue c),mul_pos ha hpos,?_⟩
  change exteriorPower.map n E.toLinearMap (a • (signValue b • coordinateVolume n)) = _
  rw [topExterior_map_eq_smul]
  simp only [smul_smul]
  congr 1
  have hs := OrientationResults.signValue_mul_self c
  linear_combination -a * signValue b * E.toLinearMap.det * hs

/-- The actual transition between two allowed product model identifications is linear. -/
def productCoordinateChangeExtension {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (C D : ProductCoordinateFamily m n) (c : CornerChart m M) (d : CornerChart n N)
    (p : M × N) :
    OrthantExtension ((productChart C c d).2.symm.trans (productChart D c d).2).source
      ((productChart C c d).2.symm.trans (productChart D c d).2)
      ((productChart C c d).2 p) := by
  let A := (C c.1 d.1).linearEquiv.symm.trans (D c.1 d.1).linearEquiv
  refine ⟨univ,isOpen_univ,mem_univ _,A,A.contDiff.contDiffOn,?_⟩
  intro z hz _
  change (D c.1 d.1).linearEquiv ((C c.1 d.1).linearEquiv.symm z.val) =
    ((productChart D c d).2 ((productChart C c d).2.symm z)).val
  rw [CornerProducts.productChart_val,CornerProducts.productChart_inverse C c d z hz.1]

/-- The full ordered product orientation is independent of the chosen linear orthant coordinates. -/
theorem product_orientation_coordinates_independent {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (C D : ProductCoordinateFamily m n) (P : CornerManifold (m+n) (M × N))
    (hC : productAtlas C S.atlas T.atlas ⊆ P.atlas)
    (_hD : productAtlas D S.atlas T.atlas ⊆ P.atlas)
    (o : CornerOrientation S) (q : CornerOrientation T) (r : CornerOrientation P)
    (h : IsCornerProductOrientation C o q r) : IsCornerProductOrientation D o q r := by
  intro c hc d hd he p hp hP v w hv hw
  let A := (C c.1 d.1).linearEquiv.symm.trans (D c.1 d.1).linearEquiv
  let H := productCoordinateChangeExtension C D c d p
  have hpC : p ∈ (productChart C c d).2.source := by
    rw [CornerProducts.productChart_source]
    exact hp
  have heC : productChart C c d ∈ P.atlas := hC ⟨c,hc,d,hd,rfl⟩
  have hsign := r.compatible (productChart C c d) (productChart D c d) heC he p hpC hP H
  have hder : (fderiv ℝ H.map ((productChart C c d).2 p).val).toLinearMap = A.toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (A.hasFDerivAt.fderiv)
  rw [hder] at hsign
  have hpositive := coordinatePositive_linearMap_of_sign A.toLinearEquiv _ _ hsign
    (coordinateProductVector (C c.1 d.1) v w) (h c hc d hd heC p hp hpC v w hv hw)
  have hnatural : determinantMap (m+n) A.toLinearEquiv
      (coordinateProductVector (C c.1 d.1) v w) =
        coordinateProductVector (D c.1 d.1) v w := by
    change determinantMap (m+n)
      ((C c.1 d.1).linearEquiv.toLinearEquiv.symm.trans (D c.1 d.1).linearEquiv.toLinearEquiv)
      (determinantMap (m+n) (C c.1 d.1).linearEquiv.toLinearEquiv
        (orderedWedge m n (Euclidean m) (Euclidean n) v w)) = _
    rw [determinantMap_trans]
    change determinantMap (m+n) (D c.1 d.1).linearEquiv.toLinearEquiv
      (determinantMap (m+n) (C c.1 d.1).linearEquiv.toLinearEquiv.symm
        (determinantMap (m+n) (C c.1 d.1).linearEquiv.toLinearEquiv _)) = _
    rw [determinantMap_symm_apply_apply]
    rfl
  rwa [hnatural] at hpositive



/-- Every allowed coordinate family gives the same global ordered product orientation. -/
theorem product_orientation_all_coordinates {m n : ℕ} {M N : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : CornerManifold m M) (T : CornerManifold n N)
    (C : ProductCoordinateFamily m n) (P : CornerManifold (m+n) (M × N))
    (hP : P.atlas = cornerMaximalExtension (productAtlas C S.atlas T.atlas))
    (o : CornerOrientation S) (q : CornerOrientation T) :
    ∃! r : CornerOrientation P, ∀ D : ProductCoordinateFamily m n,
      productAtlas D S.atlas T.atlas ⊆ P.atlas ∧ IsCornerProductOrientation D o q r := by
  have hsub (D : ProductCoordinateFamily m n) : productAtlas D S.atlas T.atlas ⊆ P.atlas := by
    obtain ⟨Q,hQ,hDQ⟩ := CornerProducts.product_corner_structure S T D
    rwa [← CornerProducts.product_canonical S T C D P Q hP hQ] at hDQ
  obtain ⟨r,hr,hu⟩ := product_orientation S T C P (hsub C) o q
  refine ⟨r, fun D => ⟨hsub D,?_⟩, ?_⟩
  · exact product_orientation_coordinates_independent S T C D P (hsub C) (hsub D) o q r hr
  · intro r' hr'
    exact hu r' (hr' C).2


section ProductFaceSigns
universe u
open BoundaryOrientationData
set_option maxHeartbeats 1500000

theorem product_left_face_ray_positive {m n : ℕ} {k : Fin (m+2)} {l : Fin (n+1)}
    (C : OrthantProductCoordinates (m+1) n k l) (i : Fin (m+1))
    (rA : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
    (rV : Module.Ray ℝ (⋀[ℝ]^(m+1) (Euclidean (m+1))))
    (rW : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)))
    (rP : Module.Ray ℝ (⋀[ℝ]^((m+1)+n) (Euclidean ((m+1)+n))))
    (v : Euclidean (m+1))
    (hface : ∀ η, IsPositive rA η ↔ IsPositive rV (normalWedge (faceInsertion i) v η))
    (hprod : ∀ α θ, IsPositive rV α → IsPositive rW θ →
      IsPositive rP (coordinateProductVector C α θ)) :
    ∀ ζ, IsPositive (OrientationProducts.orderedProductRay (by simp) (by simp) rA rW) ζ ↔
      IsPositive rP (castExterior (Nat.add_right_comm m n 1)
        (normalWedge (C.linearEquiv.toLinearMap.comp
          ((faceInsertion i).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)))
          (C.linearEquiv (v,0)) ζ)) := by
  refine BoundaryOrientations.face_positive_left m n (by simp) (faceInsertion i)
    (C.linearEquiv.toLinearMap.comp
      ((faceInsertion i).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)))
    C.linearEquiv.symm.toLinearEquiv (LinearEquiv.refl ℝ _)
    (by intro z; simp) (C.linearEquiv (v,0)) rA rV rW _ rP ?_ ?_ ?_
  · simpa using hface
  · intro η θ hη hθ
    change IsPositive _ ((exteriorPower.map (m+n) (LinearMap.id :
      Euclidean m × Euclidean n →ₗ[ℝ] Euclidean m × Euclidean n)) _)
    rw [exteriorPower.map_id]
    exact OrientationProducts.orderedProductRay_positive (by simp) (by simp) rA rW hη hθ
  · exact hprod

theorem product_right_face_ray_positive {m n : ℕ} {k : Fin (m+1)} {l : Fin (n+2)}
    (C : OrthantProductCoordinates m (n+1) k l) (j : Fin (n+1))
    (rA : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)))
    (rV : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
    (rW : Module.Ray ℝ (⋀[ℝ]^(n+1) (Euclidean (n+1))))
    (rP : Module.Ray ℝ (⋀[ℝ]^(m+(n+1)) (Euclidean (m+(n+1)))))
    (v : Euclidean (n+1))
    (hface : ∀ θ, IsPositive rA θ ↔ IsPositive rW (normalWedge (faceInsertion j) v θ))
    (hprod : ∀ η β, IsPositive rV η → IsPositive rW β →
      IsPositive rP (coordinateProductVector C η β)) :
    ∀ ζ, IsPositive (if Even m then OrientationProducts.orderedProductRay (by simp) (by simp) rV rA
      else -(OrientationProducts.orderedProductRay (by simp) (by simp) rV rA)) ζ ↔
      IsPositive rP (castExterior (Nat.add_assoc m n 1)
        (normalWedge (C.linearEquiv.toLinearMap.comp
          ((LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j)))
          (C.linearEquiv (0,v)) ζ)) := by
  refine BoundaryOrientations.face_positive_right m n (by simp) (faceInsertion j)
    (C.linearEquiv.toLinearMap.comp
      ((LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j)))
    C.linearEquiv.symm.toLinearEquiv (LinearEquiv.refl ℝ _)
    (by intro z; simp) (C.linearEquiv (0,v)) rA rV rW _ rP ?_ ?_ ?_
  · simpa using hface
  · intro η θ hη hθ
    change IsPositive _ ((exteriorPower.map (m+n) (LinearMap.id :
      Euclidean m × Euclidean n →ₗ[ℝ] Euclidean m × Euclidean n)) _)
    rw [exteriorPower.map_id]
    exact OrientationProducts.orderedProductRay_positive (by simp) (by simp) rV rA hη hθ
  · exact hprod

theorem product_left_tagged_face {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily (m+1) n) (c : CornerChart (m+1) M) (d : CornerChart n N)
    (L : ProductLabels (C c.1 d.1)) (P : CornerManifold ((m+1)+n) (M × N))
    (he : productChart C c d ∈ P.atlas) (p : M × N)
    (hp : p ∈ c.2.source ×ˢ d.2.source) (i : activeCoordinates (c.2 p.1)) :
    ∃ a : activeCoordinates ((productChart C c d).2 p),
      L.indexEquiv a.val = Sum.inl i.val ∧
      (chartFaceAt P (productChart C c d) he p (by
        rw [CornerProducts.productChart_source]; exact hp) a).val =
        factorFaceGerm c d p (Sum.inl i) ∧
      (∀ v : Euclidean (m+1), (C c.1 d.1).linearEquiv (v,0) a.val = v i.val) ∧
      ∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (faceInsertion i.val z.1,z.2) a.val = 0 := by
  let a : Fin ((m+1)+n) := L.indexEquiv.symm (Sum.inl i.val)
  have ha : L.indexEquiv a = Sum.inl i.val := L.indexEquiv.apply_symm_apply _
  have hia := (Finset.mem_filter.mp i.property).2
  have haa : a ∈ activeCoordinates ((productChart C c d).2 p) := by
    simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(L.constrained a).mpr ?_, ?_⟩
    · simpa [ha] using hia.1
    · rw [CornerProducts.productChart_val, L.coordinate, ha]
      exact hia.2
  refine ⟨⟨a,haa⟩,ha,?_,?_,?_⟩
  · change chartFaceGerm (productChart C c d) p a = _
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [continuous_snd.continuousAt (d.2.open_source.mem_nhds hp.2)] with q hq
    change (q ∈ (productChart C c d).2.source ∧
      ((productChart C c d).2 q).val a = 0) =
      (q.1 ∈ c.2.source ∧ (c.2 q.1).val i.val = 0)
    rw [CornerProducts.productChart_source, CornerProducts.productChart_val, L.coordinate, ha]
    change q.2 ∈ d.2.source at hq
    simp only [mem_prod, hq, and_true, Sum.elim_inl]
  · intro v
    rw [L.coordinate, ha]
    rfl
  · intro z
    rw [L.coordinate, ha]
    simp [faceInsertion]

theorem product_right_tagged_face {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m (n+1)) (c : CornerChart m M) (d : CornerChart (n+1) N)
    (L : ProductLabels (C c.1 d.1)) (P : CornerManifold (m+(n+1)) (M × N))
    (he : productChart C c d ∈ P.atlas) (p : M × N)
    (hp : p ∈ c.2.source ×ˢ d.2.source) (j : activeCoordinates (d.2 p.2)) :
    ∃ a : activeCoordinates ((productChart C c d).2 p),
      L.indexEquiv a.val = Sum.inr j.val ∧
      (chartFaceAt P (productChart C c d) he p (by
        rw [CornerProducts.productChart_source]; exact hp) a).val =
        factorFaceGerm c d p (Sum.inr j) ∧
      (∀ v : Euclidean (n+1), (C c.1 d.1).linearEquiv (0,v) a.val = v j.val) ∧
      ∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (z.1,faceInsertion j.val z.2) a.val = 0 := by
  let a : Fin (m+(n+1)) := L.indexEquiv.symm (Sum.inr j.val)
  have ha : L.indexEquiv a = Sum.inr j.val := L.indexEquiv.apply_symm_apply _
  have hja := (Finset.mem_filter.mp j.property).2
  have haa : a ∈ activeCoordinates ((productChart C c d).2 p) := by
    simp only [activeCoordinates, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨(L.constrained a).mpr ?_, ?_⟩
    · simpa [ha] using hja.1
    · rw [CornerProducts.productChart_val, L.coordinate, ha]
      exact hja.2
  refine ⟨⟨a,haa⟩,ha,?_,?_,?_⟩
  · change chartFaceGerm (productChart C c d) p a = _
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [continuous_fst.continuousAt (c.2.open_source.mem_nhds hp.1)] with q hq
    change (q ∈ (productChart C c d).2.source ∧
      ((productChart C c d).2 q).val a = 0) =
      (q.2 ∈ d.2.source ∧ (d.2 q.2).val j.val = 0)
    rw [CornerProducts.productChart_source, CornerProducts.productChart_val, L.coordinate, ha]
    change q.1 ∈ c.2.source at hq
    simp only [mem_prod, hq, true_and, Sum.elim_inr]
  · intro v
    rw [L.coordinate, ha]
    rfl
  · intro z
    rw [L.coordinate, ha]
    simp [faceInsertion]

theorem product_factor_face_germs_distinct {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m n) (c : CornerChart m M) (d : CornerChart n N)
    (L : ProductLabels (C c.1 d.1)) (P : CornerManifold (m+n) (M × N))
    (he : productChart C c d ∈ P.atlas) (p : M × N)
    (hp : p ∈ c.2.source ×ˢ d.2.source)
    (i : activeCoordinates (c.2 p.1)) (j : activeCoordinates (d.2 p.2)) :
    factorFaceGerm c d p (Sum.inl i) ≠ factorFaceGerm c d p (Sum.inr j) := by
  obtain ⟨f,hf,hval⟩ := CornerProducts.product_face_germs C c d L P he p hp
  intro hij
  have h : f (Sum.inl i) = f (Sum.inr j) := Subtype.ext
    ((hval (Sum.inl i)).trans (hij.trans (hval (Sum.inr j)).symm))
  cases hf.1 h

theorem product_left_face_inclusion_coordinates {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily (m+1) n) (c : CornerChart (m+1) M) (d : CornerChart n N)
    (i : Fin (m+1)) :
    (∀ x : ChartFacePatch c i, ∀ y : N,
      ((productChart C c d).2 (x.val,y)).val =
        (C c.1 d.1).linearEquiv (faceInsertion i (i.removeNth (c.2 x.val).val),(d.2 y).val)) ∧
    ∀ z : Euclidean m × Euclidean n,
      HasFDerivAt (fun w : Euclidean m × Euclidean n =>
        (C c.1 d.1).linearEquiv (faceInsertion i w.1,w.2))
        ((C c.1 d.1).linearEquiv.toContinuousLinearMap.comp
          ((faceInsertion i).toContinuousLinearMap.prodMap
            (ContinuousLinearMap.id ℝ (Euclidean n)))) z := by
  constructor
  · intro x y
    rw [CornerProducts.productChart_val]
    congr 1
    apply Prod.ext
    · change (c.2 x.val).val = i.insertNth 0 (i.removeNth (c.2 x.val).val)
      symm
      exact Fin.insertNth_eq_iff.mpr ⟨x.property.2.symm,rfl⟩
    · rfl
  · intro z
    exact ((C c.1 d.1).linearEquiv.toContinuousLinearMap.comp
      ((faceInsertion i).toContinuousLinearMap.prodMap
        (ContinuousLinearMap.id ℝ (Euclidean n)))).hasFDerivAt

theorem product_right_face_inclusion_coordinates {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (C : ProductCoordinateFamily m (n+1)) (c : CornerChart m M) (d : CornerChart (n+1) N)
    (j : Fin (n+1)) :
    (∀ x : M, ∀ y : ChartFacePatch d j,
      ((productChart C c d).2 (x,y.val)).val =
        (C c.1 d.1).linearEquiv ((c.2 x).val,faceInsertion j (j.removeNth (d.2 y.val).val))) ∧
    ∀ z : Euclidean m × Euclidean n,
      HasFDerivAt (fun w : Euclidean m × Euclidean n =>
        (C c.1 d.1).linearEquiv (w.1,faceInsertion j w.2))
        ((C c.1 d.1).linearEquiv.toContinuousLinearMap.comp
          ((ContinuousLinearMap.id ℝ (Euclidean m)).prodMap
            (faceInsertion j).toContinuousLinearMap)) z := by
  constructor
  · intro x y
    rw [CornerProducts.productChart_val]
    congr 1
    apply Prod.ext
    · rfl
    · change (d.2 y.val).val = j.insertNth 0 (j.removeNth (d.2 y.val).val)
      symm
      exact Fin.insertNth_eq_iff.mpr ⟨y.property.2.symm,rfl⟩
  · intro z
    exact ((C c.1 d.1).linearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ (Euclidean m)).prodMap
        (faceInsertion j).toContinuousLinearMap)).hasFDerivAt

theorem coordinatePositive_iff_of_generator {n : ℕ} (b : Bool)
    (r : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)))
    (hr : IsPositive r (signValue b • coordinateVolume n))
    (v : ⋀[ℝ]^n (Euclidean n)) : CoordinatePositive b v ↔ IsPositive r v := by
  rw [← hr.choose_spec, OrientationResults.positive_iff_pos_smul _ hr.choose]
  rfl

theorem product_left_resolved_sheet_orientation {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold (m+1) M} {T : CornerManifold n N}
    {P : CornerManifold ((m+1)+n) (M × N)}
    (C : ProductCoordinateFamily (m+1) n)
    (oS : CornerOrientation S) (oT : CornerOrientation T) (oP : CornerOrientation P)
    (hprod : IsCornerProductOrientation C oS oT oP)
    (c : CornerChart (m+1) M) (hc : c ∈ S.atlas)
    (d : CornerChart n N) (hd : d ∈ T.atlas)
    (L : ProductLabels (C c.1 d.1)) (he : productChart C c d ∈ P.atlas)
    (q : ResolvedFaceSpace P) (hp : q.1 ∈ c.2.source ×ˢ d.2.source)
    (hP : q.1 ∈ (productChart C c d).2.source)
    (i : activeCoordinates (c.2 q.1.1))
    (hg : q.2.val = factorFaceGerm c d q.1 (Sum.inl i))
    (rS : Module.Ray ℝ (⋀[ℝ]^(m+1) (Euclidean (m+1))))
    (rT : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)))
    (rP : Module.Ray ℝ (⋀[ℝ]^((m+1)+n) (Euclidean ((m+1)+n))))
    (hrS : IsPositive rS (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩) • coordinateVolume (m+1)))
    (hrT : IsPositive rT (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩) • coordinateVolume n))
    (hrP : IsPositive rP (signValue (oP.sign (productChart C c d) he ⟨q.1,hP⟩) •
      coordinateVolume ((m+1)+n))) :
    ∃ a : activeCoordinates ((productChart C c d).2 q.1),
      ∃ rA : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)),
      ∃ rB : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean m × Euclidean n)),
      q.2 = chartFaceAt P (productChart C c d) he q.1 hP a ∧
      (∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (faceInsertion i.val z.1,z.2) a.val = 0) ∧
      IsPositive rA (faceSign (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩)) i.val • coordinateVolume m) ∧
      (∀ η θ, IsPositive rA η → IsPositive rT θ →
        IsPositive rB (orderedWedge m n (Euclidean m) (Euclidean n) η θ)) ∧
      ∀ v : Euclidean (m+1), v i.val < 0 →
        (C c.1 d.1).linearEquiv (v,0) a.val < 0 ∧
        ∀ ζ, IsPositive rB ζ ↔
          IsPositive rP (castExterior (Nat.add_right_comm m n 1)
            (normalWedge ((C c.1 d.1).linearEquiv.toLinearMap.comp
              ((faceInsertion i.val).prodMap (LinearMap.id : Euclidean n →ₗ[ℝ] Euclidean n)))
              ((C c.1 d.1).linearEquiv (v,0)) ζ)) := by
  obtain ⟨a,_,hgerm,hnorm,htan⟩ := product_left_tagged_face C c d L P he q.1 hp i
  obtain ⟨rA,⟨hrA,hface⟩,_⟩ := local_face_ray i.val
    (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩)) (OrientationResults.signValue_ne_zero _) rS hrS
  let rB := OrientationProducts.orderedProductRay (by simp) (by simp) rA rT
  refine ⟨a,rA,rB,Subtype.ext (hg.trans hgerm.symm),htan,hrA,?_,?_⟩
  · intro η θ hη hθ
    exact OrientationProducts.orderedProductRay_positive (by simp) (by simp) rA rT hη hθ
  · intro v hv
    refine ⟨by rwa [hnorm], ?_⟩
    apply product_left_face_ray_positive (C c.1 d.1) i.val rA rS rT rP v (hface v hv)
    intro α θ hα hθ
    apply (coordinatePositive_iff_of_generator _ rP hrP _).mp
    exact hprod c hc d hd he q.1 hp hP α θ
      ((coordinatePositive_iff_of_generator _ rS hrS _).mpr hα)
      ((coordinatePositive_iff_of_generator _ rT hrT _).mpr hθ)

theorem product_right_resolved_sheet_orientation {m n : ℕ} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : CornerManifold m M} {T : CornerManifold (n+1) N}
    {P : CornerManifold (m+(n+1)) (M × N)}
    (C : ProductCoordinateFamily m (n+1))
    (oS : CornerOrientation S) (oT : CornerOrientation T) (oP : CornerOrientation P)
    (hprod : IsCornerProductOrientation C oS oT oP)
    (c : CornerChart m M) (hc : c ∈ S.atlas)
    (d : CornerChart (n+1) N) (hd : d ∈ T.atlas)
    (L : ProductLabels (C c.1 d.1)) (he : productChart C c d ∈ P.atlas)
    (q : ResolvedFaceSpace P) (hp : q.1 ∈ c.2.source ×ˢ d.2.source)
    (hP : q.1 ∈ (productChart C c d).2.source)
    (j : activeCoordinates (d.2 q.1.2))
    (hg : q.2.val = factorFaceGerm c d q.1 (Sum.inr j))
    (rS : Module.Ray ℝ (⋀[ℝ]^m (Euclidean m)))
    (rT : Module.Ray ℝ (⋀[ℝ]^(n+1) (Euclidean (n+1))))
    (rP : Module.Ray ℝ (⋀[ℝ]^(m+(n+1)) (Euclidean (m+(n+1)))))
    (hrS : IsPositive rS (signValue (oS.sign c hc ⟨q.1.1,hp.1⟩) • coordinateVolume m))
    (hrT : IsPositive rT (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩) • coordinateVolume (n+1)))
    (hrP : IsPositive rP (signValue (oP.sign (productChart C c d) he ⟨q.1,hP⟩) •
      coordinateVolume (m+(n+1)))) :
    ∃ a : activeCoordinates ((productChart C c d).2 q.1),
      ∃ rA : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)),
      ∃ rB : Module.Ray ℝ (⋀[ℝ]^(m+n) (Euclidean m × Euclidean n)),
      q.2 = chartFaceAt P (productChart C c d) he q.1 hP a ∧
      (∀ z : Euclidean m × Euclidean n,
        (C c.1 d.1).linearEquiv (z.1,faceInsertion j.val z.2) a.val = 0) ∧
      IsPositive rA (faceSign (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩)) j.val • coordinateVolume n) ∧
      (∀ η θ, IsPositive rS η → IsPositive rA θ →
        IsPositive rB (orderedWedge m n (Euclidean m) (Euclidean n) η θ)) ∧
      ∀ v : Euclidean (n+1), v j.val < 0 →
        (C c.1 d.1).linearEquiv (0,v) a.val < 0 ∧
        ∀ ζ, IsPositive (if Even m then rB else -rB) ζ ↔
          IsPositive rP (castExterior (Nat.add_assoc m n 1)
            (normalWedge ((C c.1 d.1).linearEquiv.toLinearMap.comp
              ((LinearMap.id : Euclidean m →ₗ[ℝ] Euclidean m).prodMap (faceInsertion j.val)))
              ((C c.1 d.1).linearEquiv (0,v)) ζ)) := by
  obtain ⟨a,_,hgerm,hnorm,htan⟩ := product_right_tagged_face C c d L P he q.1 hp j
  obtain ⟨rA,⟨hrA,hface⟩,_⟩ := local_face_ray j.val
    (signValue (oT.sign d hd ⟨q.1.2,hp.2⟩)) (OrientationResults.signValue_ne_zero _) rT hrT
  let rB := OrientationProducts.orderedProductRay (by simp) (by simp) rS rA
  refine ⟨a,rA,rB,Subtype.ext (hg.trans hgerm.symm),htan,hrA,?_,?_⟩
  · intro η θ hη hθ
    exact OrientationProducts.orderedProductRay_positive (by simp) (by simp) rS rA hη hθ
  · intro v hv
    refine ⟨by rwa [hnorm], ?_⟩
    apply product_right_face_ray_positive (C c.1 d.1) j.val rA rS rT rP v (hface v hv)
    intro η β hη hβ
    apply (coordinatePositive_iff_of_generator _ rP hrP _).mp
    exact hprod c hc d hd he q.1 hp hP η β
      ((coordinatePositive_iff_of_generator _ rS hrS _).mpr hη)
      ((coordinatePositive_iff_of_generator _ rT hrT _).mpr hβ)

end ProductFaceSigns

end SmoothManifolds.CornerFaceOrientations
