import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.NilpotentConeRadialTopology
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Homeomorph.Quotient

namespace RepTheorySurvey.Geometric.NilpotentConeRadialTopology

noncomputable section

open NilpotentConeChartSpecs
open P202Specs.RealProjectiveHomology (antipodal quotientMap)
open P202Specs.SpheresDisks (sphere)
open Topology
open scoped unitInterval

private abbrev ComplexPair := WithLp 2 (ℂ × ℂ)

private theorem radialSize_parametrize (p : ℂ × ℂ) :
    radialSize (parametrize p) = ‖WithLp.toLp 2 p‖ := by
  change Real.sqrt (‖-(p.1 ^ 2)‖ + ‖p.2 ^ 2‖) = ‖WithLp.toLp 2 p‖
  rw [norm_neg, norm_pow, norm_pow]
  change Real.sqrt (‖(WithLp.toLp 2 p).fst‖ ^ 2 + ‖(WithLp.toLp 2 p).snd‖ ^ 2) = _
  rw [← WithLp.prod_norm_sq_eq_of_L2, Real.sqrt_sq (norm_nonneg _)]

private theorem continuous_radialSize : Continuous radialSize :=
  Real.continuous_sqrt.comp
    ((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).norm.add
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).norm)

private theorem continuous_parametrize : Continuous parametrize :=
  (continuous_fst.mul continuous_snd).prodMk
      (((continuous_fst.pow 2).neg).prodMk (continuous_snd.pow 2)) |>.subtype_mk _

private theorem parametrize_surjective : Function.Surjective parametrize := by
  rintro ⟨⟨u, v, w⟩, h⟩
  change u ^ 2 + v * w = 0 at h
  by_cases hv : v = 0
  · obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq w zero_lt_two
    have hu : u = 0 := by simpa [hv] using h
    exact ⟨(0, b), Subtype.ext (Prod.ext (by simp [parametrize, hu])
      (Prod.ext (by simp [parametrize, hv]) hb))⟩
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-v) zero_lt_two
    have ha0 : a ≠ 0 := by
      intro e
      apply hv
      simpa [e] using ha.symm
    refine ⟨(a, u / a), Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_))⟩
    · change a * (u / a) = u
      field_simp
    · change -(a ^ 2) = v
      rw [ha, neg_neg]
    · change (u / a) ^ 2 = w
      rw [div_pow, div_eq_iff (pow_ne_zero _ ha0), ha]
      linear_combination h

private theorem parametrize_fibre (x y : ℂ × ℂ) :
    parametrize x = parametrize y ↔ antipodalSetoid.r x y := by
  change parametrize x = parametrize y ↔ x = y ∨ x = -y
  constructor
  · intro h
    have hmul : x.1 * x.2 = y.1 * y.2 := congrArg (fun z : Cone ↦ z.val.1) h
    have hfst : -(x.1 ^ 2) = -(y.1 ^ 2) := congrArg (fun z : Cone ↦ z.val.2.1) h
    have hsnd : x.2 ^ 2 = y.2 ^ 2 := congrArg (fun z : Cone ↦ z.val.2.2) h
    rcases mul_self_eq_mul_self_iff.mp (by simpa only [pow_two] using neg_injective hfst) with ha | ha <;>
      rcases mul_self_eq_mul_self_iff.mp (by simpa only [pow_two] using hsnd) with hb | hb
    · exact Or.inl (Prod.ext ha hb)
    · by_cases h0 : y.1 = 0
      · exact Or.inr (Prod.ext (by change x.1 = -y.1; simp [ha, h0]) hb)
      · have he : x.2 = y.2 := mul_left_cancel₀ h0 (ha ▸ hmul)
        exact Or.inl (Prod.ext ha he)
    · by_cases h0 : y.2 = 0
      · exact Or.inr (Prod.ext ha (by change x.2 = -y.2; simp [hb, h0]))
      · have he : x.1 = y.1 := mul_right_cancel₀ h0 (hb ▸ hmul)
        exact Or.inl (Prod.ext he hb)
    · exact Or.inr (Prod.ext ha hb)
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      simp [parametrize]

private theorem parametrize_origin : parametrize 0 = coneVertex := by
  apply Subtype.ext
  simp [parametrize, coneVertex]

private theorem parametrize_zero (x : ℂ × ℂ) : parametrize x = coneVertex ↔ x = 0 := by
  rw [← parametrize_origin, parametrize_fibre]
  change (x = 0 ∨ x = -(0 : ℂ × ℂ)) ↔ x = 0
  rw [neg_zero, or_self]

private theorem parametrize_proper : IsProperMap parametrize := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_parametrize, ?_⟩
  intro K hK
  obtain ⟨r, hr⟩ := (hK.image continuous_radialSize).isBounded.subset_closedBall (0 : ℝ)
  apply (isCompact_closedBall (0 : ℂ × ℂ) r).of_isClosed_subset
    (hK.isClosed.preimage continuous_parametrize)
  intro x hx
  have h := hr (Set.mem_image_of_mem radialSize hx)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, radialSize_parametrize,
    abs_norm] at h
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le (le_trans (WithLp.norm_fst_le ℂ (WithLp.toLp 2 x)) h)
    (le_trans (WithLp.norm_snd_le ℂ (WithLp.toLp 2 x)) h)

private def quotHomeomorphOfClosed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Setoid X) (f : X → Y) (hf : ∀ x y, f x = f y ↔ s.r x y)
    (hs : Function.Surjective f) (hc : Continuous f) (hcl : IsClosedMap f) :
    Quotient s ≃ₜ Y := by
  have hq : IsQuotientMap (Setoid.kerLift f) :=
    isQuotientMap_quotient_mk'.of_comp_isQuotientMap (hcl.isQuotientMap hc hs)
  have he : IsHomeomorph (Setoid.kerLift f) :=
    isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, Setoid.kerLift_injective f⟩
  let e := Homeomorph.Quotient.congrRight (r := s) (r' := Setoid.ker f)
    (fun x y ↦ (hf x y).symm)
  exact e.trans (he.homeomorph _)

theorem polynomialParametrization :
    NilpotentConeRadialTopologySpecs.Expected.PolynomialParametrization :=
  ⟨parametrize_proper, parametrize_surjective, parametrize_fibre, parametrize_zero⟩

theorem antipodalQuotientHomeomorphism :
    NilpotentConeRadialTopologySpecs.Expected.AntipodalQuotientHomeomorphism :=
  ⟨quotHomeomorphOfClosed _ _ parametrize_fibre parametrize_surjective
    continuous_parametrize parametrize_proper.isClosedMap, fun _ ↦ rfl, parametrize_origin⟩

/-- The Hermitian norm on the pair of complex coordinates is the Euclidean
norm on the four real coordinates. -/
private def realPairIsometry : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] ComplexPair where
  toFun x := WithLp.toLp 2 (realComplexCoordinates x)
  invFun z := WithLp.toLp 2 ![z.fst.re, z.fst.im, z.snd.re, z.snd.im]
  left_inv x := by
    ext i
    fin_cases i <;> rfl
  right_inv z := by
    apply (WithLp.ofLp_injective 2)
    change (Complex.mk z.fst.re z.fst.im, Complex.mk z.snd.re z.snd.im) = (z.fst, z.snd)
    exact Prod.ext (Complex.ext rfl rfl) (Complex.ext rfl rfl)
  map_add' _ _ := rfl
  map_smul' a x := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply Complex.ext <;> simp [realComplexCoordinates, WithLp.ofLp_smul]
    · apply Complex.ext <;> simp [realComplexCoordinates, WithLp.ofLp_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    change ‖Complex.mk (x 0) (x 1)‖ ^ 2 + ‖Complex.mk (x 2) (x 3)‖ ^ 2 =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2
    rw [Complex.sq_norm, Complex.sq_norm]
    change x 0 * x 0 + x 1 * x 1 + (x 2 * x 2 + x 3 * x 3) = _
    ring

private def complexPairIsometry : ComplexPair ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun z := WithLp.toLp 2 ![z.fst, z.snd]
  invFun z := WithLp.toLp 2 (z 0, z 1)
  left_inv _ := rfl
  right_inv z := by
    ext i
    fin_cases i <;> rfl
  map_add' x y := by
    ext i
    fin_cases i <;> rfl
  map_smul' a x := by
    ext i
    fin_cases i <;> rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, WithLp.prod_norm_sq_eq_of_L2]
    rfl

private theorem realPairIsometry_apply (x : EuclideanSpace ℝ (Fin 4)) :
    realPairIsometry x = WithLp.toLp 2 (realComplexCoordinates x) := rfl

private theorem realComplexCoordinates_injective : Function.Injective realComplexCoordinates :=
  fun x y h ↦ realPairIsometry.injective ((realPairIsometry_apply x).trans
    ((congrArg (WithLp.toLp 2) h).trans (realPairIsometry_apply y).symm))

private theorem realComplexCoordinates_neg (x : EuclideanSpace ℝ (Fin 4)) :
    realComplexCoordinates (-x) = -realComplexCoordinates x :=
  calc
    realComplexCoordinates (-x) = WithLp.ofLp (realPairIsometry (-x)) := rfl
    _ = WithLp.ofLp (-realPairIsometry x) := congrArg WithLp.ofLp (map_neg realPairIsometry x)
    _ = -realComplexCoordinates x := rfl

private theorem continuous_realComplexCoordinates : Continuous realComplexCoordinates := by
  change Continuous (WithLp.ofLp ∘ realPairIsometry)
  exact (WithLp.prod_continuous_ofLp 2 ℂ ℂ).comp realPairIsometry.continuous

private theorem radialSize_nonneg (z : Cone) : 0 ≤ radialSize z := Real.sqrt_nonneg _

private theorem radialSize_eq_zero (z : Cone) : radialSize z = 0 ↔ z = coneVertex := by
  obtain ⟨x, rfl⟩ := parametrize_surjective z
  rw [radialSize_parametrize, norm_eq_zero, WithLp.toLp_eq_zero, parametrize_zero]

private theorem radialOpen (r : ℝ) : IsOpen {z : Cone | radialSize z < r} :=
  isOpen_lt continuous_radialSize continuous_const

private theorem radialCofinal :
    ∀ U ∈ nhds coneVertex, ∃ r > 0, {z : Cone | radialSize z < r} ⊆ U := by
  intro U hU
  let g : ComplexPair → Cone := parametrize ∘ WithLp.ofLp
  have hg : Continuous g := continuous_parametrize.comp (WithLp.prod_continuous_ofLp 2 ℂ ℂ)
  have hg0 : g 0 = coneVertex := parametrize_origin
  have hpre : g ⁻¹' U ∈ nhds (0 : ComplexPair) :=
    hg.continuousAt.preimage_mem_nhds (hg0 ▸ hU)
  obtain ⟨r, hr, hsubset⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r, hr, ?_⟩
  intro z hz
  obtain ⟨x, rfl⟩ := parametrize_surjective z
  have hx : WithLp.toLp 2 x ∈ Metric.ball (0 : ComplexPair) r := by
    rw [Metric.mem_ball, dist_zero_right, ← radialSize_parametrize]
    exact hz
  exact hsubset hx

private theorem linkQuotient_open : IsOpenQuotientMap (quotientMap 3) := by
  change IsOpenQuotientMap (Quotient.mk (P202Specs.RealProjectiveHomology.antipodalSetoid 3))
  let q := Quotient.mk (P202Specs.RealProjectiveHomology.antipodalSetoid 3)
  refine ⟨Quotient.mk_surjective, continuous_quot_mk, ?_⟩
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  have he : q ⁻¹' (q '' U) = U ∪ antipodal 3 ⁻¹' U := by
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      rcases (Quotient.exact h : y.val = x.val ∨ y.val = -x.val) with h | h
      · exact Or.inl (Subtype.ext h ▸ hy)
      · apply Or.inr
        change antipodal 3 x ∈ U
        exact (show y = antipodal 3 x from Subtype.ext h) ▸ hy
    · rintro (h | h)
      · exact ⟨x, h, rfl⟩
      · exact ⟨antipodal 3 x, h, Quotient.sound (Or.inr rfl)⟩
  change IsOpen (q ⁻¹' (q '' U))
  rw [he]
  exact hU.union (hU.preimage (antipodal 3).hom.continuous)

private def atRadius (d : ProjectiveLink) (a : ℝ) : Cone :=
  Quotient.liftOn d (fun p : sphere 3 ↦ parametrize (a • realComplexCoordinates p.val))
    (fun p q h ↦ (parametrize_fibre _ _).mpr (by
      change p.val = q.val ∨ p.val = -q.val at h
      rcases h with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h, realComplexCoordinates_neg, smul_neg])))

private theorem continuous_atRadius : Continuous (fun p : ℝ × ProjectiveLink ↦ atRadius p.2 p.1) := by
  apply ((IsOpenQuotientMap.id (X := ℝ)).prodMap linkQuotient_open).isQuotientMap.continuous_iff.mpr
  exact continuous_parametrize.comp (continuous_fst.smul
    (continuous_realComplexCoordinates.comp (continuous_subtype_val.comp continuous_snd)))

private theorem radialSize_atRadius (d : ProjectiveLink) (a : ℝ) (ha : 0 ≤ a) :
    radialSize (atRadius d a) = a := by
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective d
  change radialSize (parametrize (a • realComplexCoordinates p.val)) = a
  rw [radialSize_parametrize, WithLp.toLp_smul, ← realPairIsometry_apply]
  rw [norm_smul, realPairIsometry.norm_map, mem_sphere_zero_iff_norm.mp p.property,
    Real.norm_eq_abs, abs_of_nonneg ha, mul_one]

private theorem projectiveLink_nonempty : Nonempty ProjectiveLink := by
  let x : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1
  have hx : ‖x‖ = 1 := by simp [x]
  exact ⟨quotientMap 3 ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩⟩

private theorem atRadius_surjective (z : Cone) :
    ∃ d : ProjectiveLink, atRadius d (radialSize z) = z := by
  obtain ⟨x, rfl⟩ := parametrize_surjective z
  rw [radialSize_parametrize]
  by_cases h : x = 0
  · subst x
    obtain ⟨d⟩ := projectiveLink_nonempty
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective d
    refine ⟨quotientMap 3 p, ?_⟩
    change parametrize (‖(0 : ComplexPair)‖ • realComplexCoordinates p.val) = parametrize 0
    rw [norm_zero, zero_smul]
  · let y := realPairIsometry.symm (WithLp.toLp 2 x)
    have hy : ‖y‖ = ‖WithLp.toLp 2 x‖ := realPairIsometry.symm.norm_map _
    have hn : 0 < ‖y‖ := by
      rw [hy, norm_pos_iff]
      exact fun hx ↦ h ((WithLp.toLp_eq_zero 2).mp hx)
    let p : sphere 3 := ⟨‖y‖⁻¹ • y, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg hn.le, inv_mul_cancel₀ hn.ne'])⟩
    refine ⟨quotientMap 3 p, ?_⟩
    change parametrize (‖WithLp.toLp 2 x‖ • realComplexCoordinates p.val) = parametrize x
    rw [← hy]
    have he : realComplexCoordinates p.val = WithLp.ofLp (realPairIsometry p.val) := rfl
    rw [he, ← WithLp.ofLp_smul]
    change parametrize (WithLp.ofLp (‖y‖ • realPairIsometry (‖y‖⁻¹ • y))) = parametrize x
    rw [← map_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    exact congrArg (parametrize ∘ WithLp.ofLp) (realPairIsometry.apply_symm_apply _)

private theorem atRadius_injective_link {a : ℝ} (ha : 0 < a) {d e : ProjectiveLink}
    (h : atRadius d a = atRadius e a) : d = e := by
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective d
  obtain ⟨y, rfl⟩ := Quotient.mk_surjective e
  apply Quotient.sound
  change x.val = y.val ∨ x.val = -y.val
  have hs : a • realComplexCoordinates x.val = a • realComplexCoordinates y.val ∨
    a • realComplexCoordinates x.val = -(a • realComplexCoordinates y.val) :=
    (parametrize_fibre _ _).mp h
  rcases hs with hs | hs
  · exact Or.inl (realComplexCoordinates_injective (smul_right_injective _ ha.ne' hs))
  · rw [← smul_neg, ← realComplexCoordinates_neg] at hs
    exact Or.inr (realComplexCoordinates_injective (smul_right_injective _ ha.ne' hs))

/-- A ray map retaining a continuous height coordinate is closed when its
direction space is compact. -/
private theorem closedMap_of_height {D H Y : Type*}
    [TopologicalSpace D] [CompactSpace D] [TopologicalSpace H] [TopologicalSpace Y] [T2Space Y]
    {f : H × D → Y} {g : Y → H} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, g (f p) = p.1) : IsClosedMap f := by
  intro T hT
  let k : Y × D → H × D := fun p ↦ (g p.1, p.2)
  have hk : Continuous k := (hg.comp continuous_fst).prodMk continuous_snd
  have he : f '' T = Prod.fst '' (k ⁻¹' T ∩ {p : Y × D | f (k p) = p.1}) := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(f p, p.2), ⟨?_, ?_⟩, rfl⟩
      · change (g (f p), p.2) ∈ T
        rw [h]
        exact hp
      · change f (g (f p), p.2) = f p
        rw [h]
    · rintro ⟨p, ⟨hp, heq⟩, rfl⟩
      exact ⟨k p, hp, heq⟩
  rw [he]
  exact isClosedMap_fst_of_compactSpace _ ((hT.preimage hk).inter
    (isClosed_eq (hf.comp hk) continuous_fst))

private def truncatedRay (r : ℝ) (p : Set.Ico (0 : ℝ) r × ProjectiveLink) : RadialBall r :=
  ⟨atRadius p.2 p.1.val,
    (radialSize_atRadius p.2 p.1.val p.1.property.1).trans_lt p.1.property.2⟩

private theorem truncatedRay_fibre (r : ℝ) (p q : Set.Ico (0 : ℝ) r × ProjectiveLink) :
    truncatedRay r p = truncatedRay r q ↔ (radialConeSetoid r).r p q := by
  change _ ↔ p = q ∨ (p.1.val = 0 ∧ q.1.val = 0)
  constructor
  · intro h
    have h' : atRadius p.2 p.1.val = atRadius q.2 q.1.val := congrArg Subtype.val h
    have ha : p.1.val = q.1.val := by
      rw [← radialSize_atRadius p.2 _ p.1.property.1,
        ← radialSize_atRadius q.2 _ q.1.property.1, h']
    rcases eq_or_lt_of_le p.1.property.1 with (h0 | hpos)
    · exact Or.inr ⟨h0.symm, ha.symm.trans h0.symm⟩
    · rw [← ha] at h'
      exact Or.inl (Prod.ext (Subtype.ext ha) (atRadius_injective_link hpos h'))
  · rintro (rfl | ⟨hp, hq⟩)
    · rfl
    · have h1 : atRadius p.2 p.1.val = coneVertex :=
        (radialSize_eq_zero _).mp ((radialSize_atRadius _ _ p.1.property.1).trans hp)
      have h2 : atRadius q.2 q.1.val = coneVertex :=
        (radialSize_eq_zero _).mp ((radialSize_atRadius _ _ q.1.property.1).trans hq)
      exact Subtype.ext (h1.trans h2.symm)

private def truncatedHomeomorph (r : ℝ) : RadialCone r ≃ₜ RadialBall r := by
  have hf : Continuous (truncatedRay r) := (continuous_atRadius.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
  refine quotHomeomorphOfClosed _ _ (truncatedRay_fibre r) ?_ hf ?_
  · intro z
    obtain ⟨d, hd⟩ := atRadius_surjective z.val
    exact ⟨(⟨radialSize z.val, radialSize_nonneg _, z.property⟩, d), Subtype.ext hd⟩
  · let h : RadialBall r → Set.Ico (0 : ℝ) r :=
      fun z ↦ ⟨radialSize z.val, radialSize_nonneg _, z.property⟩
    exact closedMap_of_height hf ((continuous_radialSize.comp continuous_subtype_val).subtype_mk
      (fun z ↦ (h z).property)) (fun p ↦ Subtype.ext
        (radialSize_atRadius p.2 p.1.val p.1.property.1))

private def puncturedRay (r : ℝ) (p : Set.Ioo (0 : ℝ) r × ProjectiveLink) : PuncturedBall r :=
  ⟨atRadius p.2 p.1.val,
    (radialSize_atRadius p.2 p.1.val p.1.property.1.le).trans_lt p.1.property.2,
    fun h ↦ p.1.property.1.ne' ((radialSize_atRadius p.2 p.1.val p.1.property.1.le).symm.trans
      ((radialSize_eq_zero _).mpr h))⟩

private def puncturedHomeomorph (r : ℝ) : Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r := by
  have hf : Continuous (puncturedRay r) := (continuous_atRadius.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _
  have hpos (z : PuncturedBall r) : 0 < radialSize z.val :=
    lt_of_le_of_ne (radialSize_nonneg _) (Ne.symm fun hz ↦ z.property.2 ((radialSize_eq_zero _).mp hz))
  have hbij : Function.Bijective (puncturedRay r) := by
    constructor
    · intro p q hpq
      have h' : atRadius p.2 p.1.val = atRadius q.2 q.1.val := congrArg Subtype.val hpq
      have ha : p.1.val = q.1.val := by
        rw [← radialSize_atRadius p.2 _ p.1.property.1.le,
          ← radialSize_atRadius q.2 _ q.1.property.1.le, h']
      rw [← ha] at h'
      exact Prod.ext (Subtype.ext ha) (atRadius_injective_link p.1.property.1 h')
    · intro z
      obtain ⟨d, hd⟩ := atRadius_surjective z.val
      exact ⟨(⟨radialSize z.val, hpos z, z.property.1⟩, d), Subtype.ext hd⟩
  apply (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousClosed hf
  let h : PuncturedBall r → Set.Ioo (0 : ℝ) r := fun z ↦ ⟨radialSize z.val, hpos z, z.property.1⟩
  exact closedMap_of_height hf ((continuous_radialSize.comp continuous_subtype_val).subtype_mk
    (fun z ↦ (h z).property)) (fun p ↦ Subtype.ext
      (radialSize_atRadius p.2 p.1.val p.1.property.1.le))

private def scaleCone (a : ℝ) (z : Cone) : Cone := by
  let c := (a : ℂ) ^ 2
  refine ⟨c • z.val, ?_⟩
  have hz := z.property
  change z.val.1 ^ 2 + z.val.2.1 * z.val.2.2 = 0 at hz
  change (c * z.val.1) ^ 2 + (c * z.val.2.1) * (c * z.val.2.2) = 0
  linear_combination c ^ 2 * hz

private theorem scaleCone_parametrize (a : ℝ) (x : ℂ × ℂ) :
    scaleCone a (parametrize x) = parametrize (a • x) := by
  apply Subtype.ext
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change (a : ℂ) ^ 2 * (x.1 * x.2) = (a • x.1) * (a • x.2)
    simp only [Complex.real_smul]
    ring
  · change (a : ℂ) ^ 2 * -(x.1 ^ 2) = -((a • x.1) ^ 2)
    simp only [Complex.real_smul]
    ring
  · change (a : ℂ) ^ 2 * x.2 ^ 2 = (a • x.2) ^ 2
    simp only [Complex.real_smul]
    ring

private theorem radialSize_scaleCone (a : ℝ) (z : Cone) :
    radialSize (scaleCone a z) = |a| * radialSize z := by
  obtain ⟨x, rfl⟩ := parametrize_surjective z
  rw [scaleCone_parametrize, radialSize_parametrize, radialSize_parametrize]
  change ‖a • WithLp.toLp 2 x‖ = |a| * ‖WithLp.toLp 2 x‖
  rw [norm_smul, Real.norm_eq_abs]

private def shrinkRadialBall {r : ℝ} (p : unitInterval × RadialBall r) : RadialBall r :=
  ⟨scaleCone (1 - p.1.val) p.2.val, by
    rw [radialSize_scaleCone, abs_of_nonneg (sub_nonneg.mpr p.1.property.2)]
    exact (mul_le_of_le_one_left (radialSize_nonneg _) (sub_le_self _ p.1.property.1)).trans_lt
      p.2.property⟩

private theorem continuous_shrinkRadialBall (r : ℝ) :
    Continuous (shrinkRadialBall (r := r)) := by
  have ha : Continuous (fun p : unitInterval × RadialBall r ↦ (1 : ℝ) - p.1.val) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_fst)
  have hz : Continuous (fun p : unitInterval × RadialBall r ↦ p.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hc := (Complex.continuous_ofReal.comp ha).pow 2
  exact (hc.smul hz).subtype_mk (fun p ↦ (scaleCone (1 - p.1.val) p.2.val).property)
    |>.subtype_mk (fun p ↦ (shrinkRadialBall p).property)

private def ballContraction {r : ℝ} (hr : 0 < r) :
    (ContinuousMap.id (RadialBall r)).HomotopyRel (radialContractionTarget hr)
      {z : RadialBall r | z.val = coneVertex} where
  toFun := shrinkRadialBall
  continuous_toFun := continuous_shrinkRadialBall r
  map_zero_left z := by
    refine Subtype.ext (Subtype.ext ?_)
    change (((1 - (0 : ℝ) : ℝ) : ℂ) ^ 2) • z.val.val = z.val.val
    simp only [sub_zero, Complex.ofReal_one, one_pow, one_smul]
  map_one_left z := by
    refine Subtype.ext (Subtype.ext ?_)
    change (((1 - (1 : ℝ) : ℝ) : ℂ) ^ 2) • z.val.val = (0 : ℂ × ℂ × ℂ)
    simp only [sub_self, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), zero_smul]
  prop' t z hz := by
    change z.val = coneVertex at hz
    refine Subtype.ext (Subtype.ext ?_)
    change (((1 - t.val : ℝ) : ℂ) ^ 2) • z.val.val = z.val.val
    rw [hz]
    exact smul_zero _

private def interpolateHeight {r : ℝ} (hr : 0 < r) (t : unitInterval)
    (a : Set.Ioo (0 : ℝ) r) : Set.Ioo (0 : ℝ) r :=
  ⟨(1 - t.val) * a.val + t.val * (r / 2), by
    have hmid : r / 2 ∈ Set.Ioo (0 : ℝ) r := ⟨by linarith, by linarith⟩
    simpa only [AffineMap.lineMap_apply_ring] using
      (convex_Ioo (𝕜 := ℝ) (0 : ℝ) r).lineMap_mem a.property hmid t.property⟩

private def punctureContraction {r : ℝ} (hr : 0 < r)
    (e : Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r) :
    (ContinuousMap.id (PuncturedBall r)).HomotopyRel (puncturedContractionTarget hr e)
      {z : PuncturedBall r | (e.symm z).1.val = r / 2} where
  toFun p := e (interpolateHeight hr p.1 (e.symm p.2).1, (e.symm p.2).2)
  continuous_toFun := by
    apply e.continuous.comp
    have h : Continuous (fun p : unitInterval × PuncturedBall r ↦ e.symm p.2) :=
      e.symm.continuous.comp continuous_snd
    have ha : Continuous (fun p : unitInterval × PuncturedBall r ↦ (e.symm p.2).1.val) :=
      continuous_subtype_val.comp (continuous_fst.comp h)
    have ht : Continuous (fun p : unitInterval × PuncturedBall r ↦ p.1.val) :=
      continuous_subtype_val.comp continuous_fst
    exact ((((continuous_const.sub ht).mul ha).add (ht.mul continuous_const)).subtype_mk _).prodMk
      (continuous_snd.comp h)
  map_zero_left z := by
    change e (interpolateHeight hr 0 (e.symm z).1, (e.symm z).2) = z
    calc
      _ = e (e.symm z) := by
        apply congrArg e
        apply Prod.ext
        · exact Subtype.ext (by simp [interpolateHeight])
        · rfl
      _ = z := e.apply_symm_apply z
  map_one_left z := by
    change e (interpolateHeight hr 1 (e.symm z).1, (e.symm z).2) =
      e (⟨r / 2, _⟩, (e.symm z).2)
    exact congrArg e (Prod.ext (Subtype.ext (by simp [interpolateHeight])) rfl)
  prop' t z hz := by
    change e (interpolateHeight hr t (e.symm z).1, (e.symm z).2) = z
    change (e.symm z).1.val = r / 2 at hz
    calc
      _ = e (e.symm z) := by
        apply congrArg e
        apply Prod.ext
        · apply Subtype.ext
          change (1 - t.val) * (e.symm z).1.val + t.val * (r / 2) = (e.symm z).1.val
          rw [hz]
          ring
        · rfl
      _ = z := e.apply_symm_apply z

theorem radialNeighborhoods :
    NilpotentConeRadialTopologySpecs.Expected.RadialNeighborhoods := by
  refine ⟨⟨realPairIsometry.trans complexPairIsometry, fun _ ↦ rfl⟩, ?_, radialCofinal,
    fun r _ ↦ truncatedHomeomorph r, fun r _ ↦ puncturedHomeomorph r,
    (fun _ _ _ _ ↦ rfl), (fun _ _ _ _ ↦ rfl),
    (fun _ _ _ _ _ _ ↦ Subtype.ext rfl), (fun _ hr ↦ ⟨ballContraction hr⟩),
    (fun r hr ↦ ⟨punctureContraction hr (puncturedHomeomorph r)⟩)⟩
  intro r hr
  exact ⟨radialOpen r, (radialOpen r).mem_nhds (by simpa [radialSize, coneVertex] using hr)⟩

end

end RepTheorySurvey.Geometric.NilpotentConeRadialTopology
