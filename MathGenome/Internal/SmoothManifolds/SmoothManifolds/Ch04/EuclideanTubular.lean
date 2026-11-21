import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.EuclideanTubular
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.MapClasses
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.InjectiveShrinking
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace SmoothManifolds.EuclideanTubular
open ModelData AtlasData MapData EmbeddedData FiniteRegularityData
  MapClassData EuclideanTubularData Set

variable {n q : ℕ} {M : Type} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)

theorem tangentChart_mem (p : M) : tangentChart S p ∈ S.smoothStructure.val :=
  (Classical.choose_spec (S.smoothStructure.property.1.1 p)).1

theorem mem_tangentChart_source (p : M) : p ∈ (tangentChart S p).source :=
  (Classical.choose_spec (S.smoothStructure.property.1.1 p)).2

/-- Source chart changes do not change the image of the differential. -/
theorem chartDerivative_range_eq
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothMap S T j) (p : M)
    (e d : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (hpd : p ∈ d.source) :
    LinearMap.range (chartDerivative e (euclideanChart q) j p).toLinearMap =
      LinearMap.range (chartDerivative d (euclideanChart q) j p).toLinearMap := by
  have hf : ManifoldContDiff (⊤ : ℕ∞) S.smoothStructure.val T.smoothStructure.val j := hj
  have factor (e d : ModelChart n .euclidean M)
      (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
      (hp : p ∈ e.source) (hpd : p ∈ d.source) :
      chartDerivative e (euclideanChart q) j p =
        (chartDerivative d (euclideanChart q) j p).comp (chartDerivative e d id p) := by
    have h := FiniteRegularity.chartDerivative_changeCharts (⊤ : ℕ∞) (by simp)
      _ _ S.smoothStructure.property.1 T.smoothStructure.property.1 j hf p
      e d (euclideanChart q) (euclideanChart q) he hd hT hT hp hpd (mem_univ _) (mem_univ _)
    rw [FiniteRegularity.chartDerivative_id (euclideanChart q) (j p) (mem_univ _)] at h
    simpa using h
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    exact ⟨chartDerivative e d id p v, congrArg (fun L => L v) (factor e d he hd hp hpd) |>.symm⟩
  · rintro y ⟨v, rfl⟩
    exact ⟨chartDerivative d e id p v, congrArg (fun L => L v) (factor d e hd he hpd hp) |>.symm⟩

theorem ambientTangent_eq_chart
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothMap S T j) (p : M) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : p ∈ e.source) :
    ambientTangent S j p =
      LinearMap.range (chartDerivative e (euclideanChart q) j p).toLinearMap :=
  chartDerivative_range_eq S j T hT hj p _ e (tangentChart_mem S p) he
    (mem_tangentChart_source S p) hp

/-- The chosen-coordinate definition is the image of the actual intrinsic
inclusion differential, in standard ambient coordinates. -/
theorem ambientTangent_eq_differential
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothMap S T j) (p : M)
    (L : TangentData.TangentSpace S p →ₗ[ℝ] TangentData.TangentSpace T (j p))
    (F : TangentData.TangentSpace T (j p) ≃ₗ[ℝ] Euclidean q)
    (hL : DifferentialData.IsDifferential S T j p L)
    (hF : DifferentialData.IsChartCoordinates T (j p) (euclideanChart q) F) :
    ambientTangent S j p = LinearMap.range (F.toLinearMap.comp L) := by
  obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates S p
    (tangentChart S p) (tangentChart_mem S p) (mem_tangentChart_source S p)
  have hformula (v) := FiniteRegularity.smooth_jacobian_coordinateDerivative S T j hj p L hL
    (tangentChart S p) (euclideanChart q) (tangentChart_mem S p) hT
    (mem_tangentChart_source S p) (mem_univ _) E F hE hF v
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨E.symm v, by simpa using hformula (E.symm v)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨E v, (hformula v).symm⟩

/-- The tangent dimension is n, using the embedding's actual immersion
hypothesis and the upstream full tangent invariants. -/
theorem ambientTangent_finrank
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (p : M) :
    Module.finrank ℝ (ambientTangent S j p) = n := by
  have hj1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ j (by simp) hj.1
  have hinj := (MapClasses.chart_invariants S T j hj1 p (tangentChart S p)
    (euclideanChart q) (tangentChart_mem S p) hT
    (mem_tangentChart_source S p) (mem_univ _)).2.1.mp (hj.2.2.1 p)
  exact (LinearMap.finrank_range_of_inj hinj).trans (by simp [ModelData.Euclidean])

/-- Dot-product orthogonality is the usual annihilator under the canonical
identification of real coordinate space with its dual. -/
theorem dotOrthogonal_eq_comap (E : Submodule ℝ (Euclidean q)) :
    dotOrthogonal E = E.dualAnnihilator.comap (dotProductEquiv ℝ (Fin q)).toLinearMap := by
  ext v
  simp only [dotOrthogonal, Submodule.mem_mk, Submodule.mem_comap,
    Submodule.mem_dualAnnihilator]
  rfl

theorem finrank_add_finrank_dotOrthogonal (E : Submodule ℝ (Euclidean q)) :
    Module.finrank ℝ E + Module.finrank ℝ (dotOrthogonal E) = q := by
  have hd := ((dotProductEquiv ℝ (Fin q)).ofSubmodule' E.dualAnnihilator).finrank_eq
  rw [← dotOrthogonal_eq_comap] at hd
  rw [hd]
  simpa [ModelData.Euclidean] using Subspace.finrank_add_finrank_dualAnnihilator_eq E

theorem isCompl_dotOrthogonal (E : Submodule ℝ (Euclidean q)) :
    IsCompl E (dotOrthogonal E) := by
  have hd : Disjoint E (dotOrthogonal E) := by
    apply disjoint_iff_inf_le.mpr
    intro z hz
    exact (dotProduct_self_eq_zero.mp (hz.2 z hz.1))
  apply (Submodule.isCompl_iff_disjoint E (dotOrthogonal E) ?_).mpr hd
  exact le_of_eq (by simpa [ModelData.Euclidean] using
    (finrank_add_finrank_dotOrthogonal E).symm)

theorem normalFiber_finrank
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (p : M) :
    Module.finrank ℝ (normalFiber S j p) = q - n := by
  have h := finrank_add_finrank_dotOrthogonal (ambientTangent S j p)
  rw [ambientTangent_finrank S j T hT hj p] at h
  change Module.finrank ℝ (dotOrthogonal (ambientTangent S j p)) = q - n
  omega

/-- The linear map which will be the derivative of addition at the zero
section is an isomorphism. Establishing that it is the actual derivative
still requires construction of the smooth normal bundle charts. -/
noncomputable def tangentNormalEquiv (p : M) :
    (ambientTangent S j p × normalFiber S j p) ≃ₗ[ℝ] Euclidean q :=
  (ambientTangent S j p).prodEquivOfIsCompl (normalFiber S j p)
    (isCompl_dotOrthogonal (ambientTangent S j p))

@[simp] theorem tangentNormalEquiv_apply (p : M)
    (w : ambientTangent S j p) (v : normalFiber S j p) :
    tangentNormalEquiv S j p (w, v) = w.val + v.val := rfl

@[simp] theorem normalScale_one (z : NormalTotal S j) : normalScale S j 1 z = z := by
  apply Subtype.ext
  simp [normalScale]

@[simp] theorem normalScale_zero (z : NormalTotal S j) :
    normalScale S j 0 z = normalZero S j z.val.1 := by
  apply Subtype.ext
  simp [normalScale, normalZero]

@[simp] theorem normalScale_normalZero (t : ℝ) (p : M) :
    normalScale S j t (normalZero S j p) = normalZero S j p := by
  apply Subtype.ext
  simp [normalScale, normalZero]

theorem normalScale_mul (s t : ℝ) (z : NormalTotal S j) :
    normalScale S j s (normalScale S j t z) = normalScale S j (s * t) z := by
  apply Subtype.ext
  simp [normalScale, mul_smul]

theorem continuous_normalZero : Continuous (normalZero S j) :=
  (continuous_id.prodMk continuous_const).subtype_mk _

theorem continuous_normalScale :
    Continuous (fun z : ℝ × NormalTotal S j => normalScale S j z.1 z.2) := by
  apply Continuous.subtype_mk
  exact (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
    (continuous_fst.smul (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))

theorem continuous_normalAddition (hj : Continuous j) :
    Continuous (normalAddition S j) :=
  (hj.comp (continuous_fst.comp continuous_subtype_val)).add
    (continuous_snd.comp continuous_subtype_val)

theorem radialCore_subset (V : Set (NormalTotal S j)) : radialCore S j V ⊆ V := by
  intro z hz
  simpa using hz 1 ⟨zero_le_one, le_rfl⟩

theorem normalZero_mem_radialCore {V : Set (NormalTotal S j)} (p : M)
    (hp : normalZero S j p ∈ V) : normalZero S j p ∈ radialCore S j V := by
  intro t ht
  simpa using hp

theorem radialCore_star {V : Set (NormalTotal S j)} (z : NormalTotal S j)
    (hz : z ∈ radialCore S j V) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    normalScale S j t z ∈ radialCore S j V := by
  intro s hs
  rw [normalScale_mul]
  exact hz (s * t) ⟨mul_nonneg hs.1 ht.1,
    (mul_le_mul_of_nonneg_right hs.2 ht.1).trans (by simpa using ht.2)⟩

/-- The complement is the projection of a closed set along the compact
parameter interval. No compactness of the base or of V is needed. -/
theorem isOpen_radialCore {V : Set (NormalTotal S j)} (hV : IsOpen V) :
    IsOpen (radialCore S j V) := by
  let I := Icc (0 : ℝ) 1
  let F : I × NormalTotal S j → NormalTotal S j :=
    fun z => normalScale S j z.1.val z.2
  have hF : Continuous F := (continuous_normalScale S j).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hbad : IsClosed (Prod.snd '' (F ⁻¹' Vᶜ)) :=
    isClosedMap_snd_of_compactSpace _ (hV.isClosed_compl.preimage hF)
  have heq : radialCore S j V = (Prod.snd '' (F ⁻¹' Vᶜ))ᶜ := by
    ext z
    constructor
    · intro hz hzbad
      obtain ⟨⟨t, y⟩, hy, hyz⟩ := hzbad
      change y = z at hyz
      subst y
      exact hy (hz t.val t.property)
    · intro hz t ht
      by_contra hv
      exact hz ⟨(⟨t, ht⟩, z), hv, rfl⟩

  rw [heq]
  exact hbad.isOpen_compl

/-- Radially invariant shrinking inside any prescribed open neighborhood. -/
theorem radial_shrinking (V : Set (NormalTotal S j)) (hV : IsOpen V)
    (hzero : ∀ p, normalZero S j p ∈ V) :
    ∃ U : Set (NormalTotal S j), IsOpen U ∧ U ⊆ V ∧
      (∀ p, normalZero S j p ∈ U) ∧
      ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ U :=
  ⟨radialCore S j V, isOpen_radialCore S j hV, radialCore_subset S j V,
    fun p => normalZero_mem_radialCore S j p (hzero p),
    fun z hz t ht => radialCore_star S j z hz t ht⟩

/-- The zero section carries exactly the topology of the original base. -/
def normalZeroHomeomorph : M ≃ₜ range (normalZero S j) where
  toFun p := ⟨normalZero S j p, ⟨p, rfl⟩⟩
  invFun z := z.val.val.1
  left_inv _ := rfl
  right_inv z := by
    obtain ⟨z, p, rfl⟩ := z
    rfl
  continuous_toFun := (continuous_normalZero S j).subtype_mk _
  continuous_invFun := continuous_fst.comp
    (continuous_subtype_val.comp continuous_subtype_val)

/-- Under an embedded inclusion, the total-space topology is precisely the
subspace topology of the usual ambient pair `(j(p), v)`. -/
theorem normalTotal_embedding (hj : Topology.IsEmbedding j) :
    Topology.IsEmbedding (fun z : NormalTotal S j => (j z.val.1, z.val.2)) :=
  (hj.prodMap Topology.IsEmbedding.id).comp Topology.IsEmbedding.subtypeVal

include S in
/-- Local compactness of the embedded base supplies the locally closed image
needed for shrinking. No closed-image hypothesis is necessary. -/
theorem embedded_range_isLocallyClosed (hj : Topology.IsEmbedding j) :
    IsLocallyClosed (range j) := by
  letI := SmoothManifolds.TopologicalManifold.locallyCompactSpace S.topologicalManifold
  apply isLocallyClosed_iff_isLocallyClosedAt.mpr
  rintro y ⟨p, rfl⟩
  obtain ⟨K, hK, hpK⟩ := exists_compact_mem_nhds p
  obtain ⟨O, hO, heq⟩ := hj.isInducing.isOpen_iff.mp (isOpen_interior (s := K))
  have hpO : j p ∈ O := by
    change p ∈ j ⁻¹' O
    rw [heq]
    exact mem_interior_iff_mem_nhds.mpr hpK
  refine ⟨O, hO.mem_nhds hpO, j '' K, (hK.image hj.continuous).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, p, rfl⟩
    refine ⟨hy, p, interior_subset ?_, rfl⟩
    change p ∈ j ⁻¹' O at hy
    rwa [heq] at hy
  · rintro ⟨hy, p, hp, rfl⟩
    exact ⟨hy, p, rfl⟩

/-- Global injectivity and radial shrinking once the geometric local inverse
has been established. These are helper hypotheses,
not additional assumptions in `euclidean_tubularType`. -/
theorem normal_global_injective
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hj : Topology.IsEmbedding j)
    (hloc : ∀ p : M, ∃ V : Set (NormalTotal S j),
      IsOpen V ∧ normalZero S j p ∈ V ∧ InjOn (normalAddition S j) V) :
    ∃ V : Set (NormalTotal S j), IsOpen V ∧
      (∀ p, normalZero S j p ∈ V) ∧ InjOn (normalAddition S j) V ∧
      ∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V := by
  have he : Topology.IsEmbedding
      (fun z : range (normalZero S j) => normalAddition S j z.val) := by
    convert hj.comp (normalZeroHomeomorph S j).symm.isEmbedding using 1
    funext z
    obtain ⟨z, p, rfl⟩ := z
    simp [normalAddition, normalZero, normalZeroHomeomorph]
  have him : normalAddition S j '' range (normalZero S j) = range j := by
    ext y
    constructor
    · rintro ⟨z, ⟨p, rfl⟩, rfl⟩
      exact ⟨p, by simp [normalAddition, normalZero]⟩
    · rintro ⟨p, rfl⟩
      exact ⟨normalZero S j p, ⟨p, rfl⟩, by simp [normalAddition, normalZero]⟩
  obtain ⟨V, hV, hzero, hinj⟩ := injective_shrinking T.topologicalManifold
    (normalAddition S j) (range (normalZero S j))
    (continuous_normalAddition S j hj.continuous) he
    (him ▸ embedded_range_isLocallyClosed S j hj)
    (fun z hz => by obtain ⟨p, rfl⟩ := hz; exact hloc p)
  obtain ⟨U, hU, hUV, hzeroU, hstar⟩ :=
    radial_shrinking S j V hV (fun p => hzero ⟨p, rfl⟩)
  exact ⟨U, hU, hzeroU, hinj.mono hUV, hstar⟩

section Deformation
variable (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
  (h : V ≃ₜ W)
  (hzero : ∀ p, normalZero S j p ∈ V)
  (hstar : ∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V)
  (hadd : ∀ z : V, (h z).val = normalAddition S j z.val)

def tubeRetraction (y : W) : M := (h.symm y).val.val.1

def tubeDeformation (z : Icc (0 : ℝ) 1 × W) : W :=
  h ⟨normalScale S j (1 - z.1.val) (h.symm z.2).val,
    hstar _ (h.symm z.2).property _ ⟨sub_nonneg.mpr z.1.property.2,
      sub_le_self _ z.1.property.1⟩⟩

theorem continuous_tubeRetraction : Continuous (tubeRetraction S j V W h) :=
  continuous_fst.comp (continuous_subtype_val.comp (continuous_subtype_val.comp h.symm.continuous))

theorem continuous_tubeDeformation : Continuous (tubeDeformation S j V W h hstar) := by
  apply h.continuous.comp
  apply Continuous.subtype_mk
  exact (continuous_normalScale S j).comp
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp (h.symm.continuous.comp continuous_snd)))

include hadd in
theorem tube_inverse_zero (p : M) (hp : j p ∈ W) :
    h.symm ⟨j p, hp⟩ = ⟨normalZero S j p, hzero p⟩ := by
  apply h.symm_apply_eq.mpr
  apply Subtype.ext
  simpa [normalAddition, normalZero] using (hadd ⟨normalZero S j p, hzero p⟩).symm

include hzero hadd in
theorem tubeRetraction_eq_self (p : M) (hp : j p ∈ W) :
    tubeRetraction S j V W h ⟨j p, hp⟩ = p := by
  unfold tubeRetraction
  rw [tube_inverse_zero S j V W h hzero hadd]
  rfl

include hadd in
theorem tubeDeformation_formula (t : Icc (0 : ℝ) 1) (y : W) :
    (tubeDeformation S j V W h hstar (t, y)).val =
      normalAddition S j (normalScale S j (1 - t.val) (h.symm y).val) :=
  hadd _

theorem tubeDeformation_zero (y : W) :
    tubeDeformation S j V W h hstar (⟨0, le_rfl, zero_le_one⟩, y) = y := by
  unfold tubeDeformation
  rw [← h.apply_symm_apply y]
  congr 1
  apply Subtype.ext
  simp


include hadd in
theorem tubeDeformation_one (y : W) :
    (tubeDeformation S j V W h hstar (⟨1, zero_le_one, le_rfl⟩, y)).val =
      j (tubeRetraction S j V W h y) := by
  rw [tubeDeformation_formula S j V W h hstar hadd]
  simp [normalAddition, normalScale, tubeRetraction]

include hzero hadd in
theorem tubeDeformation_fixed (t : Icc (0 : ℝ) 1) (p : M) (hp : j p ∈ W) :
    (tubeDeformation S j V W h hstar (t, ⟨j p, hp⟩)).val = j p := by
  rw [tubeDeformation_formula S j V W h hstar hadd,
    tube_inverse_zero S j V W h hzero hadd]
  simp [normalAddition, normalZero, normalScale]

end Deformation

section SmoothAssembly
open Filter
open scoped Topology

/-- A germ in the subspace topology gives an ambient extension agreeing on
all domain points in a smaller ambient neighborhood. -/
theorem localExtension_of_subtype_germ {k l : ℕ} (r : ℕ∞)
    (W : Set (Euclidean k)) (f : W → Euclidean l) (y : W)
    (hf : LocalCoordinateExtension r Subtype.val f y) :
    HasLocalContDiffExtensionAt r Subtype.val f y := by
  obtain ⟨U, hU, hyU, F, hF, heq⟩ := hf
  obtain ⟨D, hD, hDeq⟩ := (mem_nhds_subtype W y _).mp heq
  obtain ⟨O, hOD, hO, hyO⟩ := mem_nhds_iff.mp hD
  refine ⟨U ∩ O, hU.inter hO, ⟨hyU, hyO⟩, F, hF.mono inter_subset_left, ?_⟩
  intro z hz
  exact hDeq (hOD hz.2)

/-- Smoothness in the standard ambient chart is precisely the ambient local
extension needed to handle the time endpoints of the deformation. -/
theorem ambient_extension_of_smooth
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (W : Set (Euclidean q)) (hW : IsOpen W) (f : W → Euclidean q)
    (hf : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      T.smoothStructure.val f) : LocallyContDiffAlong (⊤ : ℕ∞) Subtype.val f := by
  intro y
  apply localExtension_of_subtype_germ
  let e := (euclideanChart q).subtypeRestr (s := ⟨W, hW⟩) ⟨y⟩
  have he : e ∈ openSubsetAtlas T.smoothStructure.val W hW :=
    ⟨⟨y⟩, euclideanChart q, hT, rfl⟩
  exact (hf y).2 e he (euclideanChart q) hT
    (by dsimp only [e]; rw [OpenPartialHomeomorph.subtypeRestr_source]; exact mem_univ _) (mem_univ _)

/-- The explicit ambient formula extends to all real times locally. Therefore
smoothness includes both endpoints of the closed time interval. -/
theorem smooth_radial_deformation
    (W : Set (Euclidean q)) (R : W → Euclidean q)
    (hR : LocallyContDiffAlong (⊤ : ℕ∞) Subtype.val R) :
    LocallyContDiffAlong (⊤ : ℕ∞)
      (fun z : Icc (0 : ℝ) 1 × W => Fin.cons z.1.val z.2.val)
      (fun z => R z.2 + (1 - z.1.val) • (z.2.val - R z.2)) := by
  intro z
  obtain ⟨U, hU, hyU, F, hF, heq⟩ := hR z.2
  have ht : ContDiff ℝ (⊤ : ℕ∞) (Fin.tail : Euclidean (q + 1) → Euclidean q) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (fun _ : Fin (q + 1) => ℝ) i.succ)
  have htU : MapsTo (Fin.tail : Euclidean (q + 1) → Euclidean q)
      (Fin.tail ⁻¹' U) U := fun _ hy => hy
  have hFt := hF.comp ht.contDiffOn htU
  refine ⟨Fin.tail ⁻¹' U, hU.preimage ht.continuous, ?_,
    (fun x => F (Fin.tail x) + (1 - x 0) • (Fin.tail x - F (Fin.tail x))),
    hFt.add ((contDiffOn_const.sub (contDiff_apply ℝ (fun _ : Fin (q + 1) => ℝ) (0 : Fin (q + 1))).contDiffOn).smul
      (ht.contDiffOn.sub hFt)), ?_⟩
  · simpa using hyU
  · intro w hw
    simp only [Fin.tail_cons] at hw ⊢
    rw [heq w.2 hw]
    rfl

variable (T : SmoothManifold q .euclidean (Euclidean q))
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
    (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W)

theorem smooth_tubeRetraction
    (hproj : IsSmoothMap N S (fun z => z.val.1))
    (hinv : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      (openSubsetAtlas N.smoothStructure.val V hV) h.symm) :
    ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      S.smoothStructure.val (tubeRetraction S j V W h) := by
  have hprojV : ManifoldSmooth (openSubsetAtlas N.smoothStructure.val V hV)
      S.smoothStructure.val (fun z : V => z.val.val.1) :=
    (manifoldContDiff_restrict_open (⊤ : ℕ∞) N.smoothStructure.val
      S.smoothStructure.val (fun z => z.val.1) V hV).mp (fun z _ => hproj z)
  exact manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    (openSubsetAtlas_isContDiffAtlas (⊤ : ℕ∞) _ N.smoothStructure.property.1 V hV).1
    h.symm _ hinv hprojV

/-- Once the additive diffeomorphism and normal bundle are constructed, all
retraction and smooth deformation obligations follow, without a separate
smoothness assumption on a time-product manifold. -/
theorem isTubularNeighborhood_of_diffeomorphism
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothMap S T j)
    (hN : IsNormalBundleStructure S j N)
    (hzero : ∀ p, normalZero S j p ∈ V)
    (hstar : ∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V)
    (hadd : ∀ z : V, (h z).val = normalAddition S j z.val)
    (hfwd : ManifoldSmooth (openSubsetAtlas N.smoothStructure.val V hV)
      (openSubsetAtlas T.smoothStructure.val W hW) h)
    (hinv : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      (openSubsetAtlas N.smoothStructure.val V hV) h.symm) :
    IsTubularNeighborhood S T j N V W hV hW h := by
  have hr := smooth_tubeRetraction S j T N V W hV hW h hN.1 hinv
  have hR : LocallyContDiffAlong (⊤ : ℕ∞) Subtype.val
      (fun y => j (tubeRetraction S j V W h y)) :=
    ambient_extension_of_smooth T hT W hW _
      (manifoldContDiff_comp (⊤ : ℕ∞) _ _ _ S.smoothStructure.property.1.1
        _ j hr hj)
  have hH := smooth_radial_deformation W _ hR
  have himage : range j ⊆ W := by
    rintro y ⟨p, rfl⟩
    have hz := (h ⟨normalZero S j p, hzero p⟩).property
    rw [hadd] at hz
    simpa [normalAddition, normalZero] using hz
  refine ⟨hzero, hstar, hadd, himage, hfwd, hinv,
    tubeRetraction S j V W h, tubeDeformation S j V W h hstar, hr,
    (fun _ => rfl), tubeRetraction_eq_self S j V W h hzero hadd, ?_,
    tubeDeformation_formula S j V W h hstar hadd,
    tubeDeformation_zero S j V W h hstar,
    tubeDeformation_one S j V W h hstar hadd,
    tubeDeformation_fixed S j V W h hzero hstar hadd⟩
  have hformula : (fun z : Icc (0 : ℝ) 1 × W =>
      (tubeDeformation S j V W h hstar z).val) =
      (fun z => j (tubeRetraction S j V W h z.2) +
        (1 - z.1.val) • (z.2.val - j (tubeRetraction S j V W h z.2))) := by
    funext z
    have hy : z.2.val = normalAddition S j (h.symm z.2).val := by
      simpa using hadd (h.symm z.2)
    rw [tubeDeformation_formula S j V W h hstar hadd, hy]
    simp [normalAddition, normalScale, tubeRetraction]
  rw [hformula]
  exact hH

/-- Restricting the codomain to an open set preserves the same coordinate
expressions. The statement includes an empty codomain. -/
theorem smooth_to_openSubset {k l : ℕ} {a b : ModelKind}
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (r : ℕ∞) (A : Set (ModelChart k a X)) (B : Set (ModelChart l b Y))
    (D : Set Y) (hD : IsOpen D) (f : X → D)
    (hf : ManifoldContDiff r A B (fun x => (f x).val)) :
    ManifoldContDiff r A (openSubsetAtlas B D hD) f := by
  intro x
  refine ⟨(hf x).1.codRestrict _, ?_⟩
  rintro e he _ ⟨hne, d, hd, rfl⟩ hx hfx
  exact (hf x).2 e he d hd hx
    (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hfx)

/-- Addition is smooth on the actual normal total space once its bundle
structure is constructed. The two summands use the specified projection and
ambient vector inclusion. -/
theorem smooth_normalAddition
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothMap S T j) (hN : IsNormalBundleStructure S j N) :
    IsSmoothMap N T (normalAddition S j) := by
  have hjproj := manifoldContDiff_comp (⊤ : ℕ∞) _ _ _
    S.smoothStructure.property.1.1 (fun z : NormalTotal S j => z.val.1) j hN.1 hj
  intro z
  obtain ⟨e, he, hz⟩ := N.smoothStructure.property.1.1 z
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    N.smoothStructure.property.1 T.smoothStructure.property.1 _ z).mpr
  refine ⟨(continuous_normalAddition S j
    (continuous_iff_continuousAt.mpr (fun p => (hj p).1))).continuousAt,
    e, he, euclideanChart q, hT, hz, mem_univ _, ?_⟩
  obtain ⟨U, hU, hzU, F, hF, heF⟩ :=
    (hjproj z).2 e he (euclideanChart q) hT hz (mem_univ _)
  obtain ⟨D, hD, hzD, G, hG, heG⟩ := (hN.2.2.1 z).2 e he hz
  refine ⟨U ∩ D, hU.inter hD, ⟨hzU, hzD⟩, (fun x => F x + G x),
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), ?_⟩
  filter_upwards [heF, heG] with y hyF hyG
  exact congrArg₂ (· + ·) hyF hyG

/-- The local geometric inverse is the remaining geometric input. Shrinking,
radial invariance, the global open diffeomorphism and the full smooth strong
deformation retraction are consequences of these actual local inverses. -/
theorem euclidean_tubular_of_normal_local_inverses
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (hN : IsNormalBundleStructure S j N)
    (hloc : ∀ p : M, ∃ e : OpenPartialHomeomorph (NormalTotal S j) (Euclidean q),
      normalZero S j p ∈ e.source ∧ EqOn e (normalAddition S j) e.source ∧
      ManifoldSmoothOn T.smoothStructure.val N.smoothStructure.val e.symm e.target) :
    ∃ (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
      (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
      IsTubularNeighborhood S T j N V W hV hW h := by
  classical
  obtain ⟨jhome, hjhome⟩ := hj.2.2.2
  have hjembed : Topology.IsEmbedding j := by
    have hjeq : (fun x => (jhome x).val) = j := funext hjhome
    rw [← hjeq]
    exact Topology.IsEmbedding.subtypeVal.comp jhome.isEmbedding
  choose e he0 headd hesmooth using hloc
  let U : Set (NormalTotal S j) := ⋃ p : M, (e p).source
  have hU : IsOpen U := isOpen_iUnion (fun p => (e p).open_source)
  obtain ⟨V₀, hV₀, hzero₀, hinj₀, _⟩ := normal_global_injective S j T hjembed
    (fun p => ⟨(e p).source, (e p).open_source, he0 p, fun z hz w hw hzw =>
      (e p).injOn hz hw ((headd p hz).trans (hzw.trans (headd p hw).symm))⟩)
  let V := radialCore S j (V₀ ∩ U)
  have hV : IsOpen V := isOpen_radialCore S j (hV₀.inter hU)
  have hVU : V ⊆ U := (radialCore_subset S j _).trans inter_subset_right
  have hVV₀ : V ⊆ V₀ := (radialCore_subset S j _).trans inter_subset_left
  have hzero : ∀ p, normalZero S j p ∈ V := fun p =>
    normalZero_mem_radialCore S j p ⟨hzero₀ p, mem_iUnion.mpr ⟨p, he0 p⟩⟩
  have hstar : ∀ z ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, normalScale S j t z ∈ V :=
    fun z hz t ht => radialCore_star S j z hz t ht
  have hinj : InjOn (normalAddition S j) V := hinj₀.mono hVV₀
  have himage : ∀ O : Set (NormalTotal S j), IsOpen O → O ⊆ U →
      IsOpen (normalAddition S j '' O) := by
    intro O hO hOU
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hOU hz)
    have hlocal := (e p).isOpen_image_of_subset_source
      (hO.inter (e p).open_source) (s := O ∩ (e p).source) inter_subset_right
    have hmem : normalAddition S j z ∈ e p '' (O ∩ (e p).source) :=
      ⟨z, ⟨hz, hp⟩, headd p hp⟩
    apply mem_of_superset (hlocal.mem_nhds hmem)
    rintro w ⟨v, hv, rfl⟩
    exact ⟨v, hv.1, (headd p hv.2).symm⟩
  let W := normalAddition S j '' V
  have hW : IsOpen W := himage V hV hVU
  let f : V → W := fun z => ⟨normalAddition S j z.val, mem_image_of_mem _ z.property⟩
  have hfcont : Continuous f :=
    ((continuous_normalAddition S j hjembed.continuous).comp continuous_subtype_val).subtype_mk _
  have hfb : Function.Bijective f := by
    constructor
    · intro z w heq
      apply Subtype.ext
      exact hinj z.property w.property (congrArg Subtype.val heq)
    · rintro ⟨y, z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have hfopen : IsOpenMap f := by
    apply hW.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    intro D hD
    have hDopen := hV.isOpenMap_subtype_val D hD
    have hDU : Subtype.val '' D ⊆ U := by
      rintro z ⟨w, _, rfl⟩
      exact hVU w.property
    change IsOpen ((fun z : V => normalAddition S j z.val) '' D)
    simpa only [image_image] using himage (Subtype.val '' D) hDopen hDU
  let h := (Equiv.ofBijective f hfb).toHomeomorphOfContinuousOpen hfcont hfopen
  have hadd : ∀ z : V, (h z).val = normalAddition S j z.val := fun _ => rfl
  have hfwd0 := (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _
    (normalAddition S j) V hV).mp
    (fun z _ => smooth_normalAddition S j T N hT hj.1 hN z)
  have hfwd : ManifoldSmooth (openSubsetAtlas N.smoothStructure.val V hV)
      (openSubsetAtlas T.smoothStructure.val W hW) h :=
    smooth_to_openSubset (⊤ : ℕ∞) _ _ W hW h hfwd0
  have hinclusion : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      T.smoothStructure.val (Subtype.val : W → Euclidean q) :=
    (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ id W hW).mp
      (fun y _ => manifoldContDiff_id (⊤ : ℕ∞) _ T.smoothStructure.property.1 y)
  have hinv0 : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      N.smoothStructure.val (fun y : W => (h.symm y).val) := by
    intro y
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hVU (h.symm y).property)
    have hy : y.val ∈ (e p).target := by
      rw [← h.apply_symm_apply y, hadd, ← headd p hp]
      exact (e p).map_source hp
    have hlocal := manifoldContDiffAt_comp T.smoothStructure.property.1.1
      (hinclusion y) (hesmooth p y.val hy)
    apply manifoldContDiffAt_congr hlocal
    have hcont : Continuous (fun y : W => (h.symm y).val) :=
      continuous_subtype_val.comp h.symm.continuous
    filter_upwards [hcont.continuousAt.preimage_mem_nhds ((e p).open_source.mem_nhds hp)]
      with w hw
    have hwimage : e p (h.symm w).val = w.val :=
      (headd p hw).trans (by simpa using (hadd (h.symm w)).symm)
    change (e p).symm w.val = (h.symm w).val
    rw [← hwimage, (e p).left_inv hw]
  have hinv : ManifoldSmooth (openSubsetAtlas T.smoothStructure.val W hW)
      (openSubsetAtlas N.smoothStructure.val V hV) h.symm :=
    smooth_to_openSubset (⊤ : ℕ∞) _ _ V hV h.symm hinv0
  exact ⟨V, W, hV, hW, h,
    isTubularNeighborhood_of_diffeomorphism S j T N V W hV hW h
      hT hj.1 hN hzero hstar hadd hfwd hinv⟩

end SmoothAssembly

section NormalAdditionDerivative
open Filter
open scoped Topology

/-- Coordinate form of IFT on boundaryless manifolds.  The bijectivity input is
an actual chart derivative, not an assumed differential. -/
theorem local_inverse_of_bijective_chartDerivative
    {m n : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (S : SmoothManifold m .euclidean X)
    (T : SmoothManifold n .euclidean Y) (f : X → Y)
    (hf : IsSmoothMap S T f) (p : X)
    (e : ModelChart m .euclidean X) (d : ModelChart n .euclidean Y)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hp : p ∈ e.source) (hfp : f p ∈ d.source)
    (hbij : Function.Bijective (chartDerivative e d f p)) :
    ∃ h : OpenPartialHomeomorph X Y,
      p ∈ h.source ∧ EqOn h f h.source ∧
      ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val h.symm h.target := by
  have hf1 : ManifoldContDiff 1 S.smoothStructure.val T.smoothStructure.val f :=
    manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ f (by simp) hf
  obtain ⟨F, G, L, hL⟩ := MapClasses.exists_differential_model S T f hf1 p
  letI := F.group
  letI := F.module
  letI := G.group
  letI := G.module
  have hi := MapClasses.differential_chart_invariants S T f p F G e d he hd hp hfp L hL
  have hbijL : Function.Bijective L := ⟨hi.2.1.mpr hbij.1, hi.2.2.mpr hbij.2⟩
  have hpi : p ∈ manifoldInterior S := ⟨e, he, hp, by simp [ModelData.modelSet]⟩
  have hfpi : f p ∈ manifoldInterior T := ⟨d, hd, hfp, by simp [ModelData.modelSet]⟩
  obtain ⟨h, hph, _, _, heq, _, hinv⟩ :=
    InteriorInverse.interior_inverse (⊤ : ℕ∞) (by simp) S T f hf p hpi hfpi F G L hL hbijL
  exact ⟨h, hph, heq, hinv⟩

open EuclideanTubularData MapClassData EmbeddedData

/-- The remaining local geometry can be supplied as derivatives in normal
bundle charts; all shrinking and deformation requirements then follow. -/
theorem euclidean_tubular_of_normal_chart_derivatives
    {n q : ℕ} {M : Type} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (j : M → Euclidean q)
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (hN : IsNormalBundleStructure S j N)
    (hderiv : ∀ p : M, ∃ e : ModelChart q .euclidean (NormalTotal S j),
      e ∈ N.smoothStructure.val ∧ normalZero S j p ∈ e.source ∧
      ∃ L : Euclidean q →L[ℝ] Euclidean q,
        HasCoordinateDerivative e (normalAddition S j) (normalZero S j p) L ∧
        Function.Bijective L) :
    ∃ (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
      (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
      IsTubularNeighborhood S T j N V W hV hW h := by
  apply euclidean_tubular_of_normal_local_inverses S j T N hT hj hN
  intro p
  obtain ⟨e, he, hp, L, hL, hbij⟩ := hderiv p
  have hder : chartDerivative e (euclideanChart q) (normalAddition S j)
      (normalZero S j p) = L :=
    FiniteRegularity.coordinateDerivative_eq e _ _ hp L hL
  apply local_inverse_of_bijective_chartDerivative N T (normalAddition S j)
    (smooth_normalAddition S j T N hT hj.1 hN) (normalZero S j p)
    e (euclideanChart q) he hT hp (mem_univ _)
  rwa [hder]


/-- The sum of an injective tangent parametrization and a normal basis is an
isomorphism onto the ambient Euclidean space. -/
theorem normal_sum_bijective {n k q : ℕ}
    (E : Submodule ℝ (Euclidean q))
    (D : Euclidean n →L[ℝ] Euclidean q)
    (hinj : Function.Injective D) (hrange : LinearMap.range D.toLinearMap = E)
    (b : Euclidean k ≃ₗ[ℝ] dotOrthogonal E)
    (B : Euclidean k →L[ℝ] Euclidean q)
    (hB : ∀ u, B u = (b u).val) :
    Function.Bijective (D.coprod B) := by
  let d : Euclidean n ≃ₗ[ℝ] E :=
    (LinearEquiv.ofInjective D.toLinearMap hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let a : (E × dotOrthogonal E) ≃ₗ[ℝ] Euclidean q :=
    E.prodEquivOfIsCompl (dotOrthogonal E) (isCompl_dotOrthogonal E)
  let c : (Euclidean n × Euclidean k) ≃ₗ[ℝ] Euclidean q :=
    (d.prodCongr b).trans a
  have heq : (D.coprod B : (Euclidean n × Euclidean k) → Euclidean q) = c := by
    funext z
    change D z.1 + B z.2 = (d z.1).val + (b z.2).val
    rw [hB]
    rfl
  rw [heq]
  exact c.bijective


theorem normalAddition_has_bijective_derivative
    (T : SmoothManifold q .euclidean (Euclidean q))
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (hN : IsNormalBundleStructure S j N)
    (p : M) :
    ∃ h : ModelChart q .euclidean (NormalTotal S j),
      h ∈ N.smoothStructure.val ∧ normalZero S j p ∈ h.source ∧
      ∃ L : Euclidean q →L[ℝ] Euclidean q,
        HasCoordinateDerivative h (normalAddition S j) (normalZero S j p) L ∧
        Function.Bijective L := by
  obtain ⟨e, he, hp, C, b, h, hh, hsrc, htgt, hcoord, hb⟩ := hN.2.2.2 p
  have hz : normalZero S j p ∈ h.source := by simpa [hsrc, normalZero] using hp
  have hzero_coords (x : M) (hx : x ∈ e.source) :
      (h (normalZero S j x)).val = C ((e x).val, 0) := by
    have hzx : normalZero S j x ∈ h.source := by simpa [hsrc, normalZero] using hx
    have hc := hcoord _ hzx
    change (h (normalZero S j x)).val = C ((e x).val, (b x).symm 0) at hc
    simpa only [map_zero] using hc
  obtain ⟨U, hU, hzU, F, hF, heF⟩ :=
    (smooth_normalAddition S j T N hT hj.1 hN (normalZero S j p)).2
      h hh (euclideanChart q) hT hz (mem_univ _)
  let L := fderiv ℝ F (h (normalZero S j p)).val
  have hFd : HasFDerivAt F L (h (normalZero S j p)).val :=
    ((hF.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by simp)).hasFDerivAt
  have hL : HasCoordinateDerivative h (normalAddition S j) (normalZero S j p) L :=
    ⟨F, hFd, heF⟩
  rw [hzero_coords p hp] at hFd
  let Ch := (C : (Euclidean n × Euclidean (q-n)) →L[ℝ] Euclidean q).comp
    (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean (q-n)))
  have hFh : HasCoordinateDerivative e j p (L.comp Ch) := by
    refine ⟨fun x => F (Ch x), ?_, ?_⟩
    · have hd : HasFDerivAt F L (Ch (e p).val) := hFd
      exact hd.comp (e p).val Ch.hasFDerivAt
    · filter_upwards [heF.comp_tendsto (continuous_normalZero S j).continuousAt,
        e.open_source.mem_nhds hp] with x hxF hx
      change F (h (normalZero S j x)).val = j x + 0 at hxF
      rw [hzero_coords x hx] at hxF
      simpa [Ch] using hxF
  let D := chartDerivative e (euclideanChart q) j p
  have hDh : D = L.comp Ch :=
    FiniteRegularity.coordinateDerivative_eq e j p hp _ hFh
  let B := ((normalFiber S j p).subtype.comp (b p).toLinearMap).toContinuousLinearMap
  let vmap : Euclidean (q-n) → NormalTotal S j :=
    fun u => ⟨(p, (b p u).val), (b p u).property⟩
  have hvcont : Continuous vmap :=
    (continuous_const.prodMk B.continuous).subtype_mk _
  have hvzero : vmap 0 = normalZero S j p := by
    apply Subtype.ext
    simp [vmap, normalZero]
  have hvert : (fun u => F (C ((e p).val, u))) =ᶠ[𝓝 (0 : Euclidean (q-n))]
      (fun u => j p + B u) := by
    have hvt : Tendsto vmap (𝓝 0) (𝓝 (vmap 0)) := hvcont.continuousAt
    rw [hvzero] at hvt
    have ht := heF.comp_tendsto hvt
    filter_upwards [ht] with u hu
    have hvsrc : vmap u ∈ h.source := by simpa [hsrc, vmap] using hp
    change F (h (vmap u)).val = normalAddition S j (vmap u) at hu
    rw [hcoord _ hvsrc] at hu
    simpa [vmap, B, normalAddition] using hu
  let Cv := (C : (Euclidean n × Euclidean (q-n)) →L[ℝ] Euclidean q).comp
    (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean (q-n)))
  have hCv : HasFDerivAt (fun u : Euclidean (q-n) => C ((e p).val, u)) Cv 0 := by
    convert C.hasFDerivAt.comp (0 : Euclidean (q-n))
      ((hasFDerivAt_const (e p).val (0 : Euclidean (q-n))).prodMk (hasFDerivAt_id 0)) using 1 <;>
      ext u i <;> simp [Cv]
  have hFv : HasFDerivAt (fun u : Euclidean (q-n) => F (C ((e p).val, u)))
      (L.comp Cv) 0 := by
    apply hFd.comp 0 hCv
  have hDv : L.comp Cv = B :=
    (hFv.congr_of_eventuallyEq hvert.symm).unique (B.hasFDerivAt.const_add (j p))
  have hcomp : L.comp (C : (Euclidean n × Euclidean (q-n)) →L[ℝ] Euclidean q) =
      D.coprod B := by
    apply ContinuousLinearMap.ext
    intro z
    have heq : C z = Ch z.1 + Cv z.2 := by
      change C z = C (z.1, 0) + C (0, z.2)
      rw [← map_add]
      simp only [Prod.mk_add_mk, add_zero, zero_add, Prod.eta]
    change L (C z) = D z.1 + B z.2
    rw [heq, map_add]
    rw [hDh]
    change (L (Ch z.1) + (L.comp Cv) z.2) = _
    rw [hDv]
    rfl
  refine ⟨h, hh, hz, L, hL, ?_⟩
  have hinjD : Function.Injective D := by
    have hj1 := manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ j (by simp) hj.1
    exact (MapClasses.chart_invariants S T j hj1 p e (euclideanChart q)
      he hT hp (mem_univ _)).2.1.mp (hj.2.2.1 p)
  have hsum := normal_sum_bijective (ambientTangent S j p) D hinjD
    (ambientTangent_eq_chart S j T hT hj.1 p e he hp).symm (b p) B (fun _ => rfl)
  have hbijLC : Function.Bijective (L.comp (C : (Euclidean n × Euclidean (q-n)) →L[ℝ] Euclidean q)) := by rwa [hcomp]
  constructor
  · intro x y hxy
    have heq : C.symm x = C.symm y := hbijLC.1 (by simpa using hxy)
    exact C.symm.injective heq
  · intro y
    obtain ⟨x, hx⟩ := hbijLC.2 y
    exact ⟨C x, hx⟩

/-- Construction of the smooth normal vector bundle is sufficient: the local
inverse, global shrinking, radial invariance and smooth deformation then
follow from the proved derivative calculation. -/
theorem euclidean_tubular_of_normal_bundle
    (T : SmoothManifold q .euclidean (Euclidean q))
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) (hN : IsNormalBundleStructure S j N) :
    ∃ (V : Set (NormalTotal S j)) (W : Set (Euclidean q))
      (hV : IsOpen V) (hW : IsOpen W) (h : V ≃ₜ W),
      IsTubularNeighborhood S T j N V W hV hW h :=
  euclidean_tubular_of_normal_chart_derivatives S T j N hT hj hN
    (normalAddition_has_bijective_derivative S j T N hT hj hN)

end NormalAdditionDerivative

noncomputable section
namespace NormalFrames
abbrev E (n : ℕ) := Fin n → ℝ

def transposeLinear (n q : ℕ) : (E n →L[ℝ] E q) →ₗ[ℝ] (E q →L[ℝ] E n) where
  toFun A := LinearMap.toContinuousLinearMap <|
    (dotProductEquiv ℝ (Fin n)).symm.toLinearMap.comp
      (A.toLinearMap.dualMap.comp (dotProductEquiv ℝ (Fin q)).toLinearMap)
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro v
    change (dotProductEquiv ℝ (Fin n)).symm ((A + B).toLinearMap.dualMap _) =
      (dotProductEquiv ℝ (Fin n)).symm (A.toLinearMap.dualMap _) +
      (dotProductEquiv ℝ (Fin n)).symm (B.toLinearMap.dualMap _)
    rw [← map_add]
    congr 1
    ext w
    simp
  map_smul' t A := by
    apply ContinuousLinearMap.ext
    intro v
    change (dotProductEquiv ℝ (Fin n)).symm ((t • A).toLinearMap.dualMap _) =
      t • (dotProductEquiv ℝ (Fin n)).symm (A.toLinearMap.dualMap _)
    rw [← map_smul]
    congr 1
    ext w
    simp

def transpose (n q : ℕ) : (E n →L[ℝ] E q) →L[ℝ] (E q →L[ℝ] E n) :=
  (transposeLinear n q).toContinuousLinearMap

@[simp] theorem dot_transpose (n q : ℕ) (A : E n →L[ℝ] E q)
    (v : E q) (w : E n) : dotProduct (transpose n q A v) w = dotProduct v (A w) := by
  change (dotProductEquiv ℝ (Fin n)) ((dotProductEquiv ℝ (Fin n)).symm _) w = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem contDiff_transpose (n q : ℕ) (r : ℕ∞) : ContDiff ℝ r (transpose n q) :=
  (transpose n q).contDiff

theorem contDiffWithinAt_transpose {d n q : ℕ} {r : ℕ∞}
    {f : E d → E n →L[ℝ] E q} {s : Set (E d)} {x : E d}
    (hf : ContDiffWithinAt ℝ r f s x) :
    ContDiffWithinAt ℝ r (fun x => transpose n q (f x)) s x :=
  (transpose n q).contDiff.contDiffAt.comp_contDiffWithinAt x hf

def frameNormal (n k q : ℕ) (A : (E n × E k) →L[ℝ] E q) : E k →L[ℝ] E q :=
  transpose q k ((ContinuousLinearMap.snd ℝ (E n) (E k)).comp A.inverse)

@[simp] theorem frameNormal_dot {n k q : ℕ}
    (A : (E n × E k) →L[ℝ] E q) (u : E k) (v : E q) :
    dotProduct (frameNormal n k q A u) v = dotProduct u (A.inverse v).2 := by
  exact dot_transpose q k _ u v

@[simp] theorem frameNormal_equiv_dot {n k q : ℕ}
    (A : (E n × E k) ≃L[ℝ] E q) (u : E k) (v : E q) :
    dotProduct (frameNormal n k q A u) v = dotProduct u (A.symm v).2 := by
  rw [frameNormal_dot, ContinuousLinearMap.inverse_equiv]
  rfl

theorem contDiffOn_frameNormal {d n k q : ℕ} {r : ℕ∞}
    {A : E d → (E n × E k) →L[ℝ] E q} {U : Set (E d)}
    (hA : ContDiffOn ℝ r A U) (hinv : ∀ x ∈ U, (A x).IsInvertible) :
    ContDiffOn ℝ r (fun x => frameNormal n k q (A x)) U := by
  intro x hx
  apply (transpose q k).contDiff.contDiffAt.comp_contDiffWithinAt x
  exact contDiffWithinAt_const.clm_comp
    ((hinv x hx).contDiffAt_map_inverse.comp_contDiffWithinAt x (hA x hx))

theorem isOpen_invertible_locus {d n k q : ℕ}
    {A : E d → (E n × E k) →L[ℝ] E q} {U : Set (E d)}
    (hU : IsOpen U) (hA : ContinuousOn A U) :
    IsOpen {x ∈ U | (A x).IsInvertible} :=
  hA.isOpen_inter_preimage hU ContinuousLinearMap.isOpen_setOfPred_isInvertible

def frameCoordinates (n k q : ℕ) (A : (E n × E k) →L[ℝ] E q) : E q →L[ℝ] E k :=
  transpose k q (A.comp (ContinuousLinearMap.inr ℝ (E n) (E k)))

@[simp] theorem frameCoordinates_dot {n k q : ℕ}
    (A : (E n × E k) →L[ℝ] E q) (v : E q) (u : E k) :
    dotProduct (frameCoordinates n k q A v) u = dotProduct v (A (0, u)) := by
  exact dot_transpose k q _ v u

@[simp] theorem frameCoordinates_frameNormal {n k q : ℕ}
    (A : (E n × E k) →L[ℝ] E q) (hA : A.IsInvertible) (u : E k) :
    frameCoordinates n k q A (frameNormal n k q A u) = u := by
  apply dotProduct_eq
  intro v
  rw [frameCoordinates_dot, frameNormal_dot, hA.inverse_apply_self]

theorem contDiffOn_frameCoordinates {d n k q : ℕ} {r : ℕ∞}
    {A : E d → (E n × E k) →L[ℝ] E q} {U : Set (E d)}
    (hA : ContDiffOn ℝ r A U) :
    ContDiffOn ℝ r (fun x => frameCoordinates n k q (A x)) U := by
  intro x hx
  exact (transpose k q).contDiff.contDiffAt.comp_contDiffWithinAt x
    ((hA x hx).clm_comp contDiffWithinAt_const)

theorem contDiffOn_apply_family {d k q : ℕ} {r : ℕ∞}
    {B : E d → E k →L[ℝ] E q} {U : Set (E d)}
    (hB : ContDiffOn ℝ r B U) :
    ContDiffOn ℝ r (fun z : E d × E k => B z.1 z.2) (U ×ˢ Set.univ) := by
  exact (hB.comp contDiff_fst.contDiffOn (fun z hz => hz.1)).clm_apply
    contDiff_snd.contDiffOn

theorem contDiffOn_coprod_family {d n k q : ℕ} {r : ℕ∞}
    {D : E d → E n →L[ℝ] E q} {B : E d → E k →L[ℝ] E q}
    {U : Set (E d)} (hD : ContDiffOn ℝ r D U) (hB : ContDiffOn ℝ r B U) :
    ContDiffOn ℝ r (fun x => (D x).coprod (B x)) U := by
  change ContDiffOn ℝ r
    (fun x => (D x).comp (ContinuousLinearMap.fst ℝ (E n) (E k)) +
      (B x).comp (ContinuousLinearMap.snd ℝ (E n) (E k))) U
  exact (hD.clm_comp contDiffOn_const).add (hB.clm_comp contDiffOn_const)

theorem hasFDerivAt_varying_linear_zero {d k q : ℕ}
    {B : E d → E k →L[ℝ] E q} {x : E d}
    (hB : DifferentiableAt ℝ B x) :
    HasFDerivAt (fun z : E d × E k => B z.1 z.2)
      ((B x).comp (ContinuousLinearMap.snd ℝ (E d) (E k))) (x, 0) := by
  have hB' : HasFDerivAt (fun z : E d × E k => B z.1)
      ((fderiv ℝ B x).comp (ContinuousLinearMap.fst ℝ (E d) (E k)))
      (x, (0 : E k)) := hB.hasFDerivAt.comp _ (hasFDerivAt_fst (𝕜 := ℝ))
  simpa using hB'.clm_apply
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, (0 : E k))))

theorem exists_complement_frame {n q : ℕ} (D : E n →L[ℝ] E q)
    (hD : Function.Injective D) :
    ∃ A : (E n × E (q - n)) ≃L[ℝ] E q, ∀ w, A (w, 0) = D w := by
  let R := LinearMap.range D.toLinearMap
  let Q := SmoothManifolds.EuclideanTubularData.dotOrthogonal R
  have hR : Module.finrank ℝ R = n :=
    (LinearMap.finrank_range_of_inj hD).trans (by simp [E])
  have hQ : Module.finrank ℝ Q = q - n := by
    have h := SmoothManifolds.EuclideanTubular.finrank_add_finrank_dotOrthogonal R
    rw [hR] at h
    change n + Module.finrank ℝ Q = q at h
    omega
  let eD : E n ≃ₗ[ℝ] R := LinearEquiv.ofInjective D.toLinearMap hD
  let eQ : E (q - n) ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq _ _ (by simp [E, hQ])
  let A : (E n × E (q - n)) ≃L[ℝ] E q :=
    ((eD.prodCongr eQ).trans
      (R.prodEquivOfIsCompl Q (SmoothManifolds.EuclideanTubular.isCompl_dotOrthogonal R))).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  intro w
  change (eD w).val + (eQ 0).val = D w
  rw [map_zero, Submodule.coe_zero, add_zero]
  rfl

theorem frameNormal_frameCoordinates {n k q : ℕ}
    (A : (E n × E k) →L[ℝ] E q) (hA : A.IsInvertible)
    (D : E n →L[ℝ] E q) (hD : ∀ w, A (w, 0) = D w)
    (v : E q) (hv : v ∈ SmoothManifolds.EuclideanTubularData.dotOrthogonal
      (LinearMap.range D.toLinearMap)) :
    frameNormal n k q A (frameCoordinates n k q A v) = v := by
  apply dotProduct_eq
  intro w
  rw [frameNormal_dot, frameCoordinates_dot]
  have hzero : dotProduct v (A ((A.inverse w).1, 0)) = 0 := by
    rw [hD]
    exact hv _ ⟨_, rfl⟩
  have hw : A ((A.inverse w).1, 0) + A (0, (A.inverse w).2) = w := by
    rw [← map_add]
    simpa using hA.self_apply_inverse w
  have h := congrArg (dotProduct v) hw
  simpa [dotProduct_add, hzero] using h

theorem frameNormal_range {n k q : ℕ}
    (A : (E n × E k) →L[ℝ] E q) (hA : A.IsInvertible)
    (D : E n →L[ℝ] E q) (hD : ∀ w, A (w, 0) = D w) :
    LinearMap.range (frameNormal n k q A).toLinearMap =
      SmoothManifolds.EuclideanTubularData.dotOrthogonal (LinearMap.range D.toLinearMap) := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩ w ⟨t, rfl⟩
    change dotProduct (frameNormal n k q A u) (D t) = 0
    rw [← hD, frameNormal_dot, hA.inverse_apply_self]
    simp
  · intro v hv
    exact ⟨frameCoordinates n k q A v, frameNormal_frameCoordinates A hA D hD v hv⟩

theorem exists_local_normal_frames {n q : ℕ} {U : Set (E n)}
    (hU : IsOpen U) (D : E n → E n →L[ℝ] E q)
    (hD : ContDiffOn ℝ (⊤ : ℕ∞) D U) (x0 : E n) (hx0 : x0 ∈ U)
    (hinj : Function.Injective (D x0)) :
    ∃ V : Set (E n), IsOpen V ∧ V ⊆ U ∧ x0 ∈ V ∧
      ∃ (B : E n → E (q - n) →L[ℝ] E q) (K : E n → E q →L[ℝ] E (q - n)),
        ContDiffOn ℝ (⊤ : ℕ∞) B V ∧ ContDiffOn ℝ (⊤ : ℕ∞) K V ∧
        ∀ x ∈ V,
          LinearMap.range (B x).toLinearMap =
            SmoothManifolds.EuclideanTubularData.dotOrthogonal
              (LinearMap.range (D x).toLinearMap) ∧
          (∀ u, K x (B x u) = u) ∧
          ∀ v, v ∈ SmoothManifolds.EuclideanTubularData.dotOrthogonal
            (LinearMap.range (D x).toLinearMap) → B x (K x v) = v := by
  obtain ⟨A0, hA0⟩ := exists_complement_frame (D x0) hinj
  let B0 : E (q - n) →L[ℝ] E q :=
    A0.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (E n) (E (q - n)))
  let A : E n → (E n × E (q - n)) →L[ℝ] E q := fun x => (D x).coprod B0
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A U :=
    contDiffOn_coprod_family hD contDiffOn_const
  have heq : A x0 = A0.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    rintro ⟨w, u⟩
    change D x0 w + A0 (0, u) = A0 (w, u)
    rw [← hA0, ← map_add]
    simp
  have hinv0 : (A x0).IsInvertible := heq.symm ▸ ⟨A0, rfl⟩
  let V := {x ∈ U | (A x).IsInvertible}
  have hVU : V ⊆ U := fun _ hx => hx.1
  refine ⟨V, isOpen_invertible_locus hU hA.continuousOn, hVU, ⟨hx0, hinv0⟩,
    (fun x => frameNormal n (q - n) q (A x)),
    (fun x => frameCoordinates n (q - n) q (A x)),
    contDiffOn_frameNormal (hA.mono hVU) (fun x hx => hx.2),
    contDiffOn_frameCoordinates (hA.mono hVU), ?_⟩
  intro x hx
  have hAD : ∀ w, A x (w, 0) = D x w := by
    intro w
    change D x w + B0 0 = D x w
    simp
  exact ⟨frameNormal_range (A x) hx.2 (D x) hAD,
    frameCoordinates_frameNormal (A x) hx.2,
    frameNormal_frameCoordinates (A x) hx.2 (D x) hAD⟩

end NormalFrames
end

section LocalNormalFrames
open Filter
open scoped Topology

namespace NormalFrames


variable {n q : ℕ} {a : SmoothManifolds.ModelKind} {M : Type} [TopologicalSpace M]

theorem coordinateDerivative_local_extension
    (e : ModelChart n a M) (j : M → Euclidean q) (p : M) (hp : p ∈ e.source)
    (h : LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (e y).val) j p) :
    ∃ (U : Set (Euclidean n)) (F : Euclidean n → Euclidean q) (V : Set M),
      IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ e.source ∧
      MapsTo (fun y => (e y).val) V U ∧
      EqOn (fun y => F (e y).val) j V ∧
      EqOn (coordinateDerivative e j) (fun y => fderiv ℝ F (e y).val) V := by
  obtain ⟨U, hU, hpU, F, hF, heq⟩ := h
  have hc : ContinuousAt (fun y => (e y).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousOn.continuousAt (e.open_source.mem_nhds hp))
  have hdom : {y | y ∈ e.source ∧ (e y).val ∈ U ∧ F (e y).val = j y} ∈ 𝓝 p := by
    filter_upwards [e.open_source.mem_nhds hp, hc.preimage_mem_nhds (hU.mem_nhds hpU), heq]
      with y hy hye hyf
    exact ⟨hy, hye, hyf⟩
  obtain ⟨V, hVsub, hV, hpV⟩ := mem_nhds_iff.mp hdom
  refine ⟨U, F, V, hU, hF, hV, hpV, (fun y hy => (hVsub hy).1),
    (fun y hy => (hVsub hy).2.1), (fun y hy => (hVsub hy).2.2), ?_⟩
  intro y hy
  apply SmoothManifolds.FiniteRegularity.coordinateDerivative_eq e j y (hVsub hy).1
  refine ⟨F, ?_, ?_⟩
  · exact ((hF.contDiffAt (hU.mem_nhds (hVsub hy).2.1)).differentiableAt (by simp)).hasFDerivAt
  · filter_upwards [hV.mem_nhds hy] with z hz
    exact (hVsub hz).2.2



variable {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type} [TopologicalSpace M]

theorem contDiffCompatible_restr_left {r : ℕ∞} {e d : ModelChart n a M}
    (h : ContDiffCompatible r e d) (V : Set M) :
    ContDiffCompatible r (e.restr V) d := by
  constructor
  · apply SmoothManifolds.contDiffOnModel_mono h.1
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  · apply SmoothManifolds.contDiffOnModel_mono h.2
    intro y hy
    exact ⟨hy.1, hy.2.1⟩

theorem restr_mem_maximalAtlas
    {A : Set (ModelChart n a M)} (hA : IsMaximalContDiffAtlas (⊤ : ℕ∞) A)
    {e : ModelChart n a M} (he : e ∈ A) (V : Set M) : e.restr V ∈ A := by
  have hext : e.restr V ∈ maximalExtension (⊤ : ℕ∞) A := by
    intro d hd
    exact contDiffCompatible_restr_left (hA.1.2 e he d hd) V
  have hEq := hA.2 (maximalExtension (⊤ : ℕ∞) A)
    (SmoothManifolds.maximalExtension_isContDiffAtlas hA.1)
    (SmoothManifolds.subset_maximalExtension hA.1)
  rwa [hEq] at hext

theorem contDiffCompatible_restrOpen_left {r : ℕ∞} {e d : ModelChart n a M}
    (h : ContDiffCompatible r e d) (V : Set M) (hV : IsOpen V) :
    ContDiffCompatible r (e.restrOpen V hV) d := by
  constructor
  · apply SmoothManifolds.contDiffOnModel_mono h.1
    intro y hy
    exact ⟨hy.1.1, hy.2⟩
  · apply SmoothManifolds.contDiffOnModel_mono h.2
    intro y hy
    exact ⟨hy.1, hy.2.1⟩

theorem restrOpen_mem_maximalAtlas
    {A : Set (ModelChart n a M)} (hA : IsMaximalContDiffAtlas (⊤ : ℕ∞) A)
    {e : ModelChart n a M} (he : e ∈ A) (V : Set M) (hV : IsOpen V) :
    e.restrOpen V hV ∈ A := by
  have hext : e.restrOpen V hV ∈ maximalExtension (⊤ : ℕ∞) A := by
    intro d hd
    exact contDiffCompatible_restrOpen_left (hA.1.2 e he d hd) V hV
  have hEq := hA.2 (maximalExtension (⊤ : ℕ∞) A)
    (SmoothManifolds.maximalExtension_isContDiffAtlas hA.1)
    (SmoothManifolds.subset_maximalExtension hA.1)
  rwa [hEq] at hext



variable {n k q : ℕ} {M : Type} [TopologicalSpace M]

theorem toEuclideanAt_of_oneChart
    {a : SmoothManifolds.ModelKind} {r : ℕ∞}
    (A : Set (ModelChart n a M)) (hA : IsContDiffAtlas r A)
    (e : ModelChart n a M) (he : e ∈ A)
    (f : M → Euclidean q) (x : M) (hx : x ∈ e.source)
    (hc : ContinuousAt f x)
    (h : LocalCoordinateExtension r (fun y => (e y).val) f x) :
    ManifoldContDiffToEuclideanAt r A f x := by
  refine ⟨hc, ?_⟩
  intro d hd hxd
  exact SmoothManifolds.LocalCoordinateExtension.comp h
    (SmoothManifolds.chartContDiffAt_of_compatible (hA.2 d hd e he) hxd hx)

noncomputable def localFiberEquiv
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (e : ModelChart n .euclidean M) (W : Set M)
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hBr : ∀ x ∈ W, LinearMap.range (B (e x).val).toLinearMap = normalFiber S j x)
    (hBi : ∀ x ∈ W, Function.Injective (B (e x).val)) (x : M) (hx : x ∈ W) :
    Euclidean k ≃ₗ[ℝ] normalFiber S j x :=
  (LinearEquiv.ofInjective (B (e x).val).toLinearMap (hBi x hx)).trans
    (LinearEquiv.ofEq _ _ (hBr x hx))

@[simp] theorem localFiberEquiv_apply
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (e : ModelChart n .euclidean M) (W : Set M)
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hBr : ∀ x ∈ W, LinearMap.range (B (e x).val).toLinearMap = normalFiber S j x)
    (hBi : ∀ x ∈ W, Function.Injective (B (e x).val)) (x : M) (hx : x ∈ W)
    (u : Euclidean k) : (localFiberEquiv S j e W B hBr hBi x hx u).val = B (e x).val u := rfl

theorem package_local_normal_frame
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (hdim : ∀ x, Module.finrank ℝ (normalFiber S j x) = k)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (W : Set M) (hW : IsOpen W) (hWe : W ⊆ e.source)
    (O : Set (Euclidean n)) (hO : IsOpen O)
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B O)
    (hWO : MapsTo (fun x => (e x).val) W O)
    (hBr : ∀ x ∈ W, LinearMap.range (B (e x).val).toLinearMap = normalFiber S j x)
    (hBi : ∀ x ∈ W, Function.Injective (B (e x).val)) :
    ∃ b : ∀ x, Euclidean k ≃ₗ[ℝ] normalFiber S j x,
      (∀ x ∈ W, ∀ u, (b x u).val = B (e x).val u) ∧
      ∀ (u : Euclidean k) (x : M), x ∈ W →
        ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
          (fun x => (b x u).val) x := by
  classical
  let b : ∀ x, Euclidean k ≃ₗ[ℝ] normalFiber S j x := fun x =>
    if hx : x ∈ W then localFiberEquiv S j e W B hBr hBi x hx
    else LinearEquiv.ofFinrankEq (Euclidean k) (normalFiber S j x)
      (by simpa [SmoothManifolds.ModelData.Euclidean] using (hdim x).symm)
  have heq : ∀ x ∈ W, ∀ u, (b x u).val = B (e x).val u := by
    intro x hx u
    simp [b, hx]
  refine ⟨b, heq, ?_⟩
  intro u x hx
  have hg : (fun y => B (e y).val u) =ᶠ[𝓝 x] (fun y => (b y u).val) := by
    filter_upwards [hW.mem_nhds hx] with y hy
    exact (heq y hy u).symm
  have hcoord : ContinuousAt (fun y => (e y).val) x :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt (hWe hx))
  have hBu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => B z u) O :=
    hB.clm_apply contDiffOn_const
  have hcg : ContinuousAt (fun y : M => B (e y).val u) x := by
    exact ContinuousAt.comp (f := fun y : M => (e y).val)
      (hBu.contDiffAt (hO.mem_nhds (hWO hx))).continuousAt hcoord
  have hc : ContinuousAt (fun y => (b y u).val) x := hcg.congr hg
  apply toEuclideanAt_of_oneChart S.smoothStructure.val S.smoothStructure.property.1
    e he _ x (hWe hx) hc
  exact ⟨O, hO, hWO hx, (fun z => B z u), hBu, hg⟩



open SmoothManifolds.EmbeddedData SmoothManifolds.MapClassData SmoothManifolds.FiniteRegularityData

variable {n q : ℕ} {M : Type} [TopologicalSpace M]

theorem exists_actual_local_normal_frames
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val) (hj : IsSmoothEmbedding S T j)
    (p : M) :
    ∃ (e : ModelChart n .euclidean M), e ∈ S.smoothStructure.val ∧ p ∈ e.source ∧
      ∃ (C : (Euclidean n × Euclidean (q-n)) ≃L[ℝ] Euclidean q)
        (b : ∀ x, Euclidean (q-n) ≃ₗ[ℝ] normalFiber S j x)
        (B : Euclidean n → Euclidean (q-n) →L[ℝ] Euclidean q)
        (K : Euclidean n → Euclidean q →L[ℝ] Euclidean (q-n)),
        ContDiffOn ℝ (⊤ : ℕ∞) B (Subtype.val '' e.target) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) K (Subtype.val '' e.target) ∧
        (∀ x ∈ e.source, ∀ u, (b x u).val = B (e x).val u) ∧
        (∀ x ∈ e.source, ∀ v : normalFiber S j x, (b x).symm v = K (e x).val v.val) ∧
        ∀ (u : Euclidean (q-n)) (x : M), x ∈ e.source →
          ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
            (fun x => (b x u).val) x := by
  classical
  let e0 := tangentChart S p
  have he0 : e0 ∈ S.smoothStructure.val := SmoothManifolds.EuclideanTubular.tangentChart_mem S p
  have hp0 : p ∈ e0.source := SmoothManifolds.EuclideanTubular.mem_tangentChart_source S p
  have hf : LocalCoordinateExtension (⊤ : ℕ∞) (fun y => (e0 y).val) j p :=
    (hj.1 p).2 e0 he0 (euclideanChart q) hT hp0 (mem_univ _)
  obtain ⟨U, F, V, hU, hF, hV, hpV, hVe, hVU, hFeq, hDeq⟩ :=
    coordinateDerivative_local_extension e0 j p hp0 hf
  have hj1 := SmoothManifolds.manifoldContDiff_of_le (⊤ : ℕ∞) 1 _ _ j (by simp) hj.1
  have hinj0 := (SmoothManifolds.MapClasses.chart_invariants S T j hj1 p e0
    (euclideanChart q) he0 hT hp0 (mem_univ _)).2.1.mp (hj.2.2.1 p)
  have hinj : Function.Injective (fderiv ℝ F (e0 p).val) := by
    have hDer : coordinateDerivative e0 j p = fderiv ℝ F (e0 p).val := hDeq hpV
    rw [← hDer]
    exact hinj0
  obtain ⟨O, hO, hOU, hpO, B, K, hB, hK, hBK⟩ :=
    exists_local_normal_frames hU (fderiv ℝ F)
      (hF.fderiv_of_isOpen hU (by simp)) (e0 p).val (hVU hpV) hinj
  let W : Set M := V ∩ {x | x ∈ e0.source ∧ (e0 x).val ∈ O}
  have hW : IsOpen W := hV.inter
    (e0.isOpen_inter_preimage (hO.preimage continuous_subtype_val))
  have hpW : p ∈ W := ⟨hpV, hp0, hpO⟩
  have hWe : W ⊆ e0.source := fun x hx => hx.2.1
  have hWO : MapsTo (fun x => (e0 x).val) W O := fun x hx => hx.2.2
  have hBr : ∀ x ∈ W, LinearMap.range (B (e0 x).val).toLinearMap = normalFiber S j x := by
    intro x hx
    change LinearMap.range (B (e0 x).val).toLinearMap = dotOrthogonal (ambientTangent S j x)
    rw [SmoothManifolds.EuclideanTubular.ambientTangent_eq_chart S j T hT hj.1 x e0 he0 (hWe hx)]
    change LinearMap.range (B (e0 x).val).toLinearMap =
      dotOrthogonal (LinearMap.range (coordinateDerivative e0 j x).toLinearMap)
    rw [hDeq hx.1]
    exact (hBK _ (hWO hx)).1
  have hBi : ∀ x ∈ W, Function.Injective (B (e0 x).val) := by
    intro x hx u v huv
    have hh := congrArg (K (e0 x).val) huv
    simpa only [(hBK _ (hWO hx)).2.1 u, (hBK _ (hWO hx)).2.1 v] using hh
  obtain ⟨b, hb, hbsmooth⟩ := package_local_normal_frame S j
    (SmoothManifolds.EuclideanTubular.normalFiber_finrank S j T hT hj)
    e0 he0 W hW hWe O hO B hB hWO hBr hBi
  let e := e0.restrOpen W hW
  have he : e ∈ S.smoothStructure.val := restrOpen_mem_maximalAtlas S.smoothStructure.property he0 W hW
  have heW : e.source = W := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨hWe hx, hx⟩⟩
  have htarget : Subtype.val '' e.target ⊆ O := by
    rintro y ⟨z, hz, rfl⟩
    have hzW : e.symm z ∈ W := by
      rw [← heW]
      exact e.map_target hz
    have hh := hWO hzW
    change (e (e.symm z)).val ∈ O at hh
    simpa only [e.right_inv hz] using hh
  obtain ⟨C, hC⟩ := exists_complement_frame (fderiv ℝ F (e0 p).val) hinj
  refine ⟨e, he, heW.symm ▸ hpW, C, b, B, K, hB.mono htarget, hK.mono htarget,
    ?_, ?_, ?_⟩
  · intro x hx u
    exact hb x (heW ▸ hx) u
  · intro x hx v
    have hh := (hBK _ (hWO (heW ▸ hx))).2.1 ((b x).symm v)
    rw [← hb x (heW ▸ hx), (b x).apply_symm_apply] at hh
    exact hh.symm
  · intro u x hx
    exact hbsmooth u x (heW ▸ hx)


end NormalFrames

end LocalNormalFrames

section NormalBundleCharts

open ModelData AtlasData MapData EuclideanTubularData Set
open scoped Topology

variable {n k q : ℕ} {M : Type} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
  (e : ModelChart n .euclidean M)
  (C : (Euclidean n × Euclidean k) ≃L[ℝ] Euclidean q)
  (b : ∀ p : M, Euclidean k ≃ₗ[ℝ] normalFiber S j p)

noncomputable def normalChartForward (z : NormalTotal S j) : ModelSpace q .euclidean :=
  ⟨C ((e z.val.1).val, (b z.val.1).symm ⟨z.val.2, z.property⟩), mem_univ _⟩

noncomputable def normalChartInverse (y : ModelSpace q .euclidean) : NormalTotal S j :=
  let p := e.symm ⟨(C.symm y.val).1, mem_univ _⟩
  ⟨(p, (b p (C.symm y.val).2).val), (b p (C.symm y.val).2).property⟩

/-- A continuous frame and continuous inverse frame give the full-fiber
bundle chart with precisely the ambient-coordinate target. -/
noncomputable def normalBundleChart
    (hB : ContinuousOn (fun z : M × Euclidean k => (b z.1 z.2).val)
      (e.source ×ˢ univ))
    (hK : ContinuousOn (fun z : NormalTotal S j =>
      (b z.val.1).symm ⟨z.val.2, z.property⟩)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' e.source)) :
    ModelChart q .euclidean (NormalTotal S j) where
  toFun := normalChartForward S j e C b
  invFun := normalChartInverse S j e C b
  source := (fun z => z.val.1) ⁻¹' e.source
  target := {y | (C.symm y.val).1 ∈ Subtype.val '' e.target}
  map_source' := by
    intro z hz
    change (C.symm (C ((e z.val.1).val, _))).1 ∈ Subtype.val '' e.target
    rw [C.symm_apply_apply]
    exact ⟨e z.val.1, e.map_source hz, rfl⟩
  map_target' := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    change e.symm ⟨(C.symm y.val).1, mem_univ _⟩ ∈ e.source
    have heq : (⟨(C.symm y.val).1, mem_univ _⟩ : ModelSpace n .euclidean) = x :=
      Subtype.ext hxy.symm
    rw [heq]
    exact e.map_target hx
  left_inv' := by
    intro z hz
    have hbase : e.symm ⟨(C.symm (normalChartForward S j e C b z).val).1, mem_univ _⟩ = z.val.1 := by
      change e.symm ⟨(C.symm (C ((e z.val.1).val, _))).1, mem_univ _⟩ = z.val.1
      rw [C.symm_apply_apply]
      exact e.left_inv hz
    apply Subtype.ext
    change (e.symm ⟨(C.symm (normalChartForward S j e C b z).val).1, mem_univ _⟩,
      (b (e.symm ⟨(C.symm (normalChartForward S j e C b z).val).1, mem_univ _⟩)
        (C.symm (normalChartForward S j e C b z).val).2).val) = z.val
    rw [hbase]
    simp only [normalChartForward, C.symm_apply_apply, LinearEquiv.apply_symm_apply]
  right_inv' := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have heq : (⟨(C.symm y.val).1, mem_univ _⟩ : ModelSpace n .euclidean) = x :=
      Subtype.ext hxy.symm
    apply Subtype.ext
    change C ((e (e.symm ⟨(C.symm y.val).1, mem_univ _⟩)).val,
      (b _).symm (b _ (C.symm y.val).2)) = y.val
    rw [heq, e.right_inv hx, LinearEquiv.symm_apply_apply, hxy]
    exact C.apply_symm_apply y.val
  open_source := e.open_source.preimage (continuous_fst.comp continuous_subtype_val)
  open_target := by
    have hval : IsOpen (Subtype.val '' e.target : Set (Euclidean n)) :=
      (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
        e.target e.open_target
    exact hval.preimage (continuous_fst.comp (C.symm.continuous.comp continuous_subtype_val))
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply C.continuous.continuousOn.comp
    · apply ContinuousOn.prodMk
      · exact continuous_subtype_val.continuousOn.comp
          (e.continuousOn.comp
            (continuous_fst.comp continuous_subtype_val).continuousOn (fun _ hz => hz))
          (fun _ _ => mem_univ _)
      · exact hK
    · intro z hz
      exact mem_univ _
  continuousOn_invFun := by
    let x : ModelSpace q .euclidean → ModelSpace n .euclidean :=
      fun y => ⟨(C.symm y.val).1, mem_univ _⟩
    have hx : Continuous x :=
      (continuous_fst.comp (C.symm.continuous.comp continuous_subtype_val)).subtype_mk _
    have hp : ContinuousOn (fun y => e.symm (x y))
        {y : ModelSpace q .euclidean | (C.symm y.val).1 ∈ Subtype.val '' e.target} := by
      apply e.symm.continuousOn.comp hx.continuousOn
      intro y hy
      obtain ⟨v, hv, heq⟩ := hy
      have hxy : x y = v := Subtype.ext heq.symm
      rwa [hxy]
    have hu : Continuous (fun y : ModelSpace q .euclidean => (C.symm y.val).2) :=
      continuous_snd.comp (C.symm.continuous.comp continuous_subtype_val)
    have hb := hB.comp (hp.prodMk hu.continuousOn)
      (fun y hy => ⟨by
        obtain ⟨v, hv, heq⟩ := hy
        have hxy : x y = v := Subtype.ext heq.symm
        change e.symm (x y) ∈ e.source
        rw [hxy]
        exact e.map_target hv, mem_univ _⟩)
    exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr (hp.prodMk hb)

@[simp] theorem normalBundleChart_source
    (hB : ContinuousOn (fun z : M × Euclidean k => (b z.1 z.2).val)
      (e.source ×ˢ univ))
    (hK : ContinuousOn (fun z : NormalTotal S j =>
      (b z.val.1).symm ⟨z.val.2, z.property⟩)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' e.source)) :
    (normalBundleChart S j e C b hB hK).source =
      (fun z => z.val.1) ⁻¹' e.source := rfl

@[simp] theorem normalBundleChart_target
    (hB : ContinuousOn (fun z : M × Euclidean k => (b z.1 z.2).val)
      (e.source ×ˢ univ))
    (hK : ContinuousOn (fun z : NormalTotal S j =>
      (b z.val.1).symm ⟨z.val.2, z.property⟩)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' e.source)) :
    (normalBundleChart S j e C b hB hK).target =
      {y | (C.symm y.val).1 ∈ Subtype.val '' e.target} := rfl

@[simp] theorem normalBundleChart_apply
    (hB : ContinuousOn (fun z : M × Euclidean k => (b z.1 z.2).val)
      (e.source ×ˢ univ))
    (hK : ContinuousOn (fun z : NormalTotal S j =>
      (b z.val.1).symm ⟨z.val.2, z.property⟩)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' e.source))
    (z : NormalTotal S j) :
    ((normalBundleChart S j e C b hB hK) z).val =
      C ((e z.val.1).val, (b z.val.1).symm ⟨z.val.2, z.property⟩) := rfl

/-- A base-coordinate description of a smooth local normal frame, including
its smooth inverse coordinate map. -/
structure NormalFrameChart where
  base : ModelChart n .euclidean M
  base_mem : base ∈ S.smoothStructure.val
  coordinateEquiv : (Euclidean n × Euclidean k) ≃L[ℝ] Euclidean q
  frame : ∀ p : M, Euclidean k ≃ₗ[ℝ] normalFiber S j p
  frameMap : Euclidean n → (Euclidean k →L[ℝ] Euclidean q)
  inverseMap : Euclidean n → (Euclidean q →L[ℝ] Euclidean k)
  frame_smooth : ContDiffOn ℝ (⊤ : ℕ∞) frameMap (Subtype.val '' base.target)
  inverse_smooth : ContDiffOn ℝ (⊤ : ℕ∞) inverseMap (Subtype.val '' base.target)
  frame_eq : ∀ p ∈ base.source, ∀ u, (frame p u).val = frameMap (base p).val u
  inverse_eq : ∀ p ∈ base.source, ∀ v : normalFiber S j p,
    (frame p).symm v = inverseMap (base p).val v.val

namespace NormalFrameChart
variable {S j e C b} (d : NormalFrameChart (k := k) S j)

theorem continuous_frame :
    ContinuousOn (fun z : M × Euclidean k => (d.frame z.1 z.2).val)
      (d.base.source ×ˢ univ) := by
  have hbase : ContinuousOn (fun z : M × Euclidean k => (d.base z.1).val)
      (d.base.source ×ˢ univ) :=
    continuous_subtype_val.continuousOn.comp
      (d.base.continuousOn.comp continuous_fst.continuousOn (fun _ hz => hz.1))
      (fun _ _ => mem_univ _)
  have hb := d.frame_smooth.continuousOn.comp hbase
    (fun z hz => ⟨d.base z.1, d.base.map_source hz.1, rfl⟩)
  exact (hb.clm_apply continuous_snd.continuousOn).congr
    (fun z hz => (d.frame_eq z.1 hz.1 z.2))

theorem continuous_inverse :
    ContinuousOn (fun z : NormalTotal S j =>
      (d.frame z.val.1).symm ⟨z.val.2, z.property⟩)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' d.base.source) := by
  have hbase : ContinuousOn (fun z : NormalTotal S j => (d.base z.val.1).val)
      ((fun z : NormalTotal S j => z.val.1) ⁻¹' d.base.source) :=
    continuous_subtype_val.continuousOn.comp
      (d.base.continuousOn.comp
        (continuous_fst.comp continuous_subtype_val).continuousOn (fun _ hz => hz))
      (fun _ _ => mem_univ _)
  have hk := d.inverse_smooth.continuousOn.comp hbase
    (fun z hz => ⟨d.base z.val.1, d.base.map_source hz, rfl⟩)
  exact (hk.clm_apply (continuous_snd.comp continuous_subtype_val).continuousOn).congr
    (fun z hz => (d.inverse_eq z.val.1 hz ⟨z.val.2, z.property⟩))

noncomputable def chart : ModelChart q .euclidean (NormalTotal S j) :=
  normalBundleChart S j d.base d.coordinateEquiv d.frame d.continuous_frame d.continuous_inverse

@[simp] theorem chart_source : d.chart.source =
    (fun z => z.val.1) ⁻¹' d.base.source := rfl

@[simp] theorem chart_target : d.chart.target =
    {y | (d.coordinateEquiv.symm y.val).1 ∈ Subtype.val '' d.base.target} := rfl

@[simp] theorem chart_apply (z : NormalTotal S j) :
    (d.chart z).val = d.coordinateEquiv ((d.base z.val.1).val,
      (d.frame z.val.1).symm ⟨z.val.2, z.property⟩) := rfl

@[simp] theorem chart_symm_apply (y : ModelSpace q .euclidean) :
    d.chart.symm y = normalChartInverse S j d.base d.coordinateEquiv d.frame y := rfl


/-- Normal coordinate changes are smooth because their matrix coefficients
and the base coordinate change are smooth on the corresponding open targets. -/
theorem chart_change_germ (d₁ d₂ : NormalFrameChart (k := k) S j)
    (z : NormalTotal S j) (hz₁ : z ∈ d₁.chart.source) (hz₂ : z ∈ d₂.chart.source) :
    ChartContDiffAt (⊤ : ℕ∞) d₁.chart d₂.chart id z := by
  have hp₁ : z.val.1 ∈ d₁.base.source := hz₁
  have hp₂ : z.val.1 ∈ d₂.base.source := hz₂
  obtain ⟨U, hU, hxU, F, hF, heF⟩ := chartContDiffAt_of_compatible
    (S.smoothStructure.property.1.2 d₁.base d₁.base_mem d₂.base d₂.base_mem) hp₁ hp₂
  let E₁ : Set (Euclidean n) := Subtype.val '' d₁.base.target
  let E₂ : Set (Euclidean n) := Subtype.val '' d₂.base.target
  have hE₁ : IsOpen E₁ :=
    (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
      d₁.base.target d₁.base.open_target
  have hE₂ : IsOpen E₂ :=
    (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
      d₂.base.target d₂.base.open_target
  let D : Set (Euclidean n) := (U ∩ E₁) ∩ F ⁻¹' E₂
  have hD : IsOpen D :=
    (hF.mono inter_subset_left).continuousOn.isOpen_inter_preimage (hU.inter hE₁) hE₂
  let X : Euclidean q → Euclidean n := fun y => (d₁.coordinateEquiv.symm y).1
  let Y : Euclidean q → Euclidean k := fun y => (d₁.coordinateEquiv.symm y).2
  have hX : ContDiff ℝ (⊤ : ℕ∞) X := contDiff_fst.comp d₁.coordinateEquiv.symm.contDiff
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := contDiff_snd.comp d₁.coordinateEquiv.symm.contDiff
  have hFX : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => F (X y)) (X ⁻¹' D) :=
    hF.comp hX.contDiffOn (fun y hy => hy.1.1)
  have hBX : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => d₁.frameMap (X y)) (X ⁻¹' D) :=
    d₁.frame_smooth.comp hX.contDiffOn (fun y hy => hy.1.2)
  have hKFX : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => d₂.inverseMap (F (X y))) (X ⁻¹' D) :=
    d₂.inverse_smooth.comp hFX (fun y hy => hy.2)
  let H : Euclidean q → Euclidean q := fun y =>
    d₂.coordinateEquiv (F (X y), d₂.inverseMap (F (X y)) (d₁.frameMap (X y) (Y y)))
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H (X ⁻¹' D) :=
    d₂.coordinateEquiv.contDiff.contDiffOn.comp
      (hFX.prodMk (hKFX.clm_apply (hBX.clm_apply hY.contDiffOn)))
      (fun _ _ => mem_univ _)
  refine ⟨X ⁻¹' D, hD.preimage hX.continuous, ?_, H, hH, ?_⟩
  · change X (d₁.chart z).val ∈ D
    have hXz : X (d₁.chart z).val = (d₁.base z.val.1).val := by
      simp only [X, chart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [hXz]
    refine ⟨⟨hxU, ⟨d₁.base z.val.1, d₁.base.map_source hp₁, rfl⟩⟩, ?_⟩
    change F (d₁.base z.val.1).val ∈ E₂
    have hFz : F (d₁.base z.val.1).val = (d₂.base z.val.1).val := heF.eq_of_nhds
    rw [hFz]
    exact ⟨d₂.base z.val.1, d₂.base.map_source hp₂, rfl⟩
  · have hproj : ContinuousAt (fun w : NormalTotal S j => w.val.1) z :=
      (continuous_fst.comp continuous_subtype_val).continuousAt
    filter_upwards [heF.comp_tendsto hproj, d₁.chart.open_source.mem_nhds hz₁,
      d₂.chart.open_source.mem_nhds hz₂] with w hwF hw₁ hw₂
    change F (d₁.base w.val.1).val = (d₂.base w.val.1).val at hwF
    change H (d₁.chart w).val = (d₂.chart w).val
    dsimp only [H, X, Y]
    simp only [chart_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [hwF, d₂.inverse_eq w.val.1 hw₂ ⟨w.val.2, w.property⟩]
    rw [← d₁.frame_eq w.val.1 hw₁ ((d₁.frame w.val.1).symm ⟨w.val.2, w.property⟩)]
    rw [LinearEquiv.apply_symm_apply]

theorem compatible (d₁ d₂ : NormalFrameChart (k := k) S j) :
    ContDiffCompatible (⊤ : ℕ∞) d₁.chart d₂.chart :=
  contDiffCompatible_of_germs (chart_change_germ d₁ d₂) (chart_change_germ d₂ d₁)

end NormalFrameChart

end NormalBundleCharts

section BundleSmoothness

open ModelData AtlasData MapData EuclideanTubularData Set Filter
open scoped Topology
noncomputable section

variable {n k q : ℕ} {M : Type} [TopologicalSpace M]

/-- An ambient-valued map only needs one source chart at a point. -/
theorem manifoldContDiffToEuclideanAt_of_oneChart
    {m l : ℕ} {a : ModelKind} {X : Type} [TopologicalSpace X]
    {r : ℕ∞} {A : Set (ModelChart m a X)} (hA : IsContDiffAtlas r A)
    {f : X → Euclidean l} {x : X} (hf : ContinuousAt f x)
    (e : ModelChart m a X) (he : e ∈ A) (hx : x ∈ e.source)
    (hlocal : LocalCoordinateExtension r (fun y => (e y).val) f x) :
    ManifoldContDiffToEuclideanAt r A f x := by
  refine ⟨hf, ?_⟩
  intro d hd hxd
  exact LocalCoordinateExtension.comp hlocal
    (chartContDiffAt_of_compatible (hA.2 d hd e he) hxd hx)

variable (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (e : ModelChart n .euclidean M)
    (C : (Euclidean n × Euclidean k) ≃L[ℝ] Euclidean q)
    (b : ∀ p : M, Euclidean k ≃ₗ[ℝ] normalFiber S j p)
    (h : ModelChart q .euclidean (NormalTotal S j))
    (hs : h.source = (fun z => z.val.1) ⁻¹' e.source)
    (hh : ∀ z : NormalTotal S j, (h z).val =
      C ((e z.val.1).val, (b z.val.1).symm ⟨z.val.2, z.property⟩))

include hh in
theorem normalProjection_chart_extension (z : NormalTotal S j) :
    ChartContDiffAt (⊤ : ℕ∞) h e (fun z => z.val.1) z := by
  refine ⟨univ, isOpen_univ, mem_univ _,
    (fun y => (C.symm y).1),
    (contDiff_fst.comp C.symm.contDiff).contDiffOn, ?_⟩
  exact Eventually.of_forall (fun w => by
    change (C.symm (h w).val).1 = (e w.val.1).val
    rw [hh, C.symm_apply_apply])

include hh in
theorem normalZero_chart_extension (p : M) :
    ChartContDiffAt (⊤ : ℕ∞) e h (normalZero S j) p := by
  refine ⟨univ, isOpen_univ, mem_univ _,
    (fun y => C (y, 0)),
    (C.contDiff.comp (contDiff_id.prodMk contDiff_const)).contDiffOn, ?_⟩
  exact Eventually.of_forall (fun w => by
    change C ((e w).val, 0) = (h (normalZero S j w)).val
    rw [hh]
    congr 1
    change ((e w).val, 0) = ((e w).val, (b w).symm 0)
    simp)

include hs hh in
theorem smoothAt_normalProjection
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (he : e ∈ S.smoothStructure.val) (hhmem : h ∈ N.smoothStructure.val)
    (z : NormalTotal S j) (hz : z ∈ h.source) :
    ManifoldSmoothAt N.smoothStructure.val S.smoothStructure.val
      (fun z => z.val.1) z := by
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    N.smoothStructure.property.1 S.smoothStructure.property.1 _ z).mpr
  exact ⟨(continuous_fst.comp continuous_subtype_val).continuousAt,
    h, hhmem, e, he, hz, (by simpa only [hs, mem_preimage] using hz),
    normalProjection_chart_extension S j e C b h hh z⟩

include hs hh in
theorem smoothAt_normalZero
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (he : e ∈ S.smoothStructure.val) (hhmem : h ∈ N.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) :
    ManifoldSmoothAt S.smoothStructure.val N.smoothStructure.val (normalZero S j) p := by
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 N.smoothStructure.property.1 _ p).mpr
  exact ⟨(continuous_normalZero S j).continuousAt,
    e, he, h, hhmem, hp, hs ▸ hp,
    normalZero_chart_extension S j e C b h hh p⟩

include hs hh in
theorem normalVector_chart_extension
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (Subtype.val '' e.target))
    (hb : ∀ p ∈ e.source, ∀ u, (b p u).val = B (e p).val u)
    (z : NormalTotal S j) (hz : z ∈ h.source) :
    LocalCoordinateExtension (⊤ : ℕ∞) (fun z => (h z).val)
      (fun z => z.val.2) z := by
  let U : Set (Euclidean n) := Subtype.val '' e.target
  have hU : IsOpen U :=
    (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
      e.target e.open_target
  let P : Euclidean q → Euclidean n := fun y => (C.symm y).1
  let Q : Euclidean q → Euclidean k := fun y => (C.symm y).2
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := contDiff_fst.comp C.symm.contDiff
  have hQ : ContDiff ℝ (⊤ : ℕ∞) Q := contDiff_snd.comp C.symm.contDiff
  have hzU : P (h z).val ∈ U := by
    change (C.symm (h z).val).1 ∈ Subtype.val '' e.target
    rw [hh, C.symm_apply_apply]
    exact ⟨e z.val.1, e.map_source (by simpa only [hs, mem_preimage] using hz), rfl⟩
  refine ⟨P ⁻¹' U, hU.preimage hP.continuous, hzU,
    (fun y => B (P y) (Q y)),
    (hB.comp hP.contDiffOn (fun _ hy => hy)).clm_apply hQ.contDiffOn, ?_⟩
  filter_upwards [h.open_source.mem_nhds hz] with w hw
  dsimp only [P, Q]
  rw [hh, C.symm_apply_apply]
  rw [← hb w.val.1 (by simpa only [hs, mem_preimage] using hw)]
  exact congrArg Subtype.val ((b w.val.1).apply_symm_apply ⟨w.val.2, w.property⟩)

include hs hh in
theorem smoothAt_normalVector
    (N : SmoothManifold q .euclidean (NormalTotal S j))
    (hhmem : h ∈ N.smoothStructure.val)
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (Subtype.val '' e.target))
    (hb : ∀ p ∈ e.source, ∀ u, (b p u).val = B (e p).val u)
    (z : NormalTotal S j) (hz : z ∈ h.source) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) N.smoothStructure.val
      (fun z => z.val.2) z := by
  exact manifoldContDiffToEuclideanAt_of_oneChart N.smoothStructure.property.1
    (continuous_snd.comp continuous_subtype_val).continuousAt h hhmem hz
    (normalVector_chart_extension S j e C b h hs hh B hB hb z hz)

/-- A fixed vector in a smooth local frame gives a smooth ambient section. -/
theorem smoothAt_normalFrameSection
    (he : e ∈ S.smoothStructure.val)
    (B : Euclidean n → Euclidean k →L[ℝ] Euclidean q)
    (hB : ContDiffOn ℝ (⊤ : ℕ∞) B (Subtype.val '' e.target))
    (hb : ∀ p ∈ e.source, ∀ u, (b p u).val = B (e p).val u)
    (u : Euclidean k) (p : M) (hp : p ∈ e.source) :
    ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
      (fun p => (b p u).val) p := by
  let U : Set (Euclidean n) := Subtype.val '' e.target
  have hU : IsOpen U :=
    (show IsOpen (modelSet n .euclidean) from isOpen_univ).isOpenMap_subtype_val
      e.target e.open_target
  have hep : (e p).val ∈ U := ⟨e p, e.map_source hp, rfl⟩
  have hBe : ContinuousAt B (e p).val := hB.continuousOn.continuousAt (hU.mem_nhds hep)
  have heCont : ContinuousAt (fun p => (e p).val) p :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hp)
  have hBu : ContinuousAt (fun x => B x u) (e p).val :=
    hBe.clm_apply continuousAt_const
  have hcont : ContinuousAt (fun p => B (e p).val u) p := hBu.comp (f := fun p => (e p).val) (x := p) heCont
  have heq : (fun p => B (e p).val u) =ᶠ[𝓝 p] (fun p => (b p u).val) := by
    filter_upwards [e.open_source.mem_nhds hp] with y hy
    exact (hb y hy u).symm
  apply manifoldContDiffToEuclideanAt_of_oneChart S.smoothStructure.property.1
    (hcont.congr heq) e he hp
  exact ⟨U, hU, hep, (fun y => B y u), hB.clm_apply contDiffOn_const, heq⟩

end
end BundleSmoothness

section NormalBundleAssembly

open ModelData AtlasData MapData EmbeddedData MapClassData EuclideanTubularData Set
open scoped Topology

variable {n q : ℕ} {M : Type} [TopologicalSpace M]

theorem exists_normalFrameChart
    (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val) (hj : IsSmoothEmbedding S T j)
    (p : M) :
    ∃ d : NormalFrameChart (k := q-n) S j, p ∈ d.base.source ∧
      ∀ (u : Euclidean (q-n)) (x : M), x ∈ d.base.source →
        ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
          (fun x => (d.frame x u).val) x := by
  obtain ⟨e, he, hp, C, b, B, K, hB, hK, hb, hk, hbsmooth⟩ :=
    NormalFrames.exists_actual_local_normal_frames S j T hT hj p
  let d : NormalFrameChart (k := q-n) S j :=
    { base := e
      base_mem := he
      coordinateEquiv := C
      frame := b
      frameMap := B
      inverseMap := K
      frame_smooth := hB
      inverse_smooth := hK
      frame_eq := hb
      inverse_eq := hk }
  exact ⟨d, hp, hbsmooth⟩


open ModelData AtlasData MapData EuclideanTubularData Set
open scoped Topology

variable {n q : ℕ} {M : Type} [TopologicalSpace M]
  (S : SmoothManifold n .euclidean M) (j : M → Euclidean q)

/-- A compatible cover of actual linear normal charts gives the normal
bundle on the specified subspace topology. -/
theorem exists_normal_bundle_of_charts
    (hcover : ∀ p : M, ∃ d : NormalFrameChart (k := q - n) S j,
      p ∈ d.base.source ∧
      ∀ (u : Euclidean (q-n)) (x : M), x ∈ d.base.source →
        ManifoldContDiffToEuclideanAt (⊤ : ℕ∞) S.smoothStructure.val
          (fun x => (d.frame x u).val) x)
    (hcompat : ∀ d d' : NormalFrameChart (k := q - n) S j,
      ContDiffCompatible (⊤ : ℕ∞) d.chart d'.chart) :
    ∃ N : SmoothManifold q .euclidean (NormalTotal S j),
      IsNormalBundleStructure S j N := by
  classical
  letI : T2Space M := S.topologicalManifold.hausdorff
  letI : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let A : Set (ModelChart q .euclidean (NormalTotal S j)) :=
    range (fun d : NormalFrameChart (k := q-n) S j => d.chart)
  have hAcov : IsAtlas A := by
    intro z
    obtain ⟨d, hp, _⟩ := hcover z.val.1
    exact ⟨d.chart, ⟨d, rfl⟩, by simpa only [d.chart_source, mem_preimage] using hp⟩
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := by
    refine ⟨hAcov, ?_⟩
    rintro h ⟨d, rfl⟩ h' ⟨d', rfl⟩
    exact hcompat d d'
  let N : SmoothManifold q .euclidean (NormalTotal S j) := {
    topologicalManifold := ⟨inferInstance,
      Topology.IsInducing.subtypeVal.secondCountableTopology, A, hAcov⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) A, maximalExtension_isMaximal hA⟩ }
  have hmem (d : NormalFrameChart (k := q-n) S j) : d.chart ∈ N.smoothStructure.val :=
    subset_maximalExtension hA ⟨d, rfl⟩
  refine ⟨N, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨d, hp, _⟩ := hcover z.val.1
    exact smoothAt_normalProjection S j d.base d.coordinateEquiv d.frame d.chart
      d.chart_source d.chart_apply N d.base_mem (hmem d) z hp
  · intro p
    obtain ⟨d, hp, _⟩ := hcover p
    exact smoothAt_normalZero S j d.base d.coordinateEquiv d.frame d.chart
      d.chart_source d.chart_apply N d.base_mem (hmem d) p hp
  · intro z
    obtain ⟨d, hp, _⟩ := hcover z.val.1
    exact smoothAt_normalVector S j d.base d.coordinateEquiv d.frame d.chart
      d.chart_source d.chart_apply N (hmem d) d.frameMap d.frame_smooth d.frame_eq z hp
  · intro p
    obtain ⟨d, hp, hsections⟩ := hcover p
    exact ⟨d.base, d.base_mem, hp, d.coordinateEquiv, d.frame, d.chart,
      hmem d, d.chart_source, d.chart_target, (fun z _ => d.chart_apply z), hsections⟩


/-- The normal spaces form a smooth vector bundle on their actual subspace
topology, for every smooth embedding under the original hypotheses. -/
theorem exists_normal_bundle
    (T : SmoothManifold q .euclidean (Euclidean q))
    (hT : euclideanChart q ∈ T.smoothStructure.val)
    (hj : IsSmoothEmbedding S T j) :
    ∃ N : SmoothManifold q .euclidean (NormalTotal S j),
      IsNormalBundleStructure S j N :=
  exists_normal_bundle_of_charts S j (exists_normalFrameChart S j T hT hj)
    (fun d d' => d.compatible d')

/-- Euclidean tubular neighborhood, with a smooth normal bundle, radial
invariance, retraction and smooth strong deformation, including empty bases. -/
theorem euclidean_tubular :
    Specs.SmoothManifolds.Ch04.EuclideanTubular.euclidean_tubularType := by
  intro n q M _ S T hT j hj
  obtain ⟨N, hN⟩ := exists_normal_bundle S j T hT hj
  exact ⟨N, hN, euclidean_tubular_of_normal_bundle S j T N hT hj hN⟩

end NormalBundleAssembly

end SmoothManifolds.EuclideanTubular
