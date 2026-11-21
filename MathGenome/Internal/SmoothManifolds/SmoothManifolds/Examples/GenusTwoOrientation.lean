import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.GenusTwoAtlas
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Examples.GenusTwoOrientation

/-! The full signed-frame calculation for the reflected connected sum.
Local lifts to angle coordinates differ by constant integer translations.
The two signed polar maps both have negative determinant, so positive bulk
wedges and negative seam wedges glue to the same intrinsic determinant ray. -/
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology
namespace SmoothManifolds.GenusTwoOrientation
open ModelData AtlasData SphereTorusData SphereTorus GenusTwoData GenusTwoAtlas
  OrientationData OrientationResults TangentBundleData Set Filter

/-- Local lifts of a torus map differ by a constant integer vector. -/
lemma projected_lifts_eventually {X : Type*} [TopologicalSpace X]
    {f g : X → Euclidean 2} {p : X} (hf : ContinuousAt f p) (hg : ContinuousAt g p)
    (hp : ∀ᶠ q in 𝓝 p, quotientProjection 2 (f q) = quotientProjection 2 (g q)) :
    (fun q => f q + (g p - f p)) =ᶠ[𝓝 p] g := by
  let k := g p - f p
  have hk : quotientProjection 2 k = 0 := by
    funext j
    change ((g p j : ℝ) : AddCircle (1:ℝ)) - ((f p j : ℝ) : AddCircle (1:ℝ)) = 0
    exact sub_eq_zero.mpr (congrFun ((Filter.EventuallyEq.eq_of_nhds hp).symm) j)
  have hc : ContinuousAt (fun q => f q + k) p := hf.add continuousAt_const
  have he : f p + k = g p := by dsimp [k]; abel
  have hb := (isOpen_angleBox (g p) (1/4)).mem_nhds
    (mem_angleBox_center (g p) (by norm_num))
  have hfb : ∀ᶠ q in 𝓝 p, f q + k ∈ angleBox (g p) (1/4) :=
    hc.preimage_mem_nhds (by simpa [he] using hb)
  have hgb : ∀ᶠ q in 𝓝 p, g q ∈ angleBox (g p) (1/4) := hg.preimage_mem_nhds hb
  filter_upwards [hp, hfb, hgb] with q hq hqf hqg
  apply quotientProjection_injOn_box (g p) (by norm_num : (1:ℝ)/4 < 1/2) hqf hqg
  calc
    quotientProjection 2 (f q + k) = quotientProjection 2 (f q) := by
      funext j
      change (f q j : AddCircle (1:ℝ)) + (k j : AddCircle (1:ℝ)) = _
      have hz := congrFun hk j
      change (k j : AddCircle (1:ℝ)) = 0 at hz
      rw [hz, add_zero]
      rfl
    _ = _ := hq

/-- The derivative of a lifted coordinate map is the actual intrinsic chart
transition derivative; integer translations contribute identity derivatives. -/
lemma transitionDeterminant_of_projection
    {S : SmoothManifold 2 .euclidean Surface} (K : FiberCoordinates S)
    {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(e.source ∩ d.source)) (A : Euclidean 2 → Euclidean 2)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hproj : ∀ᶠ q in 𝓝 p.val,
      quotientProjection 2 (A (e q).val) = quotientProjection 2 (d q).val) :
    transitionDeterminant K e d he hd p = (fderiv ℝ A (e p.val).val).det := by
  let k := (d p.val).val - A (e p.val).val
  let F := fun y => A y + k
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := hA.add contDiff_const
  have hrep : (fun q => F (e q).val) =ᶠ[𝓝 p.val] (fun q => (d q).val) :=
    projected_lifts_eventually
      (hA.continuous.continuousAt.comp
        (continuous_subtype_val.continuousAt.comp (e.continuousAt p.property.1)))
      (continuous_subtype_val.continuousAt.comp (d.continuousAt p.property.2)) hproj
  rw [OrientationResults.transition_jacobian S K e d he hd p univ F
    isOpen_univ (mem_univ _) hF.contDiffOn hrep]
  have hf : fderiv ℝ F (e p.val).val = fderiv ℝ A (e p.val).val := by
    exact ((hA.differentiable (by simp) _).hasFDerivAt.add_const k).fderiv
  rw [hf]

lemma bulk_transitionDeterminant
    {S : SmoothManifold 2 .euclidean Surface} (K : FiberCoordinates S)
    {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (heB : e ∈ bulkAtlas) (hdB : d ∈ bulkAtlas) (p : ↥(e.source ∩ d.source)) :
    transitionDeterminant K e d he hd p = 1 := by
  rcases heB with ⟨side,c,hc,heB⟩
  rcases hdB with ⟨side',c',hc',hdB⟩
  have h := transitionDeterminant_of_projection K he hd p id contDiff_id (by
    filter_upwards [e.open_source.mem_nhds p.property.1,
      d.open_source.mem_nhds p.property.2] with q hqe hqd
    exact interiorCharts_projection hc hc' heB hdB hqe hqd)
  simpa [ContinuousLinearMap.det] using h

lemma seam_projection {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ seamAtlas) (hd : d ∈ seamAtlas) {q : Surface}
    (hqe : q ∈ e.source) (hqd : q ∈ d.source) :
    quotientProjection 2 (e q).val = quotientProjection 2 (d q).val := by
  rcases he with ⟨a,δ,ε,_,_,_,hε,he⟩
  rcases hd with ⟨b,δ',ε',_,_,_,hε',hd⟩
  obtain ⟨heS, heq⟩ := seamChart_point he hε hqe
  obtain ⟨hdS, hdq⟩ := seamChart_point hd hε' hqd
  obtain ⟨ht,k,hk⟩ := seamPoint_fiber heS hdS (heq.trans hdq.symm)
  apply (quotientProjection_fiber 2 _ _).mpr
  refine ⟨![k,0], ?_⟩
  intro j
  fin_cases j
  · exact hk
  · simpa using ht

lemma seam_transitionDeterminant
    {S : SmoothManifold 2 .euclidean Surface} (K : FiberCoordinates S)
    {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (heS : e ∈ seamAtlas) (hdS : d ∈ seamAtlas) (p : ↥(e.source ∩ d.source)) :
    transitionDeterminant K e d he hd p = 1 := by
  have h := transitionDeterminant_of_projection K he hd p id contDiff_id (by
    filter_upwards [e.open_source.mem_nhds p.property.1,
      d.open_source.mem_nhds p.property.2] with q hqe hqd
    exact seam_projection heS hdS hqe hqd)
  simpa [ContinuousLinearMap.det] using h

lemma halfCoordinates_det_neg (side : Bool) (x : Euclidean 2)
    (hx : |x 1| < 1/16) : (fderiv ℝ (halfCoordinates side) x).det < 0 := by
  have ht := abs_lt.mp hx
  cases side
  · change (fderiv ℝ PolarData.positiveCollar x).det < 0
    rw [PolarCoordinates.positiveCollar_jacobian]
    have hp : 0 < (1/8 : ℝ)+x 1 := by linarith
    nlinarith [Real.pi_pos]
  · have he : halfCoordinates true = PolarData.negativeCollar := by
      funext y
      change reflectCoordinates (PolarData.polar ![y 0,1/8-y 1]) = _
      rw [reflectCoordinates_eq]
      rfl
    rw [he, PolarCoordinates.negativeCollar_jacobian]
    have hp : 0 < (1/8 : ℝ)-x 1 := by linarith
    nlinarith [Real.pi_pos]

lemma seam_bulk_transitionDeterminant_neg
    {S : SmoothManifold 2 .euclidean Surface} (K : FiberCoordinates S)
    {e d : ModelChart 2 .euclidean Surface}
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (heS : e ∈ seamAtlas) (hdB : d ∈ bulkAtlas) (p : ↥(e.source ∩ d.source)) :
    transitionDeterminant K e d he hd p < 0 := by
  rcases heS with ⟨a,δ,ε,_,_,_,hε,heS⟩
  rcases hdB with ⟨side,c,hc,hdB⟩
  rw [transitionDeterminant_of_projection K he hd p (halfCoordinates side)
    (smooth_halfCoordinates side) (by
      filter_upwards [e.open_source.mem_nhds p.property.1,
        d.open_source.mem_nhds p.property.2] with q hqe hqd
      exact interior_seam_projection hc hdB heS hε hqd hqe)]
  exact halfCoordinates_det_neg side _ (seamChart_point heS hε p.property.1).1

/-- A tagged family retains both prescribed sorts of charts. -/
abbrev GeneratingChart :=
  {e : ModelChart 2 .euclidean Surface // e ∈ bulkAtlas} ⊕
  {e : ModelChart 2 .euclidean Surface // e ∈ seamAtlas}

abbrev generatingChart : GeneratingChart → ModelChart 2 .euclidean Surface
  | .inl e => e.val
  | .inr e => e.val

def generatingSign : GeneratingChart → Bool
  | .inl _ => true
  | .inr _ => false

lemma generatingChart_mem (i : GeneratingChart) : generatingChart i ∈ constructionAtlas := by
  cases i with
  | inl e => exact Or.inl e.property
  | inr e => exact Or.inr e.property

lemma generatingChart_cover (p : Surface) : ∃ i : GeneratingChart, p ∈ (generatingChart i).source := by
  obtain ⟨e, he, hp⟩ := constructionAtlas_covers p
  rcases he with he | he
  · exact ⟨.inl ⟨e, he⟩, hp⟩
  · exact ⟨.inr ⟨e, he⟩, hp⟩

variable {S : SmoothManifold 2 .euclidean Surface}

lemma generatingChart_smooth
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas)
    (i : GeneratingChart) : generatingChart i ∈ S.smoothStructure.val := by
  rw [hS]
  exact subset_maximalExtension constructionAtlas_isContDiffAtlas (generatingChart_mem i)

/-- A signed coordinate wedge is a nonzero smooth local determinant section,
with its actual transition coefficients in every intrinsic coordinate system. -/
lemma constant_signed_section_smooth (K : FiberCoordinates S)
    (e : ModelChart 2 .euclidean Surface) (he : e ∈ S.smoothStructure.val) (b : Bool) :
    IsSmoothDeterminantSection e.source e.open_source
      (fun p => signValue b • coordinateVector K e he p) := by
  intro L d hd
  have ht := transitionDeterminant_smooth S L e d he hd
  have hcoeff : (fun p : ↥(e.source ∩ d.source) =>
      determinantCoefficient L d hd ⟨p.val, p.property.2⟩
        (signValue b • coordinateVector K e he ⟨p.val, p.property.1⟩)) =
      (fun p => signValue b * transitionDeterminant L e d he hd p) := by
    funext p
    rw [map_smul, smul_eq_mul]
    exact congrArg (fun t : ℝ => signValue b * t)
      ((congrArg (determinantCoefficient L d hd ⟨p.val, p.property.2⟩)
        (coordinateVector_independent K L e he ⟨p.val, p.property.1⟩)).trans
        (coefficient_coordinateVector_transition L e d he hd p))
  rw [hcoeff]
  intro p
  exact (ht p).postcomp (show ContDiff ℝ (⊤ : ℕ∞)
    (fun x : ℝ => signValue b * x) from contDiff_const.mul contDiff_id)

def chartRay (K : FiberCoordinates S) (e : ModelChart 2 .euclidean Surface)
    (he : e ∈ S.smoothStructure.val) (b : Bool) (p : e.source) : DeterminantRay S p.val :=
  rayOfNeZero ℝ (signValue b • coordinateVector K e he p)
    (signed_coordinateVector_ne_zero K e he p b)

lemma chartRay_eq_iff (K : FiberCoordinates S) (e d : ModelChart 2 .euclidean Surface)
    (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(e.source ∩ d.source)) (b c : Bool) :
    chartRay K e he b ⟨p.val, p.property.1⟩ = chartRay K d hd c ⟨p.val, p.property.2⟩ ↔
      signValue c = signValue b * SignType.sign (transitionDeterminant K e d he hd p) :=
  signed_coordinate_rays_eq_iff K e d he hd p b c

lemma generating_rays_eq
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) constructionAtlas)
    (K : FiberCoordinates S) (i j : GeneratingChart)
    (p : ↥((generatingChart i).source ∩ (generatingChart j).source)) :
    chartRay K (generatingChart i) (generatingChart_smooth hS i) (generatingSign i)
        ⟨p.val, p.property.1⟩ =
      chartRay K (generatingChart j) (generatingChart_smooth hS j) (generatingSign j)
        ⟨p.val, p.property.2⟩ := by
  have hmix : ∀ (e d : ModelChart 2 .euclidean Surface)
      (he : e ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val),
      e ∈ seamAtlas → d ∈ bulkAtlas → ∀ q : ↥(e.source ∩ d.source),
      chartRay K e he false ⟨q.val, q.property.1⟩ =
        chartRay K d hd true ⟨q.val, q.property.2⟩ := by
    intro e d he hd heS hdB q
    apply (chartRay_eq_iff K e d he hd q false true).mpr
    rw [sign_neg (seam_bulk_transitionDeterminant_neg K he hd heS hdB q)]
    norm_num [signValue]
  cases i with
  | inl e =>
    cases j with
    | inl d =>
      apply (chartRay_eq_iff K e.val d.val _ _ p true true).mpr
      rw [bulk_transitionDeterminant K _ _ e.property d.property p]
      norm_num [signValue]
    | inr d =>
      exact (hmix d.val e.val _ _ d.property e.property
        ⟨p.val, p.property.2, p.property.1⟩).symm
  | inr e =>
    cases j with
    | inl d => exact hmix e.val d.val _ _ e.property d.property p
    | inr d =>
      apply (chartRay_eq_iff K e.val d.val _ _ p false false).mpr
      rw [seam_transitionDeterminant K _ _ e.property d.property p]
      norm_num [signValue]

/-- The signed generating frames glue without an assumed coherence
certificate. The resulting ray field is continuous in every maximal chart. -/
theorem orientation_exists : Specs.SmoothManifolds.Examples.GenusTwoOrientation.orientationType := by
  intro S hS
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  choose idx hidx using generatingChart_cover
  let r : RayField S := fun p => chartRay K (generatingChart (idx p))
    (generatingChart_smooth hS (idx p)) (generatingSign (idx p)) ⟨p, hidx p⟩
  have hr : ∀ (L : FiberCoordinates S) (i : GeneratingChart) (p : (generatingChart i).source),
      IsPositive (r p.val)
        (signValue (generatingSign i) •
          coordinateVector L (generatingChart i) (generatingChart_smooth hS i) p) := by
    intro L i p
    rw [← coordinateVector_independent K L]
    refine ⟨signed_coordinateVector_ne_zero K _ _ p _, ?_⟩
    exact (generating_rays_eq hS K (idx p.val) i
      ⟨p.val, hidx p.val, p.property⟩).symm
  have hcont : IsContinuousRayField r := by
    intro L c hc
    apply locallyConstant_of_open_cover _
      (fun i : GeneratingChart => {p : c.source | p.val ∈ (generatingChart i).source})
      (fun i => (generatingChart i).open_source.preimage continuous_subtype_val)
      (fun p => generatingChart_cover p.val)
    intro i
    let e := generatingChart i
    let he := generatingChart_smooth hS i
    let g := fun p : e.source => signValue (generatingSign i) • coordinateVector K e he p
    have hgn : ∀ p, g p ≠ 0 := fun p => signed_coordinateVector_ne_zero K e he p _
    have h := smooth_section_ray_locallyConstant e.source e.open_source g hgn
      (constant_signed_section_smooth K e he (generatingSign i)) L c hc
    let incl : {p : c.source | p.val ∈ e.source} → ↥(e.source ∩ c.source) :=
      fun p => ⟨p.val.val, p.property, p.val.property⟩
    have hi : Continuous incl := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have heq : (fun p : {p : c.source | p.val ∈ e.source} =>
        Module.Ray.map (determinantCoordinates L c hc p.val) (r p.val.val)) =
        (fun p => Module.Ray.map (determinantCoordinates L c hc p.val)
          (rayOfNeZero ℝ (g ⟨p.val.val, p.property⟩) (hgn _))) := by
      funext p
      exact congrArg (Module.Ray.map (determinantCoordinates L c hc p.val))
        (hr K i ⟨p.val.val, p.property⟩).choose_spec.symm
    rw [heq]
    exact h.comp_continuous (f := incl) hi
  refine ⟨⟨r, hcont⟩, ?_⟩
  intro L e he
  constructor
  · intro heB p
    simpa [generatingChart, generatingSign, signValue] using hr L (.inl ⟨e, heB⟩) p
  · intro heS p
    have hp := hr L (.inr ⟨e, heS⟩) p
    change IsPositive (r p.val) ((-1 : ℝ) • coordinateVector L e he p) at hp
    rw [neg_one_smul ℝ (coordinateVector L e he p)] at hp
    exact hp

/-- A concrete orientation on the already fixed manifold, for downstream use. -/
def orientation : Orientation GenusTwoAtlas.smoothManifold :=
  (orientation_exists GenusTwoAtlas.smoothManifold rfl).choose

/-- The chosen orientation has the two prescribed frame signs, independently
of all intrinsic tangent-coordinate choices. -/
theorem orientation_signs (K : FiberCoordinates GenusTwoAtlas.smoothManifold)
    (e : ModelChart 2 .euclidean Surface)
    (he : e ∈ GenusTwoAtlas.smoothManifold.smoothStructure.val) :
    (e ∈ bulkAtlas → ∀ p : e.source,
      IsPositive (orientation.val p.val) (coordinateVector K e he p)) ∧
    (e ∈ seamAtlas → ∀ p : e.source,
      IsPositive (orientation.val p.val) (-coordinateVector K e he p)) :=
  (orientation_exists GenusTwoAtlas.smoothManifold rfl).choose_spec K e he

end SmoothManifolds.GenusTwoOrientation
