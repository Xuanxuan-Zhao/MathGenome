import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Degree.Properties
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Degree.RegularFibers
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.HomotopyInvariance
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.DegreeProperties
open ModelData AtlasData MapData TangentData DifferentialData CovectorData
  BundleOperationsData ExteriorData FormPullbackData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData DegreeData DeRhamData
universe u

/-- The integral characterization of degree identifies the induced map on
top cohomology in any realization of the genuine de Rham complex. -/
theorem integralFormula_on_cohomology
    {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N}
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f : M → N) (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (I : CompactTopForm S → ℝ) (Q : CompactTopForm T → ℝ) (r : ℝ)
    (hr : IntegralFormula S T f I Q r)
    (eM : K.Cohomology n ≃ₗ[ℝ] ℝ) (eN : J.Cohomology n ≃ₗ[ℝ] ℝ)
    (heM : ∀ ω : K.closed n, ∃ η : CompactTopForm S,
      η.field = ω.val.val ∧ eM (K.classOf n ω) = I η)
    (heN : ∀ ω : J.closed n, ∃ η : CompactTopForm T,
      η.field = ω.val.val ∧ eN (J.classOf n ω) = Q η)
    (F : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k)
    (hF : IsCohomologyPullback C B K J f L F) (x : J.Cohomology n) :
    eM (F n x) = r * eN x := by
  obtain ⟨α, hα⟩ := Submodule.mkQ_surjective (J.boundaries n) x
  change J.classOf n α = x at hα
  obtain ⟨β, hβ, hFβ⟩ := hF n α
  let ω : Form (E n) := ⟨α.val.val, (J.mem_forms n _).mp α.val.property⟩
  obtain ⟨η, ξ, hη, hξ, hIξ⟩ := hr A (E n) ω L hL
  obtain ⟨η', hη', heη'⟩ := heN α
  obtain ⟨ξ', hξ', heξ'⟩ := heM β
  have hηeq : η' = η := DegreeResults.compactTopForm_ext (hη'.trans hη.symm)
  have hξeq : ξ' = ξ :=
    DegreeResults.compactTopForm_ext (hξ'.trans (hβ.trans hξ.symm))
  calc
    eM (F n x) = eM (F n (J.classOf n α)) :=
      congrArg (fun z => eM (F n z)) hα.symm
    _ = eM (K.classOf n β) := congrArg eM hFβ
    _ = I ξ' := heξ'
    _ = I ξ := congrArg I hξeq
    _ = r * Q η := hIξ
    _ = r * Q η' := congrArg (fun z => r * Q z) hηeq.symm
    _ = r * eN (J.classOf n α) := congrArg (fun z => r * z) heη'.symm
    _ = r * eN x := congrArg (fun z => r * eN z) hα

theorem homotopy_invariance :
    Specs.SmoothManifolds.Degree.Properties.homotopy_invarianceType.{u} := by
  intro n a b M N _ _ _ _ _ _ S T f g hf hg hS hT hH o q I J hI hJ d e hd he
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  let B : ∀ k, FormBundle C k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  let E : ∀ k, FormBundle A k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  obtain ⟨Q⟩ := DeRhamResults.complex_exists A E
  obtain ⟨eM, heM⟩ := OrientedTopDegreeResults.compact_top_degree S hS o C B K I hI
  obtain ⟨eN, heN⟩ := OrientedTopDegreeResults.compact_top_degree T hT q A E Q J hJ
  let L := differential S T f hf
  let R := differential S T g hg
  have hL := differential_spec S T f hf
  have hR := differential_spec S T g hg
  obtain ⟨F, hF⟩ := DeRhamResults.pullback_exists S T C A B E K Q f hf L hL
  obtain ⟨G, hG⟩ := DeRhamResults.pullback_exists S T C A B E K Q g hg R hR
  have hFG := HomotopyResults.homotopy_invariance S T C B A E K Q f g hf hg hH
    L R hL hR F G hF hG n
  have hdf := integralFormula_on_cohomology C A B E K Q f L hL I J d hd.1
    eM eN heM heN F hF (eN.symm 1)
  have heg := integralFormula_on_cohomology C A B E K Q g R hR I J e he.1
    eM eN heM heN G hG (eN.symm 1)
  rw [hFG] at hdf
  have hcast : (d : ℝ) = (e : ℝ) := by simpa using hdf.symm.trans heg
  exact_mod_cast hcast

theorem identity : Specs.SmoothManifolds.Degree.Properties.identityType.{u} := by
  intro n a M _ _ _ S hS o I hI
  have hf : IsSmoothMap S S id := manifoldContDiff_id ⊤ _ S.smoothStructure.property.1
  obtain ⟨d, hd, _⟩ := DegreeResults.degree_exists S S id hf hS hS o o I I hI hI
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  let B : ∀ k, FormBundle C k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  obtain ⟨eM, heM⟩ := OrientedTopDegreeResults.compact_top_degree S hS o C B K I hI
  let L := differential S S id hf
  have hL := differential_spec S S id hf
  obtain ⟨F, hF⟩ := DeRhamResults.pullback_exists S S C C B B K K id hf L hL
  have hscalar := integralFormula_on_cohomology C C B B K K id L hL I I d hd.1
    eM eM heM heM F hF (eM.symm 1)
  rw [DeRhamResults.pullback_id S C B K L hL F hF n] at hscalar
  have hd1 : d = 1 := by exact_mod_cast (by simpa using hscalar.symm : (d : ℝ) = 1)
  simpa only [hd1] using hd

theorem composition : Specs.SmoothManifolds.Degree.Properties.compositionType.{u} := by
  intro n a b c M N P _ _ _ _ _ _ _ _ _ S T U f g hf hg hS hT hU o q r I J V hI hJ hV d e hd he
  have hgf : IsSmoothMap S U (g ∘ f) := manifoldContDiff_comp ⊤ _ _ _ T.smoothStructure.property.1.1 f g hf hg
  obtain ⟨z, hz, _⟩ := DegreeResults.degree_exists S U (g ∘ f) hgf hS hU o r I V hI hV
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  obtain ⟨D⟩ := BundleOperations.exists_cotangent U
  let B : ∀ k, FormBundle C k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  let E : ∀ k, FormBundle A k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  let W : ∀ k, FormBundle D k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle D k)
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  obtain ⟨Q⟩ := DeRhamResults.complex_exists A E
  obtain ⟨R⟩ := DeRhamResults.complex_exists D W
  obtain ⟨eM, heM⟩ := OrientedTopDegreeResults.compact_top_degree S hS o C B K I hI
  obtain ⟨eN, heN⟩ := OrientedTopDegreeResults.compact_top_degree T hT q A E Q J hJ
  obtain ⟨eP, heP⟩ := OrientedTopDegreeResults.compact_top_degree U hU r D W R V hV
  let L := differential S T f hf
  let H := differential T U g hg
  let X := differential S U (g ∘ f) hgf
  have hL := differential_spec S T f hf
  have hH := differential_spec T U g hg
  have hX := differential_spec S U (g ∘ f) hgf
  obtain ⟨F, hF⟩ := DeRhamResults.pullback_exists S T C A B E K Q f hf L hL
  obtain ⟨G, hG⟩ := DeRhamResults.pullback_exists T U A D E W Q R g hg H hH
  obtain ⟨Z, hZ⟩ := DeRhamResults.pullback_exists S U C D B W K R (g ∘ f) hgf X hX
  have hcomp := DeRhamResults.pullback_comp S T U C A D B E W K Q R f g hf hg
    L H X hL hH hX F G Z hF hG hZ n (eP.symm 1)
  have hzscalar := integralFormula_on_cohomology C D B W K R (g ∘ f) X hX I V z hz.1
    eM eP heM heP Z hZ (eP.symm 1)
  rw [hcomp, integralFormula_on_cohomology C A B E K Q f L hL I J d hd.1
    eM eN heM heN F hF, integralFormula_on_cohomology A D E W Q R g H hH J V e he.1
    eN eP heN heP G hG] at hzscalar
  have hze : z = e * d := by
    have hcast : (z : ℝ) = (e * d : ℤ) := by
      simpa only [LinearEquiv.apply_symm_apply, mul_one, Int.cast_mul, mul_comm] using hzscalar.symm
    exact_mod_cast hcast
  simpa only [hze] using hz

theorem finite_boundary_components :
    Specs.SmoothManifolds.Degree.Properties.finite_boundary_componentsType.{u} := by
  intro n a W _ _ S B
  letI := S.topologicalManifold.hausdorff
  haveI : CompactSpace (intrinsicBoundary S) :=
    isCompact_iff_compactSpace.mp (isClosed_intrinsicBoundary S).isCompact
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace B.topologicalManifold
  infer_instance

theorem boundary_pullback_integral_zero :
    Specs.SmoothManifolds.Degree.Properties.boundary_pullback_integral_zeroType.{u} := by
  intro n a b W N _ _ _ S T B hB o q hq G hG L R hL hR A E ω J hJ
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  obtain ⟨F⟩ := BundleOperations.exists_cotangent B
  let V : ∀ k, FormBundle C k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  let H : ∀ k, FormBundle A k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨K⟩ := DeRhamResults.complex_exists C V
  obtain ⟨Q⟩ := DeRhamResults.complex_exists A H
  have hω : IsForm (H n) ω.field := DegreeResults.smooth_form_change A A E (H n) ω.field ω.smooth
  let α := FormPullbackData.pullbackField S T G L ω.field
  have hα : IsForm (V n) α :=
    FormPullbackResults.pullback_smooth S T C A G hG L hL n (V n) (H n) ω.field hω
  have hzero : Q.D n ω.field = 0 := by
    funext p
    exact ExteriorAlgebraResults.fields_above_dimension A (n+1) (Nat.lt_succ_self n) _ p
  have hnat := ExteriorDerivativeResults.smooth_naturality S T C A V H K.D Q.D
    K.axioms Q.axioms G hG L hL n ω.field hω
  have hDα : K.D n α = 0 := by
    rw [hzero] at hnat
    calc
      K.D n α = FormPullbackData.pullbackField S T G L (0 : Field T (n+1)) := hnat.symm
      _ = 0 := by
        funext p
        change (FormPullbackData.fiberPullback
          (V := TangentSpace S p) (W := TangentSpace T (G p)) (n+1) (L p)) 0 = 0
        exact LinearMap.map_zero _
  have hdα : ExteriorDerivativeData.HasExteriorDerivative C α 0 := by
    simpa only [hDα] using K.coordinates n α hα
  obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral S o
  obtain ⟨η, β, hdη, _, hβ, hint⟩ := StokesResults.stokes S C B F hB o q hq
    R hR I J hI hJ α (ExteriorDerivativeResults.smooth_regular C n (V n) α 1 hα)
      (StokesResults.compact_support S n α)
  have hη : η.field = 0 := ExteriorDerivativeResults.derivative_unique C n α η.field 0 hdη hdα
  have hηzero : I η = 0 := by
    have hadd := hI.1 η η η (by rw [hη]; simp)
    linarith
  exact ⟨β, hβ, hint.symm.trans hηzero⟩

end SmoothManifolds.DegreeProperties

namespace SmoothManifolds.DegreeComponentData
open ModelData AtlasData MapData TangentData DifferentialData OrientationData
  OrientationProductData BoundaryData Set
universe u
section Topology
variable {M : Type u} [TopologicalSpace M]

lemma componentSet_mk (p : M) : componentSet (ConnectedComponents.mk p) = connectedComponent p := by
  ext q
  exact ConnectedComponents.coe_eq_coe'

lemma componentSet_nonempty (c : ConnectedComponents M) : (componentSet c).Nonempty := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  exact ⟨p, rfl⟩

lemma componentSet_isClosed (c : ConnectedComponents M) : IsClosed (componentSet c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentSet_mk]
  exact isClosed_connectedComponent

lemma componentSet_isOpen [LocallyConnectedSpace M] (c : ConnectedComponents M) : IsOpen (componentSet c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentSet_mk]
  exact isOpen_connectedComponent

lemma componentSet_isConnected (c : ConnectedComponents M) : IsConnected (componentSet c) := by
  obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe c
  rw [componentSet_mk]
  exact isConnected_connectedComponent

lemma componentSet_connectedSpace (c : ConnectedComponents M) : ConnectedSpace (componentSet c) :=
  Subtype.connectedSpace (componentSet_isConnected c)

lemma componentSet_compactSpace [CompactSpace M] (c : ConnectedComponents M) : CompactSpace (componentSet c) :=
  isCompact_iff_compactSpace.mp (componentSet_isClosed c).isCompact

lemma componentSet_component (p : M) (c : ConnectedComponents M) (hp : p ∈ componentSet c) :
    connectedComponent p = componentSet c := by
  rw [← componentSet_mk, hp]

lemma componentSet_pairwiseDisjoint : Pairwise (fun c d : ConnectedComponents M => Disjoint (componentSet c) (componentSet d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact hcd (hp.symm.trans hq)

lemma componentSet_cover : ⋃ c : ConnectedComponents M, componentSet c = Set.univ := by
  ext p
  simp [componentSet, QuotientData.componentSet]

end Topology

theorem openSubset_orientation
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U hU))
    (hi : IsSmoothMap R S Subtype.val) (o : Orientation S) :
    ∃ (E : ∀ p : U, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val),
      (∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap) ∧
      ∃ r : Orientation R,
        (∀ p, Module.Ray.map (determinantMap (V := TangentSpace R p) (W := TangentSpace S p.val) n (E p)) (r.val p) = o.val p.val) ∧
        (∀ p, orientationSign r o E p = true) := by
  classical
  have hex := fun p => OrientedTopDegreeResults.LocalTransport.open_inclusion_differential_equiv
    S U hU R hR hi p
  choose E hE using hex
  have hcont : @IsContinuousRayField n a U inferInstance R (fun p : U =>
      Module.Ray.map (determinantMap (V := TangentSpace S p.val) (W := TangentSpace R p) n (E p).symm) (o.val p.val)) := by
    exact OrientationProducts.pullbackRayField_continuous R S Subtype.val hi o E hE
  let r : Orientation R := ⟨_, hcont⟩
  have hr (p : U) : Module.Ray.map (determinantMap (V := TangentSpace R p) (W := TangentSpace S p.val) n (E p)) (r.val p) = o.val p.val := by
    change Module.Ray.map (determinantMap (V := TangentSpace R p) (W := TangentSpace S p.val) n (E p))
      (Module.Ray.map (determinantMap (V := TangentSpace S p.val) (W := TangentSpace R p) n (E p).symm) (o.val p.val)) = o.val p.val
    simpa only [LinearEquiv.symm_symm] using
      (OrientationProducts.rayMap_determinant_symm_apply_apply
        (V := TangentSpace S p.val) (W := TangentSpace R p) n (E p).symm (o.val p.val))
  exact ⟨E, hE, r, hr, fun p => by simp only [orientationSign, hr p, ↓reduceIte]⟩

end SmoothManifolds.DegreeComponentData

namespace SmoothManifolds.DegreeProperties
open ModelData AtlasData MapData TangentData DifferentialData OrientationData
  OrientationProductData BoundaryData DegreeComponentData Set
universe u

theorem component_geometry :
    Specs.SmoothManifolds.Degree.Properties.component_geometryType.{u} := by
  classical
  intro n M _ S o c
  letI := TopologicalManifold.locallyPathConnectedSpace S.topologicalManifold
  have hU := componentSet_isOpen c
  obtain ⟨R, _, hR, hi⟩ := exists_openSubset_smoothManifold S (componentSet c) hU
  obtain ⟨E, hE, r, hr, _⟩ := openSubset_orientation S _ hU R hR hi o
  exact ⟨{
    isOpen := hU
    manifold := R
    atlas_eq := hR
    inclusion_smooth := hi
    tangentEquiv := E
    tangent_differential := hE
    orientation := r
    orientation_preserving := hr }⟩

theorem component_degree_hypotheses :
    Specs.SmoothManifolds.Degree.Properties.component_degree_hypothesesType.{u} := by
  intro n m b M N _ _ _ B T q D f hf c
  refine ⟨componentSet_connectedSpace c, componentSet_compactSpace c,
    intrinsicBoundary_euclidean (D c).manifold, ?_⟩
  exact manifoldContDiff_comp _ _ _ _ B.smoothStructure.property.1.1
    Subtype.val f (D c).inclusion_smooth hf

end SmoothManifolds.DegreeProperties

namespace SmoothManifolds.DegreeProperties
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  ExteriorData FormPullbackData OrientationData OrientationProductData
  LocalIntegrationData GlobalIntegrationData Set
universe u

/-- Actual continuous pullback, compact because the component is compact. -/
def compactComponentPullback {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M) [CompactSpace U]
    (R : SmoothManifold n a U) (hi : IsSmoothMap R S Subtype.val)
    (E : ∀ p, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (η : CompactTopForm S) : CompactTopForm R where
  field := FormPullbackData.pullbackField R S Subtype.val (fun p => (E p).toLinearMap) η.field
  continuous := DiffeomorphismLocalResults.continuous_pullback_of_smooth R S Subtype.val hi
    (fun p => (E p).toLinearMap) hE η.field η.continuous
  compact_support := isClosed_closure.isCompact

/-- The component integral agrees with the ambient integral of a field supported
inside this component. This proves the required transport from the original
`IsIntegral` coordinate axioms. -/
theorem integral_open_component {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M)
    (hU : IsOpen U) (hne : Nonempty U) [CompactSpace U]
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U hU))
    (hi : IsSmoothMap R S Subtype.val)
    (E : ∀ p, TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (r : Orientation R) (o : Orientation S)
    (hpres : ∀ p, orientationSign r o E p = true)
    (I : CompactTopForm R → ℝ) (J : CompactTopForm S → ℝ)
    (hI : IsIntegral r I) (hJ : IsIntegral o J)
    (η : CompactTopForm S) (hηU : sectionSupport η.field ⊆ U)
    (ξ : CompactTopForm R)
    (hξ : ξ.field = FormPullbackData.pullbackField R S Subtype.val
      (fun p => (E p).toLinearMap) η.field) : I ξ = J η := by
  let A := {c : ModelChart n a M // c ∈ S.smoothStructure.val}
  obtain ⟨ρ, hρ⟩ := GlobalIntegrationResults.exists_chart_localization S η
  obtain ⟨t, ht, hsum⟩ := GlobalIntegrationResults.localization_decomposition
    (fun c : A => c.val) ρ η hρ
  let ζ : A → CompactTopForm S := fun i =>
    GlobalIntegrationResults.weightForm (ρ i) (hρ.1 i) η
  let ω : A → CompactTopForm R := fun i => compactComponentPullback S U R hi E hE (ζ i)
  have hsumξ : ξ.field = ∑ i ∈ t, (ω i).field := by
    funext p
    simp only [Finset.sum_apply]
    rw [hξ]
    change fiberPullback (V := TangentSpace R p) (W := TangentSpace S p.val)
      n (E p).toLinearMap (η.field p.val) = _
    rw [hsum]
    simp only [Finset.sum_apply, map_sum]
    rfl
  rw [GlobalIntegrationResults.integral_finset_sum hI t ω ξ hsumξ,
    GlobalIntegrationResults.integral_finset_sum hJ t ζ η hsum]
  apply Finset.sum_congr rfl
  intro i _
  let c := i.val
  have hc : c ∈ S.smoothStructure.val := i.property
  let d : ModelChart n a U := c.subtypeRestr (s := ⟨U, hU⟩) hne
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    apply subset_maximalExtension (openSubsetAtlas_isContDiffAtlas
      (⊤ : ℕ∞) S.smoothStructure.val S.smoothStructure.property.1 U hU)
    exact ⟨hne, c, hc, rfl⟩
  let e₀ : OpenPartialHomeomorph U M :=
    (⟨U, hU⟩ : TopologicalSpace.Opens M).openPartialHomeomorphSubtypeCoe hne
  let e : OpenPartialHomeomorph U M := e₀.restrOpen d.source d.open_source
  have hes : e.source = d.source := by
    simp only [e, OpenPartialHomeomorph.restrOpen_source,
      e₀, TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_source, univ_inter]
  have heq : EqOn e Subtype.val e.source := by intro p _; rfl
  have hζ (p : M) (hp : p ∈ sectionSupport (ζ i).field) :
      p ∈ c.source ∧ p ∈ U := by
    have hh := GlobalIntegrationResults.weight_support S n η.field (ρ i) hp
    exact ⟨hρ.2.2.1 i hh.1, hηU hh.2⟩
  have hωsupp : sectionSupport (ω i).field ⊆ e.source := by
    intro p hp
    rw [hes]
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
      (hζ p.val (GlobalIntegrationResults.pullback_support R S Subtype.val
        continuous_subtype_val (fun p => (E p).toLinearMap) n (ζ i).field hp)).1
  have hηsupp : sectionSupport (ζ i).field ⊆ c.source ∩ e.target := by
    intro p hp
    obtain ⟨hpc, hpU⟩ := hζ p hp
    refine ⟨hpc, ?_⟩
    have hsource : (⟨p, hpU⟩ : U) ∈ e.source := by
      rw [hes]
      simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hpc
    have hval : e ⟨p, hpU⟩ = p := by rfl
    have hh := e.map_source hsource
    rw [hval] at hh
    exact hh
  have hec : e.source ⊆ d.source := by rw [hes]
  have hfs := GlobalIntegrationResults.pullback_support R S Subtype.val
    continuous_subtype_val (fun p => (E p).toLinearMap) n (ζ i).field
  have hh := DegreeResults.partial_constant_sign_substitution R S Subtype.val hi e heq E
    (fun p _ => hE p) (ω i) (ζ i) (fun p _ => rfl) r o I J hI hJ
    d c hd hc hec hωsupp hfs hηsupp true (fun p _ => hpres p)
  simpa [signValue] using hh


/-- Decomposition over a finite disjoint open cover, with every term the actual
integral on the corresponding canonical subtype. The empty index case is included. -/
theorem integral_component_sum {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    {ι : Type u} [Fintype ι] (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i)) (hne : ∀ i, Nonempty (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hcover : (univ : Set M) ⊆ ⋃ i, U i)
    [∀ i, CompactSpace (U i)]
    (R : ∀ i, SmoothManifold n a (U i))
    (hR : ∀ i, (R i).smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val (U i) (hU i)))
    (hi : ∀ i, IsSmoothMap (R i) S Subtype.val)
    (E : ∀ i p, TangentSpace (R i) p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ i p, IsDifferential (R i) S Subtype.val p (E i p).toLinearMap)
    (r : ∀ i, Orientation (R i)) (o : Orientation S)
    (hpres : ∀ i p, orientationSign (r i) o (E i) p = true)
    (I : ∀ i, CompactTopForm (R i) → ℝ) (J : CompactTopForm S → ℝ)
    (hI : ∀ i, IsIntegral (r i) (I i)) (hJ : IsIntegral o J)
    (η : CompactTopForm S) (ξ : ∀ i, CompactTopForm (R i))
    (hξ : ∀ i, (ξ i).field = FormPullbackData.pullbackField (R i) S Subtype.val
      (fun p => (E i p).toLinearMap) η.field) :
    J η = ∑ i, I i (ξ i) := by
  have hcov : sectionSupport η.field ⊆ ⋃ i, U i := (subset_univ _).trans hcover
  let σ : ι → CompactTopForm S := fun i => DegreeResults.sliceTopForm η (U i) (hU i)
    (DegreeResults.closed_inter_of_disjoint_cover U hU hdisj _ isClosed_closure hcov i)
  have hσ i : sectionSupport (σ i).field ⊆ U i := fun p hp =>
    (DegreeResults.sliceField_support (U i) η.field
      (DegreeResults.closed_inter_of_disjoint_cover U hU hdisj _ isClosed_closure hcov i) hp).2
  have heq i : I i (ξ i) = J (σ i) := by
    apply integral_open_component S (U i) (hU i) (hne i) (R i) (hR i) (hi i) (E i) (hE i)
      (r i) o (hpres i) (I i) J (hI i) hJ (σ i) (hσ i)
    rw [hξ i]
    funext p
    simp only [σ, DegreeResults.sliceTopForm, FormPullbackData.pullbackField,
      DegreeResults.sliceField, p.property, ite_eq_left]
  have hdecomp := DegreeResults.integral_disjoint_slices U hU hdisj η hcov o J hJ
  rw [hdecomp]
  apply Finset.sum_congr rfl
  intro i _
  exact (heq i).symm

end SmoothManifolds.DegreeProperties

namespace SmoothManifolds.DegreeProperties
open ModelData AtlasData MapData TangentData DifferentialData CovectorData
  BundleOperationsData ExteriorData FormPullbackData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData BoundaryOrientationData DegreeData
universe u v

/-- Internal assembly: all geometry and the integral split must be supplied by
proved helpers before using this lemma in the unconditional boundary theorem. -/
theorem boundary_degree_sum_from_integral_split
    {n : ℕ} {a b : ModelKind} {W N : Type u}
    [TopologicalSpace W] [TopologicalSpace N] [CompactSpace W] [Nonempty N]
    (S : SmoothManifold (n+1) a W) (T : SmoothManifold n b N)
    (B : SmoothManifold n .euclidean (intrinsicBoundary S))
    (hB : IsNaturalBoundary S B) (o : Orientation S) (q : Orientation B)
    (hq : IsInducedOrientation o q) (r : Orientation T)
    (G : W → N) (hG : IsSmoothMap S T G) (hT : intrinsicBoundary T = ∅)
    (J : CompactTopForm T → ℝ) (hJ : IsIntegral r J)
    (Ib : CompactTopForm B → ℝ) (hIb : IsIntegral q Ib)
    {ι : Type v} [Fintype ι]
    (U : ι → Set (intrinsicBoundary S))
    (R : ∀ c, SmoothManifold n .euclidean (U c))
    (hc : ∀ c, IsSmoothMap (R c) B Subtype.val)
    (E : ∀ c, ∀ p : U c, TangentSpace (R c) p →ₗ[ℝ] TangentSpace B p.val)
    (hE : ∀ c p, IsDifferential (R c) B Subtype.val p (E c p))
    (rc : ∀ c, Orientation (R c)) (Ic : ∀ c, CompactTopForm (R c) → ℝ)
    (d : ι → ℤ)
    (hd : ∀ c, HasDegree (R c) T (fun p => G p.val.val) (rc c) r (Ic c) J (d c))
    (hsplit : ∀ (β : CompactTopForm B)
      (ξ : ∀ c, CompactTopForm (R c)),
      (∀ c, (ξ c).field = FormPullbackData.pullbackField (R c) B Subtype.val (E c) β.field) →
      Ib β = ∑ c, Ic c (ξ c)) :
    ∑ c, d c = 0 := by
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  obtain ⟨H⟩ := ExteriorAlgebraResults.exists_formBundle A n
  obtain ⟨η, hη, _, hηone⟩ := DegreeForms.exists_unit_integral_form T hT r A H J hJ
    (Classical.choice (inferInstance : Nonempty N)) Set.univ isOpen_univ (Set.mem_univ _)
  let ω : Form H := ⟨η.field, hη⟩
  let L := differential S T G hG
  have hL := differential_spec S T G hG
  let Q := differential B S Subtype.val hB.1
  have hQ := differential_spec B S Subtype.val hB.1
  let F : intrinsicBoundary S → N := G ∘ Subtype.val
  have hF : IsSmoothMap B T F :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 _ _ hB.1 hG
  let LF := differential B T F hF
  have hLF := differential_spec B T F hF
  obtain ⟨β, hβ, hβzero⟩ := boundary_pullback_integral_zero S T B hB o q hq G hG
    L Q hL hQ A H ω Ib hIb
  have hβF : β.field = FormPullbackData.pullbackField B T F LF ω.field := by
    exact hβ.trans (FormPullbackResults.pullback_comp B S T Subtype.val G hB.1 hG
      Q L LF hQ hL hLF n ω.field).symm
  have hcomp (c : ι) : IsSmoothMap (R c) T (fun p => G p.val.val) :=
    manifoldContDiff_comp ⊤ _ _ _ B.smoothStructure.property.1.1 _ _ (hc c) hF
  let Lc := fun c => differential (R c) T (fun p => G p.val.val) (hcomp c)
  have hLc := fun c => differential_spec (R c) T (fun p => G p.val.val) (hcomp c)
  have hforms (c : ι) : ∃ ξ : CompactTopForm (R c),
      ξ.field = FormPullbackData.pullbackField (R c) B Subtype.val (E c) β.field ∧
      Ic c ξ = (d c : ℝ) := by
    obtain ⟨ηc, ξ, hηc, hξ, hIc⟩ := (hd c).1 A H ω (Lc c) (hLc c)
    have hηceq : ηc = η := DegreeResults.compactTopForm_ext hηc
    refine ⟨ξ, ?_, ?_⟩
    · calc
        ξ.field = FormPullbackData.pullbackField (R c) T (fun p => G p.val.val)
            (Lc c) ω.field := hξ
        _ = FormPullbackData.pullbackField (R c) B Subtype.val (E c)
            (FormPullbackData.pullbackField B T F LF ω.field) :=
          FormPullbackResults.pullback_comp (R c) B T Subtype.val F (hc c) hF
            (E c) LF (Lc c) (hE c) hLF (hLc c) n ω.field
        _ = FormPullbackData.pullbackField (R c) B Subtype.val (E c) β.field :=
          congrArg (FormPullbackData.pullbackField (R c) B Subtype.val (E c)) hβF.symm
    · simpa only [hηceq, hηone, mul_one] using hIc
  choose ξ hξ hIξ using hforms
  have hsum : (∑ c, (d c : ℝ)) = 0 := by
    calc
      (∑ c, (d c : ℝ)) = ∑ c, Ic c (ξ c) := Finset.sum_congr rfl (fun c _ => (hIξ c).symm)
      _ = Ib β := (hsplit β ξ hξ).symm
      _ = 0 := hβzero
  exact_mod_cast hsum
end SmoothManifolds.DegreeProperties

namespace SmoothManifolds.DegreeProperties
open ModelData AtlasData MapData TangentData DifferentialData OrientationData
  OrientationProductData BoundaryData BoundaryOrientationData DegreeComponentData
  LocalIntegrationData GlobalIntegrationData DegreeData Set
universe u

open DegreeComponentData OrientationProductData

theorem boundary_degree_sum :
    Specs.SmoothManifolds.Degree.Properties.boundary_degree_sumType.{u} := by
  intro n a b W N _ _ _ _ _ S T hT B hB o q hq r J hJ G hG
  letI := S.topologicalManifold.hausdorff
  letI : CompactSpace (intrinsicBoundary S) :=
    isCompact_iff_compactSpace.mp (isClosed_intrinsicBoundary S).isCompact
  letI : Finite (ConnectedComponents (intrinsicBoundary S)) :=
    finite_boundary_components S B
  letI := Fintype.ofFinite (ConnectedComponents (intrinsicBoundary S))
  let D : ∀ c : ConnectedComponents (intrinsicBoundary S), Geometry B q c :=
    fun c => Classical.choice (component_geometry B q c)
  let F : intrinsicBoundary S → N := G ∘ Subtype.val
  have hF : IsSmoothMap B T F :=
    manifoldContDiff_comp ⊤ _ _ _ S.smoothStructure.property.1.1 _ _ hB.1 hG
  have hprops := component_degree_hypotheses B T q D F hF
  letI : ∀ c : ConnectedComponents (intrinsicBoundary S),
      ConnectedSpace (componentSet c) := fun c => (hprops c).1
  letI : ∀ c : ConnectedComponents (intrinsicBoundary S),
      CompactSpace (componentSet c) := fun c => (hprops c).2.1
  have hexI (c : ConnectedComponents (intrinsicBoundary S)) :
      ∃ I : CompactTopForm (D c).manifold → ℝ, IsIntegral (D c).orientation I := by
    obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral (D c).manifold (D c).orientation
    exact ⟨I, hI⟩
  choose I hI using hexI
  have hexd (c : ConnectedComponents (intrinsicBoundary S)) :
      ∃ d : ℤ, HasDegree (D c).manifold T (fun p => G p.val.val)
        (D c).orientation r (I c) J d := by
    obtain ⟨d, hd, _⟩ := DegreeResults.degree_exists (D c).manifold T
      (fun p => G p.val.val) (hprops c).2.2.2 (hprops c).2.2.1 hT
      (D c).orientation r (I c) J (hI c) hJ
    exact ⟨d, hd⟩
  choose d hd using hexd
  refine ⟨D, I, d, ?_, ?_⟩
  · intro c
    exact ⟨(hprops c).1, (hprops c).2.1, (hprops c).2.2.1,
      (hprops c).2.2.2, hI c, hd c⟩
  · obtain ⟨Ib, hIb, _⟩ := GlobalIntegrationResults.exists_integral B q
    have hpres (c : ConnectedComponents (intrinsicBoundary S)) (p : componentSet c) :
        orientationSign (D c).orientation q (D c).tangentEquiv p = true := by
      simp only [orientationSign, (D c).orientation_preserving p, ↓reduceIte]
    have hcover : (Set.univ : Set (intrinsicBoundary S)) ⊆
        ⋃ c : ConnectedComponents (intrinsicBoundary S), componentSet c := by
      intro p _
      exact Set.mem_iUnion.mpr ⟨ConnectedComponents.mk p, rfl⟩
    have hsum : ∑ c, d c = 0 :=
      boundary_degree_sum_from_integral_split S T B hB o q hq r G hG hT J hJ Ib hIb
        componentSet (fun c => (D c).manifold) (fun c => (D c).inclusion_smooth)
        (fun c p => ((D c).tangentEquiv p).toLinearMap)
        (fun c => (D c).tangent_differential) (fun c => (D c).orientation) I d hd
        (fun β ξ hξ => integral_component_sum B componentSet (fun c => (D c).isOpen)
          (fun _ => inferInstance) componentSet_pairwiseDisjoint hcover
          (fun c => (D c).manifold) (fun c => (D c).atlas_eq)
          (fun c => (D c).inclusion_smooth) (fun c => (D c).tangentEquiv)
          (fun c => (D c).tangent_differential) (fun c => (D c).orientation) q
          hpres I Ib hI hIb β ξ hξ)
    simpa only [finsum_eq_sum_of_fintype] using hsum

/-- The source's boundary-extension conclusion, with all auxiliary geometry
and integral realizations constructed from the given oriented manifold. -/
theorem boundary_extension :
    Specs.SmoothManifolds.Degree.Properties.boundary_extensionType.{u} := by
  intro n a b W N _ _ _ _ _ S T hT o r G hG
  obtain ⟨B, hB⟩ := (BoundaryOrientations.boundary_orientation S o).1
  obtain ⟨q, hq, _⟩ := (BoundaryOrientations.boundary_orientation S o).2 B hB
  obtain ⟨J, hJ, _⟩ := GlobalIntegrationResults.exists_integral T r
  obtain ⟨D, I, d, hD, hsum⟩ := boundary_degree_sum S T hT B hB o q hq.1 r J hJ G hG
  exact ⟨finite_boundary_components S B, B, hB, q, hq.1, J, hJ, D, I, d, hD, hsum⟩

end SmoothManifolds.DegreeProperties
