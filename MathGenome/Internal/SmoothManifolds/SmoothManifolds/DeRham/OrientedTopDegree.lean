import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.OrientedTopDegree
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.CompactSupportEuclidean
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.CompactSupport
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Stokes
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.LocallyFinite
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Products
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas

/-! The oriented compact-support and compact cases of M11.07.
The integral is the original signed integral of the underlying compact smooth
field. Local compact cohomology is compared with the full Euclidean complex;
finite localization and connectedness then identify all unit-integral classes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped BigOperators
namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData
  DeRhamData MayerVietorisData CompactSupportData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData Set
universe u

section Forms
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} {U : TopologicalSpace.Opens M}

/-- Every compact smooth top form is an actual compact continuous top form. -/
def compactTopForm (D : CompactCalculus K U) (ω : D.complex.Obj n) : CompactTopForm S where
  field := (D.inclusion.map n ω).val
  continuous := StokesResults.continuous_top_of_coefficients C _
    (ExteriorDerivativeResults.regular_continuous C n 0 _
      (ExteriorDerivativeResults.smooth_regular C n (B n) _ 0
        ((K.mem_forms n _).mp (D.inclusion.map n ω).property)))
  compact_support := (CompactSupportResults.inclusion_support D n ω).1

/-- The differential out of top degree is zero, in any full realization. -/
theorem top_closed (D : CompactCalculus K U) (ω : D.complex.Obj n) :
    ω ∈ D.complex.closed n := by
  change D.complex.d n ω = 0
  apply D.injective (n+1)
  apply Subtype.ext
  rw [map_zero]
  funext p
  exact ExteriorAlgebraResults.fields_above_dimension C (n+1) (Nat.lt_succ_self n) _ p

/-- A compact form has a finite decomposition subordinate to any open cover.
The support of each summand is compact in the ambient manifold and contained
in its assigned open set. This uses local finiteness only on the support of
the given form, and does not require the manifold or the cover to be finite. -/
theorem finite_localization {ι : Type*} (D : CompactCalculus K ⊤)
    (V : ι → TopologicalSpace.Opens M) (hcover : ∀ p, ∃ i, p ∈ V i)
    (k : ℕ) (ω : D.complex.Obj k) :
    ∃ (s : Finset ι) (α : ι → D.complex.Obj k),
      ω = ∑ i ∈ s, α i ∧
      ∀ i, sectionSupport (D.inclusion.map k (α i)).val ⊆ V i := by
  classical
  obtain ⟨ρ, hρ, hsub⟩ := exists_smooth_partition S (fun i => (V i : Set M))
    (fun i => (V i).isOpen) hcover
  let μ : ι → K.forms k := fun i =>
    CompactSupportResults.multiplyForm K k (ρ i) (hρ.1 i) (D.inclusion.map k ω)
  have hμ (i : ι) :
      IsCompact (sectionSupport (μ i).val) ∧ sectionSupport (μ i).val ⊆ V i := by
    have hs := CompactSupportResults.support_function_smul_subset (ρ i)
      (D.inclusion.map k ω).val
    exact ⟨(CompactSupportResults.inclusion_support D k ω).1.of_isClosed_subset
      isClosed_closure (hs.trans inter_subset_right),
      (hs.trans inter_subset_left).trans (hsub i)⟩
  have hex (i : ι) : ∃ x, D.inclusion.map k x = μ i :=
    (D.range k (μ i)).mp ⟨(hμ i).1, subset_univ _⟩
  choose α hα using hex
  have hfinite := hρ.2.2.1.finite_nonempty_inter_compact
    (CompactSupportResults.inclusion_support D k ω).1
  let s := hfinite.toFinset
  refine ⟨s, α, ?_, ?_⟩
  · apply D.injective k
    rw [map_sum]
    simp_rw [hα]
    apply Subtype.ext
    have hsumval : (∑ i ∈ s, μ i).val = ∑ i ∈ s, (μ i).val :=
      map_sum (K.forms k).subtype μ s
    rw [hsumval]
    funext p
    rw [Finset.sum_apply]
    change (D.inclusion.map k ω).val p =
      ∑ i ∈ s, ρ i p • (D.inclusion.map k ω).val p
    by_cases hp : (D.inclusion.map k ω).val p = 0
    · simp [hp]
    · have hs : Function.support (fun i => ρ i p) ⊆ (s : Set ι) := by
        intro i hi
        exact hfinite.mem_toFinset.mpr
          ⟨p, subset_closure hi, subset_closure hp⟩
      have hsum : (∑ i ∈ s, ρ i p) = 1 :=
        (finsum_eq_sum_of_support_subset (fun i => ρ i p) hs).symm.trans (hρ.2.2.2 p)
      rw [← Finset.sum_smul, hsum, one_smul]
  · intro i
    rw [hα]
    exact (hμ i).2

end Forms

section Algebra
/-- A degreewise inverse of a bijective map of complexes still commutes with d. -/
def inverseChainMap {A G : Cochain.{u}} (f : ChainMap A G)
    (hf : ∀ k, Function.Bijective (f.map k)) : ChainMap G A where
  map k := (LinearEquiv.ofBijective (f.map k) (hf k)).symm.toLinearMap
  comm k x := by
    apply (hf (k+1)).1
    change f.map (k+1) (A.d k ((LinearEquiv.ofBijective (f.map k) (hf k)).symm x)) =
      f.map (k+1) ((LinearEquiv.ofBijective (f.map (k+1)) (hf (k+1))).symm (G.d k x))
    rw [← f.comm]
    simp

/-- Degreewise bijective maps induce the specified isomorphisms on cohomology. -/
def cohomologyEquiv {A G : Cochain.{u}} (f : ChainMap A G)
    (hf : ∀ k, Function.Bijective (f.map k)) (k : ℕ) : A.H k ≃ₗ[ℝ] G.H k where
  toFun := f.onH k
  invFun := (inverseChainMap f hf).onH k
  left_inv x := by
    obtain ⟨ω, rfl⟩ := A.class_surjective k x
    rw [ChainMap.onH_class, ChainMap.onH_class]
    apply congrArg (A.classOf k)
    apply Subtype.ext
    exact (LinearEquiv.ofBijective (f.map k) (hf k)).symm_apply_apply ω.val
  right_inv x := by
    obtain ⟨ω, rfl⟩ := G.class_surjective k x
    rw [ChainMap.onH_class, ChainMap.onH_class]
    apply congrArg (G.classOf k)
    apply Subtype.ext
    exact (LinearEquiv.ofBijective (f.map k) (hf k)).apply_symm_apply ω.val
  map_add' := map_add (f.onH k)
  map_smul' := map_smul (f.onH k)

end Algebra

/-- This comparison needs compactness alone, with no orientation or boundary
restriction. The inverse is justified by the full range of the realization. -/
theorem compact_comparison_proof :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u} := by
  intro n a M _ _ S C B K D
  have hf (k : ℕ) : Function.Bijective (D.inclusion.map k) := by
    refine ⟨D.injective k, ?_⟩
    intro ω
    exact (D.range k ω).mp ⟨isClosed_closure.isCompact, subset_univ _⟩
  refine ⟨hf, fun k => ⟨cohomologyEquiv D.inclusion hf k, ?_⟩⟩
  intro ω
  rfl

/-- Stokes with the actual empty boundary implies vanishing on compact
exact forms. No connectedness is needed for this direction. -/
theorem derivative_integral_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold (n+1) a M)
    (hb : intrinsicBoundary S = ∅) (o : Orientation S) (C : CotangentBundle S)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (ω : Field S n) (hω : ExteriorDerivativeData.IsRegularField C 1 n ω)
    (hc : IsCompact (sectionSupport ω)) (η : CompactTopForm S)
    (hd : ExteriorDerivativeData.HasExteriorDerivative C ω η.field) : I η = 0 := by
  haveI : IsEmpty (intrinsicBoundary S) := ⟨fun p => by simpa [hb] using p.property⟩
  obtain ⟨⟨T, hT⟩, hor⟩ := BoundaryOrientations.boundary_orientation S o
  obtain ⟨q, hq, _⟩ := hor T hT
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  obtain ⟨J, hJ, _⟩ := GlobalIntegrationResults.exists_integral T q
  let L : (p : intrinsicBoundary S) →
      TangentData.TangentSpace T p →ₗ[ℝ] TangentData.TangentSpace S p.val :=
    fun p => isEmptyElim p
  have hL : ∀ p, DifferentialData.IsDifferential T S Subtype.val p (L p) :=
    fun p => isEmptyElim p
  obtain ⟨ζ, β, hζ, _, _, he⟩ := StokesResults.stokes S C T A hT o q hq.1
    L hL I J hI hJ ω hω hc
  have hfield : ζ.field = η.field :=
    ExteriorDerivativeResults.derivative_unique C n ω ζ.field η.field hζ hd
  have heq : ζ = η := by cases ζ; cases η; cases hfield; rfl
  rw [← heq, he]
  exact StokesResults.empty_boundary_integral S T q J hJ hb β

section Integral
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} (D : CompactCalculus K ⊤)
  (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)

/-- Integration on compact smooth top forms is linear through their actual
field inclusion, independent of the realization of the compact complex. -/
def integralLinear : D.complex.Obj n →ₗ[ℝ] ℝ where
  toFun ω := I (compactTopForm D ω)
  map_add' α β := hI.1 _ _ _ (by
    change (D.inclusion.map n (α+β)).val = _
    simp only [map_add]
    rfl)
  map_smul' r α := by
    exact hI.2.1 r _ _ (by
      change (D.inclusion.map n (r • α)).val = _
      simp only [map_smul]
      rfl)

theorem exact_integral_zero (hb : intrinsicBoundary S = ∅)
    (ω : D.complex.Obj n) (hω : ω ∈ D.complex.exact n) :
    integralLinear D o I hI ω = 0 := by
  cases n with
  | zero =>
    have hz : ω = 0 := hω
    rw [hz, map_zero]
  | succ n =>
    obtain ⟨β, hβ⟩ := hω
    apply derivative_integral_zero S hb o C I hI (D.inclusion.map n β).val
      (ExteriorDerivativeResults.smooth_regular C n (B n) _ 1
        ((K.mem_forms n _).mp (D.inclusion.map n β).property))
      (CompactSupportResults.inclusion_support D n β).1 (compactTopForm D ω)
    have hd := K.coordinates n (D.inclusion.map n β).val
      ((K.mem_forms n _).mp (D.inclusion.map n β).property)
    change ExteriorDerivativeData.HasExteriorDerivative C
      (D.inclusion.map n β).val (K.d n (D.inclusion.map n β)).val at hd
    have hcomm : K.d n (D.inclusion.map n β) = D.inclusion.map (n+1) ω := by
      exact (D.inclusion.comm n β).trans (congrArg (D.inclusion.map (n+1)) hβ)
    have hefield := congrArg (fun x : K.forms (n+1) => x.val) hcomm
    exact (congrArg (fun ζ : Field S (n+1) =>
      ExteriorDerivativeData.HasExteriorDerivative C (D.inclusion.map n β).val ζ)
      hefield).mp hd

/-- Integration descends through the actual quotient by compact boundaries.
Bijectivity is the separate local-to-global part of the theorem. -/
def cohomologyIntegral (hb : intrinsicBoundary S = ∅) : D.Cohomology n →ₗ[ℝ] ℝ :=
  (D.complex.boundaries n).liftQ
    ((integralLinear D o I hI).comp (D.complex.closed n).subtype) (by
      intro ω hω
      exact exact_integral_zero D o I hI hb ω.val hω)

@[simp] theorem cohomologyIntegral_class (hb : intrinsicBoundary S = ∅)
    (ω : D.complex.closed n) :
    cohomologyIntegral D o I hI hb (D.complex.classOf n ω) =
      I (compactTopForm D ω.val) := rfl

end Integral

section LocalUnits
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M}

/-- With empty intrinsic boundary, a compact top form supported in one chart
has a continuous ambient signed coefficient. Compact support controls the
artificial chart edge; empty boundary puts its coordinate support in the
interior of the model, including for half-space presentations. -/
theorem signedCoefficient_continuous (hb : intrinsicBoundary S = ∅)
    (s : SignedCharts S) (L : TangentBundleData.FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (η : CompactTopForm S) (hη : sectionSupport η.field ⊆ c.source) :
    Continuous (signedCoordinateCoefficient s L c hc η.field) := by
  have hmodel : ContinuousOn (signedCoordinateCoefficient s L c hc η.field)
      (modelSet n a) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert LocalIntegrationResults.modelSignedCoefficient_continuous s L c hc η hη using 1
    funext z
    simp [signedCoordinateCoefficient, extendModel, z.property]
  obtain ⟨hcompact, hsupport⟩ :=
    LocalIntegrationResults.signedCoefficient_compact_container s L c hc η hη
  apply continuous_of_tsupport
  intro z hz
  have hz' := (closure_minimal hsupport hcompact.isClosed) hz
  obtain ⟨p, hp, rfl⟩ := hz'
  have hpinterior : (c p).val ∈ interior (modelSet n a) := by
    by_contra hn
    have hface := (mem_modelFace_iff_not_mem_interior (c p)).mpr hn
    have hboundary : p ∈ intrinsicBoundary S := ⟨c, hc, hη hp, hface⟩
    simpa [hb] using hboundary
  exact hmodel.continuousAt (mem_interior_iff_mem_nhds.mp hpinterior)

/-- A positive top form has strictly positive signed coefficient in every
oriented chart, with the sign attached to the coordinate convention. -/
theorem signed_topCoefficient_pos (s : SignedCharts S) (o : Orientation S)
    (hs : RepresentsSignedCharts o.val s) (L : TangentBundleData.FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S n) (hω : IsPositiveTopForm o.val ω) (p : c.source) :
    0 < signValue (s.sign c hc p) *
      FormPullbackData.topCoefficient L c hc p.val p.property ω := by
  have h := hω p.val _ (hs L c hc p)
  have hv : CovectorData.coordinateVector L c hc p.val p.property =
      fun j => (L.equiv c hc p.val p.property).symm ((Pi.basisFun ℝ (Fin n)) j) := by
    funext j
    simp [CovectorData.coordinateVector]
  simpa [pairing, OrientationData.coordinateVector, FormPullbackData.topCoefficient,
    evaluate, hv, mul_comm] using h

variable {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} (D : CompactCalculus K ⊤)
  (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)

/-- Every nonempty open set contains a compact smooth top form of integral
one. This is a geometric construction using a positive top form and a smooth
bump, and requires no cohomology calculation or connectedness assumption. -/
theorem unit_integral_in_open (hb : intrinsicBoundary S = ∅)
    (W : TopologicalSpace.Opens M) (hW : (W : Set M).Nonempty) :
    ∃ β : D.complex.Obj n, sectionSupport (D.inclusion.map n β).val ⊆ W ∧
      integralLinear D o I hI β = 1 := by
  classical
  obtain ⟨p, hp⟩ := hW
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨ω, hωpos⟩ := (OrientationResults.positive_top_form S C (B n) o.val).mp o.property
  obtain ⟨f, hf, hf01, hf1, hfsupport, hfcompact⟩ :=
    exists_local_bump S p ((W : Set M) ∩ c.source) (W.isOpen.inter c.open_source) ⟨hp, hpc⟩
  let μ := CompactSupportResults.multiplyForm K n f hf
    ⟨ω.val.field, (K.mem_forms n _).mpr ω.val.smooth⟩
  have hμ : sectionSupport μ.val ⊆ sectionSupport f :=
    (CompactSupportResults.support_function_smul_subset f ω.val.field).trans inter_subset_left
  obtain ⟨α, hα⟩ := (D.range n μ).mp
    ⟨hfcompact.of_isClosed_subset isClosed_closure hμ, subset_univ _⟩
  let η := compactTopForm D α
  have hη : η.field = fun q => f q • ω.val.field q :=
    congrArg (fun ζ : K.forms n => ζ.val) hα
  have hηsource : sectionSupport η.field ⊆ c.source := by
    change sectionSupport (D.inclusion.map n α).val ⊆ c.source
    rw [hα]
    exact hμ.trans (hfsupport.trans inter_subset_right)
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  let L := C.tangent.fiberCoordinates
  let g := signedCoordinateCoefficient s L c hc η.field
  have hpos (q : c.source) :
      0 < signValue (s.sign c hc q) *
        FormPullbackData.topCoefficient L c hc q.val q.property ω.val.field :=
    signed_topCoefficient_pos s o hs L c hc ω.val.field hωpos q
  have hnonneg : 0 ≤ g := by
    intro z
    change 0 ≤ signedCoordinateCoefficient s L c hc η.field z
    by_cases hz : g z = 0
    · exact hz.ge
    · obtain ⟨q, _, hqc, heq⟩ :=
        LocalIntegrationResults.signedCoefficient_nonzero s L c hc η.field z hz
      rw [← heq, LocalIntegrationResults.signedCoefficient_at s L c hc η.field ⟨q, hqc⟩,
        hη, GlobalIntegrationResults.topCoefficient_weight]
      have h := mul_nonneg (hf01 q).1 (hpos ⟨q, hqc⟩).le
      simpa only [mul_left_comm] using h
  have hgp : g (c p).val ≠ 0 := by
    dsimp [g]
    rw [LocalIntegrationResults.signedCoefficient_at s L c hc η.field ⟨p, hpc⟩,
      hη, GlobalIntegrationResults.topCoefficient_weight, hf1.eq_of_nhds, one_mul]
    exact (hpos ⟨p, hpc⟩).ne'
  have hJ : 0 < integralLinear D o I hI α := by
    change 0 < I η
    rw [hI.2.2 s hs L c hc η hηsource]
    exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
      (signedCoefficient_continuous hb s L c hc η hηsource)
      (LocalIntegrationResults.integrable S s L c hc η hηsource) hnonneg hgp
  refine ⟨(integralLinear D o I hI α)⁻¹ • α, ?_, ?_⟩
  · rw [map_smul]
    change sectionSupport ((integralLinear D o I hI α)⁻¹ •
      (D.inclusion.map n α).val) ⊆ W
    have hs : sectionSupport (D.inclusion.map n α).val ⊆ W := by
      rw [hα]
      exact hμ.trans (hfsupport.trans inter_subset_left)
    exact (CompactSupportResults.support_smul_subset
      (integralLinear D o I hI α)⁻¹ (D.inclusion.map n α).val).trans hs
  · rw [map_smul]
    exact inv_mul_cancel₀ hJ.ne'

end LocalUnits

section IntegralSurjective
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [Nonempty M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} (D : CompactCalculus K ⊤)
  (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)

/-- Integration is onto, by a normalized compact smooth form in an arbitrary
nonempty coordinate neighborhood. Connectedness is not needed. -/
theorem cohomologyIntegral_surjective (hb : intrinsicBoundary S = ∅) :
    Function.Surjective (cohomologyIntegral D o I hI hb) := by
  obtain ⟨α, _, hα⟩ := unit_integral_in_open D o I hI hb ⊤ Set.univ_nonempty
  let z := D.complex.classOf n ⟨α, top_closed D α⟩
  have hz : cohomologyIntegral D o I hI hb z = 1 := hα
  intro r
  refine ⟨r • z, ?_⟩
  simp only [map_smul, hz, smul_eq_mul, mul_one]

end IntegralSurjective



/-- The zero-dimensional assertion retains the orientation sign in evaluation. -/
theorem zero_dimension_proof :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u} := by
  intro a M _ _ S o C B K D I hI
  haveI := LocalIntegrationResults.zero_manifold_discrete S
  haveI : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
  refine ⟨inferInstance, ?_⟩
  intro ω p
  let η := compactTopForm D ω
  refine ⟨η, rfl, ?_, ?_⟩
  · rw [GlobalIntegrationResults.zero_dimension S o I hI η]
    unfold zeroIntegral
    exact finsum_eq_single _ p (fun q hq => False.elim (hq (Subsingleton.elim q p)))
  · change ω = 0 ↔ (D.inclusion.map 0 ω).val = 0
    constructor
    · rintro rfl
      exact congrArg (fun x : K.forms 0 => x.val) ((D.inclusion.map 0).map_zero)
    · intro h
      apply D.injective 0
      exact (Subtype.ext h : D.inclusion.map 0 ω = (0 : K.forms 0)).trans
        (D.inclusion.map 0).map_zero.symm

/-- A common value on intersecting open sets propagates across a connected
space. This supplies the connectedness step for local unit-integral classes;
it does not assume finite covers or Euclidean coordinates on the whole space. -/
theorem constant_on_open_cover {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {ι Q : Type*} (V : ι → Set X) (hopen : ∀ i, IsOpen (V i))
    (hcover : ∀ p, ∃ i, p ∈ V i) (q : ι → Q)
    (hoverlap : ∀ i j, (V i ∩ V j).Nonempty → q i = q j)
    {i j : ι} (hi : (V i).Nonempty) (hj : (V j).Nonempty) : q i = q j := by
  classical
  let chosen : X → ι := fun p => (hcover p).choose
  have hchosen (p : X) : p ∈ V (chosen p) := (hcover p).choose_spec
  let f : X → Q := fun p => q (chosen p)
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro p
    refine ⟨V (chosen p), hopen _, hchosen p, ?_⟩
    intro x hx
    exact hoverlap _ _ ⟨x, hchosen x, hx⟩
  obtain ⟨x, hx⟩ := hi
  obtain ⟨y, hy⟩ := hj
  exact (hoverlap i (chosen x) ⟨x, hx, hchosen x⟩).trans
    ((hf.apply_eq_of_preconnectedSpace x y).trans
      (hoverlap (chosen y) j ⟨y, hchosen y, hy⟩))


/-- Signed scalar evaluation is an isomorphism on locally constant functions
on a connected space; the sign is its own inverse. -/
def signedEvaluationEquiv {a : ModelKind} {M : Type u} [TopologicalSpace M]
    [ConnectedSpace M] {S : SmoothManifold 0 a M} (o : Orientation S) (p : M) :
    LocallyConstant M ℝ ≃ₗ[ℝ] ℝ where
  toFun f := zeroSign o p * f p
  invFun r := LocallyConstant.const M (zeroSign o p * r)
  left_inv f := LocallyConstant.ext (fun x => by
    change zeroSign o p * (zeroSign o p * f p) = f x
    have h : f p = f x := f.isLocallyConstant.apply_eq_of_preconnectedSpace p x
    rw [h]
    unfold zeroSign
    split <;> simp)
  right_inv r := by
    change zeroSign o p * (zeroSign o p * r) = r
    unfold zeroSign
    split <;> simp
  map_add' f g := mul_add _ _ _
  map_smul' r f := by
    change zeroSign o p * (r * f p) = r * (zeroSign o p * f p)
    ring

/-- The complete integration isomorphism in dimension zero, with the original
orientation sign, not merely an abstract one-dimensionality assertion. -/
theorem zero_top_degree {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] (S : SmoothManifold 0 a M)
    (o : Orientation S) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :
    ∃ e : D.Cohomology 0 ≃ₗ[ℝ] ℝ, ∀ ω : D.complex.closed 0,
      ∃ η : CompactTopForm S, η.field = (D.inclusion.map 0 ω.val).val ∧
        e (D.complex.classOf 0 ω) = I η := by
  haveI := LocalIntegrationResults.zero_manifold_discrete S
  haveI : Subsingleton M := subsingleton_of_preconnected_totallyDisconnected
  haveI : CompactSpace M := inferInstance
  obtain ⟨_, hcmp⟩ := compact_comparison_proof S C B K D
  obtain ⟨eD, hD⟩ := hcmp 0
  obtain ⟨eH, hH⟩ := DeRhamResults.h0_locally_constant K
  let p : M := Classical.arbitrary M
  refine ⟨eD.trans (eH.trans (signedEvaluationEquiv o p)), ?_⟩
  intro ω
  obtain ⟨η, hη, hvalue, _⟩ := (zero_dimension_proof S o C B K D I hI).2 ω.val p
  refine ⟨η, hη, ?_⟩
  change zeroSign o p * eH (eD (D.complex.classOf 0 ω)) p = I η
  rw [hD ω]
  have heval : eH (K.classOf 0 (D.inclusion.onClosed 0 ω)) p =
      zeroCoefficient (D.inclusion.map 0 ω.val).val p := hH (D.inclusion.onClosed 0 ω) p
  rw [heval]
  rw [hvalue, hη]

/-- Once integration is injective on cohomology, the compact primitive
criterion follows from the actual quotient, including its degree-zero endpoint. -/
theorem exact_iff_of_top_degree
    (htop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u}) :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u} := by
  intro n a M _ _ S hb o C B K D I hI ω
  let α : D.complex.closed n := ⟨ω, top_closed D ω⟩
  obtain ⟨e, he⟩ := htop S hb o C B K D I hI
  obtain ⟨η, hη, heη⟩ := he α
  refine ⟨η, hη, ?_⟩
  constructor
  · intro hω
    have hz : D.complex.classOf n α = 0 := (D.complex.class_zero_iff n α).mpr hω
    rw [← heη, hz, map_zero]
  · intro hω
    apply (D.complex.class_zero_iff n α).mp
    apply e.injective
    rw [heη, hω, map_zero]

set_option maxHeartbeats 5000000 in
/-- The compact ordinary case is a consequence of the full compact-complex
comparison and the compact-support theorem, with the representative formula. -/
theorem compact_top_degree_of_top_degree
    (htop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u}) :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u} := by
  intro n a M _ _ _ S hb o C B K I hI
  obtain ⟨D⟩ := CompactSupportResults.open_complex_exists K ⊤
  obtain ⟨hf, hcmp⟩ := compact_comparison_proof S C B K D
  let eD := (hcmp n).choose
  have hD := (hcmp n).choose_spec
  have htop' := htop S hb o C B K D I hI
  let eC := htop'.choose
  have hC := htop'.choose_spec
  refine ⟨eD.symm.trans eC, ?_⟩
  intro ω
  let α : D.complex.closed n := (inverseChainMap D.inclusion hf).onClosed n ω
  have hα : D.inclusion.onClosed n α = ω := by
    apply Subtype.ext
    exact (LinearEquiv.ofBijective (D.inclusion.map n) (hf n)).apply_symm_apply ω.val
  obtain ⟨η, hη, heη⟩ := hC α
  have hfield : (D.inclusion.map n α.val).val = ω.val.val :=
    congrArg (fun x : K.closed n => x.val.val) hα
  refine ⟨η, hη.trans hfield, ?_⟩
  have hclass : eD (D.complex.classOf n α) = K.classOf n ω :=
    (hD α).trans (congrArg (K.classOf n) hα)
  change eC (eD.symm (K.classOf n ω)) = I η
  rw [← hclass, eD.symm_apply_apply]
  exact heη

end SmoothManifolds.OrientedTopDegreeResults


set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BoundaryData Set
universe u

/-- Empty intrinsic boundary puts every smooth coordinate image in the
ambient interior of its model, even for a half-space presentation. -/
theorem chart_target_interior {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    Subtype.val '' c.target ⊆ interior (modelSet n a) := by
  rintro z ⟨x, hx, rfl⟩
  by_contra h
  have hface := (mem_modelFace_iff_not_mem_interior x).mpr h
  have hbound : c.symm x ∈ intrinsicBoundary S := by
    refine ⟨c, hc, c.map_target hx, ?_⟩
    simpa only [c.right_inv hx] using hface
  simpa [hb] using hbound

/-- Coordinate targets of a boundary-free manifold are genuinely open in
Euclidean space, rather than only relatively open in a half-space. -/
theorem chart_target_isOpen {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    IsOpen (Subtype.val '' c.target : Set (Euclidean n)) := by
  obtain ⟨V, hV, htarget⟩ := c.open_target.image_val
  have heq : Subtype.val '' c.target = V ∩ interior (modelSet n a) := by
    apply subset_antisymm
    · intro z hz
      exact ⟨((Set.ext_iff.mp htarget z).mp hz).1, chart_target_interior hb c hc hz⟩
    · intro z hz
      rw [htarget]
      exact ⟨hz.1, interior_subset hz.2⟩
  rw [heq]
  exact hV.inter isOpen_interior

/-- A smooth chart on a boundary-free manifold can be viewed as an ordinary
open partial homeomorphism to the ambient Euclidean space. Its image and
forward coordinates are unchanged. -/
def ambientChart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) : OpenPartialHomeomorph M (Euclidean n) := by
  classical
  let q₀ : ModelSpace n a := ⟨0, by
    cases a with
    | euclidean => trivial
    | halfSpace => cases n <;> simp [modelSet, ModelData.modelSet, halfSpaceSet]⟩
  let proj : Euclidean n → ModelSpace n a := fun z =>
    if hz : z ∈ modelSet n a then ⟨z, hz⟩ else q₀
  have hproj (z : ModelSpace n a) : proj z.val = z := by
    simp only [proj, dite_eq_left z.property]
  have hprojcont : ContinuousOn proj (Subtype.val '' c.target) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    let g : (Subtype.val '' c.target : Set (Euclidean n)) → ModelSpace n a :=
      fun z => ⟨z.val, by obtain ⟨x, _, hx⟩ := z.property; exact hx ▸ x.property⟩
    have hg : Continuous g := continuous_subtype_val.subtype_mk _
    convert hg using 1
    funext z
    dsimp [g, proj]
    rw [dite_eq_left (by obtain ⟨x, _, hx⟩ := z.property; exact hx ▸ x.property)]
  refine {
    toFun := fun p => (c p).val
    invFun := fun z => c.symm (proj z)
    source := c.source
    target := Subtype.val '' c.target
    map_source' := fun p hp => ⟨c p, c.map_source hp, rfl⟩
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := c.open_source
    open_target := chart_target_isOpen hb c hc
    continuousOn_toFun := continuous_subtype_val.comp_continuousOn c.continuousOn
    continuousOn_invFun := c.continuousOn_symm.comp hprojcont ?_ }
  · rintro z ⟨x, hx, rfl⟩
    rw [hproj]
    exact c.map_target hx
  · intro p hp
    rw [hproj, c.left_inv hp]
  · rintro z ⟨x, hx, rfl⟩
    rw [hproj, c.right_inv hx]
  · rintro z ⟨x, hx, rfl⟩
    rw [hproj]
    exact hx

end SmoothManifolds.OrientedTopDegreeResults

namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BoundaryData Set
universe u

@[simp] theorem ambientChart_source {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) : (ambientChart hb c hc).source = c.source := rfl

@[simp] theorem ambientChart_target {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) :
    (ambientChart hb c hc).target = Subtype.val '' c.target := rfl

@[simp] theorem ambientChart_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (p : M) :
    ambientChart hb c hc p = (c p).val := rfl

end SmoothManifolds.OrientedTopDegreeResults


set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults
open Set Metric

/-- Reparametrize a coordinate ball by the whole inner product space. -/
def radialChart {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : OpenPartialHomeomorph X E) (z : E) (r : ℝ) :
    OpenPartialHomeomorph X E := c.trans (OpenPartialHomeomorph.univBall z r).symm

theorem radialChart_target {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : OpenPartialHomeomorph X E) (z : E) {r : ℝ}
    (hr : 0 < r) (hsub : ball z r ⊆ c.target) :
    (radialChart c z r).target = univ := by
  apply Set.eq_univ_of_forall
  intro w
  change w ∈ (OpenPartialHomeomorph.univBall z r).source ∩
    (OpenPartialHomeomorph.univBall z r) ⁻¹' c.target
  refine ⟨by simp, hsub ?_⟩
  rw [← OpenPartialHomeomorph.univBall_target z hr]
  exact (OpenPartialHomeomorph.univBall z r).map_source (by simp)

/-- Inverse coordinates of the new chart are the smooth radial map. This
identity is on the whole target, not merely on a neighborhood of its center. -/
theorem radialChart_inverse_coordinates {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : OpenPartialHomeomorph X E) (z : E) {r : ℝ}
    (hr : 0 < r) (hsub : ball z r ⊆ c.target) (w : E) :
    c ((radialChart c z r).symm w) = OpenPartialHomeomorph.univBall z r w := by
  change c (c.symm (OpenPartialHomeomorph.univBall z r w)) = _
  apply c.right_inv
  apply hsub
  rw [← OpenPartialHomeomorph.univBall_target z hr]
  exact (OpenPartialHomeomorph.univBall z r).map_source (by simp)

theorem radialChart_inverse_contDiff {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : OpenPartialHomeomorph X E) (z : E) {r : ℝ}
    (hr : 0 < r) (hsub : ball z r ⊆ c.target) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w => c ((radialChart c z r).symm w)) := by
  simp_rw [radialChart_inverse_coordinates c z hr hsub]
  exact OpenPartialHomeomorph.contDiff_univBall

/-- Every point of a chart has a smaller chart inside any prescribed open
neighborhood whose coordinate image is the entire inner product space.
The reparametrization uses the smooth radial ball map and its smooth inverse. -/
theorem exists_radialChart {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (c : OpenPartialHomeomorph X E) (p : X)
    (hp : p ∈ c.source) (W : Set X) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ d : OpenPartialHomeomorph X E,
      p ∈ d.source ∧ d.source ⊆ W ∧ d.target = univ := by
  let c' := c.restrOpen W hW
  have hp' : p ∈ c'.source := ⟨hp, hpW⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp c'.open_target (c' p) (c'.map_source hp')
  refine ⟨radialChart c' (c' p) r, ?_, ?_, radialChart_target c' (c' p) hr hsub⟩
  · change p ∈ c'.source ∩ c' ⁻¹' (OpenPartialHomeomorph.univBall (c' p) r).target
    refine ⟨hp', ?_⟩
    rw [OpenPartialHomeomorph.univBall_target (c' p) hr]
    exact mem_ball_self hr
  · intro q hq
    exact hq.1.2

end SmoothManifolds.OrientedTopDegreeResults

namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BoundaryData Set
universe u

/-- The boundary-free hypothesis supplies Euclidean neighborhoods even when
the manifold is presented using the half-space model. Radial coordinates make
the image all of Euclidean space, with source in the prescribed neighborhood. -/
theorem exists_euclidean_neighborhood {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (hb : intrinsicBoundary S = ∅) (p : M) (W : Set M)
    (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ e : OpenPartialHomeomorph M (Euclidean n),
      p ∈ e.source ∧ e.source ⊆ W ∧ e.target = univ := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  let L : Euclidean n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  let c₂ := (ambientChart hb c hc).transHomeomorph L.toHomeomorph
  have hpc₂ : p ∈ c₂.source := hpc
  obtain ⟨d, hpd, hdW, hdt⟩ := exists_radialChart c₂ p hpc₂ W hW hpW
  refine ⟨d.transHomeomorph L.symm.toHomeomorph, hpd, hdW, ?_⟩
  change L ⁻¹' d.target = univ
  rw [hdt, Set.preimage_univ]

end SmoothManifolds.OrientedTopDegreeResults

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData EuclideanCompactData Set
universe u

/-- A chart with full Euclidean image gives a genuine Euclidean manifold on
its source. A local smooth coordinate test in the original manifold is enough
to identify the inclusion as a smooth map, including across model kinds. -/
theorem presentation_of_ambient_chart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (e : OpenPartialHomeomorph M (Euclidean n)) (ht : e.target = univ)
    (hne : Nonempty e.source)
    (hincl : ∀ p : e.source, ∃ c ∈ S.smoothStructure.val,
      p.val ∈ c.source ∧ LocalCoordinateExtension (⊤ : ℕ∞)
        e (fun q => (c q).val) p.val) :
    ∃ P : Presentation n e.source,
      IsSmoothMap P.manifold S Subtype.val ∧
      (∀ p : e.source, (P.chart p).val = e p.val) := by
  let L : Euclidean n ≃ₜ ModelSpace n .euclidean := (Homeomorph.Set.univ _).symm
  let d : ModelChart n .euclidean e.source :=
    (e.subtypeRestr (s := ⟨e.source, e.open_source⟩) hne).transHomeomorph L
  have hds : d.source = univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.transHomeomorph_source,
      OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    change (p.val ∈ e.source) ↔ p ∈ (univ : Set e.source)
    simp only [mem_univ, iff_true]
    exact p.property
  have hdt : d.target = univ := by
    apply Set.eq_univ_of_forall
    intro z
    change L.symm z ∈ (e.subtypeRestr (s := ⟨e.source, e.open_source⟩) hne).target
    have hz : L.symm z ∈ e.target := ht ▸ mem_univ _
    have hp : e.symm (L.symm z) ∈ e.source := e.map_target hz
    have hdmap := e.map_subtype_source (s := ⟨e.source, e.open_source⟩) hne
      (x := (⟨e.symm (L.symm z), hp⟩ : e.source)) hp
    simpa only [e.right_inv hz] using hdmap
  have hA : IsContDiffAtlas (⊤ : ℕ∞) ({d} : Set (ModelChart n .euclidean e.source)) := by
    refine ⟨fun p => ⟨d, mem_singleton _, hds ▸ mem_univ _⟩, ?_⟩
    intro f hf g hg
    rw [mem_singleton_iff] at hf hg
    subst f
    subst g
    apply contDiffCompatible_of_germs
    · intro p _ _
      exact LocalCoordinateExtension.self _ _ p
    · intro p _ _
      exact LocalCoordinateExtension.self _ _ p
  letI := S.topologicalManifold.hausdorff
  letI := S.topologicalManifold.secondCountable
  let R : SmoothManifold n .euclidean e.source := {
    topologicalManifold := ⟨inferInstance, inferInstance, {d}, hA.1⟩
    smoothStructure := ⟨maximalExtension (⊤ : ℕ∞) {d}, maximalExtension_isMaximal hA⟩ }
  have hd : d ∈ R.smoothStructure.val := subset_maximalExtension hA (mem_singleton _)
  refine ⟨⟨R, d, hd, hds, hdt⟩, ?_, fun p => rfl⟩
  intro p
  obtain ⟨c, hc, hpc, htest⟩ := hincl p
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    R.smoothStructure.property.1 S.smoothStructure.property.1 Subtype.val p).mpr
  refine ⟨continuousAt_subtype_val, d, hd, c, hc, hds ▸ mem_univ _, hpc, ?_⟩
  exact LocalCoordinateExtension.precomp htest continuousAt_subtype_val rfl

end SmoothManifolds.OrientedTopDegreeResults.LocalTransport


namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData BoundaryData EuclideanCompactData Set Filter
open scoped Topology
universe u

/-- Explicit smooth forward coordinates identify the original restricted
atlas smoothly with the local Euclidean presentation. -/
theorem reverse_chart_map_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (e : OpenPartialHomeomorph M (Euclidean n))
    (P : Presentation n e.source)
    (hchart : ∀ q : e.source, (P.chart q).val = e q.val)
    (hforward : ∀ p : e.source, ∃ c ∈ S.smoothStructure.val,
      p.val ∈ c.source ∧ LocalCoordinateExtension (⊤ : ℕ∞)
        (fun q => (c q).val) e p.val) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val e.source e.open_source)
      P.manifold.smoothStructure.val id := by
  intro p
  obtain ⟨c, hc, hpc, htest⟩ := hforward p
  let d := c.subtypeRestr (s := ⟨e.source, e.open_source⟩) ⟨p⟩
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    (openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 _ _)
    P.manifold.smoothStructure.property.1 id p).mpr
  refine ⟨continuousAt_id, d, ⟨⟨p⟩, c, hc, rfl⟩, P.chart, P.chart_mem,
    ?_, P.source_eq ▸ mem_univ _, ?_⟩
  · simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hpc
  · change LocalCoordinateExtension (⊤ : ℕ∞)
      (fun q : e.source => (c q.val).val) (fun q : e.source => (P.chart q).val) p
    simpa only [Function.comp_def, hchart] using
      (LocalCoordinateExtension.precomp htest continuousAt_subtype_val rfl)

/-- Every point has a genuine local Euclidean presentation inside any chosen
open neighborhood. Its inclusion into the original manifold is smooth for
either permitted model, with no extra boundary or compactness assumption. -/
theorem euclidean_presentation_neighborhood {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (hb : intrinsicBoundary S = ∅) (p : M) (W : Set M)
    (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ e : OpenPartialHomeomorph M (Euclidean n),
      p ∈ e.source ∧ e.source ⊆ W ∧ e.target = univ ∧
      ∃ P : Presentation n e.source,
        IsSmoothMap P.manifold S Subtype.val ∧
        (∀ q : e.source, (P.chart q).val = e q.val) ∧
        ManifoldSmooth (openSubsetAtlas S.smoothStructure.val e.source e.open_source)
          P.manifold.smoothStructure.val id := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  let L : Euclidean n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm
  let c₂ := (ambientChart hb c hc).transHomeomorph L.toHomeomorph
  let c' := c₂.restrOpen W hW
  have hp' : p ∈ c'.source := ⟨hpc, hpW⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp c'.open_target (c' p) (c'.map_source hp')
  let d := radialChart c' (c' p) r
  let e := d.transHomeomorph L.symm.toHomeomorph
  have hpd : p ∈ d.source := by
    refine ⟨hp', ?_⟩
    change c' p ∈ (OpenPartialHomeomorph.univBall (c' p) r).target
    rw [OpenPartialHomeomorph.univBall_target (c' p) hr]
    exact Metric.mem_ball_self hr
  have het : e.target = univ := by
    change L ⁻¹' d.target = univ
    rw [radialChart_target c' (c' p) hr hsub, Set.preimage_univ]
  have hWsource : e.source ⊆ W := fun _ hx => hx.1.2
  let H : Euclidean n → Euclidean n := fun z =>
    L.symm (OpenPartialHomeomorph.univBall (c' p) r (L z))
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    L.symm.contDiff.comp (OpenPartialHomeomorph.contDiff_univBall.comp L.contDiff)
  have hcoords (q : M) (hq : q ∈ e.source) : H (e q) = (c q).val := by
    have hi := radialChart_inverse_coordinates c' (c' p) hr hsub (d q)
    change c' (d.symm (d q)) = _ at hi
    rw [d.left_inv hq] at hi
    change L.symm (OpenPartialHomeomorph.univBall (c' p) r (L (L.symm (d q)))) = _
    rw [L.apply_symm_apply, ← hi]
    exact L.symm_apply_apply ((c q).val)
  have hincl : ∀ q : e.source, ∃ c ∈ S.smoothStructure.val,
      q.val ∈ c.source ∧ LocalCoordinateExtension (⊤ : ℕ∞)
        e (fun x => (c x).val) q.val := by
    intro q
    refine ⟨c, hc, q.property.1.1, univ, isOpen_univ, mem_univ _, H, hH.contDiffOn, ?_⟩
    filter_upwards [e.open_source.mem_nhds q.property] with x hx
    exact hcoords x hx
  obtain ⟨P, hi, hchart⟩ := presentation_of_ambient_chart S e het ⟨⟨p, hpd⟩⟩ hincl
  let V : Set (Euclidean n) := L ⁻¹' Metric.ball (c' p) r
  let G : Euclidean n → Euclidean n := fun z =>
    L.symm ((OpenPartialHomeomorph.univBall (c' p) r).symm (L z))
  have hV : IsOpen V := Metric.isOpen_ball.preimage L.continuous
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G V := by
    exact L.symm.contDiff.comp_contDiffOn
      (OpenPartialHomeomorph.contDiffOn_univBall_symm.comp L.contDiff.contDiffOn
        (fun z hz => hz))
  have hforward : ∀ q : e.source, ∃ c ∈ S.smoothStructure.val,
      q.val ∈ c.source ∧ LocalCoordinateExtension (⊤ : ℕ∞)
        (fun x => (c x).val) e q.val := by
    intro q
    have hqV : (c q.val).val ∈ V := by
      change c' q.val ∈ Metric.ball (c' p) r
      have hq := q.property.2
      change c' q.val ∈ (OpenPartialHomeomorph.univBall (c' p) r).target at hq
      simpa only [OpenPartialHomeomorph.univBall_target (c' p) hr] using hq
    refine ⟨c, hc, q.property.1.1, V, hV, hqV, G, hG, ?_⟩
    exact Filter.Eventually.of_forall (fun x => rfl)
  exact ⟨e, hpd, hWsource, het, P, hi, hchart,
    reverse_chart_map_smooth S e P hchart hforward⟩

end SmoothManifolds.OrientedTopDegreeResults.LocalTransport

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData MayerVietorisData CompactSupportData
  EuclideanCompactData Set
universe u

/-- A chart onto the whole model is a Euclidean presentation of its source,
with the actual restricted smooth structure and a smooth ambient inclusion. -/
theorem presentation_of_chart {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (c : ModelChart n .euclidean M)
    (hc : c ∈ S.smoothStructure.val) (ht : c.target = Set.univ)
    (hne : Nonempty c.source) :
    ∃ P : Presentation n c.source,
      IsSmoothMap P.manifold S Subtype.val ∧
      (∀ p : c.source, P.chart p = c p.val) := by
  obtain ⟨R, _, hR, hi⟩ := exists_openSubset_smoothManifold S c.source c.open_source
  let d : ModelChart n .euclidean c.source :=
    c.subtypeRestr (s := ⟨c.source, c.open_source⟩) hne
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 _ _)
      ⟨hne, c, hc, rfl⟩
  have hds : d.source = Set.univ := by
    ext p
    simp only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage, mem_univ,
      iff_true]
    exact p.property
  have hdt : d.target = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ c.target := ht ▸ Set.mem_univ z
    have hp : c.symm z ∈ c.source := c.map_target hz
    have hdmap := c.map_subtype_source (s := ⟨c.source, c.open_source⟩) hne
      (x := (⟨c.symm z, hp⟩ : c.source)) hp
    simpa only [c.right_inv hz] using hdmap
  exact ⟨⟨R, d, hd, hds, hdt⟩, hi, fun p => rfl⟩

/-- The assumed full Euclidean calculation already supplies a normalized
compact top representative, in any full compact realization. -/
theorem unit_integral
    (hcalc : Specs.SmoothManifolds.DeRham.CompactSupportEuclidean.calculationType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M] (P : Presentation n M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤) :
    ∃ ω : D.complex.closed n, totalIntegral P D ω.val = 1 := by
  obtain ⟨_, _, ⟨e, he⟩, _⟩ := hcalc P C B K D
  obtain ⟨ω, hω⟩ := Submodule.mkQ_surjective (D.complex.boundaries n) (e.symm 1)
  change D.complex.classOf n ω = e.symm 1 at hω
  refine ⟨ω, ?_⟩
  rw [← he ω, hω]
  exact e.apply_symm_apply 1

/-- A local zero-integral top form is a compact boundary in its own full
Euclidean compact realization; the primitive is an actual lower-degree object. -/
theorem compact_primitive
    (hcalc : Specs.SmoothManifolds.DeRham.CompactSupportEuclidean.calculationType.{u})
    {n : ℕ} {M : Type u} [TopologicalSpace M] (P : Presentation (n+1) M)
    (C : CotangentBundle P.manifold) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (D : CompactCalculus K ⊤)
    (ω : D.complex.Obj (n+1)) (hω : totalIntegral P D ω = 0) :
    ∃ β : D.complex.Obj n, D.complex.d n β = ω := by
  exact ((hcalc P C B K D).2.2.2 ω).mpr hω

/-- A compactly supported primitive on an open set extends to a compact
primitive in the ambient realization. Compactness is imposed in the open-set
topology, which rules out any support at the artificial edge. -/
theorem primitive_zero_extension {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (D : CompactCalculus K ⊤) (U : TopologicalSpace.Opens M) (k : ℕ)
    (β : RestrictedField S U k) (η : RestrictedField S U (k+1))
    (hβ : IsRestrictedForm (B k) U β) (hc : IsCompact (sectionSupport β))
    (hd : HasRestrictedDerivative C U β η)
    (ω : D.complex.Obj (k+1))
    (hω : (D.inclusion.map (k+1) ω).val = zeroExtend η) :
    ∃ b : D.complex.Obj k, D.complex.d k b = ω := by
  have he := CompactSupportResults.zeroExtend_smooth (B k) U β hβ hc
  let α : K.forms k := ⟨zeroExtend β, (K.mem_forms k _).mpr he⟩
  have hαc : IsCompact (sectionSupport α.val) := by
    change IsCompact (ModelData.sectionSupport (zeroExtend β))
    rw [CompactSupportResults.zeroExtend_support U β hc]
    exact hc.image continuous_subtype_val
  obtain ⟨b, hb⟩ := (D.range k α).mp ⟨hαc, subset_univ _⟩
  refine ⟨b, ?_⟩
  apply D.injective (k+1)
  apply Subtype.ext
  have hcomm := D.inclusion.comm k b
  have hdext := CompactSupportResults.extension_derivative K U k β η hβ hc hd
  have hD : (K.d k α).val = zeroExtend η := hdext
  exact (congrArg (fun x : K.forms (k+1) => x.val) hcomm.symm).trans
    ((congrArg (fun x : K.forms k => (K.d k x).val) hb).trans (hD.trans hω.symm))

/-- Extension transports compact boundaries, with no additional support
hypothesis: its source is already the full compact realization on the open set. -/
theorem extension_exact {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {C : CotangentBundle S} {B : ∀ k, FormBundle C k} {K : Calculus C B}
    {U V : TopologicalSpace.Opens M} (hUV : U ≤ V)
    (D : CompactCalculus K U) (E : CompactCalculus K V) (k : ℕ)
    (ω : D.complex.Obj k) (hω : ω ∈ D.complex.exact k) :
    (CompactSupportResults.extension hUV D E).map k ω ∈ E.complex.exact k := by
  cases k with
  | zero =>
    have hz : ω = 0 := hω
    change (CompactSupportResults.extension hUV D E).map 0 ω = 0
    rw [hz, map_zero]
  | succ k =>
    obtain ⟨β, hβ⟩ := hω
    refine ⟨(CompactSupportResults.extension hUV D E).map k β, ?_⟩
    exact ((CompactSupportResults.extension hUV D E).comm k β).trans
      (congrArg ((CompactSupportResults.extension hUV D E).map (k+1)) hβ)
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData BundleData FrameData ModelData Set
universe u v w

/-- Synthesis in a genuine bundle trivialization on an arbitrary open patch. -/
def coordinateSynthesis {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (F : SmoothVectorBundle S r ι E) (U : TopologicalSpace.Opens M)
    (i : ι) (hi : ∀ p : U, p.val ∈ F.baseSet i) (f : U → Euclidean r) :
    (p : U) → E p.val :=
  fun p => (F.fiberCoordinates i p.val (hi p)).symm (f p)

@[simp] theorem coordinateSynthesis_coordinates {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (F : SmoothVectorBundle S r ι E) (U : TopologicalSpace.Opens M)
    (i : ι) (hi : ∀ p : U, p.val ∈ F.baseSet i) (f : U → Euclidean r) :
    Frames.sectionCoordinates F U i (coordinateSynthesis F U i hi f) = f := by
  funext p
  change ((F.trivialization i) (⟨p.val, _⟩ : Bundle.TotalSpace (Euclidean r) E)).2 = f p
  rw [← SmoothVectorBundle.fiberCoordinates_apply F i p.val (hi p)]
  exact (F.fiberCoordinates i p.val (hi p)).apply_symm_apply (f p)

theorem coordinateSynthesis_smooth {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (F : SmoothVectorBundle S r ι E) (U : TopologicalSpace.Opens M)
    (i : ι) (hi : ∀ p : U, p.val ∈ F.baseSet i) (f : U → Euclidean r)
    (hf : VectorSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen) f) :
    ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen)
      F.totalManifold.smoothStructure.val
      (fun p : U => (⟨p.val, coordinateSynthesis F U i hi f p⟩ :
        Bundle.TotalSpace (Euclidean r) E)) := by
  intro p
  apply Frames.smoothAt_of_sectionCoordinates F U U.isOpen i _ p (hi p)
  rw [coordinateSynthesis_coordinates]
  exact hf p

theorem coordinateSynthesis_support {n r : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {ι : Type v}
    {E : M → Type w} [∀ p, AddCommGroup (E p)] [∀ p, Module ℝ (E p)]
    [TopologicalSpace (Bundle.TotalSpace (Euclidean r) E)]
    (F : SmoothVectorBundle S r ι E) (U : TopologicalSpace.Opens M)
    (i : ι) (hi : ∀ p : U, p.val ∈ F.baseSet i) (f : U → Euclidean r) :
    sectionSupport (coordinateSynthesis F U i hi f) = sectionSupport f := by
  apply congrArg closure
  ext p
  change ((F.fiberCoordinates i p.val (hi p)).symm (f p) ≠ 0) ↔ f p ≠ 0
  exact not_congr ((F.fiberCoordinates i p.val (hi p)).symm.map_eq_zero_iff)
open TangentData TangentBundleData BundleOperationsData CovectorData ExteriorData
  DeRhamData MayerVietorisData CompactSupportData

/-- Smooth compact coordinate data on an open patch synthesize a genuine
restricted exterior form with the same compact support and the prescribed
bundle coordinate vector. This works for either original manifold model. -/
theorem restricted_form_of_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (U : TopologicalSpace.Opens M)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hu : (U : Set M) ⊆ c.source) (f : U → Euclidean (n.choose k))
    (hf : VectorSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen) f)
    (hcompact : IsCompact (sectionSupport f)) :
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    ∃ ω : RestrictedField S U k, IsRestrictedForm B U ω ∧
      IsCompact (sectionSupport ω) ∧
      sectionSupport ω = sectionSupport f ∧
      Frames.sectionCoordinates B.space.bundle U ⟨c,hc⟩ ω = f := by
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  let F := B.space.bundle
  have hi (p : U) : p.val ∈ F.baseSet ⟨c,hc⟩ := by
    change p.val ∈ B.space.bundle.baseSet ⟨c,hc⟩
    rw [B.baseSet, Covectors.cotangent_baseSet]
    exact hu p.property
  let ω : RestrictedField S U k := coordinateSynthesis F U ⟨c,hc⟩ hi f
  have hs : sectionSupport ω = sectionSupport f :=
    coordinateSynthesis_support F U ⟨c,hc⟩ hi f
  refine ⟨ω, ?_, hs ▸ hcompact, hs, ?_⟩
  · exact coordinateSynthesis_smooth F U ⟨c,hc⟩ hi f hf
  · exact coordinateSynthesis_coordinates F U ⟨c,hc⟩ hi f
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport


namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData
  DeRhamData MayerVietorisData CompactSupportData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData Set
universe u

section Globalization
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} (D : CompactCalculus K ⊤)

/-- Every top form is closed, so its quotient class is a linear function
on the whole space of compact top forms. -/
def topClass : D.complex.Obj n →ₗ[ℝ] D.Cohomology n :=
  (D.complex.classOf n).comp ({
    toFun ω := ⟨ω, top_closed D ω⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl } : D.complex.Obj n →ₗ[ℝ] D.complex.closed n)

theorem topClass_surjective : Function.Surjective (topClass D) := by
  intro x
  obtain ⟨ω, rfl⟩ := D.complex.class_surjective n x
  exact ⟨ω.val, rfl⟩

theorem topClass_eq_iff (α β : D.complex.Obj n) :
    topClass D α = topClass D β ↔ α - β ∈ D.complex.exact n :=
  D.complex.class_eq_iff n ⟨α, top_closed D α⟩ ⟨β, top_closed D β⟩

variable (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)

@[simp] theorem cohomologyIntegral_topClass (hb : intrinsicBoundary S = ∅)
    (ω : D.complex.Obj n) :
    cohomologyIntegral D o I hI hb (topClass D ω) = integralLinear D o I hI ω := rfl

/-- Local zero-integral exactness compares any local top form to a normalized
local form. Both compact supports remain in the given open set. This lemma
records an implication; it does not supply the Euclidean local exactness proof. -/
theorem class_eq_integral_smul (V : TopologicalSpace.Opens M)
    (hlocal : ∀ ω : D.complex.Obj n,
      sectionSupport (D.inclusion.map n ω).val ⊆ V →
      integralLinear D o I hI ω = 0 → ω ∈ D.complex.exact n)
    (α β : D.complex.Obj n)
    (hα : sectionSupport (D.inclusion.map n α).val ⊆ V)
    (hβ : sectionSupport (D.inclusion.map n β).val ⊆ V)
    (hβI : integralLinear D o I hI β = 1) :
    topClass D α = integralLinear D o I hI α • topClass D β := by
  rw [← map_smul]
  apply (topClass_eq_iff D _ _).mpr
  apply hlocal
  · let f : D.complex.Obj n →ₗ[ℝ] K.forms n := D.inclusion.map n
    let r := integralLinear D o I hI α
    have hfield : (f (α - r • β)).val = (f α).val - r • (f β).val := by
      have hc : f (α - r • β) = f α - r • f β := by rw [map_sub, map_smul]
      exact congrArg (fun x : K.forms n => x.val) hc
    have hneg : sectionSupport (-(r • (f β).val)) ⊆ sectionSupport (f β).val := by
      apply closure_mono
      intro p hp hz
      exact hp (by simp [hz])
    have hs : sectionSupport ((f α).val - r • (f β).val) ⊆ V := by
      rw [sub_eq_add_neg]
      exact (CompactSupportResults.support_add_subset _ _).trans
        (union_subset hα (hneg.trans hβ))
    exact (congrArg (fun ζ : Field S n => sectionSupport ζ ⊆ V) hfield).mpr hs
  · rw [map_sub, map_smul, hβI]
    simp

/-- The global part of the top-degree argument. A cover with local compact
zero-integral exactness and unit forms in every nonempty open set gives the
integration isomorphism by finite localization and connectedness. The local
inputs are explicit hypotheses of this reduction. The unit-form input is
supplied by `unit_integral_in_open`; no original target has extra hypotheses. -/
theorem integration_iso_of_local_exactness [ConnectedSpace M]
    (hb : intrinsicBoundary S = ∅) {ι : Type*}
    (V : ι → TopologicalSpace.Opens M)
    (hne : ∀ i, (V i : Set M).Nonempty)
    (hcover : ∀ p, ∃ i, p ∈ V i)
    (hlocal : ∀ i (ω : D.complex.Obj n),
      sectionSupport (D.inclusion.map n ω).val ⊆ V i →
      integralLinear D o I hI ω = 0 → ω ∈ D.complex.exact n)
    (hunit : ∀ W : TopologicalSpace.Opens M, (W : Set M).Nonempty →
      ∃ β : D.complex.Obj n,
        sectionSupport (D.inclusion.map n β).val ⊆ W ∧
        integralLinear D o I hI β = 1) :
    ∃ e : D.Cohomology n ≃ₗ[ℝ] ℝ,
      ∀ ω : D.complex.closed n, ∃ η : CompactTopForm S,
        η.field = (D.inclusion.map n ω.val).val ∧
        e (D.complex.classOf n ω) = I η := by
  classical
  choose β hβsupport hβintegral using fun i => hunit (V i) (hne i)
  have hclasses (i j : ι) : topClass D (β i) = topClass D (β j) := by
    apply constant_on_open_cover (fun i => (V i : Set M))
      (fun i => (V i).isOpen) hcover (fun i => topClass D (β i))
      (fun i j hij => ?_) (hne i) (hne j)
    obtain ⟨γ, hγsupport, hγintegral⟩ := hunit (V i ⊓ V j) hij
    have hi := class_eq_integral_smul D o I hI (V i) (hlocal i)
      (β i) γ (hβsupport i) (fun p hp => (hγsupport hp).1) hγintegral
    have hj := class_eq_integral_smul D o I hI (V j) (hlocal j)
      (β j) γ (hβsupport j) (fun p hp => (hγsupport hp).2) hγintegral
    rw [hβintegral, one_smul] at hi hj
    exact hi.trans hj.symm
  obtain ⟨i₀, _⟩ := hcover (Classical.arbitrary M)
  let q := topClass D (β i₀)
  let J := cohomologyIntegral D o I hI hb
  have hq : J q = 1 := hβintegral i₀
  have hnormal (x : D.Cohomology n) : x = J x • q := by
    obtain ⟨ω, rfl⟩ := topClass_surjective D x
    obtain ⟨s, α, hsum, hsupp⟩ := finite_localization D V hcover n ω
    have hα (i : ι) : topClass D (α i) = integralLinear D o I hI (α i) • q := by
      have hi := class_eq_integral_smul D o I hI (V i) (hlocal i)
        (α i) (β i) (hsupp i) (hβsupport i) (hβintegral i)
      exact hi.trans (congrArg (fun z => integralLinear D o I hI (α i) • z)
        (hclasses i i₀))
    calc
      topClass D ω = ∑ i ∈ s, topClass D (α i) := by rw [hsum, map_sum]
      _ = (∑ i ∈ s, integralLinear D o I hI (α i)) • q := by
        simp_rw [hα]
        rw [Finset.sum_smul]
      _ = J (topClass D ω) • q := by
        congr 1
        change (∑ i ∈ s, integralLinear D o I hI (α i)) =
          integralLinear D o I hI ω
        rw [hsum, map_sum]
  have hbij : Function.Bijective J := by
    constructor
    · intro x y hxy
      exact (hnormal x).trans ((congrArg (fun r => r • q) hxy).trans (hnormal y).symm)
    · intro r
      refine ⟨r • q, ?_⟩
      rw [map_smul, hq]
      exact mul_one r
  refine ⟨LinearEquiv.ofBijective J hbij, ?_⟩
  intro ω
  exact ⟨compactTopForm D ω.val, rfl, rfl⟩

end Globalization


/-- The global argument reduces to zero-integral exactness on a neighborhood
of each point. All unit representatives are supplied by the proved geometric
construction. This is a reduction, not a proof of the local hypothesis. -/
theorem integration_iso_of_pointwise_exactness
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    {K : Calculus C B} (D : CompactCalculus K ⊤)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hb : intrinsicBoundary S = ∅)
    (hlocal : ∀ p : M, ∃ V : TopologicalSpace.Opens M, p ∈ V ∧
      ∀ ω : D.complex.Obj n, sectionSupport (D.inclusion.map n ω).val ⊆ V →
        integralLinear D o I hI ω = 0 → ω ∈ D.complex.exact n) :
    ∃ e : D.Cohomology n ≃ₗ[ℝ] ℝ,
      ∀ ω : D.complex.closed n, ∃ η : CompactTopForm S,
        η.field = (D.inclusion.map n ω.val).val ∧
        e (D.complex.classOf n ω) = I η := by
  classical
  choose V hpV hV using hlocal
  exact integration_iso_of_local_exactness D o I hI hb V
    (fun p => ⟨p, hpV p⟩) (fun p => ⟨p, hpV p⟩) hV
    (fun W hW => unit_integral_in_open D o I hI hb W hW)

end SmoothManifolds.OrientedTopDegreeResults

namespace SmoothManifolds.OrientedTopDegreeResults
universe u

theorem compact_comparison :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u} :=
  compact_comparison_proof

theorem zero_dimension :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u} :=
  zero_dimension_proof

end SmoothManifolds.OrientedTopDegreeResults


set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData DifferentialData Set Filter
open scoped Topology
universe u

/-- The tangent map of a genuine open inclusion is an isomorphism. -/
theorem open_inclusion_differential_equiv {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U hU))
    (hi : IsSmoothMap R S Subtype.val) (p : U) :
    ∃ E : TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val,
      IsDifferential R S Subtype.val p E.toLinearMap := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
  let d := c.subtypeRestr (s := ⟨U,hU⟩) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension
      (openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 U hU)
      ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hpc
  obtain ⟨xc, bc, E, hxc, hEc, _⟩ := coordinate_tangent_model R p d hd hpd
  obtain ⟨yc, bd, F, hyc, hFc, _⟩ := coordinate_tangent_model S p.val c hc hpc
  let L := differential R S Subtype.val hi p
  have hL : IsDifferential R S Subtype.val p L := differential_spec R S Subtype.val hi p
  have hj (v : TangentSpace R p) : F (L v) = E v := by
    have hh := differential_jacobian R S Subtype.val hi p L hL d c hd hc hpd hpc
      E F ⟨xc,hxc,hEc⟩ ⟨yc,hyc,hFc⟩ univ id isOpen_univ (mem_univ _)
      contDiffOn_id (Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply] using hh
  have heq : L = (E.trans F.symm).toLinearMap := by
    apply LinearMap.ext
    intro v
    apply F.injective
    simpa only [LinearEquiv.trans_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hj v
  exact ⟨E.trans F.symm, heq ▸ hL⟩


/-- The raw restricted-atlas identity extends to the genuine open submanifold,
and the inclusion supplies the smooth identity in the opposite direction. -/
theorem local_restricted_diffeomorph {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (T : SmoothManifold n b U) (hi : IsSmoothMap T S Subtype.val)
    (hr : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      T.smoothStructure.val id) :
    ∃ R : SmoothManifold n a U,
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val U hU) ∧
      IsSmoothMap R S Subtype.val ∧ IsSmoothMap T R id ∧ IsSmoothMap R T id := by
  obtain ⟨R, _, hR, hRi⟩ := exists_openSubset_smoothManifold S U hU
  have hA := openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 U hU
  refine ⟨R, hR, hRi, ?_, ?_⟩
  · intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p.val
    let d := c.subtypeRestr (s := ⟨U,hU⟩) ⟨p⟩
    obtain ⟨t, ht, hpt⟩ := T.smoothStructure.property.1.1 p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      T.smoothStructure.property.1 R.smoothStructure.property.1 id p).mpr
    refine ⟨continuousAt_id, t, ht, d, ?_, hpt, ?_, ?_⟩
    · rw [hR]
      exact subset_maximalExtension hA ⟨⟨p⟩, c, hc, rfl⟩
    · simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage, id_eq] using hp
    · exact (hi p).2 t ht c hc hpt hp
  · intro p
    obtain ⟨d, hd, hpd⟩ := hA.1 p
    obtain ⟨t, ht, hpt⟩ := T.smoothStructure.property.1.1 p
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      R.smoothStructure.property.1 T.smoothStructure.property.1 id p).mpr
    refine ⟨continuousAt_id, d, ?_, t, ht, hpd, hpt, (hr p).2 d hd t ht hpd hpt⟩
    rw [hR]
    exact subset_maximalExtension hA hd

/-- The inverse tangent equivalence of a smooth identity has the inverse
identity's genuine differential property, directly on the defining germs. -/
theorem inverse_identity_differential {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (T : SmoothManifold n b M)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] TangentSpace T p)
    (hE : IsDifferential S T id p E.toLinearMap) :
    IsDifferential T S id p E.symm.toLinearMap := by
  intro v h k r hr hk
  have hh := hE (E.symm v) k h r
    (by simpa only [Function.comp_def, id_eq] using hk)
    (by simpa only [Function.comp_def, id_eq] using hr)
  change (E (E.symm v)).val k = (E.symm v).val h at hh
  rw [E.apply_symm_apply] at hh
  exact hh.symm

/-- The differential data for the full local presentation, with both identity
maps, are actual inverse equivalences and compose to the ambient inclusion. -/
theorem local_differential_data {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (T : SmoothManifold n b U) (hi : IsSmoothMap T S Subtype.val)
    (hr : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      T.smoothStructure.val id) :
    ∃ R : SmoothManifold n a U,
      R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
        (openSubsetAtlas S.smoothStructure.val U hU) ∧
      ∃ (hRi : IsSmoothMap R S Subtype.val) (hf : IsSmoothMap T R id)
        (hg : IsSmoothMap R T id),
      ∃ (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
        (A : (p : U) → TangentSpace T p ≃ₗ[ℝ] TangentSpace R p),
        (∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap) ∧
        (∀ p, IsDifferential T R id p (A p).toLinearMap) ∧
        (∀ p, IsDifferential R T id p (A p).symm.toLinearMap) := by
  classical
  obtain ⟨R,hR,hRi,hf,hg⟩ := local_restricted_diffeomorph S U hU T hi hr
  let h : Diffeomorph T.smoothStructure.val R.smoothStructure.val := {
    toEquiv := Equiv.refl U
    contDiff_toFun := hf
    contDiff_invFun := hg }
  have hE := fun p => open_inclusion_differential_equiv S U hU R hR hRi p
  have hA := fun p => differential_diffeomorph T R h p
  choose E hE using hE
  choose A hA using hA
  exact ⟨R,hR,hRi,hf,hg,E,A,hE,hA,fun p => inverse_identity_differential T R p (A p) (hA p)⟩

/-- A smooth presentation equivalent to the restricted ambient atlas has
isomorphisms as the actual tangent maps of its inclusion. -/
theorem local_inclusion_differential_equiv {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : Set M) (hU : IsOpen U)
    (T : SmoothManifold n b U) (hi : IsSmoothMap T S Subtype.val)
    (hr : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      T.smoothStructure.val id) :
    ∀ p : U, ∃ E : TangentSpace T p ≃ₗ[ℝ] TangentSpace S p.val,
      IsDifferential T S Subtype.val p E.toLinearMap := by
  obtain ⟨R,hR,hRi,hf,hg,E,A,hE,hA,hG⟩ := local_differential_data S U hU T hi hr
  intro p
  exact ⟨(A p).trans (E p),
    differential_comp T R S id Subtype.val hf hRi p
      (A p).toLinearMap (E p).toLinearMap (hA p) (hE p)⟩
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleData BundleOperationsData CovectorData ExteriorData FormPullbackData
  MayerVietorisData FrameData Set Filter
open scoped Topology
universe u

/-- Transfer a smooth form on a genuine open submanifold to its ambient
restricted tangent fibers using the differential of the inclusion. -/
theorem restricted_form_of_open_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hi : IsSmoothMap R S Subtype.val)
    (C : CotangentBundle S) (A : CotangentBundle R) (k : ℕ)
    (B : FormBundle C k) (G : FormBundle A k)
    (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (α : Field R k) (hα : IsForm G α) :
    IsRestrictedForm B U (fun p =>
      fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p) k
        (E p).symm.toLinearMap (α p)) := by
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace A).topology
  letI := B.space.topology
  letI := G.space.topology
  let β : RestrictedField S U k := fun p =>
    fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p) k
      (E p).symm.toLinearMap (α p)
  have hA := openSubsetAtlas_isContDiffAtlas ⊤ _ S.smoothStructure.property.1 U U.isOpen
  have hαraw : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen)
      G.space.bundle.totalManifold.smoothStructure.val
      (fun p => (⟨p, α p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace R q) k))) := by
    intro p
    refine ⟨(hα p).1, ?_⟩
    intro c hc d hd hp hpd
    have hcR : c ∈ R.smoothStructure.val := by
      rw [hR]
      exact subset_maximalExtension hA hc
    exact (hα p).2 c hcR d hd hp hpd
  intro p
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p.val
  let d : ModelChart n a U := c.subtypeRestr (s := U) ⟨p⟩
  have hd : d ∈ R.smoothStructure.val := by
    rw [hR]
    exact subset_maximalExtension hA ⟨⟨p⟩, c, hc, rfl⟩
  have hpd : p ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hpc
  let z : U → Euclidean (n.choose k) := fun q =>
    ((G.space.bundle.trivialization ⟨d, hd⟩) ⟨q, α q⟩).2
  have hz : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U U.isOpen) z p := by
    apply (Frames.trivializationCoordinates_smoothAt G.space.bundle ⟨d,hd⟩
      ⟨p, α p⟩ (by rw [G.baseSet, Covectors.cotangent_baseSet]; exact hpd)).comp
      (g := fun q => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun r => Fiber (TangentSpace R r) k)))
      G.space.bundle.totalManifold.smoothStructure.property.1.1
      (hαraw p)
  let T : Euclidean (n.choose k) →ₗ[ℝ] Euclidean (n.choose k) :=
    B.modelEquiv.toLinearMap.comp G.modelEquiv.symm.toLinearMap
  have ht : VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U U.isOpen)
      (fun q => T (z q)) p := hz.postcomp (LinearMap.toContinuousLinearMap T).contDiff
  apply Frames.smoothAt_of_sectionCoordinates B.space.bundle U U.isOpen
    ⟨c,hc⟩ β p (by rw [B.baseSet, Covectors.cotangent_baseSet]; exact hpc)
  apply ht.congr
  apply Filter.EventuallyEq.symm
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds
    (c.open_source.mem_nhds hpc)] with q hqc
  change q.val ∈ c.source at hqc
  have hqd : q ∈ d.source := by
    simpa only [d, OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hqc
  have hqC : q.val ∈ (cotangentSpace C).bundle.baseSet ⟨c,hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hqc
  have hqA : q ∈ (cotangentSpace A).bundle.baseSet ⟨d,hd⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hqd
  let eC := (cotangentSpace C).bundle.fiberCoordinates ⟨c,hc⟩ q.val hqC
  let eA := (cotangentSpace A).bundle.fiberCoordinates ⟨d,hd⟩ q hqA
  have hj (v : TangentSpace R q) :
      C.tangent.fiberCoordinates.equiv c hc q.val hqc (E q v) =
        A.tangent.fiberCoordinates.equiv d hd q hqd v := by
    have hh := differential_jacobian R S Subtype.val hi q
      (E q).toLinearMap (hE q) d c hd hc hqd hqc
      (A.tangent.fiberCoordinates.equiv d hd q hqd)
      (C.tangent.fiberCoordinates.equiv c hc q.val hqc)
      (A.tangent.fiberCoordinates.isCoordinates d hd q hqd)
      (C.tangent.fiberCoordinates.isCoordinates c hc q.val hqc)
      univ id isOpen_univ (mem_univ _) contDiffOn_id
      (Eventually.of_forall (fun _ => rfl)) v
    simpa only [fderiv_id, ContinuousLinearMap.id_apply, LinearEquiv.coe_coe] using hh
  have hlin : eC.toLinearMap.comp (E q).symm.toLinearMap.dualMap = eA.toLinearMap := by
    ext lam i
    simp only [eC, eA, LinearMap.comp_apply, LinearEquiv.coe_coe,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply]
    rw [Covectors.cotangent_coordinates C c hc q.val hqc,
      Covectors.cotangent_coordinates A d hd q hqd]
    change lam ((E q).symm (coordinateVector C.tangent.fiberCoordinates c hc q.val hqc i)) =
      lam (coordinateVector A.tangent.fiberCoordinates d hd q hqd i)
    congr 1
    apply (A.tangent.fiberCoordinates.equiv d hd q hqd).injective
    rw [← hj]
    simp only [LinearEquiv.apply_symm_apply, CovectorData.coordinateVector,
      LinearEquiv.apply_symm_apply]
  have hmap := congrArg (fun F => exteriorPower.map k F (α q)) hlin
  simp only [exteriorPower.map_comp, LinearMap.comp_apply] at hmap
  change ((B.space.bundle.trivialization ⟨c,hc⟩) ⟨q.val, β q⟩).2 = T (z q)
  rw [FormPullbackResults.form_coordinates C k B c hc q.val hqc]
  change B.modelEquiv (exteriorPower.map k eC.toLinearMap
    (exteriorPower.map k (E q).symm.toLinearMap.dualMap (α q))) = _
  rw [hmap]
  have hzval : z q = G.modelEquiv (exteriorPower.map k eA.toLinearMap (α q)) :=
    FormPullbackResults.form_coordinates A k G d hd q hqd (α q)
  rw [hzval]
  simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option linter.unusedVariables false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleData BundleOperationsData CovectorData ExteriorData FormPullbackData
  MayerVietorisData FrameData Set Filter
open scoped Topology
universe u

theorem fiberPullback_comp {V W X : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    (k : ℕ) (L : V →ₗ[ℝ] W) (K : W →ₗ[ℝ] X) (x : Fiber X k) :
    fiberPullback k (K.comp L) x = fiberPullback k L (fiberPullback k K x) := by
  unfold fiberPullback
  rw [← LinearMap.dualMap_comp_dualMap, exteriorPower.map_comp, LinearMap.comp_apply]


theorem fiberPullback_trans_symm {V W X : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [AddCommGroup X] [Module ℝ X]
    (k : ℕ) (A : V ≃ₗ[ℝ] W) (E : W ≃ₗ[ℝ] X) (x : Fiber V k) :
    fiberPullback k (A.trans E).symm.toLinearMap x =
      fiberPullback k E.symm.toLinearMap (fiberPullback k A.symm.toLinearMap x) := by
  rw [LinearEquiv.trans_symm, LinearEquiv.coe_trans]
  exact fiberPullback_comp k E.symm.toLinearMap A.symm.toLinearMap x

/-- Any smooth form on the local presentation pushes to a genuine smooth
restricted ambient form through the inverse of its inclusion differential. -/
theorem restricted_form_of_local_form {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (T : SmoothManifold n b U) (R : SmoothManifold n a U)
    (hR : R.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (openSubsetAtlas S.smoothStructure.val U U.isOpen))
    (hRi : IsSmoothMap R S Subtype.val) (hg : IsSmoothMap R T id)
    (C : CotangentBundle S) (CT : CotangentBundle T)
    (E : (p : U) → TangentSpace R p ≃ₗ[ℝ] TangentSpace S p.val)
    (A : (p : U) → TangentSpace T p ≃ₗ[ℝ] TangentSpace R p)
    (hE : ∀ p, IsDifferential R S Subtype.val p (E p).toLinearMap)
    (hA : ∀ p, IsDifferential R T id p (A p).symm.toLinearMap)
    (k : ℕ) (B : FormBundle C k) (F : FormBundle CT k)
    (α : Field T k) (hα : IsForm F α) :
    IsRestrictedForm B U (fun p =>
      fiberPullback (V := TangentSpace S p.val) (W := TangentSpace T p) k
        ((A p).trans (E p)).symm.toLinearMap (α p)) := by
  obtain ⟨CR⟩ := BundleOperations.exists_cotangent R
  obtain ⟨GR⟩ := ExteriorAlgebraResults.exists_formBundle CR k
  let γ : Field R k := pullbackField R T id (fun p => (A p).symm.toLinearMap) α
  have hγ : IsForm GR γ := FormPullbackResults.pullback_smooth R T CR CT id hg
    (fun p => (A p).symm.toLinearMap) hA k GR F α hα
  have hb := restricted_form_of_open_form S U R hR hRi C CR k B GR E hE γ hγ
  have he : (fun p => fiberPullback (V := TangentSpace S p.val) (W := TangentSpace T p) k
        ((A p).trans (E p)).symm.toLinearMap (α p)) =
      fun p => fiberPullback (V := TangentSpace S p.val) (W := TangentSpace R p) k
        (E p).symm.toLinearMap (γ p) := by
    funext p
    dsimp only [γ, FormPullbackData.pullbackField]
    exact @fiberPullback_trans_symm (TangentSpace T p) (TangentSpace R p)
      (TangentSpace S p.val) inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance k (A p) (E p) (α p)
  rw [he]
  exact hb
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData TangentBundleData DifferentialData
  BundleOperationsData CovectorData ExteriorData ExteriorDerivativeData DeRhamData
  MayerVietorisData CompactSupportData FormPullbackData Set
universe u

theorem fiberPullback_symm {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (e : V ≃ₗ[ℝ] W)
    (x : Fiber V k) :
    fiberPullback k e.toLinearMap (fiberPullback k e.symm.toLinearMap x) = x := by
  unfold fiberPullback
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    LinearMap.dualMap_comp_dualMap]
  simp

def fiberPullbackEquiv {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (e : V ≃ₗ[ℝ] W) :
    Fiber W k ≃ₗ[ℝ] Fiber V k where
  toFun := fiberPullback k e.toLinearMap
  invFun := fiberPullback k e.symm.toLinearMap
  left_inv := fiberPullback_symm k e.symm
  right_inv := fiberPullback_symm k e
  map_add' := map_add _
  map_smul' := map_smul _

theorem fiberPullback_injective {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (e : V ≃ₗ[ℝ] W) :
    Function.Injective (fiberPullback (V := V) (W := W) k e.toLinearMap) :=
  (fiberPullbackEquiv k e).injective

theorem fiberPullback_zero_iff {V W : Type u} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (k : ℕ) (e : V ≃ₗ[ℝ] W) (x : Fiber W k) :
    fiberPullback (V := V) (W := W) k e.toLinearMap x = 0 ↔ x = 0 :=
  (fiberPullbackEquiv k e).map_eq_zero_iff

theorem pullback_open_support {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (U : TopologicalSpace.Opens M) (P : SmoothManifold n b U)
    (L : (q : U) → TangentSpace P q ≃ₗ[ℝ] TangentSpace S q.val)
    (k : ℕ) (ω : Field S k) :
    sectionSupport (pullbackField P S Subtype.val (fun q => (L q).toLinearMap) ω) =
      Subtype.val ⁻¹' sectionSupport ω := by
  have hn : {q : U | pullbackField P S Subtype.val (fun q => (L q).toLinearMap) ω q ≠ 0} =
      Subtype.val ⁻¹' {p | ω p ≠ 0} := by
    apply Set.ext
    intro q
    change fiberPullback (V := TangentSpace P q) (W := TangentSpace S q.val) k (L q).toLinearMap (ω q.val) ≠ 0 ↔ ω q.val ≠ 0
    constructor
    · intro h hz
      exact h (by rw [hz, map_zero])
    · intro h hz
      apply h
      exact (exteriorPower.map_injective_field (L q).dualMap.injective)
        (hz.trans (map_zero _).symm)
  change closure _ = Subtype.val ⁻¹' closure _
  rw [hn]
  exact (U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    continuous_subtype_val {p | ω p ≠ 0}).symm

theorem pullback_open_compact {n : ℕ} {a b : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (U : TopologicalSpace.Opens M) (P : SmoothManifold n b U)
    (L : (q : U) → TangentSpace P q ≃ₗ[ℝ] TangentSpace S q.val)
    (k : ℕ) (ω : Field S k) (hc : IsCompact (sectionSupport ω))
    (hs : sectionSupport ω ⊆ U) :
    IsCompact (sectionSupport
      (pullbackField P S Subtype.val (fun q => (L q).toLinearMap) ω)) := by
  rw [pullback_open_support U P L k ω]
  apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hc
  intro p hp
  exact ⟨⟨p, hs hp⟩, rfl⟩

open private smoothPull smoothPull_chain from MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

section PullSupported
variable {n : ℕ} {a b : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
  {K : Calculus C B} (U : TopologicalSpace.Opens M)
  (P : SmoothManifold n b U) (A : CotangentBundle P) (F : ∀ k, FormBundle A k)
  (J : Calculus A F) (E : CompactCalculus K U) (G : CompactCalculus J ⊤)
  (hi : IsSmoothMap P S Subtype.val)
  (L : (q : U) → TangentSpace P q ≃ₗ[ℝ] TangentSpace S q.val)
  (hL : ∀ q, IsDifferential P S Subtype.val q (L q).toLinearMap)

def supportedPullForms (k : ℕ) : E.complex.Obj k →ₗ[ℝ] J.forms k :=
  (smoothPull J K Subtype.val hi (fun q => (L q).toLinearMap) hL k).comp
    (E.inclusion.map k)

theorem supportedPullForms_compact (k : ℕ) (x : E.complex.Obj k) :
    IsCompact (sectionSupport (supportedPullForms U P A F J E hi L hL k x).val) ∧
      sectionSupport (supportedPullForms U P A F J E hi L hL k x).val ⊆ (⊤ : TopologicalSpace.Opens U) := by
  exact ⟨pullback_open_compact U P L k _
    (CompactSupportResults.inclusion_support E k x).1
    (CompactSupportResults.inclusion_support E k x).2, subset_univ _⟩

def supportedPullMap (k : ℕ) : E.complex.Obj k →ₗ[ℝ] G.complex.Obj k :=
  CompactSupportResults.liftMap G k (supportedPullForms U P A F J E hi L hL k)
    (supportedPullForms_compact U P A F J E hi L hL k)

theorem supportedPullMap_eq (k : ℕ) (x : E.complex.Obj k) :
    G.inclusion.map k (supportedPullMap U P A F J E G hi L hL k x) =
      supportedPullForms U P A F J E hi L hL k x :=
  CompactSupportResults.liftMap_eq G k (supportedPullForms U P A F J E hi L hL k)
    (supportedPullForms_compact U P A F J E hi L hL k) x

theorem supportedPullForms_chain (k : ℕ) (x : E.complex.Obj k) :
    J.d k (supportedPullForms U P A F J E hi L hL k x) =
      supportedPullForms U P A F J E hi L hL (k+1) (E.complex.d k x) := by
  change J.d k (smoothPull J K Subtype.val hi (fun q => (L q).toLinearMap) hL k
      (E.inclusion.map k x)) =
      smoothPull J K Subtype.val hi (fun q => (L q).toLinearMap) hL (k+1)
        (E.inclusion.map (k+1) (E.complex.d k x))
  exact (smoothPull_chain J K Subtype.val hi (fun q => (L q).toLinearMap) hL
    ExteriorDerivativeResults.smooth_naturality k (E.inclusion.map k x)).symm.trans
    (congrArg (smoothPull J K Subtype.val hi (fun q => (L q).toLinearMap) hL (k+1))
      (E.inclusion.comm k x))

def supportedPullChain : ChainMap E.complex G.complex where
  map := supportedPullMap U P A F J E G hi L hL
  comm k x := by
    apply G.injective (k+1)
    calc
      G.inclusion.map (k+1) (G.complex.d k (supportedPullMap U P A F J E G hi L hL k x)) =
          J.d k (G.inclusion.map k (supportedPullMap U P A F J E G hi L hL k x)) :=
        (G.inclusion.comm k _).symm
      _ = J.d k (supportedPullForms U P A F J E hi L hL k x) :=
        congrArg (J.d k) (supportedPullMap_eq U P A F J E G hi L hL k x)
      _ = supportedPullForms U P A F J E hi L hL (k+1) (E.complex.d k x) :=
        supportedPullForms_chain U P A F J E hi L hL k x
      _ = G.inclusion.map (k+1)
          (supportedPullMap U P A F J E G hi L hL (k+1) (E.complex.d k x)) :=
        (supportedPullMap_eq U P A F J E G hi L hL (k+1) (E.complex.d k x)).symm

theorem supportedPullChain_field (k : ℕ) (x : E.complex.Obj k) :
    (G.inclusion.map k ((supportedPullChain U P A F J E G hi L hL).map k x)).val =
      pullbackField P S Subtype.val (fun q => (L q).toLinearMap)
        (E.inclusion.map k x).val :=
  congrArg Subtype.val (supportedPullMap_eq U P A F J E G hi L hL k x)

theorem supportedPullChain_injective (k : ℕ) :
    Function.Injective ((supportedPullChain U P A F J E G hi L hL).map k) := by
  intro x y hxy
  apply E.injective k
  apply Subtype.ext
  funext p
  by_cases hp : p ∈ U
  · have he := congrArg (fun z : G.complex.Obj k => (G.inclusion.map k z).val ⟨p,hp⟩) hxy
    rw [supportedPullChain_field, supportedPullChain_field] at he
    dsimp only [FormPullbackData.pullbackField] at he
    exact @fiberPullback_injective (TangentSpace P ⟨p,hp⟩) (TangentSpace S p)
      inferInstance inferInstance inferInstance inferInstance k (L ⟨p,hp⟩) _ _ he
  · have hx : (E.inclusion.map k x).val p = 0 := by
      by_contra hn
      exact hp ((CompactSupportResults.inclusion_support E k x).2 (subset_closure hn))
    have hy : (E.inclusion.map k y).val p = 0 := by
      by_contra hn
      exact hp ((CompactSupportResults.inclusion_support E k y).2 (subset_closure hn))
    exact hx.trans hy.symm


theorem supportedPullChain_surjective
    (hpush : ∀ (k : ℕ) (α : Field P k), IsForm (F k) α →
      IsRestrictedForm (B k) U (fun q => fiberPullback (V := TangentSpace S q.val) (W := TangentSpace P q)
        k (L q).symm.toLinearMap (α q)))
    (k : ℕ) :
    Function.Surjective ((supportedPullChain U P A F J E G hi L hL).map k) := by
  intro y
  let α : Field P k := (G.inclusion.map k y).val
  let β : RestrictedField S U k := fun q => fiberPullback (V := TangentSpace S q.val) (W := TangentSpace P q)
    k (L q).symm.toLinearMap (α q)
  have hs : sectionSupport β = sectionSupport α := by
    apply congrArg closure
    apply Set.ext
    intro q
    change fiberPullback (V := TangentSpace S q.val) (W := TangentSpace P q)
      k (L q).symm.toLinearMap (α q) ≠ 0 ↔ α q ≠ 0
    exact not_congr (@fiberPullback_zero_iff (TangentSpace S q.val) (TangentSpace P q)
      inferInstance inferInstance inferInstance inferInstance k (L q).symm (α q))
  have hc : IsCompact (sectionSupport β) := by
    rw [hs]
    exact (CompactSupportResults.inclusion_support G k y).1
  have hb : IsRestrictedForm (B k) U β :=
    hpush k α ((J.mem_forms k _).mp (G.inclusion.map k y).property)
  obtain ⟨x, hx⟩ := (CompactSupportResults.open_forms_iff E k β).mp ⟨hb, hc⟩
  refine ⟨x, ?_⟩
  apply G.injective k
  apply Subtype.ext
  rw [supportedPullChain_field]
  funext q
  change fiberPullback (V := TangentSpace P q) (W := TangentSpace S q.val) k (L q).toLinearMap ((E.inclusion.map k x).val q.val) = α q
  rw [hx q]
  exact @fiberPullback_symm (TangentSpace P q) (TangentSpace S q.val)
    inferInstance inferInstance inferInstance inferInstance k (L q) (α q)

theorem supportedPullChain_bijective
    (hpush : ∀ (k : ℕ) (α : Field P k), IsForm (F k) α →
      IsRestrictedForm (B k) U (fun q => fiberPullback (V := TangentSpace S q.val) (W := TangentSpace P q)
        k (L q).symm.toLinearMap (α q)))
    (k : ℕ) :
    Function.Bijective ((supportedPullChain U P A F J E G hi L hL).map k) :=
  ⟨supportedPullChain_injective U P A F J E G hi L hL k,
    supportedPullChain_surjective U P A F J E G hi L hL hpush k⟩

end PullSupported
end SmoothManifolds.OrientedTopDegreeResults.LocalTransport



set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults
universe u

theorem linearMap_injective_of_equiv_real {V : Type u}
    [AddCommGroup V] [Module ℝ V] (e : V ≃ₗ[ℝ] ℝ)
    (J : V →ₗ[ℝ] ℝ) (v : V) (hv : J v ≠ 0) : Function.Injective J := by
  have hev : e v ≠ 0 := by
    intro h
    apply hv
    have : v = 0 := e.injective (h.trans (map_zero e).symm)
    rw [this, map_zero]
  have hformula (w : V) : w = (e w / e v) • v := by
    apply e.injective
    rw [map_smul]
    dsimp only [smul_eq_mul]
    exact (div_mul_cancel₀ (e w) hev).symm
  intro w z h
  rw [hformula w, hformula z]
  congr 1
  have hw := congrArg J (hformula w)
  have hz := congrArg J (hformula z)
  rw [map_smul] at hw hz
  rw [hw, hz] at h
  exact mul_right_cancel₀ hv h


open ModelData AtlasData BundleOperationsData CovectorData ExteriorData
  DeRhamData MayerVietorisData CompactSupportData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData Set

/-- One-dimensionality of the compact cohomology of an open neighborhood
suffices for ambient local exactness. The ambient functional is nonzero by
an actual unit-integral compact form supported in that neighborhood. -/
theorem local_exactness_of_cohomology_equiv
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S}
    {B : ∀ k, FormBundle C k} {K : Calculus C B}
    (D : CompactCalculus K ⊤) (o : Orientation S)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (hb : intrinsicBoundary S = ∅) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M).Nonempty) (E : CompactCalculus K U)
    (e : E.Cohomology n ≃ₗ[ℝ] ℝ)
    (ω : D.complex.Obj n)
    (hsupp : sectionSupport (D.inclusion.map n ω).val ⊆ U)
    (hω : integralLinear D o I hI ω = 0) : ω ∈ D.complex.exact n := by
  let f := CompactSupportResults.extension (show U ≤ ⊤ from le_top) E D
  let J : E.Cohomology n →ₗ[ℝ] ℝ :=
    (cohomologyIntegral D o I hI hb).comp (f.onH n)
  have hf (x : E.complex.Obj n) (y : D.complex.Obj n)
      (hxy : E.inclusion.map n x = D.inclusion.map n y) : f.map n x = y := by
    apply D.injective n
    exact (CompactSupportResults.extension_field (le_top : U ≤ ⊤) E D n x).trans hxy
  have hJ (x : E.complex.closed n) (y : D.complex.Obj n)
      (hxy : E.inclusion.map n x.val = D.inclusion.map n y) :
      J (E.complex.classOf n x) = integralLinear D o I hI y := by
    change cohomologyIntegral D o I hI hb (f.onH n (E.complex.classOf n x)) = _
    rw [ChainMap.onH_class]
    change integralLinear D o I hI (f.map n x.val) = _
    rw [hf x.val y hxy]
  obtain ⟨β, hβsupport, hβintegral⟩ := unit_integral_in_open D o I hI hb U hU
  obtain ⟨b, hbfield⟩ := (E.range n (D.inclusion.map n β)).mp
    ⟨(CompactSupportResults.inclusion_support D n β).1, hβsupport⟩
  let bclosed : E.complex.closed n := ⟨b, top_closed E b⟩
  have hnonzero : J (E.complex.classOf n bclosed) ≠ 0 := by
    rw [hJ bclosed β hbfield, hβintegral]
    exact one_ne_zero
  have hJinj : Function.Injective J :=
    linearMap_injective_of_equiv_real e J (E.complex.classOf n bclosed) hnonzero
  obtain ⟨x, hxfield⟩ := (E.range n (D.inclusion.map n ω)).mp
    ⟨(CompactSupportResults.inclusion_support D n ω).1, hsupp⟩
  let xclosed : E.complex.closed n := ⟨x, top_closed E x⟩
  have hxzero : E.complex.classOf n xclosed = 0 := by
    apply hJinj
    rw [hJ xclosed ω hxfield, hω, map_zero]
  have hxexact : x ∈ E.complex.exact n :=
    (E.complex.class_zero_iff n xclosed).mp hxzero
  have hex := f.maps_exact n x hxexact
  rw [← hf x ω hxfield]
  exact hex

end SmoothManifolds.OrientedTopDegreeResults



set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.OrientedTopDegreeResults.LocalTransport
open ModelData AtlasData MapData TangentData DifferentialData TangentBundleData
  BundleOperationsData CovectorData ExteriorData DeRhamData MayerVietorisData
  CompactSupportData EuclideanCompactData Set
universe u

/-- Compact forms supported in a Euclidean neighborhood have one-dimensional
cohomology in top degree. The equivalence uses the full complexes and genuine
inverse tangent maps, so it imposes no coordinate condition on the forms. -/
theorem local_compact_cohomology_equiv {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (U : TopologicalSpace.Opens M)
    (P : Presentation n U) (hi : IsSmoothMap P.manifold S Subtype.val)
    (hr : ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen)
      P.manifold.smoothStructure.val id)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k) (K : Calculus C B)
    (E : CompactCalculus K U) : Nonempty (E.Cohomology n ≃ₗ[ℝ] ℝ) := by
  classical
  obtain ⟨R,hR,hRi,hf,hg,E₀,A₀,hE,hA,hG⟩ :=
    local_differential_data S U U.isOpen P.manifold hi hr
  obtain ⟨A⟩ := BundleOperations.exists_cotangent P.manifold
  let F : ∀ k, FormBundle A k := fun k =>
    Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨J,⟨G⟩⟩ := CompactSupportResults.complex_exists P.manifold A F
  let L : (q : U) → TangentSpace P.manifold q ≃ₗ[ℝ] TangentSpace S q.val :=
    fun q => (A₀ q).trans (E₀ q)
  have hL : ∀ q, IsDifferential P.manifold S Subtype.val q (L q).toLinearMap := by
    intro q
    exact differential_comp P.manifold R S id Subtype.val hf hRi q
      (A₀ q).toLinearMap (E₀ q).toLinearMap (hA q) (hE q)
  have hpush : ∀ (k : ℕ) (α : Field P.manifold k), IsForm (F k) α →
      IsRestrictedForm (B k) U (fun q => FormPullbackData.fiberPullback
        (V := TangentSpace S q.val) (W := TangentSpace P.manifold q)
        k (L q).symm.toLinearMap (α q)) := by
    intro k α hα
    exact restricted_form_of_local_form S U P.manifold R hR hRi hg C A E₀ A₀
      hE hG k (B k) (F k) α hα
  let f := supportedPullChain U P.manifold A F J E G hi L hL
  have hbij : ∀ k, Function.Bijective (f.map k) :=
    supportedPullChain_bijective U P.manifold A F J E G hi L hL hpush
  obtain ⟨_,_,⟨eP,_⟩,_⟩ := EuclideanCompactResults.calculation P A F J G
  exact ⟨(cohomologyEquiv f hbij n).trans eP⟩

end SmoothManifolds.OrientedTopDegreeResults.LocalTransport

namespace SmoothManifolds.OrientedTopDegreeResults
open ModelData AtlasData BundleOperationsData CovectorData ExteriorData
  DeRhamData MayerVietorisData CompactSupportData OrientationData
  LocalIntegrationData GlobalIntegrationData BoundaryData Set
universe u

/-- Integration is the isomorphism, on every connected boundary-free manifold.
Local unit classes are compared by overlaps and connectedness, then a finite
partition on each compact support gives the global representative formula. -/
theorem top_degree :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u} := by
  intro n a M _ _ S hb o C B K D I hI
  apply integration_iso_of_pointwise_exactness D o I hI hb
  intro p
  obtain ⟨e,hpe,_,_,P,hi,_,hr⟩ :=
    LocalTransport.euclidean_presentation_neighborhood S hb p univ isOpen_univ (mem_univ p)
  let U : TopologicalSpace.Opens M := ⟨e.source,e.open_source⟩
  let E : CompactCalculus K U := CompactSupportResults.supportedCalculus K U
  obtain ⟨eU⟩ := LocalTransport.local_compact_cohomology_equiv S U P hi hr C B K E
  refine ⟨U,hpe,?_⟩
  intro ω hs hω
  exact local_exactness_of_cohomology_equiv D o I hI hb U ⟨p,hpe⟩ E eU ω hs hω

/-- Exactness here means a primitive in the compact complex, including degree zero. -/
theorem exact_iff_integral_zero :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u} :=
  exact_iff_of_top_degree top_degree

/-- On a compact manifold the same integral identifies ordinary top cohomology. -/
theorem compact_top_degree :
    Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u} :=
  compact_top_degree_of_top_degree top_degree

end SmoothManifolds.OrientedTopDegreeResults
