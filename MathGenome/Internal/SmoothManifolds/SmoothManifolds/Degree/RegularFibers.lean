import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Degree.RegularFibers
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.InteriorInverse
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch04.Sard
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Integration.Global
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorDerivative
import Mathlib.MeasureTheory.Integral.Bochner.Set
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Topology
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Connected.LocallyConnected

import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.OrientedTopDegree
/-! Conditional derivation for M12.01. No unproved oriented-top-degree
implementation is imported. All uses of that interface are explicit parameters. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Topology BigOperators

namespace SmoothManifolds.DegreeResults
open ModelData AtlasData MapData MapClassData FiniteRegularityData TangentData
  DifferentialData CovectorData BundleOperationsData ExteriorData FormPullbackData
  OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  BoundaryData DeRhamData CompactSupportData DegreeData Set Filter
universe u v

/-- At a submersion point in equal dimensions, the inverse theorem gives a
neighborhood on which the original function is injective. No sign data or
positive-dimensional hypothesis is needed. -/
theorem regular_point_inverse {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (p : M) (hp : IsSubmersionAt S T f p) :
    ∃ e : OpenPartialHomeomorph M N, p ∈ e.source ∧ EqOn e f e.source ∧
      ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val f e.source ∧
      ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target := by
  obtain ⟨F, G, L, hL, hsurj⟩ := hp.2
  letI := F.group
  letI := F.module
  letI := G.group
  letI := G.module
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  have hlin := MapClasses.differential_chart_invariants S T f p F G c d hc hd hpc hpd L hL
  have hbij : Function.Bijective L := by
    refine ⟨hlin.2.1.mpr ?_, hsurj⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := Euclidean n) (V₂ := Euclidean n) rfl).mpr
      (hlin.2.2.mp hsurj)
  have hpi : p ∈ manifoldInterior S := by
    rw [← compl_intrinsicBoundary S, hS]
    simp
  have hfpi : f p ∈ manifoldInterior T := by
    rw [← compl_intrinsicBoundary T, hT]
    simp
  obtain ⟨e, he, _, _, heq, hsm, hsym⟩ :=
    InteriorInverse.interior_inverse (⊤ : ℕ∞) (by simp) S T f hf p hpi hfpi F G L hL hbij
  exact ⟨e, he, heq, hsm, hsym⟩

/-- A regular fiber is a discrete subset, also when it is empty. -/
theorem regular_fiber_discrete {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (y : N) (hy : IsRegularValue S T f y) :
    IsDiscrete (f ⁻¹' {y}) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro p hp
  obtain ⟨e, he, heq, _, _⟩ := regular_point_inverse S T f hf hS hT p (hy p hp)
  refine ⟨e.source, e.open_source, ?_⟩
  ext x
  constructor
  · rintro ⟨hx, hxy⟩
    apply mem_singleton_iff.mpr
    apply e.injOn hx he
    rw [heq hx, heq he]
    exact hxy.trans hp.symm
  · intro hx
    obtain rfl := mem_singleton_iff.mp hx
    exact ⟨he, hp⟩

/-- Compactness of the source and closedness of a fiber turn discreteness into
finiteness. Target separation is provided by its original manifold structure. -/
theorem regular_fiber_finite_proof :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_fiber_finiteType.{u} := by
  intro n a b M N _ _ _ S T f hf hS hT y hy
  letI := T.topologicalManifold.hausdorff
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  exact ((isClosed_singleton.preimage hcont).isCompact).finite
    (regular_fiber_discrete S T f hf hS hT y hy)

/-- Sard gives a regular value in positive dimension. The upstream zero-target
Sard statement proves that every value is regular in dimension zero. -/
theorem regular_value_exists_proof :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_value_existsType.{u} := by
  intro n a b M N _ _ _ S T f hf
  cases n with
  | zero =>
    obtain ⟨y⟩ := ‹Nonempty N›
    refine ⟨y, ?_⟩
    intro p hp
    by_contra hcrit
    have hz := Sard.criticalValues_target_zero S T f hf
    have hm : y ∈ SardData.criticalValues S T f := ⟨p, hcrit, hp⟩
    rw [hz] at hm
    exact hm
  | succ n =>
    exact (Sard.regularValues_dense S T f hf (Nat.succ_pos n)).nonempty

/-- A tangent differential at a regular point is genuinely invertible. -/
theorem regular_differential_bijective {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (p : M) (hp : IsSubmersionAt S T f p)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) : Function.Bijective L := by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨E, hE⟩ := FiniteRegularity.exists_smooth_chart_coordinates S p c hc hpc
  obtain ⟨D, hD⟩ := FiniteRegularity.exists_smooth_chart_coordinates T (f p) d hd hpd
  letI : FiniteDimensional ℝ (TangentSpace S p) := E.symm.finiteDimensional
  letI : FiniteDimensional ℝ (TangentSpace T (f p)) := D.symm.finiteDimensional
  have hsurj := (MapClasses.smooth_tangent_invariants S T f hf p L hL).2.2.mp hp
  have hdim : Module.finrank ℝ (TangentSpace S p) =
      Module.finrank ℝ (TangentSpace T (f p)) := E.finrank_eq.trans D.finrank_eq.symm
  have hinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℝ) (V := TangentSpace S p) (V₂ := TangentSpace T (f p)) hdim (f := L)).mpr hsurj
  exact ⟨hinj, hsurj⟩

/-- The integer sign agrees with the established determinant-ray convention
whenever the differential is represented by a linear equivalence. -/
theorem differentialSign_eq {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold n b N} {f : M → N}
    (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)) (p : M) :
    (differentialSign o q p (E p).toLinearMap : ℝ) =
      signValue (orientationSign o q E p) := by
  classical
  have he : LinearEquiv.ofBijective (E p).toLinearMap (E p).bijective = E p := by
    ext v
    rfl
  unfold differentialSign
  rw [dif_pos (show Function.Bijective (E p).toLinearMap from (E p).bijective), he]
  unfold orientationSign
  split_ifs <;> simp [signValue]

/-- A nonzero integer satisfying the regular-fiber formula forces
surjectivity. This deduction needs no chosen regular value or Sard invocation. -/
theorem surjective_of_fiberFormula {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (o : Orientation S) (q : Orientation T)
    (d : ℤ) (hd : FiberFormula f o q d) (hd0 : d ≠ 0) : Function.Surjective f := by
  intro y
  by_contra hy
  have hreg : IsRegularValue S T f y := by
    intro p hp
    exact (hy ⟨p, hp⟩).elim
  obtain ⟨hfin, hsum⟩ := hd y hreg
  have hemp : f ⁻¹' {y} = ∅ := by
    ext p
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro hp
    exact hy ⟨p, hp⟩
  have hefin : hfin.toFinset = ∅ := by
    ext p
    simp [hemp]
  have heq := hsum (differential S T f hf) (differential_spec S T f hf)
  rw [hefin, Finset.sum_empty] at heq
  exact hd0 heq

/-- All permitted cotangent realizations give the same actual coefficient
functions, because intrinsic tangent chart coordinates are unique. -/
theorem coefficients_change_cotangent {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C A : CotangentBundle S) (k : ℕ) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (ω : Field S k) (p : c.source) (j : Index n k) :
    coefficients C k c hc ω p j = coefficients A k c hc ω p j := by
  have hcoord : C.tangent.fiberCoordinates.equiv c hc p.val p.property =
      A.tangent.fiberCoordinates.equiv c hc p.val p.property :=
    TangentBundle.chartCoordinates_unique
      (C.tangent.fiberCoordinates.isCoordinates c hc p.val p.property)
      (A.tangent.fiberCoordinates.isCoordinates c hc p.val p.property)
  simp only [coefficients, hcoord]

/-- Changing a representation of the genuine exterior bundle does not change
which original fields are smooth. -/
theorem smooth_form_change {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C A : CotangentBundle S) {k : ℕ} (B : FormBundle C k) (E : FormBundle A k)
    (ω : Field S k) (hω : IsForm B ω) : IsForm E ω := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients A k E ω).mpr
  intro c hc j
  have h := (ExteriorAlgebraResults.smooth_iff_coefficients C k B ω).mp hω c hc j
  simpa only [coefficients_change_cotangent C A] using h

/-- Every top form is closed, including degree zero on a zero-manifold. -/
def topClosed {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}
    (K : Calculus C B) (ω : K.forms n) : K.closed n :=
  ⟨ω, by
    change K.d n ω = 0
    apply Subtype.ext
    funext p
    exact ExteriorAlgebraResults.fields_above_dimension C (n+1) (Nat.lt_succ_self n)
      (K.D n ω.val) p⟩

/-- A linear endomorphism of ℝ is multiplication by its value at one. -/
theorem real_linear_scalar (g : ℝ →ₗ[ℝ] ℝ) (x : ℝ) : g x = g 1 * x := by
  have h := g.map_smul x (1 : ℝ)
  simpa only [smul_eq_mul, mul_one, mul_comm] using h

/-- The real scalar follows by conjugating the actual induced pullback by
the two integration isomorphisms. Its dependence on the top-degree theorem is
explicit and does not import that unproved implementation. -/
theorem real_scalar_proof
    (htop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.real_scalarType.{u} := by
  intro n a b M N _ _ _ _ _ _ S T f hf hS hT o q I J hI hJ
  obtain ⟨C⟩ := BundleOperations.exists_cotangent S
  obtain ⟨A⟩ := BundleOperations.exists_cotangent T
  let B : ∀ k, FormBundle C k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle C k)
  let E : ∀ k, FormBundle A k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  obtain ⟨P⟩ := DeRhamResults.complex_exists A E
  obtain ⟨eM, heM⟩ := htop S hS o C B K I hI
  obtain ⟨eN, heN⟩ := htop T hT q A E P J hJ
  let L₀ := differential S T f hf
  have hL₀ : ∀ p, IsDifferential S T f p (L₀ p) := differential_spec S T f hf
  obtain ⟨F, hF⟩ := DeRhamResults.pullback_exists S T C A B E K P f hf L₀ hL₀
  let g : ℝ →ₗ[ℝ] ℝ := eM.toLinearMap.comp ((F n).comp eN.symm.toLinearMap)
  refine ⟨g 1, ?_⟩
  intro A' E' ω L hL
  have hLL : L = L₀ := by
    funext p
    exact (differential_exists S T f hf p).unique (hL p) (hL₀ p)
  subst L
  have hω : ω.field ∈ P.forms n := (P.mem_forms n ω.field).mpr
    (smooth_form_change A' A E' (E n) ω.field ω.smooth)
  let α := topClosed P ⟨ω.field, hω⟩
  obtain ⟨β, hβ, hFβ⟩ := hF n α
  obtain ⟨η, hη, heη⟩ := heN α
  obtain ⟨ξ, hξ, heξ⟩ := heM β
  refine ⟨η, ξ, hη, hξ.trans hβ, ?_⟩
  calc
    I ξ = eM (K.classOf n β) := heξ.symm
    _ = eM (F n (P.classOf n α)) := congrArg eM hFβ.symm
    _ = g (eN (P.classOf n α)) := by simp [g]
    _ = g 1 * eN (P.classOf n α) := real_linear_scalar g _
    _ = g 1 * J η := congrArg (fun z => g 1 * z) heη

/-- Connected zero-manifolds are single points; nonemptiness is already part
of ConnectedSpace. Discreteness is obtained from the actual chart cover. -/
theorem zero_connected_subsingleton {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] (S : SmoothManifold 0 a M) : Subsingleton M := by
  letI := LocalIntegrationResults.zero_manifold_discrete S
  exact subsingleton_of_preconnected_totallyDisconnected

/-- Signed evaluation on a connected zero-manifold. -/
theorem zero_integral_evaluation {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [ConnectedSpace M] (S : SmoothManifold 0 a M)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (ω : CompactTopForm S) (p : M) : I ω = zeroSign o p * zeroCoefficient ω.field p := by
  letI := zero_connected_subsingleton S
  rw [GlobalIntegrationResults.zero_dimension S o I hI ω]
  unfold zeroIntegral
  apply finsum_eq_single _ p
  intro x hx
  exact (hx (Subsingleton.elim x p)).elim

/-- The zeroth exterior pullback is exactly pullback of scalar values, for
all fiber maps, with no choice of tangent bases. -/
theorem zero_pullback_coefficient {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold 0 a M) (T : SmoothManifold 0 b N) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (ω : Field T 0) (p : M) :
    zeroCoefficient (pullbackField S T f L ω) p = zeroCoefficient ω (f p) := by
  exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality (L p).dualMap) (ω (f p))

theorem zeroSign_mul_self {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 a M} (o : Orientation S) (p : M) :
    zeroSign o p * zeroSign o p = 1 := by
  unfold zeroSign
  split_ifs <;> norm_num

/-- In dimension zero the scalar is the product of the two prescribed signs,
with the target sign inverted by squaring to one. -/
theorem zero_integral_pullback {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [ConnectedSpace M] [ConnectedSpace N]
    (S : SmoothManifold 0 a M) (T : SmoothManifold 0 b N) (f : M → N)
    (o : Orientation S) (q : Orientation T)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (η : CompactTopForm T) (ξ : CompactTopForm S)
    (hξ : ξ.field = pullbackField S T f L η.field) (p : M) :
    I ξ = (zeroSign o p * zeroSign q (f p)) * J η := by
  rw [zero_integral_evaluation S o I hI ξ p,
    zero_integral_evaluation T q J hJ η (f p), hξ,
    zero_pullback_coefficient]
  calc
    zeroSign o p * zeroCoefficient η.field (f p) =
        zeroSign o p * ((zeroSign q (f p) * zeroSign q (f p)) *
          zeroCoefficient η.field (f p)) := by rw [zeroSign_mul_self, one_mul]
    _ = (zeroSign o p * zeroSign q (f p)) *
        (zeroSign q (f p) * zeroCoefficient η.field (f p)) := by ring

/-- Every field on a one-point manifold is a compact continuous top form. -/
def pointTopForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    [ConnectedSpace M] [CompactSpace M] (S : SmoothManifold 0 a M)
    (ω : Field S 0) : CompactTopForm S where
  field := ω
  continuous := by
    letI := LocalIntegrationResults.zero_manifold_discrete S
    intro K c hc
    exact continuous_of_discreteTopology
  compact_support := isClosed_closure.isCompact

/-- All smooth zero-forms satisfy the signed scalar formula, including the
negative orientation on either source or target. -/
theorem zero_integral_formula {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [ConnectedSpace M] [ConnectedSpace N]
    [CompactSpace M] [CompactSpace N]
    (S : SmoothManifold 0 a M) (T : SmoothManifold 0 b N) (f : M → N)
    (o : Orientation S) (q : Orientation T)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J) (p : M) :
    IntegralFormula S T f I J (zeroSign o p * zeroSign q (f p)) := by
  intro C B ω L _hL
  exact ⟨pointTopForm T ω.field, pointTopForm S (pullbackField S T f L ω.field),
    rfl, rfl, zero_integral_pullback S T f o q I J hI hJ L _ _ rfl p⟩

/-- In Λ⁰ every determinant map fixes the canonical unit; its relative ray
sign is exactly the product of the source and target zero-dimensional signs. -/
theorem differentialSign_zero {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold 0 a M} {T : SmoothManifold 0 b N} {f : M → N}
    (o : Orientation S) (q : Orientation T) (p : M)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) (hL : Function.Bijective L) :
    (differentialSign o q p L : ℝ) = zeroSign o p * zeroSign q (f p) := by
  classical
  let v := (exteriorPower.zeroEquiv ℝ (TangentSpace S p)).symm 1
  let w := (exteriorPower.zeroEquiv ℝ (TangentSpace T (f p))).symm 1
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (exteriorPower.zeroEquiv ℝ (TangentSpace S p)) h
    simpa [v] using this
  have hw : w ≠ 0 := by
    intro h
    have := congrArg (exteriorPower.zeroEquiv ℝ (TangentSpace T (f p))) h
    simpa [w] using this
  let A := determinantMap (V := TangentSpace S p) (W := TangentSpace T (f p))
    0 (LinearEquiv.ofBijective L hL)
  have hco : (LinearEquiv.ofBijective L hL).toLinearMap = L := by
    ext x
    rfl
  have hAv : A v = w := by
    apply (exteriorPower.zeroEquiv ℝ (TangentSpace T (f p))).injective
    have h := LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality (R := ℝ)
      (M := TangentSpace S p) (N := TangentSpace T (f p)) L) v
    simpa [A, determinantMap, hco, v, w] using h
  let r := rayOfNeZero ℝ v hv
  let s := rayOfNeZero ℝ w hw
  have hAr : Module.Ray.map A r = s := by
    change Module.Ray.map A (rayOfNeZero ℝ v hv) = rayOfNeZero ℝ w hw
    simpa only [hAv] using Module.Ray.map_apply A v hv
  have hr : o.val p = r ∨ o.val p = -r :=
    OrientationProducts.rays_eq_or_neg (OrientationProducts.determinantLine_finrank S p) _ _
  have hs : q.val (f p) = s ∨ q.val (f p) = -s :=
    OrientationProducts.rays_eq_or_neg (OrientationProducts.determinantLine_finrank T (f p)) _ _
  have hMr : IsPositive (o.val p) v ↔ o.val p = r := by
    constructor
    · exact fun h => h.2.symm
    · exact fun h => ⟨hv, h.symm⟩
  have hNs : IsPositive (q.val (f p)) w ↔ q.val (f p) = s := by
    constructor
    · exact fun h => h.2.symm
    · exact fun h => ⟨hw, h.symm⟩
  have hnr := Module.Ray.ne_neg_self r
  have hns := Module.Ray.ne_neg_self s
  simp only [differentialSign, dif_pos hL]
  dsimp only [A] at hAr
  change _ = (if IsPositive (o.val p) v then (1 : ℝ) else -1) *
    (if IsPositive (q.val (f p)) w then (1 : ℝ) else -1)
  rw [hMr, hNs]
  rcases hr with hr | hr <;> rcases hs with hs | hs <;>
    simp [hr, hs, hAr, hnr, hns, Ne.symm hnr, Ne.symm hns]

/-- The entire degree theorem in dimension zero, including the integer count
and its signed-evaluation normalization. -/
theorem zero_dimension_proof :
    Specs.SmoothManifolds.Degree.RegularFibers.zero_dimensionType.{u} := by
  intro a b M N _ _ _ _ _ _ S T f hf o q I J hI hJ
  letI := zero_connected_subsingleton S
  letI := zero_connected_subsingleton T
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro p
  let L₀ := differential S T f hf
  have hL₀ : ∀ p, IsDifferential S T f p (L₀ p) := differential_spec S T f hf
  have hreg : IsRegularValue S T f (f p) := by
    intro x hx
    by_contra hcrit
    have hm : f p ∈ SardData.criticalValues S T f := ⟨x, hcrit, hx⟩
    rw [Sard.criticalValues_target_zero S T f hf] at hm
    exact hm
  have hbij := regular_differential_bijective S T f hf p (hreg p rfl) (L₀ p) (hL₀ p)
  let d := differentialSign o q p (L₀ p)
  have hd : (d : ℝ) = zeroSign o p * zeroSign q (f p) :=
    differentialSign_zero o q p (L₀ p) hbij
  refine ⟨d, ⟨?_, ?_⟩, hd⟩
  · rw [hd]
    exact zero_integral_formula S T f o q I J hI hJ p
  · intro y hy
    have hset : f ⁻¹' {y} = {p} := by
      ext x
      simp [Subsingleton.elim x p, Subsingleton.elim (f p) y]
    have hfin : (f ⁻¹' {y}).Finite := hset ▸ finite_singleton p
    refine ⟨hfin, ?_⟩
    intro L hL
    have hLp : L p = L₀ p := (differential_exists S T f hf p).unique (hL p) (hL₀ p)
    have hto : hfin.toFinset = {p} := by ext x; simp [hset]
    rw [hto, Finset.sum_singleton, hLp]

/-- A compact complement cannot produce additional sheets over a sufficiently
small neighborhood of the value. This includes U = ∅ and an empty fiber. -/
theorem compact_preimage_neighborhood {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M] [T2Space N]
    (f : M → N) (hf : Continuous f) (y : N) (U : Set M) (hU : IsOpen U)
    (hcover : f ⁻¹' {y} ⊆ U) :
    ∃ V : Set N, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U := by
  let V := (f '' Uᶜ)ᶜ
  have hclosed : IsClosed (f '' Uᶜ) := (hU.isClosed_compl.isCompact.image hf).isClosed
  refine ⟨V, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hcover hxy)
  · intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

/-- A regular value has one common open neighborhood whose ENTIRE preimage
is the disjoint union of its inverse sheets. The neighborhood can be chosen
inside any prescribed open neighborhood of the value. Indexing by the actual
fiber includes an empty family when the value lies outside the image. -/
theorem regular_value_sheets {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (y : N) (hy : IsRegularValue S T f y)
    (W : Set N) (hW : IsOpen W) (hyW : y ∈ W) :
    ∃ (V : Set N) (e : (f ⁻¹' {y}) → OpenPartialHomeomorph M N),
      IsOpen V ∧ y ∈ V ∧ V ⊆ W ∧
      (∀ p, p.val ∈ (e p).source ∧ (e p).target = V ∧
        EqOn (e p) f (e p).source ∧
        ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val f (e p).source ∧
        ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val (e p).symm V) ∧
      Pairwise (fun p r => Disjoint (e p).source (e r).source) ∧
      f ⁻¹' V = ⋃ p, (e p).source := by
  classical
  letI := S.topologicalManifold.hausdorff
  letI := T.topologicalManifold.hausdorff
  have hfin := regular_fiber_finite_proof S T f hf hS hT y hy
  letI := hfin.fintype
  obtain ⟨U, hU, hdisj⟩ := hfin.t2_separation
  have hinv (p : f ⁻¹' {y}) :=
    regular_point_inverse S T f hf hS hT p.val (hy p.val p.property)
  choose e₀ hp₀ heq₀ hsm₀ hsym₀ using hinv
  let e₁ : (f ⁻¹' {y}) → OpenPartialHomeomorph M N :=
    fun p => (e₀ p).restrOpen (U p.val) (hU p.val).2
  have hp₁ (p : f ⁻¹' {y}) : p.val ∈ (e₁ p).source :=
    ⟨hp₀ p, (hU p.val).1⟩
  have heq₁ (p : f ⁻¹' {y}) : EqOn (e₁ p) f (e₁ p).source :=
    fun x hx => heq₀ p hx.1
  have hyt (p : f ⁻¹' {y}) : y ∈ (e₁ p).target := by
    have h := (e₁ p).map_source (hp₁ p)
    rw [heq₁ p (hp₁ p), show f p.val = y from p.property] at h
    exact h
  let O : Set M := ⋃ p, (e₁ p).source
  have hO : IsOpen O := isOpen_iUnion (fun p => (e₁ p).open_source)
  have hcover : f ⁻¹' {y} ⊆ O := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp₁ ⟨x, hx⟩⟩
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  obtain ⟨V₀, hV₀, hyV₀, hpre₀⟩ := compact_preimage_neighborhood f hcont y O hO hcover
  let V : Set N := (V₀ ∩ W) ∩ ⋂ p, (e₁ p).target
  have hV : IsOpen V :=
    (hV₀.inter hW).inter (isOpen_iInter_of_finite (fun p => (e₁ p).open_target))
  have hyV : y ∈ V := ⟨⟨hyV₀, hyW⟩, mem_iInter.mpr hyt⟩
  have hVt (p : f ⁻¹' {y}) : V ⊆ (e₁ p).target := fun z hz => mem_iInter.mp hz.2 p
  let e : (f ⁻¹' {y}) → OpenPartialHomeomorph M N :=
    fun p => (e₁ p).trans (OpenPartialHomeomorph.ofSet V hV)
  have hes (p : f ⁻¹' {y}) : (e p).source ⊆ (e₁ p).source := fun x hx => hx.1
  have het (p : f ⁻¹' {y}) : (e p).target = V := by
    change V ∩ (id ⁻¹' (e₁ p).target) = V
    exact inter_eq_left.mpr (hVt p)
  have heq (p : f ⁻¹' {y}) : EqOn (e p) f (e p).source :=
    fun x hx => heq₁ p hx.1
  refine ⟨V, e, hV, hyV, (fun z hz => hz.1.2), ?_, ?_, ?_⟩
  · intro p
    refine ⟨?_, het p, heq p, ?_, ?_⟩
    · change p.val ∈ (e₁ p).source ∧ (e₁ p) p.val ∈ V
      exact ⟨hp₁ p, by rwa [heq₁ p (hp₁ p), p.property]⟩
    · intro x hx
      exact hsm₀ p x hx.1.1
    · intro z hz
      exact hsym₀ p z (hVt p hz).1
  · intro p r hpr
    apply (hdisj p.property r.property (fun h => hpr (Subtype.ext h))).mono
    · exact fun x hx => hx.1.2
    · exact fun x hx => hx.1.2
  · ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp (hpre₀ hx.1.1)
      exact mem_iUnion.mpr ⟨p, hp, by change (e₁ p) x ∈ V; rwa [heq₁ p hp]⟩
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      change f x ∈ V
      have hm := (e p).map_source hp
      rw [het p, heq p hp] at hm
      exact hm

/-- A regular value admits connected disjoint local inverse sheets inside
arbitrary prescribed source and target neighborhoods. Empty fibers give an
empty family, with a nonempty connected target neighborhood disjoint from the
image. -/
theorem regular_value_sheets_within {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (y : N) (hy : IsRegularValue S T f y)
    (W : Set N) (hW : IsOpen W) (hyW : y ∈ W)
    (A : (f ⁻¹' {y}) → Set M) (hA : ∀ p, IsOpen (A p))
    (hpA : ∀ p, p.val ∈ A p) :
    ∃ (V : Set N) (e : (f ⁻¹' {y}) → OpenPartialHomeomorph M N),
      IsOpen V ∧ y ∈ V ∧ IsConnected V ∧ V ⊆ W ∧
      (∀ p, p.val ∈ (e p).source ∧ (e p).target = V ∧
        (e p).source ⊆ A p ∧ IsConnected (e p).source ∧
        EqOn (e p) f (e p).source ∧
        ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val f (e p).source ∧
        ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val (e p).symm V) ∧
      Pairwise (fun p r => Disjoint (e p).source (e r).source) ∧
      f ⁻¹' V = ⋃ p, (e p).source := by
  classical
  letI := S.topologicalManifold.hausdorff
  letI := T.topologicalManifold.hausdorff
  letI := SmoothManifolds.TopologicalManifold.locallyPathConnectedSpace T.topologicalManifold
  have hfin := regular_fiber_finite_proof S T f hf hS hT y hy
  letI := hfin.fintype
  obtain ⟨U, hU, hdisj⟩ := hfin.t2_separation
  have hinv (p : f ⁻¹' {y}) :=
    regular_point_inverse S T f hf hS hT p.val (hy p.val p.property)
  choose e₀ hp₀ heq₀ hsm₀ hsym₀ using hinv
  let e₁ : (f ⁻¹' {y}) → OpenPartialHomeomorph M N :=
    fun p => (e₀ p).restrOpen (U p.val ∩ A p) ((hU p.val).2.inter (hA p))
  have hp₁ (p : f ⁻¹' {y}) : p.val ∈ (e₁ p).source :=
    ⟨hp₀ p, (hU p.val).1, hpA p⟩
  have heq₁ (p : f ⁻¹' {y}) : EqOn (e₁ p) f (e₁ p).source :=
    fun x hx => heq₀ p hx.1
  have hyt (p : f ⁻¹' {y}) : y ∈ (e₁ p).target := by
    have h := (e₁ p).map_source (hp₁ p)
    rw [heq₁ p (hp₁ p), show f p.val = y from p.property] at h
    exact h
  let O : Set M := ⋃ p, (e₁ p).source
  have hO : IsOpen O := isOpen_iUnion (fun p => (e₁ p).open_source)
  have hcover : f ⁻¹' {y} ⊆ O := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hp₁ ⟨x, hx⟩⟩
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).1)
  obtain ⟨V₀, hV₀, hyV₀, hpre₀⟩ := compact_preimage_neighborhood f hcont y O hO hcover
  let V₁ : Set N := (V₀ ∩ W) ∩ ⋂ p, (e₁ p).target
  have hV₁ : IsOpen V₁ :=
    (hV₀.inter hW).inter (isOpen_iInter_of_finite (fun p => (e₁ p).open_target))
  have hyV₁ : y ∈ V₁ := ⟨⟨hyV₀, hyW⟩, mem_iInter.mpr hyt⟩
  let V : Set N := connectedComponentIn V₁ y
  have hsub : V ⊆ V₁ := connectedComponentIn_subset V₁ y
  have hV : IsOpen V := hV₁.connectedComponentIn
  have hyV : y ∈ V := mem_connectedComponentIn hyV₁
  have hconn : IsConnected V := isConnected_connectedComponentIn_iff.mpr hyV₁
  have hVt (p : f ⁻¹' {y}) : V ⊆ (e₁ p).target :=
    fun z hz => mem_iInter.mp (hsub hz).2 p
  let e : (f ⁻¹' {y}) → OpenPartialHomeomorph M N :=
    fun p => (e₁ p).trans (OpenPartialHomeomorph.ofSet V hV)
  have hes (p : f ⁻¹' {y}) : (e p).source ⊆ (e₁ p).source := fun x hx => hx.1
  have het (p : f ⁻¹' {y}) : (e p).target = V := by
    change V ∩ (id ⁻¹' (e₁ p).target) = V
    exact inter_eq_left.mpr (hVt p)
  have heq (p : f ⁻¹' {y}) : EqOn (e p) f (e p).source :=
    fun x hx => heq₁ p hx.1
  refine ⟨V, e, hV, hyV, hconn, (fun z hz => (hsub hz).1.2), ?_, ?_, ?_⟩
  · intro p
    refine ⟨?_, het p, ?_, ?_, heq p, ?_, ?_⟩
    · change p.val ∈ (e₁ p).source ∧ (e₁ p) p.val ∈ V
      exact ⟨hp₁ p, by rwa [heq₁ p (hp₁ p), p.property]⟩
    · exact fun x hx => hx.1.2.2
    · have hh : IsConnected ((e p).symm '' (e p).target) :=
        (het p ▸ hconn).image _ (e p).continuousOn_symm
      rwa [(e p).symm_image_target_eq_source] at hh
    · intro x hx
      exact hsm₀ p x hx.1.1
    · intro z hz
      exact hsym₀ p z (hVt p hz).1
  · intro p r hpr
    apply (hdisj p.property r.property (fun h => hpr (Subtype.ext h))).mono
    · exact fun x hx => hx.1.2.1
    · exact fun x hx => hx.1.2.1
  · ext x
    constructor
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp (hpre₀ (hsub hx).1.1)
      exact mem_iUnion.mpr ⟨p, hp, by change (e₁ p) x ∈ V; rwa [heq₁ p hp]⟩
    · intro hx
      obtain ⟨p, hp⟩ := mem_iUnion.mp hx
      change f x ∈ V
      have hm := (e p).map_source hp
      rw [het p, heq p hp] at hm
      exact hm



open private scalar_comp_at from MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Differential

/-- An actual smooth partial inverse forces an invertible differential at every point of its source. -/
theorem local_inverse_differential_bijective {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (e : OpenPartialHomeomorph M N) (he : EqOn e f e.source)
    (hinv : ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target)
    (p : M) (hp : p ∈ e.source)
    (L : TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : IsDifferential S T f p L) : Function.Bijective L := by
  have hfp : f p ∈ e.target := by rw [← he hp]; exact e.map_source hp
  have hleft : e.symm (f p) = p := by rw [← he hp]; exact e.left_inv hp
  have hi : Function.Injective L := by
    intro v w hvw
    apply Subtype.ext
    apply LinearMap.ext
    intro k
    obtain ⟨r, hr, hrk⟩ := (mem_smoothGermAlgebra_iff S p k.val).mp k.property
    have hr' : PartitionData.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val r
        (e.symm (f p)) := hleft.symm ▸ hr
    let j : SmoothGerm T (f p) := ⟨Germ.ofFun (r ∘ e.symm),
      Algebra.subset_adjoin ⟨r ∘ e.symm, scalar_comp_at (hinv (f p) hfp) hr', rfl⟩⟩
    have hcomp : Germ.ofFun ((r ∘ e.symm) ∘ f) = k.val := by
      rw [hrk]
      apply Quotient.sound
      filter_upwards [e.open_source.mem_nhds hp] with x hx
      change r (e.symm (f x)) = r x
      rw [← he hx, e.left_inv hx]
    exact (hL v j k (r ∘ e.symm) rfl hcomp).symm.trans
      ((congrArg (fun z : TangentSpace T (f p) => z.val j) hvw).trans
        (hL w j k (r ∘ e.symm) rfl hcomp))
  obtain ⟨hfiniteS, hdimS⟩ := tangent_dimension S p
  obtain ⟨hfiniteT, hdimT⟩ := tangent_dimension T (f p)
  letI := hfiniteS
  letI := hfiniteT
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (V := TangentSpace S p) (V₂ := TangentSpace T (f p))
    (hdimS.trans hdimT.symm) (f := L)).mp hi⟩

/-- The determinant-ray sign of an actual differential is constant near any point where the chosen equivalences are genuine. -/
theorem orientationSign_eventually_eq :
    ∀ {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N),
    IsSmoothMap S T f → ∀ (W : Set M), IsOpen W → ∀ (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p)),
    (∀ p ∈ W, IsDifferential S T f p (E p).toLinearMap) →
    ∀ p ∈ W, ∀ᶠ x in 𝓝 p, orientationSign o q E x = orientationSign o q E p := by
  intro n a b M N _ _ S T f hf' W hW o q E hE
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf' p).1)
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  intro p hpW
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨U, hU, hpU, F, hF, hFeq⟩ := (hf' p).2 c hc d hd hp hfp
  obtain ⟨V, hVeq, hV, hpV⟩ := mem_nhds_iff.mp (hFeq.and (hW.mem_nhds hpW))
  let O : Set M := c.source ∩ f ⁻¹' d.source ∩ V ∩ (fun x => (c x).val) ⁻¹' U
  have hO : IsOpen O := by
    have hcu : IsOpen (c.source ∩ (fun x => (c x).val) ⁻¹' U) :=
      (continuous_subtype_val.comp_continuousOn c.continuousOn).isOpen_inter_preimage c.open_source hU
    convert (hcu.inter (d.open_source.preimage hfc)).inter hV using 1
    ext x
    simp only [O, mem_inter_iff, mem_preimage]
    tauto
  have hpO : p ∈ O := ⟨⟨⟨hp, hfp⟩, hpV⟩, hpU⟩
  let u (x : O) := K.equiv c hc x.val x.property.1.1.1
  let z (x : O) := L.equiv d hd (f x.val) x.property.1.1.2
  let A (x : O) : Euclidean n ≃ₗ[ℝ] Euclidean n :=
    (u x).symm.trans ((E x.val).trans (z x))
  have hjac (x : O) : (A x).toLinearMap = (fderiv ℝ F (c x.val).val).toLinearMap := by
    apply LinearMap.ext
    intro v
    have hrep : (fun y => F (c y).val) =ᶠ[𝓝 x.val] (fun y => (d (f y)).val) :=
      Filter.mem_of_superset (hV.mem_nhds x.property.1.2) (fun y hy => (hVeq hy).1)
    exact (differential_jacobian S T f hf' x.val (E x.val).toLinearMap (hE x.val (hVeq x.property.1.2).2)
      c d hc hd x.property.1.1.1 x.property.1.1.2 (u x) (z x)
      (K.isCoordinates c hc _ _) (L.isCoordinates d hd _ _)
      U F hU x.property.2 hF hrep ((u x).symm v)).trans
        (by rw [LinearEquiv.apply_symm_apply]; rfl)
  have hcc : Continuous (fun x : O => (c x.val).val) :=
    continuous_subtype_val.comp
      (c.continuousOn.comp_continuous continuous_subtype_val (fun x => x.property.1.1.1))
  have hderF : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU (by simp)
  have hder : Continuous (fun x : O => fderiv ℝ F (c x.val).val) :=
    hderF.continuousOn.comp_continuous hcc (fun x => x.property.2)
  have hdet : Continuous (fun x : O => (A x).toLinearMap.det) := by
    simp_rw [hjac]
    exact ContinuousLinearMap.continuous_det.comp hder
  let ro (x : O) : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) := Module.Ray.map (determinantMap n (u x)) (o.val x.val)
  let rq (x : O) : Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) := Module.Ray.map (determinantMap n (z x)) (q.val (f x.val))
  have hro : IsLocallyConstant ro :=
    (o.property K c hc).comp_continuous
      (f := fun x : O => (⟨x.val, x.property.1.1.1⟩ : c.source))
      (continuous_subtype_val.subtype_mk _)
  have hrq : IsLocallyConstant rq :=
    (q.property L d hd).comp_continuous
      (f := fun x : O => (⟨f x.val, x.property.1.1.2⟩ : d.source))
      ((hfc.comp continuous_subtype_val).subtype_mk _)
  have hs := (OrientationProducts.coordinateRayTransport_locallyConstant A hdet ro hro).comp₂ hrq
    (fun r s => if r = s then true else false)
  have heq (x : O) : orientationSign o q E x.val =
      (if Module.Ray.map (determinantMap n (A x)) (ro x) = rq x then true else false) := by
    have hiff := OrientationProducts.determinantRay_eq_iff (u x) (z x) (E x.val) (o.val x.val) (q.val (f x.val))
    simp only [orientationSign, hiff]
    rfl
  have hs' : IsLocallyConstant (fun x : O => orientationSign o q E x.val) := by
    simpa only [← heq] using hs
  have hn := hs'.eventually_eq ⟨p, hpO⟩
  have hn' : ∀ᶠ x in 𝓝[O] p, orientationSign o q E x = orientationSign o q E p := by
    rwa [← map_nhds_subtype_val ⟨p, hpO⟩]
  rwa [hO.nhdsWithin_eq hpO] at hn'




/-- Equal-dimensional genuine tangent fibers admit equivalences independently
of whether the given map is regular away from the chosen open set. -/
def tangentEquiv {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p) := Classical.choice (by
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨d, hd, hpd⟩ := T.smoothStructure.property.1.1 (f p)
  obtain ⟨E, _⟩ := FiniteRegularity.exists_smooth_chart_coordinates S p c hc hpc
  obtain ⟨D, _⟩ := FiniteRegularity.exists_smooth_chart_coordinates T (f p) d hd hpd
  exact ⟨E.trans D.symm⟩)

/-- Complete a locally invertible differential by arbitrary equivalences
elsewhere. Only its values on the specified open set will be used. -/
def differentialEquivExtension {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p)) (p : M) :
    TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p) :=
  if h : Function.Bijective (L p) then LinearEquiv.ofBijective (L p) h
  else tangentEquiv S T f p

theorem differentialEquivExtension_eq {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (p : M) (h : Function.Bijective (L p)) :
    (differentialEquivExtension S T f L p).toLinearMap = L p := by
  simp only [differentialEquivExtension, dif_pos h]
  rfl

/-- An integer tangent sign is locally constant on every actual inverse sheet. -/
theorem differentialSign_inverse_sheet {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (he : EqOn e f e.source)
    (hinv : ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target)
    (o : Orientation S) (q : Orientation T)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (p : M) (hp : p ∈ e.source) :
    ∀ᶠ x in 𝓝 p, differentialSign o q x (L x) = differentialSign o q p (L p) := by
  let E := differentialEquivExtension S T f L
  have hE (x : M) (hx : x ∈ e.source) : (E x).toLinearMap = L x :=
    differentialEquivExtension_eq S T f L x
      (local_inverse_differential_bijective S T f e he hinv x hx (L x) (hL x))
  have hn := orientationSign_eventually_eq S T f hf e.source e.open_source o q E
    (fun x hx => by rw [hE x hx]; exact hL x) p hp
  have hs (x : M) (hx : x ∈ e.source) :
      (differentialSign o q x (L x) : ℝ) = signValue (orientationSign o q E x) := by
    rw [← hE x hx]
    exact differentialSign_eq o q E x
  filter_upwards [hn, e.open_source.mem_nhds hp] with x hx hxS
  apply Int.cast_injective (α := ℝ)
  rw [hs x hxS, hs p hp, hx]


/-- The determinant-ray sign of a differential family is constant on a connected
inverse sheet. Only the differential condition on that sheet is required. -/
theorem orientationSign_eq_on_inverse_sheet {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (hconn : IsConnected e.source) (o : Orientation S) (q : Orientation T)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (hE : ∀ p ∈ e.source, IsDifferential S T f p (E p).toLinearMap)
    (p : M) (hp : p ∈ e.source) (x : M) (hx : x ∈ e.source) :
    orientationSign o q E x = orientationSign o q E p := by
  have hloc : IsLocallyConstant (fun z : e.source => orientationSign o q E z.val) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuousAt_subtype_val.eventually
      (orientationSign_eventually_eq S T f hf e.source e.open_source o q E hE
        z.val z.property)
  letI := Subtype.preconnectedSpace hconn.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨p, hp⟩

/-- The integer sign is constant on a connected inverse sheet. -/
theorem differentialSign_eq_on_inverse_sheet {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (he : EqOn e f e.source)
    (hinv : ManifoldSmoothOn T.smoothStructure.val S.smoothStructure.val e.symm e.target)
    (hconn : IsConnected e.source) (o : Orientation S) (q : Orientation T)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (p : M) (hp : p ∈ e.source) (x : M) (hx : x ∈ e.source) :
    differentialSign o q x (L x) = differentialSign o q p (L p) := by
  have hloc : IsLocallyConstant (fun z : e.source => differentialSign o q z.val (L z.val)) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro z
    exact continuousAt_subtype_val.eventually
      (differentialSign_inverse_sheet S T f hf e he hinv o q L hL z.val z.property)
  letI := Subtype.preconnectedSpace hconn.isPreconnected
  exact hloc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨p, hp⟩


open TangentBundleData FormPullbackData

/-- Cut a section along one open member of a disjoint support cover. -/
def sliceField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (U : Set M) (ω : Field S n) : Field S n :=
  fun p => if p ∈ U then ω p else 0

theorem sliceField_support {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (U : Set M) (ω : Field S n)
    (hclosed : IsClosed (sectionSupport ω ∩ U)) :
    sectionSupport (sliceField U ω) ⊆ sectionSupport ω ∩ U := by
  apply closure_minimal _ hclosed
  intro p hp
  have hpU : p ∈ U := by
    by_contra hn
    exact hp (by simp [sliceField, hn])
  exact ⟨subset_closure (by simpa [sliceField, hpU] using hp), hpU⟩

/-- Cutting stays continuous because the cut edge misses the closed support. -/
def sliceTopForm {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (ω : CompactTopForm S) (U : Set M)
    (hU : IsOpen U) (hclosed : IsClosed (sectionSupport ω.field ∩ U)) :
    CompactTopForm S where
  field := sliceField U ω.field
  continuous := by
    intro K c hc
    apply continuous_iff_continuousAt.mpr
    intro p
    by_cases hpU : p.val ∈ U
    · apply (ω.continuous K c hc).continuousAt.congr_of_eventuallyEq
      filter_upwards [(hU.preimage continuous_subtype_val).mem_nhds hpU] with x hx
      have hxU : x.val ∈ U := hx
      simp [sliceField, hxU, topCoefficient]
    · have hpK : p.val ∈ (sectionSupport ω.field ∩ U)ᶜ := fun h => hpU h.2
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(hclosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hpK] with x hx
      have hz : sliceField U ω.field x.val = 0 := by
        by_cases hxU : x.val ∈ U
        · have hxω : ω.field x.val = 0 := by
            by_contra hn
            exact hx ⟨subset_closure hn, hxU⟩
          simp [sliceField, hxω, hxU]
        · simp [sliceField, hxU]
      simp [topCoefficient, hz]
  compact_support := ω.compact_support.of_isClosed_subset isClosed_closure
    (fun _ hp => (sliceField_support U ω.field hclosed hp).1)

/-- Each member is closed relative to a closed set covered by disjoint opens. -/
theorem closed_inter_of_disjoint_cover {M : Type u} [TopologicalSpace M]
    {ι : Type v} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (K : Set M) (hK : IsClosed K) (hcover : K ⊆ ⋃ i, U i) (i : ι) :
    IsClosed (K ∩ U i) := by
  have heq : K ∩ U i = K ∩ (⋃ j : {j : ι // j ≠ i}, U j.val)ᶜ := by
    ext p
    constructor
    · rintro ⟨hpK, hpU⟩
      refine ⟨hpK, ?_⟩
      intro hm
      obtain ⟨j, hj⟩ := mem_iUnion.mp hm
      exact Set.disjoint_left.mp (hdisj j.property) hj hpU
    · rintro ⟨hpK, hn⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hpK)
      refine ⟨hpK, ?_⟩
      by_cases hji : j = i
      · simpa [hji] using hj
      · exact (hn (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)).elim
  rw [heq]
  exact hK.inter (isOpen_iUnion fun j : {j : ι // j ≠ i} => hU j.val).isClosed_compl

/-- A finite disjoint open support cover splits the original compact form. -/
theorem integral_disjoint_slices {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {ι : Type v} [Fintype ι] (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hdisj : Pairwise (fun i j => Disjoint (U i) (U j)))
    (ω : CompactTopForm S) (hcover : sectionSupport ω.field ⊆ ⋃ i, U i)
    (o : Orientation S) (I : CompactTopForm S → ℝ) (hI : IsIntegral o I) :
    I ω = ∑ i, I (sliceTopForm ω (U i) (hU i)
      (closed_inter_of_disjoint_cover U hU hdisj _ isClosed_closure hcover i)) := by
  classical
  apply GlobalIntegrationResults.integral_finset_sum hI Finset.univ
  funext p
  simp only [Finset.sum_apply]
  by_cases hp : ω.field p = 0
  · simp [sliceTopForm, sliceField, hp]
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (subset_closure hp))
    rw [Finset.sum_eq_single i]
    · simp [sliceTopForm, sliceField, hi]
    · intro j _ hji
      have hj : p ∉ U j := fun hj => Set.disjoint_left.mp (hdisj hji) hj hi
      simp [sliceTopForm, sliceField, hj]
    · simp


open TangentBundleData MeasureTheory Module DiffeomorphismLocalResults

def partialCoordinateMap {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M N) (c : ModelChart n a M) (d : ModelChart n b N) :
    OpenPartialHomeomorph (ModelSpace n a) (ModelSpace n b) :=
  c.symm.trans (e.trans d)

@[simp] theorem partialCoordinateMap_source {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M N) (c : ModelChart n a M) (d : ModelChart n b N)
    (x : ModelSpace n a) :
    x ∈ (partialCoordinateMap e c d).source ↔
      x ∈ c.target ∧ c.symm x ∈ e.source ∧ e (c.symm x) ∈ d.source := by
  simp [partialCoordinateMap, OpenPartialHomeomorph.trans_source]

@[simp] theorem partialCoordinateMap_target {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (e : OpenPartialHomeomorph M N) (c : ModelChart n a M) (d : ModelChart n b N)
    (y : ModelSpace n b) :
    y ∈ (partialCoordinateMap e c d).target ↔
      y ∈ d.target ∧ d.symm y ∈ e.target ∧ e.symm (d.symm y) ∈ c.source := by
  simp [partialCoordinateMap, OpenPartialHomeomorph.trans_target, and_assoc]


/-- The ambient derivative of a partial inverse chart uses only the genuine
smooth map on the partial homeomorphism's open source. -/
theorem partialCoordinateMap_derivative {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (heq : EqOn e f e.source)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (hE : ∀ p ∈ e.source, IsDifferential S T f p (E p).toLinearMap)
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hep : p ∈ e.source) (hq : f p ∈ d.source) :
    HasFDerivWithinAt (ambientMap (partialCoordinateMap e c d))
      ((((L.equiv d hd (f p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap).toContinuousLinearMap)
      (LocalIntegrationResults.ambientDomain (partialCoordinateMap e c d).source)
      (c p).val := by
  let m := partialCoordinateMap e c d
  have hx : c p ∈ m.source := by
    apply (partialCoordinateMap_source e c d _).mpr
    refine ⟨c.map_source hp, ?_⟩
    rw [c.left_inv hp]
    exact ⟨hep, by rwa [heq hep]⟩
  obtain ⟨U, hU, hpU, H, hH, hext⟩ :=
    (chartContDiffAt_iff_modelExtension (⊤ : ℕ∞) c d f p hp hq
      (hf p).1).mp ((hf p).2 c hc d hd hp hq)
  have hext' : ∀ y ∈ m.source, y.val ∈ U → H y.val = (m y).val := by
    intro y hy hyU
    obtain ⟨hyc, hye, hyd⟩ := (partialCoordinateMap_source e c d _).mp hy
    have hyd' : f (c.symm y) ∈ d.source := by rwa [heq hye] at hyd
    have hh := hext y hyc hyd' hyU
    simpa only [m, partialCoordinateMap, OpenPartialHomeomorph.trans_apply, heq hye] using hh
  have hder := ambientMap_hasFDerivWithinAt m (c p) hx U hU hpU H hH hext'
  have hrep : (fun y => H (c y).val) =ᶠ[𝓝 p] (fun y => (d (f y)).val) := by
    filter_upwards [c.open_source.mem_nhds hp,
      (hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hq),
      (continuous_subtype_val.continuousAt.comp (c.continuousAt hp)).preimage_mem_nhds
        (hU.mem_nhds hpU)] with y hyc hyd hyU
    simpa only [c.left_inv hyc] using
      hext (c y) (c.map_source hyc) (by simpa only [c.left_inv hyc, mem_preimage] using hyd) hyU
  have hj : (((L.equiv d hd (f p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap).toContinuousLinearMap =
        fderiv ℝ H (c p).val := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using
      differential_jacobian S T f hf p (E p).toLinearMap (hE p hep)
        c d hc hd hp hq (K.equiv c hc p hp) (L.equiv d hd (f p) hq)
        (K.isCoordinates c hc p hp) (L.isCoordinates d hd (f p) hq)
        U H hU hpU hH hrep ((K.equiv c hc p hp).symm v)
  rwa [← hj] at hder


/-- Local extension by zero retains the usual pullback support bound. -/
theorem local_pullback_support {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : Continuous f) (e : OpenPartialHomeomorph M N)
    (D : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (ω : Field S n) (η : Field T n)
    (hω : ∀ p ∈ e.source, ω p = pullbackField S T f D η p)
    (hcs : sectionSupport ω ⊆ e.source) :
    sectionSupport ω ⊆ f ⁻¹' sectionSupport η := by
  apply closure_minimal
  · intro p hp
    have hep := hcs (subset_closure hp)
    by_contra hy
    have hz : η (f p) = 0 := by
      by_contra hn
      exact hy (subset_closure hn)
    exact hp (by simp only [hω p hep, FormPullbackData.pullbackField, hz, map_zero])
  · exact isClosed_closure.preimage hf

/-- Signed substitution on one inverse neighborhood, with the two fields kept
on their original manifolds. Its support hypotheses are precisely those met
by a sheet term cut from a compactly supported pullback. -/
theorem partial_coordinate_naturality {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (heq : EqOn e f e.source)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (hE : ∀ p ∈ e.source, IsDifferential S T f p (E p).toLinearMap)
    (ω : Field S n) (η : Field T n)
    (hω : ∀ p ∈ e.source,
      ω p = pullbackField S T f (fun p => (E p).toLinearMap) η p)
    (o : Orientation S) (q : Orientation T)
    (s : SignedCharts S) (t : SignedCharts T)
    (hs : RepresentsSignedCharts o.val s) (ht : RepresentsSignedCharts q.val t)
    (K : FiberCoordinates S) (L : FiberCoordinates T)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hec : e.source ⊆ c.source)
    (hcs : sectionSupport ω ⊆ e.source)
    (hfs : sectionSupport ω ⊆ f ⁻¹' sectionSupport η)
    (hη : sectionSupport η ⊆ d.source ∩ e.target) :
    coordinateIntegral s K c hc ω =
      coordinateIntegral t L d hd
        (fun y => signValue (orientationSign o q E (e.symm y)) • η y) := by
  let r : N → ℝ := fun y => signValue (orientationSign o q E (e.symm y))
  let ξ : Field T n := fun y => r y • η y
  let m := partialCoordinateMap e c d
  let U := LocalIntegrationResults.ambientDomain m.source
  let V := LocalIntegrationResults.ambientDomain m.target
  let ψ := ambientMap m
  let J := fderivWithin ℝ ψ U
  let a := signedCoordinateCoefficient s K c hc ω
  let b := signedCoordinateCoefficient t L d hd ξ
  have hU : MeasurableSet U := LocalIntegrationResults.ambientDomain_measurable m.open_source
  have hJ : ∀ x ∈ U, HasFDerivWithinAt ψ (J x) U x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyc, hye, hyd⟩ := (partialCoordinateMap_source e c d _).mp hy
    have hyd' : f (c.symm y) ∈ d.source := by rwa [heq hye] at hyd
    have hder := partialCoordinateMap_derivative S T f hf e heq E hE K L c d hc hd
      (c.symm y) (c.map_target hyc) hye hyd'
    rw [c.right_inv hyc] at hder
    exact hder.differentiableWithinAt.hasFDerivWithinAt
  have hab : ∀ x ∈ U, |(J x).det| * b (ψ x) = a x := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyc, hye, hyd⟩ := (partialCoordinateMap_source e c d _).mp hy
    let p := c.symm y
    have hp : p ∈ c.source := c.map_target hyc
    have hep : p ∈ e.source := hye
    have hq : f p ∈ d.source := by rwa [heq hye] at hyd
    have hcy : c p = y := c.right_inv hyc
    have hψ : ψ y.val = (d (f p)).val := by
      change ambientMap m y.val = (d (f p)).val
      rw [ambientMap_at]
      change (d (e p)).val = (d (f p)).val
      rw [heq hep]
    have hder := partialCoordinateMap_derivative S T f hf e heq E hE K L c d hc hd p hp hep hq
    rw [hcy] at hder
    have hlin : (((L.equiv d hd (f p) hq).toLinearMap.comp (E p).toLinearMap).comp
        (K.equiv c hc p hp).symm.toLinearMap) =
        ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (f p) hq))).toLinearMap := by
      apply LinearMap.ext
      intro v
      rfl
    have hdet : (J y.val).det =
        ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (f p) hq))).toLinearMap.det := by
      have hj := hder.fderivWithin (uniqueDiffOn_modelDomain m.open_source _ ⟨y, hy, rfl⟩)
      change J y.val = _ at hj
      rw [hj]
      change LinearMap.det _ = LinearMap.det _
      exact congrArg LinearMap.det hlin
    change |(J y.val).det| * signedCoordinateCoefficient t L d hd ξ (ψ y.val) =
      signedCoordinateCoefficient s K c hc ω y.val
    rw [hψ, ← hcy,
      LocalIntegrationResults.signedCoefficient_at t L d hd ξ ⟨f p, hq⟩,
      LocalIntegrationResults.signedCoefficient_at s K c hc ω ⟨p, hp⟩]
    change |(J (c p).val).det| *
        (signValue (t.sign d hd ⟨f p, hq⟩) * topCoefficient L d hd (f p) hq ξ) =
      signValue (s.sign c hc ⟨p, hp⟩) * topCoefficient K c hc p hp ω
    have hcω : topCoefficient K c hc p hp ω =
        topCoefficient K c hc p hp
          (pullbackField S T f (fun p => (E p).toLinearMap) η) := by
      unfold topCoefficient
      rw [hω p hep]
    rw [hcy, hdet, topCoefficient_weight L d hd _ hq η r, hcω,
      topCoefficient_pullback S T f (fun p => (E p).toLinearMap) K L c d hc hd p hp hq η]
    have hr : r (f p) = signValue (orientationSign o q E p) := by
      simp only [r, ← heq hep, e.left_inv hep]
    rw [hr]
    have hsign := coordinate_sign S T f E o q s t hs ht K L c d hc hd p hp hq
    have halg := LocalIntegrationResults.signed_coefficient_identity
      (signValue (s.sign c hc ⟨p, hp⟩))
      (signValue (orientationSign o q E p) * signValue (t.sign d hd ⟨f p, hq⟩))
      ((K.equiv c hc p hp).symm.trans ((E p).trans (L.equiv d hd (f p) hq))).toLinearMap.det
      (topCoefficient L d hd (f p) hq η) hsign
    rw [hlin]
    convert halg.symm using 1 <;> ring
  have haU : Function.support a ⊆ U := by
    intro x hx
    obtain ⟨p, hp, hpc, hcx⟩ := LocalIntegrationResults.signedCoefficient_nonzero s K c hc ω x hx
    have hep := hcs hp
    have hfp : f p ∈ d.source := (hη (hfs hp)).1
    rw [← hcx]
    exact ⟨c p, (partialCoordinateMap_source e c d _).mpr
      ⟨c.map_source hpc, by
        rw [c.left_inv hpc]
        exact ⟨hep, by rwa [heq hep]⟩⟩, rfl⟩
  have hbV : Function.support b ⊆ V := by
    intro x hx
    obtain ⟨y, hy, hyd, hdx⟩ := LocalIntegrationResults.signedCoefficient_nonzero t L d hd ξ x hx
    have hyη : y ∈ sectionSupport η := weight_support_subset η r hy
    have hey : y ∈ e.target := (hη hyη).2
    rw [← hdx]
    refine ⟨d y, (partialCoordinateMap_target e c d _).mpr ?_, rfl⟩
    rw [d.left_inv hyd]
    exact ⟨d.map_source hyd, hey, hec (e.map_target hey)⟩
  have hsub := integral_image_eq_integral_abs_det_fderiv_smul volume hU hJ
    (ambientMap_geometry m).1 b
  rw [(ambientMap_geometry m).2] at hsub
  have haint : (∫ x in U, a x) = ∫ x, a x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (haU hn)))
  have hbint : (∫ x in V, b x) = ∫ x, b x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      not_not.mp (fun hn => hx (hbV hn)))
  change ∫ x, a x = ∫ x, b x
  rw [← haint, ← hbint, hsub]
  apply setIntegral_congr_fun hU
  intro x hx
  exact (hab x hx).symm


/-- The constant-sign local change-of-variables formula on the original
manifolds, with compact continuous forms and their original integrals. -/
theorem partial_constant_sign_substitution {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (e : OpenPartialHomeomorph M N)
    (heq : EqOn e f e.source)
    (E : ∀ p, TangentSpace S p ≃ₗ[ℝ] TangentSpace T (f p))
    (hE : ∀ p ∈ e.source, IsDifferential S T f p (E p).toLinearMap)
    (ω : CompactTopForm S) (η : CompactTopForm T)
    (hω : ∀ p ∈ e.source,
      ω.field p = pullbackField S T f (fun p => (E p).toLinearMap) η.field p)
    (o : Orientation S) (q : Orientation T)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J)
    (c : ModelChart n a M) (d : ModelChart n b N)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ T.smoothStructure.val)
    (hec : e.source ⊆ c.source)
    (hcs : sectionSupport ω.field ⊆ e.source)
    (hfs : sectionSupport ω.field ⊆ f ⁻¹' sectionSupport η.field)
    (hη : sectionSupport η.field ⊆ d.source ∩ e.target)
    (ε : Bool) (hε : ∀ p ∈ e.source, orientationSign o q E p = ε) :
    I ω = signValue ε * J η := by
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨t, ht, _⟩ := LocalIntegrationResults.orientation_signs T q
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨L⟩ := TangentBundle.fiberCoordinates_exists T
  obtain ⟨θ, hθ⟩ := (GlobalIntegrationResults.algebra T η η).2
    (fun _ => signValue ε) continuous_const
  have hθsupp : sectionSupport θ.field ⊆ d.source := by
    rw [hθ]
    exact (weight_support_subset η.field (fun _ => signValue ε)).trans
      (fun p hp => (hη hp).1)
  have hθvar : θ.field = fun y => signValue (orientationSign o q E (e.symm y)) • η.field y := by
    rw [hθ]
    funext y
    by_cases hz : η.field y = 0
    · simp only [hz, smul_zero]
    · have hy : y ∈ sectionSupport η.field := subset_closure hz
      rw [hε _ (e.map_target (hη hy).2)]
  rw [hI.2.2 s hs K c hc ω (hcs.trans hec)]
  rw [partial_coordinate_naturality S T f hf e heq E hE ω.field η.field hω o q
    s t hs ht K L c d hc hd hec hcs hfs hη]
  rw [← hθvar, ← hJ.2.2 t ht L d hd θ hθsupp]
  exact hJ.2.1 (signValue ε) η θ (by
    funext p
    exact congrFun hθ p)


/-- Two integers satisfying the complete signed-fiber formula agree. Regular
value existence is proved above in every dimension, rather than assumed. -/
theorem fiberFormula_unique {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [Nonempty N]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (o : Orientation S) (q : Orientation T)
    {d e : ℤ} (hd : FiberFormula f o q d) (he : FiberFormula f o q e) : d = e := by
  obtain ⟨y, hy⟩ := regular_value_exists_proof S T f hf
  obtain ⟨hfin, hd⟩ := hd y hy
  obtain ⟨hfin', he⟩ := he y hy
  exact (hd (differential S T f hf) (differential_spec S T f hf)).trans
    (he (differential S T f hf) (differential_spec S T f hf)).symm

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem regular_fiber_finite_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_fiber_finiteType.{u} :=
  regular_fiber_finite_proof

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem regular_value_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_value_existsType.{u} :=
  regular_value_exists_proof

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem real_scalar_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.real_scalarType.{u} :=
  real_scalar_proof h1

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem zero_dimension_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.zero_dimensionType.{u} :=
  zero_dimension_proof

/-- Surjectivity follows from the empty regular fiber outside the image. -/
theorem nonzero_degree_surjective_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.nonzero_degree_surjectiveType.{u} := by
  intro n a b M N _ _ _ _ _ _ S T f hf _hS _hT o q I J d _hI _hJ hd hd0
  exact surjective_of_fiberFormula S T f hf o q d hd.2 hd0

end SmoothManifolds.DegreeResults

namespace SmoothManifolds.DegreeForms
open MeasureTheory
open ModelData AtlasData MapData TangentData TangentBundleData CovectorData
  BundleOperationsData ExteriorData ExteriorDerivativeData FormPullbackData
  OrientationData LocalIntegrationData GlobalIntegrationData BoundaryData
  PartitionData Set Filter MeasureTheory
universe u

theorem topCoefficient_eq_pairing {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (ω : Field S n) :
    topCoefficient K c hc p hp ω =
      pairing p (ω p) (OrientationData.coordinateVector K c hc ⟨p,hp⟩) := by
  change (exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual ℝ (TangentSpace S p) n (ω p)))
      (CovectorData.coordinateVector K c hc p hp) = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  have hv : CovectorData.coordinateVector K c hc p hp =
      (fun j => (K.equiv c hc p hp).symm ((Pi.basisFun ℝ (Fin n)) j)) := by
    funext j
    simp only [CovectorData.coordinateVector, Pi.basisFun_apply]
  rw [hv]
  rfl

theorem continuous_top_of_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : FormBundle C n) (ω : Field S n) (hω : IsForm B ω) :
    IsContinuousTopForm ω := by
  intro K c hc
  have hs := (ExteriorAlgebraResults.smooth_iff_coefficients C n B ω).mp hω
    c hc (OrientationResults.topIndex n)
  have hcont : Continuous (fun p : c.source => coefficients C n c hc ω p
      (OrientationResults.topIndex n)) :=
    continuous_iff_continuousAt.mpr (fun p => (hs p).1)
  apply hcont.congr
  intro p
  rw [← OrientationResults.pairing_coordinateVector_eq_coefficients C c hc ω p,
    ← topCoefficient_eq_pairing]
  exact (LocalIntegrationResults.topCoefficient_coordinates_eq K C.tangent.fiberCoordinates
    c hc p.val p.property ω).symm

/-- The signed local wedge times a compact smooth bump is a genuine smooth top form. -/
theorem exists_local_smooth_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (B : FormBundle C n) (s : SignedCharts S) (c : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (y : M) (hy : y ∈ c.source)
    (V : Set M) (hV : IsOpen V) (hyV : y ∈ V) :
    ∃ (ω : CompactTopForm S) (ρ : M → ℝ),
      IsForm B ω.field ∧ sectionSupport ω.field ⊆ V ∩ c.source ∧
      (∀ z, 0 ≤ ρ z) ∧ ρ y = 1 ∧
      (∀ z : ModelSpace n a, z ∈ c.target →
        modelSignedCoefficient s C.tangent.fiberCoordinates c hc ω.field z = ρ (c.symm z)) := by
  obtain ⟨ρ, hρ, hpos, hρy, hsupp, hcompact⟩ :=
    exists_local_bump S y (V ∩ c.source) (hV.inter c.open_source) ⟨hyV, hy⟩
  let ζ := OrientationResults.localTopField C.tangent.fiberCoordinates s c hc
  let ξ : Field S n := fun p => ρ p • ζ p
  have hξ : IsForm B ξ :=
    OrientationResults.supported_local_form_smooth ExteriorAlgebraResults.smooth_iff_coefficients
      C B c.source c.open_source ζ
      (OrientationResults.smooth_localTopField_coefficients S C s c hc)
      ρ ((OrientationResults.vectorSmooth_scalar_iff _ _).mpr hρ) (fun p hp => (hsupp hp).2)
  have hsupport : sectionSupport ξ ⊆ V ∩ c.source := by
    exact fun p hp => hsupp ((GlobalIntegrationResults.weight_support S n ζ ρ hp).1)
  have hcont : IsContinuousTopForm ξ := continuous_top_of_smooth C B ξ hξ
  let ω : CompactTopForm S := ⟨ξ, hcont,
    hcompact.of_isClosed_subset isClosed_closure
      (fun p hp => (GlobalIntegrationResults.weight_support S n ζ ρ hp).1)⟩
  refine ⟨ω, ρ, hξ, hsupport, fun z => (hpos z).1, ?_, ?_⟩
  · exact hρy.eq_of_nhds
  · intro z hz
    have hp : c.symm z ∈ c.source := c.map_target hz
    simp only [modelSignedCoefficient, hz, dite_true]
    change signValue (s.sign c hc ⟨c.symm z, hp⟩) *
      topCoefficient C.tangent.fiberCoordinates c hc (c.symm z) hp ξ = ρ (c.symm z)
    rw [GlobalConstructionResults.topCoefficient_weight]
    have ht : topCoefficient C.tangent.fiberCoordinates c hc (c.symm z) hp ζ =
        signValue (s.sign c hc ⟨c.symm z, hp⟩) := by
      change evaluate (TangentSpace S (c.symm z)) n
        (OrientationResults.localTopField C.tangent.fiberCoordinates s c hc (c.symm z))
        (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) hp) = _
      simp only [OrientationResults.localTopField, hp, dite_true,
        OrientationResults.signedCoordinateTopForm, map_smul]
      rw [smul_apply, smul_eq_mul]
      have hself := OrientationResults.pairing_coordinateTopForm_self
        C.tangent.fiberCoordinates c hc ⟨c.symm z, hp⟩
      have heval : evaluate (TangentSpace S (c.symm z)) n
          (OrientationResults.coordinateTopForm C.tangent.fiberCoordinates c hc ⟨c.symm z, hp⟩)
          (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) hp) = 1 := by
        change (exteriorPower.alternatingMapLinearEquiv.symm
          (exteriorPower.pairingDual ℝ (TangentSpace S (c.symm z)) n
            (OrientationResults.coordinateTopForm C.tangent.fiberCoordinates c hc ⟨c.symm z, hp⟩)))
          (CovectorData.coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) hp) = 1
        rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
        have hv : CovectorData.coordinateVector C.tangent.fiberCoordinates c hc (c.symm z) hp =
            (fun j => (C.tangent.fiberCoordinates.equiv c hc (c.symm z) hp).symm
              ((Pi.basisFun ℝ (Fin n)) j)) := by
          funext j
          simp only [CovectorData.coordinateVector, Pi.basisFun_apply]
        rw [hv]
        exact hself
      rw [heval, mul_one]
    rw [ht]
    rw [mul_left_comm, OrientationResults.signValue_mul_self, mul_one]

/-- An integrable nonnegative local coefficient positive at one interior point
has strictly positive Euclidean integral. -/
theorem coordinate_integral_pos {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (s : SignedCharts S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : CompactTopForm S) (hsupp : sectionSupport ω.field ⊆ c.source)
    (y : M) (hy : y ∈ c.source) (hint : (c y).val ∈ interior (modelSet n a))
    (hnonneg : ∀ z : ModelSpace n a, 0 ≤ modelSignedCoefficient s K c hc ω.field z)
    (hypos : 0 < modelSignedCoefficient s K c hc ω.field (c y)) :
    0 < coordinateIntegral s K c hc ω.field := by
  let f := signedCoordinateCoefficient s K c hc ω.field
  have hfc : ContinuousAt f (c y).val := by
    apply ContinuousWithinAt.continuousAt _ (mem_interior_iff_mem_nhds.mp hint)
    apply (continuousWithinAt_iff_continuousAt_domRestrict f (c y).property).mpr
    have hh : ContinuousAt (modelSignedCoefficient s K c hc ω.field) (c y) :=
      (LocalIntegrationResults.modelSignedCoefficient_continuous s K c hc ω hsupp).continuousAt
    convert hh using 1
    funext z
    simp only [Set.domRestrict_apply, f, signedCoordinateCoefficient, extendModel,
      z.property, dite_true]
  have hfy : 0 < f (c y).val := by
    simpa only [f, signedCoordinateCoefficient, extendModel, (c y).property, dite_true] using hypos
  have hevent : ∀ᶠ z in 𝓝 (c y).val, 0 < f z :=
    hfc.preimage_mem_nhds (Ioi_mem_nhds hfy)
  obtain ⟨U, hUf, hU, hyU⟩ := eventually_nhds_iff.mp hevent
  have hfn : 0 ≤ f := by
    intro z
    dsimp [f, signedCoordinateCoefficient, extendModel]
    split_ifs with hz
    · exact hnonneg ⟨z, hz⟩
    · exact le_rfl
  apply (integral_pos_iff_support_of_nonneg hfn
    (LocalIntegrationResults.integrable S s K c hc ω hsupp)).mpr
  exact (hU.measure_pos volume ⟨(c y).val, hyU⟩).trans_le
    (measure_mono (fun z hz => ne_of_gt (hUf z hz)))

/-- Every nonempty open neighborhood in an oriented boundaryless manifold
contains a compactly supported smooth top form of integral one. -/
theorem exists_unit_integral_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (hS : intrinsicBoundary S = ∅) (o : Orientation S)
    (C : CotangentBundle S) (B : FormBundle C n)
    (I : CompactTopForm S → ℝ) (hI : IsIntegral o I)
    (y : M) (V : Set M) (hV : IsOpen V) (hyV : y ∈ V) :
    ∃ η : CompactTopForm S, IsForm B η.field ∧
      sectionSupport η.field ⊆ V ∧ I η = 1 := by
  obtain ⟨c, hc, hy⟩ := S.smoothStructure.property.1.1 y
  obtain ⟨s, hs, _⟩ := LocalIntegrationResults.orientation_signs S o
  obtain ⟨ω, ρ, hω, hsupp, hρpos, hρy, hcoef⟩ :=
    exists_local_smooth_form S C B s c hc y hy V hV hyV
  have hint : (c y).val ∈ interior (modelSet n a) := by
    by_contra hn
    have hm : y ∈ intrinsicBoundary S :=
      ⟨c, hc, hy, (mem_modelFace_iff_not_mem_interior (c y)).mpr hn⟩
    simpa only [hS, mem_empty_iff_false] using hm
  have hnonneg : ∀ z : ModelSpace n a,
      0 ≤ modelSignedCoefficient s C.tangent.fiberCoordinates c hc ω.field z := by
    intro z
    by_cases hz : z ∈ c.target
    · rw [hcoef z hz]
      exact hρpos _
    · simp only [modelSignedCoefficient, hz, dite_false, le_refl]
  have hypos : 0 < modelSignedCoefficient s C.tangent.fiberCoordinates c hc ω.field (c y) := by
    rw [hcoef (c y) (c.map_source hy), c.left_inv hy, hρy]
    norm_num
  have hip : 0 < I ω := by
    rw [hI.2.2 s hs C.tangent.fiberCoordinates c hc ω (fun p hp => (hsupp hp).2)]
    exact coordinate_integral_pos S s C.tangent.fiberCoordinates c hc ω
      (fun p hp => (hsupp hp).2) y hy hint hnonneg hypos
  let η := GlobalIntegrationResults.weightForm (fun _ => (I ω)⁻¹) continuous_const ω
  have hη : IsForm B η.field := by
    apply (ExteriorDerivativeResults.smooth_coefficients C n B _).mpr
    exact ExteriorDerivativeResults.regularField_smul C n ⊤ (I ω)⁻¹
      ((ExteriorDerivativeResults.smooth_coefficients C n B _).mp hω)
  refine ⟨η, hη, ?_, ?_⟩
  · intro p hp
    exact (hsupp ((GlobalIntegrationResults.weight_support S n ω.field
      (fun _ => (I ω)⁻¹) hp).2)).1
  · rw [hI.2.1 (I ω)⁻¹ ω η rfl]
    exact inv_mul_cancel₀ hip.ne'

end SmoothManifolds.DegreeForms

namespace SmoothManifolds.DegreeResults
open ModelData AtlasData MapData MapClassData TangentData TangentBundleData
  DifferentialData CovectorData BundleOperationsData ExteriorData FormPullbackData
  OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  BoundaryData DegreeData Set Filter
universe u

/-- A compact top form is determined by its original exterior field. -/
theorem compactTopForm_ext {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} {α β : CompactTopForm S}
    (h : α.field = β.field) : α = β := by
  cases α
  cases β
  cases h
  rfl

/-- Reindex the sum over a finite set by its subtype, retaining empty sets. -/
theorem finite_set_sum {A : Type u} {R : Type*} [AddCommMonoid R]
    (K : Set A) (hK : K.Finite) (g : A → R) :
    letI := hK.fintype
    ∑ x : K, g x.val = ∑ x ∈ hK.toFinset, g x := by
  classical
  letI := hK.fintype
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _
    exact hK.mem_toFinset.mpr x.property
  · intro x _ z _ hxz
    exact Subtype.ext hxz
  · intro x hx
    exact ⟨⟨x, hK.mem_toFinset.mp hx⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

/-- The real integration scalar is the integer signed count at EVERY regular
value. The common sheet neighborhood and the finite-sum proof include empty
fibers; no positivity of the dimension is needed. -/
theorem real_scalar_eq_regular_sum {n : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N] [CompactSpace M]
    (S : SmoothManifold n a M) (T : SmoothManifold n b N) (f : M → N)
    (hf : IsSmoothMap S T f) (hS : intrinsicBoundary S = ∅)
    (hT : intrinsicBoundary T = ∅) (o : Orientation S) (q : Orientation T)
    (I : CompactTopForm S → ℝ) (J : CompactTopForm T → ℝ)
    (hI : IsIntegral o I) (hJ : IsIntegral q J)
    (r : ℝ) (hr : IntegralFormula S T f I J r)
    (y : N) (hy : IsRegularValue S T f y) (hfin : (f ⁻¹' {y}).Finite)
    (L : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) :
    r = ((∑ p ∈ hfin.toFinset, differentialSign o q p (L p) : ℤ) : ℝ) := by
  classical
  letI := hfin.fintype
  obtain ⟨d, hd, hyd⟩ := T.smoothStructure.property.1.1 y
  have hcharts (p : f ⁻¹' {y}) := S.smoothStructure.property.1.1 p.val
  choose c hc hpc using hcharts
  obtain ⟨V, e, hV, hyV, hconnV, hVd, he, hdisj, hpre⟩ :=
    regular_value_sheets_within S T f hf hS hT y hy d.source d.open_source hyd
      (fun p => (c p).source) (fun p => (c p).open_source) hpc
  obtain ⟨C⟩ := BundleOperations.exists_cotangent T
  obtain ⟨B⟩ := ExteriorAlgebraResults.exists_formBundle C n
  obtain ⟨η, hηsm, hηV, hηunit⟩ :=
    DegreeForms.exists_unit_integral_form T hT q C B J hJ y V hV hyV
  obtain ⟨η', ξ, hη', hξ, hrel⟩ := hr C B ⟨η.field, hηsm⟩ L hL
  have heη : η' = η := compactTopForm_ext hη'
  subst η'
  rw [hηunit, mul_one] at hrel
  have hcont : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hf p).1)
  have hξpre : sectionSupport ξ.field ⊆ f ⁻¹' sectionSupport η.field := by
    rw [hξ]
    exact GlobalIntegrationResults.pullback_support S T f hcont L n η.field
  have hcover : sectionSupport ξ.field ⊆ ⋃ p, (e p).source := by
    rw [← hpre]
    exact fun x hx => hηV (hξpre hx)
  have hclosed (p : f ⁻¹' {y}) : IsClosed (sectionSupport ξ.field ∩ (e p).source) :=
    closed_inter_of_disjoint_cover (fun p => (e p).source) (fun p => (e p).open_source)
      hdisj _ isClosed_closure hcover p
  let α : (f ⁻¹' {y}) → CompactTopForm S := fun p =>
    sliceTopForm ξ (e p).source (e p).open_source (hclosed p)
  let E := differentialEquivExtension S T f L
  have hEeq (p : f ⁻¹' {y}) (x : M) (hx : x ∈ (e p).source) :
      (E x).toLinearMap = L x := by
    rcases he p with ⟨_, ht, _, _, heq, _, hsym⟩
    apply differentialEquivExtension_eq S T f L x
    apply local_inverse_differential_bijective S T f (e p) heq _ x hx (L x) (hL x)
    rwa [ht]
  have hE (p : f ⁻¹' {y}) (x : M) (hx : x ∈ (e p).source) :
      IsDifferential S T f x (E x).toLinearMap := by
    rw [hEeq p x hx]
    exact hL x
  have hlocal (p : f ⁻¹' {y}) :
      I (α p) = (differentialSign o q p.val (L p.val) : ℝ) := by
    rcases he p with ⟨hp, ht, hec, hconn, heq, _, _⟩
    have hαS : sectionSupport (α p).field ⊆ (e p).source :=
      fun x hx => (sliceField_support (e p).source ξ.field (hclosed p) hx).2
    have hαpre : sectionSupport (α p).field ⊆ f ⁻¹' sectionSupport η.field :=
      fun x hx => hξpre (sliceField_support (e p).source ξ.field (hclosed p) hx).1
    have hαpull : ∀ x ∈ (e p).source,
        (α p).field x = pullbackField S T f (fun x => (E x).toLinearMap) η.field x := by
      intro x hx
      change sliceField (e p).source ξ.field x = _
      simp only [sliceField, ite_eq_left hx]
      rw [hξ]
      simp only [FormPullbackData.pullbackField, hEeq p x hx]
    have hηlocal : sectionSupport η.field ⊆ d.source ∩ (e p).target := by
      intro z hz
      exact ⟨hVd (hηV hz), ht.symm ▸ hηV hz⟩
    have hconst : ∀ x ∈ (e p).source,
        orientationSign o q E x = orientationSign o q E p.val :=
      fun x hx => orientationSign_eq_on_inverse_sheet S T f hf (e p) hconn o q E
        (hE p) p.val hp x hx
    have hi := partial_constant_sign_substitution S T f hf (e p) heq E (hE p)
      (α p) η hαpull o q I J hI hJ (c p) d (hc p) hd hec hαS hαpre hηlocal
      (orientationSign o q E p.val) hconst
    rw [hηunit, mul_one] at hi
    have hsg : (differentialSign o q p.val (L p.val) : ℝ) =
        signValue (orientationSign o q E p.val) := by
      rw [← hEeq p p.val hp]
      exact differentialSign_eq o q E p.val
    exact hi.trans hsg.symm
  calc
    r = I ξ := hrel.symm
    _ = ∑ p : f ⁻¹' {y}, I (α p) :=
      integral_disjoint_slices (fun p => (e p).source) (fun p => (e p).open_source)
        hdisj ξ hcover o I hI
    _ = ∑ p : f ⁻¹' {y}, (differentialSign o q p.val (L p.val) : ℝ) :=
      Finset.sum_congr rfl (fun p _ => hlocal p)
    _ = ((∑ p ∈ hfin.toFinset, differentialSign o q p (L p) : ℤ) : ℝ) := by
      rw [Int.cast_sum]
      exact finite_set_sum _ hfin (fun p => (differentialSign o q p (L p) : ℝ))

end SmoothManifolds.DegreeResults

namespace SmoothManifolds.DegreeResults
open ModelData AtlasData MapData MapClassData TangentData TangentBundleData
  DifferentialData CovectorData BundleOperationsData ExteriorData FormPullbackData
  OrientationData OrientationProductData LocalIntegrationData GlobalIntegrationData
  BoundaryData DegreeData Set Filter
universe u
/-- The local signed calculation identifies the real scalar with an integer
and proves its signed-fiber formula at every regular value. -/
theorem degree_exists_proof
    (htop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.degree_existsType.{u} := by
  intro n a b M N _ _ _ _ _ _ S T f hf hS hT o q I J hI hJ
  obtain ⟨r, hr⟩ := real_scalar_proof htop S T f hf hS hT o q I J hI hJ
  obtain ⟨y, hy⟩ := regular_value_exists_proof S T f hf
  let hyfin := regular_fiber_finite_proof S T f hf hS hT y hy
  let L := differential S T f hf
  have hL := differential_spec S T f hf
  let d : ℤ := ∑ p ∈ hyfin.toFinset, differentialSign o q p (L p)
  have hrd : r = (d : ℝ) := by
    simpa only [d, Int.cast_sum] using
      real_scalar_eq_regular_sum S T f hf hS hT o q I J hI hJ r hr y hy hyfin L hL
  have hdF : FiberFormula f o q d := by
    intro z hz
    let hzfin := regular_fiber_finite_proof S T f hf hS hT z hz
    refine ⟨hzfin, ?_⟩
    intro K hK
    have hsum := real_scalar_eq_regular_sum S T f hf hS hT o q I J hI hJ
      r hr z hz hzfin K hK
    exact_mod_cast hrd.symm.trans hsum
  refine ⟨d, ⟨?_, hdF⟩, ?_⟩
  · rwa [← hrd]
  · intro e he
    exact fiberFormula_unique S T f hf o q he.2 hdF

/-- All signed regular-fiber sums equal the same integer, independently of
chosen regular values and representations of the actual differential. -/
theorem regular_value_independent_proof
    (htop : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_value_independentType.{u} := by
  intro n a b M N _ _ _ _ _ _ S T f hf hS hT o q y z hy hz hyfin hzfin L K hL hK
  obtain ⟨I, hI, _⟩ := GlobalIntegrationResults.exists_integral S o
  obtain ⟨J, hJ, _⟩ := GlobalIntegrationResults.exists_integral T q
  obtain ⟨d, hd, _⟩ := degree_exists_proof htop S T f hf hS hT o q I J hI hJ
  obtain ⟨hyfin', hdY⟩ := hd.2 y hy
  obtain ⟨hzfin', hdZ⟩ := hd.2 z hz
  exact (hdY L hL).symm.trans (hdZ K hK)

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem degree_exists_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.degree_existsType.{u} :=
  degree_exists_proof h1

/-- Conditional helper with the entire ordered frozen upstream contract. -/
theorem regular_value_independent_conditional
    (h0 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_comparisonType.{u})
    (h1 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.compact_top_degreeType.{u})
    (h2 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.exact_iff_integral_zeroType.{u})
    (h3 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.top_degreeType.{u})
    (h4 : Specs.SmoothManifolds.DeRham.OrientedTopDegree.zero_dimensionType.{u}) :
    Specs.SmoothManifolds.Degree.RegularFibers.regular_value_independentType.{u} :=
  regular_value_independent_proof h1

end SmoothManifolds.DegreeResults

universe v8_closure_2bd3681ebf052b3c_u0
theorem _root_.«SmoothManifolds».«DegreeResults».«degree_exists» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«degree_existsType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«degree_exists_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«nonzero_degree_surjective» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«nonzero_degree_surjectiveType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«nonzero_degree_surjective_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«real_scalar» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«real_scalarType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«real_scalar_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«regular_fiber_finite» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«regular_fiber_finiteType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«regular_fiber_finite_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«regular_value_exists» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«regular_value_existsType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«regular_value_exists_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«regular_value_independent» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«regular_value_independentType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«regular_value_independent_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
theorem _root_.«SmoothManifolds».«DegreeResults».«zero_dimension» : _root_.«Specs».«SmoothManifolds».«Degree».«RegularFibers».«zero_dimensionType».{v8_closure_2bd3681ebf052b3c_u0} :=
  @_root_.«SmoothManifolds».«DegreeResults».«zero_dimension_conditional».{v8_closure_2bd3681ebf052b3c_u0} (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_comparison».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«compact_top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«exact_iff_integral_zero».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«top_degree».{v8_closure_2bd3681ebf052b3c_u0}) (@_root_.«SmoothManifolds».«OrientedTopDegreeResults».«zero_dimension».{v8_closure_2bd3681ebf052b3c_u0})
