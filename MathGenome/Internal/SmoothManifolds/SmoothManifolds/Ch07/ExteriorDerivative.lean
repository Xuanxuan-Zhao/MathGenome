import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch07.ExteriorDerivative
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.Atlases
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.FormPullback
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Convex.Topology

/-! Exterior differentiation on the original intrinsic exterior bundles.
The coordinate calculation is proved natural before gluing; the resulting smooth
family satisfies the characterizing axioms and is unique. C¹ and corner calculus,
support, face restriction and the tautological cotangent formula are included. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SmoothManifolds.ExteriorDerivativeResults
open ModelData AtlasData MapData TangentData DifferentialData BundleOperationsData
  CovectorData ExteriorData FormPullbackData ExteriorDerivativeData Module Set Filter
open scoped Topology
universe u v

/-- Any fiberwise zero-preserving map over a continuous base map has this support bound. -/
theorem sectionSupport_map_subset {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {E : Y → Type u} {F : X → Type u} [∀ y, Zero (E y)] [∀ x, Zero (F x)]
    (f : X → Y) (hf : Continuous f) (A : (x : X) → E (f x) → F x)
    (hA : ∀ x, A x 0 = 0) (s : (y : Y) → E y) :
    sectionSupport (fun x => A x (s (f x))) ⊆ f ⁻¹' sectionSupport s := by
  apply closure_minimal _ (isClosed_closure.preimage hf)
  intro x hx
  apply subset_closure
  intro hs
  exact hx (by change A x (s (f x)) = 0; rw [hs, hA])

theorem pullback_support :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.pullback_supportType.{u} := by
  intro n m a b M N _ _ S T f hf L k ω
  exact sectionSupport_map_subset
    (E := fun q => ExteriorData.Fiber (TangentSpace T q) k)
    (F := fun p => ExteriorData.Fiber (TangentSpace S p) k)
    f hf (fun p z => fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (f p)) k (L p) z)
    (fun _ => LinearMap.map_zero _) ω

theorem proper_pullback_compact_support :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.proper_pullback_compact_supportType.{u} := by
  intro n m a b M N _ _ S T f hf L k ω hω
  exact (hf.isCompact_preimage hω).of_isClosed_subset isClosed_closure
    (pullback_support S T f hf.continuous L k ω)

theorem closed_embedding_proper :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_embedding_properType.{u} := by
  intro X Y _ _ i hi
  exact hi.isProperMap

theorem closed_face_inclusion_proper :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.closed_face_inclusion_properType.{u} := by
  intro X _ A hA
  exact hA.isProperMap_subtypeVal

/-- Unique differentiability identifies the ambient Fréchet derivatives before
alternation. No regularity outside the common relative germ is needed. -/
theorem extension_independence :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.extension_independenceType := by
  intro n k s hs x hx ω η hω hη heq
  have hd : fderiv ℝ ω x = fderiv ℝ η x :=
    (hs x hx).eq hω.hasFDerivAt.hasFDerivWithinAt
      (hη.hasFDerivAt.hasFDerivWithinAt.congr_of_eventuallyEq heq
        (heq.eq_of_nhdsWithin hx))
  exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin hd

/-- Orthants are products of one-sided intervals and unrestricted coordinates. -/
theorem uniqueDiffOn_orthant :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.uniqueDiffOn_orthantType := by
  intro n c
  have heq : orthantSet n c =
      Set.pi {i : Fin n | i.val < c.val} (fun _ => Set.Ici (0 : ℝ)) := by
    ext x
    rfl
  change UniqueDiffOn ℝ (orthantSet n c)
  rw [heq]
  exact UniqueDiffOn.pi (fun _ _ => uniqueDiffOn_Ici 0)

/-- Relative open subsets inherit unique derivatives from the full corner. -/
theorem uniqueDiffOn_orthantDomain {n : ℕ} {c : Fin (n+1)}
    {s : Set (Orthant n c)} (hs : IsOpen s) :
    UniqueDiffOn ℝ (Subtype.val '' s : Set (Euclidean n)) := by
  obtain ⟨U, hU, hEq⟩ := hs.image_val
  rw [hEq, inter_comm]
  exact (uniqueDiffOn_orthant n c).inter hU

/-- A shared proof for restrictions to any domain with unique derivatives. -/
theorem extDeriv_eq_on_extensions {n k : ℕ} {s : Set (Euclidean n)}
    (hs : UniqueDiffOn ℝ s) {U V : Set (Euclidean n)} (hU : IsOpen U) (hV : IsOpen V)
    {ω η : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ}
    (hω : ContDiffOn ℝ 1 ω U) (hη : ContDiffOn ℝ 1 η V)
    (heq : EqOn ω η (s ∩ U ∩ V)) {x : Euclidean n} (hx : x ∈ s)
    (hxU : x ∈ U) (hxV : x ∈ V) : extDeriv ω x = extDeriv η x := by
  apply extension_independence n k (s ∩ U ∩ V) ((hs.inter hU).inter hV) x
    ⟨⟨hx, hxU⟩, hxV⟩ ω η
    ((hω.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num))
    ((hη.contDiffAt (hV.mem_nhds hxV)).differentiableAt (by norm_num))
  exact heq.eventuallyEq.filter_mono inf_le_right

theorem orthant_extension_independence :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.orthant_extension_independenceType := by
  intro n k c s hs U V hU hV ω η hω hη heq x hx hxU hxV
  refine extDeriv_eq_on_extensions (uniqueDiffOn_orthantDomain hs) hU hV hω hη
    ?_ (x := x.val) ⟨x, hx, rfl⟩ hxU hxV
  rintro _ ⟨⟨⟨y, hy, rfl⟩, hyU⟩, hyV⟩
  exact heq y hy hyU hyV

theorem model_extension_independence :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.model_extension_independenceType := by
  intro n k a s hs U V hU hV ω η hω hη heq x hx hxU hxV
  refine extDeriv_eq_on_extensions (uniqueDiffOn_modelDomain hs) hU hV hω hη
    ?_ (x := x.val) ⟨x, hx, rfl⟩ hxU hxV
  rintro _ ⟨⟨⟨y, hy, rfl⟩, hyU⟩, hyV⟩
  exact heq y hy hyU hyV

theorem ambient_derivative_continuous :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_continuousType := by
  intro n k U hU ω hω
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean n) ℝ).continuous.comp_continuousOn
    (hω.continuousOn_fderiv_of_isOpen hU (by norm_num))

theorem ambient_derivative_square :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_derivative_squareType := by
  intro n k U hU ω hω x hx
  exact extDeriv_extDeriv_apply (hω.contDiffAt (hU.mem_nhds hx)) (by simp)

theorem ambient_naturality :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_naturalityType := by
  intro n m k U V hU hV ω f hω hf hmap x hx
  exact extDeriv_pullback
    ((hω.contDiffAt (hV.mem_nhds (hmap hx))).differentiableAt (by norm_num))
    (hf.contDiffAt (hU.mem_nhds hx)) (by simp)

theorem ambient_dimension_zero :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.ambient_dimension_zeroType := by
  intro k ω x
  ext v
  exact ContinuousAlternatingMap.map_coord_zero (extDeriv ω x) 0
    (Subsingleton.elim (v 0) 0)

/-- Transport between equal exterior degrees preserves the zero element. -/
theorem exteriorDegreeCast_zero {V : Type u} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) :
    Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) (0 : ExteriorData.Fiber V i) h = 0 := by
  subst j
  rfl

/-- Zero coefficients have zero derivatives, including at chart boundaries. -/
theorem coordinateDerivative_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) : coordinateDerivative C k c hc 0 p hp = 0 := by
  have hz (I : Index n k) : ambientCoefficient C k c hc 0 I = 0 := by
    classical
    funext z
    unfold ambientCoefficient
    split_ifs <;> try rfl
    dsimp only [coefficients, Pi.zero_apply]
    rw [LinearEquiv.map_zero]
    rfl
  simpa [coordinateDerivative, coordinateExpression, hz] using
    exteriorDegreeCast_zero (V := TangentSpace S p) (1+k) (k+1) (Nat.add_comm 1 k)

theorem coordinate_locality :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_localityType.{u} := by
  intro n a M _ S C k c hc ω η p hp heq
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [ContinuousAt, c.left_inv hp] using c.symm.continuousAt (c.map_source hp)
  have hcoef (I : Index n k) :
      (fun z : ModelSpace n a => ambientCoefficient C k c hc ω I z.val) =ᶠ[𝓝 (c p)]
      (fun z : ModelSpace n a => ambientCoefficient C k c hc η I z.val) := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hp), ht.eventually heq] with z hz he
    simp only [ambientCoefficient, dite_eq_left z.property, dite_eq_left hz, coefficients, he]
  have hder (I : Index n k) :
      fderivWithin ℝ (ambientCoefficient C k c hc ω I) (Subtype.val '' c.target) (c p).val =
      fderivWithin ℝ (ambientCoefficient C k c hc η I) (Subtype.val '' c.target) (c p).val := by
    have he : ambientCoefficient C k c hc ω I =ᶠ[𝓝[modelSet n a] (c p).val]
        ambientCoefficient C k c hc η I := by
      rw [← map_nhds_subtype_val (c p)]
      exact hcoef I
    have hd : (Subtype.val '' c.target : Set (Euclidean n)) ⊆ modelSet n a := by
      rintro _ ⟨z, _, rfl⟩
      exact z.property
    exact (he.filter_mono (nhdsWithin_mono _ hd)).fderivWithin_eq
      (he.self_of_nhdsWithin (c p).property)
  unfold coordinateDerivative
  simp only [hder]

theorem derivative_unique :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_uniqueType.{u} := by
  intro n a M _ S C k ω η ζ hη hζ
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  exact (hη c hc p hp).trans (hζ c hc p hp).symm

theorem derivative_locality :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_localityType.{u} := by
  intro n a M _ S C k ω α η β hη hβ p heq
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  rw [hη c hc p hp, hβ c hc p hp]
  exact coordinate_locality C k c hc ω α p hp heq

theorem derivative_support :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_supportType.{u} := by
  intro n a M _ S C k ω η hη
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_contra hω
  have hz : ∀ᶠ q in 𝓝 p, ω q = 0 := by
    have hh := isClosed_closure.isOpen_compl.mem_nhds hω
    filter_upwards [hh] with q hq
    by_contra hne
    exact hq (subset_closure hne)
  obtain ⟨c, hc, hpc⟩ := S.smoothStructure.property.1.1 p
  apply hp
  rw [hη c hc p hpc, coordinate_locality C k c hc ω 0 p hpc hz,
    coordinateDerivative_zero]

theorem coordinate_formula_extension :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.coordinate_formula_extensionType.{u} := by
  intro n a M _ S C k c hc ω p hp U F hU hpU hF heq
  have hpoint : (c p).val ∈ (Subtype.val '' c.target : Set (Euclidean n)) :=
    ⟨c p, c.map_source hp, rfl⟩
  have hd (I : Index n k) :
      fderivWithin ℝ (ambientCoefficient C k c hc ω I) (Subtype.val '' c.target) (c p).val =
        fderiv ℝ (F I) (c p).val := by
    have he : ambientCoefficient C k c hc ω I =ᶠ[𝓝[Subtype.val '' c.target] (c p).val] F I := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hpU)] with z hz hzU
      obtain ⟨q, hq, rfl⟩ := hz
      simp only [ambientCoefficient, dite_eq_left q.property, dite_eq_left hq]
      exact (heq q hq hzU I).symm
    rw [he.fderivWithin_eq_of_mem hpoint]
    exact ((hF I).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num)
      |>.fderivWithin (uniqueDiffOn_modelDomain c.open_target _ hpoint)
  simp only [coordinateDerivative, hd]

theorem zero_derivative :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_derivativeType.{u} := by
  intro n a M _ S C k c hc p hp
  exact (coordinateDerivative_zero C k c hc p hp).symm

theorem zero_dim_derivative :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_derivativeType.{u} := by
  intro a M _ S C k ω c hc p hp
  symm
  simpa [coordinateDerivative, coordinateExpression] using
    exteriorDegreeCast_zero (V := TangentSpace S p) (1+k) (k+1) (Nat.add_comm 1 k)

theorem derivative_compact_support :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.derivative_compact_supportType.{u} := by
  intro n a M _ S C k ω η hη hω
  exact hω.of_isClosed_subset isClosed_closure (derivative_support C k ω η hη)

/-- Lowering the requested regularity preserves local coefficient extensions. -/
theorem regularField_mono {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    {r s : ℕ∞} (hrs : r ≤ s) {ω : Field S k} (hω : IsRegularField C s k ω) :
    IsRegularField C r k ω := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc p
  exact ⟨U, hU, hpU, F, hF.of_le (by exact_mod_cast hrs), he⟩

theorem regularField_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r : ℕ∞) {ω η : Field S k} (hω : IsRegularField C r k ω)
    (hη : IsRegularField C r k η) : IsRegularField C r k (ω+η) := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hω c hc p
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hη c hc p
  refine ⟨U ∩ V, hU.inter hV, ⟨hpU, hpV⟩, F+G,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), ?_⟩
  intro q hq
  rw [Pi.add_apply, heF q hq.1, heG q hq.2]
  funext I
  simp [ExteriorData.coefficients, map_add]

theorem regularField_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r : ℕ∞) (t : ℝ) {ω : Field S k} (hω : IsRegularField C r k ω) :
    IsRegularField C r k (t • ω) := by
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc p
  refine ⟨U, hU, hpU, t • F, hF.const_smul t, ?_⟩
  intro q hq
  rw [Pi.smul_apply, he q hq]
  funext I
  simp [ExteriorData.coefficients, map_smul]

/-- Even order zero regularity entails continuity of every coefficient. -/
theorem regular_continuous :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.regular_continuousType.{u} := by
  intro n a M _ S C k r ω hω c hc I
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc p
  have hcoord : ContinuousAt (fun q : c.source => (c q.val).val) p :=
    (continuous_subtype_val.continuousAt.comp (c.continuousAt p.property)).comp
      continuousAt_subtype_val
  have hFI : ContinuousOn (fun z => F z I) U :=
    (continuous_apply I).comp_continuousOn hF.continuousOn
  apply ((hFI.continuousAt (hU.mem_nhds hpU)).comp
    (f := fun q : c.source => (c q.val).val) hcoord).congr
  filter_upwards [hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hq
  exact congrFun (he q hq) I

/-- C¹ coefficient extensions supply actual within-set derivatives on chart images. -/
theorem differentiableWithinAt_ambientCoefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (hω : IsRegularField C 1 k ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (I : Index n k) :
    DifferentiableWithinAt ℝ (ambientCoefficient C k c hc ω I)
      (Subtype.val '' c.target) (c p).val := by
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc ⟨p, hp⟩
  have hFI := (contDiffOn_pi.mp hF I).contDiffAt (hU.mem_nhds hpU)
  apply (hFI.differentiableAt (by norm_num)).differentiableWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hpU)] with z hz hzU
    obtain ⟨q, hq, rfl⟩ := hz
    simp only [ambientCoefficient, dite_eq_left q.property, dite_eq_left hq]
    simpa only [c.right_inv hq] using
      (congrFun (he ⟨c.symm q, c.map_target hq⟩
        (by simpa only [c.right_inv hq] using hzU)) I).symm
  · exact ⟨c p, c.map_source hp, rfl⟩

/-- Degree transport is linear. -/
theorem exteriorDegreeCast_add {V : Type u} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (x y : ExteriorData.Fiber V i) :
    Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) (x+y) h =
      Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) x h +
      Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) y h := by
  subst j
  rfl

theorem exteriorDegreeCast_smul {V : Type u} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (r : ℝ) (x : ExteriorData.Fiber V i) :
    Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) (r • x) h =
      r • Eq.ndrec (motive := fun d => ExteriorData.Fiber V d) x h := by
  subst j
  rfl

theorem coordinateExpression_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A B : Index n k → Euclidean n →L[ℝ] ℝ) :
    coordinateExpression C k c hc p hp (A+B) =
      coordinateExpression C k c hc p hp A + coordinateExpression C k c hc p hp B := by
  unfold coordinateExpression
  simp only [Pi.add_apply, add_apply, add_smul, Finset.sum_add_distrib]
  exact exteriorDegreeCast_add (V := TangentSpace S p) (1+k) (k+1) (Nat.add_comm 1 k) _ _

theorem coordinateExpression_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (r : ℝ) (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    coordinateExpression C k c hc p hp (r • A) = r • coordinateExpression C k c hc p hp A := by
  unfold coordinateExpression
  simp only [Pi.smul_apply, smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum]
  exact exteriorDegreeCast_smul (V := TangentSpace S p) (1+k) (k+1) (Nat.add_comm 1 k) r _

theorem ambientCoefficient_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω η : Field S k) (I : Index n k) :
    ambientCoefficient C k c hc (ω+η) I =
      ambientCoefficient C k c hc ω I + ambientCoefficient C k c hc η I := by
  classical
  funext z
  simp only [Pi.add_apply]
  unfold ambientCoefficient
  split_ifs <;> simp_all [ExteriorData.coefficients, map_add]

theorem ambientCoefficient_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (r : ℝ) (ω : Field S k) (I : Index n k) :
    ambientCoefficient C k c hc (r • ω) I = r • ambientCoefficient C k c hc ω I := by
  classical
  funext z
  simp only [Pi.smul_apply]
  unfold ambientCoefficient
  split_ifs <;> simp_all [ExteriorData.coefficients, map_smul]

/-- Real linearity of the intrinsic coordinate derivative on C¹ fields. -/
theorem coordinateDerivative_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω η : Field S k) (hω : IsRegularField C 1 k ω) (hη : IsRegularField C 1 k η)
    (p : M) (hp : p ∈ c.source) :
    coordinateDerivative C k c hc (ω+η) p hp =
      coordinateDerivative C k c hc ω p hp + coordinateDerivative C k c hc η p hp := by
  have hder (I : Index n k) := fderivWithin_add
    (uniqueDiffOn_modelDomain c.open_target _ ⟨c p, c.map_source hp, rfl⟩)
    (differentiableWithinAt_ambientCoefficient C k ω hω c hc p hp I)
    (differentiableWithinAt_ambientCoefficient C k η hη c hc p hp I)
  unfold coordinateDerivative
  simp_rw [ambientCoefficient_add, hder]
  exact
    coordinateExpression_add C k c hc p hp
      (fun I => fderivWithin ℝ (ambientCoefficient C k c hc ω I)
        (Subtype.val '' c.target) (c p).val)
      (fun I => fderivWithin ℝ (ambientCoefficient C k c hc η I)
        (Subtype.val '' c.target) (c p).val)

theorem coordinateDerivative_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (r : ℝ) (ω : Field S k) (hω : IsRegularField C 1 k ω) (p : M) (hp : p ∈ c.source) :
    coordinateDerivative C k c hc (r • ω) p hp = r • coordinateDerivative C k c hc ω p hp := by
  have hder (I : Index n k) := fderivWithin_const_smul
    (uniqueDiffOn_modelDomain c.open_target _ ⟨c p, c.map_source hp, rfl⟩)
    (differentiableWithinAt_ambientCoefficient C k ω hω c hc p hp I) r
  unfold coordinateDerivative
  simp_rw [ambientCoefficient_smul, hder]
  exact
    coordinateExpression_smul C k c hc p hp r
      (fun I => fderivWithin ℝ (ambientCoefficient C k c hc ω I)
        (Subtype.val '' c.target) (c p).val)

/-- Linearity for any derivatives satisfying the coordinate characterization. -/
theorem derivative_add {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω α : Field S k) (η β : Field S (k+1))
    (hω : IsRegularField C 1 k ω) (hα : IsRegularField C 1 k α)
    (hη : HasExteriorDerivative C ω η) (hβ : HasExteriorDerivative C α β) :
    HasExteriorDerivative C (ω+α) (η+β) := by
  intro c hc p hp
  rw [Pi.add_apply, hη c hc p hp, hβ c hc p hp,
    coordinateDerivative_add C k c hc ω α hω hα p hp]

theorem derivative_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r : ℝ) (ω : Field S k) (η : Field S (k+1)) (hω : IsRegularField C 1 k ω)
    (hη : HasExteriorDerivative C ω η) : HasExteriorDerivative C (r • ω) (r • η) := by
  intro c hc p hp
  rw [Pi.smul_apply, hη c hc p hp, coordinateDerivative_smul C k c hc r ω hω p hp]

/-- The coefficient of a scalar in the empty coordinate wedge is the scalar. -/
theorem exterior_zero_coefficient {V : Type u} [AddCommGroup V] [Module ℝ V] (n : ℕ)
    (b : Module.Basis (Fin n) ℝ V) (r : ℝ) (I : Index n 0) :
    (b.exteriorPower 0).repr ((exteriorPower.zeroEquiv ℝ V).symm r) I = r := by
  have he : (exteriorPower.zeroEquiv ℝ V).symm r =
      r • b.exteriorPower 0 I := by
    simp only [exteriorPower.zeroEquiv_symm_apply, exteriorPower.basis_apply]
    congr 2
    exact funext fun i => Fin.elim0 i
  rw [he]
  simp

theorem scalarField_coefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (f : M → ℝ)
    (p : c.source) (I : Index n 0) :
    ExteriorData.coefficients C 0 c hc (scalarField S f) p I = f p.val := by
  dsimp only [ExteriorData.coefficients, scalarField]
  exact exterior_zero_coefficient (V := Module.Dual ℝ (TangentSpace S p.val)) n
    (((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis) (f p.val) I

/-- The empty wedge is the multiplicative unit in each homogeneous degree. -/
theorem exterior_wedge_degree_zero {V : Type u} [AddCommGroup V] [Module ℝ V]
    (k : ℕ) (x : ExteriorData.Fiber V k) (α : Fin 0 → Module.Dual ℝ V) :
    ExteriorData.wedge (V := V) (k := k) (l := 0) x (exteriorPower.ιMulti ℝ 0 α) = x := by
  apply Subtype.ext
  simp [ExteriorData.wedge, exteriorPower.wedge, ExteriorAlgebra.ιMulti]

/-- In degree zero the coordinate sum is the ordinary differential expansion. -/
theorem coordinateExpression_degree_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : Euclidean n →L[ℝ] ℝ) :
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p)))
      (coordinateExpression C 0 c hc p hp (fun _ => A)) =
      ∑ j : Fin n, A (Pi.single j 1) •
        coordinateCovector C.tangent.fiberCoordinates c hc p hp j := by
  classical
  let : Unique (Index n 0) :=
    { default := ⟨∅, rfl⟩
      uniq := fun I => Subtype.ext (Finset.card_eq_zero.mp I.property) }
  simp only [coordinateExpression, Nat.add_zero, exterior_wedge_degree_zero,
    Fintype.sum_unique, map_sum, map_smul, LinearEquiv.apply_symm_apply]

/-- The intrinsic coordinate derivative agrees with the already constructed
ordinary differential of every smooth function, in all charts and dimensions. -/
theorem function_derivative :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.function_derivativeType.{u} := by
  intro n a M _ S C f hf c hc p hp
  obtain ⟨F, hF⟩ := exists_germChartExtension S p c hc hp (functionGerm S f hf p)
  obtain ⟨U, hU, hpU, hFU⟩ := hF.1
  have he : (fun q => F (c q).val) =ᶠ[𝓝 p] f := Germ.coe_eq.mp hF.2
  have ht : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa only [ContinuousAt, c.left_inv hp] using c.symm.continuousAt (c.map_source hp)
  have hd (I : Index n 0) :
      fderivWithin ℝ (ambientCoefficient C 0 c hc (scalarField S f) I)
        (Subtype.val '' c.target) (c p).val = fderiv ℝ F (c p).val := by
    have heq : (fun z : ModelSpace n a => ambientCoefficient C 0 c hc (scalarField S f) I z.val)
        =ᶠ[𝓝 (c p)] (fun z => F z.val) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source hp), ht.eventually he] with z hz hez
      simp only [ambientCoefficient, dite_eq_left z.property, dite_eq_left hz,
        scalarField_coefficient]
      simpa only [c.right_inv hz] using hez.symm
    have heq' : ambientCoefficient C 0 c hc (scalarField S f) I =ᶠ[𝓝[modelSet n a] (c p).val] F := by
      rw [← map_nhds_subtype_val (c p)]
      exact heq
    have hsub : (Subtype.val '' c.target : Set (Euclidean n)) ⊆ modelSet n a := by
      rintro _ ⟨z, _, rfl⟩
      exact z.property
    rw [(heq'.filter_mono (nhdsWithin_mono _ hsub)).fderivWithin_eq_of_mem
      ⟨c p, c.map_source hp, rfl⟩]
    exact (hFU.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
      |>.fderivWithin (uniqueDiffOn_modelDomain c.open_target _ ⟨c p, c.map_source hp, rfl⟩)
  apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [coordinateDerivative, hd, coordinateExpression_degree_zero]
  exact (Covectors.differential_coordinates S C f hf c hc p hp F hF).2

open FrameData

/-- Restriction to an open subspace retains the actual extension germs. -/
theorem vectorSmoothAt_restrict {n : ℕ} {a : ModelKind} {X : Type u}
    [TopologicalSpace X] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Set (ModelChart n a X)) (U : Set X) (hU : IsOpen U)
    (f : X → V) (p : U) (hf : VectorSmoothAt A f p.val) :
    VectorSmoothAt (openSubsetAtlas A U hU) (fun q : U => f q.val) p := by
  refine ⟨hf.1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne, c, hc, rfl⟩ hp
  obtain ⟨W, hW, hpW, F, hF, he⟩ := hf.2 c hc (by simpa using hp)
  exact ⟨W, hW, hpW, F, hF, he.comp_tendsto continuousAt_subtype_val⟩

/-- On a chart source, extension on an entire relative coordinate neighborhood
is equivalent to smoothness defined by extension germs in the restricted atlas.
Shrinking the ambient neighborhood converts germ agreement into exact agreement. -/
theorem locallySmoothAlong_chart_iff {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (f : c.source → V) :
    LocallyContDiffAlong (⊤ : ℕ∞) (fun p : c.source => (c p.val).val) f ↔
      VectorSmooth (openSubsetAtlas S.smoothStructure.val c.source c.open_source) f := by
  constructor
  · intro h p
    obtain ⟨U, hU, hpU, F, hF, he⟩ := h p
    have htotal : VectorSmoothAt S.smoothStructure.val (FrameData.totalize f) p.val := by
      apply BundleOperations.vectorSmoothAt_of_chart S (FrameData.totalize f) p.val c hc
        p.property U hU hpU F hF
      filter_upwards [c.open_source.mem_nhds p.property,
        (continuous_subtype_val.continuousAt.comp (c.continuousAt p.property)).preimage_mem_nhds
          (hU.mem_nhds hpU)] with q hq hqU
      rw [FrameData.totalize_of_mem f q hq]
      exact he ⟨q, hq⟩ hqU
    have hr := vectorSmoothAt_restrict S.smoothStructure.val c.source c.open_source
      (FrameData.totalize f) p htotal
    simpa only [FrameData.totalize_of_mem f _ (Subtype.property _)] using hr
  · intro h p
    have ht := (h p).totalize c.open_source
    obtain ⟨U, hU, hpU, F, hF, he⟩ := ht.2 c hc p.property
    obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp he
    obtain ⟨W, hW, hWT⟩ := isOpen_induced_iff.mp (c.symm.isOpen_inter_preimage hO)
    have hpW : (c p.val).val ∈ W := by
      change c p.val ∈ Subtype.val ⁻¹' W
      rw [hWT]
      exact ⟨c.map_source p.property, by
        change c.symm (c p.val) ∈ O
        simpa only [c.left_inv p.property] using hpO⟩
    refine ⟨U ∩ W, hU.inter hW, ⟨hpU, hpW⟩, F, hF.mono inter_subset_left, ?_⟩
    intro q hq
    have hqO : q.val ∈ O := by
      have hh : c q.val ∈ c.symm.source ∩ c.symm ⁻¹' O := by
        rw [← hWT]
        exact hq.2
      have hhO : c.symm (c q.val) ∈ O := hh.2
      simpa only [c.left_inv q.property] using hhO
    have hh : F (c q.val).val = FrameData.totalize f q.val := hOsub hqO
    simpa only [FrameData.totalize_of_mem f q.val q.property] using hh

/-- The local coefficient regularity convention agrees with the canonical
smooth section interface, including degree zero and boundary charts. -/
theorem smooth_coefficients :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_coefficientsType.{u} := by
  intro n a M _ S C k B ω
  rw [ExteriorAlgebraResults.smooth_iff_coefficients C k B ω]
  constructor
  · intro h c hc
    apply (locallySmoothAlong_chart_iff c hc _).mpr
    intro p
    exact VectorSmoothAt.pi (fun I => h c hc I p)
  · intro h c hc I p
    have hh := (locallySmoothAlong_chart_iff c hc _).mp (h c hc) p
    exact hh.postcomp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Index n k => ℝ) I).contDiff

/-- The zero field has coefficient extensions of every order. -/
theorem regularField_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (r : ℕ∞) (k : ℕ) : IsRegularField C r k (0 : Field S k) := by
  intro c hc p
  refine ⟨univ, isOpen_univ, mem_univ _, fun _ => 0, contDiffOn_const, ?_⟩
  intro q _
  funext I
  simp [ExteriorData.coefficients]

theorem zero_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) : IsForm B (0 : Field S k) :=
  (smooth_coefficients C k B 0).mpr (regularField_zero C ⊤ k)

/-- On a zero-dimensional manifold the zero operator satisfies every axiom,
and every proposed family necessarily has the same positive-degree values. -/
theorem zero_dim_family_exists :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.zero_dim_family_existsType.{u} := by
  intro a M _ S C B
  refine ⟨fun _ _ => 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k ω _
      exact zero_form C (k+1) (B (k+1))
    · intro k α β _ _
      exact (add_zero (0 : Field S (k+1))).symm
    · intro k r α _
      exact (smul_zero r).symm
    · intro f hf p
      have hzero := derivative_unique C 0 (scalarField S f) _ 0
        (function_derivative C f hf) (zero_dim_derivative C 0 (scalarField S f))
      exact (congrFun hzero p).symm
    · intro k ω _
      rfl
    · intro k l α β _ _ p
      simp
  · intro E _ k ω _
    funext p
    exact (ExteriorAlgebraResults.fields_above_dimension C (k+1) (Nat.zero_lt_succ k)
      (E k ω) p).symm

/-- Degree transport commutes with induced exterior maps. -/
theorem exteriorDegreeCast_map {V : Type u} {W : Type v} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W)
    (i j : ℕ) (h : i = j) (x : ⋀[ℝ]^i V) :
    exteriorPower.map j L (Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h) =
      Eq.ndrec (motive := fun d => ⋀[ℝ]^d W) (exteriorPower.map i L x) h := by
  subst j
  rfl

/-- Coefficient derivative synthesis in a fixed standard coframe. -/
def standardDerivativeExpression (n k : ℕ) (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    ⋀[ℝ]^(k+1) (Euclidean n) :=
  Eq.ndrec (motive := fun d => ⋀[ℝ]^d (Euclidean n))
    (∑ I : Index n k, ∑ j : Fin n, (A I (Pi.single j 1)) •
      exteriorPower.wedge ℝ (Euclidean n) 1 k
        ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1))
        (exteriorPower.ιMulti ℝ k (fun i =>
          Pi.single (Set.powersetCard.ofFinEmbEquiv.symm I i) 1))) (Nat.add_comm 1 k)

/-- Synthesis is independent of which vector space carries the ordered coframe. -/
theorem coordinateExpression_standard {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    coordinateExpression C k c hc p hp A =
      exteriorPower.map (k+1)
        (((Pi.basisFun ℝ (Fin n)).map
          (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.equivFun.symm.toLinearMap)
        (standardDerivativeExpression n k A) := by
  let e := ((Pi.basisFun ℝ (Fin n)).map
          (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.equivFun.symm
  have he (j : Fin n) : e (Pi.single j 1) =
      coordinateCovector C.tangent.fiberCoordinates c hc p hp j := by
    rw [show e (Pi.single j 1) =
      ((Pi.basisFun ℝ (Fin n)).map
        (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis j from
        by simp [e, Basis.equivFun_symm_apply]]
    exact ExteriorAlgebraResults.coordinate_dualBasis C.tangent.fiberCoordinates c hc p hp j
  have hone (j : Fin n) : exteriorPower.map 1 e.toLinearMap
      ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1)) =
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (coordinateCovector C.tangent.fiberCoordinates c hc p hp j) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
    have ht := LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (R := ℝ) e.toLinearMap)
      ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1))
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he] using ht
  change _ = exteriorPower.map (k+1) e.toLinearMap _
  rw [standardDerivativeExpression, exteriorDegreeCast_map]
  unfold coordinateExpression
  simp only [map_sum, map_smul, ExteriorAlgebraResults.map_wedge, hone,
    exteriorPower.map_apply_ιMulti, Function.comp_def, LinearEquiv.coe_coe, he]

/-- Increasing coefficients of synthesis are constant linear expressions in A. -/
theorem coordinateExpression_coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    ((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.exteriorPower (k+1)).equivFun
        (coordinateExpression C k c hc p hp A)) =
      ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
        (standardDerivativeExpression n k A) := by
  let b := ((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis
  have hb : (Pi.basisFun ℝ (Fin n)).map b.equivFun.symm = b := by
    ext j
    simp [Basis.equivFun_symm_apply]
  rw [coordinateExpression_standard]
  change (b.exteriorPower (k+1)).equivFun
      (exteriorPower.map (k+1) b.equivFun.symm.toLinearMap _) = _
  rw [← hb, ExteriorAlgebraResults.exteriorBasis_map]
  simp only [Basis.map_equivFun, LinearEquiv.trans_apply]
  exact congrArg ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
    ((BundleOperations.exteriorEquiv (k+1) b.equivFun.symm).symm_apply_apply _)

/-- The degree equality used in coordinate synthesis preserves addition. -/
theorem exteriorPowerDegreeCast_add {V : Type u} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (x y : ⋀[ℝ]^i V) :
    Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) (x+y) h =
      Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h +
      Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) y h := by
  subst j
  rfl

theorem exteriorPowerDegreeCast_smul {V : Type u} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (t : ℝ) (x : ⋀[ℝ]^i V) :
    Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) (t • x) h =
      t • Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h := by
  subst j
  rfl

/-- Differentiating coefficient vectors and then synthesizing d uses a fixed
continuous linear map, including empty coefficient types and n=0. -/
def coefficientDerivativeMap (n k : ℕ) :
    (Index n k → Euclidean n →L[ℝ] ℝ) →L[ℝ] (Index n (k+1) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
        (standardDerivativeExpression n k A)
      map_add' := by
        intro A B
        unfold standardDerivativeExpression
        simp only [Pi.add_apply, add_apply, add_smul,
          Finset.sum_add_distrib, exteriorPowerDegreeCast_add, map_add]
      map_smul' := by
        intro r A
        unfold standardDerivativeExpression
        simp only [Pi.smul_apply, smul_apply, smul_eq_mul,
          ← smul_smul, ← Finset.smul_sum, exteriorPowerDegreeCast_smul, map_smul,
          RingHom.id_apply] }

/-- Coefficient differentiation loses one order of regularity on any field
satisfying the all-charts coordinate formula. This does not assert existence. -/
theorem derivative_regular {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (r s : ℕ∞) (hrs : r+1 ≤ s) (ω : Field S k) (η : Field S (k+1))
    (hω : IsRegularField C s k ω) (hη : HasExteriorDerivative C ω η) :
    IsRegularField C r (k+1) η := by
  have hs1 : (1 : ℕ∞) ≤ s := le_trans (by simp) hrs
  intro c hc p
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc p
  let G : Euclidean n → (Index n (k+1) → ℝ) := fun z =>
    coefficientDerivativeMap n k (fun I => fderiv ℝ (fun y => F y I) z)
  have hG : ContDiffOn ℝ r G U := by
    apply (coefficientDerivativeMap n k).contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro I
    exact (contDiffOn_pi.mp hF I).fderiv_of_isOpen hU (by exact_mod_cast hrs)
  refine ⟨U, hU, hpU, G, hG, ?_⟩
  intro q hq
  have hscalar : ∀ I, ContDiffOn ℝ 1 (fun z => F z I) U := fun I =>
    (contDiffOn_pi.mp hF I).of_le (by exact_mod_cast hs1)
  have hext : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I := by
    intro z hz hzU I
    have hh := congrFun (he ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzU)) I
    simpa only [c.right_inv hz] using hh
  have hformula := coordinate_formula_extension C k c hc ω q.val q.property U
    (fun I z => F z I) hU hq hscalar hext
  change ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
      (standardDerivativeExpression n k (fun I => fderiv ℝ (fun y => F y I) (c q.val).val)) =
    ((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm).dualBasis.exteriorPower (k+1)).equivFun
        (η q.val))
  rw [hη c hc q.val q.property, hformula]
  exact (coordinateExpression_coefficients C k c hc q.val q.property _).symm

/-- The coordinate derivative of a C¹ field is continuous whenever it exists. -/
theorem c1_derivative_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)) (hω : IsRegularField C 1 k ω)
    (hη : HasExteriorDerivative C ω η) : IsContinuousField C (k+1) η :=
  regular_continuous C (k+1) 0 η (derivative_regular C k 0 1 (by simp) ω η hω hη)

/-- Smoothness of the intrinsic derivative follows from its coordinate formula. -/
theorem derivative_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (B : FormBundle C k) (E : FormBundle C (k+1)) (ω : Field S k) (η : Field S (k+1))
    (hω : IsForm B ω) (hη : HasExteriorDerivative C ω η) : IsForm E η := by
  apply (smooth_coefficients C (k+1) E η).mpr
  exact derivative_regular C k ⊤ ⊤ (by simp) ω η
    ((smooth_coefficients C k B ω).mp hω) hη


 theorem scalarField_value {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (f : M → ℝ) (p : M) :
    (scalarField S f p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      algebraMap ℝ (ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) (f p) := by
  simp [scalarField, exteriorPower.zeroEquiv_symm_apply, exteriorPower.ιMulti,
    ExteriorAlgebra.ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]

 theorem fieldWedge_scalar {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (f : M → ℝ)
    (k : ℕ) (ω : Field S k) :
    fieldWedge ω (scalarField S f) = fun p => f p • ω p := by
  funext p
  apply Subtype.ext
  change (ω p).val * (scalarField S f p).val = f p • (ω p).val
  rw [scalarField_value, ← Algebra.commutes, Algebra.smul_def]

 theorem axioms_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) : D k 0 = 0 := by
  simpa only [zero_smul] using hD.smul k 0 0 (zero_form C k (B k))

theorem scalarField_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : FormBundle C 0) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) : IsForm B (scalarField S f) := by
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C 0 B (scalarField S f)).mpr
  intro c hc I p
  have hv : FrameData.VectorSmoothAt S.smoothStructure.val (fun y (_ : Fin 1) => f y) p.val :=
    hf p.val
  have hs : FrameData.VectorSmoothAt S.smoothStructure.val f p.val :=
    hv.postcomp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
  simpa only [scalarField_coefficient] using
    vectorSmoothAt_restrict S.smoothStructure.val c.source c.open_source f p hs

 theorem axioms_zero_germ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k)
    (hω : IsForm (B k) ω) (p : M) (hz : ∀ᶠ q in 𝓝 p, ω q = 0) : D k ω p = 0 := by
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hz
  obtain ⟨f, hf, hf01, hf1, hfU, hfcp⟩ := exists_local_bump S p U hU hpU
  have hwedge : fieldWedge ω (scalarField S f) = 0 := by
    rw [fieldWedge_scalar]
    funext q
    by_cases hq : q ∈ U
    · have hωq : ω q = 0 := hUsub hq
      simp only [hωq, smul_zero, Pi.zero_apply]
    · have hfq : f q = 0 := by
        by_contra hn
        exact hq (hfU (subset_closure hn))
      simp only [hfq, zero_smul, Pi.zero_apply]
  have hh := hD.leibniz k 0 ω (scalarField S f) hω (scalarField_form C (B 0) f hf) p
  rw [hwedge] at hh
  simp only [Nat.add_zero] at hh
  rw [axioms_zero C B D hD k] at hh
  have hwp : ω p = 0 := hUsub hpU
  have hfp : f p = 1 := hf1.eq_of_nhds
  have hscalar : scalarField S f p = (scalarField S (fun _ => 1)) p := by rw [scalarField, scalarField, hfp]
  simp only [Pi.zero_apply, hwp, map_zero, LinearMap.zero_apply, Submodule.coe_zero, smul_zero, add_zero] at hh
  have hfiber : ExteriorData.wedge (V := TangentSpace S p) (D k ω p) (scalarField S f p) = D k ω p := by
    have ha := congrFun (fieldWedge_scalar f (k+1) (D k ω)) p
    simpa only [fieldWedge, hfp, one_smul] using ha
  rw [hfiber] at hh
  exact Subtype.val_injective hh.symm

theorem sub_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (α β : Field S k)
    (hα : IsForm B α) (hβ : IsForm B β) : IsForm B (α-β) := by
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  apply (ExteriorAlgebraResults.smooth_iff_coefficients C k B (α-β)).mpr
  intro c hc I p
  have hαc := (ExteriorAlgebraResults.smooth_iff_coefficients C k B α).mp hα c hc I p
  have hβc := (ExteriorAlgebraResults.smooth_iff_coefficients C k B β).mp hβ c hc I p
  have hsub := (hαc.prod hβc).postcomp
    ((ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff)
  simpa [ExteriorData.coefficients, Pi.sub_apply, map_sub, ContinuousLinearMap.fst, ContinuousLinearMap.snd] using hsub

 theorem axioms_locality {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (α β : Field S k)
    (hα : IsForm (B k) α) (hβ : IsForm (B k) β)
    (p : M) (heq : ∀ᶠ q in 𝓝 p, α q = β q) : D k α p = D k β p := by
  have hneg : IsForm (B k) (-β) := by
    simpa only [zero_sub] using sub_form C k (B k) 0 β (zero_form C k (B k)) hβ
  have hnegD : D k (-β) = -(D k β) := by
    have h := hD.smul k (-1) β hβ
    have hb : (-1 : ℝ) • β = -β := by
      funext q
      exact neg_one_smul ℝ (β q)
    have hd : (-1 : ℝ) • D k β = -(D k β) := by
      funext q
      exact neg_one_smul ℝ (D k β q)
    rw [hb, hd] at h
    exact h
  have hsubD : D k (α-β) = D k α - D k β := by
    rw [sub_eq_add_neg, hD.add k α (-β) hα hneg, hnegD, sub_eq_add_neg]
  have hh := axioms_zero_germ C B D hD k (α-β) (sub_form C k (B k) α β hα hβ) p
    (heq.mono (fun q hq => by simpa only [Pi.sub_apply, hq, sub_self]))
  rw [hsubD] at hh
  exact sub_eq_zero.mp hh

theorem axioms_support {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k)
    (hω : IsForm (B k) ω) : sectionSupport (D k ω) ⊆ sectionSupport ω := by
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_contra hωp
  have hz : ∀ᶠ q in 𝓝 p, ω q = 0 := by
    have hh := isClosed_closure.isOpen_compl.mem_nhds hωp
    filter_upwards [hh] with q hq
    by_contra hne
    exact hq (subset_closure hne)
  exact hp (axioms_zero_germ C B D hD k ω hω p hz)

/-- A locally smooth scalar function has a globally smooth representative of its germ.
The hypothesis is only on the specified open neighborhood. -/
theorem scalar_globalize {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (f : M → ℝ)
    (hf : ∀ q ∈ U, PartitionData.ScalarContDiffAt (⊤ : ℕ∞) S.smoothStructure.val f q)
    (p : M) (hp : p ∈ U) :
    ∃ g : M → ℝ, PartitionData.ScalarSmooth S.smoothStructure.val g ∧ g =ᶠ[𝓝 p] f := by
  exact exists_global_representative S p f (hf p hp)


theorem smooth_regular {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (ω : Field S k) (r : ℕ∞)
    (hω : IsForm B ω) : IsRegularField C r k ω :=
  regularField_mono C k le_top ((smooth_coefficients C k B ω).mp hω)

/-- Smooth intrinsic pullback has coefficient extensions of every finite order. -/
theorem smooth_pullback_regular {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (k : ℕ)
    (B : FormBundle C k) (E : FormBundle A k) (ω : Field T k)
    (hω : IsForm E ω) (r : ℕ∞) :
    IsRegularField C r k (FormPullbackData.pullbackField S T f L ω) := by
  apply smooth_regular C k B _ r
  exact FormPullbackResults.pullback_smooth S T C A f hf L hL k B E ω hω

/-- Above either dimension every pullback has coefficient extensions of every order. -/
theorem pullback_regular_above_dimension {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (k : ℕ) (ω : Field T k) (h : n < k ∨ m < k) (r : ℕ∞) :
    IsRegularField C r k (FormPullbackData.pullbackField S T f L ω) := by
  have he : FormPullbackData.pullbackField S T f L ω = 0 :=
    funext (FormPullbackResults.pullback_high_degree S T C A f L k ω h)
  rw [he]
  exact regularField_zero C r k


/-- Addition preserves smooth forms. -/
theorem add_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (α β : Field S k)
    (hα : IsForm B α) (hβ : IsForm B β) : IsForm B (α+β) :=
  (smooth_coefficients C k B _).mpr (regularField_add C k ⊤
    ((smooth_coefficients C k B _).mp hα) ((smooth_coefficients C k B _).mp hβ))

theorem sum_form {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) {ι : Type v} (s : Finset ι) (α : ι → Field S k)
    (hα : ∀ i ∈ s, IsForm B (α i)) : IsForm B (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using zero_form C k B
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact add_form C k B _ _ (hα i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hα j (Finset.mem_insert_of_mem hj)))

/-- Real linearity extends to finite sums of smooth forms. -/
theorem axioms_sum {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) {ι : Type v} (s : Finset ι)
    (α : ι → Field S k) (hα : ∀ i ∈ s, IsForm (B k) (α i)) :
    D k (∑ i ∈ s, α i) = ∑ i ∈ s, D k (α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, axioms_zero C B D hD k]
  | @insert i s hi ih =>
    have hs := fun j hj => hα j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hD.add k _ _ (hα i (Finset.mem_insert_self _ _)) (sum_form C k (B k) s α hs), ih hs]

/-- The characterizing axioms force the coefficient product rule. -/
theorem axioms_function_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω)
    (f : M → ℝ) (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) :
    (D k (fun q => f q • ω q) p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      f p • (D k ω p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) +
      (-1 : ℝ)^k • (ExteriorData.wedge (V := TangentSpace S p) (k := k) (l := 1)
        (ω p) ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (dFunction S f hf p)) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) := by
  have hh := hD.leibniz k 0 ω (scalarField S f) hω (scalarField_form C (B 0) f hf) p
  rw [fieldWedge_scalar] at hh
  simp only [Nat.add_zero, hD.function_rule f hf p] at hh
  rw [show (ExteriorData.wedge (V := TangentSpace S p) (k := k+1) (l := 0)
      (D k ω p) (scalarField S f p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
        f p • (D k ω p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) by
    exact congrArg Subtype.val (congrFun (fieldWedge_scalar f (k+1) (D k ω)) p)] at hh
  exact hh

/-- For a closed factor the axioms force d(fω)=df∧ω. -/
theorem axioms_function_smul_closed {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω)
    (hclosed : D k ω = 0) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) (p : M) :
    (D k (fun q => f q • ω q) p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (dFunction S f hf p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) *
        (ω p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) := by
  have hh := axioms_function_smul C B D hD k ω hω f hf p
  rw [hclosed] at hh
  simp only [Pi.zero_apply, Submodule.coe_zero, smul_zero, zero_add] at hh
  rw [ExteriorAlgebraResults.wedge_comm (TangentSpace S p) k 1] at hh
  simpa only [Nat.mul_one, smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow, one_smul, ExteriorData.wedge, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul] using hh

theorem scalar_globalize_open {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (U : Set M) (hU : IsOpen U) (f : U → ℝ)
    (hf : FrameData.VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU) f)
    (p : U) :
    ∃ g : M → ℝ, PartitionData.ScalarSmooth S.smoothStructure.val g ∧
      g =ᶠ[𝓝 p.val] FrameData.totalize f := by
  apply scalar_globalize S U hU (FrameData.totalize f) ?_ p.val p.property
  intro q hq
  apply (scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val _ q).mpr
  exact FrameData.VectorSmoothAt.totalize hU (hf ⟨q, hq⟩)

 theorem scalar_globalize_coordinate {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) :
    ∃ g : M → ℝ, PartitionData.ScalarSmooth S.smoothStructure.val g ∧
      g =ᶠ[𝓝 p] (fun q => (c q).val j) := by
  apply scalar_globalize S c.source c.open_source (fun q => (c q).val j) ?_ p hp
  intro q hq
  apply scalarContDiffAt_of_chart S.smoothStructure.property.1 hc hq
  exact ⟨univ, isOpen_univ, mem_univ _, fun z => z j,
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).contDiffOn, Filter.EventuallyEq.rfl⟩

 theorem scalar_globalize_coefficient {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k) (ω : Field S k)
    (hω : IsForm B ω) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) (I : Index n k) :
    ∃ g : M → ℝ, PartitionData.ScalarSmooth S.smoothStructure.val g ∧
      g =ᶠ[𝓝 p.val] FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q I) := by
  apply scalar_globalize_open S c.source c.open_source _ _ p
  exact (ExteriorAlgebraResults.smooth_iff_coefficients C k B ω).mp hω c hc I

theorem scalar_globalize_coordinate_differential {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (j : Fin n) :
    ∃ (g : M → ℝ) (hg : PartitionData.ScalarSmooth S.smoothStructure.val g),
      g =ᶠ[𝓝 p] (fun q => (c q).val j) ∧
      ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
        dFunction S g hg q = coordinateCovector C.tangent.fiberCoordinates c hc q hq j := by
  obtain ⟨g, hg, he⟩ := scalar_globalize_coordinate S c hc p hp j
  refine ⟨g, hg, he, ?_⟩
  filter_upwards [he.eventuallyEq_nhds] with q hq hqc
  exact Covectors.coordinateCovector_germ C.tangent.fiberCoordinates c hc q hqc j
    (functionGerm S g hg q) (Germ.coe_eq.mpr hq)

 theorem axioms_exact_closed {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (f : M → ℝ)
    (hf : PartitionData.ScalarSmooth S.smoothStructure.val f) :
    D 1 (fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
      (dFunction S f hf p)) = 0 := by
  have hfunction : D 0 (scalarField S f) = (fun p =>
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (dFunction S f hf p)) := by
    funext p
    exact hD.function_rule f hf p
  rw [← hfunction]
  exact hD.square 0 (scalarField S f) (scalarField_form C (B 0) f hf)

theorem dFunction_const {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : ℝ)
    (hr : PartitionData.ScalarSmooth S.smoothStructure.val (fun _ => r)) (p : M) :
    dFunction S (fun _ => r) hr p = 0 := by
  apply LinearMap.ext
  intro v
  change v.val (functionGerm S (fun _ => r) hr p) = 0
  have hg : functionGerm S (fun _ => r) hr p = algebraMap ℝ (SmoothGerm S p) r := by
    apply Subtype.ext
    rfl
  rw [hg]
  exact derivation_kills_constants (germEvaluation S p) v r

 theorem axioms_constant {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (r : ℝ) : D 0 (scalarField S (fun _ => r)) = 0 := by
  funext p
  rw [hD.function_rule (fun _ => r) (scalarContDiff_const ⊤ _ r) p, dFunction_const, map_zero]
  rfl

 theorem axioms_exact_wedge {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (f : Fin k → M → ℝ)
    (hf : ∀ i, PartitionData.ScalarSmooth S.smoothStructure.val (f i)) :
    IsForm (B k) (fun p => exteriorPower.ιMulti ℝ k (fun i => dFunction S (f i) (hf i) p)) ∧
    D k (fun p => exteriorPower.ιMulti ℝ k (fun i => dFunction S (f i) (hf i) p)) = 0 := by
  induction k with
  | zero =>
      have heq : (fun p => exteriorPower.ιMulti ℝ 0 (fun i => dFunction S (f i) (hf i) p)) =
          scalarField S (fun _ => 1) := by
        funext p
        apply (exteriorPower.zeroEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).injective
        simp [scalarField]
      rw [heq]
      exact ⟨scalarField_form C (B 0) _ (scalarContDiff_const ⊤ _ 1), axioms_constant C B D hD 1⟩
  | succ k ih =>
      let α : Field S k := fun p => exteriorPower.ιMulti ℝ k
        (fun i => dFunction S (f i.castSucc) (hf i.castSucc) p)
      let β : Field S 1 := fun p =>
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
          (dFunction S (f (Fin.last k)) (hf (Fin.last k)) p)
      have hα := ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
      have hβeq : D 0 (scalarField S (f (Fin.last k))) = β := by
        funext p
        exact hD.function_rule _ (hf (Fin.last k)) p
      have hβ : IsForm (B 1) β := hβeq ▸ hD.smooth 0 _ (scalarField_form C (B 0) _ (hf _))
      have hβD : D 1 β = 0 := axioms_exact_closed C B D hD _ (hf (Fin.last k))
      have heq : fieldWedge α β =
          (fun p => exteriorPower.ιMulti ℝ (k+1) (fun i => dFunction S (f i) (hf i) p)) := by
        funext p
        apply Subtype.ext
        change ExteriorAlgebra.ιMulti ℝ k (fun i => dFunction S (f i.castSucc) (hf i.castSucc) p) *
          ExteriorAlgebra.ιMulti ℝ 1 (fun _ => dFunction S (f (Fin.last k)) (hf (Fin.last k)) p) = _
        rw [ExteriorAlgebra.ιMulti_mul_ιMulti, Fin.append_right_eq_snoc]
        congr 1
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp
      rw [← heq]
      refine ⟨ExteriorAlgebraResults.wedge_smooth C k 1 (B k) (B 1) (B (k+1)) α β hα.1 hβ, ?_⟩
      funext p
      apply Subtype.val_injective
      have hh := hD.leibniz k 1 α β hα.1 hβ p
      rw [hα.2, hβD] at hh
      simpa using hh

theorem exists_smooth_coordinate_expansion {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (k : ℕ) (B : FormBundle C k) (ω : Field S k)
    (hω : IsForm B ω) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) :
    ∃ (b : Index n k → M → ℝ) (hb : ∀ I, PartitionData.ScalarSmooth S.smoothStructure.val (b I))
      (x : Fin n → M → ℝ) (hx : ∀ j, PartitionData.ScalarSmooth S.smoothStructure.val (x j)),
      (∀ I, b I =ᶠ[𝓝 p] FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q I)) ∧
      (∀ j, ∀ᶠ q in 𝓝 p, ∀ hq : q ∈ c.source,
        dFunction S (x j) (hx j) q = coordinateCovector C.tangent.fiberCoordinates c hc q hq j) ∧
      ∀ᶠ q in 𝓝 p, ω q = ∑ I : Index n k, b I q •
        exteriorPower.ιMulti ℝ k (fun i =>
          dFunction S (x (Set.powersetCard.ofFinEmbEquiv.symm I i))
            (hx (Set.powersetCard.ofFinEmbEquiv.symm I i)) q) := by
  classical
  choose x hx hxe hdx using fun j : Fin n => scalar_globalize_coordinate_differential C c hc p hp j
  choose b hb hbe using fun I : Index n k => scalar_globalize_coefficient C k B ω hω c hc ⟨p, hp⟩ I
  refine ⟨b, hb, x, hx, hbe, hdx, ?_⟩
  have hbeall : ∀ᶠ q in 𝓝 p, ∀ I, b I q =
      FrameData.totalize (fun q : c.source => ExteriorData.coefficients C k c hc ω q I) q :=
    Filter.eventually_all.mpr hbe
  have hdxall : ∀ᶠ q in 𝓝 p, ∀ j, ∀ hq : q ∈ c.source,
      dFunction S (x j) (hx j) q = coordinateCovector C.tangent.fiberCoordinates c hc q hq j :=
    Filter.eventually_all.mpr hdx
  filter_upwards [hbeall, hdxall, c.open_source.mem_nhds hp] with q hbq hdxq hq
  rw [ExteriorAlgebraResults.coefficient_expansion C k c hc ω ⟨q, hq⟩]
  apply Finset.sum_congr rfl
  intro I _
  rw [hbq I, FrameData.totalize_of_mem _ q hq]
  congr 1
  apply congrArg (exteriorPower.ιMulti ℝ k)
  funext i
  exact (hdxq _ hq).symm


/-- A coefficient extension also represents every global smooth function
with the same local coefficient germ. -/
theorem coefficient_extension_germ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : M) (hp : p ∈ c.source) (I : Index n k)
    (b : M → ℝ) (hb : PartitionData.ScalarSmooth S.smoothStructure.val b)
    (hbe : b =ᶠ[𝓝 p] FrameData.totalize (fun q : c.source => coefficients C k c hc ω q I))
    (U : Set (Euclidean n)) (F : Euclidean n → ℝ) (hU : IsOpen U)
    (hpU : (c p).val ∈ U) (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (heF : ∀ q : c.source, (c q.val).val ∈ U → F (c q.val).val = coefficients C k c hc ω q I) :
    GermChartExtension S p c (functionGerm S b hb p) F := by
  refine ⟨⟨U, hU, hpU, hF⟩, ?_⟩
  apply Germ.coe_eq.mpr
  have hcoord : ContinuousAt (fun q => (c q).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  filter_upwards [hbe, c.open_source.mem_nhds hp,
    hcoord.preimage_mem_nhds (hU.mem_nhds hpU)] with q hbq hqc hqU
  rw [FrameData.totalize_of_mem _ q hqc] at hbq
  exact (heF ⟨q, hqc⟩ hqU).trans hbq.symm


@[irreducible] def coefficientPullback (n m k : ℕ) (J : Euclidean m →L[ℝ] Euclidean n)
    (z : Index m k → ℝ) : Index n k → ℝ :=
  ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
    (exteriorPower.map k J.toLinearMap
      (((Pi.basisFun ℝ (Fin m)).exteriorPower k).equivFun.symm z))

theorem coefficientPullback_formula (n m k : ℕ) (J : Euclidean m →L[ℝ] Euclidean n)
    (z : Index m k → ℝ) (s : Index n k) :
    coefficientPullback n m k J z s =
      ∑ t : Index m k, z t *
        (Matrix.of (fun i j : Fin k =>
          J (Pi.single (Set.powersetCard.ofFinEmbEquiv.symm t i) 1)
            (Set.powersetCard.ofFinEmbEquiv.symm s j))).det := by
  classical
  let bm := (Pi.basisFun ℝ (Fin m)).exteriorPower k
  have he : bm.equivFun.symm z = ∑ t : Index m k, z t • bm t := by
    simp only [Module.Basis.equivFun_symm_apply]
  unfold coefficientPullback
  rw [he]
  simp only [map_sum, map_smul, Module.Basis.equivFun_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  ext t
  simp only [bm, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPower.map_apply_ιMulti, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti, Module.Basis.coord_apply,
    Pi.basisFun_repr, Function.comp_apply, Pi.basisFun_apply]
  rfl

theorem contDiff_coefficientPullback (n m k : ℕ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (fun w : (Euclidean m →L[ℝ] Euclidean n) × (Index m k → ℝ) =>
      coefficientPullback n m k w.1 w.2) := by
  classical
  apply contDiff_pi.mpr
  intro s
  simp only [coefficientPullback_formula, Matrix.det_apply, Matrix.of_apply]
  fun_prop

/-- Increasing coframe coefficients are exactly the usual exterior coordinates. -/
theorem coefficients_eq_coordinate_map {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : Field S k) (p : c.source) :
    letI := (cotangentSpace C).topology
    (fun I => coefficients C k c hc ω p I) =
      ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
        (exteriorPower.map k ((cotangentSpace C).bundle.fiberCoordinates
          ⟨c, hc⟩ p.val ((Covectors.cotangent_baseSet C c hc).symm ▸ p.property)).toLinearMap
            (ω p.val)) := by
  letI := (cotangentSpace C).topology
  obtain ⟨B⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle k
  letI := B.space.topology
  have h := ExteriorAlgebraResults.coefficients_coordinates C B c hc ω p
  have hp : p.val ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact p.property
  have hs : Frames.sectionCoordinates B.space.bundle c.source ⟨c, hc⟩
        (fun q => ω q.val) p = B.modelEquiv (exteriorPower.map k
          ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ p.val hp).toLinearMap (ω p.val)) :=
    ExteriorAlgebraResults.exterior_coordinates (cotangentSpace C).bundle B ⟨c, hc⟩ p.val hp (ω p.val)
  rw [hs, LinearEquiv.symm_apply_apply] at h
  exact h

theorem smooth_pullback_coordinate_matrix {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) (k : ℕ) :
    ∃ J : M → Euclidean m →L[ℝ] Euclidean n,
      VectorSmoothAt S.smoothStructure.val J p ∧
        ∀ y (hy : y ∈ c.source) (hfy : f y ∈ d.source) (ω : Field T k),
          (fun I => coefficients C k c hc (FormPullbackData.pullbackField S T f L ω) ⟨y, hy⟩ I) =
            coefficientPullback n m k (J y)
              (fun I => coefficients A k d hd ω ⟨f y, hfy⟩ I) := by
  classical
  letI := (cotangentSpace C).topology
  letI := (cotangentSpace A).topology
  letI := C.tangent.topology
  letI := A.tangent.topology
  have hdf := TangentBundle.map_smooth S T C.tangent A.tangent f hf L hL
  let v (i : Fin n) (y : M) : TangentSpace S y :=
    if hy : y ∈ c.source then coordinateVector C.tangent.fiberCoordinates c hc y hy i else 0
  let α (j : Fin m) (y : M) : CotangentFiber T (f y) :=
    if hy : f y ∈ d.source then coordinateCovector A.tangent.fiberCoordinates d hd (f y) hy j else 0
  have hv (i : Fin n) : ManifoldSmoothAt S.smoothStructure.val C.tangent.manifold.smoothStructure.val
      (fun y => (⟨y, v i y⟩ : TangentBundleData.TotalSpace S)) p := by
    apply TangentBundle.lift_smoothAt_of_coeff S C.tangent S _ p c hc hp
      (fun _ => Pi.single i 1)
      ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p)
      (VectorSmoothAt.const _ _ _)
    filter_upwards [c.open_source.mem_nhds hp] with y hy
    refine ⟨hy, ?_⟩
    simp [v, hy, coordinateVector]
  have hα (j : Fin m) : ManifoldSmoothAt S.smoothStructure.val
      (cotangentSpace A).bundle.totalManifold.smoothStructure.val
      (fun y => (⟨f y, α j y⟩ : CotangentTotal T)) p := by
    apply Frames.smoothAt_from_trivialization (cotangentSpace A).bundle
      S.smoothStructure.property.1 ⟨d, hd⟩
      (by rw [Covectors.cotangent_baseSet]; exact hfp)
      (hf p) (VectorSmoothAt.const _ (Pi.single j 1) _) (fun _ => rfl)
    filter_upwards [(hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfp)] with y hy
    change f y ∈ d.source at hy
    ext i
    rw [Covectors.cotangent_coordinates A d hd (f y) hy]
    simp only [α, dite_eq_left hy, Covectors.coordinateCovector_apply, Pi.single_apply, eq_comm]
  let J : M → Euclidean m →L[ℝ] Euclidean n := fun y =>
    QuotientBundles.columnOperator (fun j i => α j y (L y (v i y)))
  have hJ : VectorSmoothAt S.smoothStructure.val J p := by
    apply BundleOperations.columnOperator_smooth
    intro j
    apply VectorSmoothAt.pi
    intro i
    apply Covectors.evaluation_smoothAt S A f (α j) (fun y => L y (v i y)) p hf (hα j)
    exact manifoldContDiffAt_comp C.tangent.manifold.smoothStructure.property.1.1
      (hv i) (hdf ⟨p, v i p⟩)
  refine ⟨J, hJ, ?_⟩
  intro y hy hfy ω
  have hyC : y ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hy
  have hyA : f y ∈ (cotangentSpace A).bundle.baseSet ⟨d, hd⟩ := by
    rw [Covectors.cotangent_baseSet]; exact hfy
  let eC := (cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ y hyC
  let eA := (cotangentSpace A).bundle.fiberCoordinates ⟨d, hd⟩ (f y) hyA
  have heJ (lam : CotangentFiber T (f y)) : J y (eA lam) = eC (lam.comp (L y)) := by
    ext i
    have heval := congrArg (fun β : CotangentFiber T (f y) => β (L y (v i y)))
      (Covectors.covector_expansion A.tangent.fiberCoordinates d hd (f y) hfy lam)
    simpa [J, QuotientBundles.columnOperator_apply, eC, eA,
      BundleData.SmoothVectorBundle.fiberCoordinates_apply, Covectors.cotangent_coordinates,
      α, v, hy, hfy, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using heval.symm
  have heLin : eC.toLinearMap.comp (L y).dualMap = (J y).toLinearMap.comp eA.toLinearMap := by
    ext lam i
    exact congrFun (heJ lam).symm i
  have hs := coefficients_eq_coordinate_map C k c hc
    (FormPullbackData.pullbackField S T f L ω) ⟨y, hy⟩
  dsimp only [FormPullbackData.pullbackField, fiberPullback] at hs
  have ht := coefficients_eq_coordinate_map A k d hd ω ⟨f y, hfy⟩
  have heMap := congrArg (fun F => exteriorPower.map k F (ω (f y))) heLin
  simp only [exteriorPower.map_comp, LinearMap.comp_apply] at heMap
  calc
    _ = ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
          (exteriorPower.map k eC.toLinearMap
            (exteriorPower.map k (L y).dualMap (ω (f y)))) := by
      with_reducible exact hs
    _ = ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
          (exteriorPower.map k (J y).toLinearMap
            (exteriorPower.map k eA.toLinearMap (ω (f y)))) := by
      with_reducible exact congrArg _ heMap
    _ = _ := by
      unfold coefficientPullback
      rw [ht, LinearEquiv.symm_apply_apply]

/-- A finite-order coordinate extension germ can be shrunk to actual agreement. -/
theorem localExtensionAt_of_germ {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℕ) (c : ModelChart n a M) (f : c.source → V) (p : c.source)
    (F : Euclidean n → V) (hF : ContDiffAt ℝ r F (c p.val).val)
    (he : (fun y => F (c y).val) =ᶠ[𝓝 p.val] FrameData.totalize f) :
    HasLocalContDiffExtensionAt r (fun q : c.source => (c q.val).val) f p := by
  obtain ⟨U, hpU, hFU⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨U', hUsub, hU', hpU'⟩ := mem_nhds_iff.mp hpU
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp he
  obtain ⟨W, hW, hWT⟩ := isOpen_induced_iff.mp (c.symm.isOpen_inter_preimage hO)
  have hpW : (c p.val).val ∈ W := by
    change c p.val ∈ Subtype.val ⁻¹' W
    rw [hWT]
    exact ⟨c.map_source p.property, by
      change c.symm (c p.val) ∈ O
      simpa only [c.left_inv p.property] using hpO⟩
  refine ⟨U' ∩ W, hU'.inter hW, ⟨hpU', hpW⟩, F, hFU.mono ?_, ?_⟩
  · exact fun z hz => hUsub hz.1
  · intro q hq
    have hqO : q.val ∈ O := by
      have hh : c q.val ∈ c.symm.source ∩ c.symm ⁻¹' O := by
        rw [← hWT]
        exact hq.2
      have hhO : c.symm (c q.val) ∈ O := hh.2
      simpa only [c.left_inv q.property] using hhO
    have hh : F (c q.val).val = FrameData.totalize f q.val := hOsub hqO
    simpa only [FrameData.totalize_of_mem f q.val q.property] using hh

/-- Smooth pullback preserves every finite coefficient regularity class. -/
theorem pullback_regular_finite {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (k r : ℕ) (ω : Field T k) (hω : IsRegularField A r k ω) :
    IsRegularField C r k (FormPullbackData.pullbackField S T f L ω) := by
  classical
  intro c hc p
  obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p.val)
  obtain ⟨J, hJ, heJ⟩ := smooth_pullback_coordinate_matrix S T C A f hf L hL
    c hc d hd p.val p.property hfp k
  obtain ⟨U, hU, hpU, JF, hJF, heJF⟩ := hJ.2 c hc p.property
  obtain ⟨V, hV, hfpV, F, hF, heF⟩ := hω d hd ⟨f p.val, hfp⟩
  obtain ⟨W, hW, hpW, H, hH, heH⟩ := (hf p.val).2 c hc d hd p.property hfp
  have hHeq : H (c p.val).val = (d (f p.val)).val := heH.eq_of_nhds
  let K : Euclidean n → Index n k → ℝ := fun z => coefficientPullback n m k (JF z) (F (H z))
  have hJF' : ContDiffAt ℝ r JF (c p.val).val :=
    (hJF.contDiffAt (hU.mem_nhds hpU)).of_le (by simp)
  have hH' : ContDiffAt ℝ r H (c p.val).val :=
    (hH.contDiffAt (hW.mem_nhds hpW)).of_le (by simp)
  have hF' : ContDiffAt ℝ r F (H (c p.val).val) := by
    rw [hHeq]
    exact hF.contDiffAt (hV.mem_nhds hfpV)
  have hK : ContDiffAt ℝ r K (c p.val).val :=
    (contDiff_coefficientPullback n m k r).contDiffAt.comp _ (hJF'.prodMk (hF'.comp _ hH'))
  apply localExtensionAt_of_germ r c _ p K hK
  have htarget : ContinuousAt (fun y => (d (f y)).val) p.val :=
    continuous_subtype_val.continuousAt.comp ((d.continuousAt hfp).comp (hf p.val).1)
  filter_upwards [c.open_source.mem_nhds p.property,
    (hf p.val).1.preimage_mem_nhds (d.open_source.mem_nhds hfp),
    htarget.preimage_mem_nhds (hV.mem_nhds hfpV), heJF, heH] with y hy hfy hyV hyJ hyH
  change f y ∈ d.source at hfy
  change (d (f y)).val ∈ V at hyV
  rw [FrameData.totalize_of_mem _ y hy]
  dsimp only [K]
  rw [hyJ, hyH, heF ⟨f y, hfy⟩ hyV]
  exact (heJ y hy hfy ω).symm

/-- Smooth pullback preserves the local ambient-extension regularity classes. -/
theorem pullback_regular {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (k : ℕ) (r : ℕ∞) (ω : Field T k) (hω : IsRegularField A r k ω) :
    IsRegularField C r k (FormPullbackData.pullbackField S T f L ω) := by
  cases r using ENat.recTopCoe with
  | top =>
    letI := (cotangentSpace C).topology
    letI := (cotangentSpace A).topology
    obtain ⟨B⟩ := BundleOperations.exists_exterior (cotangentSpace C).bundle k
    obtain ⟨E⟩ := BundleOperations.exists_exterior (cotangentSpace A).bundle k
    have hform : IsForm E ω := (smooth_coefficients A k E ω).mpr hω
    exact (smooth_coefficients C k B _).mp
      (FormPullbackResults.pullback_smooth S T C A f hf L hL k B E ω hform)
  | coe r =>
    exact pullback_regular_finite S T C A f hf L hL k r ω hω

theorem axioms_coordinate_sum {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D : ∀ k, Field S k → Field S (k+1)) (hD : DerivativeAxioms C B D)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (b : Index n k → M → ℝ) (hb : ∀ I, PartitionData.ScalarSmooth S.smoothStructure.val (b I))
    (x : Fin n → M → ℝ) (hx : ∀ j, PartitionData.ScalarSmooth S.smoothStructure.val (x j))
    (hdx : ∀ j, dFunction S (x j) (hx j) p = coordinateCovector C.tangent.fiberCoordinates c hc p hp j)
    (heq : ∀ᶠ q in 𝓝 p, ω q = ∑ I : Index n k, b I q •
      exteriorPower.ιMulti ℝ k (fun i => dFunction S (x (Set.powersetCard.ofFinEmbEquiv.symm I i))
        (hx (Set.powersetCard.ofFinEmbEquiv.symm I i)) q)) :
    (D k ω p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      ∑ I : Index n k,
        ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
            (dFunction S (b I) (hb I) p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) *
          (exteriorPower.ιMulti ℝ k (fun i => coordinateCovector C.tangent.fiberCoordinates
            c hc p hp (Set.powersetCard.ofFinEmbEquiv.symm I i)) :
              ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) := by
  classical
  let W : Index n k → Field S k := fun I q => exteriorPower.ιMulti ℝ k
    (fun i => dFunction S (x (Set.powersetCard.ofFinEmbEquiv.symm I i))
      (hx (Set.powersetCard.ofFinEmbEquiv.symm I i)) q)
  have hW : ∀ I, IsForm (B k) (W I) ∧ D k (W I) = 0 := fun I =>
    axioms_exact_wedge C B D hD k _ _
  let A : Index n k → Field S k := fun I q => b I q • W I q
  have hA : ∀ I, IsForm (B k) (A I) := by
    intro I
    have hh := ExteriorAlgebraResults.wedge_smooth C k 0 (B k) (B 0) (B k)
      (W I) (scalarField S (b I)) (hW I).1 (scalarField_form C (B 0) _ (hb I))
    rw [fieldWedge_scalar] at hh
    exact hh
  have hsum : IsForm (B k) (∑ I, A I) := sum_form C k (B k) Finset.univ A (fun I _ => hA I)
  have hloc : ∀ᶠ q in 𝓝 p, ω q = (∑ I, A I) q := by
    simpa only [Finset.sum_apply, A, W] using heq
  rw [axioms_locality C B D hD k ω (∑ I, A I) hω hsum p hloc,
    axioms_sum C B D hD k Finset.univ A (fun I _ => hA I), Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [show A I = fun q => b I q • W I q from rfl,
    axioms_function_smul_closed C B D hD k (W I) (hW I).1 (hW I).2 (b I) (hb I) p]
  congr 1
  change (exteriorPower.ιMulti ℝ k (fun i => dFunction S
      (x (Set.powersetCard.ofFinEmbEquiv.symm I i)) (hx _) p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = _
  simp only [hdx]

theorem homogeneous_degree_cast_coe {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (x : ⋀[ℝ]^i V) :
    (Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h : ExteriorAlgebra ℝ V) = x.val := by
  subst j
  rfl

theorem global_coordinates :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.global_coordinatesType.{u} := by
  intro n a M _ S C B D hD k ω hω c hc p hp
  classical
  obtain ⟨b, hb, x, hx, hbe, hdx, heq⟩ :=
    exists_smooth_coordinate_expansion C k (B k) ω hω c hc p hp
  have hd := axioms_coordinate_sum C B D hD k ω hω c hc p hp b hb x hx
    (fun j => (hdx j).self_of_nhds hp) heq
  obtain ⟨U, hU, hpU, F, hF, heF⟩ :=
    (smooth_coefficients C k (B k) ω).mp hω c hc ⟨p, hp⟩
  have hFI (I : Index n k) : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => F z I) U :=
    (contDiffOn_pi.mp hF) I
  have hdb (I : Index n k) : dFunction S (b I) (hb I) p = ∑ j : Fin n,
      fderiv ℝ (fun z => F z I) (c p).val (Pi.single j 1) •
        coordinateCovector C.tangent.fiberCoordinates c hc p hp j := by
    exact (Covectors.differential_coordinates S C (b I) (hb I) c hc p hp _
      (coefficient_extension_germ C k c hc ω p hp I (b I) (hb I) (hbe I) U _ hU hpU
        (hFI I) (fun q hq => congrFun (heF q hq) I))).2
  have hformula : coordinateDerivative C k c hc ω p hp =
      coordinateExpression C k c hc p hp (fun I => fderiv ℝ (fun z => F z I) (c p).val) := by
    apply coordinate_formula_extension C k c hc ω p hp U (fun I z => F z I) hU hpU
      (fun I => (hFI I).of_le (by simp))
    intro z hz hzU I
    have hh := congrFun (heF ⟨c.symm z, c.map_target hz⟩ (by
      simpa only [c.right_inv hz] using hzU)) I
    simpa only [c.right_inv hz] using hh
  rw [hformula]
  apply Subtype.val_injective
  rw [hd]
  unfold coordinateExpression
  rw [homogeneous_degree_cast_coe]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro I _
  rw [hdb I, map_sum]
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_mul, smul_mul_assoc]
  rfl

theorem axioms_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (D E : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (hE : DerivativeAxioms C B E)
    (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) : D k ω = E k ω :=
  derivative_unique C k ω (D k ω) (E k ω)
    (global_coordinates C B D hD k ω hω) (global_coordinates C B E hE k ω hω)


namespace Euclidean

theorem continuous_multilinear_euclidean {n k : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin k => Euclidean n) ℝ) : Continuous f := by
  classical
  have he (v : Fin k → Euclidean n) :
      f v = ∑ r : Fin k → Fin n, (∏ i, v i (r i)) • f (fun i => Pi.single (r i) 1) := by
    calc
      f v = f (fun i => ∑ j : Fin n, (v i j) • Pi.single j (1 : ℝ)) := by
        congr 1
        funext i j
        simp [Pi.single_apply]
      _ = ∑ r : Fin k → Fin n, f (fun i => (v i (r i)) • Pi.single (r i) 1) := f.map_sum _
      _ = _ := by simp only [f.map_smul_univ]
  change Continuous (fun v => f v)
  rw [show (fun v => f v) = (fun v => ∑ r : Fin k → Fin n,
      (∏ i, v i (r i)) • f (fun i => Pi.single (r i) 1)) from funext he]
  fun_prop

def evaluateContinuous (n k : ℕ) :
    Fiber (Euclidean n) k →ₗ[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ) where
  toFun ξ := { evaluate (Euclidean n) k ξ with
    cont := continuous_multilinear_euclidean (evaluate (Euclidean n) k ξ).toMultilinearMap }
  map_add' ξ η := by
    ext v
    change evaluate _ _ (ξ + η) v = _
    rw [map_add]
    rfl
  map_smul' r ξ := by
    ext v
    change evaluate _ _ (r • ξ) v = _
    rw [map_smul]
    rfl

@[simp] theorem evaluateContinuous_apply (n k : ℕ) (ξ : Fiber (Euclidean n) k)
    (v : Fin k → Euclidean n) : evaluateContinuous n k ξ v = evaluate (Euclidean n) k ξ v := rfl

theorem evaluateContinuous_bijective (n k : ℕ) : Function.Bijective (evaluateContinuous n k) := by
  have he := SmoothManifolds.ExteriorAlgebraResults.alternating_interpretation (Euclidean n) k
  constructor
  · intro ξ η h
    apply he.1
    ext v
    exact congrArg (fun A : (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ => A v) h
  · intro A
    obtain ⟨ξ, hξ⟩ := he.2 A.toAlternatingMap
    refine ⟨ξ, ?_⟩
    ext v
    exact congrArg (fun B : AlternatingMap ℝ (Euclidean n) ℝ (Fin k) => B v) hξ

def evaluationEquiv (n k : ℕ) :
    Fiber (Euclidean n) k ≃ₗ[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ) :=
  LinearEquiv.ofBijective (evaluateContinuous n k) (evaluateContinuous_bijective n k)

def euclideanExteriorBasis (n k : ℕ) : Basis (Index n k) ℝ (Fiber (Euclidean n) k) :=
  (Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k

def coefficientAlternatingLinearEquiv (n k : ℕ) :
    (Index n k → ℝ) ≃ₗ[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (euclideanExteriorBasis n k).equivFun.symm.trans (evaluationEquiv n k)

def coefficientAlternating (n k : ℕ) :
    (Index n k → ℝ) →L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (coefficientAlternatingLinearEquiv n k).toLinearMap.toContinuousLinearMap

@[simp] theorem coefficientAlternating_apply (n k : ℕ) (a : Index n k → ℝ) :
    coefficientAlternating n k a = ∑ I : Index n k, a I • evaluateContinuous n k
      (euclideanExteriorBasis n k I) := by
  change evaluateContinuous n k ((euclideanExteriorBasis n k).equivFun.symm a) = _
  rw [Module.Basis.equivFun_symm_apply, map_sum]
  simp only [map_smul]

theorem evaluate_cons {V : Type*} [AddCommGroup V] [Module ℝ V] (k : ℕ)
    (α : Module.Dual ℝ V) (β : Fin k → Module.Dual ℝ V) (v : Fin (k+1) → V) :
    evaluate V (k+1) (exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β)) v =
      ∑ i : Fin (k+1), (-1 : ℝ)^i.val * α (v i) *
        evaluate V k (exteriorPower.ιMulti ℝ k β) (i.removeNth v) := by
  rw [SmoothManifolds.ExteriorAlgebraResults.determinant_normalization]
  rw [Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro i hi
  rw [SmoothManifolds.ExteriorAlgebraResults.determinant_normalization]
  congr 2

/-- A constant decomposable k-form multiplied by a coefficient has derivative
    obtained by putting the coefficient differential in the first wedge slot. -/
theorem extDeriv_coefficient_decomposable {n k : ℕ}
    (f : Euclidean n → ℝ) (β : Fin k → Module.Dual ℝ (Euclidean n))
    (x : Euclidean n) (hf : DifferentiableAt ℝ f x) :
    extDeriv (fun y => f y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k β)) x =
      evaluateContinuous n (k+1) (exteriorPower.ιMulti ℝ (k+1)
        (Fin.cons (fderiv ℝ f x).toLinearMap β)) := by
  ext v
  rw [extDeriv_apply]
  · rw [evaluateContinuous_apply, evaluate_cons]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, evaluateContinuous_apply]
    rw [fderiv_mul_const]
    · simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.coe_coe]
      ring
    · exact hf
  · exact hf.smul_const _

/-- The coefficient identification is continuous in both directions. -/
def coefficientAlternatingEquiv (n k : ℕ) :
    (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ) :=
  (coefficientAlternatingLinearEquiv n k).toContinuousLinearEquiv

theorem extDeriv_sum_coefficients {ι : Type*} [Fintype ι] {n k : ℕ}
    (f : ι → Euclidean n → ℝ) (β : ι → Fin k → Module.Dual ℝ (Euclidean n))
    (x : Euclidean n) (hf : ∀ I, DifferentiableAt ℝ (f I) x) :
    extDeriv (fun y => ∑ I, f I y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k (β I))) x =
      evaluateContinuous n (k+1) (∑ I, exteriorPower.ιMulti ℝ (k+1)
        (Fin.cons (fderiv ℝ (f I) x).toLinearMap (β I))) := by
  classical
  have hh : extDeriv (fun y => ∑ I, f I y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k (β I))) x =
      ∑ I, extDeriv (fun y => f I y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k (β I))) x := by
    unfold extDeriv
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun I y => f I y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k (β I)))
      (fun I _ => (hf I).smul_const _)]
    exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclidean n) ℝ) _ _
  rw [hh, map_sum]
  apply Finset.sum_congr rfl
  intro I hI
  exact extDeriv_coefficient_decomposable (f I) (β I) x (hf I)

theorem coefficient_alternating_bridge (n k : ℕ) :
    ∃ e : (Index n k → ℝ) ≃L[ℝ] ((Euclidean n) [⋀^Fin k]→L[ℝ] ℝ),
      (∀ (a : Index n k → ℝ) (v : Fin k → Euclidean n),
        e a v = evaluate (Euclidean n) k
          (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower k).equivFun.symm a) v) ∧
      ∀ (f : Euclidean n → Index n k → ℝ) (x : Euclidean n),
        DifferentiableAt ℝ f x → ∀ v : Fin (k+1) → Euclidean n,
          extDeriv (fun y => e (f y)) x v =
            evaluate (Euclidean n) (k+1) (∑ I : Index n k,
              exteriorPower.ιMulti ℝ (k+1)
                (Fin.cons (fderiv ℝ (fun y => f y I) x).toLinearMap
                  (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
                    (Set.powersetCard.ofFinEmbEquiv.symm I j)))) v := by
  refine ⟨coefficientAlternatingEquiv n k, ?_, ?_⟩
  · intros
    rfl
  · intro f x hf v
    have hh (y : Euclidean n) : coefficientAlternatingEquiv n k (f y) =
        ∑ I : Index n k, f y I • evaluateContinuous n k
          (exteriorPower.ιMulti ℝ k (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
            (Set.powersetCard.ofFinEmbEquiv.symm I j))) := by
      change coefficientAlternating n k (f y) = _
      rw [coefficientAlternating_apply]
      apply Finset.sum_congr rfl
      intro I hI
      congr 2
      exact exteriorPower.basis_apply ℝ k (Pi.basisFun ℝ (Fin n)).dualBasis I
    rw [show (fun y => coefficientAlternatingEquiv n k (f y)) = _ from funext hh]
    rw [extDeriv_sum_coefficients]
    · rfl
    · intro I
      exact (differentiableAt_pi.mp hf) I

theorem exteriorDegreeCast_coe {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (x : ⋀[ℝ]^i V) :
    (Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h : ExteriorAlgebra ℝ V) = x.val := by
  subst j
  rfl

theorem exterior_cons_wedge {V : Type*} [AddCommGroup V] [Module ℝ V] (k : ℕ)
    (α : V) (β : Fin k → V) :
    exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β) =
      Eq.ndrec (motive := fun d => ⋀[ℝ]^d V)
        (exteriorPower.wedge ℝ V 1 k ((exteriorPower.oneEquiv ℝ V).symm α)
          (exteriorPower.ιMulti ℝ k β)) (Nat.add_comm 1 k) := by
  apply Subtype.ext
  rw [exteriorDegreeCast_coe]
  have hα : (exteriorPower.oneEquiv ℝ V).symm α =
      exteriorPower.ιMulti ℝ 1 (fun _ => α) := by
    apply (exteriorPower.oneEquiv ℝ V).injective
    simp [exteriorPower.oneEquiv_ιMulti]
  rw [hα]
  change ExteriorAlgebra.ιMulti ℝ (k+1) (Fin.cons α β) =
    ExteriorAlgebra.ιMulti ℝ 1 (fun _ => α) * ExteriorAlgebra.ιMulti ℝ k β
  rw [ExteriorAlgebra.ιMulti_succ_apply]
  simp [Matrix.vecTail]

/-- Expansion of the coefficient differential in the standard dual frame. -/
theorem exterior_cons_coordinate_expansion {n k : ℕ}
    (α : Module.Dual ℝ (Euclidean n)) (β : Fin k → Module.Dual ℝ (Euclidean n)) :
    exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β) =
      ∑ j : Fin n, α (Pi.single j 1) •
        exteriorPower.ιMulti ℝ (k+1)
          (Fin.cons ((Pi.basisFun ℝ (Fin n)).dualBasis j) β) := by
  let L : Module.Dual ℝ (Euclidean n) →ₗ[ℝ] Fiber (Euclidean n) (k+1) :=
    { toFun := fun α => exteriorPower.ιMulti ℝ (k+1) (Fin.cons α β)
      map_add' := fun α γ => (exteriorPower.ιMulti ℝ (k+1)).map_vecCons_add β α γ
      map_smul' := fun r α => (exteriorPower.ιMulti ℝ (k+1)).map_vecCons_smul β r α }
  change L α = ∑ j : Fin n, α (Pi.single j 1) • L ((Pi.basisFun ℝ (Fin n)).dualBasis j)
  conv_lhs => rw [← (Pi.basisFun ℝ (Fin n)).dualBasis.sum_repr α]
  rw [map_sum]
  simp only [map_smul, Basis.dualBasis_repr, Pi.basisFun_apply]

theorem extDeriv_sum_coefficients_coordinate {ι : Type*} [Fintype ι] {n k : ℕ}
    (f : ι → Euclidean n → ℝ) (β : ι → Fin k → Module.Dual ℝ (Euclidean n))
    (x : Euclidean n) (hf : ∀ I, DifferentiableAt ℝ (f I) x) :
    extDeriv (fun y => ∑ I, f I y • evaluateContinuous n k (exteriorPower.ιMulti ℝ k (β I))) x =
      evaluateContinuous n (k+1) (∑ I, ∑ j : Fin n,
        (fderiv ℝ (f I) x (Pi.single j 1)) •
          Eq.ndrec (motive := fun d => Fiber (Euclidean n) d)
            (wedge (V := Euclidean n) (k := 1) (l := k)
              ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (Euclidean n))).symm
                ((Pi.basisFun ℝ (Fin n)).dualBasis j))
              (exteriorPower.ιMulti ℝ k (β I))) (Nat.add_comm 1 k)) := by
  rw [extDeriv_sum_coefficients f β x hf]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [exterior_cons_coordinate_expansion]
  apply Finset.sum_congr rfl
  intro j hj
  rw [exterior_cons_wedge]
  rfl

theorem dualBasis_synthesis_map (n d : ℕ) (z : ⋀[ℝ]^d (Euclidean n)) :
    ((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower d).equivFun.symm
      (((Pi.basisFun ℝ (Fin n)).exteriorPower d).equivFun z) =
      exteriorPower.map d (Pi.basisFun ℝ (Fin n)).dualBasis.equivFun.symm.toLinearMap z := by
  let b := (Pi.basisFun ℝ (Fin n)).dualBasis
  have hb : (Pi.basisFun ℝ (Fin n)).map b.equivFun.symm = b := by
    ext j
    simp [Basis.equivFun_symm_apply]
  change (b.exteriorPower d).equivFun.symm
    (((Pi.basisFun ℝ (Fin n)).exteriorPower d).equivFun z) = _
  rw [← hb, SmoothManifolds.ExteriorAlgebraResults.exteriorBasis_map]
  simp only [Basis.map_equivFun, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rfl

theorem differential_sum_eq_standard_map (n k : ℕ)
    (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    (∑ I : Index n k, exteriorPower.ιMulti ℝ (k+1)
      (Fin.cons (A I).toLinearMap (fun i => (Pi.basisFun ℝ (Fin n)).dualBasis
        (Set.powersetCard.ofFinEmbEquiv.symm I i)))) =
      exteriorPower.map (k+1) (Pi.basisFun ℝ (Fin n)).dualBasis.equivFun.symm.toLinearMap
        (standardDerivativeExpression n k A) := by
  let e := (Pi.basisFun ℝ (Fin n)).dualBasis.equivFun.symm
  have he (j : Fin n) : e (Pi.single j 1) = (Pi.basisFun ℝ (Fin n)).dualBasis j := by
    simp [e, Basis.equivFun_symm_apply]
  have hone (j : Fin n) : exteriorPower.map 1 e.toLinearMap
      ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1)) =
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (Euclidean n))).symm
        ((Pi.basisFun ℝ (Fin n)).dualBasis j) := by
    apply (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (Euclidean n))).injective
    have ht := LinearMap.congr_fun (exteriorPower.oneEquiv_naturality (R := ℝ) e.toLinearMap)
      ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1))
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, he] using ht
  have hi (I : Index n k) : exteriorPower.ιMulti ℝ (k+1)
      (Fin.cons (A I).toLinearMap (fun i => (Pi.basisFun ℝ (Fin n)).dualBasis
        (Set.powersetCard.ofFinEmbEquiv.symm I i))) =
      ∑ j : Fin n, (A I (Pi.single j 1)) •
        Eq.ndrec (motive := fun d => Fiber (Euclidean n) d)
          (wedge (V := Euclidean n) (k := 1) (l := k)
            ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (Euclidean n))).symm
              ((Pi.basisFun ℝ (Fin n)).dualBasis j))
            (exteriorPower.ιMulti ℝ k (fun i => (Pi.basisFun ℝ (Fin n)).dualBasis
              (Set.powersetCard.ofFinEmbEquiv.symm I i)))) (Nat.add_comm 1 k) := by
    rw [exterior_cons_coordinate_expansion]
    apply Finset.sum_congr rfl
    intro j hj
    rw [exterior_cons_wedge]
    rfl
  rw [show (fun I : Index n k => exteriorPower.ιMulti ℝ (k+1)
      (Fin.cons (A I).toLinearMap (fun i => (Pi.basisFun ℝ (Fin n)).dualBasis
        (Set.powersetCard.ofFinEmbEquiv.symm I i)))) = _ from funext hi]
  change _ = exteriorPower.map (k+1) e.toLinearMap _
  rw [standardDerivativeExpression, exteriorDegreeCast_map]
  apply Subtype.ext
  rw [exteriorDegreeCast_coe]
  simp only [map_sum, map_smul, SmoothManifolds.ExteriorAlgebraResults.map_wedge, hone,
    exteriorPower.map_apply_ιMulti, Function.comp_def, LinearEquiv.coe_coe, he,
    Submodule.coe_sum, Submodule.coe_smul, exteriorDegreeCast_coe]

/-- The library exterior derivative agrees with the literal coordinate coefficient
operator on every differentiable Euclidean coefficient field. -/
theorem extDeriv_coefficientAlternatingEquiv {n k : ℕ}
    (F : Euclidean n → Index n k → ℝ) (x : Euclidean n)
    (hF : DifferentiableAt ℝ F x) :
    extDeriv (fun y => coefficientAlternatingEquiv n k (F y)) x =
      coefficientAlternatingEquiv n (k+1)
        (coefficientDerivativeMap n k (fun I => fderiv ℝ (fun y => F y I) x)) := by
  have hh (y : Euclidean n) : coefficientAlternatingEquiv n k (F y) =
      ∑ I : Index n k, F y I • evaluateContinuous n k
        (exteriorPower.ιMulti ℝ k (fun j => (Pi.basisFun ℝ (Fin n)).dualBasis
          (Set.powersetCard.ofFinEmbEquiv.symm I j))) := by
    change coefficientAlternating n k (F y) = _
    rw [coefficientAlternating_apply]
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    exact exteriorPower.basis_apply ℝ k (Pi.basisFun ℝ (Fin n)).dualBasis I
  rw [show (fun y => coefficientAlternatingEquiv n k (F y)) = _ from funext hh]
  rw [extDeriv_sum_coefficients]
  · change evaluateContinuous n (k+1) _ = evaluateContinuous n (k+1)
      (((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower (k+1)).equivFun.symm
        (((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
          (standardDerivativeExpression n k (fun I => fderiv ℝ (fun y => F y I) x))))
    rw [dualBasis_synthesis_map, differential_sum_eq_standard_map]
  · intro I
    exact (differentiableAt_pi.mp hF) I

theorem coefficient_derivative_square {n k : ℕ}
    (F : Euclidean n → Index n k → ℝ) (U : Set (Euclidean n)) (hU : IsOpen U)
    (hF : ContDiffOn ℝ 2 F U) (x : Euclidean n) (hx : x ∈ U) :
    coefficientDerivativeMap n (k+1) (fun J => fderiv ℝ
      (fun y => coefficientDerivativeMap n k (fun I => fderiv ℝ (fun z => F z I) y) J) x) = 0 := by
  let G : Euclidean n → Index n (k+1) → ℝ := fun y =>
    coefficientDerivativeMap n k (fun I => fderiv ℝ (fun z => F z I) y)
  have hG : ContDiffOn ℝ 1 G U := by
    apply (coefficientDerivativeMap n k).contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro I
    exact (contDiffOn_pi.mp hF I).fderiv_of_isOpen hU (by norm_num)
  have hω : ContDiffOn ℝ 2 (fun y => coefficientAlternatingEquiv n k (F y)) U :=
    (coefficientAlternatingEquiv n k).toContinuousLinearMap.contDiff.comp_contDiffOn hF
  have he : extDeriv (fun y => coefficientAlternatingEquiv n k (F y)) =ᶠ[𝓝 x]
      (fun y => coefficientAlternatingEquiv n (k+1) (G y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact extDeriv_coefficientAlternatingEquiv F y
      ((hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hzero : extDeriv (fun y => coefficientAlternatingEquiv n (k+1) (G y)) x = 0 := by
    rw [← he.extDeriv_eq]
    exact extDeriv_extDeriv_apply (hω.contDiffAt (hU.mem_nhds hx)) (by simp)
  rw [extDeriv_coefficientAlternatingEquiv G x
    ((hG.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))] at hzero
  apply (coefficientAlternatingEquiv n (k+2)).injective
  simpa only [map_zero] using hzero

open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
  SmoothManifolds.ExteriorDerivativeData

/-- The intrinsic coordinate derivative squares to zero for C² fields, whenever
both derivatives are represented by the coordinate relation. -/
theorem intrinsic_derivative_square {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (ω : Field S k) (η : Field S (k+1)) (ζ : Field S ((k+1)+1))
    (hω : IsRegularField C 2 k ω) (hη : HasExteriorDerivative C ω η)
    (hζ : HasExteriorDerivative C η ζ) : ζ = 0 := by
  funext p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, he⟩ := hω c hc ⟨p, hp⟩
  let G : Euclidean n → Index n (k+1) → ℝ := fun z =>
    coefficientDerivativeMap n k (fun I => fderiv ℝ (fun y => F y I) z)
  have hG : ContDiffOn ℝ 1 G U := by
    apply (coefficientDerivativeMap n k).contDiff.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro I
    exact (contDiffOn_pi.mp hF I).fderiv_of_isOpen hU (by norm_num)
  have hextF : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I := by
    intro z hz hzU I
    have hh := congrFun (he ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzU)) I
    simpa only [c.right_inv hz] using hh
  have heG (q : c.source) (hq : (c q.val).val ∈ U) :
      G (c q.val).val = (fun J => coefficients C (k+1) c hc η q J) := by
    have hscalar : ∀ I, ContDiffOn ℝ 1 (fun z => F z I) U := fun I =>
      (contDiffOn_pi.mp hF I).of_le (by norm_num)
    have hformula := coordinate_formula_extension C k c hc ω q.val q.property U
      (fun I z => F z I) hU hq hscalar hextF
    change ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+1)).equivFun
      (standardDerivativeExpression n k (fun I => fderiv ℝ (fun y => F y I) (c q.val).val)) =
      ((((Pi.basisFun ℝ (Fin n)).map
        (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm).dualBasis.exteriorPower (k+1)).equivFun
          (η q.val))
    rw [hη c hc q.val q.property, hformula]
    exact (coordinateExpression_coefficients C k c hc q.val q.property _).symm
  have hextG : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ J,
      G z.val J = coefficients C (k+1) c hc η ⟨c.symm z, c.map_target hz⟩ J := by
    intro z hz hzU J
    have hh := congrFun (heG ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzU)) J
    simpa only [c.right_inv hz] using hh
  rw [hζ c hc p hp, coordinate_formula_extension C (k+1) c hc η p hp U
    (fun J z => G z J) hU hpU (fun J => contDiffOn_pi.mp hG J) hextG]
  apply ((((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.exteriorPower ((k+1)+1)).equivFun).injective
  rw [coordinateExpression_coefficients]
  simp only [Pi.zero_apply, map_zero]
  change coefficientDerivativeMap n (k+1) (fun J => fderiv ℝ (fun z => G z J) (c p).val) = 0
  exact coefficient_derivative_square F U hU hF (c p).val hpU


end Euclidean

namespace CoefficientCalculus
def coefficientBasis (n k : ℕ) := (Pi.basisFun ℝ (Fin n)).exteriorPower k

def coefficientSynthesis (n k : ℕ) (a : Index n k → ℝ) : ⋀[ℝ]^k (Euclidean n) :=
  (coefficientBasis n k).equivFun.symm a

def coefficientWedge (n k l : ℕ) :
    (Index n k → ℝ) →L[ℝ] (Index n l → ℝ) →L[ℝ] (Index n (k+l) → ℝ) :=
  let L := ((exteriorPower.wedge ℝ (Euclidean n) k l).compl₁₂
    (coefficientBasis n k).equivFun.symm.toLinearMap
    (coefficientBasis n l).equivFun.symm.toLinearMap).compr₂
    (coefficientBasis n (k+l)).equivFun.toLinearMap
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp L)

@[simp] theorem coefficientSynthesis_coefficientWedge (n k l : ℕ) (a : Index n k → ℝ) (b : Index n l → ℝ) :
    coefficientSynthesis n (k+l) (coefficientWedge n k l a b) =
      exteriorPower.wedge ℝ (Euclidean n) k l (coefficientSynthesis n k a) (coefficientSynthesis n l b) := by
  exact (coefficientBasis n (k+l)).equivFun.symm_apply_apply _

theorem exteriorDegreeCast_coe {V : Type*} [AddCommGroup V] [Module ℝ V]
    (i j : ℕ) (h : i = j) (x : ⋀[ℝ]^i V) :
    (Eq.ndrec (motive := fun d => ⋀[ℝ]^d V) x h : ExteriorAlgebra ℝ V) = x.val := by
  subst j
  rfl

@[simp] theorem oneEquiv_symm_coe {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    ((exteriorPower.oneEquiv ℝ V).symm v : ExteriorAlgebra ℝ V) = ExteriorAlgebra.ι ℝ v := by
  have hv : (exteriorPower.oneEquiv ℝ V).symm v = exteriorPower.ιMulti ℝ 1 (fun _ => v) := by
    apply (exteriorPower.oneEquiv ℝ V).injective
    simp [exteriorPower.oneEquiv_ιMulti]
  rw [hv]
  simp

theorem standardDerivativeExpression_eq_sum (n k : ℕ)
    (A : Index n k → Euclidean n →L[ℝ] ℝ) :
    (standardDerivativeExpression n k A : ExteriorAlgebra ℝ (Euclidean n)) =
      ∑ j : Fin n, ExteriorAlgebra.ι ℝ (Pi.single j 1) *
        (coefficientSynthesis n k (fun I => A I (Pi.single j 1)) : ExteriorAlgebra ℝ (Euclidean n)) := by
  unfold standardDerivativeExpression
  rw [exteriorDegreeCast_coe]
  simp only [Submodule.coe_sum, Submodule.coe_smul, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, oneEquiv_symm_coe]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold coefficientSynthesis
  rw [Basis.equivFun_symm_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.mul_sum, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro I hI
  congr 2
  simp [coefficientBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family, Function.comp_def, Pi.basisFun_apply]

/-- A vector-valued coefficient derivative evaluates componentwise. -/
theorem fderiv_coefficient_apply {n k : ℕ} (f : Euclidean n → Index n k → ℝ)
    (x : Euclidean n) (hf : DifferentiableAt ℝ f x) (I : Index n k) :
    fderiv ℝ (fun y => f y I) x = (ContinuousLinearMap.proj I).comp (fderiv ℝ f x) := by
  exact ((ContinuousLinearMap.proj I).hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- The usual bilinear product rule, transported back to genuine exterior powers. -/
theorem coefficientSynthesis_fderiv_wedge_apply {n k l : ℕ}
    (f : Euclidean n → Index n k → ℝ) (g : Euclidean n → Index n l → ℝ)
    (x v : Euclidean n) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    (coefficientSynthesis n (k+l) (fderiv ℝ (fun y => coefficientWedge n k l (f y) (g y)) x v) :
      ExteriorAlgebra ℝ (Euclidean n)) =
      (coefficientSynthesis n k (fderiv ℝ f x v) : ExteriorAlgebra ℝ (Euclidean n)) * (coefficientSynthesis n l (g x) : ExteriorAlgebra ℝ (Euclidean n)) +
      (coefficientSynthesis n k (f x) : ExteriorAlgebra ℝ (Euclidean n)) * coefficientSynthesis n l (fderiv ℝ g x v) := by
  rw [(coefficientWedge n k l).fderiv_of_bilinear hf hg]
  simp only [add_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precompL_apply]
  change (coefficientSynthesis n (k+l)
    (coefficientWedge n k l (f x) (fderiv ℝ g x v) +
      coefficientWedge n k l (fderiv ℝ f x v) (g x)) : ExteriorAlgebra ℝ (Euclidean n)) = _
  simp only [coefficientSynthesis, map_add, Submodule.coe_add]
  rw [← coefficientSynthesis, ← coefficientSynthesis, coefficientSynthesis_coefficientWedge, coefficientSynthesis_coefficientWedge]
  exact add_comm _ _

/-- Graded Leibniz for differentiable Euclidean exterior coefficient fields. -/
theorem coordinate_derivative_leibniz {n k l : ℕ}
    (f : Euclidean n → Index n k → ℝ) (g : Euclidean n → Index n l → ℝ)
    (x : Euclidean n) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    (standardDerivativeExpression n (k+l)
      (fun I => fderiv ℝ (fun y => coefficientWedge n k l (f y) (g y) I) x) :
        ExteriorAlgebra ℝ (Euclidean n)) =
      (exteriorPower.wedge ℝ (Euclidean n) (k+1) l
        (standardDerivativeExpression n k (fun I => fderiv ℝ (fun y => f y I) x))
        (coefficientSynthesis n l (g x)) : ExteriorAlgebra ℝ (Euclidean n)) +
      (-1 : ℝ)^k • (exteriorPower.wedge ℝ (Euclidean n) k (l+1)
        (coefficientSynthesis n k (f x))
        (standardDerivativeExpression n l (fun I => fderiv ℝ (fun y => g y I) x)) :
          ExteriorAlgebra ℝ (Euclidean n)) := by
  have hw : DifferentiableAt ℝ (fun y => coefficientWedge n k l (f y) (g y)) x :=
    ((coefficientWedge n k l).hasFDerivAt_of_bilinear hf.hasFDerivAt hg.hasFDerivAt).differentiableAt
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]
  simp_rw [standardDerivativeExpression_eq_sum, fderiv_coefficient_apply _ x hw,
    fderiv_coefficient_apply f x hf, fderiv_coefficient_apply g x hg]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  change (∑ j, ExteriorAlgebra.ι ℝ (Pi.single j 1) *
    (coefficientSynthesis n (k+l) (fderiv ℝ (fun y => coefficientWedge n k l (f y) (g y)) x (Pi.single j 1)) :
      ExteriorAlgebra ℝ (Euclidean n))) = _
  simp_rw [coefficientSynthesis_fderiv_wedge_apply f g x _ hf hg]
  change (∑ j, ExteriorAlgebra.ι ℝ (Pi.single j 1) *
    ((coefficientSynthesis n k (fderiv ℝ f x (Pi.single j 1)) : ExteriorAlgebra ℝ (Euclidean n)) * (coefficientSynthesis n l (g x) : ExteriorAlgebra ℝ (Euclidean n)) +
      (coefficientSynthesis n k (f x) : ExteriorAlgebra ℝ (Euclidean n)) * (coefficientSynthesis n l (fderiv ℝ g x (Pi.single j 1)) : ExteriorAlgebra ℝ (Euclidean n)))) =
    (∑ j, ExteriorAlgebra.ι ℝ (Pi.single j 1) *
      (coefficientSynthesis n k (fderiv ℝ f x (Pi.single j 1)) : ExteriorAlgebra ℝ (Euclidean n))) * (coefficientSynthesis n l (g x) : ExteriorAlgebra ℝ (Euclidean n)) +
    (-1 : ℝ)^k • ((coefficientSynthesis n k (f x) : ExteriorAlgebra ℝ (Euclidean n)) *
      ∑ j, ExteriorAlgebra.ι ℝ (Pi.single j 1) *
        (coefficientSynthesis n l (fderiv ℝ g x (Pi.single j 1)) : ExteriorAlgebra ℝ (Euclidean n)))
  rw [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact (mul_assoc _ _ _).symm
  · apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc]
    have hcomm := SmoothManifolds.ExteriorAlgebraResults.homogeneous_anticomm
      (Euclidean n) 1 k ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm (Pi.single j 1))
        (coefficientSynthesis n k (f x))
    rw [oneEquiv_symm_coe, one_mul] at hcomm
    rw [hcomm, smul_mul_assoc, mul_assoc]

theorem exterior_coefficients_wedge {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n k l : ℕ} (b : Basis (Fin n) ℝ V) (α : ⋀[ℝ]^k V) (β : ⋀[ℝ]^l V) :
    (b.exteriorPower (k+l)).equivFun (exteriorPower.wedge ℝ V k l α β) =
      coefficientWedge n k l ((b.exteriorPower k).equivFun α) ((b.exteriorPower l).equivFun β) := by
  let e := b.equivFun.symm
  have hb : (Pi.basisFun ℝ (Fin n)).map e = b := by
    ext j
    simp [e, Basis.equivFun_symm_apply]
  rw [← hb, SmoothManifolds.ExteriorAlgebraResults.exteriorBasis_map]
  simp only [Basis.map_equivFun, LinearEquiv.trans_apply]
  change ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+l)).equivFun
    ((SmoothManifolds.BundleOperations.exteriorEquiv (k+l) e).symm
      (exteriorPower.wedge ℝ V k l α β)) = _
  change _ = ((Pi.basisFun ℝ (Fin n)).exteriorPower (k+l)).equivFun
    (exteriorPower.wedge ℝ (Euclidean n) k l
      (((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun.symm
        ((((Pi.basisFun ℝ (Fin n)).map e).exteriorPower k).equivFun α))
      (((Pi.basisFun ℝ (Fin n)).exteriorPower l).equivFun.symm
        ((((Pi.basisFun ℝ (Fin n)).map e).exteriorPower l).equivFun β)))
  rw [SmoothManifolds.ExteriorAlgebraResults.exteriorBasis_map,
    SmoothManifolds.ExteriorAlgebraResults.exteriorBasis_map]
  simp only [Basis.map_equivFun, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  congr 1
  exact SmoothManifolds.ExteriorAlgebraResults.map_wedge e.symm.toLinearMap α β

theorem exterior_synthesis_eq_map {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n k : ℕ} (b : Basis (Fin n) ℝ V) (a : Index n k → ℝ) :
    (b.exteriorPower k).equivFun.symm a =
      exteriorPower.map k b.equivFun.symm.toLinearMap (coefficientSynthesis n k a) := by
  let e := b.equivFun.symm
  have hb : (Pi.basisFun ℝ (Fin n)).map e = b := by
    ext j
    simp [e, Basis.equivFun_symm_apply]
  rw [← hb, SmoothManifolds.ExteriorAlgebraResults.exteriorBasis_map]
  simp only [Basis.map_equivFun, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  rfl

open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.CovectorData
  SmoothManifolds.ExteriorDerivativeData

set_option maxHeartbeats 4000000 in
/-- Graded Leibniz for the intrinsic C¹ coordinate derivative relation. -/
theorem intrinsic_derivative_leibniz {n : ℕ} {a : SmoothManifolds.ModelKind} {M : Type*}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k l : ℕ)
    (α : Field S k) (β : Field S l) (η : Field S (k+1)) (ζ : Field S (l+1))
    (θ : Field S ((k+l)+1))
    (hα : IsRegularField C 1 k α) (hβ : IsRegularField C 1 l β)
    (hη : HasExteriorDerivative C α η) (hζ : HasExteriorDerivative C β ζ)
    (hθ : HasExteriorDerivative C (fieldWedge α β) θ) (p : M) :
    (θ p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
      (wedge (V := TangentSpace S p) (η p) (β p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) +
      (-1 : ℝ)^k • (wedge (V := TangentSpace S p) (α p) (ζ p) :
        ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) := by
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨U, hU, hpU, F, hF, heF⟩ := hα c hc ⟨p, hp⟩
  obtain ⟨V, hV, hpV, G, hG, heG⟩ := hβ c hc ⟨p, hp⟩
  let W := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hpW : (c p).val ∈ W := ⟨hpU, hpV⟩
  have hFW : ContDiffOn ℝ 1 F W := hF.mono Set.inter_subset_left
  have hGW : ContDiffOn ℝ 1 G W := hG.mono Set.inter_subset_right
  let H : Euclidean n → Index n (k+l) → ℝ := fun z => coefficientWedge n k l (F z) (G z)
  have hH : ContDiffOn ℝ 1 H W :=
    ((coefficientWedge n k l).contDiff.comp_contDiffOn hFW).clm_apply hGW
  have hextF : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ W → ∀ I,
      F z.val I = coefficients C k c hc α ⟨c.symm z, c.map_target hz⟩ I := by
    intro z hz hzW I
    have hh := congrFun (heF ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzW.1)) I
    simpa only [c.right_inv hz] using hh
  have hextG : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ W → ∀ J,
      G z.val J = coefficients C l c hc β ⟨c.symm z, c.map_target hz⟩ J := by
    intro z hz hzW J
    have hh := congrFun (heG ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzW.2)) J
    simpa only [c.right_inv hz] using hh
  have hextH : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ W → ∀ K,
      H z.val K = coefficients C (k+l) c hc (fieldWedge α β) ⟨c.symm z, c.map_target hz⟩ K := by
    intro z hz hzW K
    let q : c.source := ⟨c.symm z, c.map_target hz⟩
    let b := ((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc q.val q.property).symm).dualBasis
    have hfe : F z.val = fun I => coefficients C k c hc α q I := funext (hextF z hz hzW)
    have hge : G z.val = fun J => coefficients C l c hc β q J := funext (hextG z hz hzW)
    change coefficientWedge n k l (F z.val) (G z.val) K = _
    rw [hfe, hge]
    exact congrFun (exterior_coefficients_wedge b (α q.val) (β q.val)).symm K
  have hηp : η p = coordinateExpression C k c hc p hp
      (fun I => fderiv ℝ (fun z => F z I) (c p).val) :=
    (hη c hc p hp).trans (coordinate_formula_extension C k c hc α p hp W
      (fun I z => F z I) hW hpW (fun I => contDiffOn_pi.mp hFW I) hextF)
  have hζp : ζ p = coordinateExpression C l c hc p hp
      (fun J => fderiv ℝ (fun z => G z J) (c p).val) :=
    (hζ c hc p hp).trans (coordinate_formula_extension C l c hc β p hp W
      (fun J z => G z J) hW hpW (fun J => contDiffOn_pi.mp hGW J) hextG)
  have hθp : θ p = coordinateExpression C (k+l) c hc p hp
      (fun K => fderiv ℝ (fun z => H z K) (c p).val) :=
    (hθ c hc p hp).trans (coordinate_formula_extension C (k+l) c hc (fieldWedge α β) p hp W
      (fun K z => H z K) hW hpW (fun K => contDiffOn_pi.mp hH K) hextH)
  let b := ((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis
  let e := b.equivFun.symm.toLinearMap
  have hαp : α p = exteriorPower.map k e (coefficientSynthesis n k (F (c p).val)) := by
    rw [heF ⟨p, hp⟩ hpU, ← exterior_synthesis_eq_map b]
    exact ((b.exteriorPower k).equivFun.symm_apply_apply (α p)).symm
  have hβp : β p = exteriorPower.map l e (coefficientSynthesis n l (G (c p).val)) := by
    rw [heG ⟨p, hp⟩ hpV, ← exterior_synthesis_eq_map b]
    exact ((b.exteriorPower l).equivFun.symm_apply_apply (β p)).symm
  have hamb := coordinate_derivative_leibniz F G (c p).val
    ((hFW.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by norm_num))
    ((hGW.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by norm_num))
  have hmap := congrArg (ExteriorAlgebra.map e) hamb
  rw [hθp, hηp, hζp, hαp, hβp]
  simp only [coordinateExpression_standard,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, exteriorPower.coe_map]
  simpa only [map_add, map_smul, map_mul, exteriorPower.wedge,
    DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul] using hmap


end CoefficientCalculus

/-- Coordinate coefficient forms evaluate on the original intrinsic tangent vectors. -/
theorem coefficientAlternating_evaluate {V : Type u} [AddCommGroup V] [Module ℝ V]
    (n k : ℕ) (E : V ≃ₗ[ℝ] Euclidean n) (ξ : Fiber V k) (v : Fin k → Euclidean n) :
    Euclidean.coefficientAlternatingEquiv n k
      ((((Pi.basisFun ℝ (Fin n)).map E.symm).dualBasis.exteriorPower k).equivFun ξ) v =
      evaluate V k ξ (fun i => E.symm (v i)) := by
  classical
  let b := ((Pi.basisFun ℝ (Fin n)).map E.symm).dualBasis
  let c := (Pi.basisFun ℝ (Fin n)).dualBasis
  have hb (j : Fin n) (w : Euclidean n) : b j (E.symm w) = w j := by
    simp [b, Module.Basis.map_repr]
  change evaluate (Euclidean n) k
      ((c.exteriorPower k).equivFun.symm ((b.exteriorPower k).equivFun ξ)) v = _
  rw [Module.Basis.equivFun_symm_apply]
  conv_rhs => rw [← (b.exteriorPower k).sum_repr ξ]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    Module.Basis.equivFun_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro I hI
  congr 1
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rw [ExteriorAlgebraResults.determinant_normalization,
    ExteriorAlgebraResults.determinant_normalization]
  congr 1
  ext i j
  simp only [Function.comp_apply, hb, c, Module.Basis.dualBasis_apply, Pi.basisFun_repr]

theorem coordinateExpression_evaluate {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : M) (hp : p ∈ c.source)
    (A : Index n k → Euclidean n →L[ℝ] ℝ) (v : Fin (k+1) → Euclidean n) :
    evaluate (TangentSpace S p) (k+1) (coordinateExpression C k c hc p hp A)
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p hp).symm (v i)) =
        Euclidean.coefficientAlternatingEquiv n (k+1) (coefficientDerivativeMap n k A) v := by
  have h := @coefficientAlternating_evaluate.{u} (TangentSpace S p) _ _ n (k+1)
    (C.tangent.fiberCoordinates.equiv c hc p hp) (coordinateExpression C k c hc p hp A) v
  rw [coordinateExpression_coefficients] at h
  exact h.symm

/-- A genuine coefficient extension computes the coordinate exterior derivative
as the analytic exterior derivative of the corresponding alternating form. -/
theorem coordinateDerivative_evaluate_extension {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) (k : ℕ)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (ω : Field S k)
    (p : M) (hp : p ∈ c.source) (U : Set (Euclidean n)) (hU : IsOpen U)
    (hpU : (c p).val ∈ U) (F : Euclidean n → Index n k → ℝ)
    (hF : ContDiffOn ℝ 1 F U)
    (heF : ∀ q : c.source, (c q.val).val ∈ U → F (c q.val).val =
      fun I => coefficients C k c hc ω q I) (v : Fin (k+1) → Euclidean n) :
    evaluate (TangentSpace S p) (k+1) (coordinateDerivative C k c hc ω p hp)
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p hp).symm (v i)) =
        extDeriv (fun z => Euclidean.coefficientAlternatingEquiv n k (F z)) (c p).val v := by
  have hext : ∀ (z : ModelSpace n a) (hz : z ∈ c.target), z.val ∈ U → ∀ I,
      F z.val I = coefficients C k c hc ω ⟨c.symm z, c.map_target hz⟩ I := by
    intro z hz hzU I
    have hh := congrFun (heF ⟨c.symm z, c.map_target hz⟩
      (by simpa only [c.right_inv hz] using hzU)) I
    simpa only [c.right_inv hz] using hh
  rw [coordinate_formula_extension C k c hc ω p hp U (fun I z => F z I)
    hU hpU (fun I => contDiffOn_pi.mp hF I) hext,
    coordinateExpression_evaluate]
  rw [Euclidean.extDeriv_coefficientAlternatingEquiv F (c p).val
    ((hF.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))]

/-- The genuine tangent Jacobian gives the analytic coefficient pullback. -/
theorem coefficient_pullback_of_jacobian {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source)
    (K : Euclidean n →L[ℝ] Euclidean m)
    (hK : ∀ v : TangentSpace S p,
      A.tangent.fiberCoordinates.equiv d hd (f p) hfp (L p v) =
        K (C.tangent.fiberCoordinates.equiv c hc p hp v))
    (k : ℕ) (ω : Field T k) :
    Euclidean.coefficientAlternatingEquiv n k
      (fun I => coefficients C k c hc (FormPullbackData.pullbackField S T f L ω) ⟨p,hp⟩ I) =
    (Euclidean.coefficientAlternatingEquiv m k
      (fun I => coefficients A k d hd ω ⟨f p,hfp⟩ I)).compContinuousLinearMap K := by
  ext v
  change Euclidean.coefficientAlternatingEquiv n k
    ((((Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p hp).symm).dualBasis.exteriorPower k).equivFun
        ((FormPullbackData.pullbackField S T f L ω) p)) v = _
  rw [@coefficientAlternating_evaluate.{u} (TangentSpace S p) _ _ n k
    (C.tangent.fiberCoordinates.equiv c hc p hp)]
  have hpb := @FormPullbackResults.evaluate_fiberPullback.{u}
    (TangentSpace S p) (TangentSpace T (f p)) _ _ _ _ k (L p) (ω (f p))
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p hp).symm (v i))
  change evaluate (TangentSpace S p) k
    (fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) k (L p) (ω (f p)))
      (fun i => (C.tangent.fiberCoordinates.equiv c hc p hp).symm (v i)) = _
  rw [hpb]
  have hv : (fun i => L p ((C.tangent.fiberCoordinates.equiv c hc p hp).symm (v i))) =
      (fun i => (A.tangent.fiberCoordinates.equiv d hd (f p) hfp).symm (K (v i))) := by
    funext i
    apply (A.tangent.fiberCoordinates.equiv d hd (f p) hfp).injective
    rw [hK, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rw [hv]
  change evaluate (TangentSpace T (f p)) k (ω (f p))
    (fun i => (A.tangent.fiberCoordinates.equiv d hd (f p) hfp).symm (K (v i))) =
      Euclidean.coefficientAlternatingEquiv m k
        ((((Pi.basisFun ℝ (Fin m)).map
          (A.tangent.fiberCoordinates.equiv d hd (f p) hfp).symm).dualBasis.exteriorPower k).equivFun
            (ω (f p))) (fun i => K (v i))
  with_reducible exact (@coefficientAlternating_evaluate.{u}
    (TangentSpace T (f p)) _ _ m k (A.tangent.fiberCoordinates.equiv d hd (f p) hfp)
      (ω (f p)) (fun i => K (v i))).symm

/-- Pointwise coordinate naturality, before any global derivative is chosen. -/
theorem coordinate_derivative_pullback {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (f : M → N)
    (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p))
    (k : ℕ) (ω : Field T k) (hω : IsRegularField A 1 k ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart m b N) (hd : d ∈ T.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hfp : f p ∈ d.source) :
    coordinateDerivative C k c hc (FormPullbackData.pullbackField S T f L ω) p hp =
      fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p)) (k+1) (L p) (coordinateDerivative A k d hd ω (f p) hfp) := by
  classical
  let E := C.tangent.fiberCoordinates.equiv c hc p hp
  let D := A.tangent.fiberCoordinates.equiv d hd (f p) hfp
  have hpbreg := pullback_regular S T C A f hf L hL k 1 ω hω
  obtain ⟨U, hU, hpU, G, hG, heG⟩ := hpbreg c hc ⟨p,hp⟩
  obtain ⟨V, hV, hfpV, F, hF, heF⟩ := hω d hd ⟨f p,hfp⟩
  obtain ⟨W, hW, hpW, H, hH, heH⟩ := (hf p).2 c hc d hd hp hfp
  have hHeq : H (c p).val = (d (f p)).val := heH.eq_of_nhds
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp heH
  let Φ : Euclidean n → (Euclidean n) [⋀^Fin k]→L[ℝ] ℝ := fun z =>
    (Euclidean.coefficientAlternatingEquiv m k (F (H z))).compContinuousLinearMap (fderiv ℝ H z)
  have hJac (y : M) (hy : y ∈ c.source) (hfy : f y ∈ d.source)
      (hyW : (c y).val ∈ W) (hyO : y ∈ O) :
      ∀ v : TangentSpace S y,
        A.tangent.fiberCoordinates.equiv d hd (f y) hfy (L y v) =
          fderiv ℝ H (c y).val (C.tangent.fiberCoordinates.equiv c hc y hy v) := by
    apply differential_jacobian S T f hf y (L y) (hL y) c d hc hd hy hfy
      (C.tangent.fiberCoordinates.equiv c hc y hy)
      (A.tangent.fiberCoordinates.equiv d hd (f y) hfy)
      (C.tangent.fiberCoordinates.isCoordinates c hc y hy)
      (A.tangent.fiberCoordinates.isCoordinates d hd (f y) hfy) W H hW hyW hH
    filter_upwards [hO.mem_nhds hyO] with z hz
    exact hOsub hz
  have hcoord : ContinuousAt (fun y => (c y).val) p :=
    continuous_subtype_val.continuousAt.comp (c.continuousAt hp)
  have htarget : ContinuousAt (fun y => (d (f y)).val) p :=
    continuous_subtype_val.continuousAt.comp ((d.continuousAt hfp).comp (hf p).1)
  have heM : (fun y => Euclidean.coefficientAlternatingEquiv n k (G (c y).val)) =ᶠ[𝓝 p]
      (fun y => Φ (c y).val) := by
    filter_upwards [c.open_source.mem_nhds hp,
      (hf p).1.preimage_mem_nhds (d.open_source.mem_nhds hfp),
      hcoord.preimage_mem_nhds (hU.mem_nhds hpU),
      hcoord.preimage_mem_nhds (hW.mem_nhds hpW),
      htarget.preimage_mem_nhds (hV.mem_nhds hfpV), hO.mem_nhds hpO] with y hy hfy hyU hyW hyV hyO
    change f y ∈ d.source at hfy
    change (c y).val ∈ U at hyU
    change (c y).val ∈ W at hyW
    change (d (f y)).val ∈ V at hyV
    have hyH : H (c y).val = (d (f y)).val := hOsub hyO
    dsimp only [Φ]
    rw [heG ⟨y,hy⟩ hyU, hyH, heF ⟨f y,hfy⟩ hyV]
    exact coefficient_pullback_of_jacobian S T C A f L c hc d hd y hy hfy
      (fderiv ℝ H (c y).val) (hJac y hy hfy hyW hyO) k ω
  have heModel : (fun z : ModelSpace n a => Euclidean.coefficientAlternatingEquiv n k (G z.val))
      =ᶠ[𝓝 (c p)] (fun z => Φ z.val) := by
    rw [← c.map_nhds_eq hp]
    exact heM
  have heAmbient : (fun z => Euclidean.coefficientAlternatingEquiv n k (G z))
      =ᶠ[𝓝[Subtype.val '' c.target] (c p).val] Φ := by
    have hh : (fun z => Euclidean.coefficientAlternatingEquiv n k (G z))
        =ᶠ[𝓝[modelSet n a] (c p).val] Φ := by
      rw [← map_nhds_subtype_val (c p)]
      exact heModel
    exact hh.filter_mono (nhdsWithin_mono _ (by
      rintro z ⟨w,hw,rfl⟩
      exact w.property))
  have hdG : DifferentiableAt ℝ (fun z => Euclidean.coefficientAlternatingEquiv n k (G z)) (c p).val :=
    (Euclidean.coefficientAlternatingEquiv n k).differentiableAt.comp _
      ((hG.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by norm_num))
  have hdF : DifferentiableAt ℝ (fun z => Euclidean.coefficientAlternatingEquiv m k (F z)) (H (c p).val) := by
    rw [hHeq]
    exact (Euclidean.coefficientAlternatingEquiv m k).differentiableAt.comp _
      ((hF.contDiffAt (hV.mem_nhds hfpV)).differentiableAt (by norm_num))
  have hdH := (hH.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
  have hdDH : DifferentiableAt ℝ (fderiv ℝ H) (c p).val :=
    ((hH.contDiffAt (hW.mem_nhds hpW)).fderiv_right (m := 1) (by simp)).differentiableAt (by norm_num)
  have hdΦ : DifferentiableAt ℝ Φ (c p).val :=
    (hdF.comp _ hdH).continuousAlternatingMapCompContinuousLinearMap hdDH
  have heD := extension_independence n k (Subtype.val '' c.target)
    (uniqueDiffOn_modelDomain c.open_target) (c p).val ⟨c p,c.map_source hp,rfl⟩
      (fun z => Euclidean.coefficientAlternatingEquiv n k (G z)) Φ hdG hdΦ heAmbient
  have hnat := extDeriv_pullback hdF (hH.contDiffAt (hW.mem_nhds hpW)) (by simp)
  letI : FiniteDimensional ℝ (TangentSpace S p) :=
    FiniteDimensional.of_injective E.toLinearMap E.injective
  apply (ExteriorAlgebraResults.alternating_interpretation (TangentSpace S p) (k+1)).1
  ext w
  let v : Fin (k+1) → Euclidean n := fun i => E (w i)
  have hv : (fun i => E.symm (v i)) = w := by funext i; exact E.symm_apply_apply (w i)
  rw [← hv]
  calc
    _ = extDeriv (fun z => Euclidean.coefficientAlternatingEquiv n k (G z)) (c p).val v :=
      coordinateDerivative_evaluate_extension C k c hc _ p hp U hU hpU G hG heG v
    _ = extDeriv Φ (c p).val v := congrArg (fun A => A v) heD
    _ = extDeriv (fun z => Euclidean.coefficientAlternatingEquiv m k (F z)) (d (f p)).val
        (fun i => fderiv ℝ H (c p).val (v i)) := by
      have hh := congrArg (fun A : (Euclidean n) [⋀^Fin (k+1)]→L[ℝ] ℝ => A v) hnat
      simpa only [Φ, hHeq, ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def] using hh
    _ = evaluate (TangentSpace T (f p)) (k+1) (coordinateDerivative A k d hd ω (f p) hfp)
        (fun i => D.symm (fderiv ℝ H (c p).val (v i))) :=
      (coordinateDerivative_evaluate_extension A k d hd ω (f p) hfp V hV hfpV F hF heF _).symm
    _ = evaluate (TangentSpace T (f p)) (k+1) (coordinateDerivative A k d hd ω (f p) hfp)
        (fun i => L p (E.symm (v i))) := by
      congr 1
      funext i
      apply D.injective
      rw [LinearEquiv.apply_symm_apply, hJac p hp hfp hpW hpO, LinearEquiv.apply_symm_apply]
    _ = _ := by
      with_reducible exact (@FormPullbackResults.evaluate_fiberPullback.{u}
        (TangentSpace S p) (TangentSpace T (f p)) _ _ _ _ (k+1) (L p)
        (coordinateDerivative A k d hd ω (f p) hfp) (fun i => E.symm (v i))).symm

/-- Intrinsic C¹ naturality follows before choosing a global operator. -/
theorem c1_naturality : Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_naturalityType.{u} := by
  intro n m a b M N _ _ S T C A f hf L hL k ω η hω hη
  constructor
  · exact pullback_regular S T C A f hf L hL k 1 ω hω
  · intro c hc p hp
    obtain ⟨d, hd, hfp⟩ := T.smoothStructure.property.1.1 (f p)
    change fiberPullback (V := TangentSpace S p) (W := TangentSpace T (f p))
      (k+1) (L p) (η (f p)) = _
    rw [hη d hd (f p) hfp]
    exact (coordinate_derivative_pullback S T C A f hf L hL k ω hω c hc d hd p hp hfp).symm

/-- Coordinate naturality for the identity is overlap compatibility. -/
theorem coordinateDerivative_chart_independent {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (hω : IsRegularField C 1 k ω)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ c.source) (hpd : p ∈ d.source) :
    coordinateDerivative C k c hc ω p hp = coordinateDerivative C k d hd ω p hpd := by
  have hid : IsSmoothMap S S id := manifoldContDiff_id _ _ S.smoothStructure.property.1
  have hL : ∀ p, IsDifferential S S id p (LinearMap.id : TangentSpace S p →ₗ[ℝ] TangentSpace S p) :=
    fun p => differential_id S p
  have hnat := coordinate_derivative_pullback S S C C id hid (fun p => LinearMap.id) hL
    k ω hω c hc d hd p hp hpd
  rw [FormPullbackResults.pullback_id S (fun p => LinearMap.id) hL k ω] at hnat
  simpa only [id_eq, fiberPullback, LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply] using hnat


/-- The derivative candidate is chosen pointwise in one covering chart.
Its chart independence is proved separately, not built into manifold data. -/
def chartDerivative {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) : Field S (k+1) := fun p =>
  let c := Classical.choose (S.smoothStructure.property.1.1 p)
  let hc := (Classical.choose_spec (S.smoothStructure.property.1.1 p)).1
  let hp := (Classical.choose_spec (S.smoothStructure.property.1.1 p)).2
  coordinateDerivative C k c hc ω p hp

/-- Gluing requires only the already intrinsic equality on every chart overlap. -/
theorem chartDerivative_has_of_compatible {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k)
    (hcompat : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
      (p : M) (hp : p ∈ c.source) (hpd : p ∈ d.source),
      coordinateDerivative C k c hc ω p hp = coordinateDerivative C k d hd ω p hpd) :
    HasExteriorDerivative C ω (chartDerivative C k ω) := by
  intro c hc p hp
  exact hcompat _ _ c hc p _ hp

/-- Once chart compatibility has been proved, the all-charts C¹ existence theorem
follows with continuous output from the coefficient regularity theorem. -/
theorem c1_derivative_exists_of_compatible {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (hω : IsRegularField C 1 k ω)
    (hcompat : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
      (p : M) (hp : p ∈ c.source) (hpd : p ∈ d.source),
      coordinateDerivative C k c hc ω p hp = coordinateDerivative C k d hd ω p hpd) :
    ∃ η : Field S (k+1), HasExteriorDerivative C ω η ∧ IsContinuousField C (k+1) η := by
  have hd := chartDerivative_has_of_compatible C k ω hcompat
  exact ⟨chartDerivative C k ω, hd, c1_derivative_continuous C k ω _ hω hd⟩

/-- Assembly from the three independently proved local calculus statements. -/
theorem smooth_family_of_local_calculus {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k)
    (hcompat : ∀ k (ω : Field S k), IsRegularField C 1 k ω →
      ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val)
        (p : M) (hp : p ∈ c.source) (hpd : p ∈ d.source),
        coordinateDerivative C k c hc ω p hp = coordinateDerivative C k d hd ω p hpd)
    (hsquare : ∀ k (ω : Field S k) (η : Field S (k+1)) (ζ : Field S (k+1+1)),
      IsRegularField C 2 k ω → HasExteriorDerivative C ω η → HasExteriorDerivative C η ζ → ζ = 0)
    (hleibniz : ∀ k l (α : Field S k) (β : Field S l)
      (η : Field S (k+1)) (ζ : Field S (l+1)) (θ : Field S (k+l+1)),
      IsRegularField C 1 k α → IsRegularField C 1 l β →
      HasExteriorDerivative C α η → HasExteriorDerivative C β ζ →
      HasExteriorDerivative C (fieldWedge α β) θ → ∀ p,
        (θ p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) =
          (wedge (V := TangentSpace S p) (k := k+1) (l := l) (η p) (β p) :
            ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) +
          (-1 : ℝ)^k • (wedge (V := TangentSpace S p) (k := k) (l := l+1) (α p) (ζ p) :
            ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p)))) :
    ∃ D : ∀ k, Field S k → Field S (k+1), DerivativeAxioms C B D ∧
      ∀ E, DerivativeAxioms C B E → ∀ k ω, IsForm (B k) ω → D k ω = E k ω := by
  let D : ∀ k, Field S k → Field S (k+1) := chartDerivative C
  have hd (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) : HasExteriorDerivative C ω (D k ω) :=
    chartDerivative_has_of_compatible C k ω (hcompat k ω (smooth_regular C k (B k) ω 1 hω))
  have hsm (k : ℕ) (ω : Field S k) (hω : IsForm (B k) ω) : IsForm (B (k+1)) (D k ω) :=
    derivative_smooth C k (B k) (B (k+1)) ω _ hω (hd k ω hω)
  have hD : DerivativeAxioms C B D :=
    { smooth := hsm
      add := by
        intro k α β hα hβ
        apply derivative_unique C k (α+β) (D k (α+β)) (D k α + D k β)
        · exact hd k (α+β) (add_form C k (B k) α β hα hβ)
        · exact derivative_add C k α β _ _ (smooth_regular C k (B k) α 1 hα)
            (smooth_regular C k (B k) β 1 hβ) (hd k α hα) (hd k β hβ)
      smul := by
        intro k r α hα
        have hr : IsForm (B k) (r • α) := (smooth_coefficients C k (B k) _).mpr
          (regularField_smul C k ⊤ r ((smooth_coefficients C k (B k) α).mp hα))
        exact derivative_unique C k (r • α) _ _ (hd k (r • α) hr)
          (derivative_smul C k r α _ (smooth_regular C k (B k) α 1 hα) (hd k α hα))
      function_rule := by
        intro f hf p
        exact congrFun (derivative_unique C 0 (scalarField S f) _ _
          (hd 0 (scalarField S f) (scalarField_form C (B 0) f hf)) (function_derivative C f hf)) p
      square := by
        intro k ω hω
        exact hsquare k ω (D k ω) (D (k+1) (D k ω))
          (smooth_regular C k (B k) ω 2 hω) (hd k ω hω) (hd (k+1) (D k ω) (hsm k ω hω))
      leibniz := by
        intro k l α β hα hβ p
        exact hleibniz k l α β (D k α) (D l β) (D (k+l) (fieldWedge α β))
          (smooth_regular C k (B k) α 1 hα) (smooth_regular C l (B l) β 1 hβ)
          (hd k α hα) (hd l β hβ)
          (hd (k+l) (fieldWedge α β) (ExteriorAlgebraResults.wedge_smooth C k l (B k) (B l)
            (B (k+l)) α β hα hβ)) p }
  exact ⟨D, hD, fun E hE k ω hω => axioms_unique C B D E hD hE k ω hω⟩

theorem chartDerivative_has {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (ω : Field S k) (hω : IsRegularField C 1 k ω) :
    HasExteriorDerivative C ω (chartDerivative C k ω) :=
  chartDerivative_has_of_compatible C k ω (coordinateDerivative_chart_independent C k ω hω)

/-- The intrinsic exterior derivative of every C¹ field exists, is independent
of all chart choices, and is continuous. -/
theorem c1_derivative_exists :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.c1_derivative_existsType.{u} := by
  intro n a M _ S C k ω hω
  exact c1_derivative_exists_of_compatible C k ω hω (coordinateDerivative_chart_independent C k ω hω)

/-- The unique smooth degree-raising family satisfies the characterizing axioms
on the original intrinsic exterior sections in every degree. -/
theorem smooth_family_exists :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.smooth_family_existsType.{u} := by
  intro n a M _ S C B
  exact smooth_family_of_local_calculus C B (coordinateDerivative_chart_independent C)
    (Euclidean.intrinsic_derivative_square C) (CoefficientCalculus.intrinsic_derivative_leibniz C)

/-- The same global family commutes with smooth pullback on intrinsic forms. -/
theorem smooth_naturality {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T)
    (B : ∀ k, FormBundle C k) (E : ∀ k, FormBundle A k)
    (D : ∀ k, Field S k → Field S (k+1)) (J : ∀ k, Field T k → Field T (k+1))
    (hD : DerivativeAxioms C B D) (hJ : DerivativeAxioms A E J)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, IsDifferential S T f p (L p)) (k : ℕ) (ω : Field T k)
    (hω : IsForm (E k) ω) :
    FormPullbackData.pullbackField S T f L (J k ω) =
      D k (FormPullbackData.pullbackField S T f L ω) := by
  have hn := (c1_naturality S T C A f hf L hL k ω (J k ω)
    (smooth_regular A k (E k) ω 1 hω) (global_coordinates A E J hJ k ω hω)).2
  exact derivative_unique C k _ _ _ hn
    (global_coordinates C B D hD k _
      (FormPullbackResults.pullback_smooth S T C A f hf L hL k (B k) (E k) ω hω))

/-- A C¹ form restricts to a C¹ form on every smooth embedded submanifold,
including a smooth face, and restriction commutes with its derivative. -/
theorem c1_restriction {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (A : CotangentBundle T) (i : M → N)
    (hi : MapClassData.IsSmoothEmbedding S T i)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (i p))
    (hL : ∀ p, IsDifferential S T i p (L p))
    (k : ℕ) (ω : Field T k) (η : Field T (k+1))
    (hω : IsRegularField A 1 k ω) (hη : HasExteriorDerivative A ω η) :
    IsRegularField C 1 k (FormPullbackData.pullbackField S T i L ω) ∧
      HasExteriorDerivative C (FormPullbackData.pullbackField S T i L ω)
        (FormPullbackData.pullbackField S T i L η) :=
  c1_naturality S T C A i hi.1 L hL k ω η hω hη

open BundleData in
theorem oneForm_isForm {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (B : FormBundle C 1) (α : CovectorField S)
    (hα : IsOneForm C α) :
    IsForm B (fun p => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm (α p)) := by
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  have hpC : p ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]
    exact hp
  have hv := FrameData.VectorSmoothAt.comp
    (g := fun q : M => (⟨q, α q⟩ : Bundle.TotalSpace (Euclidean n) (CotangentFiber S)))
    (cotangentSpace C).bundle.totalManifold.smoothStructure.property.1.1
    (Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle ⟨c, hc⟩ ⟨p, α p⟩ hpC)
    (hα p)
  let L : Euclidean n →ₗ[ℝ] Euclidean (n.choose 1) :=
    B.modelEquiv.toLinearMap.comp (exteriorPower.oneEquiv ℝ (Euclidean n)).symm.toLinearMap
  have hLv := hv.postcomp L.toContinuousLinearMap.contDiff
  apply Frames.smoothAt_from_trivialization B.space.bundle S.smoothStructure.property.1
    ⟨c, hc⟩ (by rw [B.baseSet, Covectors.cotangent_baseSet]; exact hp)
    ((manifoldContDiff_id _ _ S.smoothStructure.property.1) p) hLv (fun _ => rfl)
  filter_upwards [c.open_source.mem_nhds hp] with q hq
  have hqC : q ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]
    exact hq
  change B.space.bundle.fiberCoordinates ⟨c, hc⟩ q ((B.baseSet ⟨c, hc⟩).symm ▸ hqC)
    ((exteriorPower.oneEquiv ℝ (CotangentFiber S q)).symm (α q)) = _
  rw [ExteriorAlgebraResults.exterior_coordinates (cotangentSpace C).bundle B ⟨c, hc⟩ q hqC]
  change B.modelEquiv (exteriorPower.map 1
      ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ q hqC).toLinearMap
      ((exteriorPower.oneEquiv ℝ (CotangentFiber S q)).symm (α q))) =
    B.modelEquiv ((exteriorPower.oneEquiv ℝ (Euclidean n)).symm
      (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ⟨q, α q⟩).2)
  congr 1
  apply (exteriorPower.oneEquiv ℝ (Euclidean n)).injective
  rw [LinearEquiv.apply_symm_apply]
  have hh := LinearMap.congr_fun (exteriorPower.oneEquiv_naturality
    (R := ℝ) ((cotangentSpace C).bundle.fiberCoordinates ⟨c, hc⟩ q hqC).toLinearMap)
      ((exteriorPower.oneEquiv ℝ (CotangentFiber S q)).symm (α q))
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    SmoothVectorBundle.fiberCoordinates_apply] using hh


/-- Every ordinary point of a relatively open corner domain is approached by
ordinary interior points. The empty coordinate family includes dimension zero. -/
theorem orthant_domain_closure_interior {n : ℕ} {c : Fin (n+1)}
    {s : Set (Orthant n c)} (hs : IsOpen s) :
    (Subtype.val '' s : Set (Euclidean n)) ⊆
      closure (interior (Subtype.val '' s : Set (Euclidean n))) := by
  have hconv : Convex ℝ (orthantSet n c) := by
    change Convex ℝ (Set.pi {i : Fin n | i.val < c.val} (fun _ => Set.Ici (0 : ℝ)))
    exact convex_pi (fun _ _ => convex_Ici 0)
  have hint : (interior (orthantSet n c)).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    change (fun _ : Fin n => (1 : ℝ)) ∈
      interior (Set.pi {i : Fin n | i.val < c.val} (fun _ => Set.Ici (0 : ℝ)))
    rw [interior_pi_set (Set.toFinite _)]
    intro i hi
    simp
  have hclosure : orthantSet n c ⊆ closure (interior (orthantSet n c)) := by
    rw [hconv.closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure
  obtain ⟨U, hU, hEq⟩ := hs.image_val
  rw [hEq]
  intro x hx
  have hh := hU.inter_closure (t := interior (orthantSet n c))
    (show x ∈ U ∩ closure (interior (orthantSet n c)) from ⟨hx.1, hclosure hx.2⟩)
  simpa only [interior_inter, hU.interior_eq] using hh

/-- A map with the specified local ambient extensions is C^r within its domain. -/
theorem locallyContDiffOn_contDiffOn {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ∞) (s : Set (Euclidean n)) (f : Euclidean n → F)
    (hf : LocallyContDiffOn r s (fun x => f x.val)) : ContDiffOn ℝ r f s := by
  intro x hx
  obtain ⟨U, hU, hxU, g, hg, he⟩ := hf ⟨x, hx⟩
  apply (hg.contDiffAt (hU.mem_nhds hxU)).contDiffWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with y hy hyU
    exact (he ⟨y, hy⟩ hyU).symm
  · exact (he ⟨x, hx⟩ hxU).symm

/-- Naturality on relatively open orthant domains uses only local C¹ extensions
of the form and smooth local ambient extensions of the map. The ambient map is
required to land in the target corner only on the actual source domain. -/
theorem orthant_extDerivWithin_pullback {n m k : ℕ}
    {c : Fin (n+1)} {d : Fin (m+1)}
    (s : Set (Orthant n c)) (t : Set (Orthant m d)) (hs : IsOpen s) (_ht : IsOpen t)
    (ω : Euclidean m → (Euclidean m) [⋀^Fin k]→L[ℝ] ℝ)
    (f : Euclidean n → Euclidean m)
    (hω : LocallyContDiffOn 1 (Subtype.val '' t : Set (Euclidean m)) (fun y => ω y.val))
    (hf : LocallyContDiffOn (⊤ : ℕ∞) (Subtype.val '' s : Set (Euclidean n)) (fun x => f x.val))
    (hmap : MapsTo f (Subtype.val '' s) (Subtype.val '' t))
    (x : Euclidean n) (hx : x ∈ (Subtype.val '' s : Set (Euclidean n))) :
    extDerivWithin
      (fun y => (ω (f y)).compContinuousLinearMap
        (fderivWithin ℝ f (Subtype.val '' s) y)) (Subtype.val '' s) x =
      (extDerivWithin ω (Subtype.val '' t) (f x)).compContinuousLinearMap
        (fderivWithin ℝ f (Subtype.val '' s) x) := by
  have hω' := locallyContDiffOn_contDiffOn 1 (Subtype.val '' t) ω hω
  have hf' := locallyContDiffOn_contDiffOn ⊤ (Subtype.val '' s) f hf
  exact extDerivWithin_pullback
    ((hω' (f x) (hmap hx)).differentiableWithinAt (by norm_num))
    (hf' x hx) (by simp) (uniqueDiffOn_orthantDomain hs)
    (orthant_domain_closure_interior hs hx) hx hmap


/-- Continuity of all chart coefficients is continuity of the original section
into any of the genuine exterior bundle total spaces. -/
theorem continuous_field_section {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (ω : Field S k) (hω : IsContinuousField C k ω) :
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    Continuous (fun p => (⟨p,ω p⟩ :
      Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k))) := by
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
  let e : Euclidean (n.choose k) ≃ₗ[ℝ] (Index n k → ℝ) :=
    B.modelEquiv.symm.trans ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
  have he (q : c.source) : e (Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩
      (fun q => ω q.val) q) = fun I => coefficients C k c hc ω q I :=
    (ExteriorAlgebraResults.coefficients_coordinates C B c hc ω q).symm
  have hcoeff : Continuous (fun q : c.source => fun I => coefficients C k c hc ω q I) :=
    continuous_pi (fun I => hω c hc I)
  have hcoords : Continuous (Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩
      (fun q => ω q.val)) := by
    have hh := e.symm.toContinuousLinearEquiv.continuous.comp hcoeff
    have heq : (fun q : c.source => e.symm (fun I => coefficients C k c hc ω q I)) =
        Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩ (fun q => ω q.val) := by
      funext q
      rw [← he, LinearEquiv.symm_apply_apply]
    change Continuous (fun q : c.source => e.symm (fun I => coefficients C k c hc ω q I)) at hh
    rw [heq] at hh
    exact hh
  apply (c.open_source.isOpenEmbedding_subtypeVal.continuousAt_iff (x := (⟨p,hp⟩ : c.source))).mp
  change ContinuousAt (fun q : c.source => (⟨q.val,ω q.val⟩ :
    Bundle.TotalSpace (Euclidean (n.choose k)) (fun z => Fiber (TangentSpace S z) k))) ⟨p,hp⟩
  let t := B.space.bundle.trivialization ⟨c,hc⟩
  have hbase (q : c.source) : q.val ∈ t.baseSet := by
    rw [B.space.bundle.trivialization_baseSet, B.baseSet, Covectors.cotangent_baseSet]
    exact q.property
  apply t.continuousAt_of_comp_left
  · exact continuousAt_subtype_val
  · exact hbase ⟨p,hp⟩
  · have hh : ContinuousAt (fun q : c.source =>
        (q.val, Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩ (fun q => ω q.val) q)) ⟨p,hp⟩ :=
      continuousAt_subtype_val.prodMk hcoords.continuousAt
    apply hh.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun q => by
      apply Prod.ext
      · exact (t.coe_fst' (x := (⟨q.val,ω q.val⟩ :
          Bundle.TotalSpace (Euclidean (n.choose k)) (fun z => Fiber (TangentSpace S z) k))) (hbase q))
      · rfl)

/-- Continuity in the total bundle implies continuity of every chart coefficient. -/
theorem section_continuous_field {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (ω : Field S k)
    (hω : letI := (cotangentSpace C).topology
      letI := B.space.topology
      Continuous (fun p => (⟨p,ω p⟩ :
        Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k)))) :
    IsContinuousField C k ω := by
  letI := (cotangentSpace C).topology
  letI := B.space.topology
  intro c hc I
  let t := B.space.bundle.trivialization ⟨c,hc⟩
  let e : Euclidean (n.choose k) ≃ₗ[ℝ] (Index n k → ℝ) :=
    B.modelEquiv.symm.trans ((Pi.basisFun ℝ (Fin n)).exteriorPower k).equivFun
  have he (q : c.source) : e (Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩
      (fun q => ω q.val) q) = fun I => coefficients C k c hc ω q I :=
    (ExteriorAlgebraResults.coefficients_coordinates C B c hc ω q).symm
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp : p.val ∈ t.baseSet := by
    rw [B.space.bundle.trivialization_baseSet, B.baseSet, Covectors.cotangent_baseSet]
    exact p.property
  have hs : ContinuousAt (fun q : c.source => (⟨q.val,ω q.val⟩ :
      Bundle.TotalSpace (Euclidean (n.choose k)) (fun z => Fiber (TangentSpace S z) k))) p :=
    hω.continuousAt.comp continuousAt_subtype_val
  have hcoords : ContinuousAt (Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩
      (fun q => ω q.val)) p :=
    ((t.toOpenPartialHomeomorph.continuousAt (t.mem_source.mpr hp)).comp hs).snd
  have hcoef := (continuous_apply I).continuousAt.comp (e.toContinuousLinearEquiv.continuousAt.comp hcoords)
  change ContinuousAt (fun q : c.source => e
    (Frames.sectionCoordinates B.space.bundle c.source ⟨c,hc⟩ (fun q => ω q.val) q) I) p at hcoef
  simpa only [he] using hcoef

/-- The coordinate and intrinsic notions of continuous forms agree. -/
theorem continuous_field_section_iff {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C k) (ω : Field S k) :
    IsContinuousField C k ω ↔
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    Continuous (fun p => (⟨p,ω p⟩ :
      Bundle.TotalSpace (Euclidean (n.choose k)) (fun q => Fiber (TangentSpace S q) k))) :=
  ⟨continuous_field_section C k B ω, section_continuous_field C k B ω⟩

/-- A C¹ exterior derivative is an actual continuous section of Λ^(k+1)T*M. -/
theorem c1_derivative_section_continuous {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (k : ℕ) (B : FormBundle C (k+1)) (ω : Field S k) (η : Field S (k+1))
    (hω : IsRegularField C 1 k ω) (hη : HasExteriorDerivative C ω η) :
    letI := (cotangentSpace C).topology
    letI := B.space.topology
    Continuous (fun p => (⟨p,η p⟩ :
      Bundle.TotalSpace (Euclidean (n.choose (k+1))) (fun q => Fiber (TangentSpace S q) (k+1)))) :=
  continuous_field_section C (k+1) B η (c1_derivative_continuous C k ω η hω hη)


open BundleData
set_option maxHeartbeats 2000000

theorem axioms_closed_sum_at {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (B : ∀ k, FormBundle C k) (D : ∀ k, Field S k → Field S (k+1))
    (hD : DerivativeAxioms C B D) (k : ℕ) (ω : Field S k)
    (hω : IsForm (B k) ω) {ι : Type v} [Fintype ι]
    (b : ι → M → ℝ) (hb : ∀ j, PartitionData.ScalarSmooth S.smoothStructure.val (b j))
    (γ : ι → Field S k) (hγ : ∀ j, IsForm (B k) (γ j)) (hγD : ∀ j, D k (γ j) = 0)
    (p : M) (heq : ∀ᶠ q in 𝓝 p, ω q = ∑ j, b j q • γ j q) :
    (D k ω p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) = ∑ j,
      ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace S p))).symm
        (dFunction S (b j) (hb j) p) : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) *
        (γ j p : ExteriorAlgebra ℝ (Module.Dual ℝ (TangentSpace S p))) := by
  classical
  let T : ι → Field S k := fun j q => b j q • γ j q
  have hT (j : ι) : IsForm (B k) (T j) := by
    have hh := ExteriorAlgebraResults.wedge_smooth C k 0 (B k) (B 0) (B k)
      (γ j) (scalarField S (b j)) (hγ j) (scalarField_form C (B 0) _ (hb j))
    rw [fieldWedge_scalar] at hh
    exact hh
  have hloc : ∀ᶠ q in 𝓝 p, ω q = (∑ j, T j) q := by
    simpa only [Finset.sum_apply, T] using heq
  rw [axioms_locality C B D hD k ω (∑ j, T j) hω
      (sum_form C k (B k) Finset.univ T (fun j _ => hT j)) p hloc,
    axioms_sum C B D hD k Finset.univ T (fun j _ => hT j), Finset.sum_apply, Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact axioms_function_smul_closed C B D hD k (γ j) (hγ j) (hγD j) (b j) (hb j) p

theorem oneEquiv_sum_smul {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} [Fintype ι] (α : Module.Dual ℝ V) (r a : ι → ℝ)
    (β : ι → Module.Dual ℝ V) (γ : ι → Fiber V 1)
    (hα : α = ∑ j, r j • β j) (hr : ∀ j, r j = a j)
    (hγ : ∀ j, (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm (β j) = γ j) :
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ V)).symm α = ∑ j, a j • γ j := by
  rw [hα, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hr j, hγ j]

theorem axioms_local_covector_sum {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (A : CotangentBundle T) (B : ∀ k, FormBundle A k)
    (D : ∀ k, Field T k → Field T (k+1)) (hD : DerivativeAxioms A B D)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (z : P) → TangentSpace T z →ₗ[ℝ] TangentSpace S (f z))
    (hL : ∀ z, IsDifferential T S f z (L z))
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (q : P) (hq : (f q) ∈ c.source)
    (r : Fin n → P → ℝ)
    (hr : ∀ j, ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val (r j) q)
    (α : CovectorField T)
    (hα : IsForm (B 1) (fun z =>
      (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm (α z)))
    (hαcoord : ∀ (z : P) (hz : (f z) ∈ c.source), α z = ∑ j : Fin n,
      r j z • (coordinateCovector C.tangent.fiberCoordinates c hc (f z) hz j).comp (L z)) :
    ∃ g : Fin n → SmoothGerm T q,
      (∀ j, (g j).val = Germ.ofFun (r j)) ∧
      D 1 (fun z => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm (α z)) q =
        ∑ j : Fin n, ExteriorData.wedge (V := TangentSpace T q) (k := 1) (l := 1)
          ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
            (germDifferential T q (g j)))
          ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
            ((coordinateCovector C.tangent.fiberCoordinates c hc (f q) hq j).comp (L q))) := by
  classical
  choose x hx hxe hdx using fun j : Fin n =>
    scalar_globalize_coordinate_differential C c hc (f q) hq j
  choose hxp hdxp using fun j : Fin n =>
    Covectors.pullback_differential S T f hf L hL (x j) (hx j)
  choose b hb hbe using fun j : Fin n => exists_global_representative T q (r j) (hr j)
  let γ : Fin n → Field T 1 := fun j z =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm
      (dFunction T (x j ∘ f) (hxp j) z)
  have hγeq (j : Fin n) : D 0 (scalarField T (x j ∘ f)) = γ j := by
    funext z
    exact hD.function_rule _ (hxp j) z
  have hγ (j : Fin n) : IsForm (B 1) (γ j) :=
    hγeq j ▸ hD.smooth 0 _ (scalarField_form A (B 0) _ (hxp j))
  have hγD (j : Fin n) : D 1 (γ j) = 0 :=
    axioms_exact_closed A B D hD _ (hxp j)
  let τ : Fin n → Field T 1 := fun j z => b j z • γ j z
  have hT (j : Fin n) : IsForm (B 1) (τ j) := by
    have hh := ExteriorAlgebraResults.wedge_smooth A 1 0 (B 1) (B 0) (B 1)
      (γ j) (scalarField T (b j)) (hγ j) (scalarField_form A (B 0) _ (hb j))
    rw [fieldWedge_scalar] at hh
    exact hh
  let θ : Field T 1 := fun z =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm (α z)
  have hθ : IsForm (B 1) θ := hα
  have hbeall : ∀ᶠ z in 𝓝 q, ∀ j, b j z = r j z := Filter.eventually_all.mpr hbe
  have hdxall : ∀ᶠ z in 𝓝 q, ∀ j, ∀ hz : (f z) ∈ c.source,
      dFunction S (x j) (hx j) (f z) =
        coordinateCovector C.tangent.fiberCoordinates c hc (f z) hz j :=
    Filter.eventually_all.mpr (fun j => (hf q).1.eventually (hdx j))
  have hloc : ∀ᶠ z in 𝓝 q, θ z = (∑ j, τ j) z := by
    filter_upwards [hbeall, hdxall, (hf q).1.preimage_mem_nhds (c.open_source.mem_nhds hq)]
      with z hbz hdxz hz
    have ht := hαcoord z hz
    have hγz (j : Fin n) :
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm
          ((coordinateCovector C.tangent.fiberCoordinates c hc (f z) hz j).comp (L z)) = γ j z := by
      apply congrArg (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm
      have hdj : dFunction T (x j ∘ f) (hxp j) z =
          (dFunction S (x j) (hx j) (f z)).comp (L z) := congrFun (hdxp j) z
      exact (hdj.trans (congrArg (fun α : CotangentFiber S (f z) => α.comp (L z)) (hdxz j hz))).symm
    have hpoint := oneEquiv_sum_smul (V := TangentSpace T z) (ι := Fin n) (α z) (fun j => r j z)
      (fun j => b j z)
      (fun j => (coordinateCovector C.tangent.fiberCoordinates c hc (f z) hz j).comp (L z))
      (fun j => γ j z) ht (fun j => (hbz j).symm) hγz
    simpa only [θ, Finset.sum_apply, τ] using hpoint
  refine ⟨fun j => functionGerm T (b j) (hb j) q, ?_, ?_⟩
  · intro j
    exact Germ.coe_eq.mpr (hbe j)
  · apply Subtype.val_injective
    have hmain := axioms_closed_sum_at A B D hD 1 θ hθ b hb γ hγ hγD q
      (by simpa only [Finset.sum_apply, τ] using hloc)
    refine hmain.trans ?_
    change (∑ j, ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
      (dFunction T (b j) (hb j) q)).val * (γ j q).val) = _
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hdj : dFunction T (x j ∘ f) (hxp j) q =
        (dFunction S (x j) (hx j) (f q)).comp (L q) := congrFun (hdxp j) q
    have hγq : γ j q = (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
        ((coordinateCovector C.tangent.fiberCoordinates c hc (f q) hq j).comp (L q)) :=
      congrArg (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
        (hdj.trans (congrArg (fun α : CotangentFiber S (f q) => α.comp (L q))
          ((hdx j).self_of_nhds hq)))
    exact congrArg (fun v : Fiber (TangentSpace T q) 1 =>
      ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
        (dFunction T (b j) (hb j) q)).val * v.val) hγq

theorem tautological_axioms_coordinates {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S) :
    letI := (cotangentSpace C).topology
    let Q := (cotangentSpace C).bundle.totalManifold
    ∀ (A : CotangentBundle Q) (B : ∀ k, FormBundle A k)
      (D : ∀ k, Field Q k → Field Q (k+1)), DerivativeAxioms A B D →
      ∀ (L : (ξ : CotangentTotal S) → TangentSpace Q ξ →ₗ[ℝ] TangentSpace S ξ.proj),
      (∀ ξ, IsDifferential Q S Bundle.TotalSpace.proj ξ (L ξ)) →
      ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (ξ : CotangentTotal S) (hξ : ξ.proj ∈ c.source),
        ∃ g : Fin n → SmoothGerm Q ξ,
          (∀ j, (g j).val = Germ.ofFun (fun ζ : CotangentTotal S =>
            (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ζ).2 j)) ∧
          D 1 (fun ζ => (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ζ))).symm
            (tautologicalField C L ζ)) ξ = ∑ j : Fin n,
            ExteriorData.wedge (V := TangentSpace Q ξ) (k := 1) (l := 1)
              ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ξ))).symm
                (germDifferential Q ξ (g j)))
              ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace Q ξ))).symm
                ((coordinateCovector C.tangent.fiberCoordinates c hc ξ.proj hξ j).comp (L ξ))) := by
  letI := (cotangentSpace C).topology
  let Q := (cotangentSpace C).bundle.totalManifold
  dsimp only
  intro A B D hD L hL c hc ξ hξ
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hπ : IsSmoothMap Q S Bundle.TotalSpace.proj := (cotangentSpace C).bundle.projection_smooth
  let momentum : Fin n → CotangentTotal S → ℝ := fun j ζ =>
    (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ζ).2 j
  have hξC : ξ.proj ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
    rw [Covectors.cotangent_baseSet]
    exact hξ
  have hmom (j : Fin n) : ScalarContDiffAt (⊤ : ℕ∞) Q.smoothStructure.val (momentum j) ξ := by
    apply (scalarContDiffAt_iff (⊤ : ℕ∞) Q.smoothStructure.val _ ξ).mpr
    exact (Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle ⟨c, hc⟩ ξ hξC).postcomp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).contDiff
  exact axioms_local_covector_sum S Q C A B D hD Bundle.TotalSpace.proj hπ L hL c hc ξ hξ
    momentum hmom (tautologicalField C L)
    (oneForm_isForm A (B 1) _ (FormPullbackResults.tautological_smooth C L hL A))
    (fun ζ hζ => @FormPullbackResults.tautological_coordinates n a M _ S C L hL c hc ζ hζ)


theorem covector_sum_derivative_exists {n m : ℕ} {a b : ModelKind} {M P : Type u}
    [TopologicalSpace M] [TopologicalSpace P]
    (S : SmoothManifold n a M) (T : SmoothManifold m b P)
    (C : CotangentBundle S) (A : CotangentBundle T) (B : FormBundle A 2)
    (f : P → M) (hf : IsSmoothMap T S f)
    (L : (z : P) → TangentSpace T z →ₗ[ℝ] TangentSpace S (f z))
    (hL : ∀ z, IsDifferential T S f z (L z))
    (α : CovectorField T) (hα : IsOneForm A α)
    (r : ∀ (c : ModelChart n a M), c ∈ S.smoothStructure.val → Fin n → P → ℝ)
    (hr : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (q : P), f q ∈ c.source → ∀ j,
      ScalarContDiffAt (⊤ : ℕ∞) T.smoothStructure.val (r c hc j) q)
    (hαcoord : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (z : P) (hz : f z ∈ c.source), α z = ∑ j : Fin n,
      r c hc j z • (coordinateCovector C.tangent.fiberCoordinates c hc (f z) hz j).comp (L z)) :
    ∃ η : Field T 2, IsForm B η ∧
      HasExteriorDerivative A (fun z =>
        (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm (α z)) η ∧
      ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
        (q : P) (hq : f q ∈ c.source),
        ∃ g : Fin n → SmoothGerm T q,
          (∀ j, (g j).val = Germ.ofFun (r c hc j)) ∧
          η q = ∑ j : Fin n, ExteriorData.wedge (V := TangentSpace T q) (k := 1) (l := 1)
            ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
              (germDifferential T q (g j)))
            ((exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T q))).symm
              ((coordinateCovector C.tangent.fiberCoordinates c hc (f q) hq j).comp (L q))) := by
  classical
  let F : ∀ k, FormBundle A k := fun k => Classical.choice (ExteriorAlgebraResults.exists_formBundle A k)
  obtain ⟨D, hD, huniq⟩ := smooth_family_exists A F
  let θ : Field T 1 := fun z =>
    (exteriorPower.oneEquiv ℝ (Module.Dual ℝ (TangentSpace T z))).symm (α z)
  have hθ : IsForm (F 1) θ := oneForm_isForm A (F 1) α hα
  have hHas : HasExteriorDerivative A θ (D 1 θ) := global_coordinates A F D hD 1 θ hθ
  refine ⟨D 1 θ, derivative_smooth A 1 (F 1) B θ (D 1 θ) hθ hHas, hHas, ?_⟩
  intro c hc q hq
  exact axioms_local_covector_sum S T C A F D hD f hf L hL c hc q hq
    (r c hc) (hr c hc q hq) α hθ (hαcoord c hc)

theorem tautological_derivative :
    Specs.SmoothManifolds.Ch07.ExteriorDerivative.tautological_derivativeType.{u} := by
  intro n a M _ S C
  letI := (cotangentSpace C).topology
  let Q := (cotangentSpace C).bundle.totalManifold
  dsimp only
  intro A B L hL
  letI : NormedSpace ℝ ℝ := NormedField.toNormedSpace
  have hπ : IsSmoothMap Q S Bundle.TotalSpace.proj := (cotangentSpace C).bundle.projection_smooth
  let r : ∀ (c : ModelChart n a M), c ∈ S.smoothStructure.val → Fin n → CotangentTotal S → ℝ :=
    fun c hc j ζ => (((cotangentSpace C).bundle.trivialization ⟨c, hc⟩) ζ).2 j
  have hr (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
      (ξ : CotangentTotal S) (hξ : ξ.proj ∈ c.source) (j : Fin n) :
      ScalarContDiffAt (⊤ : ℕ∞) Q.smoothStructure.val (r c hc j) ξ := by
    have hξC : ξ.proj ∈ (cotangentSpace C).bundle.baseSet ⟨c, hc⟩ := by
      rw [Covectors.cotangent_baseSet]
      exact hξ
    apply (scalarContDiffAt_iff (⊤ : ℕ∞) Q.smoothStructure.val _ ξ).mpr
    exact (Frames.trivializationCoordinates_smoothAt (cotangentSpace C).bundle ⟨c, hc⟩ ξ hξC).postcomp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).contDiff
  exact covector_sum_derivative_exists S Q C A B Bundle.TotalSpace.proj hπ L hL
    (tautologicalField C L) (FormPullbackResults.tautological_smooth C L hL A) r hr
    (fun c hc ζ hζ => @FormPullbackResults.tautological_coordinates n a M _ S C L hL c hc ζ hζ)


end SmoothManifolds.ExteriorDerivativeResults
