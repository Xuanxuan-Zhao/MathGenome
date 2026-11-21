import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityUniqueness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityExistence
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.SpectralMeasure.FugledeIntertwining
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal CompactlySupported
namespace ExpandedFA.VonNeumann.MultiplicityUniqueness
open MultiplicityModel.Spec
open MultiplicityExistence

/-- Coordinate-by-coordinate a.e. identities have one common exceptional set. -/
theorem ae_coordinates_eq {μ : Measure ℂ} {f g : ℂ → SequenceSpace}
    (h : ∀ k, ∀ᵐ z ∂μ, f z k = g z k) : f =ᵐ[μ] g := by
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact lp.ext (funext hz)

/-- Changing multiplicity only on a null set changes neither L² classes nor
coordinate multiplication. -/
def sameMeasureEquivalence {μ : Measure ℂ} (m n : Multiplicity μ)
    (h : m.toFun =ᵐ[μ] n.toFun) : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n :=
  LpFamily.restrictEquivalence (LinearIsometryEquiv.refl ℂ _) _ _ (fun f => by
    rw [MultiplicityModel.multiplicity_invariance μ m n h]
    rfl)

@[simp] theorem sameMeasureEquivalence_val {μ : Measure ℂ} (m n : Multiplicity μ)
    (h : m.toFun =ᵐ[μ] n.toFun) (f : DirectIntegral μ m) :
    (sameMeasureEquivalence m n h f).val = f.val := rfl

theorem sameMeasureEquivalence_coordinate {μ : Measure ℂ} (m n : Multiplicity μ)
    (h : m.toFun =ᵐ[μ] n.toFun) (hμ hν : BoundedCoordinate μ) (f : DirectIntegral μ m) :
    sameMeasureEquivalence m n h (coordinateOperatorValue μ m hμ f) =
      coordinateOperatorValue μ n hν (sameMeasureEquivalence m n h f) := by
  apply Subtype.ext
  apply Lp.ext
  exact (coordinateLpValue_ae hμ f).trans (coordinateLpValue_ae hν f).symm

namespace RNTransport
variable (ν μ : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure μ]

/-- Mutual absolute continuity removes the support restriction on scalar RN
transport. This remains a surjection when both measures are zero. -/
theorem scalar_surjective (hνμ : ν ≪ μ) (hμν : μ ≪ ν) :
    Function.Surjective (ScalarRN.transport ν μ hνμ) := by
  intro g
  apply ScalarRN.transport_surjective_supported
  filter_upwards [hμν.ae_le (Measure.rnDeriv_pos hνμ)] with z hz
  exact fun hzero => False.elim (hz.ne' hzero)

def scalar (hνμ : ν ≪ μ) (hμν : μ ≪ ν) : Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (ScalarRN.transport ν μ hνμ)
    (scalar_surjective ν μ hνμ hμν)

/-- Direct sum of scalar RN unitaries. -/
def family (hνμ : ν ≪ μ) (hμν : μ ≪ ν) :
    lp (fun _ : ℕ => Lp ℂ 2 ν) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℕ => Lp ℂ 2 μ) 2 :=
  { toLinearEquiv :=
      { toFun := LpFamily.map (fun _ => (scalar ν μ hνμ hμν).toLinearIsometry)
        invFun := LpFamily.map (fun _ => (scalar ν μ hνμ hμν).symm.toLinearIsometry)
        left_inv := fun x => by
          apply lp.ext; funext j
          exact (scalar ν μ hνμ hμν).symm_apply_apply (x j)
        right_inv := fun x => by
          apply lp.ext; funext j
          exact (scalar ν μ hνμ hμν).apply_symm_apply (x j)
        map_add' := fun x y => (LpFamily.map _).map_add x y
        map_smul' := fun c x => (LpFamily.map _).map_smul c x }
    norm_map' := fun x => (LpFamily.map _).norm_map x }

/-- RN transport of ℓ²-valued L² functions via the already proved packing
unitaries. Its pointwise formula is proved below, using one common null set. -/
def ambient (hνμ : ν ≪ μ) (hμν : μ ≪ ν) :
    Lp SequenceSpace 2 ν ≃ₗᵢ[ℂ] Lp SequenceSpace 2 μ :=
  (L2Packing.pack ν).symm.trans ((family ν μ hνμ hμν).trans (L2Packing.pack μ))

theorem ambient_ae (hνμ : ν ≪ μ) (hμν : μ ≪ ν) (f : Lp SequenceSpace 2 ν) :
    ambient ν μ hνμ hμν f =ᵐ[μ] fun z => ScalarRN.weight ν μ z • f z := by
  let x := (L2Packing.pack ν).symm f
  have hμpack := L2Packing.pack_ae μ (family ν μ hνμ hμν x)
  have hνpack := L2Packing.pack_ae ν x
  have hscalar : ∀ j, ∀ᵐ z ∂μ,
      (family ν μ hνμ hμν x) j z = ScalarRN.weight ν μ z • x j z :=
    fun j => ScalarRN.transport_apply ν μ hνμ (x j)
  have hpack : ∀ᵐ z ∂μ, ∀ j, x j z = f z j := by
    apply hμν.ae_le
    filter_upwards [hνpack] with z hz j
    simpa only [x, LinearIsometryEquiv.apply_symm_apply] using (hz j).symm
  filter_upwards [hμpack, ae_all_iff.mpr hscalar, hpack] with z hz hr hp
  apply lp.ext
  funext j
  change L2Packing.pack μ (family ν μ hνμ hμν x) z j = _
  rw [hz j, hr j, hp j]
  rfl

/-- The square-root derivative is nonzero on a common μ-conull set. -/
theorem weight_nonzero (hνμ : ν ≪ μ) (hμν : μ ≪ ν) :
    ∀ᵐ z ∂μ, ScalarRN.weight ν μ z ≠ 0 := by
  filter_upwards [hμν.ae_le (Measure.rnDeriv_pos hνμ), Measure.rnDeriv_ne_top ν μ]
    with z hpos htop
  exact ScalarRN.weight_ne_zero ν μ hpos.ne' htop

/-- RN transport preserves the variable coordinate support condition. -/
theorem ambient_mem_iff (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (m : Multiplicity ν) (n : Multiplicity μ) (hmn : m.toFun =ᵐ[μ] n.toFun)
    (f : Lp SequenceSpace 2 ν) :
    f ∈ directIntegralSubmodule ν m ↔
      ambient ν μ hνμ hμν f ∈ directIntegralSubmodule μ n := by
  constructor
  · intro hf
    filter_upwards [hμν.ae_le hf, ambient_ae ν μ hνμ hμν f, hmn] with z hf hW hmn
    intro k hk
    rw [hW]
    change ScalarRN.weight ν μ z • f z k = 0
    rw [hf k (by simpa only [hmn] using hk), smul_zero]
  · intro hf
    apply hνμ.ae_le
    filter_upwards [hf, ambient_ae ν μ hνμ hμν f, weight_nonzero ν μ hνμ hμν, hmn]
      with z hf hW hw hmn
    intro k hk
    have hzero := hf k (by simpa only [← hmn] using hk)
    rw [hW] at hzero
    change ScalarRN.weight ν μ z • f z k = 0 at hzero
    exact (smul_eq_zero.mp hzero).resolve_left hw

/-- The RN unitary between the actual direct integrals, including null-set
changes of multiplicity, not just an equivalence of scalar L² spaces. -/
def sections (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (m : Multiplicity ν) (n : Multiplicity μ) (hmn : m.toFun =ᵐ[μ] n.toFun) :
    DirectIntegral ν m ≃ₗᵢ[ℂ] DirectIntegral μ n :=
  LpFamily.restrictEquivalence (ambient ν μ hνμ hμν) _ _
    (ambient_mem_iff ν μ hνμ hμν m n hmn)

/-- Arbitrary multiplication graphs are preserved; no extra boundedness of
the derivative, or of the scalar function, is required. -/
theorem ambient_covariant (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (φ : ℂ → ℂ) (f g : Lp SequenceSpace 2 ν)
    (hfg : g =ᵐ[ν] fun z => φ z • f z) :
    ambient ν μ hνμ hμν g =ᵐ[μ] fun z => φ z • ambient ν μ hνμ hμν f z := by
  filter_upwards [ambient_ae ν μ hνμ hμν g, ambient_ae ν μ hνμ hμν f,
    hμν.ae_le hfg] with z hg hf hz
  rw [hg, hf, hz]
  exact smul_comm _ _ _

theorem sections_coordinate (hνμ : ν ≪ μ) (hμν : μ ≪ ν)
    (m : Multiplicity ν) (n : Multiplicity μ) (hmn : m.toFun =ᵐ[μ] n.toFun)
    (hν : BoundedCoordinate ν) (hμ : BoundedCoordinate μ) (f : DirectIntegral ν m) :
    sections ν μ hνμ hμν m n hmn (coordinateOperatorValue ν m hν f) =
      coordinateOperatorValue μ n hμ (sections ν μ hνμ hμν m n hmn f) := by
  apply Subtype.ext
  apply Lp.ext
  exact (ambient_covariant ν μ hνμ hμν id f.val
    (coordinateOperatorValue ν m hν f).val (coordinateLpValue_ae hν f)).trans
      (coordinateLpValue_ae hμ (sections ν μ hνμ hμν m n hmn f)).symm

end RNTransport
def fiberCoordinates (n : ℕ) : fiber (n : ℕ∞) →ₗ[ℂ] (Fin n → ℂ) where
  toFun x i := x.val i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fiberCoordinates_injective (n : ℕ) : Function.Injective (fiberCoordinates n) := by
  intro x y h
  apply Subtype.ext
  apply lp.ext
  funext k
  by_cases hk : k < n
  · exact congrFun h ⟨k, hk⟩
  · rw [x.property k (by exact_mod_cast hk), y.property k (by exact_mod_cast hk)]

def finiteSequence (n : ℕ) (x : Fin n → ℂ) : SequenceSpace := by
  classical
  refine ⟨fun k => if h : k < n then x ⟨k,h⟩ else 0, ?_⟩
  apply Memℓp.of_exponent_ge (q := 0) _ zero_le
  apply memℓp_zero
  apply (Set.finite_Iio n).subset
  intro k hk
  by_contra h
  simp only [Set.mem_Iio] at h
  simp [h] at hk

theorem fiberCoordinates_surjective (n : ℕ) : Function.Surjective (fiberCoordinates n) := by
  classical
  intro x
  refine ⟨⟨finiteSequence n x, ?_⟩, ?_⟩
  · intro k hk
    have h : ¬ k < n := by exact_mod_cast hk
    simp [finiteSequence, h]
  · funext i
    change (if h : (i : ℕ) < n then x ⟨i,h⟩ else 0) = x i
    simp [i.isLt]

def finiteFiberEquiv (n : ℕ) : fiber (n : ℕ∞) ≃ₗ[ℂ] (Fin n → ℂ) :=
  LinearEquiv.ofBijective (fiberCoordinates n)
    ⟨fiberCoordinates_injective n, fiberCoordinates_surjective n⟩

instance finiteFiberFiniteDimensional (n : ℕ) : FiniteDimensional ℂ (fiber (n : ℕ∞)) :=
  Module.Finite.of_injective (fiberCoordinates n) (fiberCoordinates_injective n)

theorem finiteFiber_finrank (n : ℕ) : Module.finrank ℂ (fiber (n : ℕ∞)) = n := by
  rw [(finiteFiberEquiv n).finrank_eq]
  simp

/-- Any isometric surjection between actual fibers is an algebraic equivalence. -/
def fiberEquiv {d e : ℕ∞} (B : SequenceSpace →L[ℂ] SequenceSpace)
    (hB : Spec.IsFiberUnitary d e B) : fiber d ≃ₗ[ℂ] fiber e :=
  LinearEquiv.ofBijective ((B.toLinearMap.domRestrict (fiber d)).codRestrict
    (fiber e) (fun x => hB.1 x)) (by
      constructor
      · intro x y h
        apply sub_eq_zero.mp
        apply Subtype.ext
        apply norm_eq_zero.mp
        change ‖x.val - y.val‖ = 0
        rw [← hB.2.2.1 (x.val - y.val) ((fiber d).sub_mem x.property y.property)]
        have heq : B x.val = B y.val := congrArg Subtype.val h
        rw [map_sub, heq, sub_self, norm_zero]
      · intro y
        obtain ⟨x,hx,hxy⟩ := hB.2.2.2 y.val y.property
        exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩)

/-- There are at least k independent coordinates when k ≤ d. -/
def initialFiberEmbedding (k : ℕ) (d : ℕ∞) (hkd : (k : ℕ∞) ≤ d) :
    fiber (k : ℕ∞) →ₗ[ℂ] fiber d :=
  Submodule.inclusion (by
    intro x hx j hj
    apply hx j
    exact fun h => hj (h.trans_le hkd))

theorem finiteFiber_infinite {n : ℕ}
    (e : fiber (n : ℕ∞) ≃ₗ[ℂ] fiber (⊤ : ℕ∞)) : False := by
  let L := (e.symm.toLinearMap.comp (initialFiberEmbedding (n+1) ⊤ le_top))
  have hL : Function.Injective L :=
    e.symm.injective.comp (Submodule.inclusion_injective _)
  have h := LinearMap.finrank_le_finrank_of_injective hL
  rw [finiteFiber_finrank, finiteFiber_finrank] at h
  omega

theorem fiber_dimension : Spec.FiberDimension := by
  intro d e B hB
  have U := fiberEquiv B hB
  induction d using ENat.recTopCoe with
  | top =>
    induction e using ENat.recTopCoe with
    | top => rfl
    | coe n => exact (finiteFiber_infinite U.symm).elim
  | coe m =>
    induction e using ENat.recTopCoe with
    | top => exact (finiteFiber_infinite U).elim
    | coe n =>
      have h := U.finrank_eq
      rw [finiteFiber_finrank, finiteFiber_finrank] at h
      exact congrArg Nat.cast h


theorem sufficiency : Spec.Sufficiency := by
  intro μ ν _ _ m n hμ hν hdata
  refine ⟨RNTransport.sections μ ν hdata.1 hdata.2.1 m n
    (hdata.2.1.ae_le hdata.2.2), ?_⟩
  exact RNTransport.sections_coordinate μ ν hdata.1 hdata.2.1 m n
    (hdata.2.1.ae_le hdata.2.2) hμ hν

/-- Reuse a measurable multiplicity representative on an absolutely
continuous measure. There is no pointwise positivity assumption. -/
def rebaseMultiplicity {μ ν : Measure ℂ} (n : Multiplicity ν) (hμν : μ ≪ ν) :
    Multiplicity μ where
  toFun := n.toFun
  measurable_toFun := n.measurable_toFun
  positive := hμν.ae_le n.positive

/-- Composition of equivalences preserves the specified coordinate, rather
than merely conjugating to some unitarily equivalent normal operator. -/
theorem coordinateEquivalent_trans {μ ν ρ : Measure ℂ}
    {m : Multiplicity μ} {n : Multiplicity ν} {p : Multiplicity ρ}
    {hμ : BoundedCoordinate μ} {hν : BoundedCoordinate ν} {hρ : BoundedCoordinate ρ}
    (hU : Spec.CoordinateEquivalent μ ν m n hμ hν)
    (hV : Spec.CoordinateEquivalent ν ρ n p hν hρ) :
    Spec.CoordinateEquivalent μ ρ m p hμ hρ := by
  obtain ⟨U, hU⟩ := hU
  obtain ⟨V, hV⟩ := hV
  refine ⟨U.trans V, ?_⟩
  intro f
  change V (U (coordinateOperatorValue μ m hμ f)) =
    coordinateOperatorValue ρ p hρ (V (U f))
  rw [hU, hV]

/-- Fiber unitarity is on one common conull set, so the dimension comparison
also holds with one exceptional set, including infinite fibers. -/
theorem multiplicity_eq_of_unitaryField {μ : Measure ℂ} {m n : Multiplicity μ}
    (B : Spec.UnitaryField μ m n) : m.toFun =ᵐ[μ] n.toFun :=
  B.unitary.mono fun z hz => fiber_dimension (m z) (n z) (B z) hz

/-- A canonical zero extension of a fiber unitary is a contraction even when
its source fiber is zero. -/
theorem fiberUnitary_norm_le_one {d e : ℕ∞}
    (B : SequenceSpace →L[ℂ] SequenceSpace) (hB : Spec.IsFiberUnitary d e B) :
    ‖B‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  let P := (fiber d).starProjection
  have hz := hB.2.1 (x - P x) ((fiber d).sub_starProjection_mem_orthogonal x)
  rw [map_sub] at hz
  have heq := sub_eq_zero.mp hz
  rw [heq, hB.2.2.1 (P x) ((fiber d).starProjection_apply_mem x), one_mul]
  exact (fiber d).norm_starProjection_apply_le x

/-- Assembly of measure-class invariance, scalar intertwining and fiber reconstruction. -/
theorem classification_from_bridges : Spec.ClassificationFromBridges := by
  intro hmeasure hscalar hfield μ ν _ _ m n hμ hν
  constructor
  · intro hU
    obtain ⟨hμν, hνμ⟩ := hmeasure μ ν m n hμ hν hU
    let n' : Multiplicity μ := rebaseMultiplicity n hμν
    have htransport : Spec.CoordinateEquivalent ν μ n n' hν hμ := by
      refine ⟨RNTransport.sections ν μ hνμ hμν n n' Filter.EventuallyEq.rfl, ?_⟩
      exact RNTransport.sections_coordinate ν μ hνμ hμν n n' Filter.EventuallyEq.rfl hν hμ
    obtain ⟨W,hW⟩ := coordinateEquivalent_trans hU htransport
    obtain ⟨B,_⟩ := hfield μ m n' W (hscalar μ m n' hμ hμ W hW)
    exact ⟨hμν, hνμ, multiplicity_eq_of_unitaryField B⟩
  · exact sufficiency μ ν m n hμ hν



namespace FiberBasis
open scoped InnerProductSpace
abbrev Index (d : ℕ∞) := {k : ℕ // (k : ℕ∞) < d}

def vector (d : ℕ∞) (i : Index d) : fiber d :=
  ⟨lp.single 2 i.val (1 : ℂ), by
    intro j hj
    rw [lp.single_apply]
    apply Pi.single_eq_of_ne
    intro heq
    subst j
    exact hj i.property⟩

lemma orthonormal (d : ℕ∞) : Orthonormal ℂ (vector d) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪(lp.single 2 i.val (1 : ℂ) : SequenceSpace), lp.single 2 j.val (1 : ℂ)⟫_ℂ = _
  simp only [lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst j; simp
  · have hv : i.val ≠ j.val := fun hh => h (Subtype.ext hh)
    simp [hv, h]

lemma total (d : ℕ∞) : (Submodule.span ℂ (Set.range (vector d)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply Subtype.ext
  apply lp.ext
  funext k
  change x.val k = 0
  by_cases hk : (k : ℕ∞) < d
  · have h := hx (vector d ⟨k,hk⟩) (Submodule.subset_span ⟨⟨k,hk⟩,rfl⟩)
    change ⟪(lp.single 2 k (1 : ℂ) : SequenceSpace), x.val⟫_ℂ = 0 at h
    simpa only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using h
  · exact x.property k hk

def basis (d : ℕ∞) : HilbertBasis (Index d) ℂ (fiber d) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal d) (total d)

@[simp] lemma basis_apply (d : ℕ∞) (i : Index d) : basis d i = vector d i := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot (orthonormal d) (total d)) i

lemma ext {d : ℕ∞} {x y : fiber d}
    (h : ∀ i, ⟪vector d i, x⟫_ℂ = ⟪vector d i, y⟫_ℂ) : x = y := by
  apply (basis d).repr.injective
  apply lp.ext
  funext i
  simpa only [HilbertBasis.repr_apply_apply, basis_apply] using h i

/-- Map the coordinate Hilbert basis to any orthonormal column family. -/
def columnMap {d e : ℕ∞} (a : Index d → fiber e) (ha : Orthonormal ℂ a) :
    fiber d →ₗᵢ[ℂ] fiber e :=
  ha.orthogonalFamily.linearIsometry.comp (basis d).repr.toLinearIsometry

@[simp] lemma columnMap_vector {d e : ℕ∞} (a : Index d → fiber e)
    (ha : Orthonormal ℂ a) (i : Index d) : columnMap a ha (vector d i) = a i := by
  change ha.orthogonalFamily.linearIsometry ((basis d).repr (vector d i)) = a i
  rw [← basis_apply d i, HilbertBasis.repr_self]
  simp [LinearIsometry.toSpanSingleton_apply]

/-- The coefficient of the image against one of its columns is the original
coordinate, even for an infinite coordinate fiber. -/
lemma inner_columnMap {d e : ℕ∞} (a : Index d → fiber e)
    (ha : Orthonormal ℂ a) (i : Index d) (x : fiber d) :
    ⟪a i, columnMap a ha x⟫_ℂ = x.val i.val := by
  rw [← columnMap_vector a ha i, (columnMap a ha).inner_map_map]
  change ⟪(lp.single 2 i.val (1 : ℂ) : SequenceSpace), x.val⟫_ℂ = _
  simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]


/-- Continuous maps are determined by their values on the coordinate Hilbert basis. -/
lemma map_ext {d : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A B : fiber d →L[ℂ] E) (h : ∀ i, A (vector d i) = B (vector d i)) : A = B := by
  apply ContinuousLinearMap.ext
  intro x
  have hA := A.hasSum ((basis d).hasSum_repr x)
  have hB := B.hasSum ((basis d).hasSum_repr x)
  have ht : (fun i => A ((basis d).repr x i • basis d i)) =
      fun i => B ((basis d).repr x i • basis d i) := by
    funext i
    simp only [map_smul, basis_apply, h i]
  rw [ht] at hA
  exact hA.unique hB

/-- Cross-coordinate inner products identify the reverse column map as the
actual Hilbert adjoint. -/
lemma columnMap_adjoint {d e : ℕ∞} (a : Index d → fiber e) (b : Index e → fiber d)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hc : ∀ i j, ⟪a i, vector e j⟫_ℂ = ⟪vector d i, b j⟫_ℂ) :
    (columnMap a ha).toContinuousLinearMap.adjoint = (columnMap b hb).toContinuousLinearMap := by
  apply map_ext
  intro j
  apply ext
  intro i
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪columnMap a ha (vector d i), vector e j⟫_ℂ =
    ⟪vector d i, columnMap b hb (vector e j)⟫_ℂ
  rw [columnMap_vector, columnMap_vector]
  exact hc i j

/-- Both column families must be used: forward orthonormality alone gives
only an isometry, whereas reverse orthonormality and the cross tests give onto. -/
lemma columnMap_surjective {d e : ℕ∞} (a : Index d → fiber e) (b : Index e → fiber d)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hc : ∀ i j, ⟪a i, vector e j⟫_ℂ = ⟪vector d i, b j⟫_ℂ) :
    Function.Surjective (columnMap a ha) := by
  have hadj := columnMap_adjoint a b ha hb hc
  have hrev : (columnMap b hb).toContinuousLinearMap.adjoint =
      (columnMap a ha).toContinuousLinearMap := by
    rw [← hadj, ContinuousLinearMap.adjoint_adjoint]
  have h := (columnMap b hb).adjoint_comp_self
  rw [hrev] at h
  intro y
  refine ⟨columnMap b hb y, ?_⟩
  exact congrArg (fun T : fiber e →L[ℂ] fiber e => T y) h

/-- Canonical ambient zero extension of the forward column isometry. -/
def extension {d e : ℕ∞} (a : Index d → fiber e) (ha : Orthonormal ℂ a) :
    SequenceSpace →L[ℂ] SequenceSpace :=
  (fiber e).subtypeL ∘L (columnMap a ha).toContinuousLinearMap ∘L
    (fiber d).orthogonalProjectionOnto

lemma extension_unitary {d e : ℕ∞} (a : Index d → fiber e) (b : Index e → fiber d)
    (ha : Orthonormal ℂ a) (hb : Orthonormal ℂ b)
    (hc : ∀ i j, ⟪a i, vector e j⟫_ℂ = ⟪vector d i, b j⟫_ℂ) :
    Spec.IsFiberUnitary d e (extension a ha) := by
  refine ⟨fun x => (columnMap a ha ((fiber d).orthogonalProjectionOnto x)).property, ?_, ?_, ?_⟩
  · intro x hx
    simp [extension, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hx]
  · intro x hx
    change ‖columnMap a ha ((fiber d).orthogonalProjectionOnto x)‖ = ‖x‖
    rw [(columnMap a ha).norm_map]
    change ‖(fiber d).orthogonalProjectionOnto (⟨x,hx⟩ : fiber d)‖ = ‖(⟨x,hx⟩ : fiber d)‖
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  · intro y hy
    obtain ⟨x,hx⟩ := columnMap_surjective a b ha hb hc ⟨y,hy⟩
    refine ⟨x.val, x.property, ?_⟩
    change (columnMap a ha ((fiber d).orthogonalProjectionOnto x.val)).val = y
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact congrArg Subtype.val hx


@[simp] lemma extension_apply {d e : ℕ∞} (a : Index d → fiber e)
    (ha : Orthonormal ℂ a) (x : fiber d) :
    extension a ha x.val = (columnMap a ha x).val := by
  simp [extension]

lemma single_orthogonal {d : ℕ∞} {k : ℕ} (hk : ¬ (k : ℕ∞) < d) :
    (lp.single 2 k (1 : ℂ) : SequenceSpace) ∈ (fiber d)ᗮ := by
  intro x hx
  rw [lp.inner_single_right, hx k hk]
  simp

lemma extension_single {d e : ℕ∞} (a : Index d → fiber e)
    (ha : Orthonormal ℂ a) (k : ℕ) :
    extension a ha (lp.single 2 k (1 : ℂ)) =
      if hk : (k : ℕ∞) < d then (a ⟨k,hk⟩).val else 0 := by
  classical
  by_cases hk : (k : ℕ∞) < d
  · rw [dite_eq_left hk]
    change extension a ha (vector d ⟨k,hk⟩).val = _
    rw [extension_apply, columnMap_vector]
  · rw [dite_eq_right hk]
    simp [extension, Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
      (single_orthogonal hk)]

end FiberBasis

namespace Localization
open scoped InnerProductSpace
variable {μ : Measure ℂ} {m n : Multiplicity μ}

/-- Restrict a native section to a measurable set. -/
def restrictSection {s : Set ℂ} (hs : MeasurableSet s) (f : DirectIntegral μ m) :
    DirectIntegral μ m :=
  ⟨((Lp.memLp f.val).indicator hs.nullMeasurableSet).toLp (s.indicator f.val), by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f.val).indicator hs.nullMeasurableSet), f.property]
      with z hz hf
    rw [hz]
    by_cases hzs : z ∈ s
    · simpa only [Set.indicator_of_mem hzs] using hf
    · simp only [Set.indicator_of_notMem hzs]
      exact (fiber (m z)).zero_mem⟩

lemma section_ae {s : Set ℂ} (hs : MeasurableSet s) (f : DirectIntegral μ m) :
    (restrictSection hs f).val =ᵐ[μ] s.indicator f.val :=
  MemLp.coeFn_toLp ((Lp.memLp f.val).indicator hs.nullMeasurableSet)

lemma section_add {s : Set ℂ} (hs : MeasurableSet s) (f g : DirectIntegral μ m) :
    restrictSection hs (f + g) = restrictSection hs f + restrictSection hs g := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [section_ae hs (f + g), section_ae hs f, section_ae hs g,
    Lp.coeFn_add f.val g.val, Lp.coeFn_add (restrictSection hs f).val (restrictSection hs g).val]
    with z hfg hf hg ha hb
  change (restrictSection hs (f + g)).val z =
    ((restrictSection hs f).val + (restrictSection hs g).val) z
  rw [hfg, hb]
  simp only [Pi.add_apply]
  rw [hf, hg]
  change (f + g).val z = f.val z + g.val z at ha
  by_cases hz : z ∈ s
  · simpa only [Set.indicator_of_mem hz] using ha
  · simp only [Set.indicator_of_notMem hz, zero_add]

lemma section_smul {s : Set ℂ} (hs : MeasurableSet s) (c : ℂ) (f : DirectIntegral μ m) :
    restrictSection hs (c • f) = c • restrictSection hs f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [section_ae hs (c • f), section_ae hs f,
    Lp.coeFn_smul c f.val, Lp.coeFn_smul c (restrictSection hs f).val]
    with z hcf hf ha hb
  change (restrictSection hs (c • f)).val z = (c • (restrictSection hs f).val) z
  rw [hcf, hb]
  simp only [Pi.smul_apply]
  rw [hf]
  change (c • f).val z = c • f.val z at ha
  by_cases hz : z ∈ s
  · simpa only [Set.indicator_of_mem hz] using ha
  · simp only [Set.indicator_of_notMem hz, smul_zero]

lemma section_norm_le {s : Set ℂ} (hs : MeasurableSet s) (f : DirectIntegral μ m) :
    ‖restrictSection hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [section_ae hs f] with z hz
  change ‖(restrictSection hs f).val z‖ ≤ ‖f.val z‖
  rw [hz]
  by_cases hzs : z ∈ s <;> simp [hzs]

/-- Native indicator multiplication, as a bounded operator on the restrictSection space. -/
def projection {s : Set ℂ} (hs : MeasurableSet s) :
    DirectIntegral μ m →L[ℂ] DirectIntegral μ m :=
  ({ toFun := restrictSection hs
     map_add' := section_add hs
     map_smul' := section_smul hs } :
      DirectIntegral μ m →ₗ[ℂ] DirectIntegral μ m).mkContinuous 1
    (fun f => by simpa using section_norm_le hs f)

lemma inner_section {s : Set ℂ} (hs : MeasurableSet s) (f g : DirectIntegral μ m) :
    ⟪f, restrictSection hs g⟫_ℂ = ∫ z in s, ⟪f.val z, g.val z⟫_ℂ ∂μ := by
  change ⟪f.val, (restrictSection hs g).val⟫_ℂ = _
  rw [L2.inner_def, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [section_ae hs g] with z hz
  rw [hz]
  by_cases hzs : z ∈ s <;> simp [hzs]

lemma intertwines_section (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ n)
    (hT : Spec.IntertwinesScalars T) {s : Set ℂ} (hs : MeasurableSet s)
    (f : DirectIntegral μ m) : T (restrictSection hs f) = restrictSection hs (T f) := by
  apply Subtype.ext
  apply Lp.ext
  have hg : (restrictSection hs f).val =ᵐ[μ]
      fun z => s.indicator (fun _ => (1 : ℂ)) z • f.val z := by
    filter_upwards [section_ae hs f] with z hz
    rw [hz]
    by_cases hzs : z ∈ s <;> simp [hzs]
  have hh := hT (s.indicator (fun _ => (1 : ℂ))) (measurable_const.indicator hs)
    ⟨1, fun z => by by_cases hzs : z ∈ s <;> simp [hzs]⟩ f (restrictSection hs f) hg
  filter_upwards [hh, section_ae hs (T f)] with z hz ht
  rw [hz, ht]
  by_cases hzs : z ∈ s <;> simp [hzs]

/-- Scalar module unitaries preserve inner products pointwise a.e., not only
integrated inner products. The localization tests range over all measurable sets. -/
theorem unitary_inner_ae (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap)
    (f g : DirectIntegral μ m) :
    (fun z => ⟪(U f).val z, (U g).val z⟫_ℂ) =ᵐ[μ]
      fun z => ⟪f.val z, g.val z⟫_ℂ := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (L2.integrable_inner (U f).val (U g).val) (L2.integrable_inner f.val g.val)
  intro s hs _
  have hc := intertwines_section U.toLinearIsometry.toContinuousLinearMap hU hs g
  change U (restrictSection hs g) = restrictSection hs (U g) at hc
  rw [← inner_section hs (U f) (U g), ← inner_section hs f g, ← hc]
  exact U.inner_map_map f (restrictSection hs g)

/-- The inverse intertwines the same scalars; no independent inverse
commutation hypothesis is required. -/
theorem inverse_intertwines (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    Spec.IntertwinesScalars U.symm.toLinearIsometry.toContinuousLinearMap := by
  intro φ hφ hb f g hfg
  -- Move the multiplication graph across U using equality of scalar-module actions.
  obtain ⟨C,hC⟩ := hb
  have hmem : MemLp (fun z => φ z • (U.symm f).val z) 2 μ :=
    (Lp.memLp (U.symm f).val).of_le_mul
      (hφ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (U.symm f).val))
      (c := C) (by
        filter_upwards [] with z
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
  let a : DirectIntegral μ m := ⟨hmem.toLp _, by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [MemLp.coeFn_toLp hmem, (U.symm f).property] with z hz hf
    rw [hz]
    exact (fiber (m z)).smul_mem (φ z) hf⟩
  have ha : a.val =ᵐ[μ] fun z => φ z • (U.symm f).val z := MemLp.coeFn_toLp hmem
  have hUa : U a = g := by
    apply Subtype.ext
    apply Lp.ext
    exact (hU φ hφ ⟨C,hC⟩ (U.symm f) a ha).trans
      (by
        change (fun z => φ z • (U (U.symm f)).val z) =ᵐ[μ] g.val
        simpa only [LinearIsometryEquiv.apply_symm_apply] using hfg.symm)
  have hag : U.symm g = a := by rw [← hUa, U.symm_apply_apply]
  change (U.symm g).val =ᵐ[μ] fun z => φ z • (U.symm f).val z
  rw [hag]
  exact ha

section Finite
variable [IsFiniteMeasure μ]

/-- The active constant kth coordinate section. -/
def coordinateSection (m : Multiplicity μ) (k : ℕ) : DirectIntegral μ m := by
  classical
  exact ⟨indicatorConstLp (E := SequenceSpace) 2 (MultiplicityModel.coordinate_support_measurable m k)
    (measure_ne_top μ _) (lp.single (E := fun _ : ℕ => ℂ) 2 k (1 : ℂ)), by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [indicatorConstLp_coeFn (p := 2)
      (hs := MultiplicityModel.coordinate_support_measurable m k)
      (hμs := measure_ne_top μ _) (c := lp.single (E := fun _ : ℕ => ℂ) 2 k (1 : ℂ))] with z hz
    rw [hz]
    intro j hj
    by_cases hk : (k : ℕ∞) < m z
    · rw [Set.indicator_of_mem (show z ∈ {z | (k : ℕ∞) < m z} from hk), lp.single_apply]
      apply Pi.single_eq_of_ne
      intro h
      subst j
      exact hj hk
    · rw [Set.indicator_of_notMem (show z ∉ {z | (k : ℕ∞) < m z} from hk)]
      rfl⟩

lemma coordinateSection_ae (m : Multiplicity μ) (k : ℕ) :
    (coordinateSection m k).val =ᵐ[μ]
      fun z => if (k : ℕ∞) < m z then lp.single (E := fun _ : ℕ => ℂ) 2 k (1 : ℂ) else 0 := by
  classical
  have h := indicatorConstLp_coeFn (p := 2) (μ := μ)
    (hs := MultiplicityModel.coordinate_support_measurable m k)
    (hμs := measure_ne_top μ _) (c := (lp.single 2 k (1 : ℂ) : SequenceSpace))
  filter_upwards [h] with z hz
  change (indicatorConstLp 2 (MultiplicityModel.coordinate_support_measurable m k)
    (measure_ne_top μ _) (lp.single 2 k (1 : ℂ)) : Lp SequenceSpace 2 μ) z = _
  rw [hz]
  by_cases hk : (k : ℕ∞) < m z
  · rw [Set.indicator_of_mem (show z ∈ {z | (k : ℕ∞) < m z} from hk), ite_eq_left hk]
  · rw [Set.indicator_of_notMem (show z ∉ {z | (k : ℕ∞) < m z} from hk), ite_eq_right hk]

/-- Positivity a.e. makes the zeroth coordinate a faithful scalar test. -/
lemma coordinateSection_zero_ae (m : Multiplicity μ) :
    (coordinateSection m 0).val =ᵐ[μ] fun _ => lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) := by
  filter_upwards [coordinateSection_ae m 0, m.positive] with z hz hp
  simpa [hp] using hz

/-- The native indicator projections have exactly the original measure's
null ideal, including when μ=0. -/
theorem projection_eq_zero_iff {s : Set ℂ} (hs : MeasurableSet s) :
    projection (μ := μ) (m := m) hs = 0 ↔ μ s = 0 := by
  constructor
  · intro h
    have hzero : (restrictSection hs (coordinateSection m 0)).val =ᵐ[μ] fun _ => 0 := by
      have heq : restrictSection hs (coordinateSection m 0) = 0 :=
        congrArg (fun T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m =>
          T (coordinateSection m 0)) h
      rw [heq]
      exact Lp.coeFn_zero _ _ _
    have hn : ∀ᵐ z ∂μ, z ∉ s := by
      filter_upwards [hzero, section_ae hs (coordinateSection m 0),
        coordinateSection_zero_ae m] with z hz hl hc
      intro hzs
      have hh : lp.single (E := fun _ : ℕ => ℂ) 2 0 (1 : ℂ) = (0 : SequenceSpace) := by
        simpa only [hl, Set.indicator_of_mem hzs, hc] using hz
      have hh0 := congrArg (fun x : SequenceSpace => x 0) hh
      simp at hh0
    simpa [ae_iff] using hn
  · intro h
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    apply Lp.ext
    have hn : ∀ᵐ z ∂μ, z ∉ s := by simpa [ae_iff] using h
    filter_upwards [section_ae hs f, hn, Lp.coeFn_zero SequenceSpace 2 μ] with z hz hn h0
    change (restrictSection hs f).val z = (0 : Lp SequenceSpace 2 μ) z
    simp only [hz, Set.indicator_of_notMem hn, h0, Pi.zero_apply]

/-- All countably many column inner-product tests hold on one common conull
set. Inactive columns are zero; active columns are orthonormal. -/
theorem column_inner_ae (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    ∀ᵐ z ∂μ, ∀ j k : ℕ,
      ⟪(U (coordinateSection m j)).val z, (U (coordinateSection m k)).val z⟫_ℂ =
        if j = k ∧ (j : ℕ∞) < m z then 1 else 0 := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  filter_upwards [unitary_inner_ae U hU (coordinateSection m j) (coordinateSection m k),
    coordinateSection_ae m j, coordinateSection_ae m k] with z hz hj hk
  rw [hz, hj, hk]
  by_cases hjz : (j : ℕ∞) < m z <;> by_cases hkz : (k : ℕ∞) < m z
  · simp only [ite_eq_left hjz, ite_eq_left hkz, lp.inner_single_left, lp.single_apply]
    by_cases h : j = k
    · subst k; simp [hjz]
    · simp [h]
  · have hne : j ≠ k := by intro heq; exact hkz (heq ▸ hjz)
    simp [hjz, hkz, hne]
  · simp [hjz, hkz]
  · simp [hjz, hkz]


/-- A pointwise orthonormal family in a finite coordinate fiber has at most
that many active indices. This compares the finite and infinite cases uniformly. -/
theorem dimension_le_of_columns {d e : ℕ∞} (a : ℕ → SequenceSpace)
    (hs : ∀ k, a k ∈ fiber e)
    (hi : ∀ j k, ⟪a j, a k⟫_ℂ = if j = k ∧ (j : ℕ∞) < d then 1 else 0) :
    d ≤ e := by
  classical
  induction e using ENat.recTopCoe with
  | top => exact le_top
  | coe r =>
    by_contra h
    have hrd : (r : ℕ∞) < d := lt_of_not_ge h
    let v : Fin (r+1) → fiber (r : ℕ∞) := fun i => ⟨a i, hs i⟩
    have hv : Orthonormal ℂ v := by
      rw [orthonormal_iff_ite]
      intro i j
      change ⟪a i.val, a j.val⟫_ℂ = _
      rw [hi]
      have hid : (i.val : ℕ∞) < d := lt_of_le_of_lt (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hrd
      simp only [hid, and_true, Fin.ext_iff]
    have hcard := hv.linearIndependent.fintype_card_le_finrank
    rw [Fintype.card_fin, finiteFiber_finrank] at hcard
    omega

/-- Localized inner-product tests alone already force multiplicity equality;
this does not assume a pre-existing measurable fiber field. -/
theorem multiplicity_eq_of_scalar_unitary
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    m.toFun =ᵐ[μ] n.toFun := by
  have hUn := inverse_intertwines U hU
  have hs : ∀ᵐ z ∂μ, ∀ k, (U (coordinateSection m k)).val z ∈ fiber (n z) :=
    ae_all_iff.mpr fun k => (U (coordinateSection m k)).property
  have ht : ∀ᵐ z ∂μ, ∀ k, (U.symm (coordinateSection n k)).val z ∈ fiber (m z) :=
    ae_all_iff.mpr fun k => (U.symm (coordinateSection n k)).property
  filter_upwards [column_inner_ae U hU, column_inner_ae U.symm hUn, hs, ht]
    with z hcol hinv hs ht
  exact le_antisymm
    (dimension_le_of_columns _ hs hcol) (dimension_le_of_columns _ ht hinv)

end Finite
end Localization


namespace Reconstruction
open scoped InnerProductSpace
open ExpandedFA.VonNeumann.MultiplicityUniqueness.Localization FiberBasis
variable {μ : Measure ℂ} [IsFiniteMeasure μ] {m n : Multiplicity μ}

/-- Countably many forward, reverse, and cross-coordinate tests. The cross
tests are essential for proving surjectivity of each fiber map. -/
structure Good (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n) (z : ℂ) : Prop where
  forward_support : ∀ k, (U (coordinateSection m k)).val z ∈ fiber (n z)
  reverse_support : ∀ k, (U.symm (coordinateSection n k)).val z ∈ fiber (m z)
  forward_inner : ∀ j k,
    ⟪(U (coordinateSection m j)).val z, (U (coordinateSection m k)).val z⟫_ℂ =
      if j = k ∧ (j : ℕ∞) < m z then 1 else 0
  reverse_inner : ∀ j k,
    ⟪(U.symm (coordinateSection n j)).val z, (U.symm (coordinateSection n k)).val z⟫_ℂ =
      if j = k ∧ (j : ℕ∞) < n z then 1 else 0
  cross_inner : ∀ j k : ℕ, (j : ℕ∞) < m z → (k : ℕ∞) < n z →
    ⟪(U (coordinateSection m j)).val z, (lp.single 2 k (1 : ℂ) : SequenceSpace)⟫_ℂ =
      ⟪(lp.single 2 j (1 : ℂ) : SequenceSpace), (U.symm (coordinateSection n k)).val z⟫_ℂ

lemma good_ae (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    ∀ᵐ z ∂μ, Good U z := by
  have hs : ∀ᵐ z ∂μ, ∀ k, (U (coordinateSection m k)).val z ∈ fiber (n z) :=
    ae_all_iff.mpr fun k => (U (coordinateSection m k)).property
  have ht : ∀ᵐ z ∂μ, ∀ k, (U.symm (coordinateSection n k)).val z ∈ fiber (m z) :=
    ae_all_iff.mpr fun k => (U.symm (coordinateSection n k)).property
  have hc : ∀ j k : ℕ, ∀ᵐ z ∂μ, (j : ℕ∞) < m z → (k : ℕ∞) < n z →
      ⟪(U (coordinateSection m j)).val z, (lp.single 2 k (1 : ℂ) : SequenceSpace)⟫_ℂ =
        ⟪(lp.single 2 j (1 : ℂ) : SequenceSpace), (U.symm (coordinateSection n k)).val z⟫_ℂ := by
    intro j k
    have hh := unitary_inner_ae U hU (coordinateSection m j) (U.symm (coordinateSection n k))
    simp only [U.apply_symm_apply] at hh
    filter_upwards [hh, coordinateSection_ae m j, coordinateSection_ae n k] with z hz hj hk
    intro hjz hkz
    simpa only [hj, hk, ite_eq_left hjz, ite_eq_left hkz] using hz
  filter_upwards [hs, ht, column_inner_ae U hU,
    column_inner_ae U.symm (inverse_intertwines U hU), ae_all_iff.mpr (fun j => ae_all_iff.mpr (hc j))]
    with z hs ht hf hr hc
  exact ⟨hs,ht,hf,hr,hc⟩

def forward {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ} (h : Good U z) :
    Index (m z) → fiber (n z) := fun i => ⟨(U (coordinateSection m i.val)).val z, h.forward_support i.val⟩

def reverse {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ} (h : Good U z) :
    Index (n z) → fiber (m z) := fun i => ⟨(U.symm (coordinateSection n i.val)).val z, h.reverse_support i.val⟩

lemma forward_orthonormal {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ}
    (h : Good U z) : Orthonormal ℂ (forward h) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪(U (coordinateSection m i.val)).val z, (U (coordinateSection m j.val)).val z⟫_ℂ = _
  rw [h.forward_inner]
  simp only [i.property, and_true, Subtype.ext_iff]

lemma reverse_orthonormal {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ}
    (h : Good U z) : Orthonormal ℂ (reverse h) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪(U.symm (coordinateSection n i.val)).val z, (U.symm (coordinateSection n j.val)).val z⟫_ℂ = _
  rw [h.reverse_inner]
  simp only [i.property, and_true, Subtype.ext_iff]

lemma cross {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ} (h : Good U z)
    (i : Index (m z)) (j : Index (n z)) :
    ⟪forward h i, vector (n z) j⟫_ℂ = ⟪vector (m z) i, reverse h j⟫_ℂ :=
  h.cross_inner i.val j.val i.property j.property

/-- A common conull set is selected before extending any coordinate map.
Off that set the canonical zero extension is defined to be zero. -/
def fieldAt (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n) (z : ℂ) :
    SequenceSpace →L[ℂ] SequenceSpace := by
  classical
  exact if h : Good U z then extension (forward h) (forward_orthonormal h) else 0

lemma fieldAt_good {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ} (h : Good U z) :
    fieldAt U z = extension (forward h) (forward_orthonormal h) := by
  simp only [fieldAt, dite_eq_left h]

lemma fieldAt_unitary {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ} (h : Good U z) :
    Spec.IsFiberUnitary (m z) (n z) (fieldAt U z) := by
  rw [fieldAt_good h]
  exact extension_unitary (forward h) (reverse h) (forward_orthonormal h)
    (reverse_orthonormal h) (cross h)

lemma fieldAt_single {U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n} {z : ℂ}
    (h : Good U z) (k : ℕ) :
    fieldAt U z (lp.single 2 k (1 : ℂ)) = (U (coordinateSection m k)).val z := by
  rw [fieldAt_good h, extension_single]
  by_cases hk : (k : ℕ∞) < m z
  · rw [dite_eq_left hk]; rfl
  · rw [dite_eq_right hk]
    symm
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [hk, and_false, ite_eq_right not_false] using h.forward_inner k k

lemma fieldAt_orbit_measurable (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) (x : SequenceSpace) :
    AEStronglyMeasurable (fun z => fieldAt U z x) μ := by
  have hs (s : Finset ℕ) : AEStronglyMeasurable
      (fun z => ∑ k ∈ s, x k • (U (coordinateSection m k)).val z) μ := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using aestronglyMeasurable_const (b := (0 : SequenceSpace))
    | @insert k s hk ih =>
      simpa only [Finset.sum_insert hk] using
        (show AEStronglyMeasurable (fun z => x k • (U (coordinateSection m k)).val z +
          ∑ j ∈ s, x j • (U (coordinateSection m j)).val z) μ from
          ((Lp.aestronglyMeasurable (U (coordinateSection m k)).val).const_smul (x k)).add ih)
  have hl : ∀ᵐ z ∂μ, Tendsto
      (fun N => ∑ k ∈ Finset.range N, x k • (U (coordinateSection m k)).val z)
      atTop (nhds (fieldAt U z x)) := by
    filter_upwards [good_ae U hU] with z hz
    have hsum := (fieldAt U z).hasSum (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    have heq : (fun k => fieldAt U z (lp.single 2 k (x k))) =
        fun k => x k • (U (coordinateSection m k)).val z := by
      funext k
      have hsingle : (lp.single 2 k (x k) : SequenceSpace) = x k • lp.single 2 k (1 : ℂ) := by
        simpa only [smul_eq_mul, mul_one] using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 k (x k) (1 : ℂ))
      rw [hsingle, map_smul, fieldAt_single hz]
    rw [heq] at hsum
    exact hsum.tendsto_sum_nat
  exact aestronglyMeasurable_of_tendsto_ae atTop (fun N => hs (Finset.range N)) hl

/-- The reconstructed field has strongly measurable constant-vector orbits
and a single exceptional set for all its fiber-unitary laws. -/
def field (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    Spec.UnitaryField μ m n where
  toFun := fieldAt U
  measurable_orbit := fieldAt_orbit_measurable U hU
  unitary := (good_ae U hU).mono fun _ h => fieldAt_unitary h

lemma field_realizes (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hU : Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap) :
    Spec.Realizes U (field U hU) := by
  intro f
  have hh : ∀ k, ∀ᵐ z ∂μ,
      ⟪(U (coordinateSection m k)).val z, (U f).val z⟫_ℂ =
        ⟪(coordinateSection m k).val z, f.val z⟫_ℂ :=
    fun k => unitary_inner_ae U hU (coordinateSection m k) f
  filter_upwards [good_ae U hU, ae_all_iff.mpr hh,
    ae_all_iff.mpr (coordinateSection_ae m), f.property, (U f).property]
    with z hz hh he hf hUf
  let A := columnMap (forward hz) (forward_orthonormal hz)
  obtain ⟨x,hx⟩ := columnMap_surjective (forward hz) (reverse hz)
    (forward_orthonormal hz) (reverse_orthonormal hz) (cross hz) ⟨(U f).val z,hUf⟩
  have hxf : x = (⟨f.val z,hf⟩ : fiber (m z)) := by
    apply FiberBasis.ext
    intro i
    have ht := hh i.val
    rw [he i.val, ite_eq_left i.property] at ht
    have hc := inner_columnMap (forward hz) (forward_orthonormal hz) i x
    rw [hx] at hc
    change ⟪(U (coordinateSection m i.val)).val z, (U f).val z⟫_ℂ = _ at hc
    rw [ht] at hc
    change ⟪vector (m z) i, x⟫_ℂ = ⟪vector (m z) i, ⟨f.val z,hf⟩⟫_ℂ
    change ⟪(lp.single 2 i.val (1 : ℂ) : SequenceSpace), x.val⟫_ℂ =
      ⟪(lp.single 2 i.val (1 : ℂ) : SequenceSpace), f.val z⟫_ℂ
    simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] at hc ⊢
    exact hc.symm
  change (U f).val z = fieldAt U z (f.val z)
  rw [fieldAt_good hz]
  change (U f).val z = extension (forward hz) (forward_orthonormal hz) (⟨f.val z,hf⟩ : fiber (m z)).val
  rw [extension_apply]
  exact (congrArg Subtype.val (hxf ▸ hx)).symm

end Reconstruction

/-- Scalar-intertwining unitaries are actual measurable fiber unitaries. -/
theorem unitary_decomposition : Spec.UnitaryDecomposition := by
  intro μ _ m n U hU
  exact ⟨Reconstruction.field U hU, Reconstruction.field_realizes U hU⟩


/-- Weighted regular-measure approximation transfers continuous coefficient tests
to all measurable sets, even when the two finite control measures differ. -/
lemma continuous_tests_setIntegral {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (p q : X → ℂ) (hp : Integrable p μ) (hq : Integrable q ν)
    (h : ∀ f : C_c(X, ℂ), (∫ x, f x * p x ∂μ) = ∫ x, f x * q x ∂ν) :
    ∀ s, MeasurableSet s → (∫ x in s, p x ∂μ) = ∫ x in s, q x ∂ν := by
  let ρp := μ.withDensity (fun x => (‖p x‖₊ : ℝ≥0∞))
  let ρq := ν.withDensity (fun x => (‖q x‖₊ : ℝ≥0∞))
  let : IsFiniteMeasure ρp := isFiniteMeasure_withDensity hp.2.ne
  let : IsFiniteMeasure ρq := isFiniteMeasure_withDensity hq.2.ne
  let ρ := ρp + ρq
  have heqp (a : X → ℝ) : (∫ x, a x ∂ρp) = ∫ x, ‖p x‖ * a x ∂μ := by
    exact integral_withDensity_eq_integral_smul₀ hp.aestronglyMeasurable.nnnorm.aemeasurable a
  have heqq (a : X → ℝ) : (∫ x, a x ∂ρq) = ∫ x, ‖q x‖ * a x ∂ν := by
    exact integral_withDensity_eq_integral_smul₀ hq.aestronglyMeasurable.nnnorm.aemeasurable a
  intro s hs
  apply eq_of_forall_dist_le
  intro ε hε
  obtain ⟨g, hgnorm, hg⟩ := FunctionSpaces.ScalarRieszMarkov.exists_compactlySupported_indicator_approx
    ρ hs (half_pos hε) (𝕜 := ℂ)
  let f : C(X, ℂ) := g.toContinuousMap
  let a : X → ℝ := fun x => ‖s.indicator (fun _ => (1 : ℂ)) x - f x‖
  have ha_bound : ∀ x, ‖a x‖ ≤ 2 := by
    intro x
    rw [Real.norm_eq_abs, abs_norm]
    apply (norm_sub_le _ _).trans
    have hi : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [hx]
    exact (add_le_add hi (hgnorm x)).trans (by norm_num)
  have ha (τ : Measure X) [IsFiniteMeasure τ] : Integrable a τ := by
    apply Integrable.mono' (integrable_const (2 : ℝ))
      ((measurable_const.indicator hs).sub f.continuous.measurable).norm.aestronglyMeasurable
    exact ae_of_all _ ha_bound
  have hfp : Integrable (fun x => f x * p x) μ :=
    hp.bdd_mul f.continuous.aestronglyMeasurable (by
      filter_upwards [] with x
      exact hgnorm x)
  have hfq : Integrable (fun x => f x * q x) ν :=
    hq.bdd_mul f.continuous.aestronglyMeasurable (by
      filter_upwards [] with x
      exact hgnorm x)
  have hnear (τ : Measure X) [IsFiniteMeasure τ] (r : X → ℂ) (hr : Integrable r τ)
      (hfr : Integrable (fun x => f x * r x) τ) :
      ‖(∫ x in s, r x ∂τ) - ∫ x, f x * r x ∂τ‖ ≤ ∫ x, ‖r x‖ * a x ∂τ := by
    rw [← integral_indicator hs, ← integral_sub (hr.indicator hs) hfr]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards [] with x
    have hi : s.indicator r x = s.indicator (fun _ => (1 : ℂ)) x * r x := by
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hi, ← sub_mul, norm_mul, mul_comm]
  calc
    dist (∫ x in s, p x ∂μ) (∫ x in s, q x ∂ν) ≤
        dist (∫ x in s, p x ∂μ) (∫ x, f x * p x ∂μ) +
        dist (∫ x, f x * q x ∂ν) (∫ x in s, q x ∂ν) := by
      have hf : (∫ x, f x * p x ∂μ) = ∫ x, f x * q x ∂ν := h g
      rw [← hf]
      exact dist_triangle _ _ _
    _ ≤ (∫ x, ‖p x‖ * a x ∂μ) + ∫ x, ‖q x‖ * a x ∂ν := by
      simpa only [dist_eq_norm, norm_sub_rev] using add_le_add
        (hnear μ p hp hfp) (hnear ν q hq hfq)
    _ = ∫ x, a x ∂ρ := by rw [integral_add_measure (ha ρp) (ha ρq), heqp, heqq]
    _ ≤ ε / 2 := hg
    _ ≤ ε := by linarith


open MeasureTheory Filter Set
open Classical
open scoped InnerProductSpace ComplexConjugate
namespace NativeScalar
open ExpandedFA.VonNeumann.MultiplicityModel.Spec
variable {S : Type*} [TopologicalSpace S] [CompactSpace S] [MeasurableSpace S] [BorelSpace S]
variable {μ : Measure ℂ} (m : Multiplicity μ) (q : ℂ → S) (hq : Measurable q)
include hq

lemma mul_memLp (a : C(S, ℂ)) (f : DirectIntegral μ m) :
    MemLp (fun z => a (q z) • f.val z) 2 μ :=
  (Lp.memLp f.val).of_le_mul
    ((a.continuous.measurable.comp hq).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable f.val)) (c := ‖a‖) (by
      filter_upwards [] with z
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm (q z)) (norm_nonneg _))

def mulSection (a : C(S, ℂ)) (f : DirectIntegral μ m) : DirectIntegral μ m :=
  ⟨(mul_memLp m q hq a f).toLp _, by
    change ∀ᵐ z ∂μ, _ ∈ fiber (m z)
    filter_upwards [MemLp.coeFn_toLp (mul_memLp m q hq a f), f.property] with z hz hf
    rw [hz]
    exact (fiber (m z)).smul_mem (a (q z)) hf⟩

lemma mulSection_ae (a : C(S, ℂ)) (f : DirectIntegral μ m) :
    (mulSection m q hq a f).val =ᵐ[μ] fun z => a (q z) • f.val z :=
  MemLp.coeFn_toLp (mul_memLp m q hq a f)

lemma mulSection_norm (a : C(S, ℂ)) (f : DirectIntegral μ m) :
    ‖mulSection m q hq a f‖ ≤ ‖a‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mulSection_ae m q hq a f] with z hz
  change ‖(mulSection m q hq a f).val z‖ ≤ _
  rw [hz, norm_smul]
  exact mul_le_mul_of_nonneg_right (a.norm_coe_le_norm (q z)) (norm_nonneg _)

def mulOperator (a : C(S, ℂ)) : DirectIntegral μ m →L[ℂ] DirectIntegral μ m :=
  ({ toFun := mulSection m q hq a
     map_add' := by
       intro f g
       apply Subtype.ext
       apply Lp.ext
       filter_upwards [mulSection_ae m q hq a (f+g), mulSection_ae m q hq a f,
         mulSection_ae m q hq a g, Lp.coeFn_add f.val g.val,
         Lp.coeFn_add (mulSection m q hq a f).val (mulSection m q hq a g).val]
         with z hfg hf hg hi ho
       change (mulSection m q hq a (f+g)).val z =
         ((mulSection m q hq a f).val + (mulSection m q hq a g).val) z
       rw [ho, hfg]
       simp only [Pi.add_apply]
       rw [hf, hg]
       change (f+g).val z = f.val z + g.val z at hi
       rw [hi, smul_add]
     map_smul' := by
       intro c f
       apply Subtype.ext
       apply Lp.ext
       filter_upwards [mulSection_ae m q hq a (c • f), mulSection_ae m q hq a f,
         Lp.coeFn_smul c f.val, Lp.coeFn_smul c (mulSection m q hq a f).val]
         with z hcf hf hi ho
       change (mulSection m q hq a (c • f)).val z =
         (c • (mulSection m q hq a f).val) z
       rw [ho, hcf]
       simp only [Pi.smul_apply]
       rw [hf]
       change (c • f).val z = c • f.val z at hi
       rw [hi, smul_comm] } :
    DirectIntegral μ m →ₗ[ℂ] DirectIntegral μ m).mkContinuous ‖a‖ (mulSection_norm m q hq a)

lemma mulOperator_ae (a : C(S, ℂ)) (f : DirectIntegral μ m) :
    (mulOperator m q hq a f).val =ᵐ[μ] fun z => a (q z) • f.val z :=
  mulSection_ae m q hq a f

lemma mulOperator_star (a : C(S, ℂ)) :
    mulOperator m q hq (star a) = star (mulOperator m q hq a) := by
  ext f : 1
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  change ⟪g.val, (mulOperator m q hq (star a) f).val⟫_ℂ =
    ⟪(mulOperator m q hq a g).val, f.val⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [mulOperator_ae m q hq (star a) f, mulOperator_ae m q hq a g] with z hf hg
  rw [hf, hg, inner_smul_left, inner_smul_right]
  rfl

def representation : C(S, ℂ) →⋆ₐ[ℂ] (DirectIntegral μ m →L[ℂ] DirectIntegral μ m) where
  toFun := mulOperator m q hq
  map_one' := by
    ext f : 1
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [mulOperator_ae m q hq 1 f] with z hz
    simpa using hz
  map_zero' := by
    ext f : 1
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [mulOperator_ae m q hq 0 f, Lp.coeFn_zero (SequenceSpace) 2 μ] with z hz h0
    change (mulOperator m q hq 0 f).val z = (0 : Lp SequenceSpace 2 μ) z
    rw [h0]
    simpa using hz
  map_add' a b := by
    ext f : 1
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [mulOperator_ae m q hq (a+b) f, mulOperator_ae m q hq a f,
      mulOperator_ae m q hq b f, Lp.coeFn_add (mulOperator m q hq a f).val
        (mulOperator m q hq b f).val] with z hab ha hb ho
    change (mulOperator m q hq (a+b) f).val z =
      ((mulOperator m q hq a f).val + (mulOperator m q hq b f).val) z
    rw [ho, hab]
    simp only [Pi.add_apply]
    rw [ha, hb]
    exact add_smul _ _ _
  map_mul' a b := by
    ext f : 1
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [mulOperator_ae m q hq (a*b) f,
      mulOperator_ae m q hq a (mulOperator m q hq b f), mulOperator_ae m q hq b f]
      with z hab ha hb
    change (mulOperator m q hq (a*b) f).val z =
      (mulOperator m q hq a (mulOperator m q hq b f)).val z
    rw [hab, ha, hb]
    exact mul_smul _ _ _
  commutes' c := by
    ext f : 1
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [mulOperator_ae m q hq (algebraMap ℂ C(S,ℂ) c) f,
      Lp.coeFn_smul c f.val] with z hc hs
    change (mulOperator m q hq (algebraMap ℂ C(S,ℂ) c) f).val z = _
    rw [hc]
    simpa using hs.symm
  map_star' := mulOperator_star m q hq

lemma representation_continuous : Continuous (representation m q hq) := by
  have hb (a : C(S,ℂ)) : ‖representation m q hq a‖ ≤ 1 * ‖a‖ := by
    change ‖mulOperator m q hq a‖ ≤ 1 * ‖a‖
    rw [one_mul]
    exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (mulSection_norm m q hq a)
  exact AddMonoidHomClass.continuous_of_bound (representation m q hq) 1 hb

end NativeScalar

namespace NativeScalar
variable {μ ν : Measure ℂ}
variable {s : Set ℂ} [CompactSpace s]

def retract (s : Set ℂ) (h0 : (0 : ℂ) ∈ s) (z : ℂ) : s :=
  if hz : z ∈ s then ⟨z, hz⟩ else ⟨0, h0⟩

lemma retract_measurable (hs : MeasurableSet s) (h0 : (0 : ℂ) ∈ s) :
    Measurable (retract s h0) := by
  exact (measurable_id : Measurable (fun z : s => z)).dite measurable_const hs

open ExpandedFA.VonNeumann.MultiplicityModel.Spec
lemma representation_coordinate (m : Multiplicity μ) (hμ : BoundedCoordinate μ)
    (hs : MeasurableSet s) (h0 : (0 : ℂ) ∈ s) (hconull : ∀ᵐ z ∂μ, z ∈ s) :
    representation m (retract s h0) (retract_measurable hs h0)
      ((ContinuousMap.id ℂ).restrict s) = coordinateOperatorValue μ m hμ := by
  ext f : 1
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [mulOperator_ae m (retract s h0) (retract_measurable hs h0)
    ((ContinuousMap.id ℂ).restrict s) f, coordinateLpValue_ae hμ f.val, hconull] with z ha hb hz
  change (mulOperator m (retract s h0) (retract_measurable hs h0)
    ((ContinuousMap.id ℂ).restrict s) f).val z = coordinateLpValue hμ f.val z
  rw [ha, hb]
  simp [retract, hz]

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma continuous_intertwining
    (π : C(s, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ρ : C(s, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (hπ : Continuous π) (hρ : Continuous ρ) (T : K →L[ℂ] H)
    (hT : (π ((ContinuousMap.id ℂ).restrict s)).comp T =
      T.comp (ρ ((ContinuousMap.id ℂ).restrict s))) (f : C(s, ℂ)) :
    (π f).comp T = T.comp (ρ f) := by
  let c := (ContinuousMap.id ℂ).restrict s
  have hN : IsStarNormal (π c) := IsStarNormal.map π c
  have hM : IsStarNormal (ρ c) := IsStarNormal.map ρ c
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    rw [show π (ContinuousMap.const s r) = r • 1 from π.commutes r,
      show ρ (ContinuousMap.const s r) = r • 1 from ρ.commutes r]
    ext x
    simp
  | id => exact hT
  | star_id =>
    rw [map_star, map_star]
    exact ExpandedFA.SpectralMeasure.FugledeIntertwining.adjoint_intertwining
      H K (π c) (ρ c) T hN.star_comm_self.eq hM.star_comm_self.eq hT
  | add f g hf hg =>
    rw [map_add, map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, hf, hg]
  | mul f g hf hg =>
    rw [map_mul, map_mul]
    change (π f).comp ((π g).comp T) = (T.comp (ρ f)).comp (ρ g)
    rw [hg, ← ContinuousLinearMap.comp_assoc, hf]
  | frequently f hf =>
    have hc : IsClosed {g : C(s, ℂ) | (π g).comp T = T.comp (ρ g)} :=
      isClosed_eq (hπ.clm_comp continuous_const) (continuous_const.clm_comp hρ)
    exact hc.mem_of_frequently_of_tendsto hf tendsto_id

end NativeScalar


open MultiplicityModel.Spec

namespace SpectralBridge

theorem coefficient_integrals_of_continuous_action
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {m : Multiplicity μ} {n : Multiplicity ν}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral ν n)
    (L : C_c(ℂ, ℂ) → DirectIntegral μ m →L[ℂ] DirectIntegral μ m)
    (R : C_c(ℂ, ℂ) → DirectIntegral ν n →L[ℂ] DirectIntegral ν n)
    (hL : ∀ a f, (L a f).val =ᵐ[μ] fun z => a z • f.val z)
    (hR : ∀ a f, (R a f).val =ᵐ[ν] fun z => a z • f.val z)
    (hU : ∀ a f, U (L a f) = R a (U f)) :
    ∀ (x : DirectIntegral ν n) (f : DirectIntegral μ m)
      (s : Set ℂ), MeasurableSet s →
      (∫ z in s, ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ) =
        ∫ z in s, ⟪x.val z, (U f).val z⟫_ℂ ∂ν := by
  intro x f
  apply continuous_tests_setIntegral μ ν _ _
    (L2.integrable_inner (U.symm x).val f.val)
    (L2.integrable_inner x.val (U f).val)
  intro a
  calc
    (∫ z, a z * ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ) =
        ⟪U.symm x, L a f⟫_ℂ := by
      change _ = ⟪(U.symm x).val, (L a f).val⟫_ℂ
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hL a f] with z hz
      rw [hz, inner_smul_right]
    _ = ⟪x, U (L a f)⟫_ℂ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (U.inner_map_map (U.symm x) (L a f)).symm
    _ = ⟪x, R a (U f)⟫_ℂ := by rw [hU]
    _ = ∫ z, a z * ⟪x.val z, (U f).val z⟫_ℂ ∂ν := by
      change ⟪x.val, (R a (U f)).val⟫_ℂ = _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hR a (U f)] with z hz
      rw [hz, inner_smul_right]

theorem scalar_intertwining_of_coefficient_ae {μ : Measure ℂ} {m n : Multiplicity μ}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hcoef : ∀ (x : DirectIntegral μ n) (f : DirectIntegral μ m),
      (fun z => ⟪x.val z, (U f).val z⟫_ℂ) =ᵐ[μ]
        fun z => ⟪(U.symm x).val z, f.val z⟫_ℂ) :
    Spec.IntertwinesScalars U.toLinearIsometry.toContinuousLinearMap := by
  intro φ hφ hb f g hfg
  obtain ⟨C,hC⟩ := hb
  have hmem : MemLp (fun z => φ z • (U f).val z) 2 μ :=
    (Lp.memLp (U f).val).of_le_mul
      (hφ.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (U f).val))
      (c := C) (by
        filter_upwards [] with z
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
  let a : DirectIntegral μ n := ⟨hmem.toLp _, by
    change ∀ᵐ z ∂μ, _ ∈ fiber (n z)
    filter_upwards [MemLp.coeFn_toLp hmem, (U f).property] with z hz hf
    rw [hz]
    exact (fiber (n z)).smul_mem (φ z) hf⟩
  have ha : a.val =ᵐ[μ] fun z => φ z • (U f).val z := MemLp.coeFn_toLp hmem
  have heq : U g = a := by
    apply ext_inner_left ℂ
    intro x
    calc
      ⟪x, U g⟫_ℂ = ⟪U.symm x, g⟫_ℂ := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          (U.inner_map_map (U.symm x) g)
      _ = ∫ z, φ z * ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ := by
        change ⟪(U.symm x).val, g.val⟫_ℂ = _
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hfg] with z hz
        rw [hz, inner_smul_right]
      _ = ∫ z, φ z * ⟪x.val z, (U f).val z⟫_ℂ ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcoef x f] with z hz
        rw [hz]
      _ = ⟪x, a⟫_ℂ := by
        change _ = ⟪x.val, a.val⟫_ℂ
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ha] with z hz
        rw [hz, inner_smul_right]
  change (U g).val =ᵐ[μ] fun z => φ z • (U f).val z
  rw [heq]
  exact ha

theorem projection_intertwining_of_coefficient_integrals
    {μ ν : Measure ℂ} {m : Multiplicity μ} {n : Multiplicity ν}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral ν n)
    (hsets : ∀ (x : DirectIntegral ν n) (f : DirectIntegral μ m)
      (s : Set ℂ), MeasurableSet s →
      (∫ z in s, ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ) =
        ∫ z in s, ⟪x.val z, (U f).val z⟫_ℂ ∂ν) :
    ∀ (s : Set ℂ) (hs : MeasurableSet s) (f : DirectIntegral μ m),
      U (Localization.restrictSection hs f) = Localization.restrictSection hs (U f) := by
  intro s hs f
  apply ext_inner_left ℂ
  intro x
  calc
    ⟪x, U (Localization.restrictSection hs f)⟫_ℂ =
        ⟪U.symm x, Localization.restrictSection hs f⟫_ℂ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (U.inner_map_map (U.symm x) (Localization.restrictSection hs f))
    _ = ∫ z in s, ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ :=
      Localization.inner_section hs (U.symm x) f
    _ = ∫ z in s, ⟪x.val z, (U f).val z⟫_ℂ ∂ν := hsets x f s hs
    _ = ⟪x, Localization.restrictSection hs (U f)⟫_ℂ :=
      (Localization.inner_section hs x (U f)).symm

theorem coefficient_ae_of_coefficient_integrals
    {μ : Measure ℂ} {m n : Multiplicity μ}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral μ n)
    (hsets : ∀ (x : DirectIntegral μ n) (f : DirectIntegral μ m)
      (s : Set ℂ), MeasurableSet s →
      (∫ z in s, ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ) =
        ∫ z in s, ⟪x.val z, (U f).val z⟫_ℂ ∂μ) :
    ∀ (x : DirectIntegral μ n) (f : DirectIntegral μ m),
      (fun z => ⟪x.val z, (U f).val z⟫_ℂ) =ᵐ[μ]
        fun z => ⟪(U.symm x).val z, f.val z⟫_ℂ := by
  intro x f
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (L2.integrable_inner x.val (U f).val) (L2.integrable_inner (U.symm x).val f.val)
  intro s hs _
  exact (hsets x f s hs).symm

theorem measure_class_of_projection_intertwining
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {m : Multiplicity μ} {n : Multiplicity ν}
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral ν n)
    (hproj : ∀ (s : Set ℂ) (hs : MeasurableSet s) (f : DirectIntegral μ m),
      U (Localization.restrictSection hs f) = Localization.restrictSection hs (U f)) :
    μ ≪ ν ∧ ν ≪ μ := by
  have heq (s : Set ℂ) (hs : MeasurableSet s) : μ s = 0 ↔ ν s = 0 := by
    rw [← Localization.projection_eq_zero_iff (m := m) hs,
      ← Localization.projection_eq_zero_iff (m := n) hs]
    constructor
    · intro h
      apply ContinuousLinearMap.ext
      intro f
      change Localization.restrictSection hs f = 0
      obtain ⟨g, rfl⟩ := U.surjective f
      have hh := hproj s hs g
      have hz : Localization.restrictSection hs g = 0 :=
        congrArg (fun T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m => T g) h
      simpa [hz] using hh.symm
    · intro h
      apply ContinuousLinearMap.ext
      intro f
      change Localization.restrictSection hs f = 0
      apply U.injective
      have hh := hproj s hs f
      have hz : Localization.restrictSection hs (U f) = 0 :=
        congrArg (fun T : DirectIntegral ν n →L[ℂ] DirectIntegral ν n => T (U f)) h
      simpa [hz] using hh
  constructor
  · exact Measure.AbsolutelyContinuous.mk fun s hs hzero => (heq s hs).mpr hzero
  · exact Measure.AbsolutelyContinuous.mk fun s hs hzero => (heq s hs).mp hzero

theorem coefficient_integrals_of_coordinate_intertwining
    {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {m : Multiplicity μ} {n : Multiplicity ν}
    (hμ : BoundedCoordinate μ) (hν : BoundedCoordinate ν)
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] DirectIntegral ν n)
    (hU : ∀ f, U (coordinateOperatorValue μ m hμ f) =
      coordinateOperatorValue ν n hν (U f)) :
    ∀ (x : DirectIntegral ν n) (f : DirectIntegral μ m)
      (s : Set ℂ), MeasurableSet s →
      (∫ z in s, ⟪(U.symm x).val z, f.val z⟫_ℂ ∂μ) =
        ∫ z in s, ⟪x.val z, (U f).val z⟫_ℂ ∂ν := by
  classical
  let r : ℝ := max (hμ.choose : ℝ) (hν.choose : ℝ)
  let s : Set ℂ := Metric.closedBall 0 r
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  letI : CompactSpace s := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) r)
  have h0 : (0 : ℂ) ∈ s := by
    change dist (0 : ℂ) 0 ≤ r
    rw [dist_self]
    exact le_trans hμ.choose.coe_nonneg (le_max_left _ _)
  have hμs : ∀ᵐ z ∂μ, z ∈ s := by
    filter_upwards [hμ.choose_spec] with z hz
    change dist z 0 ≤ r
    rw [dist_zero_right]
    exact hz.trans (le_max_left _ _)
  have hνs : ∀ᵐ z ∂ν, z ∈ s := by
    filter_upwards [hν.choose_spec] with z hz
    change dist z 0 ≤ r
    rw [dist_zero_right]
    exact hz.trans (le_max_right _ _)
  let q := NativeScalar.retract s h0
  have hq : Measurable q := NativeScalar.retract_measurable hs h0
  let ρ := NativeScalar.representation m q hq
  let π := NativeScalar.representation n q hq
  have hcρ : ρ ((ContinuousMap.id ℂ).restrict s) = coordinateOperatorValue μ m hμ :=
    NativeScalar.representation_coordinate m hμ hs h0 hμs
  have hcπ : π ((ContinuousMap.id ℂ).restrict s) = coordinateOperatorValue ν n hν :=
    NativeScalar.representation_coordinate n hν hs h0 hνs
  have hT : (π ((ContinuousMap.id ℂ).restrict s)).comp
      U.toLinearIsometry.toContinuousLinearMap =
      U.toLinearIsometry.toContinuousLinearMap.comp (ρ ((ContinuousMap.id ℂ).restrict s)) := by
    rw [hcπ, hcρ]
    apply ContinuousLinearMap.ext
    intro f
    exact (hU f).symm
  let L : C_c(ℂ, ℂ) → DirectIntegral μ m →L[ℂ] DirectIntegral μ m :=
    fun a => ρ (a.toContinuousMap.restrict s)
  let R : C_c(ℂ, ℂ) → DirectIntegral ν n →L[ℂ] DirectIntegral ν n :=
    fun a => π (a.toContinuousMap.restrict s)
  apply coefficient_integrals_of_continuous_action U L R
  · intro a f
    filter_upwards [NativeScalar.mulOperator_ae m q hq (a.toContinuousMap.restrict s) f,
      hμs] with z hz hzs
    change (NativeScalar.mulOperator m q hq (a.toContinuousMap.restrict s) f).val z = _
    rw [hz]
    simp [q, NativeScalar.retract, hzs]
  · intro a f
    filter_upwards [NativeScalar.mulOperator_ae n q hq (a.toContinuousMap.restrict s) f,
      hνs] with z hz hzs
    change (NativeScalar.mulOperator n q hq (a.toContinuousMap.restrict s) f).val z = _
    rw [hz]
    simp [q, NativeScalar.retract, hzs]
  · intro a f
    have hh := NativeScalar.continuous_intertwining π ρ
      (NativeScalar.representation_continuous n q hq)
      (NativeScalar.representation_continuous m q hq)
      U.toLinearIsometry.toContinuousLinearMap hT (a.toContinuousMap.restrict s)
    exact (congrArg (fun T : DirectIntegral μ m →L[ℂ] DirectIntegral ν n => T f) hh).symm

end SpectralBridge

/-- Native coordinate intertwining preserves the original control measure class. -/
theorem measure_class_invariant : Spec.MeasureClassInvariant := by
  intro μ ν _ _ m n hμ hν h
  obtain ⟨U, hU⟩ := h
  exact SpectralBridge.measure_class_of_projection_intertwining U
    (SpectralBridge.projection_intertwining_of_coefficient_integrals U
      (SpectralBridge.coefficient_integrals_of_coordinate_intertwining hμ hν U hU))

/-- Fuglede and continuous coefficient uniqueness give every bounded Borel scalar action. -/
theorem coordinate_scalar_intertwining : Spec.CoordinateScalarIntertwining := by
  intro μ _ m n hμ hν U hU
  exact SpectralBridge.scalar_intertwining_of_coefficient_ae U
    (SpectralBridge.coefficient_ae_of_coefficient_integrals U
      (SpectralBridge.coefficient_integrals_of_coordinate_intertwining hμ hν U hU))



/-- Two bounded native normal-coordinate models are unitarily equivalent exactly
when their finite measure classes and almost-everywhere multiplicities agree. -/
theorem classification : Spec.Classification :=
  classification_from_bridges measure_class_invariant coordinate_scalar_intertwining
    unitary_decomposition

end ExpandedFA.VonNeumann.MultiplicityUniqueness
