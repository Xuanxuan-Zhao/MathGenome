import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Orientations.Equivalences
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Tangent.Bundle
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch07.ExteriorAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! M09.01: intrinsic determinant rays, signed coordinates, and positive top forms.
The final declarations use the proved exterior-algebra interface.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Topology

namespace SmoothManifolds.OrientationResults
open ModelData AtlasData TangentData TangentBundleData OrientationData
  FrameData MapData Set Module Filter
universe u v w

/-- Positivity on a ray is exactly strict positive rescaling of any generator. -/
theorem positive_iff_pos_smul {V : Type v} [AddCommGroup V] [Module ℝ V]
    (x : V) (hx : x ≠ 0) (y : V) :
    IsPositive (rayOfNeZero ℝ x hx) y ↔ ∃ t : ℝ, 0 < t ∧ y = t • x := by
  constructor
  · rintro ⟨hy, h⟩
    exact ((ray_eq_iff hy hx).mp h).exists_pos_right hy hx
  · rintro ⟨t, ht, rfl⟩
    exact ⟨smul_ne_zero ht.ne' hx, ray_pos_smul hx ht _⟩

/-- A real line has exactly two rays, irrespective of its presentation. -/
theorem ray_eq_or_neg_of_finrank_one {V : Type v} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 1)
    (r s : Module.Ray ℝ V) : r = s ∨ r = -s := by
  induction r using Module.Ray.ind with | h x hx =>
  induction s using Module.Ray.ind with | h y hy =>
  have hnot : ¬LinearIndependent ℝ ![x, y] := by
    intro h
    have hcard := h.fintype_card_le_finrank
    simp [hV] at hcard
  rcases sameRay_or_sameRay_neg_iff_not_linearIndependent.mpr hnot with h | h
  · exact Or.inl ((ray_eq_iff hx hy).mpr h)
  · exact Or.inr (by rw [neg_rayOfNeZero, ray_eq_iff]; exact h)

/-- The intrinsic determinant fibers have rank one even when n = 0. -/
theorem determinant_finrank {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (p : M) :
    Module.finrank ℝ (DeterminantLine S p) = 1 := by
  letI := (tangent_dimension S p).1
  letI : Module.Free ℝ (TangentData.TangentSpace S p) :=
    @Module.Free.of_divisionRing ℝ (TangentData.TangentSpace S p) _ _ _
  exact (exteriorPower.finrank_eq ℝ (TangentData.TangentSpace S p) n).trans
    (by rw [(tangent_dimension S p).2, Nat.choose_self])

theorem determinant_ray_eq_or_neg {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (p : M)
    (r s : DeterminantRay S p) : r = s ∨ r = -s := by
  letI := (tangent_dimension S p).1
  exact ray_eq_or_neg_of_finrank_one (determinant_finrank S p) r s

/-- Negating a ray field preserves continuity in every determinant chart. -/
theorem continuous_neg {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} {r : RayField S} (hr : IsContinuousRayField r) :
    IsContinuousRayField (fun p => -r p) := by
  intro K c hc
  have h := (hr K c hc).comp (fun x => -x)
  convert h using 1
  funext p
  exact Module.Ray.map_neg (determinantCoordinates K c hc p) (r p.val)

def opposite {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o : Orientation S) : Orientation S :=
  ⟨fun p => -o.val p, continuous_neg o.property⟩

@[simp] theorem opposite_apply {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (o : Orientation S) (p : M) :
    (opposite o).val p = -o.val p := rfl

/-- Comparison in a single chart is comparison of two locally constant maps
into the same fixed two-point ray space. -/
theorem comparison_on_chart {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (o q : Orientation S)
    (K : FiberCoordinates S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    IsLocallyConstant (fun p : c.source => comparison o q p.val) := by
  have h := ((o.property K c hc).prodMk (q.property K c hc)).comp
    (fun z => if z.1 = z.2 then true else false)
  convert h using 1
  funext p
  simp only [Function.comp_apply, comparison]
  congr 1
  exact propext (Module.Ray.map (determinantCoordinates K c hc p)).injective.eq_iff.symm

/-- Global comparison is locally constant, using any chart about a point. -/
theorem comparison_locallyConstant {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (o q : Orientation S) :
    IsLocallyConstant (comparison o q) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro p
  obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  obtain ⟨V, hV, hpV, hconst⟩ :=
    (comparison_on_chart o q K c hc).exists_open ⟨p, hp⟩
  refine ⟨Subtype.val '' V, c.open_source.isOpenMap_subtype_val V hV,
    ⟨⟨p, hp⟩, hpV, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact hconst z hz

/-- The comparison sign reconstructs the second orientation pointwise. -/
theorem comparison_reconstruct {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (o q : Orientation S) (p : M) :
    q.val p = if comparison o q p then o.val p else -o.val p := by
  by_cases h : o.val p = q.val p
  · simp [comparison, h]
  · simp only [comparison, if_neg h, Bool.false_eq_true, ↓reduceIte]
    exact (determinant_ray_eq_or_neg S p (q.val p) (o.val p)).resolve_left (Ne.symm h)



/-- A specified positive ray identifies the two rays of a line with signs. -/
def raySignEquiv {V : Type v} [AddCommGroup V] [Module ℝ V]
    (r : Module.Ray ℝ V) (h : ∀ s, s = r ∨ s = -r) : Bool ≃ Module.Ray ℝ V where
  toFun b := if b then r else -r
  invFun s := if s = r then true else false
  left_inv b := by
    cases b <;> simp [Ne.symm (Module.Ray.ne_neg_self r)]
  right_inv s := by
    rcases h s with hs | hs
    · simp [hs]
    · simp [hs, Ne.symm (Module.Ray.ne_neg_self r)]

/-- Any ray field on a discrete manifold is continuous. -/
theorem continuous_of_discrete {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] [DiscreteTopology M] {S : SmoothManifold n a M}
    (r : RayField S) : IsContinuousRayField r := by
  intro K c hc
  exact IsLocallyConstant.of_discrete _

/-- The zeroth exterior power supplies the reference ray 1, not a demand that
an empty coordinate frame represent either choice of orientation. -/
def zeroRayEquiv {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (p : M) : Bool ≃ DeterminantRay S p :=
  let z := exteriorPower.zeroEquiv ℝ (TangentData.TangentSpace S p)
  let x := z.symm 1
  let hx : x ≠ 0 := z.symm.map_ne_zero_iff.mpr one_ne_zero
  raySignEquiv (rayOfNeZero ℝ x hx)
    (fun s => determinant_ray_eq_or_neg S p s (rayOfNeZero ℝ x hx))

@[simp] theorem zeroRayEquiv_true {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 a M) (p : M) :
    IsPositive (zeroRayEquiv S p true)
      ((exteriorPower.zeroEquiv ℝ (TangentData.TangentSpace S p)).symm 1) := by
  exact ⟨_, rfl⟩

/-- The two existing scalar smoothness interfaces have identical local
ambient extension data. -/
theorem vectorSmooth_scalar_iff {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (f : M → ℝ) :
    FrameData.VectorSmooth A f ↔ PartitionData.ScalarSmooth A f := by
  exact forall_congr' (fun p => (scalarContDiffAt_iff (⊤ : ℕ∞) A f p).symm)

/-- Positive smooth rescaling is already an equivalence relation before using
the orientation/top-form correspondence. -/
theorem positiveMultiple_equivalence {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    {C : BundleOperationsData.CotangentBundle S} {D : ExteriorData.FormBundle C n} :
    Equivalence (@PositiveMultiple n a M _ S C D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α
    refine ⟨fun _ => 1, ?_, fun _ => zero_lt_one, ?_⟩
    · exact (vectorSmooth_scalar_iff _ _).mpr
        (scalarContDiff_const (⊤ : ℕ∞) S.smoothStructure.val 1)
    · intro p
      exact (one_smul ℝ (α.val.field p)).symm
  · intro α β h
    obtain ⟨f, hf, hpos, heq⟩ := h
    refine ⟨fun p => (f p)⁻¹, ?_, fun p => inv_pos.mpr (hpos p), ?_⟩
    · exact (vectorSmooth_scalar_iff _ _).mpr
        (scalarContDiff_inv ((vectorSmooth_scalar_iff _ _).mp hf)
          (fun p => (hpos p).ne'))
    · intro p
      rw [heq p, inv_smul_smul₀ (hpos p).ne']
  · intro α β γ hαβ hβγ
    obtain ⟨f, hf, hposf, hαβ⟩ := hαβ
    obtain ⟨g, hg, hposg, hβγ⟩ := hβγ
    refine ⟨fun p => g p * f p, ?_, fun p => mul_pos (hposg p) (hposf p), ?_⟩
    · exact (vectorSmooth_scalar_iff _ _).mpr
        (scalarContDiff_mul ((vectorSmooth_scalar_iff _ _).mp hg)
          ((vectorSmooth_scalar_iff _ _).mp hf))
    · intro p
      rw [hβγ p, hαβ p, mul_smul]

/-- Positive-overlap generators determine a unique pointwise ray field.
Continuity of this ray field is proved below using the local smoothness test. -/
theorem generators_ray_exists_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (G : LocalGenerators S) :
    ∃! r : RayField S, RepresentsGenerators r G := by
  let idx (p : M) := Classical.choose (G.cover p)
  have hidx (p : M) : p ∈ G.domain (idx p) := Classical.choose_spec (G.cover p)
  let r : RayField S := fun p => rayOfNeZero ℝ
    (G.generator (idx p) ⟨p, hidx p⟩) (G.nonzero (idx p) ⟨p, hidx p⟩)
  refine ⟨r, ?_, ?_⟩
  · intro i p
    obtain ⟨f, _, heq⟩ := G.overlap (idx p.val) i
    obtain ⟨hpos, heq⟩ := heq ⟨p.val, hidx p.val, p.property⟩
    refine ⟨G.nonzero i p, ?_⟩
    dsimp only [r]
    apply (ray_eq_iff _ _).mpr
    rw [heq]
    exact SameRay.sameRay_pos_smul_left _ hpos
  · intro s hs
    funext p
    exact (hs (idx p) ⟨p, hidx p⟩).choose_spec.symm

/-- The coordinate wedge has determinant coefficient one, including in degree zero. -/
theorem coefficient_coordinateVector {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    determinantCoefficient K c hc p (coordinateVector K c hc p) = 1 := by
  unfold determinantCoefficient coordinateVector
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact Basis.det_self _

theorem coordinateVector_ne_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    coordinateVector K c hc p ≠ 0 := by
  intro h
  have h1 := coefficient_coordinateVector K c hc p
  rw [h, map_zero] at h1
  exact zero_ne_one h1

/-- A determinant coefficient is the actual scalar relative to its coordinate wedge. -/
theorem determinant_eq_coefficient_smul {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (v : DeterminantLine S p.val) :
    v = determinantCoefficient K c hc p v • coordinateVector K c hc p := by
  letI := (tangent_dimension S p.val).1
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero'
    (coordinateVector K c hc p) (coordinateVector_ne_zero K c hc p)).mp
      (determinant_finrank S p.val) v
  rw [← ht, map_smul, coefficient_coordinateVector, smul_eq_mul, mul_one]

theorem determinantCoefficient_ne_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (v : DeterminantLine S p.val) (hv : v ≠ 0) :
    determinantCoefficient K c hc p v ≠ 0 := by
  intro h
  apply hv
  rw [determinant_eq_coefficient_smul K c hc p v, h, zero_smul]

/-- Coordinate transport of the coordinate wedge is independent of the base point. -/
theorem determinantCoordinates_coordinateVector {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    determinantCoordinates K c hc p (coordinateVector K c hc p) =
      exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n)) := by
  change exteriorPower.map n _ (exteriorPower.ιMulti ℝ n _) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  exact LinearEquiv.apply_symm_apply _ _

/-- On a real line, the ray of a nonzero continuous scalar multiple is locally constant. -/
theorem locallyConstant_ray_smul {X : Type*} [TopologicalSpace X]
    {V : Type v} [AddCommGroup V] [Module ℝ V] (v : V) (hv : v ≠ 0)
    (f : X → ℝ) (hf : Continuous f) (hn : ∀ x, f x ≠ 0) :
    IsLocallyConstant (fun x => rayOfNeZero ℝ (f x • v) (smul_ne_zero (hn x) hv)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  rcases lt_or_gt_of_ne (hn x) with hx | hx
  · have he : ∀ᶠ y in 𝓝 x, f y < 0 := (hf.continuousAt).eventually (gt_mem_nhds hx)
    have hneg (y : X) (hy : f y < 0) :
        rayOfNeZero ℝ (f y • v) (smul_ne_zero (hn y) hv) = rayOfNeZero ℝ (-v) (neg_ne_zero.mpr hv) := by
      apply (ray_eq_iff _ _).mpr
      have hs := SameRay.sameRay_pos_smul_left (R := ℝ) (a := -(f y)) (-v) (neg_pos.mpr hy)
      simpa using hs
    filter_upwards [he] with y hy
    exact (hneg y hy).trans (hneg x hx).symm
  · have he : ∀ᶠ y in 𝓝 x, 0 < f y := (hf.continuousAt).eventually (lt_mem_nhds hx)
    filter_upwards [he] with y hy
    exact (ray_pos_smul hv hy _).trans (ray_pos_smul hv hx _).symm

/-- Local constancy can be checked on an arbitrary open cover. -/
theorem locallyConstant_of_open_cover {X : Type*} [TopologicalSpace X] {Y : Type*}
    {ι : Type*} (f : X → Y) (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (hf : ∀ i, IsLocallyConstant (fun x : U i => f x.val)) : IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨i, hi⟩ := hcover x
  obtain ⟨V, hV, hxV, he⟩ := (hf i).exists_open ⟨x, hi⟩
  refine ⟨Subtype.val '' V, (hU i).isOpenMap_subtype_val V hV, ⟨⟨x, hi⟩, hxV, rfl⟩, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact he z hz

theorem standardDeterminantVector_ne_zero (n : ℕ) :
    exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n)) ≠ 0 := by
  intro h
  have he : exteriorPower.alternatingMapLinearEquiv (Pi.basisFun ℝ (Fin n)).det
      (exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n))) = 1 := by
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact Basis.det_self _
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- A smooth nonzero determinant section gives locally constant rays in every chart. -/
theorem smooth_section_ray_locallyConstant {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (U : Set M) (hU : IsOpen U)
    (g : (p : U) → DeterminantLine S p.val) (hg : ∀ p, g p ≠ 0)
    (hs : IsSmoothDeterminantSection U hU g) (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    IsLocallyConstant (fun p : ↥(U ∩ c.source) =>
      Module.Ray.map (determinantCoordinates K c hc ⟨p.val, p.property.2⟩)
        (rayOfNeZero ℝ (g ⟨p.val, p.property.1⟩) (hg _))) := by
  let f : ↥(U ∩ c.source) → ℝ := fun p =>
    determinantCoefficient K c hc ⟨p.val, p.property.2⟩ (g ⟨p.val, p.property.1⟩)
  have hn : ∀ p, f p ≠ 0 := fun p => determinantCoefficient_ne_zero K c hc _ _ (hg _)
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun p => (hs K c hc p).1)
  have h := locallyConstant_ray_smul _ (standardDeterminantVector_ne_zero n) f hf hn
  have he : (fun p : ↥(U ∩ c.source) =>
      Module.Ray.map (determinantCoordinates K c hc ⟨p.val, p.property.2⟩)
        (rayOfNeZero ℝ (g ⟨p.val, p.property.1⟩) (hg _))) =
      (fun p => rayOfNeZero ℝ (f p • exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n)))
        (smul_ne_zero (hn p) (standardDeterminantVector_ne_zero n))) := by
    funext p
    rw [Module.Ray.map_apply]
    have hev := congrArg (determinantCoordinates K c hc ⟨p.val, p.property.2⟩)
      (determinant_eq_coefficient_smul K c hc ⟨p.val, p.property.2⟩
        (g ⟨p.val, p.property.1⟩))
    simp only [map_smul, determinantCoordinates_coordinateVector] at hev
    exact (ray_eq_iff _ _).mpr (hev ▸ SameRay.rfl)
  rw [he]
  exact h

/-- Smooth positive-overlap generators produce a continuous intrinsic ray field. -/
theorem continuous_of_represents_generators {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (r : RayField S)
    (G : LocalGenerators S) (hr : RepresentsGenerators r G) : IsContinuousRayField r := by
  intro K c hc
  apply locallyConstant_of_open_cover _ (fun i => {p : c.source | p.val ∈ G.domain i})
    (fun i => (G.isOpen_domain i).preimage continuous_subtype_val)
    (fun p => G.cover p.val)
  intro i
  have h := smooth_section_ray_locallyConstant (G.domain i) (G.isOpen_domain i)
    (G.generator i) (G.nonzero i) (G.smooth i) K c hc
  let incl : {p : c.source | p.val ∈ G.domain i} → ↥(G.domain i ∩ c.source) :=
    fun p => ⟨p.val.val, p.property, p.val.property⟩
  have hi : Continuous incl := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : (fun p : {p : c.source | p.val ∈ G.domain i} =>
      Module.Ray.map (determinantCoordinates K c hc p.val) (r p.val.val)) =
      (fun p => Module.Ray.map
        (determinantCoordinates K c hc ⟨p.val.val, p.val.property⟩)
        (rayOfNeZero ℝ (G.generator i ⟨p.val.val, p.property⟩) (G.nonzero i _))) := by
    funext p
    exact congrArg (Module.Ray.map (determinantCoordinates K c hc p.val))
      (hr i ⟨p.val.val, p.property⟩).choose_spec.symm
  rw [he]
  have hfin := h.comp_continuous (f := incl) hi
  exact hfin

theorem coefficient_coordinateVector_transition {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) :
    determinantCoefficient K d hd ⟨p.val, p.property.2⟩
      (coordinateVector K c hc ⟨p.val, p.property.1⟩) = transitionDeterminant K c d hc hd p := by
  unfold determinantCoefficient coordinateVector transitionDeterminant
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Basis.det_apply,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n))]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply]


theorem coordinateVector_independent {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K L : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    coordinateVector K c hc p = coordinateVector L c hc p := by
  unfold coordinateVector
  rw [TangentBundle.chartCoordinates_unique (K.isCoordinates c hc p.val p.property)
    (L.isCoordinates c hc p.val p.property)]

theorem signValue_ne_zero (b : Bool) : signValue b ≠ 0 := by
  cases b <;> norm_num [signValue]

theorem signed_coordinateVector_ne_zero {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) (b : Bool) :
    signValue b • coordinateVector K c hc p ≠ 0 :=
  smul_ne_zero (signValue_ne_zero b) (coordinateVector_ne_zero K c hc p)

/-- The two signed multiples of a coordinate wedge parametrize its two rays. -/
def coordinateRayEquiv {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    Bool ≃ DeterminantRay S p.val :=
  raySignEquiv (rayOfNeZero ℝ (coordinateVector K c hc p) (coordinateVector_ne_zero K c hc p))
    (fun s => determinant_ray_eq_or_neg S p.val s _)

@[simp] theorem coordinateRayEquiv_apply {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) (b : Bool) :
    coordinateRayEquiv K c hc p b = rayOfNeZero ℝ
      (signValue b • coordinateVector K c hc p) (signed_coordinateVector_ne_zero K c hc p b) := by
  cases b
  · change -rayOfNeZero ℝ (coordinateVector K c hc p) _ = _
    rw [neg_rayOfNeZero]
    apply (ray_eq_iff _ _).mpr
    have he : signValue false • coordinateVector K c hc p = -coordinateVector K c hc p := by
      change (-1 : ℝ) • coordinateVector K c hc p = _
      exact neg_one_smul ℝ (coordinateVector K c hc p)
    rw [he]
    exact SameRay.rfl
  · change rayOfNeZero ℝ (coordinateVector K c hc p) _ = _
    apply (ray_eq_iff _ _).mpr
    have he : signValue true • coordinateVector K c hc p = coordinateVector K c hc p := by
      exact one_smul ℝ _
    rw [he]

/-- Signs of an intrinsic ray field relative to a chosen coordinate system. -/
def chartSign {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (r : RayField S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : Bool := (coordinateRayEquiv K c hc p).symm (r p.val)

theorem chartSign_represents {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K L : FiberCoordinates S)
    (r : RayField S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    IsPositive (r p.val) (signValue (chartSign K r c hc p) • coordinateVector L c hc p) := by
  rw [← coordinateVector_independent K L]
  refine ⟨signed_coordinateVector_ne_zero _ _ _ _ _, ?_⟩
  rw [← coordinateRayEquiv_apply]
  exact (coordinateRayEquiv K c hc p).apply_symm_apply _

/-- Standard coordinate rays identify transported rays with a fixed sign set. -/
def standardRayEquiv (n : ℕ) : Bool ≃ Module.Ray ℝ (⋀[ℝ]^n (Euclidean n)) :=
  raySignEquiv (rayOfNeZero ℝ (exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n)))
    (standardDeterminantVector_ne_zero n)) (by
      intro s
      letI : Module.Free ℝ (Euclidean n) := Module.Free.of_divisionRing ℝ (Euclidean n)
      apply ray_eq_or_neg_of_finrank_one _ s _
      rw [exteriorPower.finrank_eq, Module.finrank_pi, Fintype.card_fin, Nat.choose_self])

theorem map_coordinateRayEquiv {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) (b : Bool) :
    Module.Ray.map (determinantCoordinates K c hc p) (coordinateRayEquiv K c hc p b) =
      standardRayEquiv n b := by
  cases b <;> simp [coordinateRayEquiv, standardRayEquiv, raySignEquiv,
    Module.Ray.map_apply, Module.Ray.map_neg, determinantCoordinates_coordinateVector]

theorem chartSign_locallyConstant {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (r : RayField S) (hr : IsContinuousRayField r)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    IsLocallyConstant (chartSign K r c hc) := by
  have h := (hr K c hc).comp (standardRayEquiv n).symm
  convert h using 1
  funext p
  apply (standardRayEquiv n).injective
  dsimp only [Function.comp_apply]
  rw [Equiv.apply_symm_apply, ← map_coordinateRayEquiv K c hc p]
  congr 1
  exact (coordinateRayEquiv K c hc p).apply_symm_apply _

theorem continuous_of_signed_representation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (r : RayField S)
    (s : SignedCharts S) (h : RepresentsSignedCharts r s) : IsContinuousRayField r := by
  intro K c hc
  have he : (fun p : c.source => Module.Ray.map (determinantCoordinates K c hc p) (r p.val)) =
      (fun p => standardRayEquiv n (s.sign c hc p)) := by
    funext p
    rw [← map_coordinateRayEquiv K c hc p]
    congr 1
    rw [coordinateRayEquiv_apply]
    exact (h K c hc p).choose_spec.symm
  rw [he]
  exact (s.locallyConstant c hc).comp (standardRayEquiv n)

theorem signed_representation_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (r : RayField S)
    (s t : SignedCharts S) (hs : RepresentsSignedCharts r s) (ht : RepresentsSignedCharts r t) :
    s = t := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  have he : s.sign = t.sign := by
    funext c hc p
    apply (coordinateRayEquiv K c hc p).injective
    simp only [coordinateRayEquiv_apply]
    exact (hs K c hc p).choose_spec.trans (ht K c hc p).choose_spec.symm
  cases s
  cases t
  cases he
  rfl

theorem scalar_sign_compatibility_iff (δ : ℝ) (hδ : δ ≠ 0) (sc sd : Bool) :
    signValue sd = signValue sc * SignType.sign δ ↔
      0 < signValue sc * δ * signValue sd := by
  rcases lt_or_gt_of_ne hδ with hδ | hδ
  · cases sc <;> cases sd <;> simp [signValue, sign_neg hδ, hδ, hδ.not_gt, le_of_lt hδ] <;> norm_num
  · cases sc <;> cases sd <;> simp [signValue, sign_pos hδ, hδ, hδ.not_gt, le_of_lt hδ] <;> norm_num

theorem signed_scalar_sameRay_iff {V : Type v} [AddCommGroup V] [Module ℝ V]
    (y : V) (hy : y ≠ 0) (δ : ℝ) (hδ : δ ≠ 0) (sc sd : Bool) :
    SameRay ℝ (signValue sc • (δ • y)) (signValue sd • y) ↔
      signValue sd = signValue sc * SignType.sign δ := by
  rw [scalar_sign_compatibility_iff δ hδ]
  have he : signValue sc • (δ • y) =
      (signValue sc * δ * signValue sd) • (signValue sd • y) := by
    cases sc <;> cases sd <;> simp [signValue, smul_smul, mul_assoc, neg_smul]
  rw [he, sameRay_smul_left_iff_of_ne
    (smul_ne_zero (signValue_ne_zero sd) hy)
    (mul_ne_zero (mul_ne_zero (signValue_ne_zero sc) hδ) (signValue_ne_zero sd))]

theorem signed_coordinate_rays_eq_iff {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) (sc sd : Bool) :
    rayOfNeZero ℝ (signValue sc • coordinateVector K c hc ⟨p.val, p.property.1⟩)
        (smul_ne_zero (signValue_ne_zero sc) (coordinateVector_ne_zero K c hc _)) =
      rayOfNeZero ℝ (signValue sd • coordinateVector K d hd ⟨p.val, p.property.2⟩)
        (smul_ne_zero (signValue_ne_zero sd) (coordinateVector_ne_zero K d hd _)) ↔
      signValue sd = signValue sc * SignType.sign (transitionDeterminant K c d hc hd p) := by
  let x := coordinateVector K c hc ⟨p.val, p.property.1⟩
  let y := coordinateVector K d hd ⟨p.val, p.property.2⟩
  let δ := transitionDeterminant K c d hc hd p
  have htrans : determinantCoefficient K d hd ⟨p.val, p.property.2⟩ x = δ :=
    coefficient_coordinateVector_transition K c d hc hd p
  have hδ : δ ≠ 0 := by
    rw [← htrans]
    exact determinantCoefficient_ne_zero K d hd _ _ (coordinateVector_ne_zero K c hc _)
  have hxy : x = δ • y := by
    exact (determinant_eq_coefficient_smul K d hd ⟨p.val, p.property.2⟩ x).trans
      (congrArg (fun z => z • y) htrans)
  rw [ray_eq_iff]
  change SameRay ℝ (signValue sc • x) (signValue sd • y) ↔
    signValue sd = signValue sc * SignType.sign δ
  rw [hxy]
  exact signed_scalar_sameRay_iff y (coordinateVector_ne_zero K d hd _) δ hδ sc sd

/-- Compatible signed-coordinate rays glue pointwise, independently of coordinates. -/
theorem signed_charts_ray_exists_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (s : SignedCharts S) :
    ∃! r : RayField S, RepresentsSignedCharts r s := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  choose c hc hp using S.smoothStructure.property.1.1
  let r : RayField S := fun p => rayOfNeZero ℝ
    (signValue (s.sign (c p) (hc p) ⟨p, hp p⟩) • coordinateVector K (c p) (hc p) ⟨p, hp p⟩)
    (signed_coordinateVector_ne_zero K (c p) (hc p) ⟨p, hp p⟩ _)
  have hr : RepresentsSignedCharts r s := by
    intro L d hd p
    rw [← coordinateVector_independent K L]
    refine ⟨signed_coordinateVector_ne_zero K d hd p _, ?_⟩
    have h := (signed_coordinate_rays_eq_iff K (c p.val) d (hc p.val) hd
      ⟨p.val, hp p.val, p.property⟩
      (s.sign (c p.val) (hc p.val) ⟨p.val, hp p.val⟩) (s.sign d hd p)).mpr
      (s.compatible K (c p.val) d (hc p.val) hd ⟨p.val, hp p.val, p.property⟩)
    exact h.symm
  refine ⟨r, hr, ?_⟩
  intro r' hr'
  funext p
  exact ((hr' K (c p) (hc p) ⟨p, hp p⟩).choose_spec.symm).trans
    (hr K (c p) (hc p) ⟨p, hp p⟩).choose_spec


/-- Intrinsic continuous rays have a unique compatible signed-coordinate description. -/
theorem signed_charts_equivalence {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : RayField S) :
    IsContinuousRayField r ↔ ∃! s : SignedCharts S, RepresentsSignedCharts r s := by
  constructor
  · intro hr
    obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
    let s : SignedCharts S := {
      sign := chartSign K r
      locallyConstant := chartSign_locallyConstant K r hr
      compatible := by
        intro L c d hc hd p
        apply (signed_coordinate_rays_eq_iff L c d hc hd p _ _).mp
        exact (chartSign_represents K L r c hc ⟨p.val,p.property.1⟩).choose_spec.trans
          (chartSign_represents K L r d hd ⟨p.val,p.property.2⟩).choose_spec.symm }
    have hs : RepresentsSignedCharts r s := by
      intro L c hc p
      exact chartSign_represents K L r c hc p
    exact ⟨s, hs, fun t ht => signed_representation_unique r t s ht hs⟩
  · rintro ⟨s, hs, _⟩
    exact continuous_of_signed_representation r s hs

/-- Compatible signed charts determine a unique continuous intrinsic ray field. -/
theorem signed_orientation_exists_unique {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (s : SignedCharts S) :
    ∃! o : Orientation S, RepresentsSignedCharts o.val s := by
  obtain ⟨r, hr, hu⟩ := signed_charts_ray_exists_unique s
  exact ⟨⟨r, continuous_of_signed_representation r s hr⟩, hr,
    fun o ho => Subtype.ext (hu o.val ho)⟩


/-- The determinant is a smooth polynomial in the entries of an operator. -/
theorem contDiff_operator_det (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun L : Euclidean n →L[ℝ] Euclidean n => LinearMap.det L.toLinearMap) := by
  simp_rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin n)), Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply contDiff_const.mul
  apply contDiff_prod
  intro i _
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (σ i)).contDiff.comp
    (contDiff_id.clm_apply contDiff_const)

/-- Restricting a smooth function to an open subspace preserves its ambient extensions. -/
theorem vectorSmoothAt_restrict {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set (ModelChart n a M)} {f : M → V} (U : Set M) (hU : IsOpen U)
    (p : U) (hf : VectorSmoothAt A f p.val) :
    VectorSmoothAt (openSubsetAtlas A U hU) (fun q => f q.val) p := by
  refine ⟨hf.1.comp continuous_subtype_val.continuousAt, ?_⟩
  rintro d ⟨hne, c, hc, rfl⟩ hp
  have hp' : p.val ∈ c.source := by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp
  obtain ⟨W, hW, hpW, F, hF, he⟩ := hf.2 c hc hp'
  refine ⟨W, hW, hpW, F, hF, ?_⟩
  exact he.comp_tendsto continuousAt_subtype_val

/-- The transition determinant is smooth on the whole chart overlap. -/
theorem transitionDeterminant_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
      (c.open_source.inter d.open_source)) (transitionDeterminant K c d hc hd) := by
  intro p
  have ht := (BundleOperations.tangentPresentation S K).smooth ⟨c, hc⟩ ⟨d, hd⟩
    p.val p.property.1 p.property.2
  have hdet := ht.postcomp (contDiff_operator_det n)
  have hr := vectorSmoothAt_restrict (c.source ∩ d.source)
    (c.open_source.inter d.open_source) p hdet
  convert hr using 1
  funext q
  change LinearMap.det _ = _
  apply congrArg LinearMap.det
  apply LinearMap.ext
  intro v
  exact (BundleOperations.tangentTransition_apply K ⟨c, hc⟩ ⟨d, hd⟩ q.val
    q.property.1 q.property.2 v).symm

/-- Every locally constant function is smooth, with a constant ambient representative. -/
theorem vectorSmooth_of_isLocallyConstant {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Set (ModelChart n a M)) {f : M → V} (hf : IsLocallyConstant f) :
    VectorSmooth A f := by
  intro p
  apply (VectorSmoothAt.const A (f p) p).congr
  filter_upwards [hf.eventually_eq p] with y hy
  exact hy.symm

/-- Smooth functions on an open subspace restrict to every smaller open subspace. -/
theorem vectorSmooth_restrict_open {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set (ModelChart n a M)} (U W : Set M) (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) {f : U → V} (hf : VectorSmooth (openSubsetAtlas A U hU) f) :
    VectorSmooth (openSubsetAtlas A W hW) (fun p => f ⟨p.val, hWU p.property⟩) := by
  intro p
  have ht := (hf ⟨p.val, hWU p.property⟩).totalize hU
  have hr := vectorSmoothAt_restrict W hW p ht
  simpa only [FrameData.totalize_of_mem f _ (hWU (Subtype.property _))] using hr

/-- Transition determinants stay smooth on every open subset of their overlap. -/
theorem transitionDeterminant_smooth_on {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (U : Set M) (hU : IsOpen U)
    (hUc : U ⊆ c.source) (hUd : U ⊆ d.source) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val U hU)
      (fun p : U => transitionDeterminant K c d hc hd
        ⟨p.val, hUc p.property, hUd p.property⟩) := by
  exact vectorSmooth_restrict_open (c.source ∩ d.source) U
    (c.open_source.inter d.open_source) hU (fun _ hp => ⟨hUc hp, hUd hp⟩)
    (transitionDeterminant_smooth S K c d hc hd)

/-- A locally constant signed coordinate wedge is a smooth determinant section. -/
theorem signed_coordinate_section_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (s : SignedCharts S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) :
    IsSmoothDeterminantSection c.source c.open_source
      (fun p => signValue (s.sign c hc p) • coordinateVector K c hc p) := by
  intro L d hd
  have ht := transitionDeterminant_smooth S L c d hc hd
  let incl : ↥(c.source ∩ d.source) → c.source := fun p => ⟨p.val, p.property.1⟩
  have hinc : Continuous incl := continuous_subtype_val.subtype_mk _
  have hsign : IsLocallyConstant (fun p : ↥(c.source ∩ d.source) =>
      signValue (s.sign c hc ⟨p.val, p.property.1⟩)) :=
    ((s.locallyConstant c hc).comp signValue).comp_continuous hinc
  have hs := vectorSmooth_of_isLocallyConstant
    (openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
      (c.open_source.inter d.open_source)) hsign
  have hind (p : c.source) : coordinateVector K c hc p = coordinateVector L c hc p := by
    unfold coordinateVector
    rw [TangentBundle.chartCoordinates_unique (K.isCoordinates c hc p.val p.property)
      (L.isCoordinates c hc p.val p.property)]
  have he : (fun p : ↥(c.source ∩ d.source) =>
      determinantCoefficient L d hd ⟨p.val, p.property.2⟩
        (signValue (s.sign c hc ⟨p.val, p.property.1⟩) •
          coordinateVector K c hc ⟨p.val, p.property.1⟩)) =
      (fun p : ↥(c.source ∩ d.source) => signValue (s.sign c hc ⟨p.val, p.property.1⟩) *
        transitionDeterminant L c d hc hd p) := by
    funext p
    rw [map_smul, smul_eq_mul, hind, coefficient_coordinateVector_transition]
  rw [he]
  intro p
  exact ((hs p).prod (ht p)).postcomp (contDiff_fst.mul contDiff_snd)

def signedGenerator {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (s : SignedCharts S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (p : c.source) : DeterminantLine S p.val :=
  signValue (s.sign c hc p) • coordinateVector K c hc p

theorem signValue_mul_self (b : Bool) : signValue b * signValue b = 1 := by
  cases b <;> norm_num [signValue]

theorem signed_scalar_factor {V : Type*} [AddCommGroup V] [Module ℝ V]
    (x y : V) (δ : ℝ) (sc sd : Bool) (he : x = δ • y) :
    signValue sd • x = (signValue sd * δ * signValue sc) • (signValue sc • y) := by
  rw [he, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, signValue_mul_self, mul_one]

def signedGeneratorFactor {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (s : SignedCharts S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) : ℝ :=
  signValue (s.sign d hd ⟨p.val, p.property.2⟩) *
    transitionDeterminant K d c hd hc ⟨p.val, p.property.2, p.property.1⟩ *
      signValue (s.sign c hc ⟨p.val, p.property.1⟩)

theorem signedGenerator_factor {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (s : SignedCharts S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) :
    signedGenerator K s d hd ⟨p.val, p.property.2⟩ =
      signedGeneratorFactor K s c d hc hd p • signedGenerator K s c hc ⟨p.val, p.property.1⟩ := by
  have he := determinant_eq_coefficient_smul K c hc ⟨p.val, p.property.1⟩
    (coordinateVector K d hd ⟨p.val, p.property.2⟩)
  rw [coefficient_coordinateVector_transition K d c hd hc ⟨p.val, p.property.2, p.property.1⟩] at he
  exact signed_scalar_factor (V := DeterminantLine S p.val)
    (coordinateVector K d hd ⟨p.val,p.property.2⟩)
    (coordinateVector K c hc ⟨p.val,p.property.1⟩)
    (transitionDeterminant K d c hd hc ⟨p.val,p.property.2,p.property.1⟩)
    (s.sign c hc ⟨p.val,p.property.1⟩) (s.sign d hd ⟨p.val,p.property.2⟩) he

theorem signedGeneratorFactor_positive {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (r : RayField S) (s : SignedCharts S) (hr : RepresentsSignedCharts r s)
    (c d : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (hd : d ∈ S.smoothStructure.val) (p : ↥(c.source ∩ d.source)) :
    0 < signedGeneratorFactor K s c d hc hd p := by
  let x := signedGenerator K s c hc ⟨p.val,p.property.1⟩
  let y := signedGenerator K s d hd ⟨p.val,p.property.2⟩
  have hx : x ≠ 0 := signed_coordinateVector_ne_zero K c hc _ _
  have he : rayOfNeZero ℝ x hx = r p.val := (hr K c hc _).choose_spec
  have hy : IsPositive (rayOfNeZero ℝ x hx) y := by
    rw [he]
    exact hr K d hd _
  obtain ⟨t, ht, hyt⟩ := (positive_iff_pos_smul x hx y).mp hy
  have hfactor : y = signedGeneratorFactor K s c d hc hd p • x :=
    signedGenerator_factor K s c d hc hd p
  have heq : signedGeneratorFactor K s c d hc hd p = t := by
    exact (smul_left_injective ℝ hx) (hfactor.symm.trans hyt)
  rw [heq]
  exact ht

theorem vectorSmooth_mul {n : ℕ} {a : ModelKind} {X : Type u} [TopologicalSpace X]
    (A : Set (ModelChart n a X)) {f g : X → ℝ}
    (hf : VectorSmooth A f) (hg : VectorSmooth A g) :
    VectorSmooth A (fun p => f p * g p) := by
  intro p
  exact ((hf p).prod (hg p)).postcomp (contDiff_fst.mul contDiff_snd)

theorem signedGeneratorFactor_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (K : FiberCoordinates S)
    (s : SignedCharts S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
      (c.open_source.inter d.open_source)) (signedGeneratorFactor K s c d hc hd) := by
  let A := openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
    (c.open_source.inter d.open_source)
  have hsc : IsLocallyConstant (fun p : ↥(c.source ∩ d.source) =>
      signValue (s.sign c hc ⟨p.val,p.property.1⟩)) :=
    ((s.locallyConstant c hc).comp signValue).comp_continuous
      (continuous_subtype_val.subtype_mk _)
  have hsd : IsLocallyConstant (fun p : ↥(c.source ∩ d.source) =>
      signValue (s.sign d hd ⟨p.val,p.property.2⟩)) :=
    ((s.locallyConstant d hd).comp signValue).comp_continuous
      (continuous_subtype_val.subtype_mk _)
  exact vectorSmooth_mul A
    (vectorSmooth_mul A (vectorSmooth_of_isLocallyConstant A hsd)
      (transitionDeterminant_smooth_on S K d c hd hc (c.source ∩ d.source)
        (c.open_source.inter d.open_source) inter_subset_right inter_subset_left))
    (vectorSmooth_of_isLocallyConstant A hsc)

/-- Signed coordinate generators form a smooth positive-overlap cover. -/
theorem generators_of_signed_representation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : RayField S)
    (s : SignedCharts S) (hr : RepresentsSignedCharts r s) :
    ∃ G : LocalGenerators S, RepresentsGenerators r G := by
  obtain ⟨K⟩ := TangentBundle.fiberCoordinates_exists S
  let G : LocalGenerators S := {
    index := BundleOperationsData.TangentIndex S
    domain := fun i => i.val.source
    isOpen_domain := fun i => i.val.open_source
    cover := by
      intro p
      obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
      exact ⟨⟨c,hc⟩,hp⟩
    generator := fun i => signedGenerator K s i.val i.property
    nonzero := fun i p => signed_coordinateVector_ne_zero K i.val i.property p _
    smooth := fun i => signed_coordinate_section_smooth S K s i.val i.property
    overlap := by
      intro i j
      exact ⟨signedGeneratorFactor K s i.val j.val i.property j.property,
        signedGeneratorFactor_smooth S K s i.val j.val i.property j.property,
        fun p => ⟨signedGeneratorFactor_positive K r s hr i.val j.val i.property j.property p,
          signedGenerator_factor K s i.val j.val i.property j.property p⟩⟩ }
  exact ⟨G, fun i p => hr K i.val i.property p⟩

/-- Continuous intrinsic rays are exactly rays represented by smooth local generators. -/
theorem smooth_generators_equivalence {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (r : RayField S) :
    IsContinuousRayField r ↔ ∃ G : LocalGenerators S, RepresentsGenerators r G := by
  constructor
  · intro hr
    obtain ⟨s,hs,_⟩ := (signed_charts_equivalence S r).mp hr
    exact generators_of_signed_representation S r s hs
  · rintro ⟨G,hG⟩
    exact continuous_of_represents_generators r G hG

variable {V : Type u} [AddCommGroup V] [Module ℝ V] {n : ℕ}

lemma basis_pairing_self (b : Basis (Fin n) ℝ V) :
    exteriorPower.pairingDual ℝ V n (exteriorPower.ιMulti ℝ n b.dualBasis)
      (exteriorPower.ιMulti ℝ n b) = 1 := by
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  suffices (Matrix.of (fun i j => b.dualBasis j (b i))) = (1 : Matrix (Fin n) (Fin n) ℝ) by
    rw [this, Matrix.det_one]
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply]

lemma dual_top_finrank (b : Basis (Fin n) ℝ V) :
    Module.finrank ℝ (⋀[ℝ]^n (Module.Dual ℝ V)) = 1 := by
  letI := b.finiteDimensional_of_finite
  letI : Module.Free ℝ (Module.Dual ℝ V) := Module.Free.of_divisionRing ℝ _
  rw [exteriorPower.finrank_eq, Module.finrank_eq_card_basis b.dualBasis]
  simp

lemma exists_unique_positive_ray [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) (L : V →ₗ[ℝ] ℝ) (hL : L ≠ 0) :
    ∃! r : Module.Ray ℝ V, ∀ v, OrientationData.IsPositive r v ↔ 0 < L v := by
  obtain ⟨x, hx⟩ := (surjective_of_nonzero_of_finrank_eq_one
    (Module.finrank_self ℝ) hL) 1
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  refine ⟨rayOfNeZero ℝ x hx0, ?_, ?_⟩
  · intro v
    rw [OrientationResults.positive_iff_pos_smul x hx0]
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [map_smul, hx] using ht
    · intro hv
      obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' x hx0).mp hdim v
      refine ⟨t, ?_, ht.symm⟩
      simpa [← ht, map_smul, hx] using hv
  · intro r hr
    have hpos : OrientationData.IsPositive r x := (hr x).mpr (by simpa [hx])
    exact hpos.choose_spec.symm

lemma pairingDual_ne_zero
    (h : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.alternating_interpretationType.{u})
    [FiniteDimensional ℝ V] {ω : ExteriorData.Fiber V n} (hω : ω ≠ 0) :
    exteriorPower.pairingDual ℝ V n ω ≠ 0 := by
  intro hpair
  apply hω
  apply (h V n).1
  simp [ExteriorData.evaluate, hpair]

def topIndex (n : ℕ) : ExteriorData.Index n n :=
  Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id (Fin n))

lemma topIndex_unique (I : ExteriorData.Index n n) : I = topIndex n := by
  apply Subtype.ext
  have hI : I.val = Finset.univ := Finset.eq_univ_of_card _ (by simpa using I.property)
  have ht : (topIndex n).val = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using (topIndex n).property)
  exact hI.trans ht.symm

lemma top_exterior_basis (b : Basis (Fin n) ℝ V) :
    b.exteriorPower n (topIndex n) = exteriorPower.ιMulti ℝ n b := by
  simp [exteriorPower.basis_apply, exteriorPower.ιMulti_family, topIndex, Function.comp_def]

lemma top_exterior_expansion (b : Basis (Fin n) ℝ V) (ω : ExteriorData.Fiber V n) :
    ω = (b.dualBasis.exteriorPower n).repr ω (topIndex n) •
      exteriorPower.ιMulti ℝ n b.dualBasis := by
  letI : Unique (ExteriorData.Index n n) := ⟨⟨topIndex n⟩, topIndex_unique⟩
  have hsum := ((b.dualBasis.exteriorPower n).sum_repr ω).symm
  rw [Fintype.sum_unique] at hsum
  change ω = _ at hsum
  rw [show (default : ExteriorData.Index n n) = topIndex n from rfl,
    top_exterior_basis] at hsum
  exact hsum

lemma pairing_top_eq_coefficient (b : Basis (Fin n) ℝ V) (ω : ExteriorData.Fiber V n) :
    exteriorPower.pairingDual ℝ V n ω (exteriorPower.ιMulti ℝ n b) =
      (b.dualBasis.exteriorPower n).repr ω (topIndex n) := by
  conv_lhs => rw [top_exterior_expansion b ω]
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, basis_pairing_self, mul_one]

open ModelData AtlasData TangentData TangentBundleData OrientationData BundleOperationsData

lemma pairing_coordinateVector_eq_coefficients {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : ExteriorData.Field S n) (p : c.source) :
    pairing p.val (ω p.val) (coordinateVector C.tangent.fiberCoordinates c hc p) =
      ExteriorData.coefficients C n c hc ω p (topIndex n) := by
  let b : Basis (Fin n) ℝ (TangentSpace S p.val) :=
    (Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm
  have hv : coordinateVector C.tangent.fiberCoordinates c hc p =
      exteriorPower.ιMulti ℝ n b := by
    rfl
  rw [hv]
  change exteriorPower.pairingDual ℝ (TangentSpace S p.val) n (ω p.val)
    (exteriorPower.ιMulti ℝ n b) = (b.dualBasis.exteriorPower n).repr (ω p.val) (topIndex n)
  exact @pairing_top_eq_coefficient (TangentSpace S p.val) inferInstance inferInstance n b (ω p.val)

lemma top_coefficient_ne_zero (b : Basis (Fin n) ℝ V)
    {ω : ExteriorData.Fiber V n} (hω : ω ≠ 0) :
    (b.dualBasis.exteriorPower n).repr ω (topIndex n) ≠ 0 := by
  intro he
  apply hω
  rw [top_exterior_expansion b ω, he, zero_smul]

lemma coefficients_top_ne_zero {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : CotangentBundle S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (ω : ExteriorData.Field S n) (hω : ∀ p, ω p ≠ 0) (p : c.source) :
    ExteriorData.coefficients C n c hc ω p (topIndex n) ≠ 0 := by
  let b : Basis (Fin n) ℝ (TangentSpace S p.val) :=
    (Pi.basisFun ℝ (Fin n)).map
      (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm
  exact @top_coefficient_ne_zero (TangentSpace S p.val) inferInstance inferInstance n b
    (ω p.val) (hω p.val)

lemma positive_ray_characterization [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 1) (r : Module.Ray ℝ V) (L : V →ₗ[ℝ] ℝ)
    (hpos : ∀ v, OrientationData.IsPositive r v → 0 < L v) :
    ∀ v, OrientationData.IsPositive r v ↔ 0 < L v := by
  induction r using Module.Ray.ind with | h x hx =>
  have hLx : 0 < L x := hpos x ⟨hx, rfl⟩
  intro v
  rw [OrientationResults.positive_iff_pos_smul x hx]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa only [map_smul, smul_eq_mul] using mul_pos ht hLx
  · intro hv
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim v
    refine ⟨t, ?_, ht.symm⟩
    rw [← ht, map_smul, smul_eq_mul] at hv
    exact (mul_pos_iff_of_pos_right hLx).mp hv

lemma continuous_of_positive_top_form
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {a : ModelKind} {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (C : CotangentBundle S) (D : ExteriorData.FormBundle C n)
    (r : RayField S) (ω : NonvanishingTopForm D) (hpos : IsPositiveTopForm r ω.val.field) :
    IsContinuousRayField r := by
  intro K c hc
  let f : c.source → ℝ := fun p => ExteriorData.coefficients C n c hc ω.val.field p (topIndex n)
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun p =>
    ((hcoeff C n D ω.val.field).mp ω.val.smooth c hc (topIndex n) p).1)
  have hfn : ∀ p, f p ≠ 0 := coefficients_top_ne_zero C c hc ω.val.field ω.property
  have hlc := OrientationResults.locallyConstant_ray_smul _
    (OrientationResults.standardDeterminantVector_ne_zero n) f hf hfn
  have he : (fun p : c.source => Module.Ray.map (determinantCoordinates K c hc p) (r p.val)) =
      (fun p => rayOfNeZero ℝ
        (f p • exteriorPower.ιMulti ℝ n (Pi.basisFun ℝ (Fin n)))
        (smul_ne_zero (hfn p) (OrientationResults.standardDeterminantVector_ne_zero n))) := by
    funext p
    letI := (tangent_dimension S p.val).1
    have hp : IsPositive (r p.val)
        (f p • coordinateVector C.tangent.fiberCoordinates c hc p) := by
      apply (@positive_ray_characterization (DeterminantLine S p.val) inferInstance inferInstance
        inferInstance (OrientationResults.determinant_finrank S p.val) (r p.val)
        (exteriorPower.pairingDual ℝ (TangentSpace S p.val) n (ω.val.field p.val)) (hpos p.val) _).mpr
      change 0 < _
      rw [map_smul, smul_eq_mul]
      change 0 < f p * pairing p.val (ω.val.field p.val)
        (coordinateVector C.tangent.fiberCoordinates c hc p)
      rw [pairing_coordinateVector_eq_coefficients]
      exact mul_self_pos.mpr (hfn p)
    rw [← hp.choose_spec, Module.Ray.map_apply]
    have hec : coordinateVector C.tangent.fiberCoordinates c hc p = coordinateVector K c hc p := by
      unfold coordinateVector
      rw [TangentBundle.chartCoordinates_unique
        (C.tangent.fiberCoordinates.isCoordinates c hc p.val p.property)
        (K.isCoordinates c hc p.val p.property)]
    simp only [map_smul, hec, OrientationResults.determinantCoordinates_coordinateVector]
  rw [he]
  exact hlc


/-- The determinant-normalized dual coordinate wedge. -/
def coordinateTopForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    ExteriorData.Fiber (TangentSpace S p.val) n :=
  let b := (Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm
  exteriorPower.ιMulti ℝ n b.dualBasis

lemma pairing_coordinateTopForm_self {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    pairing p.val (coordinateTopForm K c hc p) (coordinateVector K c hc p) = 1 := by
  let b := (Pi.basisFun ℝ (Fin n)).map (K.equiv c hc p.val p.property).symm
  exact @basis_pairing_self (TangentSpace S p.val) inferInstance inferInstance n b

lemma linearMap_eq_coefficient {W : Type*} [AddCommGroup W] [Module ℝ W]
    (L : W →ₗ[ℝ] ℝ) (x y : W) (t : ℝ) (hx : L x = 1) (hy : y = t • x) :
    L y = t := by
  rw [hy, map_smul, hx, smul_eq_mul, mul_one]

lemma pairing_coordinateTopForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (v : DeterminantLine S p.val) :
    pairing p.val (coordinateTopForm K c hc p) v = determinantCoefficient K c hc p v := by
  exact @linearMap_eq_coefficient (DeterminantLine S p.val) inferInstance inferInstance
    (exteriorPower.pairingDual ℝ (TangentSpace S p.val) n (coordinateTopForm K c hc p))
    (coordinateVector K c hc p) v (determinantCoefficient K c hc p v)
    (pairing_coordinateTopForm_self K c hc p) (determinant_eq_coefficient_smul K c hc p v)

def signedCoordinateTopForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (s : SignedCharts S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source) :
    ExteriorData.Fiber (TangentSpace S p.val) n :=
  signValue (s.sign c hc p) • coordinateTopForm K c hc p

lemma positive_signedCoordinateTopForm {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (r : RayField S)
    (s : SignedCharts S) (hr : RepresentsSignedCharts r s)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (v : DeterminantLine S p.val) (hv : IsPositive (r p.val) v) :
    0 < pairing p.val (signedCoordinateTopForm K s c hc p) v := by
  have hx := hr K c hc p
  have hv' : IsPositive (rayOfNeZero ℝ (signValue (s.sign c hc p) • coordinateVector K c hc p) hx.choose) v := by
    rw [hx.choose_spec]
    exact hv
  obtain ⟨t, ht, hvt⟩ := (positive_iff_pos_smul _ hx.choose v).mp hv'
  have he : pairing p.val (signedCoordinateTopForm K s c hc p) v = t := by
    unfold signedCoordinateTopForm pairing
    rw [map_smul, LinearMap.smul_apply]
    change signValue (s.sign c hc p) * pairing p.val (coordinateTopForm K c hc p) v = t
    rw [pairing_coordinateTopForm]
    have hcV := congrArg (determinantCoefficient K c hc p) hvt
    simp only [map_smul, coefficient_coordinateVector, smul_eq_mul, mul_one] at hcV
    rw [hcV, mul_left_comm, signValue_mul_self, mul_one]
  rw [he]
  exact ht


lemma form_orientation_exists_unique
    (hpair : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.alternating_interpretationType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {a : ModelKind} {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (C : CotangentBundle S) (D : ExteriorData.FormBundle C n) (ω : NonvanishingTopForm D) :
    ∃! o : Orientation S, ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.val.field p) v := by
  have hex : ∀ p : M, ∃! r : DeterminantRay S p,
      ∀ v, IsPositive r v ↔ 0 < pairing p (ω.val.field p) v := by
    intro p
    letI := (tangent_dimension S p).1
    exact @exists_unique_positive_ray (DeterminantLine S p) inferInstance inferInstance
      inferInstance (OrientationResults.determinant_finrank S p)
      (exteriorPower.pairingDual ℝ (TangentSpace S p) n (ω.val.field p))
      (@pairingDual_ne_zero (TangentSpace S p) inferInstance inferInstance n hpair
        inferInstance (ω.val.field p) (ω.property p))
  choose r hr huniq using hex
  have hp : IsPositiveTopForm r ω.val.field := fun p v hv => (hr p v).mp hv
  refine ⟨⟨r, continuous_of_positive_top_form hcoeff S C D r ω hp⟩, hr, ?_⟩
  intro q hq
  apply Subtype.ext
  funext p
  exact huniq p (q.val p) (hq p)

lemma exists_positive_ratio_of_positive_top_forms
    {a : ModelKind} {M : Type u} [TopologicalSpace M] (S : SmoothManifold n a M)
    (C : CotangentBundle S) (D : ExteriorData.FormBundle C n)
    (r : RayField S) (α β : NonvanishingTopForm D)
    (hα : IsPositiveTopForm r α.val.field) (hβ : IsPositiveTopForm r β.val.field) :
    ∃ f : M → ℝ, (∀ p, 0 < f p) ∧ ∀ p, β.val.field p = f p • α.val.field p := by
  have hex : ∀ p, ∃ t : ℝ, t • α.val.field p = β.val.field p := by
    intro p
    obtain ⟨c, hc, hp⟩ := S.smoothStructure.property.1.1 p
    let b : Basis (Fin n) ℝ (TangentSpace S p) :=
      (Pi.basisFun ℝ (Fin n)).map (C.tangent.fiberCoordinates.equiv c hc p hp).symm
    have hdim := @dual_top_finrank (TangentSpace S p) inferInstance inferInstance n b
    exact (finrank_eq_one_iff_of_nonzero' (K := ℝ) (α.val.field p) (α.property p)).mp hdim
      (β.val.field p)
  choose f hf using hex
  refine ⟨f, ?_, fun p => (hf p).symm⟩
  intro p
  have hrep : ∃ (x : DeterminantLine S p) (hx : x ≠ 0), rayOfNeZero ℝ x hx = r p := by
    induction r p using Module.Ray.ind with | h x hx => exact ⟨x, hx, rfl⟩
  obtain ⟨x, hx, hxr⟩ := hrep
  have hax : 0 < pairing p (α.val.field p) x := hα p x ⟨hx, hxr⟩
  have hbx : 0 < pairing p (β.val.field p) x := hβ p x ⟨hx, hxr⟩
  rw [← hf p] at hbx
  change 0 < (exteriorPower.pairingDual ℝ (TangentSpace S p) n
    (f p • α.val.field p)) x at hbx
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul] at hbx
  exact (mul_pos_iff_of_pos_right hax).mp hbx


theorem vectorSmoothAt_restrict_open {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {A : Set (ModelChart n a M)}
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {U : Set M} (hU : IsOpen U) {f : M → V} {p : U}
    (hf : VectorSmoothAt A f p.val) :
    VectorSmoothAt (openSubsetAtlas A U hU) (fun q : U => f q.val) p := by
  refine ⟨hf.1.comp continuous_subtype_val.continuousAt, ?_⟩
  rintro d ⟨hne, c, hc, rfl⟩ hp
  obtain ⟨W, hW, hpW, F, hF, he⟩ := hf.2 c hc (by simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hp)
  refine ⟨W, hW, hpW, F, hF, ?_⟩
  exact he.comp_tendsto continuous_subtype_val.continuousAt

/-- Smoothness on open subspaces detects global smoothness for actual ambient germs. -/
theorem vectorSmooth_of_open_cover {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M))
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ι : Type w} (f : M → V) (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ p, ∃ i, p ∈ U i)
    (hf : ∀ i, VectorSmooth (openSubsetAtlas A (U i) (hU i)) (fun p => f p.val)) :
    VectorSmooth A f := by
  intro p
  obtain ⟨i, hi⟩ := hcover p
  have h := (hf i ⟨p, hi⟩).totalize (hU i)
  apply h.congr
  filter_upwards [(hU i).mem_nhds hi] with q hq
  exact totalize_of_mem _ q hq

theorem vectorSmoothAt_div {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {A : Set (ModelChart n a M)} {f g : M → ℝ} {p : M}
    (hf : VectorSmoothAt A f p) (hg : VectorSmoothAt A g p) (hgp : g p ≠ 0) :
    VectorSmoothAt A (fun q => f q / g q) p := by
  have hi : VectorSmoothAt A (fun q => (g q)⁻¹) p :=
    hg.postcompOn isOpen_compl_singleton hgp (contDiffOn_inv ℝ)
  exact (hf.prod hi).postcomp (contDiff_fst.mul contDiff_snd)

/-- A scalar is smooth if its restriction to every chart source is smooth. -/
theorem vectorSmooth_of_chart_restrictions {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (hA : IsAtlas A)
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : M → V)
    (hf : ∀ c (hc : c ∈ A), VectorSmooth (openSubsetAtlas A c.source c.open_source)
      (fun p => f p.val)) : VectorSmooth A f := by
  apply vectorSmooth_of_open_cover A f (fun c : A => c.val.source)
    (fun c => c.val.open_source)
  · intro p
    obtain ⟨c, hc, hp⟩ := hA p
    exact ⟨⟨c, hc⟩, hp⟩
  · intro c
    exact hf c.val c.property

lemma coefficients_of_smul_relation {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M}
    (C : BundleOperationsData.CotangentBundle S)
    (α β : ExteriorData.Field S n) (f : M → ℝ)
    (hrel : ∀ p, β p = f p • α p)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source)
    (I : ExteriorData.Index n n) :
    ExteriorData.coefficients C n c hc β p I =
      f p.val * ExteriorData.coefficients C n c hc α p I := by
  unfold ExteriorData.coefficients
  rw [hrel]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- The pointwise scalar relating nonvanishing top forms is globally smooth. -/
theorem smooth_scalar_of_smul_relation
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : BundleOperationsData.CotangentBundle S)
    (D : ExteriorData.FormBundle C n) (α β : ExteriorData.Form D) (f : M → ℝ)
    (hrel : ∀ p, β.field p = f p • α.field p)
    (I : ExteriorData.Index n n)
    (hn : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (p : c.source),
      ExteriorData.coefficients C n c hc α.field p I ≠ 0) :
    VectorSmooth S.smoothStructure.val f := by
  apply vectorSmooth_of_chart_restrictions S.smoothStructure.val S.smoothStructure.property.1.1
  intro c hc p
  have hα := ((hcoeff C n D α.field).mp α.smooth c hc I) p
  have hβ := ((hcoeff C n D β.field).mp β.smooth c hc I) p
  have hdiv := vectorSmoothAt_div hβ hα (hn c hc p)
  apply hdiv.congr
  apply Filter.Eventually.of_forall
  intro q
  exact ((eq_div_iff (hn c hc q)).mpr
    (coefficients_of_smul_relation C α.field β.field f hrel c hc q I).symm).symm


open ExteriorData PartitionData BundleOperationsData

def localTopField {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (K : FiberCoordinates S) (s : SignedCharts S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) : Field S n :=
  fun p => if h : p ∈ c.source then signedCoordinateTopForm K s c hc ⟨p,h⟩ else 0

lemma coefficients_localTopField {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (s : SignedCharts S) (c d : ModelChart n a M)
    (hc : c ∈ S.smoothStructure.val) (hd : d ∈ S.smoothStructure.val)
    (p : ↥(c.source ∩ d.source)) :
    coefficients C n d hd (localTopField C.tangent.fiberCoordinates s c hc)
      ⟨p.val,p.property.2⟩ (topIndex n) =
        signValue (s.sign c hc ⟨p.val,p.property.1⟩) *
          transitionDeterminant C.tangent.fiberCoordinates d c hd hc
            ⟨p.val,p.property.2,p.property.1⟩ := by
  rw [← pairing_coordinateVector_eq_coefficients]
  unfold localTopField
  rw [dif_pos p.property.1]
  unfold signedCoordinateTopForm pairing
  rw [map_smul, LinearMap.smul_apply]
  change signValue (s.sign c hc ⟨p.val,p.property.1⟩) *
    pairing p.val (coordinateTopForm C.tangent.fiberCoordinates c hc ⟨p.val,p.property.1⟩)
      (coordinateVector C.tangent.fiberCoordinates d hd ⟨p.val,p.property.2⟩) = _
  congr 1
  exact (pairing_coordinateTopForm C.tangent.fiberCoordinates c hc
    ⟨p.val,p.property.1⟩ (coordinateVector C.tangent.fiberCoordinates d hd ⟨p.val,p.property.2⟩)).trans
      (coefficient_coordinateVector_transition C.tangent.fiberCoordinates d c hd hc
        ⟨p.val,p.property.2,p.property.1⟩)

lemma smooth_localTopField_coefficients {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (s : SignedCharts S) (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    (d : ModelChart n a M) (hd : d ∈ S.smoothStructure.val) (I : Index n n) :
    VectorSmooth (openSubsetAtlas S.smoothStructure.val (c.source ∩ d.source)
      (c.open_source.inter d.open_source))
      (fun p : ↥(c.source ∩ d.source) =>
        coefficients C n d hd (localTopField C.tangent.fiberCoordinates s c hc)
          ⟨p.val,p.property.2⟩ I) := by
  rw [topIndex_unique I]
  have he : (fun p : ↥(c.source ∩ d.source) =>
      coefficients C n d hd (localTopField C.tangent.fiberCoordinates s c hc)
        ⟨p.val,p.property.2⟩ (topIndex n)) =
      (fun p => signValue (s.sign c hc ⟨p.val,p.property.1⟩) *
        transitionDeterminant C.tangent.fiberCoordinates d c hd hc
          ⟨p.val,p.property.2,p.property.1⟩) := by
    funext p
    exact coefficients_localTopField C s c d hc hd p
  rw [he]
  have hsc : IsLocallyConstant (fun p : ↥(c.source ∩ d.source) =>
      signValue (s.sign c hc ⟨p.val,p.property.1⟩)) :=
    ((s.locallyConstant c hc).comp signValue).comp_continuous
      (continuous_subtype_val.subtype_mk _)
  exact vectorSmooth_mul _ (vectorSmooth_of_isLocallyConstant _ hsc)
    (transitionDeterminant_smooth_on S C.tangent.fiberCoordinates d c hd hc
      (c.source ∩ d.source) (c.open_source.inter d.open_source)
      inter_subset_right inter_subset_left)


/-- A local scalar coefficient may be multiplied by a supported smooth weight
and extended by zero, including at the boundary of its local domain. -/
theorem weighted_local_scalar_smooth {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (A : Set (ModelChart n a M)) (U V : Set M)
    (hU : IsOpen U) (hV : IsOpen V) (ρ : M → ℝ) (hρ : VectorSmooth A ρ)
    (hsupp : sectionSupport ρ ⊆ U) (f : ↥(U ∩ V) → ℝ)
    (hf : VectorSmooth (openSubsetAtlas A (U ∩ V) (hU.inter hV)) f) :
    VectorSmooth (openSubsetAtlas A V hV)
      (fun p : V => if hp : p.val ∈ U then ρ p.val * f ⟨p.val, hp, p.property⟩ else 0) := by
  intro p
  by_cases hp : p.val ∈ U
  · have hft := (hf ⟨p.val, hp, p.property⟩).totalize (hU.inter hV)
    have hmul := ((hρ p.val).prod hft).postcomp (contDiff_fst.mul contDiff_snd)
    have hres := vectorSmoothAt_restrict V hV p hmul
    apply hres.congr
    filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hU.mem_nhds hp)] with q hq
    change q.val ∈ U at hq
    simp only [dite_eq_left hq, FrameData.totalize_of_mem f q.val ⟨hq, q.property⟩]
  · have hp' : p.val ∉ sectionSupport ρ := fun h => hp (hsupp h)
    have he : ∀ᶠ y in 𝓝 p.val, ρ y = 0 := by
      filter_upwards [isClosed_closure.compl_mem_nhds hp'] with y hy
      exact Function.notMem_support.mp (fun h => hy (subset_closure h))
    apply (VectorSmoothAt.const _ (0 : ℝ) p).congr
    have he' : ρ =ᶠ[𝓝 p.val] (fun _ => 0) := he
    filter_upwards [he'.comp_tendsto continuousAt_subtype_val] with q hq
    change ρ q.val = 0 at hq
    split_ifs <;> simp [hq]

/-- An exterior coordinate coefficient is a linear functional, and hence
commutes with every sum having finite support. -/
theorem coefficients_finsum {n k : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (C : CotangentBundle S)
    (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val)
    {ι : Type v} (f : ι → Field S k) (p : c.source) (I : Index n k)
    (hf : Function.HasFiniteSupport (fun i => f i p.val)) :
    coefficients C k c hc (fun q => ∑ᶠ i, f i q) p I =
      ∑ᶠ i, coefficients C k c hc (f i) p I := by
  let b := ((Pi.basisFun ℝ (Fin n)).map
    (C.tangent.fiberCoordinates.equiv c hc p.val p.property).symm).dualBasis.exteriorPower k
  exact (((Finsupp.lapply I).comp b.repr.toLinearMap).toAddMonoidHom.map_finsum hf)

/-- Smooth exterior fields can be summed whenever a locally finite scalar
support family bounds their nonzero loci. -/
theorem finsum_forms_smooth
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C k)
    {ι : Type v} (f : ι → Field S k) (hf : ∀ i, IsForm D (f i))
    (ρ : ι → M → ℝ) (hlf : LocallyFinite (fun i => sectionSupport (ρ i)))
    (hzero : ∀ i p, ρ i p = 0 → f i p = 0) :
    IsForm D (fun p => ∑ᶠ i, f i p) := by
  apply (h9 C k D _).mpr
  intro c hc I
  have hcoeffsupp : ∀ i,
      sectionSupport (fun p : c.source => coefficients C k c hc (f i) p I) ⊆
        Subtype.val ⁻¹' sectionSupport (ρ i) := by
    intro i
    apply closure_minimal
    · intro p hp
      apply subset_closure
      intro hz
      apply hp
      have hfz := hzero i p.val hz
      simp only [ExteriorData.coefficients, hfz, map_zero, Finsupp.zero_apply]
    · exact isClosed_closure.preimage continuous_subtype_val
  have hlf' := (hlf.preimage_continuous continuous_subtype_val).subset hcoeffsupp
  have hs := scalarContDiff_finsum
    (fun i => (vectorSmooth_scalar_iff _ _).mp ((h9 C k D (f i)).mp (hf i) c hc I)) hlf'
  apply (vectorSmooth_scalar_iff _ _).mpr
  convert hs using 1
  funext p
  apply coefficients_finsum
  apply (hlf.point_finite p.val).subset
  intro i hi
  apply subset_closure
  intro hz
  exact hi (hzero i p.val hz)

/-- A local exterior field becomes a global smooth form after multiplication
by a smooth scalar whose closed support lies in its domain of smoothness. -/
theorem supported_local_form_smooth
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C k)
    (U : Set M) (hU : IsOpen U) (ω : Field S k)
    (hω : ∀ (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val (U ∩ c.source)
        (hU.inter c.open_source))
        (fun p => coefficients C k c hc ω ⟨p.val, p.property.2⟩ I))
    (ρ : M → ℝ) (hρ : VectorSmooth S.smoothStructure.val ρ)
    (hsupp : sectionSupport ρ ⊆ U) : IsForm D (fun p => ρ p • ω p) := by
  apply (h9 C k D _).mpr
  intro c hc I
  have hs := weighted_local_scalar_smooth S.smoothStructure.val U c.source hU c.open_source
    ρ hρ hsupp _ (hω c hc I)
  convert hs using 1
  funext p
  by_cases hp : p.val ∈ U
  · simp only [dite_eq_left hp, ExteriorData.coefficients, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · have hz : ρ p.val = 0 := by
      by_contra hz
      exact hp (hsupp (subset_closure hz))
    simp only [dite_eq_right hp, hz, zero_smul, ExteriorData.coefficients, map_zero, Finsupp.zero_apply]

/-- A subordinate smooth partition globalizes any family of exterior fields
whose coefficients are smooth on their assigned open domains. -/
theorem globalize_local_forms
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {n k : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n a M} (C : CotangentBundle S) (D : FormBundle C k)
    {ι : Type v} (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (ω : ι → Field S k)
    (hω : ∀ i (c : ModelChart n a M) (hc : c ∈ S.smoothStructure.val) (I : Index n k),
      VectorSmooth (openSubsetAtlas S.smoothStructure.val (U i ∩ c.source)
        ((hU i).inter c.open_source))
        (fun p => coefficients C k c hc (ω i) ⟨p.val, p.property.2⟩ I))
    (ρ : ι → M → ℝ) (hρ : IsSmoothPartition S.smoothStructure.val ρ)
    (hsub : IsSubordinate U ρ) :
    IsForm D (fun p => ∑ᶠ i, ρ i p • ω i p) := by
  refine finsum_forms_smooth h9 C D (fun i p => ρ i p • ω i p) ?_ ρ hρ.2.2.1 ?_
  · intro i
    exact supported_local_form_smooth h9 C D (U i) (hU i) (ω i) (hω i) (ρ i)
      ((vectorSmooth_scalar_iff _ _).mpr (hρ.1 i)) (hsub i)
  · intro i p hp
    rw [hp, zero_smul]

theorem map_weighted_finsum_positive {ι : Type*} {V : Type*}
    [AddCommGroup V] [Module ℝ V] (ρ : ι → ℝ) (v : ι → V) (L : V →ₗ[ℝ] ℝ)
    (hfin : Function.HasFiniteSupport ρ) (hn : ∀ i, 0 ≤ ρ i)
    (hsum : ∑ᶠ i, ρ i = 1) (hp : ∀ i, ρ i ≠ 0 → 0 < L (v i)) :
    0 < L (∑ᶠ i, ρ i • v i) := by
  have hw : Function.HasFiniteSupport (fun i => ρ i • v i) := by
    apply hfin.subset
    intro i hi hz
    exact hi (by simp only [hz, zero_smul])
  have he : L (∑ᶠ i, ρ i • v i) = ∑ᶠ i, L (ρ i • v i) :=
    L.toAddMonoidHom.map_finsum hw
  rw [he]
  simp only [map_smul, smul_eq_mul]
  apply finsum_pos
  · intro i
    by_cases hi : ρ i = 0
    · simp [hi]
    · exact mul_nonneg (hn i) (hp i hi).le
  · have hex : ∃ i, ρ i ≠ 0 := by
      by_contra h
      have hzero : ∀ i, ρ i = 0 := by simpa using h
      rw [finsum_eq_zero_of_forall_eq_zero hzero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i,hi⟩ := hex
    exact ⟨i, mul_pos (lt_of_le_of_ne (hn i) (Ne.symm hi)) (hp i hi)⟩
  · apply hfin.subset
    intro i hi hz
    exact hi (by simp only [hz, zero_mul])

theorem field_ne_zero_of_positive {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] {S : SmoothManifold n a M} (r : RayField S)
    (ω : Field S n) (hp : IsPositiveTopForm r ω) (p : M) : ω p ≠ 0 := by
  have hex : ∃ v, IsPositive (r p) v := by
    induction r p using Module.Ray.ind with | h x hx => exact ⟨x,hx,rfl⟩
  obtain ⟨v,hv⟩ := hex
  have he := hp p v hv
  intro hz
  unfold pairing at he
  rw [hz, map_zero, LinearMap.zero_apply] at he
  exact (lt_irrefl 0) he

/-- A continuous intrinsic orientation admits a positive smooth global top form. -/
theorem positive_top_form_exists
    (h9 : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (D : FormBundle C n)
    (r : RayField S) (hr : IsContinuousRayField r) :
    ∃ ω : NonvanishingTopForm D, IsPositiveTopForm r ω.val.field := by
  obtain ⟨s, hs, _⟩ := (signed_charts_equivalence S r).mp hr
  let K := C.tangent.fiberCoordinates
  let U : TangentIndex S → Set M := fun i => i.val.source
  have hU : ∀ i, IsOpen (U i) := fun i => i.val.open_source
  have hcover : ∀ p, ∃ i, p ∈ U i := by
    intro p
    obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p
    exact ⟨⟨c,hc⟩,hp⟩
  obtain ⟨ρ,hρ,hsub⟩ := exists_smooth_partition S U hU hcover
  let ωloc : TangentIndex S → Field S n := fun i => localTopField K s i.val i.property
  let ω : Field S n := fun p => ∑ᶠ i, ρ i p • ωloc i p
  have hω : IsForm D ω := globalize_local_forms h9 C D U hU ωloc
    (fun i c hc I => smooth_localTopField_coefficients S C s i.val i.property c hc I)
    ρ hρ hsub
  have hpos : IsPositiveTopForm r ω := by
    intro p v hv
    let L : Fiber (TangentSpace S p) n →ₗ[ℝ] ℝ :=
      (exteriorPower.pairingDual ℝ (TangentSpace S p) n).flip v
    have hfin : Function.HasFiniteSupport (fun i => ρ i p) :=
      (hρ.2.2.1.point_finite p).subset (fun i hi => subset_closure hi)
    change 0 < L (∑ᶠ i, ρ i p • ωloc i p)
    apply map_weighted_finsum_positive (fun i => ρ i p) (fun i => ωloc i p) L
      hfin (fun i => hρ.2.1 i p) (hρ.2.2.2 p)
    intro i hi
    have hp : p ∈ i.val.source := hsub i (subset_closure hi)
    change 0 < pairing p (localTopField K s i.val i.property p) v
    unfold localTopField
    rw [dif_pos hp]
    exact positive_signedCoordinateTopForm K r s hs i.val i.property ⟨p,hp⟩ v hv
  exact ⟨⟨⟨ω,hω⟩, field_ne_zero_of_positive r ω hpos⟩,hpos⟩

/-- Abstract quotient step once the positive-form existence and ratio arguments
have been established for the actual determinant pairing. -/
theorem top_form_quotient_of_characters {n : ℕ} {a : ModelKind} {M : Type u}
    [TopologicalSpace M] (S : SmoothManifold n a M) (C : CotangentBundle S)
    (D : ExteriorData.FormBundle C n)
    (hori : ∀ ω : NonvanishingTopForm D, ∃! o : Orientation S,
      ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.val.field p) v)
    (hsurj : ∀ o : Orientation S, ∃ ω : NonvanishingTopForm D,
      ∀ p v, IsPositive (o.val p) v ↔ 0 < pairing p (ω.val.field p) v)
    (hratio : ∀ (r : RayField S) (α β : NonvanishingTopForm D),
      IsPositiveTopForm r α.val.field → IsPositiveTopForm r β.val.field → PositiveMultiple α β) :
    ∃ e : Quot (@PositiveMultiple n a M _ S C D) ≃ Orientation S,
      ∀ (ω : NonvanishingTopForm D) (p : M) (v : DeterminantLine S p),
        IsPositive ((e (Quot.mk _ ω)).val p) v ↔ 0 < pairing p (ω.val.field p) v := by
  choose O hO huniq using hori
  have hrespect : ∀ α β : NonvanishingTopForm D, PositiveMultiple α β → O α = O β := by
    intro α β h
    obtain ⟨f, hf, hpos, heq⟩ := h
    apply huniq β (O α)
    intro p v
    rw [hO α p v, heq p]
    change 0 < pairing p (α.val.field p) v ↔
      0 < exteriorPower.pairingDual ℝ (TangentSpace S p) n (f p • α.val.field p) v
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact (mul_pos_iff_of_pos_left (hpos p)).symm
  let F : Quot (@PositiveMultiple n a M _ S C D) → Orientation S :=
    Quot.lift O hrespect
  have hinj : Function.Injective F := by
    intro x y
    induction x using Quot.ind with | _ α =>
    induction y using Quot.ind with | _ β =>
    intro he
    apply Quot.sound
    apply hratio (O α).val α β
    · intro p v hv
      exact (hO α p v).mp hv
    · intro p v hv
      have hβ : IsPositive ((O β).val p) v := by
        change O α = O β at he
        rw [← he]
        exact hv
      exact (hO β p v).mp hβ
  have hsur : Function.Surjective F := by
    intro o
    obtain ⟨ω, hω⟩ := hsurj o
    exact ⟨Quot.mk _ ω, (huniq ω o hω).symm⟩
  let e := Equiv.ofBijective F ⟨hinj, hsur⟩
  exact ⟨e, hO⟩

/-- The quotient correspondence follows once positive representatives exist. -/
theorem top_form_quotient_from_positive_top_form
    (hpair : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.alternating_interpretationType.{u})
    (hcoeff : Specs.SmoothManifolds.Ch07.ExteriorAlgebra.smooth_iff_coefficientsType.{u})
    (hpos : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u}) :
    Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u} := by
  intro n a M _ S C D
  apply top_form_quotient_of_characters S C D
  · exact form_orientation_exists_unique hpair hcoeff S C D
  · intro o
    obtain ⟨ω, hω⟩ := (hpos S C D o.val).mp o.property
    refine ⟨ω, ?_⟩
    intro p v
    letI := (tangent_dimension S p).1
    exact @positive_ray_characterization (DeterminantLine S p) inferInstance inferInstance
      inferInstance (determinant_finrank S p) (o.val p)
      (exteriorPower.pairingDual ℝ (TangentSpace S p) n (ω.val.field p)) (hω p) v
  · intro r α β hα hβ
    obtain ⟨f, hf, hrel⟩ := exists_positive_ratio_of_positive_top_forms S C D r α β hα hβ
    refine ⟨f, ?_, hf, hrel⟩
    exact smooth_scalar_of_smul_relation hcoeff S C D α.val β.val f hrel (topIndex n)
      (fun c hc p => coefficients_top_ne_zero C c hc α.val.field α.property p)


theorem generators_orientation
    : Specs.SmoothManifolds.Orientations.Equivalences.generators_orientationType.{u} := by
  intro n a M _ S G
  obtain ⟨r, hr, hu⟩ := generators_ray_exists_unique G
  refine ⟨⟨r, continuous_of_represents_generators r G hr⟩, hr, ?_⟩
  intro o ho
  exact Subtype.ext (hu o.val ho)

theorem comparison
    : Specs.SmoothManifolds.Orientations.Equivalences.comparisonType.{u} := by
  intro n a M _ S o q
  exact ⟨comparison_locallyConstant o q, comparison_reconstruct o q⟩

theorem transition_jacobian
    : Specs.SmoothManifolds.Orientations.Equivalences.transition_jacobianType.{u} := by
  intro n a M _ S K c d hc hd p U F hU hpU hF hrep
  unfold transitionDeterminant
  apply congrArg LinearMap.det
  apply LinearMap.ext
  intro v
  have h := TangentBundle.transition_jacobian S K c d hc hd p.val
    p.property.1 p.property.2 U F hU hpU hF hrep
    ((K.equiv c hc p.val p.property.1).symm v)
  simpa using h

theorem empty
    : Specs.SmoothManifolds.Orientations.Equivalences.emptyType.{u} := by
  intro n a M _ _ S
  let r : RayField S := fun p => isEmptyElim p
  have hr : IsContinuousRayField r := by
    intro K c hc
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro p
    exact False.elim (isEmptyElim p.val : False)
  refine ⟨⟨⟨r, hr⟩⟩, ⟨?_⟩⟩
  intro o q
  exact Subtype.ext (funext (fun p => isEmptyElim p))

theorem connected_two
    : Specs.SmoothManifolds.Orientations.Equivalences.connected_twoType.{u} := by
  intro n a M _ _ S o
  let p₀ : M := Classical.choice inferInstance
  let e : Bool ≃ Orientation S := {
    toFun := fun b => if b then o else opposite o
    invFun := fun q => OrientationData.comparison o q p₀
    left_inv := by
      intro b
      cases b <;> simp [OrientationData.comparison, opposite, Module.Ray.ne_neg_self]
    right_inv := by
      intro q
      apply Subtype.ext
      funext p
      have hconst := (comparison_locallyConstant o q).apply_eq_of_preconnectedSpace p₀ p
      have hrec := comparison_reconstruct o q p
      change (if OrientationData.comparison o q p₀ then o else opposite o).val p = q.val p
      rw [hconst]
      cases hb : OrientationData.comparison o q p <;> simpa [hb] using hrec.symm }
  exact ⟨e, rfl, fun p => rfl⟩

theorem zero_dimension
    : Specs.SmoothManifolds.Orientations.Equivalences.zero_dimensionType.{u} := by
  intro a M _ S
  letI := _root_.SmoothManifolds.TopologicalManifold.toChartedSpace S.topologicalManifold
  letI : DiscreteTopology M := ChartedSpace.discreteTopology (ModelSpace 0 a) M
  let e₁ : Orientation S ≃ RayField S := {
    toFun := Subtype.val
    invFun := fun r => ⟨r, continuous_of_discrete r⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let e₂ : RayField S ≃ (M → Bool) :=
    Equiv.piCongrRight (fun p => (zeroRayEquiv S p).symm)
  refine ⟨e₁.trans e₂, ?_⟩
  intro o p
  change (zeroRayEquiv S p).symm (o.val p) = true ↔ _
  rw [Equiv.symm_apply_eq]
  constructor
  · intro h
    rw [h]
    exact zeroRayEquiv_true S p
  · rintro ⟨hv, h⟩
    exact h.symm

theorem positive_multiple
    : Specs.SmoothManifolds.Orientations.Equivalences.positive_multipleType.{u} := by
  intro n a M _ S C D α β
  let s : Setoid (NonvanishingTopForm D) :=
    ⟨PositiveMultiple, positiveMultiple_equivalence⟩
  constructor
  · intro h
    exact @Quotient.exact _ s α β h
  · exact Quot.sound

theorem signed_charts
    : Specs.SmoothManifolds.Orientations.Equivalences.signed_chartsType.{u} := by
  intro n a M _ S r
  exact signed_charts_equivalence S r

theorem signed_orientation
    : Specs.SmoothManifolds.Orientations.Equivalences.signed_orientationType.{u} := by
  intro n a M _ S s
  exact signed_orientation_exists_unique S s

theorem smooth_generators
    : Specs.SmoothManifolds.Orientations.Equivalences.smooth_generatorsType.{u} := by
  intro n a M _ S r
  exact smooth_generators_equivalence S r

theorem positive_top_form
    : Specs.SmoothManifolds.Orientations.Equivalences.positive_top_formType.{u} := by
  intro n a M _ S C D r
  constructor
  · exact positive_top_form_exists ExteriorAlgebraResults.smooth_iff_coefficients S C D r
  · rintro ⟨ω,hω⟩
    exact continuous_of_positive_top_form ExteriorAlgebraResults.smooth_iff_coefficients S C D r ω hω

theorem top_form_quotient
    : Specs.SmoothManifolds.Orientations.Equivalences.top_form_quotientType.{u} := by
  exact top_form_quotient_from_positive_top_form
    ExteriorAlgebraResults.alternating_interpretation
    ExteriorAlgebraResults.smooth_iff_coefficients positive_top_form


end SmoothManifolds.OrientationResults
