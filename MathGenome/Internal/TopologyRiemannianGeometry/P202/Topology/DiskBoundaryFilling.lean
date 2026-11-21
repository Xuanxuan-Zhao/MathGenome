import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.DiskBoundaryFilling
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HigherHomotopy
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Order.Interval.Set.IsoIoo

namespace P202.Topology

open P202Specs.Topology
open scoped unitInterval _root_.Topology

universe u v
noncomputable section

namespace DiskBoundaryFilling

abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

def sphereInDisk {n : ℕ} (z : UnitSphere n) : ClosedDisk n :=
  ⟨z.val, (mem_sphere_zero_iff_norm.mp z.property).le⟩

theorem continuous_sphereInDisk {n : ℕ} : Continuous (@sphereInDisk n) := by
  unfold sphereInDisk
  fun_prop

theorem sphereInDisk_mem {n : ℕ} (z : UnitSphere n) :
    sphereInDisk z ∈ DiskBoundary n :=
  mem_sphere_zero_iff_norm.mp z.property

def coneMap {n : ℕ} : C(unitInterval × UnitSphere n, ClosedDisk n) where
  toFun p := ⟨(p.1 : ℝ) • p.2.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1,
      mem_sphere_zero_iff_norm.mp p.2.property, mul_one]
    exact p.1.property.2⟩
  continuous_toFun := by fun_prop

theorem coneMap_surjective {n : ℕ} (s : UnitSphere n) :
    Function.Surjective (@coneMap n) := by
  intro z
  by_cases hz : z.val = 0
  · exact ⟨(0, s), Subtype.ext (by simpa [coneMap] using hz.symm)⟩
  · have hn : 0 < ‖z.val‖ := norm_pos_iff.mpr hz
    refine ⟨(⟨‖z.val‖, norm_nonneg _, z.property⟩,
      ⟨‖z.val‖⁻¹ • z.val, ?_⟩), ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      exact inv_mul_cancel₀ hn.ne'
    · apply Subtype.ext
      change ‖z.val‖ • (‖z.val‖⁻¹ • z.val) = z.val
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem coneMap_quotient {n : ℕ} (s : UnitSphere n) :
    Topology.IsQuotientMap (@coneMap n) :=
  coneMap.continuous.isClosedMap.isQuotientMap coneMap.continuous
    (coneMap_surjective s)

/-- A free null homotopy of the sphere gives a filling of its exact map.
Continuity at the cone vertex uses a quotient map; the target is arbitrary. -/
theorem sphere_filling_of_nullhomotopic {n : ℕ} {X : Type u} [TopologicalSpace X]
    (s : UnitSphere n) (b : C(UnitSphere n, X)) (h : b.Nullhomotopic) :
    ∃ g : C(ClosedDisk n, X), ∀ z : UnitSphere n, g (sphereInDisk z) = b z := by
  obtain ⟨x, ⟨H⟩⟩ := h
  let K : C(unitInterval × UnitSphere n, X) :=
    H.symm.toContinuousMap
  have hK : Function.FactorsThrough K (@coneMap n) := by
    intro p q hpq
    have hv : (p.1 : ℝ) • p.2.val = (q.1 : ℝ) • q.2.val := congrArg Subtype.val hpq
    have hn := congrArg norm hv
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg p.1.property.1,
      abs_of_nonneg q.1.property.1,
      mem_sphere_zero_iff_norm.mp p.2.property,
      mem_sphere_zero_iff_norm.mp q.2.property, mul_one] at hn
    have ht : p.1 = q.1 := Subtype.ext hn
    by_cases hp : p.1 = 0
    · have hq : q.1 = 0 := ht.symm.trans hp
      change H.symm (p.1, p.2) = H.symm (q.1, q.2)
      rw [hp, hq, H.symm.apply_zero, H.symm.apply_zero]
      rfl
    · have hp' : (p.1 : ℝ) ≠ 0 := fun h => hp (Subtype.ext h)
      have hs : p.2 = q.2 := by
        apply Subtype.ext
        rw [← ht] at hv
        exact (smul_right_injective _ hp') hv
      exact congrArg K (Prod.ext ht hs)
  let g := (coneMap_quotient s).lift K hK
  refine ⟨g, fun z => ?_⟩
  have he := DFunLike.congr_fun ((coneMap_quotient s).lift_comp K hK) (1, z)
  calc
    g (sphereInDisk z) = g (coneMap (1, z)) := by
      congr 1
      apply Subtype.ext
      simp [sphereInDisk, coneMap]
    _ = K (1, z) := he
    _ = b z := H.symm.apply_one z

/-- A quotient presentation of the sphere by a cube with its boundary collapsed.
This is geometric data about the source spaces only. -/
structure CubeSpherePresentation (n : ℕ) where
  map : C(UnitCube (n + 1), UnitSphere (n + 2))
  pole : UnitSphere (n + 2)
  surjective : Function.Surjective map
  boundary : ∀ z ∈ CubeBoundary (n + 1), map z = pole
  fibers : ∀ z w, map z = map w →
    z = w ∨ (z ∈ CubeBoundary (n + 1) ∧ w ∈ CubeBoundary (n + 1))

section SpherePresentation

open Set
open scoped OnePoint Classical

/-- Collapse the complement of an open subspace to the point at infinity. -/
def collapseOpen {T : Type*} (U : Set T) (z : T) : OnePoint U :=
  if h : z ∈ U then (⟨z, h⟩ : U) else ∞

theorem continuous_collapseOpen {T : Type*} [TopologicalSpace T] [T2Space T]
    {U : Set T} (hU : IsOpen U) : Continuous (collapseOpen U) := by
  classical
  apply continuous_def.mpr
  intro V hV
  by_cases hv : (∞ : OnePoint U) ∈ V
  · have hc := ((OnePoint.isOpen_iff_of_mem hv).mp hV).2
    have he : collapseOpen U ⁻¹' V =
        (Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V)ᶜ)ᶜ := by
      ext z
      by_cases hz : z ∈ U
      · simp [collapseOpen, hz, Set.mem_image]
      · simp [collapseOpen, hz, hv, Set.mem_image]
    rw [he]
    exact (hc.image continuous_subtype_val).isClosed.isOpen_compl
  · have he : collapseOpen U ⁻¹' V =
        Subtype.val '' (((↑) : U → OnePoint U) ⁻¹' V) := by
      ext z
      by_cases hz : z ∈ U
      · simp [collapseOpen, hz, Set.mem_image]
      · simp [collapseOpen, hz, hv, Set.mem_image]
    rw [he]
    exact hU.isOpenMap_subtype_val _ ((OnePoint.isOpen_iff_of_notMem hv).mp hV)

theorem collapseOpen_surjective {T : Type*} {U : Set T} (s : T) (hs : s ∉ U) :
    Function.Surjective (collapseOpen U) := by
  classical
  intro z
  induction z using OnePoint.rec with
  | infty => exact ⟨s, by simp [collapseOpen, hs]⟩
  | coe z => exact ⟨z.val, by simp [collapseOpen, z.property]⟩

theorem collapseOpen_fibers {T : Type*} {U : Set T} {z w : T}
    (h : collapseOpen U z = collapseOpen U w) :
    z = w ∨ (z ∉ U ∧ w ∉ U) := by
  classical
  by_cases hz : z ∈ U <;> by_cases hw : w ∈ U
  · left
    have he : (⟨z, hz⟩ : U) = ⟨w, hw⟩ := OnePoint.coe_injective (by
      simpa only [collapseOpen, dite_eq_left hz, dite_eq_left hw] using h)
    exact congrArg Subtype.val he
  · simp [collapseOpen, hz, hw] at h
  · simp [collapseOpen, hz, hw] at h
  · exact Or.inr ⟨hz, hw⟩

def openCube (n : ℕ) : Set (UnitCube n) :=
  {z | ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1}

theorem isOpen_openCube (n : ℕ) : IsOpen (openCube n) := by
  have he : openCube n = ⋂ i : Fin n,
      {z : UnitCube n | (z i : ℝ) ∈ Ioo 0 1} := by ext; simp [openCube]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_Ioo.preimage (by fun_prop))

theorem notMem_openCube_iff {n : ℕ} (z : UnitCube n) :
    z ∉ openCube n ↔ z ∈ CubeBoundary n := by
  classical
  change (¬ ∀ i, 0 < (z i : ℝ) ∧ (z i : ℝ) < 1) ↔ ∃ i, z i = 0 ∨ z i = 1
  constructor
  · intro h
    push Not at h
    obtain ⟨i, hi⟩ := h
    by_cases h0 : 0 < (z i : ℝ)
    · exact ⟨i, Or.inr (Subtype.ext (le_antisymm (z i).property.2 (hi h0)))⟩
    · exact ⟨i, Or.inl (Subtype.ext (le_antisymm (not_lt.mp h0) (z i).property.1))⟩
  · rintro ⟨i, hi | hi⟩ h
    · simpa [hi] using (h i).1
    · simpa [hi] using (h i).2

/-- Affine coordinates identify the open cube with a product of open intervals. -/
def openCubeIntervalHomeo (n : ℕ) :
    (openCube n) ≃ₜ (Fin n → Ioo (-1 : ℝ) 1) where
  toFun z i := ⟨2 * (z.val i : ℝ) - 1, by
    have h := z.property i
    constructor <;> linarith⟩
  invFun z := ⟨fun i => ⟨((z i : ℝ) + 1) / 2, by
    rcases (z i).property with ⟨h0, h1⟩
    constructor <;> linarith⟩, fun i => by
      rcases (z i).property with ⟨h0, h1⟩
      constructor <;> dsimp <;> linarith⟩
  left_inv z := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    dsimp
    ring
  right_inv z := by
    funext i
    apply Subtype.ext
    dsimp
    ring
  continuous_toFun := by
    apply continuous_pi
    intro i
    apply Continuous.subtype_mk
    have hc : Continuous (fun z : openCube n => (z.val i : ℝ)) :=
      continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)
    exact (hc.const_mul 2).sub continuous_const
  continuous_invFun := by fun_prop

def openCubeEuclideanHomeo (n : ℕ) : (openCube n) ≃ₜ (Fin n → ℝ) :=
  (openCubeIntervalHomeo n).trans
    (Homeomorph.piCongrRight (fun _ => (orderIsoIooNegOneOne ℝ).symm.toHomeomorph))

/-- Collapsing exactly the cube boundary gives the ordinary Euclidean sphere.
The proof uses the one-point compactification of the open cube. -/
def cubeSpherePresentation (n : ℕ) : CubeSpherePresentation n := by
  classical
  let e : OnePoint (openCube (n + 1)) ≃ₜ UnitSphere (n + 2) :=
    (openCubeEuclideanHomeo (n + 1)).onePointCongr.trans
      (onePointEquivSphereOfFinrankEq (by simp))
  refine {
    map := ⟨e ∘ collapseOpen (openCube (n + 1)),
      e.continuous.comp (continuous_collapseOpen (isOpen_openCube (n + 1)))⟩
    pole := e ∞
    surjective := e.surjective.comp (collapseOpen_surjective (fun _ => 0) ?_)
    boundary := ?_
    fibers := ?_ }
  · apply (notMem_openCube_iff _).mpr
    exact ⟨0, Or.inl rfl⟩
  · intro z hz
    change e (collapseOpen _ z) = e ∞
    rw [collapseOpen, dite_eq_right ((notMem_openCube_iff z).mpr hz)]
  · intro z w h
    have he : collapseOpen (openCube (n + 1)) z =
        collapseOpen (openCube (n + 1)) w := e.injective h
    rcases collapseOpen_fibers he with h | ⟨hz, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨(notMem_openCube_iff z).mp hz, (notMem_openCube_iff w).mp hw⟩

end SpherePresentation

variable {X : Type u} [TopologicalSpace X]

/-- Free null homotopy of a based cube still forces its based class to be zero.
The change-of-basepoint isomorphism sends zero to zero. -/
theorem cubeClass_eq_one_of_moving {n : ℕ} {x y : X} (d : Path x y)
    (a : CubeMap (n + 1) x)
    (H : MovingCubeHomotopy d a (GenLoop.const : CubeMap (n + 1) y)) :
    cubeClass a = 1 := by
  obtain ⟨E, hE⟩ := higherBasepointTransport n X x y d
  apply E.injective
  rw [E.map_one, hE a GenLoop.const ⟨H⟩]
  rfl

/-- Descending a boundary-fixed null homotopy along the collapsed-boundary
presentation gives an actual sphere null homotopy in the arbitrary target. -/
theorem sphere_null_of_cube_null {n : ℕ} (q : CubeSpherePresentation n)
    (b : C(UnitSphere (n + 2), X))
    (a : CubeMap (n + 1) (b q.pole)) (ha : ∀ z, a z = b (q.map z))
    (H : CubeHomotopy a (GenLoop.const : CubeMap (n + 1) (b q.pole))) :
    b.Nullhomotopic := by
  let Q : C(unitInterval × UnitCube (n + 1), unitInterval × UnitSphere (n + 2)) :=
    ⟨fun p => (p.1, q.map p.2), continuous_fst.prodMk
      (q.map.continuous.comp continuous_snd)⟩
  have hQ : Topology.IsQuotientMap Q :=
    .of_surjective_continuous (fun p => by
      obtain ⟨z, hz⟩ := q.surjective p.2
      exact ⟨(p.1, z), Prod.ext rfl hz⟩) Q.continuous
  have hf : Function.FactorsThrough H.toContinuousMap Q := by
    intro p r h
    have ht : p.1 = r.1 := congrArg (fun p : unitInterval × UnitSphere (n + 2) => p.1) h
    have hz : q.map p.2 = q.map r.2 := congrArg (fun p : unitInterval × UnitSphere (n + 2) => p.2) h
    rcases q.fibers p.2 r.2 hz with hz | ⟨hp, hr⟩
    · exact congrArg H (Prod.ext ht hz)
    · change H (p.1, p.2) = H (r.1, r.2)
      rw [H.eq_fst _ hp, H.eq_fst _ hr]
      exact (GenLoop.boundary a _ hp).trans (GenLoop.boundary a _ hr).symm
  let K := hQ.lift H.toContinuousMap hf
  have hK (t : unitInterval) (z : UnitCube (n + 1)) : K (t, q.map z) = H (t, z) :=
    DFunLike.congr_fun (hQ.lift_comp H.toContinuousMap hf) (t, z)
  refine ⟨b q.pole, ⟨{
    toContinuousMap := K
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro z
    obtain ⟨w, rfl⟩ := q.surjective z
    exact (hK 0 w).trans ((H.apply_zero w).trans (ha w))
  · intro z
    obtain ⟨w, rfl⟩ := q.surjective z
    exact (hK 1 w).trans (H.apply_one w)

/-- Injectivity for the actual inclusion reflects free null homotopies of sphere
maps, after the boundary is collapsed and the moving basepoint is followed. -/
theorem sphere_null_reflected {Y : Type u} [TopologicalSpace Y] {A : Set Y}
    {n : ℕ} (q : CubeSpherePresentation n)
    (hinj : ∀ x : A, Function.Injective
      (higherInduced n
        (⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩ : PointedMap A Y x x.val)))
    (b : C(UnitSphere (n + 2), A))
    (h : ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp b).Nullhomotopic) :
    b.Nullhomotopic := by
  let x : A := b q.pole
  let incl : PointedMap A Y x x.val := ⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩
  let a : CubeMap (n + 1) x :=
    ⟨b.comp q.map, fun z hz => congrArg b (q.boundary z hz)⟩
  obtain ⟨y, ⟨H⟩⟩ := h
  let d : Path x.val y :=
    { toFun := fun t => H (t, q.pole)
      continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
      source' := H.apply_zero q.pole
      target' := H.apply_one q.pole }
  let M : MovingCubeHomotopy d (cubeMap incl a) (GenLoop.const : CubeMap (n + 1) y) :=
    { toFun := fun p => H (p.1, q.map p.2)
      continuous_toFun := H.continuous.comp
        (continuous_fst.prodMk (q.map.continuous.comp continuous_snd))
      map_zero_left := fun z => H.apply_zero (q.map z)
      map_one_left := fun z => H.apply_one (q.map z)
      boundary := fun t z hz => congrArg (fun s => H (t, s)) (q.boundary z hz) }
  have hy : higherInduced n incl (cubeClass a) = 1 :=
    (higherInducedFormula n A Y x x.val incl a).trans
      (cubeClass_eq_one_of_moving d (cubeMap incl a) M)
  have ha : cubeClass a = cubeClass (GenLoop.const : CubeMap (n + 1) x) := by
    apply hinj x
    exact hy.trans (map_one (higherInduced n incl)).symm
  obtain ⟨K⟩ := (higherClassEquality _ _ _ _ _).mp ha
  exact sphere_null_of_cube_null q b a (fun _ => rfl) K

def boundaryMap {Y : Type u} [TopologicalSpace Y] {A : Set Y} {n : ℕ}
    (f : RelativeDiskMap n A) : C(UnitSphere n, A) where
  toFun z := ⟨f.val (sphereInDisk z), f.property _ (sphereInDisk_mem z)⟩
  continuous_toFun := (f.val.continuous.comp continuous_sphereInDisk).subtype_mk _

/-- The given filled disk supplies a free radial contraction of its boundary. -/
theorem boundaryMap_null_in_ambient {Y : Type u} [TopologicalSpace Y]
    {A : Set Y} {n : ℕ} (f : RelativeDiskMap n A) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(A, Y)).comp (boundaryMap f)).Nullhomotopic := by
  let center : ClosedDisk n := ⟨0, by simp⟩
  refine ⟨f.val center, ⟨{
    toFun := fun p => f.val (coneMap (unitInterval.symm p.1, p.2))
    continuous_toFun := f.val.continuous.comp
      (coneMap.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro z
    change f.val _ = f.val _
    congr 1
    apply Subtype.ext
    simp [coneMap, sphereInDisk]
  · intro z
    change f.val _ = f.val center
    congr 1
    apply Subtype.ext
    simp [coneMap, center]

theorem boundaryFilling_of_presentation {Y : Type u} [TopologicalSpace Y]
    (A : Set Y) (n : ℕ) (q : CubeSpherePresentation n)
    (hinj : ∀ x : A, Function.Injective
      (higherInduced n
        (⟨⟨Subtype.val, continuous_subtype_val⟩, rfl⟩ : PointedMap A Y x x.val)))
    (f : RelativeDiskMap (n + 2) A) :
    ∃ g : C(ClosedDisk (n + 2), A),
      ∀ z ∈ DiskBoundary (n + 2), (g z).val = f.val z := by
  have hnull := sphere_null_reflected q hinj (boundaryMap f) (boundaryMap_null_in_ambient f)
  obtain ⟨g, hg⟩ := sphere_filling_of_nullhomotopic q.pole (boundaryMap f) hnull
  refine ⟨g, fun z hz => ?_⟩
  let s : UnitSphere (n + 2) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  exact congrArg Subtype.val (hg s)

end DiskBoundaryFilling

theorem diskBoundaryFilling : ExpectedDiskBoundaryFilling.boundaryFilling.{u} := by
  intro Y _ A n hinj f
  exact DiskBoundaryFilling.boundaryFilling_of_presentation A n
    (DiskBoundaryFilling.cubeSpherePresentation n) hinj f

end
end P202.Topology
