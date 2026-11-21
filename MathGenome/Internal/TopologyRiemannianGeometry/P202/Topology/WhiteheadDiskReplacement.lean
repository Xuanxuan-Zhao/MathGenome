import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.WhiteheadDiskReplacement
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HigherHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.DiskBoundaryFilling
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.DiskFillingCorrection

namespace P202.Topology

open P202Specs.Topology
open scoped unitInterval _root_.Topology

universe u
noncomputable section
variable {Y : Type u} [TopologicalSpace Y]

/-- Extract the π₁ surjectivity with the paper's path convention from the
canonical one-cube homomorphism in the weak equivalence hypothesis. -/
theorem inclusion_piOne_surjective {A : Set Y}
    (h : IsWeakHomotopyEquivalenceInclusion A) (x : A) :
    Function.Surjective (pointedSubspaceInclusion x).induced := by
  intro b
  obtain ⟨a, ha⟩ := (h.2 0 x).2 ((higherPiOneEquiv x.val).symm b)
  refine ⟨higherPiOneEquiv x a, ?_⟩
  rw [← higherPiOneNaturality A Y x x.val (pointedSubspaceInclusion x), ha]
  exact (higherPiOneEquiv x.val).apply_symm_apply b

theorem inclusion_basedCubeLift : ExpectedDiskReplacement.basedCubeLift.{u} := by
  intro Y _ A h n x a
  obtain ⟨c, hc⟩ := (h.2 n x).2 (cubeClass a)
  obtain ⟨b, rfl⟩ := cubeClass_surjective c
  refine ⟨b, (higherClassEquality (n + 1) Y x.val a _).mp ?_⟩
  exact hc.symm

theorem inclusion_basedCubeNull : ExpectedDiskReplacement.basedCubeNull.{u} := by
  intro Y _ A h n x a ha
  apply (higherClassEquality (n + 1) A x a GenLoop.const).mp
  apply (h.2 n x).1
  have he := (higherClassEquality (n + 1) Y x.val _ GenLoop.const).mpr ha
  rw [higherInducedFormula, (higherGroupConvention n A x).2.1, map_one]
  exact he.trans (higherGroupConvention n Y x.val).2.1

/-- The component hypothesis supplies a point of the subspace and an actual
path to it, for every point of the ambient space. -/
theorem exists_path_to_subspace {A : Set Y}
    (h : Function.Surjective (componentMap (subspaceInclusion A))) (y : Y) :
    ∃ x : A, Nonempty (Path y x.val) := by
  obtain ⟨c, hc⟩ := h (ZerothHomotopy.mk y)
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective c
  change ZerothHomotopy.mk x.val = ZerothHomotopy.mk y at hc
  exact ⟨x, (higherComponents.{u,u}.1 Y y x.val).mp hc.symm⟩

/-- A path in Y with endpoints in A can be replaced by a path in A. The first
step uses component injectivity; the correction loop uses π₁ surjectivity. -/
theorem pathReplacement : ExpectedDiskReplacement.pathReplacement.{u} := by
  intro Y _ A hc hp x y p
  have hxy : ZerothHomotopy.mk x = ZerothHomotopy.mk y := by
    apply hc
    exact (higherComponents.{u,u}.1 Y x.val y.val).mpr ⟨p⟩
  obtain ⟨g⟩ := (higherComponents.{u,u}.1 A x y).mp hxy
  let gy : Path x.val y.val := g.map continuous_subtype_val
  obtain ⟨l, hl⟩ := hp x (loopClass (p.trans gy.symm))
  obtain ⟨ell, rfl⟩ := loopClass_surjective l
  have hloop : Path.Homotopic.Quotient.mk (ell.map continuous_subtype_val) =
      (Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk gy).symm := by
    have he := congrArg pathClass hl
    rw [inducedFormula A Y x x.val (pointedSubspaceInclusion x) ell] at he
    simpa only [pathClass_loopClass, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.mk_cast,
      pointedSubspaceInclusion, subspaceInclusion,
      Path.cast_rfl_rfl, Path.Homotopic.Quotient.cast_rfl_rfl] using he
  refine ⟨ell.trans g, Path.Homotopic.Quotient.eq.mp ?_⟩
  rw [Path.map_trans, Path.Homotopic.Quotient.mk_trans, hloop]
  change Path.Homotopic.Quotient.mk p =
    ((Path.Homotopic.Quotient.mk p).trans (Path.Homotopic.Quotient.mk gy).symm).trans
      (Path.Homotopic.Quotient.mk gy)
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- The zero-disk has one point and empty boundary. -/
theorem diskReplacement_zero : ExpectedDiskReplacement.zero.{u} := by
  intro Y _ A hc f
  let z : ClosedDisk 0 := ⟨0, by simp⟩
  obtain ⟨x, ⟨p⟩⟩ := exists_path_to_subspace hc (f.val z)
  refine ⟨ContinuousMap.const _ x, ⟨{
    toFun := fun a => p a.1
    continuous_toFun := p.continuous.comp continuous_fst
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro w
    have hw : w = z := Subtype.ext (Subsingleton.elim _ _)
    simpa only [hw] using p.source
  · intro w
    exact p.target
  · intro t w hw
    have hz : w.val = 0 := Subsingleton.elim _ _
    change ‖w.val‖ = 1 at hw
    simp [hz] at hw

namespace DiskOne

theorem norm_eq_abs (z : EuclideanSpace ℝ (Fin 1)) : ‖z‖ = |z 0| := by
  simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

/-- Affine parametrization of the literal Euclidean disk by [0,1]. -/
def ofInterval : C(unitInterval, ClosedDisk 1) where
  toFun t := ⟨WithLp.toLp 2 (fun _ => 2 * (t : ℝ) - 1), by
    rw [norm_eq_abs]
    change |2 * (t : ℝ) - 1| ≤ 1
    rw [abs_le]
    constructor <;> have h0 := t.property.1 <;> have h1 := t.property.2 <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 _).comp
    fun_prop

/-- Inverse affine parameter. -/
def toInterval : C(ClosedDisk 1, unitInterval) where
  toFun z := ⟨(z.val 0 + 1) / 2, by
    have h := z.property
    rw [norm_eq_abs, abs_le] at h
    constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

@[simp] theorem toInterval_ofInterval (t : unitInterval) :
    toInterval (ofInterval t) = t := by
  apply Subtype.ext
  change (2 * (t : ℝ) - 1 + 1) / 2 = t
  ring

@[simp] theorem ofInterval_toInterval (z : ClosedDisk 1) :
    ofInterval (toInterval z) = z := by
  apply Subtype.ext
  ext i
  fin_cases i
  change 2 * ((z.val 0 + 1) / 2) - 1 = z.val 0
  ring

theorem boundary_iff (z : ClosedDisk 1) :
    z ∈ DiskBoundary 1 ↔ toInterval z = 0 ∨ toInterval z = 1 := by
  change ‖z.val‖ = 1 ↔ _
  rw [norm_eq_abs]
  constructor
  · intro h
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp h with h | h
    · right
      apply Subtype.ext
      change (z.val 0 + 1) / 2 = 1
      linarith
    · left
      apply Subtype.ext
      change (z.val 0 + 1) / 2 = 0
      linarith
  · rintro (h | h)
    all_goals
      have he := congrArg (fun t : unitInterval => (t : ℝ)) h
      change (z.val 0 + 1) / 2 = _ at he
      norm_num at he
    · have hz : z.val 0 = -1 := by linarith
      simp [hz]
    · have hz : z.val 0 = 1 := by linarith
      simp [hz]

theorem boundary_zero : ofInterval 0 ∈ DiskBoundary 1 :=
  (boundary_iff _).mpr (Or.inl (toInterval_ofInterval 0))

theorem boundary_one : ofInterval 1 ∈ DiskBoundary 1 :=
  (boundary_iff _).mpr (Or.inr (toInterval_ofInterval 1))

end DiskOne

/-- Transfer the endpoint-fixed path homotopy back to the Euclidean one-disk.
In particular the relative condition fixes each boundary point individually. -/
theorem diskReplacement_one : ExpectedDiskReplacement.one.{u} := by
  intro Y _ A h f
  let x : A := ⟨f.val (DiskOne.ofInterval 0), f.property _ DiskOne.boundary_zero⟩
  let y : A := ⟨f.val (DiskOne.ofInterval 1), f.property _ DiskOne.boundary_one⟩
  let p : Path x.val y.val := {
    toContinuousMap := f.val.comp DiskOne.ofInterval
    source' := rfl
    target' := rfl }
  obtain ⟨q, ⟨H⟩⟩ := pathReplacement Y A h.1.1
    (inclusion_piOne_surjective h) x y p
  refine ⟨q.toContinuousMap.comp DiskOne.toInterval, ⟨{
    toFun := fun a => H (a.1, DiskOne.toInterval a.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (DiskOne.toInterval.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro z
    change H (0, DiskOne.toInterval z) = f.val z
    rw [H.apply_zero]
    change f.val (DiskOne.ofInterval (DiskOne.toInterval z)) = f.val z
    rw [DiskOne.ofInterval_toInterval]
  · intro z
    exact H.apply_one _
  · intro t z hz
    have he : f.val z = p (DiskOne.toInterval z) := by
      change f.val z = f.val (DiskOne.ofInterval (DiskOne.toInterval z))
      rw [DiskOne.ofInterval_toInterval]
    change H (t, DiskOne.toInterval z) = f.val z
    rw [he]
    apply H.eq_fst
    exact (DiskOne.boundary_iff z).mp hz

/-- Disk replacement in every dimension. In dimensions at least two,
injectivity fills the boundary and surjectivity corrects that filling
by a homotopy fixing the entire original boundary. -/
theorem diskReplacement : ExpectedDiskReplacement.diskReplacement.{u} := by
  intro Y _ A h n
  cases n with
  | zero => exact diskReplacement_zero Y A h.1.2
  | succ n =>
    cases n with
    | zero => exact diskReplacement_one Y A h
    | succ n =>
      intro f
      -- Injectivity on π_(n+1) gives a filling with exactly the old boundary.
      obtain ⟨g, hg⟩ := diskBoundaryFilling Y A n (fun x => (h.2 n x).1) f
      -- Surjectivity on π_(n+2) corrects the difference of the two fillings.
      -- The correction must produce a homotopy fixing the *entire* boundary.
      exact diskFillingCorrection Y A n (fun x => (h.2 (n + 1) x).2) f g hg

end
end P202.Topology
