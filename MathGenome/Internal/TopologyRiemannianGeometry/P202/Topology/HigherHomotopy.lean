import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HigherHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.FundamentalGroupoid

namespace P202.Topology
open P202Specs.Topology
open scoped unitInterval _root_.Topology

universe u v w
noncomputable section
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Every class has an actual boundary-constant cube representative. -/
theorem cubeClass_surjective {n : ℕ} {x : X} :
    Function.Surjective (cubeClass : CubeMap n x → HigherPi n X x) := by
  intro a
  obtain ⟨p, hp⟩ := Quotient.mk_surjective a.unop
  exact ⟨p, congrArg MulOpposite.op hp⟩

theorem higherClassEquality : ExpectedHigher.classEquality.{u} := by
  intro n X _ x a b
  exact MulOpposite.op_inj.trans Quotient.eq

theorem higherGroupConvention : ExpectedHigher.groupConvention.{u} := by
  intro n X _ x
  refine ⟨?_, rfl, ?_⟩
  · intro i a b
    apply MulOpposite.unop_injective
    exact (HomotopyGroup.mul_spec (i := i)).symm
  · intro i a
    apply MulOpposite.unop_injective
    exact (HomotopyGroup.inv_spec (i := i)).symm

theorem higherInducedFormula : ExpectedHigher.inducedFormula.{u,v} := by
  intro n X Y _ _ x y f a
  rfl

@[simp] theorem cubeMap_id {n : ℕ} {x : X} (a : CubeMap n x) :
    cubeMap (PointedMap.id x) a = a := by
  ext t
  rfl

@[simp] theorem cubeMap_comp {n : ℕ} {x : X} {y : Y} {z : Z}
    (f : PointedMap X Y x y) (g : PointedMap Y Z y z) (a : CubeMap n x) :
    cubeMap (g.comp f) a = cubeMap g (cubeMap f a) := by
  ext t
  rfl

@[simp] theorem higherInduced_id (n : ℕ) (x : X) :
    higherInduced n (PointedMap.id x) = MonoidHom.id (HigherPi (n + 1) X x) := by
  ext a
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  change cubeClass (cubeMap (PointedMap.id x) a) = cubeClass a
  rw [cubeMap_id]

@[simp] theorem higherInduced_comp (n : ℕ) {x : X} {y : Y} {z : Z}
    (f : PointedMap X Y x y) (g : PointedMap Y Z y z) :
    higherInduced n (g.comp f) = (higherInduced n g).comp (higherInduced n f) := by
  ext a
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  change cubeClass (cubeMap (g.comp f) a) = cubeClass (cubeMap g (cubeMap f a))
  rw [cubeMap_comp]

theorem higherFunctoriality : ExpectedHigher.functoriality.{u,v,w} :=
  ⟨fun _ _ _ _ => higherInduced_id _ _,
    fun _ _ _ _ _ _ _ _ _ _ f g => higherInduced_comp _ f g⟩

/-- Restrict the target homotopy to any cube. Constancy on its boundary follows
from the fact that the target homotopy fixes the basepoint. -/
def cubeBasedHomotopy {n : ℕ} {x : X} {y : Y} (f g : PointedMap X Y x y)
    (H : f.BasedHomotopy g) (a : CubeMap n x) :
    CubeHomotopy (cubeMap f a) (cubeMap g a) where
  toFun p := H (p.1, a p.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (a.val.continuous.comp continuous_snd))
  map_zero_left t := H.apply_zero (a t)
  map_one_left t := H.apply_one (a t)
  prop' t z hz := by
    change H (t, a z) = f.map (a z)
    have ha : a z = x := GenLoop.boundary a z hz
    rw [ha]
    exact H.eq_fst t (Set.mem_singleton x)

theorem higherBasedHomotopy : ExpectedHigher.basedHomotopy.{u,v} := by
  intro n X Y _ _ x y f g ⟨H⟩
  ext a
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  exact (higherClassEquality _ _ _ _ _).mpr ⟨cubeBasedHomotopy f g H a⟩

theorem higherPointedEquivalence : ExpectedHigher.pointedEquivalence.{u,v} := by
  intro n X Y _ _ x y e
  have hl : (higherInduced n e.backward).comp (higherInduced n e.forward) =
      MonoidHom.id (HigherPi (n + 1) X x) := by
    rw [← higherInduced_comp]
    exact (higherBasedHomotopy n X X x x _ _ ⟨e.left⟩).trans (higherInduced_id n x)
  have hr : (higherInduced n e.forward).comp (higherInduced n e.backward) =
      MonoidHom.id (HigherPi (n + 1) Y y) := by
    rw [← higherInduced_comp]
    exact (higherBasedHomotopy n Y Y y y _ _ ⟨e.right⟩).trans (higherInduced_id n y)
  refine ⟨{
    toFun := higherInduced n e.forward
    invFun := higherInduced n e.backward
    left_inv := fun a => DFunLike.congr_fun hl a
    right_inv := fun b => DFunLike.congr_fun hr b
    map_mul' := (higherInduced n e.forward).map_mul }, fun _ => rfl, fun _ => rfl⟩

theorem higherPiOneFormula : ExpectedHigher.piOneFormula.{u} := by
  intro X _ x a
  rfl

/-- Postcomposition of a one-cube gives the same actual path as the π₁ map. -/
theorem cubeMap_one_loop {x : X} {y : Y} (f : PointedMap X Y x y) (a : CubeMap 1 x) :
    genLoopEquivOfUnique (Fin 1) (cubeMap f a) =
      (((genLoopEquivOfUnique (Fin 1) a).map f.map.continuous).cast
        f.point.symm f.point.symm) := by
  ext t
  rfl

theorem higherPiOneNaturality : ExpectedHigher.piOneNaturality.{u,v} := by
  intro X Y _ _ x y f a
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  rw [higherInducedFormula 0 X Y x y f a, higherPiOneFormula,
    higherPiOneFormula, inducedFormula]
  rw [cubeMap_one_loop]

theorem higherComponents : ExpectedHigher.components.{u,v} := by
  refine ⟨?_, ?_⟩
  · intro X _ x y
    exact Quotient.eq
  · intro X Y _ _ f g ⟨H⟩
    funext a
    exact Quotient.inductionOn a fun x => Quotient.sound ⟨H.evalAt x⟩

theorem relativePathEquality : ExpectedHigher.relativePathEquality.{u} := by
  intro X _ A x a b
  exact Quotient.eq

/-! Concentric cubes and their collars. The thickness ranges from zero to
one-half the radius. Keeping the denominator at least one-half avoids a
singularity when the collar has zero width. -/
namespace CubeCollar

private def radius {n : ℕ} (z : UnitCube (n + 1)) : ℝ :=
  ‖fun i => 2 * (z i : ℝ) - 1‖

private theorem radius_le_one {n : ℕ} (z : UnitCube (n + 1)) : radius z ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> have h0 := (z i).property.1 <;> have h1 := (z i).property.2 <;> linarith

private theorem radius_boundary {n : ℕ} {z : UnitCube (n + 1)}
    (hz : z ∈ CubeBoundary (n + 1)) : radius z = 1 := by
  apply le_antisymm (radius_le_one z)
  obtain ⟨i, hi | hi⟩ := hz
  all_goals
    have h := norm_le_pi_norm (fun j => 2 * (z j : ℝ) - 1) i
    change _ ≤ radius z at h
    norm_num [hi] at h ⊢
    exact h

private def expand {n : ℕ} (s : unitInterval) (z : UnitCube (n + 1)) : UnitCube (n + 1) :=
  fun i => Set.projIcc 0 1 zero_le_one (((z i : ℝ) - s / 4) / (1 - s / 2))

private theorem denominator_pos (s : unitInterval) : 0 < 1 - (s : ℝ) / 2 := by
  have := s.property.2
  linarith

private theorem expand_zero {n : ℕ} (z : UnitCube (n + 1)) : expand 0 z = z := by
  ext i
  simp [expand]

private theorem expand_boundary {n : ℕ} (s : unitInterval) (z : UnitCube (n + 1))
    (hz : radius z = 1 - (s : ℝ) / 2) : expand s z ∈ CubeBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := (IsGreatest.pi_norm (fun j => 2 * (z j : ℝ) - 1)).1
  change ‖2 * (z i : ℝ) - 1‖ = radius z at hi
  rw [Real.norm_eq_abs, hz] at hi
  have hd := denominator_pos s
  rcases le_total 0 (2 * (z i : ℝ) - 1) with h | h
  · rw [abs_of_nonneg h] at hi
    refine ⟨i, Or.inr ?_⟩
    change Set.projIcc 0 1 zero_le_one _ = 1
    have he : ((z i : ℝ) - s / 4) / (1 - s / 2) = 1 := by
      apply (div_eq_iff (ne_of_gt hd)).mpr
      linarith
    rw [he]
    exact Set.projIcc_right _
  · rw [abs_of_nonpos h] at hi
    refine ⟨i, Or.inl ?_⟩
    change Set.projIcc 0 1 zero_le_one _ = 0
    have he : ((z i : ℝ) - s / 4) / (1 - s / 2) = 0 := by
      apply (div_eq_zero_iff).mpr
      left
      linarith
    rw [he]
    exact Set.projIcc_left _

private theorem continuous_radius {n : ℕ} : Continuous (@radius n) := by
  unfold radius
  fun_prop

private theorem continuous_expand {n : ℕ} :
    Continuous (fun p : unitInterval × UnitCube (n + 1) => expand p.1 p.2) := by
  apply continuous_pi
  intro i
  exact continuous_projIcc.comp (((continuous_apply i).comp continuous_snd).subtype_val.sub
    (continuous_fst.subtype_val.div_const 4) |>.div
      (continuous_const.sub (continuous_fst.subtype_val.div_const 2))
        (fun p => ne_of_gt (denominator_pos p.1)))

private def paste {T : Type*} {n : ℕ} (c : T → unitInterval)
    (A : T × UnitCube (n + 1) → X) (B : T × unitInterval → X)
    (p : T × UnitCube (n + 1)) : X :=
  if radius p.2 ≤ 1 - (c p.1 : ℝ) / 2 then A (p.1, expand (c p.1) p.2)
  else B (p.1, Set.projIcc 0 1 zero_le_one (2 * radius p.2 - 2 + c p.1))

private theorem continuous_paste {T : Type*} [TopologicalSpace T] {n : ℕ}
    (c : T → unitInterval) (A : T × UnitCube (n + 1) → X) (B : T × unitInterval → X)
    (hc : Continuous c) (hA : Continuous A) (hB : Continuous B)
    (hAB : ∀ t z, z ∈ CubeBoundary (n + 1) → A (t, z) = B (t, 0)) :
    Continuous (paste c A B) := by
  apply continuous_if_le (continuous_radius.comp continuous_snd)
    (continuous_const.sub ((hc.comp continuous_fst).subtype_val.div_const 2))
  · exact (hA.comp (continuous_fst.prodMk
      (continuous_expand.comp ((hc.comp continuous_fst).prodMk continuous_snd)))).continuousOn
  · exact (hB.comp (continuous_fst.prodMk (continuous_projIcc.comp
      (((continuous_radius.comp continuous_snd).const_mul 2).sub continuous_const |>.add
        (hc.comp continuous_fst).subtype_val)))).continuousOn
  · intro p hp
    change radius p.2 = 1 - (c p.1 : ℝ) / 2 at hp
    rw [hAB p.1 _ (expand_boundary _ _ hp)]
    congr 2
    have he : 2 * radius p.2 - 2 + (c p.1 : ℝ) = 0 := by linarith
    rw [he]
    exact (Set.projIcc_left _).symm

omit [TopologicalSpace X] in
private theorem paste_boundary {T : Type*} {n : ℕ}
    (c : T → unitInterval) (A : T × UnitCube (n + 1) → X) (B : T × unitInterval → X)
    (hAB : ∀ t z, z ∈ CubeBoundary (n + 1) → A (t, z) = B (t, 0))
    (t : T) (z : UnitCube (n + 1)) (hz : z ∈ CubeBoundary (n + 1)) :
    paste c A B (t, z) = B (t, c t) := by
  unfold paste
  rw [radius_boundary hz]
  split_ifs with h
  · have hc : c t = 0 := by
      apply Subtype.ext
      change (c t : ℝ) = 0
      have := (c t).property.1
      linarith
    rw [hc, expand_zero, hAB _ _ hz]
  · congr 2
    convert Set.projIcc_of_mem zero_le_one (c t).property using 1
    norm_num

omit [TopologicalSpace X] in
private theorem paste_zero {T : Type*} {n : ℕ} (c : T → unitInterval)
    (A : T × UnitCube (n + 1) → X) (B : T × unitInterval → X)
    (t : T) (h : c t = 0) (z : UnitCube (n + 1)) : paste c A B (t, z) = A (t, z) := by
  simp [paste, h, radius_le_one, expand_zero]


/-- A homotopy that shrinks a cube while inserting the successive initial
segments of the basepoint path in the collar. -/
private def liftMap {n : ℕ} {x y : X} (d : Path x y) (a : CubeMap (n + 1) x) :
    C(unitInterval × UnitCube (n + 1), X) where
  toFun := paste id (fun p => a p.2) (fun p => d p.2)
  continuous_toFun := continuous_paste _ _ _ continuous_id
    (a.val.continuous.comp continuous_snd) (d.continuous.comp continuous_snd)
    (fun _ z hz => (GenLoop.boundary a z hz).trans d.source.symm)

/-- The concentric-cube representative at the terminal basepoint. -/
def cube {n : ℕ} {x y : X} (d : Path x y) (a : CubeMap (n + 1) x) : CubeMap (n + 1) y :=
  ⟨⟨fun z => liftMap d a (1, z), (liftMap d a).continuous.comp
    (continuous_const.prodMk continuous_id)⟩, fun z hz =>
      (paste_boundary id (fun p => a p.2) (fun p => d p.2)
        (fun _ z hz => (GenLoop.boundary a z hz).trans d.source.symm) 1 z hz).trans d.target⟩

/-- A moving-boundary lift with the exact trace d(t), including at times 0 and 1. -/
def lift {n : ℕ} {x y : X} (d : Path x y) (a : CubeMap (n + 1) x) :
    MovingCubeHomotopy d a (cube d a) where
  toContinuousMap := liftMap d a
  map_zero_left z := paste_zero id (fun p => a p.2) (fun p => d p.2) 0 rfl z
  map_one_left _ := rfl
  boundary t z hz := paste_boundary id (fun p => a p.2) (fun p => d p.2)
    (fun _ z hz => (GenLoop.boundary a z hz).trans d.source.symm) t z hz

/-- A fixed-boundary cube homotopy extends across the collar. -/
def mapHomotopy {n : ℕ} {x y : X} (d : Path x y) {a b : CubeMap (n + 1) x}
    (H : CubeHomotopy a b) : CubeHomotopy (cube d a) (cube d b) where
  toFun := paste (fun _ => 1) (fun p => H p) (fun p => d p.2)
  continuous_toFun := continuous_paste _ _ _ continuous_const H.continuous
    (d.continuous.comp continuous_snd) (fun t z hz =>
      (H.eq_fst t hz).trans ((GenLoop.boundary a z hz).trans d.source.symm))
  map_zero_left z := by
    change (if _ then H (0, _) else _) = (if _ then _ else _)
    dsimp only
    simp only [id_eq]
    split_ifs
    · exact H.apply_zero _
    · rfl
  map_one_left z := by
    change (if _ then H (1, _) else _) = (if _ then _ else _)
    dsimp only
    simp only [id_eq]
    split_ifs
    · exact H.apply_one _
    · rfl
  prop' t z hz := by
    change paste (fun _ => 1) (fun p => H p) (fun p => d p.2) (t, z) = (cube d a).val z
    rw [paste_boundary _ _ _ (fun t z hz =>
      (H.eq_fst t hz).trans ((GenLoop.boundary a z hz).trans d.source.symm)) t z hz]
    exact d.target.trans (GenLoop.boundary (cube d a) z hz).symm

/-- Compression with a constant collar is homotopic to the original cube,
relative to the whole boundary. -/
def compression {n : ℕ} {x : X} (a : CubeMap (n + 1) x) :
    CubeHomotopy a (cube (Path.refl x) a) where
  toHomotopy := (lift (Path.refl x) a).toHomotopy
  prop' t z hz := ((lift (Path.refl x) a).boundary t z hz).trans
    (GenLoop.boundary a z hz).symm

private def remainingTime (s r : unitInterval) : unitInterval :=
  ⟨s + (1 - s) * r, by
    constructor
    · have hs := s.property.1
      have hs' := s.property.2
      have hr := r.property.1
      nlinarith
    · have hs := s.property.2
      have hr := r.property.2
      nlinarith⟩

private theorem remainingTime_zero (r : unitInterval) : remainingTime 0 r = r := by
  ext
  simp [remainingTime]
private theorem remainingTime_one (r : unitInterval) : remainingTime 1 r = 1 := by
  ext
  simp [remainingTime]
private theorem remainingTime_zero_right (s : unitInterval) : remainingTime s 0 = s := by
  ext
  simp [remainingTime]
private theorem remainingTime_one_right (s : unitInterval) : remainingTime s 1 = 1 := by
  ext
  simp [remainingTime]

/-- Insert the remaining segment of d at each time of a moving homotopy.
The boundary then stays at the final basepoint. -/
def normalize {n : ℕ} {x y : X} {d : Path x y} {a : CubeMap (n + 1) x}
    {b : CubeMap (n + 1) y} (H : MovingCubeHomotopy d a b) :
    CubeHomotopy (cube d a) (cube (Path.refl y) b) where
  toFun := paste (fun _ => 1) (fun p => H.toHomotopy p)
    (fun p => d (remainingTime p.1 p.2))
  continuous_toFun := continuous_paste _ _ _ continuous_const H.toHomotopy.continuous
    (d.continuous.comp (by unfold remainingTime; fun_prop)) (fun t z hz => by
      rw [remainingTime_zero_right]
      exact H.boundary t z hz)
  map_zero_left z := by
    change (if _ then H.toHomotopy (0, _) else _) = (if _ then _ else _)
    dsimp only
    simp only [id_eq]
    split_ifs
    · exact H.toHomotopy.apply_zero _
    · exact congrArg d (remainingTime_zero _)
  map_one_left z := by
    change (if _ then H.toHomotopy (1, _) else _) = (if _ then _ else _)
    dsimp only
    simp only [id_eq]
    split_ifs
    · exact H.toHomotopy.apply_one _
    · rw [remainingTime_one]
      exact d.target
  prop' t z hz := by
    change paste (fun _ => 1) (fun p => H.toHomotopy p)
      (fun p => d (remainingTime p.1 p.2)) (t, z) = (cube d a).val z
    rw [paste_boundary _ _ _ (fun t z hz => by
      rw [remainingTime_zero_right]; exact H.boundary t z hz) t z hz]
    rw [remainingTime_one_right, d.target]
    exact (GenLoop.boundary (cube d a) z hz).symm

/-- Any moving homotopy yields the expected equality of transported classes. -/
theorem class_eq_of_moving {n : ℕ} {x y : X} {d : Path x y} {a : CubeMap (n + 1) x}
    {b : CubeMap (n + 1) y} (H : MovingCubeHomotopy d a b) :
    cubeClass (cube d a) = cubeClass b :=
  (higherClassEquality _ _ _ _ _).mpr ⟨(normalize H).trans (compression b).symm⟩

theorem mapHomotopic {n : ℕ} {x y : X} (d : Path x y) {a b : CubeMap (n + 1) x}
    (h : GenLoop.Homotopic a b) : GenLoop.Homotopic (cube d a) (cube d b) := by
  obtain ⟨H⟩ := h
  exact ⟨mapHomotopy d H⟩

/-- The induced transport on the quotient; multiplicativity is proved below. -/
def transport {n : ℕ} {x y : X} (d : Path x y) : HigherPi (n + 1) X x → HigherPi (n + 1) X y :=
  fun a => MulOpposite.op (Quotient.map (cube d) (fun _ _ h => mapHomotopic d h) a.unop)

@[simp] theorem transport_class {n : ℕ} {x y : X} (d : Path x y) (a : CubeMap (n + 1) x) :
    transport d (cubeClass a) = cubeClass (cube d a) := rfl

def reverseMoving {n : ℕ} {x y : X} {d : Path x y} {a : CubeMap (n + 1) x}
    {b : CubeMap (n + 1) y} (H : MovingCubeHomotopy d a b) :
    MovingCubeHomotopy d.symm b a where
  toHomotopy := H.toHomotopy.symm
  boundary t z hz := H.boundary (unitInterval.symm t) z hz

@[simp] theorem transport_inverse {n : ℕ} {x y : X} (d : Path x y)
    (a : HigherPi (n + 1) X x) : transport d.symm (transport d a) = a := by
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  exact class_eq_of_moving (reverseMoving (lift d a))


/-- Concatenate two moving cubes at every time. Their gluing face has the
common value d(t), which also controls the entire outer boundary. -/
def concatMoving {n : ℕ} {x y : X} {d : Path x y}
    {a b : CubeMap (n + 1) x} {a' b' : CubeMap (n + 1) y}
    (i : Fin (n + 1)) (H : MovingCubeHomotopy d a a') (K : MovingCubeHomotopy d b b') :
    MovingCubeHomotopy d (GenLoop.transAt i a b) (GenLoop.transAt i a' b') where
  toFun p := if (p.2 i : ℝ) ≤ 1 / 2 then
    H.toHomotopy (p.1, Function.update p.2 i (Set.projIcc 0 1 zero_le_one (2 * p.2 i)))
    else K.toHomotopy (p.1, Function.update p.2 i
      (Set.projIcc 0 1 zero_le_one (2 * p.2 i - 1)))
  continuous_toFun := by
    apply continuous_if_le (by fun_prop) continuous_const
    · apply Continuous.continuousOn
      apply H.toHomotopy.continuous.comp
      exact continuous_fst.prodMk (continuous_snd.update i
        (continuous_projIcc.comp (((continuous_apply i).comp continuous_snd).subtype_val.const_mul 2)))
    · apply Continuous.continuousOn
      apply K.toHomotopy.continuous.comp
      exact continuous_fst.prodMk (continuous_snd.update i
        (continuous_projIcc.comp ((((continuous_apply i).comp continuous_snd).subtype_val.const_mul 2).sub
          continuous_const)))
    · intro p hp
      change (p.2 i : ℝ) = 1 / 2 at hp
      have hl : Function.update p.2 i (Set.projIcc 0 1 zero_le_one (2 * p.2 i)) ∈
          CubeBoundary (n + 1) := by
        refine ⟨i, Or.inr ?_⟩
        rw [Function.update_self]
        have he : 2 * (p.2 i : ℝ) = 1 := by linarith
        rw [he]
        exact Set.projIcc_right _
      have hr : Function.update p.2 i (Set.projIcc 0 1 zero_le_one (2 * p.2 i - 1)) ∈
          CubeBoundary (n + 1) := by
        refine ⟨i, Or.inl ?_⟩
        rw [Function.update_self]
        have he : 2 * (p.2 i : ℝ) - 1 = 0 := by linarith
        rw [he]
        exact Set.projIcc_left _
      exact (H.boundary _ _ hl).trans (K.boundary _ _ hr).symm
  map_zero_left z := by
    change (if _ then H.toHomotopy (0, _) else K.toHomotopy (0, _)) =
      (if _ then _ else _)
    dsimp only
    split_ifs
    · exact H.toHomotopy.apply_zero _
    · exact K.toHomotopy.apply_zero _
  map_one_left z := by
    change (if _ then H.toHomotopy (1, _) else K.toHomotopy (1, _)) =
      (if _ then _ else _)
    dsimp only
    split_ifs
    · exact H.toHomotopy.apply_one _
    · exact K.toHomotopy.apply_one _
  boundary t z hz := by
    change (if _ then _ else _) = d t
    split_ifs with hi
    · apply H.boundary
      obtain ⟨j, hj⟩ := hz
      by_cases hji : j = i
      · subst j
        rcases hj with hj | hj
        · refine ⟨i, Or.inl ?_⟩
          simp [hj]
        · have : (1 : ℝ) ≤ 1 / 2 := by simpa [hj] using hi
          norm_num at this
      · exact ⟨j, by simpa [Function.update_of_ne hji] using hj⟩
    · apply K.boundary
      obtain ⟨j, hj⟩ := hz
      by_cases hji : j = i
      · subst j
        rcases hj with hj | hj
        · simp [hj] at hi
        · refine ⟨i, Or.inr ?_⟩
          norm_num [hj]
      · exact ⟨j, by simpa [Function.update_of_ne hji] using hj⟩

/-- Transport respects the paper's first-cube-first multiplication. -/
theorem transport_mul {n : ℕ} {x y : X} (d : Path x y)
    (a b : HigherPi (n + 1) X x) : transport d (a * b) = transport d a * transport d b := by
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  obtain ⟨b, rfl⟩ := cubeClass_surjective b
  have hmul := (higherGroupConvention n X x).1 (0 : Fin (n + 1)) a b
  rw [← hmul, transport_class, transport_class, transport_class]
  rw [← (higherGroupConvention n X y).1 (0 : Fin (n + 1))]
  exact class_eq_of_moving (concatMoving 0 (lift d a) (lift d b))

/-- The change-of-basepoint isomorphism, in the direction of d. -/
def equiv {n : ℕ} {x y : X} (d : Path x y) :
    HigherPi (n + 1) X x ≃* HigherPi (n + 1) X y where
  toFun := transport d
  invFun := transport d.symm
  left_inv := transport_inverse d
  right_inv a := by simpa only [Path.symm_symm] using transport_inverse d.symm a
  map_mul' := transport_mul d

end CubeCollar

/-- The collar construction supplies a representative for every initial cube. -/
theorem movingCubeLift : ExpectedHigher.movingCubeLift.{u} := by
  intro n X _ x y d a
  exact ⟨CubeCollar.cube d a, ⟨CubeCollar.lift d a⟩⟩

theorem higherBasepointTransport : ExpectedHigher.basepointTransport.{u} := by
  intro n X _ x y d
  exact ⟨CubeCollar.equiv d, fun a b ⟨H⟩ => CubeCollar.class_eq_of_moving H⟩

theorem higherBasepointTransportUnique : ExpectedHigher.basepointTransportUnique.{u} := by
  intro n X _ x y d E E' hE hE'
  ext a
  obtain ⟨a, rfl⟩ := cubeClass_surjective a
  obtain ⟨b, H⟩ := movingCubeLift n X x y d a
  exact (hE a b H).trans (hE' a b H).symm

/-- Applying an ordinary target homotopy to a based cube produces a moving
cube whose boundary trace is exactly the basepoint trace of the homotopy. -/
def cubeUnbasedHomotopy {n : ℕ} (f g : C(X, Y)) (F : f.Homotopy g) (x : X)
    (a : CubeMap (n + 1) x) :
    MovingCubeHomotopy (F.evalAt x)
      (cubeMap (⟨f, rfl⟩ : PointedMap X Y x (f x)) a)
      (cubeMap (⟨g, rfl⟩ : PointedMap X Y x (g x)) a) where
  toFun p := F (p.1, a p.2)
  continuous_toFun := F.continuous.comp
    (continuous_fst.prodMk (a.val.continuous.comp continuous_snd))
  map_zero_left z := F.apply_zero (a z)
  map_one_left z := F.apply_one (a z)
  boundary t z hz := by
    change F (t, a z) = F (t, x)
    rw [GenLoop.boundary a z hz]

theorem higherUnbasedHomotopy : ExpectedHigher.unbasedHomotopy.{u,v} := by
  intro n X Y _ _ f g F x
  refine ⟨CubeCollar.equiv (F.evalAt x), ?_, ?_⟩
  · exact fun a b ⟨H⟩ => CubeCollar.class_eq_of_moving H
  · ext a
    obtain ⟨a, rfl⟩ := cubeClass_surjective a
    exact CubeCollar.class_eq_of_moving (cubeUnbasedHomotopy f g F x a)

end
end P202.Topology
