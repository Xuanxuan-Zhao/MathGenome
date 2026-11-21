import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.FundamentalGroupoid

namespace P202.Topology
open P202Specs.Topology
open CategoryTheory
open scoped unitInterval

universe u v w
noncomputable section
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem pathClass_ofClass {x : X} (p : PathClass x x) :
    pathClass (ofClass p) = p := rfl
@[simp] theorem ofClass_pathClass {x : X} (p : Pi1 X x) :
    ofClass (pathClass p) = p := rfl

theorem pathClass_injective {x : X} : Function.Injective (pathClass : Pi1 X x → PathClass x x) :=
  fun a b h => by simpa using congrArg ofClass h

@[simp] theorem pathClass_mul {x : X} (a b : Pi1 X x) :
    pathClass (a * b) = (pathClass a).trans (pathClass b) := rfl
@[simp] theorem pathClass_one {x : X} :
    pathClass (1 : Pi1 X x) = Path.Homotopic.Quotient.refl x := rfl
@[simp] theorem pathClass_inv {x : X} (a : Pi1 X x) :
    pathClass (a⁻¹) = (pathClass a).symm := rfl
@[simp] theorem pathClass_loopClass {x : X} (a : SourcePath x x) :
    pathClass (loopClass a) = Path.Homotopic.Quotient.mk a := rfl

theorem loopClass_surjective {x : X} : Function.Surjective (loopClass : SourcePath x x → Pi1 X x) := by
  intro a
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective (pathClass a)
  exact ⟨p, pathClass_injective hp⟩

theorem pathOperations : Expected.pathOperations.{u} := by
  intro X _ x y z a b
  exact ⟨fun _ => rfl, fun t => Path.trans_apply a b t⟩

theorem classEquality : Expected.classEquality.{u} := by
  intro X _ x y a b
  exact Path.Homotopic.Quotient.eq

theorem groupoidLaws : Expected.groupoidLaws.{u} := by
  intro X _ x y z w a b c
  exact ⟨Path.Homotopic.Quotient.trans_assoc a b c,
    Path.Homotopic.Quotient.refl_trans a,
    Path.Homotopic.Quotient.trans_refl a,
    Path.Homotopic.Quotient.trans_symm a,
    Path.Homotopic.Quotient.symm_trans a⟩

theorem groupConvention : Expected.groupConvention.{u} := by
  intro X _ x
  refine ⟨fun a b => rfl, rfl, fun a => rfl, pathClass_injective, ?_⟩
  intro a
  exact ⟨ofClass a, rfl⟩

@[simp] theorem induced_pathClass {x : X} {y : Y} (f : PointedMap X Y x y) (a : Pi1 X x) :
    pathClass (f.induced a) = ((pathClass a).map f.map).cast f.point.symm f.point.symm := by
  exact congrArg CategoryTheory.End.asHom (FundamentalGroup.mapOfEq_apply f.map f.point a.unop)

theorem inducedFormula : Expected.inducedFormula.{u,v} := by
  intro X Y _ _ x y f a
  apply pathClass_injective
  simp only [induced_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.mk_map]

@[simp] theorem induced_id (x : X) : (PointedMap.id x).induced = MonoidHom.id (Pi1 X x) := by
  ext a
  apply pathClass_injective
  obtain ⟨a, rfl⟩ := loopClass_surjective a
  simp only [induced_pathClass, pathClass_loopClass]
  rfl

@[simp] theorem induced_comp {x : X} {y : Y} {z : Z}
    (f : PointedMap X Y x y) (g : PointedMap Y Z y z) :
    (g.comp f).induced = g.induced.comp f.induced := by
  ext a
  apply pathClass_injective
  simp only [MonoidHom.comp_apply, induced_pathClass, PointedMap.comp,
    Path.Homotopic.Quotient.map_cast, Path.Homotopic.Quotient.cast_cast,
    Path.Homotopic.Quotient.map_comp]

theorem functoriality : Expected.functoriality.{u,v,w} :=
  ⟨fun _ _ x => induced_id x, fun _ _ _ _ _ _ _ _ _ f g => induced_comp f g⟩

theorem basepointFormula : Expected.basepointFormula.{u} := by
  intro X _ x y d b
  simp [changeBasepoint, oppositeEquiv, FundamentalGroup.fundamentalGroupMulEquivOfPath,
    Iso.conj, Iso.homCongr, pathClass, Path.Homotopic.Quotient.trans_assoc]
  rw [← Groupoid.inv_eq_inv]
  rfl


/-- Restricting a homotopy fixed at the basepoint to a loop gives a path homotopy. -/
theorem based_map_homotopic {x : X} {y : Y} (f g : PointedMap X Y x y)
    (H : f.BasedHomotopy g) (a : SourcePath x x) :
    ((a.map f.map.continuous).cast f.point.symm f.point.symm).Homotopic
      ((a.map g.map.continuous).cast g.point.symm g.point.symm) := by
  refine ⟨{
    toFun := fun p => H (p.1, a p.2)
    continuous_toFun := H.continuous.comp (continuous_fst.prodMk (a.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro t
    exact H.apply_zero (a t)
  · intro t
    exact H.apply_one (a t)
  · intro t s hs
    rcases hs with hs | hs
    · subst s
      change H (t, a 0) = f.map (a 0)
      simpa only [Path.source] using H.eq_fst t (Set.mem_singleton x)
    · have hs : s = 1 := hs
      subst s
      change H (t, a 1) = f.map (a 1)
      simpa only [Path.target] using H.eq_fst t (Set.mem_singleton x)

theorem basedHomotopy : Expected.basedHomotopy.{u,v} := by
  intro X Y _ _ x y f g ⟨H⟩
  ext a
  obtain ⟨a, rfl⟩ := loopClass_surjective a
  rw [inducedFormula X Y x y f a, inducedFormula X Y x y g a]
  exact congrArg ofClass (Path.Homotopic.Quotient.eq.mpr (based_map_homotopic f g H a))

/-- A pointed homotopy inverse gives two-sided inverses on the based groups. -/
theorem pointedEquivalence : Expected.pointedEquivalence.{u,v} := by
  intro X Y _ _ x y e
  have hl : e.backward.induced.comp e.forward.induced = MonoidHom.id (Pi1 X x) := by
    rw [← induced_comp]
    exact (basedHomotopy X X x x _ _ ⟨e.left⟩).trans (induced_id x)
  have hr : e.forward.induced.comp e.backward.induced = MonoidHom.id (Pi1 Y y) := by
    rw [← induced_comp]
    exact (basedHomotopy Y Y y y _ _ ⟨e.right⟩).trans (induced_id y)
  refine ⟨{
    toFun := e.forward.induced
    invFun := e.backward.induced
    left_inv := fun a => DFunLike.congr_fun hl a
    right_inv := fun b => DFunLike.congr_fun hr b
    map_mul' := e.forward.induced.map_mul }, ?_, ?_⟩
  · exact fun _ => rfl
  · exact fun _ => rfl


@[simp] theorem class_trans_symm_cancel {x y z : X} (a : PathClass x y) (b : PathClass x z) :
    a.trans (a.symm.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

@[simp] theorem class_symm_trans_cancel {x y z : X} (a : PathClass x y) (b : PathClass y z) :
    a.symm.trans (a.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem changeBasepoint_pathClass {x y : X} (d : SourcePath x y) (b : Pi1 X y) :
    pathClass (changeBasepoint d b) =
      ((Path.Homotopic.Quotient.mk d).trans (pathClass b)).trans
        (Path.Homotopic.Quotient.mk d.symm) := basepointFormula X x y d b

@[simp] theorem loopClass_inv {x : X} (a : SourcePath x x) :
    loopClass a.symm = (loopClass a)⁻¹ := rfl

/-- The precise inner automorphism when the basepoint path is changed. -/
theorem basepointInner : Expected.basepointInner.{u} := by
  intro X _ x y d d' b
  rw [← loopClass_inv, Path.trans_symm, Path.symm_symm]
  apply pathClass_injective
  simp only [pathClass_mul, changeBasepoint_pathClass, pathClass_loopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc, class_symm_trans_cancel]

/-- Naturality of the boundary of the homotopy square, followed by cancellation
of its moving-basepoint side, gives the unbased correction formula. -/
theorem unbasedHomotopy : Expected.unbasedHomotopy.{u,v} := by
  intro X Y _ _ f g F x a
  apply pathClass_injective
  rw [basepointFormula, pathClass_loopClass, pathClass_loopClass]
  have h : (Path.Homotopic.Quotient.mk (a.map f.continuous)).trans
      (Path.Homotopic.Quotient.mk (F.evalAt x)) =
      (Path.Homotopic.Quotient.mk (F.evalAt x)).trans
        (Path.Homotopic.Quotient.mk (a.map g.continuous)) := by
    simpa only [← Path.Homotopic.Quotient.mk_trans] using
      (Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt F a))
  calc
    _ = ((Path.Homotopic.Quotient.mk (a.map f.continuous)).trans
        (Path.Homotopic.Quotient.mk (F.evalAt x))).trans
        (Path.Homotopic.Quotient.mk (F.evalAt x).symm) := by
      simp [Path.Homotopic.Quotient.trans_assoc]
    _ = _ := congrArg (fun p => p.trans (Path.Homotopic.Quotient.mk (F.evalAt x).symm)) h


@[simp] theorem squareTrace_apply (f g : C(X, Y)) (F : C(X × unitInterval, Y))
    (h0 : ∀ x, F (x, 0) = f x) (h1 : ∀ x, F (x, 1) = g x) (x : X) (t : unitInterval) :
    squareTrace f g F h0 h1 x t = F (x, t) := rfl

theorem unbasedSquare : Expected.unbasedSquare.{u,v} := by
  intro X Y _ _ f g F h0 h1 x a
  rw [unbasedHomotopy X Y f g (squareHomotopy f g F h0 h1) x a]
  apply pathClass_injective
  rw [changeBasepoint_pathClass]
  rfl

end
end P202.Topology
