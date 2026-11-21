import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.Monodromy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringCriterion

namespace P202.Topology
open P202Specs.Topology
open scoped unitInterval
universe u v
noncomputable section
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

@[simp] theorem fiberAction_eq {p : E → B} (hp : Covering p) (b : B)
    (e : Fiber p b) (g : Pi1 B b) :
    fiberAction p b e g = (covering_to_library hp).monodromy (pathClass g) e := by
  simp only [fiberAction, dite_eq_left (covering_to_library hp)]

theorem monodromyActionLaws : MonodromyExpected.actionLaws.{u,v} := by
  intro E B _ _ p hp b
  constructor
  · intro e
    rw [fiberAction_eq hp, pathClass_one, IsCoveringMap.monodromy_refl]
    rfl
  · intro e g h
    simp only [fiberAction_eq hp, pathClass_mul, IsCoveringMap.monodromy_trans_apply]

theorem monodromyEndpointFormula : MonodromyExpected.endpointFormula.{u,v} := by
  intro E B _ _ p hp b e a L hL h0
  rw [fiberAction_eq hp, pathClass_loopClass]
  exact (covering_to_library hp).monodromy_eq_apply_one (funext hL) h0

theorem monodromyTransitive : MonodromyExpected.transitive.{u,v} := by
  intro E B _ _ _ _ p hp b e f
  let d := PathConnectedSpace.somePath e.val f.val
  let a : SourcePath b b := (d.map (coveringContinuous E B p hp)).cast e.property.symm f.property.symm
  refine ⟨loopClass a, Subtype.ext ?_⟩
  exact (monodromyEndpointFormula E B p hp b e a d.toContinuousMap (fun _ => rfl)
    d.source).trans d.target

theorem monodromyStabilizer : MonodromyExpected.stabilizer.{u,v} := by
  intro E B _ _ p hp b e g
  obtain ⟨a, rfl⟩ := loopClass_surjective g
  let cov := covering_to_library hp
  let L := cov.liftPath a.toContinuousMap e.val (a.source.trans e.property.symm)
  have hL : ∀ t, p (L t) = a t := fun t => congr_fun (cov.liftPath_lifts ..) t
  have h0 : L 0 = e.val := cov.liftPath_zero ..
  have hend := monodromyEndpointFormula E B p hp b e a L hL h0
  rw [Subtype.ext_iff, hend]
  exact closedLiftCriterion E B e.val b ⟨p, e.property⟩ hp a L hL h0

/-- Two group elements have equal endpoints precisely when they lie in the
same right coset of the image subgroup. -/
theorem fiberAction_eq_iff {p : C(E, B)} (hp : Covering p) (b : B)
    (e : Fiber p b) (g h : Pi1 B b) :
    fiberAction p b e g = fiberAction p b e h ↔
      QuotientGroup.rightRel (fiberSubgroup p b e) g h := by
  have hmul := (monodromyActionLaws E B p hp b).2
  have hone := (monodromyActionLaws E B p hp b).1
  rw [QuotientGroup.rightRel_apply, ← monodromyStabilizer E B p hp b e]
  constructor
  · intro heq
    rw [hmul, ← heq, ← hmul, mul_inv_cancel, hone]
  · intro heq
    have h := congrArg (fun z => fiberAction p b z g) heq
    simpa only [← hmul, inv_mul_cancel_right] using h.symm

theorem monodromyCosetEquivalence : MonodromyExpected.cosetEquivalence.{u,v} := by
  intro E B _ _ _ _ p hp b e
  let H := fiberSubgroup p b e
  let f : RightCosets H → Fiber p b := Quotient.lift (fiberAction p b e)
    (fun a b hab => (fiberAction_eq_iff hp _ _ _ _).mpr hab)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn with | _ a =>
        induction b using Quotient.inductionOn with | _ b =>
          exact fun h => Quotient.sound ((fiberAction_eq_iff hp _ _ _ _).mp h)
    · intro y
      obtain ⟨g, hg⟩ := monodromyTransitive E B p hp b e y
      exact ⟨rightCoset H g, hg⟩
  refine ⟨Equiv.ofBijective f hf, (fun _ => rfl), ?_⟩
  intro q g
  induction q using Quotient.inductionOn with | _ a =>
    exact (monodromyActionLaws E B p hp b).2 e a g

theorem monodromyFiberTransport : MonodromyExpected.fiberTransport.{u,v} := by
  intro E B _ _ p hp x y d
  let cov := covering_to_library hp
  let T : Fiber p x ≃ Fiber p y := {
    toFun := cov.monodromy (.mk d)
    invFun := cov.monodromy (.mk d.symm)
    left_inv := fun e => by
      rw [← cov.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.trans_symm, cov.monodromy_refl]
      rfl
    right_inv := fun e => by
      rw [← cov.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm,
        Path.Homotopic.Quotient.symm_trans, cov.monodromy_refl]
      rfl }
  exact ⟨T, fun e L hL h0 => cov.monodromy_eq_apply_one (funext hL) h0,
    fun e L hL h0 => cov.monodromy_eq_apply_one (funext hL) h0⟩

theorem monodromyFiberIndex : MonodromyExpected.fiberIndex.{u,v} := by
  intro E B _ _ _ _ p hp b e
  obtain ⟨F, _, _⟩ := monodromyCosetEquivalence E B p hp b e
  exact Cardinal.lift_mk_eq'.mpr ⟨F.symm.trans
    (QuotientGroup.quotientRightRelEquivQuotientLeftRel (fiberSubgroup p b e))⟩

/-- Send a sheet to the unique point over b on that sheet. -/
def sheetPoint {p : E → B} {U : Set B} {b : B} (hb : b ∈ U)
    (s : CoveringSheet p U) : Fiber p b :=
  ⟨s.chart.symm b, (congrFun s.projection _).symm.trans
    (s.chart.right_inv (by rwa [s.target_eq]))⟩

theorem sheetPoint_mem {p : E → B} {U : Set B} {b : B} (hb : b ∈ U)
    (s : CoveringSheet p U) : (sheetPoint hb s).val ∈ s.chart.source :=
  s.chart.map_target (by rwa [s.target_eq])

theorem monodromySheetCardinality : MonodromyExpected.sheetCardinality.{u,v} := by
  intro E B _ _ p U b hb S hdis hcover
  have hbij : Function.Bijective (fun s : S => sheetPoint hb s.val) := by
    constructor
    · intro s t hst
      apply Subtype.ext
      by_contra hne
      have hd := hdis s.property t.property hne
      exact Set.disjoint_left.mp hd (sheetPoint_mem hb s.val)
        (by rw [show (sheetPoint hb s.val).val = (sheetPoint hb t.val).val from
          congrArg Subtype.val hst]; exact sheetPoint_mem hb t.val)
    · intro e
      have he : e.val ∈ ⋃ s ∈ S, s.chart.source := by
        rw [hcover]
        change p e.val ∈ U
        simpa only [show p e.val = b from e.property] using hb
      simp only [Set.mem_iUnion] at he
      obtain ⟨s, hs, he⟩ := he
      refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
      change s.chart.symm b = e.val
      calc
        s.chart.symm b = s.chart.symm (p e.val) := congrArg s.chart.symm e.property.symm
        _ = s.chart.symm (s.chart e.val) :=
          congrArg s.chart.symm (congrFun s.projection e.val).symm
        _ = e.val := s.chart.left_inv he
  exact (Cardinal.lift_id'.{u,v} _).symm.trans
    ((Cardinal.lift_mk_eq'.mpr ⟨Equiv.ofBijective _ hbij⟩).trans
      (congrFun Cardinal.lift_umax.{u,v} _))

theorem monodromySheetIndex : MonodromyExpected.sheetIndex.{u,v} := by
  intro E B _ _ _ _ p hp b e U c hc S hdis hcover
  obtain ⟨T, _, _⟩ := monodromyFiberTransport E B p hp b c
    (PathConnectedSpace.somePath b c)
  rw [monodromySheetCardinality E B p U c hc S hdis hcover,
    ← Cardinal.mk_congr T, monodromyFiberIndex E B p hp b e]

end
end P202.Topology
