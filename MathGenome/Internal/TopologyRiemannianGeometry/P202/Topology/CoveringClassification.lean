import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CoveringClassification
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SubgroupCoverConstruction
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Monodromy

namespace P202.Topology.CoveringClassification
open P202Specs.Topology
open Filter Set _root_.Topology
universe u v w
noncomputable section

variable {E : Type u} {D : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace D] [TopologicalSpace B]

theorem connectedCoverLocallyPathConnected :
    ClassificationExpected.connectedCoverLocallyPathConnected.{u,v} := by
  intro E B _ _ _ p hp
  constructor
  intro x
  rw [hasBasis_self]
  intro V hV
  obtain ⟨a, hx, _⟩ := (covering_to_library hp).isLocalHomeomorph x
  have hax : a x ∈ a.target := a.map_source hx
  have hn : a.symm ⁻¹' V ∈ 𝓝 (a x) := by
    apply a.symm.continuousAt hax |>.preimage_mem_nhds
    simpa only [a.left_inv hx] using hV
  obtain ⟨W, ⟨hW, hconn⟩, hsub⟩ := (path_connected_basis (a x)).mem_iff.mp
    (inter_mem (a.open_target.mem_nhds hax) hn)
  refine ⟨a.symm '' W, ?_, ?_, ?_⟩
  · have hm := (a.symm.map_nhds_eq hax).symm
    rw [a.left_inv hx] at hm
    rw [hm]
    exact Filter.image_mem_map hW
  · exact hconn.image' (a.continuousOn_invFun.mono fun y hy => (hsub hy).1)
  · rintro y ⟨z, hz, rfl⟩
    exact (hsub hz).2

theorem connectedCoverPathConnected : ClassificationExpected.connectedCoverPathConnected.{u,v} := by
  intro E B _ _ _ _ p hp
  have := connectedCoverLocallyPathConnected E B p hp
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- A continuous pointed map over the base gives inclusion of image subgroups. -/
theorem image_le_of_lift {e : E} {d : D} {b : B}
    (p : PointedMap E B e b) (q : PointedMap D B d b)
    (L : C(E, D)) (hL : ∀ x, q.map (L x) = p.map x) (hpoint : L e = d) :
    p.induced.range ≤ q.induced.range := by
  let f : PointedMap E D e d := ⟨L, hpoint⟩
  have heq : q.comp f = p := by
    have hm : (q.comp f).map = p.map := by ext x; exact hL x
    exact pointedMap_ext hm
  rintro g ⟨a, rfl⟩
  refine ⟨f.induced a, ?_⟩
  change (q.induced.comp f.induced) a = p.induced a
  rw [← induced_comp, heq]

/-- Pointed homeomorphisms preserve the image subgroup. -/
theorem image_eq_of_pointedIsomorphism {e : E} {d : D} {b : B}
    (p : PointedMap E B e b) (q : PointedMap D B d b)
    (h : PointedCoverIsomorphic p q) : p.induced.range = q.induced.range := by
  obtain ⟨F, hpoint, hover⟩ := h
  apply le_antisymm (image_le_of_lift p q ⟨F, F.continuous⟩ hover hpoint)
  apply image_le_of_lift q p ⟨F.symm, F.symm.continuous⟩
  · intro y
    exact (hover (F.symm y)).symm.trans (congrArg q.map (F.apply_symm_apply y))
  · change F.symm d = e
    rw [← hpoint, F.symm_apply_apply]

theorem pointedIsomorphismCriterion : ClassificationExpected.pointedIsomorphismCriterion.{u,v,w} := by
  intro E D B _ _ _ _ _ _ e d b p q hp hq
  have := connectedCoverLocallyPathConnected E B p.map hp
  have := connectedCoverLocallyPathConnected D B q.map hq
  have := connectedCoverPathConnected E B p.map hp
  have := connectedCoverPathConnected D B q.map hq
  constructor
  · intro hsub
    obtain ⟨L, hL, _⟩ := (coveringLiftCriterion D B E d b e q hq p).mpr hsub.le
    obtain ⟨M, hM, _⟩ := (coveringLiftCriterion E B D e b d p hp q).mpr hsub.ge
    have hML : M.comp L = ContinuousMap.id E := by
      apply coveringLiftUnique E B E e b e p hp p
      · exact ⟨fun x => (hM.1 (L x)).trans (hL.1 x), (congrArg M hL.2).trans hM.2⟩
      · exact ⟨fun _ => rfl, rfl⟩
    have hLM : L.comp M = ContinuousMap.id D := by
      apply coveringLiftUnique D B D d b d q hq q
      · exact ⟨fun x => (hL.1 (M x)).trans (hM.1 x), (congrArg L hM.2).trans hL.2⟩
      · exact ⟨fun _ => rfl, rfl⟩
    refine ⟨{ toFun := L
              invFun := M
              left_inv := fun x => DFunLike.congr_fun hML x
              right_inv := fun x => DFunLike.congr_fun hLM x
              continuous_toFun := L.continuous
              continuous_invFun := M.continuous }, hL.2, hL.1⟩
  · exact image_eq_of_pointedIsomorphism p q

/-- The stabilizer of e·g is g⁻¹Hg for the paper's right action. -/
theorem pointChangeConjugacy : ClassificationExpected.pointChangeConjugacy.{u,v} := by
  intro E B _ _ p hp b e g
  ext a
  change a ∈ fiberSubgroup p b (fiberAction p b e g) ↔
    g * a * g⁻¹ ∈ fiberSubgroup p b e
  rw [← monodromyStabilizer E B p hp b (fiberAction p b e g),
    ← monodromyStabilizer E B p hp b e]
  have hmul := (monodromyActionLaws E B p hp b).2
  have hone := (monodromyActionLaws E B p hp b).1
  constructor
  · intro h
    rw [hmul, hmul, h, ← hmul, mul_inv_cancel, hone]
  · intro h
    have h' := congrArg (fun z => fiberAction p b z g) h
    simpa only [← hmul, inv_mul_cancel_right] using h'

theorem unpointedIsomorphismCriterion :
    ClassificationExpected.unpointedIsomorphismCriterion.{u,v,w} := by
  intro E D B _ _ _ _ _ _ _ e d b p q hp hq
  have := connectedCoverPathConnected E B p.map hp
  have := connectedCoverPathConnected D B q.map hq
  constructor
  · rintro ⟨F, hover⟩
    let fp : Fiber q.map b := ⟨F e, (hover e).trans p.point⟩
    let q' : PointedMap D B fp.val b := ⟨q.map, fp.property⟩
    have himage : p.induced.range = q'.induced.range :=
      image_eq_of_pointedIsomorphism p q' ⟨F, rfl, hover⟩
    obtain ⟨g, hg⟩ := monodromyTransitive D B q.map hq b fp ⟨d, q.point⟩
    have hc := pointChangeConjugacy D B q.map hq b fp g
    rw [hg] at hc
    change q.induced.range = conjugateSubgroup q'.induced.range g at hc
    exact ⟨g, himage ▸ hc⟩
  · rintro ⟨g, hg⟩
    let ep : Fiber p.map b := ⟨e, p.point⟩
    let ep' := fiberAction p.map b ep g
    let p' : PointedMap E B ep'.val b := ⟨p.map, ep'.property⟩
    have hc := pointChangeConjugacy E B p.map hp b ep g
    change p'.induced.range = conjugateSubgroup p.induced.range g at hc
    have heq : p'.induced.range = q.induced.range := hc.trans hg.symm
    obtain ⟨F, _, hF⟩ :=
      (pointedIsomorphismCriterion E D B ep'.val d b p' q hp hq).mp heq
    exact ⟨F, hF⟩

/-- The already constructed E_H, bundled without adding any certificates to
its underlying path quotient or topology. -/
def subgroupRepresentative (B : Type u) [TopologicalSpace B] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B] (hsemi : SemilocallySimplyConnected B)
    (b : B) (H : Subgroup (Pi1 B b)) : ConnectedPointedCover B b where
  total := SubgroupCover b H
  topology := inferInstance
  connected := by
    have := SubgroupCoverConstruction.pathConnected B hsemi b H
    infer_instance
  point := SubgroupCover.basepoint H
  projection := ⟨⟨SubgroupCover.endpoint H,
    SubgroupCoverConstruction.endpoint_continuous H hsemi⟩, rfl⟩
  covering := SubgroupCoverConstruction.covering B hsemi b H

@[simp] theorem subgroupRepresentative_image (B : Type u) [TopologicalSpace B]
    [PathConnectedSpace B] [LocallyPathConnectedSpace B]
    (hsemi : SemilocallySimplyConnected B) (b : B) (H : Subgroup (Pi1 B b)) :
    (subgroupRepresentative B hsemi b H).imageSubgroup = H :=
  SubgroupCoverConstruction.imageSubgroup B hsemi b H
    (SubgroupCoverConstruction.endpoint_continuous H hsemi)

/-- This also ensures that the bundled class space represents covers with
arbitrary total-space universe. -/
theorem canonicalRepresentative : ClassificationExpected.canonicalRepresentative.{u,v} := by
  intro E B _ _ _ _ _ hsemi e b p hp
  let H := p.induced.range
  let C := subgroupRepresentative B hsemi b H
  have heq : p.induced.range = C.projection.induced.range :=
    (subgroupRepresentative_image B hsemi b H).symm
  exact (pointedIsomorphismCriterion E C.total B e C.point b
    p C.projection hp C.covering).mp heq

theorem pointedClassification : ClassificationExpected.pointedClassification.{u} := by
  intro B _ _ _ hsemi b
  let f : ConnectedPointedCover.PointedClasses B b → Subgroup (Pi1 B b) :=
    Quotient.lift ConnectedPointedCover.imageSubgroup
      (fun C D h => image_eq_of_pointedIsomorphism C.projection D.projection h)
  have hf : Function.Bijective f := by
    constructor
    · intro c d
      induction c using Quotient.inductionOn with | _ C =>
        induction d using Quotient.inductionOn with | _ D =>
          intro h
          exact Quotient.sound ((pointedIsomorphismCriterion C.total D.total B
            C.point D.point b C.projection D.projection C.covering D.covering).mp h)
    · intro H
      exact ⟨Quotient.mk _ (subgroupRepresentative B hsemi b H),
        subgroupRepresentative_image B hsemi b H⟩
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

theorem unpointedClassification : ClassificationExpected.unpointedClassification.{u} := by
  intro B _ _ _ hsemi b
  let f : ConnectedPointedCover.UnpointedClasses B b → SubgroupConjugacyClasses (Pi1 B b) :=
    Quotient.lift (fun C => Quotient.mk _ C.imageSubgroup) (by
      intro C D h
      exact Quotient.sound ((unpointedIsomorphismCriterion C.total D.total B
        C.point D.point b C.projection D.projection C.covering D.covering).mp h))
  have hf : Function.Bijective f := by
    constructor
    · intro c d
      induction c using Quotient.inductionOn with | _ C =>
        induction d using Quotient.inductionOn with | _ D =>
          intro h
          exact Quotient.sound ((unpointedIsomorphismCriterion C.total D.total B
            C.point D.point b C.projection D.projection C.covering D.covering).mpr
              (Quotient.exact h))
    · intro h
      induction h using Quotient.inductionOn with | _ H =>
        refine ⟨Quotient.mk _ (subgroupRepresentative B hsemi b H), ?_⟩
        change Quotient.mk _ (subgroupRepresentative B hsemi b H).imageSubgroup = _
        rw [subgroupRepresentative_image]
  exact ⟨Equiv.ofBijective f hf, fun _ => rfl⟩

theorem universalCover : ClassificationExpected.universalCover.{u,v} := by
  intro B _ _ _ hsemi b
  exact ⟨SubgroupCoverConstruction.covering B hsemi b ⊥,
    SubgroupCoverConstruction.simplyConnected B hsemi b,
    fun E _ _ e p hp => SubgroupCoverConstruction.universalProperty B E hsemi b e p hp⟩

end
end P202.Topology.CoveringClassification
