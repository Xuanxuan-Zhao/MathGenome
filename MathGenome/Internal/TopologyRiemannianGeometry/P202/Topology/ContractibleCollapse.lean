import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.ContractibleCollapse
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.HomotopyExtension
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.HomotopyExtension
noncomputable section
universe u
open Set Topology ContinuousMap
open P202.Cellular

namespace P202.Topology

/-- The quotient argument of Proposition 2.4, conditional on homotopy
extension for a source and target in the same universe. -/
theorem contractibleCollapse_of_selfExtension
    (hep : P202Specs.Topology.HomotopyExtension.cwHomotopyExtension.{u, u}) :
    P202Specs.Topology.ContractibleCollapse.contractibleCollapse.{u} := by
  intro X _ _ A _ hA
  let : ContractibleSpace A := hA
  obtain ⟨a₀, ⟨c⟩⟩ := id_nullhomotopic A
  let g : C(A, X) := ContinuousMap.const A a₀.1
  let h : ContinuousMap.Homotopy
      ((ContinuousMap.id X).comp
        (P202Specs.Topology.HomotopyExtension.subcomplexInclusion A)) g := {
    toFun := fun p => (c p).1
    continuous_toFun := continuous_subtype_val.comp c.continuous
    map_zero_left := fun a => congrArg Subtype.val (c.map_zero_left a)
    map_one_left := fun a => congrArg Subtype.val (c.map_one_left a) }
  obtain ⟨_, H', H'A⟩ := hep X X A (ContinuousMap.id X) g h
  let H : C(X × Interval, X) :=
    ⟨fun p => H' (p.2, p.1), H'.continuous.comp continuous_swap⟩
  have Hzero (x : X) : H (x, 0) = x := H'.map_zero_left x
  have HA (a : A) (t : Interval) : H (a.1, t) = (c (t, a)).1 := H'A t a
  let q := collapseProjection A
  have qquot : IsQuotientMap (q : X → Collapse A) := isQuotientMap_quotient_mk'
  have qrel (x y : X) (hxy : q x = q y) :
      x = y ∨ (x ∈ A.carrier ∧ y ∈ A.carrier) := Quotient.exact hxy
  have Hends (a : A) : H (a.1, 1) = a₀.1 := by
    rw [HA]
    exact congrArg Subtype.val (c.map_one_left a)
  let F : C(X, X) :=
    ⟨fun x => H (x, 1), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have Ffiber : ∀ x y, q x = q y → F x = F y := by
    intro x y hxy
    rcases qrel x y hxy with rfl | ⟨hx, hy⟩
    · rfl
    · exact (Hends ⟨x, hx⟩).trans (Hends ⟨y, hy⟩).symm
  obtain ⟨j', ⟨jc, jq⟩, _⟩ := D10Topology.Ch03.quotient_descent q
    ((D10Topology.Ch03.quotientMap_iff_mathlib q).mpr qquot) F F.continuous Ffiber
  let j : C(Collapse A, X) := ⟨j', jc⟩
  have j_q (x : X) : j (q x) = H (x, 1) := congrFun jq x
  have qHfiber (x y : X) (t : Interval) (hxy : q x = q y) :
      q (H (x, t)) = q (H (y, t)) := by
    rcases qrel x y hxy with rfl | ⟨hx, hy⟩
    · rfl
    · rw [HA ⟨x, hx⟩ t, HA ⟨y, hy⟩ t]
      exact Quotient.sound (Or.inr ⟨(c (t, ⟨x, hx⟩)).2, (c (t, ⟨y, hy⟩)).2⟩)
  let qp : X × Interval → Collapse A × Interval := Prod.map q id
  have qpquot : IsQuotientMap qp := quotientProductInterval q qquot
  have projFiber : ∀ p p', qp p = qp p' → q (H p) = q (H p') := by
    rintro ⟨x, t⟩ ⟨y, s⟩ heq
    have ht : t = s := congrArg Prod.snd heq
    subst s
    exact qHfiber x y t (congrArg Prod.fst heq)
  obtain ⟨K, ⟨Kc, Kqp⟩, _⟩ := D10Topology.Ch03.quotient_descent qp
    ((D10Topology.Ch03.quotientMap_iff_mathlib qp).mpr qpquot)
    (fun p => q (H p)) (q.continuous.comp H.continuous) projFiber
  have K_q (x : X) (t : Interval) : K (q x, t) = q (H (x, t)) :=
    congrFun Kqp (x, t)
  have leftH : (ContinuousMap.id X).Homotopic (j.comp q) := by
    refine ⟨{
      toFun := fun p => H (p.2, p.1)
      continuous_toFun := H.continuous.comp continuous_swap
      map_zero_left := Hzero
      map_one_left := fun x => (j_q x).symm }⟩
  have rightH : (ContinuousMap.id (Collapse A)).Homotopic (q.comp j) := by
    refine ⟨{
      toFun := fun p => K (p.2, p.1)
      continuous_toFun := Kc.comp continuous_swap
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro z
      obtain ⟨x, rfl⟩ := qquot.surjective z
      change K (q x, 0) = q x
      rw [K_q, Hzero]
    · intro z
      obtain ⟨x, rfl⟩ := qquot.surjective z
      change K (q x, 1) = q (j (q x))
      rw [K_q, j_q]
  exact ⟨{
    toFun := q
    invFun := j
    left_inv := leftH.symm
    right_inv := rightH.symm }, rfl⟩

/-- Collapsing a nonempty contractible CW subcomplex gives a homotopy
 equivalence whose forward map is the quotient projection. -/
theorem contractibleCollapse :
    P202Specs.Topology.ContractibleCollapse.contractibleCollapse.{u} :=
  contractibleCollapse_of_selfExtension cwHomotopyExtensionSelf

end P202.Topology
