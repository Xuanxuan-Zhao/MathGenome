import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.OrderTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.BasesAndNeighborhoods

/-! Order topologies on arbitrary linear orders, including empty and singleton
types. The interval basis requires only nontriviality; the subtype equality
requires precisely order convexity. -/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

def orderRays (L : Type u) [LinearOrder L] : Set (Set L) :=
  {U | ∃ a, U = Ioi a ∨ U = Iio a}

@[instance_reducible] def orderTopology (L : Type u) [LinearOrder L] : TopologicalSpace L :=
  TopologicalSpace.generateFrom (orderRays L)

def orderIntervals (L : Type u) [LinearOrder L] : Set (Set L) :=
  {U | (∃ a b, a < b ∧ U = Ioo a b) ∨
    (∃ m b, IsBot m ∧ m < b ∧ U = Ico m b) ∨
    (∃ a M, IsTop M ∧ a < M ∧ U = Ioc a M)}

theorem orderTopology_eq_mathlib (L : Type u) [LinearOrder L] :
    orderTopology L = Preorder.topology L := rfl

theorem orderRays_open (L : Type u) [LinearOrder L] (a : L) :
    IsOpen[orderTopology L] (Iio a) ∧ IsOpen[orderTopology L] (Ioi a) := by
  exact ⟨TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, Or.inr rfl⟩,
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨a, Or.inl rfl⟩⟩

theorem orderIntervals_basis (L : Type u) [LinearOrder L] [Nontrivial L] :
    BasisFor (orderTopology L) (orderIntervals L) := by
  let : TopologicalSpace L := orderTopology L
  let : OrderTopology L := ⟨rfl⟩
  apply (basis_iff_mathlib _ _).mpr
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro U (⟨a, b, _, rfl⟩ | ⟨m, b, hm, _, rfl⟩ | ⟨a, M, hM, _, rfl⟩)
    · exact isOpen_Ioo
    · have he : Ico m b = Iio b := by
        ext x
        exact ⟨fun h => h.2, fun h => ⟨hm x, h⟩⟩
      rw [he]
      exact isOpen_Iio
    · have he : Ioc a M = Ioi a := by
        ext x
        exact ⟨fun h => h.1, fun h => ⟨h, hM x⟩⟩
      rw [he]
      exact isOpen_Ioi
  · intro x U hx hU
    have hnhds := hU.mem_nhds hx
    by_cases hl : ∃ l : L, l < x
    · by_cases hu : ∃ b : L, x < b
      · obtain ⟨a, b, hab, hsub⟩ := (mem_nhds_iff_exists_Ioo_subset' hl hu).mp hnhds
        exact ⟨Ioo a b, Or.inl ⟨a, b, hab.1.trans hab.2, rfl⟩, hab, hsub⟩
      · have htop : IsTop x := fun y => le_of_not_gt (fun h => hu ⟨y, h⟩)
        obtain ⟨a, ha, hsub⟩ := exists_Ioc_subset_of_mem_nhds hnhds hl
        exact ⟨Ioc a x, Or.inr (Or.inr ⟨a, x, htop, ha, rfl⟩), ⟨ha, le_rfl⟩, hsub⟩
    · have hbot : IsBot x := fun y => le_of_not_gt (fun h => hl ⟨y, h⟩)
      obtain ⟨b, hb⟩ := exists_ne x
      have hxb : x < b := lt_of_le_of_ne (hbot b) (Ne.symm hb)
      obtain ⟨b, hb, hsub⟩ := exists_Ico_subset_of_mem_nhds hnhds ⟨b, hxb⟩
      exact ⟨Ico x b, Or.inr (Or.inl ⟨x, b, hbot, hb, rfl⟩), ⟨le_rfl, hb⟩, hsub⟩

theorem orderTopology_hausdorff (L : Type u) [LinearOrder L] :
    @T2Space L (orderTopology L) := by
  let : TopologicalSpace L := orderTopology L
  let : OrderTopology L := ⟨rfl⟩
  infer_instance

theorem orderTopology_convex_subspace (L : Type u) [LinearOrder L] (A : Set L)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ z, x ≤ z → z ≤ y → z ∈ A) :
    orderTopology A = TopologicalSpace.induced (Subtype.val : A → L) (orderTopology L) := by
  let : TopologicalSpace L := orderTopology L
  let : OrderTopology L := ⟨rfl⟩
  have hc : OrdConnected A := ⟨by
    intro x hx y hy z hz
    exact hA x hx y hy z hz.1 hz.2⟩
  have hr : OrdConnected (range (Subtype.val : A → L)) := by
    simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using hc
  exact ((Subtype.strictMono_coe (· ∈ A)).induced_topology_eq_preorder hr).symm

theorem orderTopology_convex_subspace_opens (L : Type u) [LinearOrder L] (A : Set L)
    (hA : ∀ x ∈ A, ∀ y ∈ A, ∀ z, x ≤ z → z ≤ y → z ∈ A) (U : Set A) :
    IsOpen[orderTopology A] U ↔
      ∃ V : Set L, IsOpen[orderTopology L] V ∧ U = (Subtype.val : A → L) ⁻¹' V := by
  let : TopologicalSpace L := orderTopology L
  rw [orderTopology_convex_subspace L A hA]
  rw [isOpen_induced_iff]
  exact exists_congr fun V => and_congr_right fun _ => eq_comm

end D10Topology.Ch01
