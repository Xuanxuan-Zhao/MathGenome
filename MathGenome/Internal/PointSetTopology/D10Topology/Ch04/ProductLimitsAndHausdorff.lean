import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.ProductLimitsAndHausdorff
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetFilterBridge
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.ULift

/-! Products and unique limits (paper.tex, d10:04:product-convergence).
The canonical product-topology bridge justifies the library's coordinate test.
Proper filters with two limits test Hausdorffness; their canonical nets give
the converse net test. No nonemptiness assumption is placed on the spaces. -/

open Set Filter
open scoped Topology
universe u v w
namespace D10Topology.Ch04

abbrev Hausdorff {X : Type u} :=
  @Specs.D10Topology.Ch04.ProductLimitsAndHausdorff.Hausdorff X

theorem hausdorff_iff_t2 {X : Type u} (t : TopologicalSpace X) :
    Hausdorff t ↔ @T2Space X t := by
  let := t
  exact (t2Space_iff X).symm

/-- Bridge between the paper's eventual-neighborhood definition and atTop. -/
theorem converges_iff_tendsto_atTop {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (t : TopologicalSpace X) (a : D → X) (x : X) :
    Converges t a x ↔ @Tendsto D X a atTop (@nhds X t x) := by
  let := t
  rw [Filter.tendsto_def]
  constructor
  · intro h N hN
    exact Filter.mem_atTop_sets.mpr
      (h N ((Ch01.neighborhood_iff_mem_nhds t x N).mpr hN))
  · intro h N hN
    exact Filter.mem_atTop_sets.mp
      (h N ((Ch01.neighborhood_iff_mem_nhds t x N).mp hN))

theorem net_product_converges_iff {I : Type u} {X : I → Type v} {D : Type w}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (tX : ∀ i, TopologicalSpace (X i)) (a : D → ∀ i, X i) (x : ∀ i, X i) :
    Converges (Ch03.productTopology tX) a x ↔
      ∀ i, Converges (tX i) (fun d => a d i) (x i) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  simp only [converges_iff_tendsto_atTop]
  exact tendsto_pi_nhds

theorem filter_product_converges_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (F : Filter (∀ i, X i)) [F.NeBot]
    (x : ∀ i, X i) :
    @FilterConverges _ (Ch03.productTopology tX) F x ↔
      ∀ i, @FilterConverges _ (tX i) (ImageFilter (Ch03.projection i) F) (x i) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  simp only [converges_iff_le_nhds]
  change (F ≤ nhds x) ↔ ∀ i, Filter.map (fun a : (∀ j, X j) => a i) F ≤ nhds (x i)
  simpa only [Filter.Tendsto, Filter.map_id, id_eq] using
    (tendsto_pi_nhds (f := (id : (∀ i, X i) → ∀ i, X i)) (g := x) (u := F))

theorem hausdorff_iff_unique_filter_limits {X : Type u} (t : TopologicalSpace X) :
    Hausdorff t ↔ ∀ (F : Filter X) [F.NeBot] (x y : X),
      @FilterConverges X t F x → @FilterConverges X t F y → x = y := by
  let := t
  rw [hausdorff_iff_t2]
  constructor
  · intro hT F hF x y hx hy
    exact (t2_iff_nhds.mp hT)
      (hF.mono (le_inf ((converges_iff_le_nhds F x).mp hx)
        ((converges_iff_le_nhds F y).mp hy)))
  · intro h
    apply t2_iff_nhds.mpr
    intro x y hxy
    exact @h (nhds x ⊓ nhds y) hxy x y
      ((converges_iff_le_nhds _ x).mpr inf_le_left)
      ((converges_iff_le_nhds _ y).mpr inf_le_right)

theorem net_limits_unique {X : Type u} {D : Type v}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (t : TopologicalSpace X) (hT : Hausdorff t) (a : D → X) (x y : X)
    (hx : Converges t a x) (hy : Converges t a y) : x = y := by
  let := t
  let := tailFilter_proper a
  exact (hausdorff_iff_unique_filter_limits t).mp hT (TailFilter a) x y
    ((tailFilter_converges a x).mpr hx) ((tailFilter_converges a y).mpr hy)

theorem hausdorff_iff_unique_net_limits {X : Type u} (t : TopologicalSpace X) :
    Hausdorff t ↔
      ∀ (D : Type (max u v)) [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : D → X) (x y : X), Converges t a x → Converges t a y → x = y := by
  constructor
  · intro hT D _ _ _ a x y hx hy
    exact net_limits_unique t hT a x y hx hy
  · intro h
    apply (hausdorff_iff_unique_filter_limits t).mpr
    intro F hF x y hx hy
    let := t
    let := hF
    let E := ULift.{v} (FilterNetIndex F)
    let : IsDirectedOrder E := ⟨fun p q => by
      obtain ⟨r, hpr, hqr⟩ := exists_ge_ge p.down q.down
      exact ⟨ULift.up r, hpr, hqr⟩⟩
    have hdown : SubnetMap (ULift.down : E → FilterNetIndex F) :=
      ⟨fun _ _ hpq => hpq, fun p => ⟨ULift.up p, le_rfl⟩⟩
    have hnet (z : X) (hz : FilterConverges F z) : Converges t (filterNet F) z := by
      apply (tailFilter_converges (filterNet F) z).mp
      rw [filterNet_tailFilter]
      exact hz
    exact h E (subnet (filterNet F) ULift.down) x y
      (converges_subnet t _ _ x hdown (hnet x hx))
      (converges_subnet t _ _ y hdown (hnet y hy))

end D10Topology.Ch04
