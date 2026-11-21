import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.ProductCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.MapCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.SeparateContinuityCounterexample
import Mathlib.Algebra.Order.Archimedean.Basic

/-! The four cautions in paper.tex, `d10:03:product-cautions`. -/

open Set
open scoped Topology

namespace D10Topology.Ch03.ProductCounterexamples

def diagonal : ℝ → (ℕ+ → ℝ) := fun t _ => t

def shrinkingBox : Set (ℕ+ → ℝ) :=
  univ.pi (fun n => Ioo (-(1 / (n : ℝ))) (1 / (n : ℝ)))

theorem diagonal_product_continuous :
    Continuous[inferInstance, productTopology (fun _ : ℕ+ => inferInstance)] diagonal := by
  apply (continuous_product_iff _ _ _).mpr
  intro n
  exact continuous_id

theorem shrinkingBox_box_open :
    IsOpen[boxTopology (fun _ : ℕ+ => inferInstance)] shrinkingBox := by
  apply TopologicalSpace.isOpen_generateFrom_of_mem
  exact ⟨fun n => Ioo (-(1 / (n : ℝ))) (1 / (n : ℝ)), fun _ => isOpen_Ioo, rfl⟩

theorem diagonal_preimage_shrinkingBox :
    diagonal ⁻¹' shrinkingBox = ({0} : Set ℝ) := by
  ext t
  constructor
  · intro ht
    change ∀ n : ℕ+, n ∈ (univ : Set ℕ+) →
      t ∈ Ioo (-(1 / (n : ℝ))) (1 / (n : ℝ)) at ht
    apply mem_singleton_iff.mpr
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
    let k : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    have hk := ht k (mem_univ k)
    have ha : |t| < 1 / ((n : ℝ) + 1) := by
      simpa [k] using (abs_lt.mpr hk)
    exact (not_lt_of_ge (le_of_lt hn)) ha
  · rintro (rfl : t = 0)
    change ∀ n : ℕ+, n ∈ (univ : Set ℕ+) →
      (0 : ℝ) ∈ Ioo (-(1 / (n : ℝ))) (1 / (n : ℝ))
    intro n _
    have hn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos
    exact ⟨neg_neg_of_pos (one_div_pos.mpr hn), one_div_pos.mpr hn⟩

theorem diagonal_box_not_continuous :
    ¬ Continuous[inferInstance, boxTopology (fun _ : ℕ+ => inferInstance)] diagonal := by
  intro hc
  have ho : IsOpen (diagonal ⁻¹' shrinkingBox) :=
    @Continuous.isOpen_preimage ℝ (ℕ+ → ℝ) inferInstance
      (boxTopology (fun _ : ℕ+ => inferInstance)) diagonal hc _ shrinkingBox_box_open
  rw [diagonal_preimage_shrinkingBox] at ho
  exact not_isOpen_singleton (0 : ℝ) ho

theorem binary_basic_neighborhood_has_second_point
    (B : Set (ℕ+ → Bool))
    (hB : B ∈ productBasis (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool)))
    (x : ℕ+ → Bool) (hx : x ∈ B) : ∃ y ∈ B, y ≠ x := by
  classical
  rcases hB with ⟨U, F, _hU, rfl⟩
  obtain ⟨k, hk⟩ := F.exists_notMem
  refine ⟨Function.update x k (!(x k)), ?_, ?_⟩
  · intro i hi
    have hik : i ≠ k := by
      intro he
      subst i
      exact hk hi
    simpa [Function.update_of_ne hik] using hx i hi
  · intro heq
    have he := congrFun heq k
    simp at he

theorem binary_singleton_not_open (x : ℕ+ → Bool) :
    ¬ IsOpen[productTopology (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool))]
      ({x} : Set (ℕ+ → Bool)) := by
  intro ho
  obtain ⟨A, hA, hUnion⟩ := (product_opens _ _).mp ho
  have hx : x ∈ ⋃₀ A := hUnion ▸ mem_singleton x
  obtain ⟨B, hBA, hxB⟩ := mem_sUnion.mp hx
  obtain ⟨y, hyB, hyx⟩ := binary_basic_neighborhood_has_second_point B (hA hBA) x hxB
  have hy : y ∈ ({x} : Set (ℕ+ → Bool)) :=
    hUnion.symm ▸ mem_sUnion.mpr ⟨B, hBA, hyB⟩
  exact hyx (mem_singleton_iff.mp hy)

theorem binary_product_not_discrete :
    ¬ @DiscreteTopology (ℕ+ → Bool)
      (productTopology (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool))) := by
  intro hd
  let : TopologicalSpace (ℕ+ → Bool) :=
    productTopology (fun _ : ℕ+ => (⊥ : TopologicalSpace Bool))
  let : DiscreteTopology (ℕ+ → Bool) := hd
  exact binary_singleton_not_open (fun _ => false) (isOpen_discrete _)

theorem projection_closed_counterexample :
    IsClosed {z : ℝ × ℝ | z.1 * z.2 = 1} ∧
      Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1} = (univ : Set ℝ) \ {0} ∧
      ¬ IsClosed (Prod.fst '' {z : ℝ × ℝ | z.1 * z.2 = 1}) ∧
      ¬ IsClosedMap (Prod.fst : ℝ × ℝ → ℝ) :=
  ⟨Ch02.MapCounterexamples.hyperbola_closed,
    Ch02.MapCounterexamples.hyperbola_projection,
    Ch02.MapCounterexamples.hyperbola_projection_not_closed,
    Ch02.MapCounterexamples.real_projection_open_not_closed.2⟩

theorem separate_continuity_counterexample :
    let h := Ch02.separateContinuityMap
    h (0, 0) = 0 ∧
      (∀ p : ℝ × ℝ, p ≠ (0, 0) → h p = p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) ∧
      (∀ y : ℝ, Continuous (fun x : ℝ => h (x, y))) ∧
      (∀ x : ℝ, Continuous (fun y : ℝ => h (x, y))) ∧
      ¬ ContinuousAt h (0, 0) :=
  ⟨Ch02.separateContinuityMap_at_origin,
    Ch02.separateContinuityMap_off_origin,
    Ch02.separateContinuityMap_horizontal_continuous,
    Ch02.separateContinuityMap_vertical_continuous,
    Ch02.separateContinuityMap_not_continuousAt_origin⟩

end D10Topology.Ch03.ProductCounterexamples
