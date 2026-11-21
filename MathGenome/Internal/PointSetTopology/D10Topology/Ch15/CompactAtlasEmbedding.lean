import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.CompactAtlasEmbedding
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.FinitePartition
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.CompactNormal
import Mathlib.Logic.Equiv.Fin.Basic

open Set Topology
universe u

namespace D10Topology.Ch15

-- A chart map may be extended arbitrarily outside its open domain: after
-- multiplying by a subordinate coefficient its extension is continuous.
private theorem continuous_weighted_chart {X : Type u} [TopologicalSpace X]
    {I : Type*} (f : _root_.PartitionOfUnity I X) (U : I → Set X)
    (hf : f.IsSubordinate U) (hU : ∀ i, IsOpen (U i))
    {n : ℕ} (c : ∀ i, U i → (Fin n → ℝ))
    (hc : ∀ i, Continuous (c i)) (i : I) :
    ∃ g : X → (Fin n → ℝ),
      Continuous (fun x => f i x • g x) ∧
      ∀ (x : X) (hx : x ∈ U i), g x = c i ⟨x, hx⟩ := by
  classical
  let g : X → (Fin n → ℝ) := fun x => if hx : x ∈ U i then c i ⟨x, hx⟩ else 0
  have hg : ∀ (x : X) (hx : x ∈ U i), g x = c i ⟨x, hx⟩ := by
    intro x hx
    simp [g, hx]
  have hcont : ContinuousOn g (U i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hc i using 1
    funext x
    exact hg x x.property
  exact ⟨g, f.continuous_smul (fun x hx =>
    hcont.continuousAt ((hU i).mem_nhds (hf i hx))), hg⟩

/-- The exact finite-atlas dimension bound, including zero charts or coordinates. -/
theorem compact_finite_atlas_embedding {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (k n : ℕ)
    (U : Fin k → Set X) (O : Fin k → Set (Fin n → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (χ : ∀ i, U i ≃ₜ O i) :
    ∃ F : X → Fin (k * (n + 1)) → ℝ, IsEmbedding F := by
  classical
  have hX : Ch05.CoverCompact X := (Ch05.coverCompact_iff_compactSpace X).mpr inferInstance
  obtain ⟨φ, hφ⟩ := finite_subordinate_partition
    (Ch07.compact_hausdorff_normal hX) U hU hcover
  obtain ⟨f, hf, _⟩ := (partition_iff_mathlib U φ).mp hφ
  let c : ∀ i, U i → (Fin n → ℝ) := fun i x => (χ i x : Fin n → ℝ)
  have hc : ∀ i, Continuous (c i) := fun i =>
    continuous_subtype_val.comp (χ i).continuous
  choose g hg hgc using continuous_weighted_chart f U hf hU c hc
  let E : X → Fin k → Fin (n + 1) → ℝ :=
    fun x i => Fin.cons (f i x) (f i x • g i x)
  have hE : Continuous E := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    refine Fin.cases ?_ (fun l => ?_) j
    · simpa only [E, Fin.cons_zero] using (f i).continuous
    · simpa only [Function.comp_def, E, Fin.cons_succ] using (continuous_apply l).comp (hg i)
  have hEinj : Function.Injective E := by
    intro x y hxy
    obtain ⟨i, hi⟩ := f.exists_pos (mem_univ x)
    have hcoeff : f i x = f i y := by
      simpa only [E, Fin.cons_zero] using congrFun (congrFun hxy i) 0
    have hiy : 0 < f i y := hcoeff ▸ hi
    have hxU : x ∈ U i := hf i (subset_closure (ne_of_gt hi))
    have hyU : y ∈ U i := hf i (subset_closure (ne_of_gt hiy))
    have hchart : c i ⟨x, hxU⟩ = c i ⟨y, hyU⟩ := by
      rw [← hgc i x hxU, ← hgc i y hyU]
      funext j
      have heq := congrFun (congrFun hxy i) j.succ
      simp only [E, Fin.cons_succ, Pi.smul_apply, smul_eq_mul] at heq
      rw [← hcoeff] at heq
      exact mul_left_cancel₀ (ne_of_gt hi) heq
    have hsub : (⟨x, hxU⟩ : U i) = ⟨y, hyU⟩ :=
      (χ i).injective (Subtype.ext hchart)
    exact congrArg Subtype.val hsub
  let F : X → Fin (k * (n + 1)) → ℝ := fun x j =>
    E x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    exact (continuous_apply (finProdFinEquiv.symm j).2).comp
      ((continuous_apply (finProdFinEquiv.symm j).1).comp hE)
  refine ⟨F, Ch05.compact_to_hausdorff_injective F hX hF ?_⟩
  intro x y hxy
  apply hEinj
  funext i j
  have heq := congrFun hxy (finProdFinEquiv (i, j))
  simpa only [F, Equiv.symm_apply_apply] using heq

/-- Compact Hausdorff topological n-manifolds have finite-dimensional
Euclidean embeddings. The local Euclidean hypothesis is written explicitly
as open neighborhoods homeomorphic to open subsets of real n-space. -/
theorem compact_manifold_embedding {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (n : ℕ)
    (hcharts : ∀ x : X, ∃ U : Set X, ∃ O : Set (Fin n → ℝ),
      IsOpen U ∧ IsOpen O ∧ x ∈ U ∧ Nonempty (U ≃ₜ O)) :
    ∃ m : ℕ, ∃ F : X → Fin m → ℝ, IsEmbedding F := by
  classical
  choose U O hU hO hx χ using hcharts
  have hcover : (univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hfinitecover : ∀ x, ∃ i, x ∈ U (e i).val := by
    intro x
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hs (mem_univ x))
    obtain ⟨hy, hxy⟩ := mem_iUnion.mp hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    simpa only [Equiv.apply_symm_apply] using hxy
  obtain ⟨F, hF⟩ := compact_finite_atlas_embedding (Fintype.card s) n
    (fun i => U (e i).val) (fun i => O (e i).val)
    (fun i => hU (e i).val) hfinitecover (fun i => (χ (e i).val).some)
  exact ⟨Fintype.card s * (n + 1), F, hF⟩

end D10Topology.Ch15
