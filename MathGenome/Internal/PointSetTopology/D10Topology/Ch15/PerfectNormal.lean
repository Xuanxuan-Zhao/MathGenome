import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PerfectNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ClosureSums
import Mathlib.Topology.Separation.PerfectlyNormal

/-!
The three conclusions of paper.tex, d10:15:perfect-normal.

For each open O, select from each locally finite basis layer those members
whose closures lie in O. Their unions V n are open, cover O, and have
closures inside O. The last assertion uses the locally finite closure-union
theorem, and is the step where local finiteness is essential.

These unions give countable separating covers of disjoint closed sets and
also express the complement of O as a countable intersection of opens.
For the cozero function we use Mathlib's proved zero-set characterization
of perfectly normal spaces. Its forward proof constructs a Urysohn series
with weights 1 / 2 / 2^n, proves summability by the geometric majorant, and
uses `continuous_tsum` with that same uniform bound. Thus uniform convergence
and continuity are justified without a compactness assumption on X.
-/

open Set TopologicalSpace
open scoped Topology
universe u

namespace D10Topology.Ch15

variable {X : Type u} [TopologicalSpace X]

/-- An open set has a countable open cover whose termwise closures stay in it. -/
theorem exists_open_cover_closure_subset [RegularSpace X]
    (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hσ : SigmaLocallyFinite (fun b : B => (b : Set X)))
    (O : Set X) (hO : IsOpen O) :
    ∃ V : ℕ → Set X, (∀ n, IsOpen (V n)) ∧
      O = ⋃ n, V n ∧ ∀ n, closure (V n) ⊆ O := by
  classical
  obtain ⟨L, hL, hfin⟩ := hσ
  let A (n : ℕ) (b : L n) : Set X :=
    if closure (b.val : Set X) ⊆ O then (b.val : Set X) else ∅
  have hAO (n : ℕ) (b : L n) : closure (A n b) ⊆ O := by
    dsimp only [A]
    split_ifs with h
    · exact h
    · simp
  have hAf (n : ℕ) : LocallyFinite (A n) := by
    apply (hfin n).subset
    intro b
    dsimp only [A]
    split_ifs <;> simp
  refine ⟨fun n => ⋃ b : L n, A n b, ?_, ?_, ?_⟩
  · intro n
    apply isOpen_iUnion
    intro b
    dsimp only [A]
    split_ifs
    · exact hB.isOpen b.val.property
    · exact isOpen_empty
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨b, hb, hxb, hbc⟩ := hB.exists_closure_subset (hO.mem_nhds hx)
      obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hL (⟨b, hb⟩ : B)
      refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨⟨⟨b, hb⟩, hn⟩, ?_⟩⟩
      simpa only [A, ite_eq_left hbc] using hxb
    · apply iUnion_subset
      intro n
      apply iUnion_subset
      intro b
      exact subset_closure.trans (hAO n b)
  · intro n
    rw [D10Topology.Ch15.closure_iUnion (A n) (hAf n)]
    exact iUnion_subset (hAO n)

/-- Separate disjoint closed sets by the countable layer construction. -/
theorem sigmaLocallyFinite_basis_normal
    (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hσ : SigmaLocallyFinite (fun b : B => (b : Set X))) : NormalSpace X := by
  have cover (s t : Set X) (ht : IsClosed t) (hd : Disjoint s t) :
      HasSeparatingCover s t := by
    obtain ⟨V, hVo, hVcov, hVc⟩ :=
      exists_open_cover_closure_subset B hB hσ tᶜ ht.isOpen_compl
    refine ⟨V, ?_, fun n => ⟨hVo n, ?_⟩⟩
    · rw [← hVcov]
      exact disjoint_left.mp hd
    · exact disjoint_left.mpr fun x hx ht => hVc n hx ht
  exact ⟨fun s t hs ht hd =>
    hasSeparatingCovers_iff_separatedNhds.mp
      ⟨cover s t ht hd, cover t s hs hd.symm⟩⟩

/-- The complement of the closure of each layer union is an open Gδ factor. -/
theorem sigmaLocallyFinite_basis_closed_gdelta
    (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hσ : SigmaLocallyFinite (fun b : B => (b : Set X)))
    (F : Set X) (hF : IsClosed F) : IsGδ F := by
  obtain ⟨V, hVo, hVcov, hVc⟩ :=
    exists_open_cover_closure_subset B hB hσ Fᶜ hF.isOpen_compl
  apply isGδ_iff_eq_iInter_nat.mpr
  refine ⟨fun n => (closure (V n))ᶜ,
    fun _ => isClosed_closure.isOpen_compl, ?_⟩
  ext x
  simp only [mem_iInter, mem_compl_iff]
  constructor
  · intro hx n hxn
    exact hVc n hxn hx
  · intro hx
    by_contra hxF
    have hxU : x ∈ ⋃ n, V n := hVcov ▸ hxF
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact hx n (subset_closure hn)

/-- Every open set is exactly the positive locus of a continuous interval-valued map. -/
theorem sigmaLocallyFinite_basis_cozero
    (X : Type u) [TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hσ : SigmaLocallyFinite (fun b : B => (b : Set X)))
    (O : Set X) (hO : IsOpen O) :
    ∃ f : X → unitInterval, Continuous f ∧ O = {x | 0 < (f x : ℝ)} := by
  let : PerfectlyNormalSpace X :=
    { toNormalSpace := sigmaLocallyFinite_basis_normal X B hB hσ
      closed_gdelta := fun {F} hF =>
        sigmaLocallyFinite_basis_closed_gdelta X B hB hσ F hF }
  obtain ⟨g, hg, hgI⟩ :=
    perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.mp
      (inferInstance : PerfectlyNormalSpace X) Oᶜ hO.isClosed_compl
  refine ⟨fun x => ⟨g x, hgI x⟩, g.continuous.subtype_mk _, ?_⟩
  ext x
  have hz : x ∉ O ↔ g x = 0 := by
    change x ∈ Oᶜ ↔ x ∈ g ⁻¹' {0}
    rw [hg]
  change x ∈ O ↔ 0 < g x
  constructor
  · intro hx
    exact lt_of_le_of_ne (hgI x).1 (fun h => (hz.mpr h.symm) hx)
  · intro hx
    by_contra hxO
    exact (ne_of_gt hx) (hz.mp hxO)

end D10Topology.Ch15
