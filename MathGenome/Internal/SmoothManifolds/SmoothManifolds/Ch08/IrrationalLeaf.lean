import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.IrrationalLeaf
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.IrrationalLine
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.GlobalLeaves
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.IrrationalSlopeDistribution
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch08.IrrationalOrbitLeaf
import Mathlib.Topology.Sequences

set_option autoImplicit false
noncomputable section
namespace SmoothManifolds.IrrationalLeaf
open ModelData AtlasData MapData MapClassData SphereTorusData IrrationalLineData
  LeafData Set Filter
open scoped Topology

/-- The period is exactly one, so the circle criterion has precisely the
irrationality hypothesis of the original example. -/
theorem circle_density : Specs.SmoothManifolds.Ch08.IrrationalLeaf.circle_densityType := by
  intro α hα
  exact AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)

/-- Fix a lift x of the first coordinate and use parameters x+j. Their second
coordinates are the translate of the dense integer rotation by αx. -/
theorem density : Specs.SmoothManifolds.Ch08.IrrationalLeaf.densityType := by
  intro α hα p
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (p 0)
  let F : AddCircle (1 : ℝ) → FlatTorus 2 :=
    fun y => ![(x : AddCircle (1 : ℝ)), ((α * x : ℝ) : AddCircle (1 : ℝ)) + y]
  have hF : Continuous F := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [F, Matrix.cons_val_zero, Matrix.cons_val_one]
    · exact continuous_const
    · exact (continuous_const : Continuous (fun _ : AddCircle (1 : ℝ) =>
        ((α * x : ℝ) : AddCircle (1 : ℝ)))).add continuous_id
  have hp : F (p 1 - (α * x : AddCircle (1 : ℝ))) = p := by
    ext i
    fin_cases i
    · exact hx
    · simp [F]
  rw [← hp]
  apply closure_mono (s := F '' range (fun j : ℤ => j • (α : AddCircle (1 : ℝ))))
  · rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
    refine ⟨x + (j : ℝ), ?_⟩
    have hj0 : ((j : ℝ) : AddCircle (1 : ℝ)) = 0 :=
      (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨j, by simp⟩
    ext i
    fin_cases i
    · change ((x + (j : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ))
      rw [AddCircle.coe_add, hj0, add_zero]
    · change ((α * (x + (j : ℝ)) : ℝ) : AddCircle (1 : ℝ)) =
        ((α * x : ℝ) : AddCircle (1 : ℝ)) + j • (α : AddCircle (1 : ℝ))
      rw [mul_add, AddCircle.coe_add]
      congr 1
      rw [mul_comm, ← zsmul_eq_mul, AddCircle.coe_zsmul]
  · exact mem_closure_image hF.continuousAt (circle_density α hα _)

/-- A compactness proof of recurrence, using two increasingly separated terms
of a convergent subsequence. It works for every slope. -/
theorem recurrence : Specs.SmoothManifolds.Ch08.IrrationalLeaf.recurrenceType := by
  intro α
  obtain ⟨p, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq
    (fun n : ℕ => irrationalLine α (n : ℝ))
  let q : ℕ → ℕ := fun n => φ ((n+1)+n) - φ n
  have hq (n : ℕ) : n+1 ≤ q n := by
    have h := hφ.add_le_nat (n+1) n
    dsimp [q]
    omega
  have htop : Tendsto (fun n : ℕ => (n+1)+n) atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp only [id]; omega) tendsto_id
  have hlim' := hlim.comp htop
  have hreturn := hlim'.sub hlim
  have heq (n : ℕ) :
      irrationalLine α (q n : ℝ) =
        irrationalLine α (φ ((n+1)+n) : ℝ) - irrationalLine α (φ n : ℝ) := by
    rw [← IrrationalLine.line_sub]
    congr 1
    exact Nat.cast_sub (hφ.monotone (by omega))
  refine ⟨q, fun n => lt_of_lt_of_le (by omega) (hq n), ?_, ?_⟩
  · exact tendsto_atTop_mono (fun n => le_trans (Nat.le_succ n) (hq n)) tendsto_id
  · simpa only [Function.comp_def, ← heq, sub_self] using hreturn

theorem injective_immersion :
    Specs.SmoothManifolds.Ch08.IrrationalLeaf.injective_immersionType := by
  intro α hα S Q hS hQ
  exact ⟨IrrationalLine.injective α hα, IrrationalLine.smoothImmersion α S Q hS hQ⟩

theorem transported_topology :
    Specs.SmoothManifolds.Ch08.IrrationalLeaf.transported_topologyType :=
  IrrationalLine.immersedTopology_strict

/-- Any intrinsic topology for which this same parametrization is a
homeomorphism is strictly finer than the ambient subspace topology. -/
theorem topology_from_parametrization (α : ℝ) (s : Set (FlatTorus 2))
    (t : TopologicalSpace s) (h : @Homeomorph ℝ s inferInstance t)
    (hh : ∀ x, (h x).val = irrationalLine α x) :
    t < TopologicalSpace.induced (Subtype.val : s → FlatTorus 2) inferInstance := by
  have hc : @Continuous ℝ s inferInstance (TopologicalSpace.induced Subtype.val inferInstance) h := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x : ℝ => (h x).val)
    simpa only [hh] using IrrationalLine.continuous_line α
  have hle : t ≤ TopologicalSpace.induced (Subtype.val : s → FlatTorus 2) inferInstance := by
    simpa only [h.coinduced_eq] using hc.coinduced_le
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hE : @Topology.IsEmbedding ℝ s inferInstance (TopologicalSpace.induced Subtype.val inferInstance) h := by
    rw [← heq]
    exact h.isEmbedding
  letI : TopologicalSpace s := TopologicalSpace.induced
    (Subtype.val : s → FlatTorus 2) inferInstance
  have hcomp := Topology.IsEmbedding.subtypeVal.comp hE
  apply IrrationalLine.not_isEmbedding α
  simpa only [Function.comp_def, hh] using hcomp

/-- The original line parametrizes the whole intrinsic leaf. The global leaf
construction supplies its manifold structure and universal property; the
translated integral lines identify the entire connected leaf with one orbit. -/
theorem irrational_leaf : Specs.SmoothManifolds.Ch08.IrrationalLeaf.irrational_leafType := by
  intro α hα S Q hS hQ
  obtain ⟨hinj, hsmooth, himm⟩ := injective_immersion α hα S Q hS hQ
  refine ⟨hinj, hsmooth, himm, density α hα, ?_⟩
  obtain ⟨C, D, hD, hspan, hfamily⟩ :=
    IrrationalSlopeDistribution.slope_distribution α S Q hS hQ
  obtain ⟨A, hA, _, _, hleaves⟩ := GlobalLeaves.global_leaves D hD
  obtain ⟨T, hconn, _, hcharts, hint, huniv⟩ := hleaves (0 : FlatTorus 2)
  obtain ⟨hrange, hparam⟩ :=
    IrrationalOrbitLeaf.orbit_leaf α hα S Q hS hQ C D hfamily A hA T hconn huniv
  refine ⟨C, D, hspan, hD, A, hA, hrange, T, hconn, hcharts, hint, huniv, hparam, ?_⟩
  letI := leafTopology A 1 (0 : FlatTorus 2)
  obtain ⟨h, hh⟩ := hparam
  exact topology_from_parametrization α (leafSet A 1 (0 : FlatTorus 2))
    (leafTopology A 1 (0 : FlatTorus 2)) h.toHomeomorph hh

end SmoothManifolds.IrrationalLeaf
