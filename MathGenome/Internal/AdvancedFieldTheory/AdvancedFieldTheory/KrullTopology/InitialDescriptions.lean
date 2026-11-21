import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.FiniteKernels
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.KrullTopology.InitialDescriptions

/-! The initial descriptions of the Krull topology (FT-T03).
Both descriptions are given by their universal property for an arbitrary
source space, with explicitly discrete targets. -/

universe u v w
noncomputable section
open scoped Pointwise Topology
open TopologicalSpace

namespace AdvancedFieldTheory.KrullTopology

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

private theorem mem_coset_stabilizer (σ τ : L ≃ₐ[K] L) (S : Set L) :
    τ ∈ σ • (finiteStabilizer K L S : Set (L ≃ₐ[K] L)) ↔
      ∀ x ∈ S, τ x = σ x := by
  rw [mem_leftCoset_iff]
  change (∀ x ∈ S, σ.symm (τ x) = x) ↔ _
  constructor
  · intro h x hx
    simpa using congrArg σ (h x hx)
  · intro h x hx
    rw [h x hx, σ.symm_apply_apply]

variable [IsGalois K L]

private theorem evaluation_continuous (x : L) :
    @Continuous (L ≃ₐ[K] L) L _ ⊥ (fun σ => σ x) := by
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  apply continuous_discrete_rng.mpr
  intro y
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  refine Filter.mem_of_superset
    (((finiteStabilizer_isOpen ({x} : Set L) (Set.finite_singleton x)).leftCoset σ).mem_nhds
      (show σ ∈ σ • (finiteStabilizer K L {x} : Set (L ≃ₐ[K] L)) from
        ⟨1, (finiteStabilizer K L {x}).one_mem, mul_one σ⟩)) ?_
  intro τ hτ
  have h := (mem_coset_stabilizer σ τ {x}).mp hτ x rfl
  exact h.trans hσ

/-- The full universal property for all evaluations to discrete L. -/
theorem continuous_iff_evaluations (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (f : X → (L ≃ₐ[K] L)) :
    Continuous f ↔ ∀ x : L, @Continuous X L _ ⊥ (fun z => f z x) := by
  let : TopologicalSpace L := ⊥
  let : DiscreteTopology L := ⟨rfl⟩
  constructor
  · intro hf x
    exact (evaluation_continuous x).comp hf
  · intro hf
    apply (finiteCosetBasis_isTopologicalBasis K L).continuous_iff.mpr
    rintro U ⟨σ, S, hS, rfl⟩
    have heq : f ⁻¹' (σ • (finiteStabilizer K L S : Set (L ≃ₐ[K] L))) =
        ⋂ x ∈ S, (fun z => f z x) ⁻¹' {σ x} := by
      ext z
      simp only [Set.mem_preimage, mem_coset_stabilizer, Set.mem_iInter,
        Set.mem_singleton_iff]
    rw [heq]
    exact hS.isOpen_biInter fun x _ => (isOpen_discrete _).preimage (hf x)

omit [IsGalois K L] in
private theorem finiteRestriction_continuous (E : FiniteGaloisIntermediateField K L) :
    @Continuous (L ≃ₐ[K] L) (E ≃ₐ[K] E) _ ⊥ (restriction E.toIntermediateField) := by
  let : TopologicalSpace (E ≃ₐ[K] E) := ⊥
  let : DiscreteTopology (E ≃ₐ[K] E) := ⟨rfl⟩
  apply continuous_discrete_rng.mpr
  intro q
  rw [isOpen_iff_mem_nhds]
  intro σ hσ
  refine Filter.mem_of_superset
    (((finiteGaloisKernel_isOpen E).leftCoset σ).mem_nhds
      (show σ ∈ σ • (finiteGaloisKernel E : Set (L ≃ₐ[K] L)) from
        ⟨1, (finiteGaloisKernel E).one_mem, mul_one σ⟩)) ?_
  rintro τ ⟨h, hh, rfl⟩
  change restriction E.toIntermediateField (σ * h) = q
  rw [map_mul]
  have hh' : restriction E.toIntermediateField h = 1 := hh
  rw [hh', mul_one]
  exact hσ

/-- The full universal property for restrictions to every finite Galois stage. -/
theorem continuous_iff_finiteRestrictions (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {X : Type w} [TopologicalSpace X] (f : X → (L ≃ₐ[K] L)) :
    Continuous f ↔ ∀ E : FiniteGaloisIntermediateField K L,
      @Continuous X (E ≃ₐ[K] E) _ ⊥ (fun z => restriction E.toIntermediateField (f z)) := by
  constructor
  · intro hf E
    let : TopologicalSpace (E ≃ₐ[K] E) := ⊥
    exact (finiteRestriction_continuous E).comp hf
  · intro hf
    apply (continuous_iff_evaluations K L f).mpr
    intro x
    obtain ⟨E, hxE, hfin, hgal⟩ :=
      exists_finite_galois_containing K L {x} (Set.finite_singleton x)
    let F : FiniteGaloisIntermediateField K L :=
      { toIntermediateField := E, finiteDimensional := hfin, isGalois := hgal }
    let : TopologicalSpace L := ⊥
    let : DiscreteTopology L := ⟨rfl⟩
    let : TopologicalSpace (F ≃ₐ[K] F) := ⊥
    let : DiscreteTopology (F ≃ₐ[K] F) := ⟨rfl⟩
    have hc : Continuous (fun q : F ≃ₐ[K] F => (q ⟨x, hxE rfl⟩ : L)) :=
      continuous_of_discreteTopology
    have h := hc.comp (hf F)
    simpa only [Function.comp_def, restriction_apply] using h

end AdvancedFieldTheory.KrullTopology
