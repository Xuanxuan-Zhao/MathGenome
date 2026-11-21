import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.InverseLimit.Gluing
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.KrullTopology.InitialDescriptions
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.InverseLimit.Profiniteness

/-! # Topological inverse limit and profiniteness (FT-T06)
The two directions of continuity use the finite-restriction initial topology.
Compatibility is a closed condition in the product of finite discrete groups.
-/

universe u v
noncomputable section
namespace AdvancedFieldTheory

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- Every restriction compatibility equation cuts out a closed set. -/
theorem compatibleTuplesSubgroup_isClosed (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    IsClosed (compatibleTuplesSubgroup K L :
      Set (∀ E : finiteGaloisStage K L, finiteStageGroup E)) := by
  have heq : (compatibleTuplesSubgroup K L :
      Set (∀ E : finiteGaloisStage K L, finiteStageGroup E)) =
      ⋂ (E : finiteGaloisStage K L) (F : finiteGaloisStage K L) (h : E ≤ F),
        {σ | finiteStageTransition h (σ F) = σ E} := by
    ext σ
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rfl
  rw [heq]
  exact isClosed_iInter fun E => isClosed_iInter fun F => isClosed_iInter fun h =>
    isClosed_eq ((finiteStageTransition h).continuous.comp (continuous_apply F))
      (continuous_apply E)

instance compatibleTuples_compactSpace : CompactSpace (compatibleTuples K L) :=
  isCompact_iff_compactSpace.mp (compatibleTuplesSubgroup_isClosed K L).isCompact

variable [IsGalois K L]

/-- The coordinates of rho are the continuous finite restrictions. -/
theorem continuous_canonicalRestriction : Continuous (canonicalRestriction K L) := by
  apply Continuous.subtype_mk
  apply continuous_pi (A := fun E : finiteGaloisStage K L => finiteStageGroup E)
  intro E
  let F : FiniteGaloisIntermediateField K L :=
    { toIntermediateField := E.val
      finiteDimensional := E.property.1
      isGalois := E.property.2 }
  exact ((KrullTopology.continuous_iff_finiteRestrictions K L
    (id : GaloisGroup K L → GaloisGroup K L)).mp continuous_id) F

/-- The canonical restriction isomorphism, with the source's projection formulas. -/
theorem canonicalRestriction_topologicalIsomorphism (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    ∃! e : GaloisGroup K L ≃ₜ* compatibleTuples K L,
      e.toMulEquiv.toMonoidHom = canonicalRestriction K L ∧
      ∀ (E : finiteGaloisStage K L) (σ : GaloisGroup K L),
        compatibleTupleProjection E (e σ) = restriction E.val σ := by
  let e := MulEquiv.ofBijective (canonicalRestriction K L)
    (canonicalRestriction_bijective K L)
  have hi : Continuous e.symm := by
    apply (KrullTopology.continuous_iff_finiteRestrictions K L e.symm).mpr
    intro F
    let E : finiteGaloisStage K L :=
      ⟨F.toIntermediateField, inferInstance, inferInstance⟩
    have heq : (fun τ => restriction F.toIntermediateField (e.symm τ)) =
        (fun τ => compatibleTupleProjection E τ) := by
      funext τ
      exact congrArg (fun t : compatibleTuples K L => t.val E) (e.apply_symm_apply τ)
    rw [heq]
    exact (compatibleTupleProjection E).continuous
  let c : GaloisGroup K L ≃ₜ* compatibleTuples K L :=
    { e with
      continuous_toFun := continuous_canonicalRestriction
      continuous_invFun := hi }
  refine ⟨c, ⟨rfl, fun E σ => rfl⟩, ?_⟩
  intro c' hc'
  apply ContinuousMulEquiv.ext
  intro σ
  exact DFunLike.congr_fun hc'.1 σ

/-- Compactness is transported from the closed subspace of the finite product. -/
instance galoisGroup_compactSpace (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    CompactSpace (GaloisGroup K L) := by
  obtain ⟨e, _, _⟩ := canonicalRestriction_topologicalIsomorphism K L
  exact e.toHomeomorph.symm.compactSpace

/-- The finite product separates points; this remains true on the inverse limit. -/
theorem galoisGroup_t2Space (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    T2Space (GaloisGroup K L) := by
  obtain ⟨e, _, _⟩ := canonicalRestriction_topologicalIsomorphism K L
  exact e.toHomeomorph.symm.t2Space

/-- Products of discrete spaces, and their subspaces, are totally disconnected. -/
theorem galoisGroup_totallyDisconnectedSpace (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    TotallyDisconnectedSpace (GaloisGroup K L) := by
  obtain ⟨e, _, _⟩ := canonicalRestriction_topologicalIsomorphism K L
  exact e.toHomeomorph.symm.totallyDisconnectedSpace

end AdvancedFieldTheory
