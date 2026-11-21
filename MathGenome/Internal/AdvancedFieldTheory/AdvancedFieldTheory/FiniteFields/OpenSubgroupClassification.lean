import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.OpenSubgroupClassification
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.ProfiniteIntegers.ProjectionKernels
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.FiniteFields.AbsoluteGaloisGroup
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.InfiniteGalois
import MathGenome.Internal.AdvancedFieldTheory.AdvancedFieldTheory.Correspondence.OpenFiniteFields

universe u v
noncomputable section
namespace AdvancedFieldTheory.FiniteFields
open ProfiniteIntegers
open Specs.AdvancedFieldTheory.OpenSubgroups

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
local instance : IsGalois k Ω := algebraicClosure_isGalois k Ω

omit [IsAlgClosure k Ω] in
/-- Zero exponent is precisely identity restriction, for the specified Θ. -/
theorem kernel_pullback (coords : Coordinates k Ω)
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative Zhat)
    (he : CoordinateAction coords e) (n : ℕ+) :
    pullback e (π n).ker = (finiteRootField k Ω n).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  change π n (e σ).toAdd = 0 ↔ ∀ x ∈ finiteRootField k Ω n, σ x = x
  constructor
  · intro h x hx
    have hh := he σ n ⟨x, hx⟩
    change (coords n (Multiplicative.ofAdd (π n (e σ).toAdd)) ⟨x, hx⟩ : Ω) = σ x at hh
    rw [h] at hh
    simpa only [ofAdd_zero, map_one, AlgEquiv.one_apply] using hh.symm
  · intro h
    have hid : coords n (Multiplicative.ofAdd (π n (e σ).toAdd)) = 1 := by
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (he σ n x).trans (h x x.property)
    have hz := (coords n).injective (hid.trans (map_one (coords n)).symm)
    exact congrArg Multiplicative.toAdd hz

/-- The kernel identity for the unique arithmetic Frobenius map supplied
by E06, with its coordinate formula and normalization preserved. -/
theorem arithmeticKernelCorrespondence :
    Specs.AdvancedFieldTheory.OpenSubgroups.arithmeticKernelCorrespondence_type.{u,v} := by
  intro k Ω _ _ _ _ _
  obtain ⟨coords, hc, e, he, hu⟩ := AbsoluteGalois.absoluteGaloisGroup k Ω
  refine ⟨coords, hc, e, ⟨he, ?_⟩, ?_⟩
  · intro n
    exact kernel_pullback k Ω coords e he.1 n
  · intro e' he'
    exact hu e' he'.1

theorem layerProperties : Specs.AdvancedFieldTheory.OpenSubgroups.layerProperties_type.{u,v} := by
  intro k Ω _ _ _ _ _ coords e he n
  have hp := kernel_pullback k Ω coords e he n
  have hi : (finiteRootField k Ω n).fixingSubgroup.index = (n : ℕ) := by
    rw [← hp]
    change (((π n).ker.toSubgroup).comap e.toMonoidHom).index = _
    rw [Subgroup.index_comap_of_surjective _ e.surjective,
      AddSubgroup.index_toSubgroup]
    exact index_ker_π n
  refine ⟨ker_π n, hp, index_ker_π n, hi, ?_, (clopen_ker_π n).isOpen, ?_⟩
  · change IntermediateField.fixedField (pullback e (π n).ker) = finiteRootField k Ω n
    rw [hp]
    exact fixedField_fixingSubgroup k Ω _
  · exact (fixingSubgroup_isOpen_iff_finiteDimensional k Ω _).mpr
      (finiteRootField_finite_galois k Ω n n.pos).1

/-- Openness makes a subgroup closed; C04 recovers it from its finite fixed
field, which E03 identifies by its degree. -/
theorem galoisClassification :
    Specs.AdvancedFieldTheory.OpenSubgroups.galoisClassification_type.{u,v} := by
  intro k Ω _ _ _ _ _ H hH
  let : IsGalois k Ω := algebraicClosure_isGalois k Ω
  have hrec : (IntermediateField.fixedField H).fixingSubgroup = H := by
    change fixingSubgroup (fixedField H) = H
    rw [fixingSubgroup_fixedField_eq_topologicalClosure]
    apply SetLike.ext'
    exact (H.isClosed_of_isOpen hH).closure_eq
  have hrec' : fixingSubgroup (fixedField H) = H := hrec
  have hfin : FiniteDimensional k (IntermediateField.fixedField H) :=
    (fixingSubgroup_isOpen_iff_finiteDimensional k Ω _).mp (by
      change IsOpen (fixingSubgroup (fixedField H) : Set (Ω ≃ₐ[k] Ω))
      rw [hrec']
      exact hH)
  let := hfin
  obtain ⟨hd, hf⟩ := finite_intermediateField_eq_rootField k Ω (IntermediateField.fixedField H)
  refine ⟨⟨Module.finrank k (IntermediateField.fixedField H), hd⟩,
    ?_, ?_, hfin, rfl⟩
  · change H = (finiteRootField k Ω (Module.finrank k (IntermediateField.fixedField H))).fixingSubgroup
    rw [← hf, hrec]
  · intro m hm
    have hfield : IntermediateField.fixedField H = finiteRootField k Ω m := by
      rw [hm]
      exact fixedField_fixingSubgroup k Ω _
    apply Subtype.ext
    change (m : ℕ) = Module.finrank k (IntermediateField.fixedField H)
    rw [hfield]
    exact (finiteRootField_finrank k Ω m m.pos).symm

theorem residueClassification :
    Specs.AdvancedFieldTheory.OpenSubgroups.residueClassification_type.{u,v} := by
  intro k Ω _ _ _ _ _ coords e he H hH
  have hopen : IsOpen (pullback e H : Set (Ω ≃ₐ[k] Ω)) :=
    hH.preimage e.continuous
  obtain ⟨n, hn⟩ := galoisClassification k Ω (pullback e H) hopen
  have hker : H = (π n).ker := by
    apply SetLike.ext
    intro a
    obtain ⟨σ, hσ⟩ := e.surjective (Multiplicative.ofAdd a)
    have hmem := SetLike.ext_iff.mp
      (hn.1.trans (kernel_pullback k Ω coords e he n).symm) σ
    change (e σ).toAdd ∈ H ↔ (e σ).toAdd ∈ (π n).ker at hmem
    simpa only [hσ, toAdd_ofAdd] using hmem
  refine ⟨n, hker, ?_, hker.trans (ker_π n), ?_, hn.2.2.1, hn.2.2.2⟩
  · intro m hm
    change H = (π m).ker at hm
    apply Subtype.ext
    calc
      (m : ℕ) = (π m).ker.index := (index_ker_π m).symm
      _ = H.index := congrArg AddSubgroup.index hm.symm
      _ = (π n).ker.index := congrArg AddSubgroup.index hker
      _ = (n : ℕ) := index_ker_π n
  · rw [hker]
    exact index_ker_π n

theorem modulusOne : Specs.AdvancedFieldTheory.OpenSubgroups.modulusOne_type.{u,v} := by
  intro k Ω _ _ _ _ _
  refine ⟨?_, ?_, finiteRootField_one k Ω⟩
  · apply eq_top_iff.mpr
    intro a _
    change (π 1 a : ZMod 1) = 0
    exact @Subsingleton.elim (ZMod 1) (ZMod.subsingleton_iff.mpr rfl) _ _
  · rw [show Specs.AdvancedFieldTheory.rootField k Ω 1 = ⊥ from finiteRootField_one k Ω]
    exact IntermediateField.fixingSubgroup_bot

end AdvancedFieldTheory.FiniteFields
