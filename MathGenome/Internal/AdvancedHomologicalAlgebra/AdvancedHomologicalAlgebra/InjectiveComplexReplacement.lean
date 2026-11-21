import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InjectiveComplexReplacement
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedDerivedModels
import Mathlib.Algebra.Homology.Factorizations.CM5a
-- Contains adaptations from Mathlib (Joël Riou, Apache-2.0). See the notice below.
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AdvancedHomologicalAlgebra.InjectiveComplexReplacement

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- At the first nonzero source degree, injectivity on cohomology and monicity
in the following degree imply monicity on terms. -/
lemma mono_at_lower_bound {X I : CochainComplex A ℤ} (f : X ⟶ I) (a : ℤ)
    [X.IsStrictlyGE a] [QuasiIso f] [Mono (f.f (a + 1))] : Mono (f.f a) := by
  have : IsIso (X.homologyπ a) :=
    X.isIso_homologyπ (a - 1) a (by simp) (by
      exact (X.isZero_of_isStrictlyGE a (a - 1) (by omega)).eq_of_src _ _)
  have : Mono (cyclesMap f a) := by
    apply mono_of_mono_fac (homologyπ_naturality f a).symm
  rw [Preadditive.mono_iff_cancel_zero]
  intro T x hx
  have hd : x ≫ X.d a (a + 1) = 0 := by
    rw [← cancel_mono (f.f (a + 1)), Category.assoc, ← f.comm, ← Category.assoc,
      hx, zero_comp, zero_comp]
  have hz : X.liftCycles x (a + 1) (by simp) hd = 0 := by
    rw [← cancel_mono (cyclesMap f a), ← cancel_mono (I.iCycles a)]
    simp [hx]
  simpa using congrArg (fun z => z ≫ X.iCycles a) hz

/-- The projection to good lower truncation is an isomorphism strictly above
the cut. -/
lemma isIso_truncation_component (I : CochainComplex A ℤ) (a q : ℤ) (hq : a < q) :
    IsIso ((I.πTruncGE a).f q) := by
  let k : ℕ := (q - a).natAbs
  have hk : (ComplexShape.embeddingUpIntGE a).f k = q := by
    change a + ((q - a).natAbs : ℤ) = q
    rw [Int.natAbs_of_nonneg (by omega)]
    omega
  change IsIso ((HomologicalComplex.πTruncGE I (ComplexShape.embeddingUpIntGE a)).f q)
  dsimp only [HomologicalComplex.πTruncGE]
  apply (ComplexShape.Embedding.isIso_liftExtend_f_iff _ _ _ hk).mpr
  apply I.isIso_restrictionToTruncGE'
  rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
  intro h
  have : k = 0 := h
  simp [this] at hk
  omega

open Specs.AdvancedHomologicalAlgebra.InjectiveComplexReplacement

/-- HA-R01: a monic quasi-isomorphism to injectives with the identical lower bound. -/
theorem replacement : replacementType := by
  intro A _ _ _ X a hX
  have := hX
  have : HasDerivedCategory A := MorphismProperty.HasLocalization.standard _
  obtain ⟨L, i, hi, hiq, hL, hLb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective X
      (a - 1) a (by omega)
  have : L.IsGE a := by
    have hXa : X.IsGE a := inferInstance
    rw [← _root_.DerivedCategory.isGE_Q_obj_iff] at hXa ⊢
    exact _root_.DerivedCategory.TStructure.t.isGE_of_iso
      (asIso (_root_.DerivedCategory.Q.map i)) a
  have : QuasiIso (L.πTruncGE a) := inferInstance
  have : Injective (L.opcycles a) :=
    L.injective_opcycles (a - 1) a (L.exactAt_of_isGE a (a - 1))
  let f : X ⟶ L.truncGE a := i ≫ L.πTruncGE a
  have hfq : QuasiIso f := inferInstance
  have hf_above (q : ℤ) (hq : a < q) : Mono (f.f q) := by
    have := isIso_truncation_component L a q hq
    dsimp [f]
    infer_instance
  have hfa : Mono (f.f a) := by
    have := hf_above (a + 1) (by omega)
    exact mono_at_lower_bound f a
  refine ⟨L.truncGE a, f, ?_, hfq, ?_, inferInstance⟩
  · intro q
    obtain hq | rfl | hq := lt_trichotomy q a
    · exact (X.isZero_of_isStrictlyGE a q hq).mono _
    · exact hfa
    · exact hf_above q hq
  · intro q
    obtain hq | hq | hq := lt_trichotomy q a
    · exact ((L.truncGE a).isZero_of_isStrictlyGE a q hq).injective
    · subst q
      exact Injective.of_iso (L.truncGEXIsoOpcycles a).symm inferInstance
    · exact Injective.of_iso (L.truncGEXIso a q hq).symm (hL q)

/-- Apply the strict-model theorem before replacing a derived object. -/
theorem derivedRepresentative : derivedRepresentativeType := by
  intro A _ _ _ _ Y a hY
  obtain ⟨X, hX, ⟨e⟩⟩ :=
    (AdvancedHomologicalAlgebra.BoundedDerivedModels.strictModels A Y a a).1 hY
  obtain ⟨I, f, _, hf, hI, hIa⟩ := replacement A X a hX
  have := hf
  exact ⟨I, hI, hIa, ⟨e ≪≫ asIso (_root_.DerivedCategory.Q.map f)⟩⟩

/-- Every object of D⁺ is represented by a bounded below complex of injectives. -/
theorem plusRepresentative : plusRepresentativeType := by
  intro A _ _ _ _ Y
  obtain ⟨a, ha⟩ := Y.property
  have hYa : Y.obj.IsGE a := ha
  obtain ⟨I, hI, hIa, e⟩ := derivedRepresentative A Y.obj a
    ((_root_.DerivedCategory.isGE_iff Y.obj a).mp hYa)
  exact ⟨a, I, hI, hIa, e⟩

end AdvancedHomologicalAlgebra.InjectiveComplexReplacement


/-
Parts of this file (lines 56–91) are adapted from Mathlib.
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Homology/Factorizations/CM5a.lean#L669-L693
The lower-bound truncation was adapted to provide degreewise monomorphisms at the bound.
-/
