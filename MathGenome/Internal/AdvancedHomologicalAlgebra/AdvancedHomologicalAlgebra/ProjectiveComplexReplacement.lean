import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.BoundedDerivedModels
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.CochainComplexOpposite
-- Contains adaptations from Mathlib (Joël Riou, Apache-2.0). See the notice below.
set_option linter.checkUnivs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe w v u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace AdvancedHomologicalAlgebra.ProjectiveComplexReplacement

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- At the first supported degree, injectivity on cohomology and on the next
term imply injectivity on terms. -/
lemma mono_at_lower_bound {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ)
    [K.IsStrictlyGE n] [QuasiIsoAt f n] [Mono (f.f (n + 1))] : Mono (f.f n) := by
  have hd : K.d (n - 1) n = 0 :=
    (K.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _
  have : IsIso (K.homologyπ n) := K.isIso_homologyπ (n - 1) n (by simp) hd
  apply Preadditive.mono_of_cancel_zero
  intro T a ha
  have had : a ≫ K.d n (n + 1) = 0 := by
    rw [← cancel_mono (f.f (n + 1)), Category.assoc, ← f.comm, ← Category.assoc, ha,
      zero_comp, zero_comp]
  let c := K.liftCycles a (n + 1) (by simp) had
  have hc : c ≫ cyclesMap f n = 0 := by
    rw [← cancel_mono (L.iCycles n), Category.assoc, cyclesMap_i]
    simpa [c, ← Category.assoc] using ha
  have hc' : c ≫ K.homologyπ n = 0 := by
    rw [← cancel_mono (homologyMap f n), Category.assoc, homologyπ_naturality,
      ← Category.assoc, hc, zero_comp, zero_comp]
  have hc0 : c = 0 := by simpa using (cancel_mono (K.homologyπ n)).mp (by simpa using hc')
  calc
    a = c ≫ K.iCycles n := (K.liftCycles_i a _ _ had).symm
    _ = 0 := by rw [hc0, zero_comp]

/-- The usual injective replacement can be truncated to the original bound
without losing its monomorphism at the first nonzero degree. -/
lemma exists_mono_injective_replacement [EnoughInjectives A]
    (K : CochainComplex A ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    ∃ (L : CochainComplex A ℤ) (i : K ⟶ L),
      L.IsStrictlyGE n ∧ (∀ q : ℤ, Injective (L.X q)) ∧
      (∀ q : ℤ, Mono (i.f q)) ∧ QuasiIso i := by
  let : HasDerivedCategory A := HasDerivedCategory.standard A
  obtain ⟨L, i, hi, hi', hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K (n - 1) n (by simp)
  have : L.IsGE n := by
    have hK : K.IsGE n := inferInstance
    rw [← DerivedCategory.isGE_Q_obj_iff] at hK ⊢
    exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (DerivedCategory.Q.map i)) n
  have : Injective (L.opcycles n) :=
    L.injective_opcycles (n - 1) n (L.exactAt_of_isGE n (n - 1))
  let j := i ≫ L.πTruncGE n
  have hj : QuasiIso j := inferInstance
  have hjhi (q : ℤ) (hq : n < q) : Mono (j.f q) := by
    have : IsIso ((L.πTruncGE n).f q) :=
      AdvancedHomologicalAlgebra.GoodTruncations.projectionComponent_isIso L n q hq
    dsimp [j]
    infer_instance
  refine ⟨L.truncGE n, j, inferInstance, ?_, ?_, hj⟩
  · intro q
    rcases lt_trichotomy q n with h | heq | h
    · exact (CochainComplex.isZero_of_isStrictlyGE _ n _ h).injective
    · subst q
      exact Injective.of_iso (L.truncGEXIsoOpcycles n).symm inferInstance
    · exact Injective.of_iso (L.truncGEXIso n q h).symm (hL q)
  · intro q
    rcases lt_trichotomy q n with h | heq | h
    · exact (K.isZero_of_isStrictlyGE n q h).mono _
    · subst q
      have := hjhi (n + 1) (by omega)
      exact mono_at_lower_bound j n
    · exact hjhi q h

/-- Reversing integer degrees and taking opposites preserves quasi-isomorphisms. -/
lemma quasiIso_reverse_unop {K L : CochainComplex Aᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso (((CochainComplex.opEquivalence A).inverse.map f).unop) := by
  let R := (ChainComplex.cochainComplexEquivalence Aᵒᵖ).inverse
  have hR : QuasiIso (R.map f) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff' _ (n + 1) n (n - 1) (by simp) (by simp)]
    have h := (quasiIsoAt_iff' f (-(n + 1)) (-n) (-(n - 1))
      (by simp; omega) (by simp; omega)).mp (inferInstance : QuasiIsoAt f (-n))
    exact h
  exact inferInstanceAs (QuasiIso ((HomologicalComplex.unopFunctor A (.down ℤ)).map (R.map f).op))

theorem replacement : Specs.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement.replacementType := by
  intro A _ _ _ X b hX
  have := hX
  let E := CochainComplex.opEquivalence A
  let K := E.functor.obj (op X)
  have hK : K.IsStrictlyGE (-b) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (X.isZero_of_isStrictlyLE b (-n) (by omega)).op
  have := hK
  obtain ⟨L, i, hLb, hL, hi, hi'⟩ := exists_mono_injective_replacement K (-b)
  let P := (E.inverse.obj L).unop
  let q : P ⟶ (E.inverse.obj K).unop := (E.inverse.map i).unop
  let e : (E.inverse.obj K).unop ≅ X := (E.unitIso.app (op X)).unop
  have hq : QuasiIso q := quasiIso_reverse_unop i
  have hP : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (L.isZero_of_isStrictlyGE (-b) (-n) (by omega)).unop
  have hproj (n : ℤ) : Projective (P.X n) := by
    have := hL (-n)
    exact inferInstanceAs (Projective (unop (L.X (-n))))
  have hepi (n : ℤ) : Epi (q.f n) := by
    have := hi (-n)
    exact inferInstanceAs (Epi ((i.f (-n)).unop))
  refine ⟨P, q ≫ e.hom, hP, hproj, ?_, inferInstance⟩
  intro n
  have := hepi n
  dsimp
  infer_instance

theorem derivedRepresentative :
    Specs.AdvancedHomologicalAlgebra.ProjectiveComplexReplacement.derivedRepresentativeType := by
  intro A _ _ _ _ X
  obtain ⟨b, hb⟩ := X.property
  obtain ⟨L, hLb, ⟨e⟩⟩ := X.obj.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, p, hPb, hP, hp, hp'⟩ := replacement A L b hLb
  exact ⟨b, P, hPb, hP, ⟨e ≪≫ (asIso (DerivedCategory.Q.map p)).symm⟩⟩

end AdvancedHomologicalAlgebra.ProjectiveComplexReplacement

/-
Parts of this file (lines 41–75) are adapted from Mathlib.
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Homology/Factorizations/CM5a.lean#L669-L693
The truncation was adapted with a degreewise monomorphism before dualizing to the projective replacement.
-/
