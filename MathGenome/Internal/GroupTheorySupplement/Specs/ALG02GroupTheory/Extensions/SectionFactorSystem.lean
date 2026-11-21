import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
Independent specification for the extraction and change of factor systems and the
outer and abelian actions in paper.tex:325–344, 351–359, 380–381.
-/

namespace Specs.ALG02GroupTheory.Extensions

universe u v w

-- The expected types retain independent universes for the groups.
set_option linter.checkUnivs false

/-- Normalized factor-system data for a left action up to inner automorphisms. -/
structure NormalizedFactorSystem (N : Type u) (Q : Type w) [Group N] [Group Q] where
  alpha : Q → MulAut N
  factor : Q → Q → N
  alpha_one : alpha 1 = 1
  factor_one_left : ∀ q, factor 1 q = 1
  factor_one_right : ∀ q, factor q 1 = 1
  alpha_mul : ∀ q r, alpha q * alpha r = MulAut.conj (factor q r) * alpha (q * r)
  factor_assoc : ∀ q r t,
    factor q r * factor (q * r) t = alpha q (factor r t) * factor q (r * t)

def FactorSystemType := ∀ (N : Type u) (Q : Type w) [Group N] [Group Q], Type (max u w)

def factorSystemValue : FactorSystemType.{u, w} :=
  fun N Q _ _ => NormalizedFactorSystem N Q

def InnerAutomorphismsType := ∀ (N : Type u) [Group N], Subgroup (MulAut N)

abbrev innerAutomorphismsValue (N : Type u) [Group N] : Subgroup (MulAut N) :=
  (MulAut.conj : N →* MulAut N).range

instance innerAutomorphismsNormal (N : Type u) [Group N] : (innerAutomorphismsValue N).Normal where
  conj_mem := by
    rintro _ ⟨n, rfl⟩ beta
    refine ⟨beta n, ?_⟩
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

def OuterAutType := ∀ (N : Type u) [Group N], Type u

abbrev outerAutValue (N : Type u) [Group N] : Type u :=
  MulAut N ⧸ innerAutomorphismsValue N

def OuterClassType := ∀ (N : Type u) [Group N], MulAut N →* outerAutValue N

def outerClassValue (N : Type u) [Group N] : MulAut N →* outerAutValue N :=
  QuotientGroup.mk' (innerAutomorphismsValue N)

theorem outerClassValue_conj {N : Type u} [Group N] (n : N) :
    outerClassValue N (MulAut.conj n) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ⟨n, rfl⟩

def InnerAutomorphismsNormal : Prop :=
  ∀ (N : Type u) [Group N], (innerAutomorphismsValue N).Normal

variable {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]

def SectionAlphaType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q), normalizedSectionValue S → Q → MulAut N

noncomputable def sectionAlphaValue (S : GroupExtension N E Q)
    (s : normalizedSectionValue S) (q : Q) : MulAut N :=
  S.conjAct (s.val q)

def SectionFactorType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q), normalizedSectionValue S → Q → Q → N

/-- Invert the prescribed inclusion on the kernel of the prescribed projection. -/
noncomputable def kernelPreimage (S : GroupExtension N E Q) (e : E)
    (he : S.rightHom e = 1) : N :=
  (MonoidHom.ofInjective S.inl_injective).symm
    ⟨e, S.range_inl_eq_ker_rightHom.symm ▸ S.rightHom.mem_ker.mpr he⟩

theorem inl_kernelPreimage (S : GroupExtension N E Q) (e : E)
    (he : S.rightHom e = 1) : S.inl (kernelPreimage S e he) = e :=
  MonoidHom.apply_ofInjective_symm S.inl_injective _

noncomputable def sectionFactorValue (S : GroupExtension N E Q)
    (s : normalizedSectionValue S) (q r : Q) : N :=
  kernelPreimage S (s.val q * s.val r * (s.val (q * r))⁻¹) (by simp)

def SectionChangeType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q), normalizedSectionValue S → normalizedSectionValue S → Q → N

noncomputable def sectionChangeValue (S : GroupExtension N E Q)
    (s s' : normalizedSectionValue S) (q : Q) : N :=
  kernelPreimage S (s'.val q * (s.val q)⁻¹) (by simp)

def SectionAlphaFormula : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S) (q : Q) (n : N),
    S.inl (sectionAlphaValue S s q n) = s.val q * S.inl n * (s.val q)⁻¹

def SectionFactorFormula : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S) (q r : Q),
    S.inl (sectionFactorValue S s q r) = s.val q * s.val r * (s.val (q * r))⁻¹

def SectionFactorSystem : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S),
    ∃ D : NormalizedFactorSystem N Q,
      D.alpha = sectionAlphaValue S s ∧ D.factor = sectionFactorValue S s

def SectionChangeUnique : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s s' : normalizedSectionValue S),
    sectionChangeValue S s s' 1 = 1 ∧
      (∀ q, s'.val q = S.inl (sectionChangeValue S s s' q) * s.val q) ∧
      ∀ b : Q → N, (∀ q, s'.val q = S.inl (b q) * s.val q) → b = sectionChangeValue S s s'

def ChangeOfSection : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s s' : normalizedSectionValue S) (b : Q → N),
    (∀ q, s'.val q = S.inl (b q) * s.val q) →
    (∀ q, sectionAlphaValue S s' q = MulAut.conj (b q) * sectionAlphaValue S s q) ∧
    ∀ q r, sectionFactorValue S s' q r =
      b q * sectionAlphaValue S s q (b r) * sectionFactorValue S s q r * (b (q * r))⁻¹

/-- Conjugation within the embedded kernel is inner conjugation. -/
theorem conjAct_inl (S : GroupExtension N E Q) (n : N) :
    S.conjAct (S.inl n) = MulAut.conj n := by
  ext x
  apply S.inl_injective
  simp only [S.inl_conjAct_comm, MulAut.conj_apply, map_mul, map_inv]

/-- Descend conjugation along the prescribed projection when inner conjugations act trivially. -/
noncomputable def descendConjugation {H : Type*} [Group H] (S : GroupExtension N E Q)
    (f : MulAut N →* H) (hf : ∀ n, f (MulAut.conj n) = 1) : Q →* H :=
  S.rightHom.liftOfSurjective S.rightHom_surjective
    ⟨f.comp S.conjAct, by
      intro e he
      rw [← S.range_inl_eq_ker_rightHom] at he
      obtain ⟨n, rfl⟩ := he
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, conjAct_inl] using hf n⟩

theorem descendConjugation_apply {H : Type*} [Group H] (S : GroupExtension N E Q)
    (f : MulAut N →* H) (hf : ∀ n, f (MulAut.conj n) = 1) (e : E) :
    descendConjugation S f hf (S.rightHom e) = f (S.conjAct e) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

def OuterActionType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q],
    GroupExtension N E Q → (Q →* outerAutValue N)

noncomputable def outerActionValue (S : GroupExtension N E Q) : Q →* outerAutValue N :=
  descendConjugation S (outerClassValue N) outerClassValue_conj

def OuterActionFormula : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (e : E),
    outerActionValue S (S.rightHom e) = outerClassValue N (S.conjAct e)

def OuterActionOfSection : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [Group N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S) (q : Q),
    outerActionValue S q = outerClassValue N (sectionAlphaValue S s q)

def AbelianActionType :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [CommGroup N] [Group E] [Group Q],
    GroupExtension N E Q → (Q →* MulAut N)

theorem conj_eq_one {N : Type u} [CommGroup N] (n : N) : MulAut.conj n = 1 := by
  ext x
  simp [mul_comm n x, mul_assoc]

noncomputable def abelianActionValue {N : Type u} {E : Type v} {Q : Type w}
    [CommGroup N] [Group E] [Group Q] (S : GroupExtension N E Q) : Q →* MulAut N :=
  descendConjugation S (MonoidHom.id (MulAut N)) conj_eq_one

def AbelianActionFormula : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [CommGroup N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (e : E),
    abelianActionValue S (S.rightHom e) = S.conjAct e

def AbelianActionOfSection : Prop :=
  ∀ {N : Type u} {E : Type v} {Q : Type w} [CommGroup N] [Group E] [Group Q]
    (S : GroupExtension N E Q) (s : normalizedSectionValue S) (q : Q),
    abelianActionValue S q = sectionAlphaValue S s q

end Specs.ALG02GroupTheory.Extensions
