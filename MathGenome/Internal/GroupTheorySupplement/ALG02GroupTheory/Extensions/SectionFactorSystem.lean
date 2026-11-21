import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.Basic
import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.SectionFactorSystem
import Mathlib.Tactic.Group

namespace ALG02GroupTheory.Extensions

open Specs.ALG02GroupTheory.Extensions (NormalizedFactorSystem)

abbrev FactorSystem := NormalizedFactorSystem

/-- The image of conjugation by elements of the kernel. -/
abbrev innerAutomorphisms := Specs.ALG02GroupTheory.Extensions.innerAutomorphismsValue

theorem innerAutomorphismsNormal (N : Type*) [Group N] : (innerAutomorphisms N).Normal :=
  inferInstanceAs (Specs.ALG02GroupTheory.Extensions.innerAutomorphismsValue N).Normal

/-- The quotient of automorphisms by inner automorphisms. -/
abbrev OuterAut := Specs.ALG02GroupTheory.Extensions.outerAutValue

def outerClass := Specs.ALG02GroupTheory.Extensions.outerClassValue

section

variable {N E Q : Type*} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q)
variable (s s' : NormalizedSection S)

/-- The automorphism given by conjugation by the chosen section value. -/
noncomputable def sectionAlpha (q : Q) : MulAut N :=
  S.conjAct (s.val q)

/-- The defect of multiplicativity of a normalized section, valued in the kernel. -/
noncomputable def sectionFactor (q r : Q) : N :=
  Specs.ALG02GroupTheory.Extensions.sectionFactorValue S s q r

/-- The kernel element translating each value of the old section to the new one. -/
noncomputable def sectionChange (q : Q) : N :=
  Specs.ALG02GroupTheory.Extensions.sectionChangeValue S s s' q

theorem inl_sectionAlpha (q : Q) (n : N) :
    S.inl (sectionAlpha S s q n) = s.val q * S.inl n * (s.val q)⁻¹ :=
  S.inl_conjAct_comm

theorem inl_sectionFactor (q r : Q) :
    S.inl (sectionFactor S s q r) = s.val q * s.val r * (s.val (q * r))⁻¹ :=
  Specs.ALG02GroupTheory.Extensions.inl_kernelPreimage S _ (by simp)

private theorem section_mul (q r : Q) :
    s.val q * s.val r = S.inl (sectionFactor S s q r) * s.val (q * r) := by
  rw [inl_sectionFactor, inv_mul_cancel_right]

/-- The data extracted from a normalized section satisfy both factor-system identities. -/
noncomputable def factorSystemOfSection : FactorSystem N Q where
  alpha := sectionAlpha S s
  factor := sectionFactor S s
  alpha_one := by simp only [sectionAlpha, s.property, map_one]
  factor_one_left q := by
    apply S.inl_injective
    simp only [inl_sectionFactor, s.property, one_mul, mul_inv_cancel, map_one]
  factor_one_right q := by
    apply S.inl_injective
    simp only [inl_sectionFactor, s.property, mul_one, mul_inv_cancel, map_one]
  alpha_mul q r := by
    unfold sectionAlpha
    rw [← map_mul, section_mul S s q r, map_mul,
      Specs.ALG02GroupTheory.Extensions.conjAct_inl]
  factor_assoc q r t := by
    apply S.inl_injective
    simp only [map_mul, inl_sectionAlpha, inl_sectionFactor, mul_assoc q r t]
    group

theorem sectionFactorSystem :
    ∃ D : FactorSystem N Q, D.alpha = sectionAlpha S s ∧ D.factor = sectionFactor S s :=
  ⟨factorSystemOfSection S s, rfl, rfl⟩

private theorem inl_sectionChange (q : Q) :
    S.inl (sectionChange S s s' q) = s'.val q * (s.val q)⁻¹ :=
  Specs.ALG02GroupTheory.Extensions.inl_kernelPreimage S _ (by simp)

theorem sectionChangeUnique :
    sectionChange S s s' 1 = 1 ∧
      (∀ q, s'.val q = S.inl (sectionChange S s s' q) * s.val q) ∧
      ∀ b : Q → N, (∀ q, s'.val q = S.inl (b q) * s.val q) → b = sectionChange S s s' := by
  refine ⟨?_, ?_, ?_⟩
  · apply S.inl_injective
    simp only [inl_sectionChange, s.property, s'.property, inv_one, one_mul, map_one]
  · intro q
    rw [inl_sectionChange, inv_mul_cancel_right]
  · intro b hb
    funext q
    apply S.inl_injective
    rw [inl_sectionChange, hb q, mul_inv_cancel_right]

theorem changeOfSection (b : Q → N) (hb : ∀ q, s'.val q = S.inl (b q) * s.val q) :
    (∀ q, sectionAlpha S s' q = MulAut.conj (b q) * sectionAlpha S s q) ∧
      ∀ q r, sectionFactor S s' q r =
        b q * sectionAlpha S s q (b r) * sectionFactor S s q r * (b (q * r))⁻¹ := by
  constructor
  · intro q
    rw [sectionAlpha, hb, map_mul, Specs.ALG02GroupTheory.Extensions.conjAct_inl]
    rfl
  · intro q r
    apply S.inl_injective
    simp only [map_mul, map_inv, inl_sectionAlpha, inl_sectionFactor, hb]
    group

/-- Conjugation on the kernel modulo inner automorphisms descends to the quotient. -/
noncomputable def outerAction : Q →* OuterAut N :=
  Specs.ALG02GroupTheory.Extensions.outerActionValue S

theorem outerActionFormula (e : E) :
    outerAction S (S.rightHom e) = outerClass N (S.conjAct e) :=
  Specs.ALG02GroupTheory.Extensions.descendConjugation_apply S _
    Specs.ALG02GroupTheory.Extensions.outerClassValue_conj e

theorem outerActionOfSection (q : Q) :
    outerAction S q = outerClass N (sectionAlpha S s q) := by
  simpa only [s.val.rightHom_section, sectionAlpha] using outerActionFormula S (s.val q)

end

section

variable {N E Q : Type*} [CommGroup N] [Group E] [Group Q] (S : GroupExtension N E Q)

/-- With an abelian kernel, conjugation itself descends to the quotient. -/
noncomputable def abelianAction : Q →* MulAut N :=
  Specs.ALG02GroupTheory.Extensions.abelianActionValue S

theorem abelianActionFormula (e : E) :
    abelianAction S (S.rightHom e) = S.conjAct e :=
  Specs.ALG02GroupTheory.Extensions.descendConjugation_apply S (MonoidHom.id (MulAut N))
    Specs.ALG02GroupTheory.Extensions.conj_eq_one e

theorem abelianActionOfSection (s : NormalizedSection S) (q : Q) :
    abelianAction S q = sectionAlpha S s q := by
  simpa only [s.val.rightHom_section, sectionAlpha] using abelianActionFormula S (s.val q)

end

end ALG02GroupTheory.Extensions
