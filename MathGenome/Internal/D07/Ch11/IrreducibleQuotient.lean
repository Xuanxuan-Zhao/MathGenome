import MathGenome.Internal.Specs.D07.Ch11.IrreducibleQuotient
import MathGenome.Internal.D07.Ch09.MaximalQuotient
import MathGenome.Internal.D07.Ch10.PidPrimeMaximal
import MathGenome.Internal.D07.Ch11.FieldPolynomialPid
import MathGenome.Internal.D07.Ch11.EvaluationUniversal
import MathGenome.Internal.D07.Ch11.DegreeArithmetic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Field.Equiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Adjoining a root by the canonical principal-ideal quotient, including the
degenerate cases and the real quadratic example (K07.11.irreducible_quotient).
-/

universe u

namespace D07.Ch11.IrreducibleQuotient

open Polynomial
open Specs.D07.Ch11.IrreducibleQuotient

theorem quotientFieldIffIrreducible : QuotientFieldIffIrreducible.{u} := by
  intro F _ f hf
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  exact (Ch09.MaximalQuotient.maximal_iff_isField_quotient
    (Polynomial F) (Ideal.span {f})).symm.trans
    (Ch10.PidPrimeMaximal.irreducible_iff_maximal (Polynomial F)
      (FieldPolynomialPid.fieldPolynomialPID F) f hf0).symm

theorem quotientRootEquation : QuotientRootEquation.{u} := by
  intro F _ f
  let π := Ideal.Quotient.mk (Ideal.span {f})
  have heval : eval₂RingHom (π.comp C) (π X) = π :=
    Polynomial.ringHom_ext (fun a => by simp [π]) (by simp)
  change (eval₂RingHom (π.comp C) (π X)) f = 0
  rw [heval]
  exact Ideal.Quotient.mk_singleton_self f

private theorem positiveDegreeOfNonunit {F : Type u} [Field F]
    {p : Polynomial F} (hp : p ≠ 0) (hu : ¬ IsUnit p) : 0 < p.natDegree := by
  apply natDegree_pos_iff_degree_pos.mpr
  exact lt_of_le_of_ne (zero_le_degree_iff.mpr hp)
    (fun h => hu (isUnit_iff_degree_eq_zero.mpr h.symm))

private theorem quotientClassNonzeroOfDegreeLt {F : Type u} [Field F]
    {f g : Polynomial F} (hg : g ≠ 0) (hdeg : g.natDegree < f.natDegree) :
    Ideal.Quotient.mk (Ideal.span {f}) g ≠ 0 := by
  intro hzero
  have hdvd := (Ideal.Quotient.eq_zero_iff_dvd f g).mp hzero
  exact (not_le_of_gt hdeg) (Polynomial.natDegree_le_of_dvd hdvd hg)

theorem reducibleQuotientZeroDivisors : ReducibleQuotientZeroDivisors.{u} := by
  intro F _ f hf hirr
  have hf0 : f ≠ 0 := ne_zero_of_natDegree_gt hf
  have hfu : ¬ IsUnit f := by
    intro hunit
    have hd := Polynomial.degree_eq_zero_of_isUnit hunit
    have hpos := natDegree_pos_iff_degree_pos.mp hf
    rw [hd] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨g, h, hgu, hhu, hfac⟩ := (irreducible_or_factor hfu).resolve_left hirr
  have hg0 : g ≠ 0 := left_ne_zero_of_mul (hfac ▸ hf0)
  have hh0 : h ≠ 0 := right_ne_zero_of_mul (hfac ▸ hf0)
  have hgpos := positiveDegreeOfNonunit hg0 hgu
  have hhpos := positiveDegreeOfNonunit hh0 hhu
  have hdeg : f.natDegree = g.natDegree + h.natDegree := by
    rw [hfac, Polynomial.natDegree_mul hg0 hh0]
  have hgl : g.natDegree < f.natDegree := by omega
  have hhl : h.natDegree < f.natDegree := by omega
  refine ⟨g, h, hfac, hgpos, hhpos, hgl, hhl,
    quotientClassNonzeroOfDegreeLt hg0 hgl,
    quotientClassNonzeroOfDegreeLt hh0 hhl, ?_⟩
  rw [← map_mul, ← hfac, Ideal.Quotient.mk_singleton_self]

theorem zeroPolynomialQuotient : ZeroPolynomialQuotient.{u} := by
  intro F _
  have hspan : Ideal.span {(0 : Polynomial F)} = ⊥ := Ideal.span_singleton_zero
  let e : (Polynomial F ⧸ Ideal.span {(0 : Polynomial F)}) ≃+* Polynomial F :=
    (Ideal.quotEquivOfEq hspan).trans (RingEquiv.quotientBot (Polynomial F))
  have he (p : Polynomial F) : e (Ideal.Quotient.mk _ p) = p := rfl
  refine ⟨⟨e, he⟩, e.toMulEquiv.isDomain _, ?_, ?_⟩
  · intro h
    exact Polynomial.not_isField F (e.symm.toMulEquiv.isField h)
  · intro h
    have hu := h.map e.toMonoidHom
    change IsUnit (e (Ideal.Quotient.mk _ X)) at hu
    rw [he] at hu
    exact Polynomial.not_isUnit_X hu

theorem nonzeroConstantQuotient : NonzeroConstantQuotient.{u} := by
  intro F _ a ha
  have hu : IsUnit (C a : Polynomial F) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
  have ht : Ideal.span {(C a : Polynomial F)} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  have hs : Subsingleton (Polynomial F ⧸ Ideal.span {C a}) := by
    rw [ht]
    infer_instance
  let := hs
  exact ⟨hu, hs, not_isField_of_subsingleton _⟩

private theorem realQuadraticDegree : (X ^ 2 + 1 : Polynomial ℝ).natDegree = 2 := by
  compute_degree; norm_num

private theorem realQuadraticIrreducible : Irreducible (X ^ 2 + 1 : Polynomial ℝ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [realQuadraticDegree]
    decide
  · intro x hx
    have hz : x ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using hx
    nlinarith [sq_nonneg x]

theorem realQuadraticExample : RealQuadraticExample := by
  let f : Polynomial ℝ := X ^ 2 + 1
  let Q := Polynomial ℝ ⧸ Ideal.span {f}
  let π : Polynomial ℝ →+* Q := Ideal.Quotient.mk _
  let α : Q := π X
  have hfield : IsField Q :=
    (quotientFieldIffIrreducible ℝ f (by
      change 0 < (X ^ 2 + 1 : Polynomial ℝ).natDegree
      rw [realQuadraticDegree]
      decide)).mpr
      realQuadraticIrreducible
  have hsquare : α ^ 2 = -1 := by
    have hz : α ^ 2 + 1 = 0 := by
      simpa [f, α, π] using quotientRootEquation ℝ f
    exact eq_neg_of_add_eq_zero_left hz
  let : Field Q := hfield.toField
  let ev : Polynomial ℝ →ₐ[ℝ] ℂ := Polynomial.aeval Complex.I
  have hev : ∀ p ∈ Ideal.span {f}, ev p = 0 := by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [ev, f, map_mul, Complex.I_sq]
  let φ : Q →ₐ[ℝ] ℂ := Ideal.Quotient.liftₐ (Ideal.span {f}) ev hev
  have hφ (p : Polynomial ℝ) : φ (π p) = ev p := rfl
  have hα : φ α = Complex.I := by simp [α, hφ, ev]
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨algebraMap ℝ Q z.re + algebraMap ℝ Q z.im * α, ?_⟩
    simpa only [map_add, map_mul, AlgHom.commutes, Complex.coe_algebraMap, hα]
      using z.re_add_im
  let e : Q ≃ₐ[ℝ] ℂ := AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have heα : e α = Complex.I := hα
  have hformula (a b : ℝ) :
      e (algebraMap ℝ Q a + algebraMap ℝ Q b * α) =
        (a : ℂ) + (b : ℂ) * Complex.I := by
    simp only [map_add, map_mul, AlgEquiv.commutes, Complex.coe_algebraMap, heα]
  refine ⟨hfield, hsquare, e, heα, hformula, ?_⟩
  intro x
  refine ⟨((e x).re, (e x).im), ?_, ?_⟩
  · apply e.injective
    rw [hformula]
    exact (e x).re_add_im.symm
  · rintro ⟨a, b⟩ hab
    have hc := congrArg e hab
    rw [hformula] at hc
    apply Prod.ext
    · simpa using congrArg Complex.re hc.symm
    · simpa using congrArg Complex.im hc.symm

end D07.Ch11.IrreducibleQuotient
