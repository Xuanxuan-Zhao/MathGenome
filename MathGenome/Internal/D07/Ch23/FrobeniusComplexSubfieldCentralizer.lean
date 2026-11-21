import MathGenome.Internal.Specs.D07.Ch23.FrobeniusComplexSubfieldCentralizer
import MathGenome.Internal.D07.Ch23.AlgebraicallyClosedCenter
import MathGenome.Internal.D07.Ch23.Centralizers
import Mathlib.Analysis.Complex.Polynomial.Basic

universe u

namespace D07.Ch23.FrobeniusComplexSubfieldCentralizer

open Specs.D07.Ch23.FrobeniusComplexSubfieldCentralizer

/-- The irreducible real polynomial degree bound applies in a noncommutative
ambient division ring because the coefficients are central. -/
theorem realMinimalPolynomialDegree : RealMinimalPolynomialDegree.{u} := by
  intro D _ _ h x
  have hx := (h x).isIntegral
  exact ⟨minpoly.monic hx, minpoly.irreducible hx, minpoly.aeval ℝ x,
    (minpoly.irreducible hx).natDegree_le_two⟩

/-- Apply the real/complex classification only to the commutative finite
simple subfield ℝ[x], never to the ambient division ring. -/
theorem complexEmbeddingExists : ComplexEmbeddingExists.{u} := by
  intro D _ _ h hn
  obtain ⟨x, hx⟩ := hn
  let A := Algebra.adjoin ℝ ({x} : Set D)
  let : Module.Finite ℝ A :=
    (AlgebraicallyClosedCenter.simpleAdjoinFiniteField ℝ D x (h x)).2.1
  let := fieldOfFiniteDimensional ℝ A
  let : Algebra.IsAlgebraic ℝ A := ⟨fun a =>
    Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (h a.val)⟩
  obtain hR | hC := Real.nonempty_algEquiv_or A
  · obtain ⟨e⟩ := hR
    exfalso
    apply hx
    let a : A := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
    refine ⟨e a, ?_⟩
    have ha : algebraMap ℝ A (e a) = a := by
      apply e.injective
      simp only [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    exact congrArg (fun b : A => (b : D)) ha
  · obtain ⟨e⟩ := hC
    let φ : ℂ →ₐ[ℝ] D := A.val.comp e.symm.toAlgHom
    refine ⟨φ Complex.I, φ, ?_, rfl, φ.injective⟩
    rw [← map_pow, Complex.I_sq, map_neg, map_one]

/-- Real and imaginary coordinates propagate the one commuting relation to
all elements of the complex image. -/
lemma commute_complex_image {D : Type u} [DivisionRing D] [Algebra ℝ D]
    (φ : ℂ →ₐ[ℝ] D) (y : D)
    (hy : y * φ Complex.I = φ Complex.I * y) (z : ℂ) :
    y * φ z = φ z * y := by
  rw [← Complex.re_add_im z]
  simp only [map_add, map_mul, AlgHom.map_coe_real_complex]
  have hr : Commute y (algebraMap ℝ D z.re) := (Algebra.commutes z.re y).symm
  have hi : Commute y (algebraMap ℝ D z.im) := (Algebra.commutes z.im y).symm
  exact (hr.add_right (hi.mul_right (show Commute y (φ Complex.I) from hy))).eq

/-- Scalar closedness is applied only after restricting to the division
subring centralizing the chosen imaginary unit. -/
theorem complexCentralizerImage : ComplexCentralizerImage.{u} := by
  intro D _ _ h φ y
  constructor
  · intro hy
    obtain ⟨E, hE⟩ := Centralizers.centralizerDivisionSubring D (φ Complex.I)
    have memE (a : D) : a ∈ E ↔ a * φ Complex.I = φ Complex.I * a := by
      change a ∈ E.toSubring ↔ _
      rw [hE]
      exact Set.ext_iff.mp (Centralizers.centralizerCarrier D (φ Complex.I)) a
    let g : ℂ →+* E :=
      { φ.toRingHom with
        toFun := fun z => ⟨φ z, (memE _).mpr (by rw [← map_mul, mul_comm, map_mul])⟩
        map_one' := Subtype.ext (map_one φ)
        map_mul' := fun a b => Subtype.ext (map_mul φ a b)
        map_zero' := Subtype.ext (map_zero φ)
        map_add' := fun a b => Subtype.ext (map_add φ a b) }
    have hg (z : ℂ) (a : E) : g z * a = a * g z := by
      apply Subtype.ext
      exact (commute_complex_image φ a.val ((memE _).mp a.property) z).symm
    let : Algebra ℂ E := g.toAlgebra' hg
    let : Algebra ℝ E := Algebra.complexToReal
    let v : E →ₐ[ℝ] D :=
      { E.subtype with
        commutes' := fun r => by change φ (algebraMap ℝ ℂ r) = _; exact φ.commutes r }
    have halg (a : E) : IsAlgebraic ℂ a := by
      have ha : IsAlgebraic ℝ a := (isAlgebraic_algHom_iff v Subtype.val_injective).mp (h a.val)
      exact ha.tower_top ℂ
    obtain ⟨z, hz⟩ :=
      (AlgebraicallyClosedCenter.scalarMapBijective ℂ E halg).2 ⟨y, (memE _).mpr hy⟩
    exact ⟨z, congrArg (fun a : E => (a : D)) hz⟩
  · rintro ⟨z, rfl⟩
    rw [← map_mul, mul_comm, map_mul]

end D07.Ch23.FrobeniusComplexSubfieldCentralizer
