import Mathlib.Algebra.Homology.HomologySequence

/-!
HA-G07, notes/002/advanced-homological-algebra.tex, lines 2343–2394.
We use arbitrary integer-indexed cochain complexes in an abelian category.
`opcycles p` is the cokernel of the incoming differential, hence K^p/B^p K.
The boundaries are represented by the kernel of the quotient projection
K^p → K^p/B^p K. This is canonically the image of the incoming differential;
`boundaryImageComparisonType` below records this identification, including its
compatibility with the inclusion into K^p.
No boundedness, injective objects, or resolutions are assumed.
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u

namespace Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness

variable {A : Type u} [Category.{v} A] [Abelian A]

noncomputable abbrev boundaries (K : CochainComplex A ℤ) (p : ℤ) :=
  kernel (K.pOpcycles p)

noncomputable abbrev boundariesMap {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ) :
    boundaries K p ⟶ boundaries L p :=
  kernel.map (K.pOpcycles p) (L.pOpcycles p) (f.f p) (opcyclesMap f p)
    (p_opcyclesMap f p)

noncomputable def boundarySequence (S : ShortComplex (CochainComplex A ℤ)) (p : ℤ) :
    ShortComplex A :=
  ShortComplex.mk (boundariesMap S.f p) (boundariesMap S.g p) (by
    apply (cancel_mono (kernel.ι (S.X₃.pOpcycles p))).1
    simp only [Category.assoc, boundariesMap, kernel.lift_ι, kernel.lift_ι_assoc]
    simp only [← comp_f, S.zero, zero_f, comp_zero, zero_comp])

/-- The representation of boundaries agrees, over K^p, with im(d^(p-1)). -/
def boundaryImageComparisonType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ) (p : ℤ),
    ∃ e : boundaries K p ≅ Abelian.image (K.d (p - 1) p),
      e.hom ≫ Abelian.image.ι (K.d (p - 1) p) = kernel.ι (K.pOpcycles p)

/-- All four invariant sequences of any admissible short exact sequence. -/
def shortExactInvariantsType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (S : ShortComplex (CochainComplex A ℤ)), S.ShortExact →
    (∀ p, Mono (opcyclesMap S.f p)) → ∀ p,
    (boundarySequence S p).ShortExact ∧
    (S.map (cyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact ∧
    (S.map (homologyFunctor A (ComplexShape.up ℤ) p)).ShortExact ∧
    (S.map (opcyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact

/-- The original statement with W = coker(i) and precisely the two injection tests. -/
def horizontalInvariantExactnessType :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (U V : CochainComplex A ℤ) (i : U ⟶ V),
    (∀ p, Mono (i.f p)) → (∀ p, Mono (opcyclesMap i p)) →
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    S.ShortExact ∧ ∀ p,
      (boundarySequence S p).ShortExact ∧
      (S.map (cyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact ∧
      (S.map (homologyFunctor A (ComplexShape.up ℤ) p)).ShortExact ∧
      (S.map (opcyclesFunctor A (ComplexShape.up ℤ) p)).ShortExact

end Specs.AdvancedHomologicalAlgebra.HorizontalInvariantExactness
