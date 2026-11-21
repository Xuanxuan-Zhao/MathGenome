import MathGenome.Internal.Specs.D07.Ch14.GaloisClosure
import MathGenome.Internal.D07.Ch12.DegreeDefinition
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure

/-!
The finite Galois closure, K07.14.galois_closure.
We use the normal closure formed from images of base-preserving embeddings.
Its finite-dimensionality follows from finiteness of the set of embeddings
of a finite extension; separability is inherited from the conjugate images.
Normality forces every normal overfield containing E to contain those images.
For any generating list, mapping its adjoin under the ambient embeddings gives
one inclusion in the conjugate-root adjoin; splitting in the normal closure
gives the other. Thus the resulting embedded field is independent of the list.
-/

universe u v

namespace D07.Ch14.GaloisClosure

open IntermediateField Polynomial Specs.D07.Ch14.GaloisClosure

private theorem normalClosure_minimal
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E M : IntermediateField K Ω)
    (hM : Normal K M) (hEM : E ≤ M) : normalClosure K E Ω ≤ M := by
  let := hM
  exact (normalClosure_le_iff_of_normal).mpr hEM

/-- Without separability the same construction is finite and normal. -/
theorem finiteNormalClosure : FiniteNormalClosure.{u, v} := by
  intro K Ω _ _ _ _ E hfinite
  let : FiniteDimensional K E :=
    (Ch12.DegreeDefinition.finite_iff_finiteDimensional K E).mp hfinite
  refine ⟨normalClosure K E Ω, ⟨le_normalClosure E, ?_, inferInstance,
    normalClosure_minimal K Ω E⟩, ?_⟩
  · exact (Ch12.DegreeDefinition.finite_iff_finiteDimensional K _).mpr inferInstance
  · intro M hM
    exact le_antisymm
      (hM.2.2.2 _ inferInstance (le_normalClosure E))
      (normalClosure_minimal K Ω E M hM.2.2.1 hM.1)

/-- Separability of E makes its finite normal closure Galois. -/
theorem finiteGaloisClosure : FiniteGaloisClosure.{u, v} := by
  intro K Ω _ _ _ _ E hfinite hsep
  let : FiniteDimensional K E :=
    (Ch12.DegreeDefinition.finite_iff_finiteDimensional K E).mp hfinite
  let : Algebra.IsSeparable K E := hsep
  refine ⟨normalClosure K E Ω, ⟨le_normalClosure E, ?_, inferInstance,
    inferInstance, (show Algebra.IsSeparable K (normalClosure K E Ω) from inferInstance),
    normalClosure_minimal K Ω E⟩, ?_⟩
  · exact (Ch12.DegreeDefinition.finite_iff_finiteDimensional K _).mpr inferInstance
  · intro M hM
    exact le_antisymm
      (hM.2.2.2.2.2 _ inferInstance (le_normalClosure E))
      (normalClosure_minimal K Ω E M hM.2.2.2.1 hM.1)

private theorem normalClosure_eq_adjoin_conjugates
    (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (E : IntermediateField K Ω)
    (r : ℕ) (a : Fin r → Ω) (hgen : adjoin K (Set.range a) = E) :
    normalClosure K E Ω = adjoin K {y : Ω | ∃ i, y ∈ (minpoly K (a i)).rootSet Ω} := by
  have hmem (i : Fin r) : a i ∈ E := hgen ▸ subset_adjoin K _ ⟨i, rfl⟩
  apply le_antisymm
  · rw [normalClosure_def' E]
    apply iSup_le
    intro f
    rw [← hgen, adjoin_map]
    apply adjoin_le_iff.mpr
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    apply subset_adjoin
    refine ⟨i, mem_rootSet.mpr ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral (a i)), ?_⟩⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  · apply adjoin_le_iff.mpr
    rintro y ⟨i, hy⟩
    let C := normalClosure K E Ω
    have hia : a i ∈ C := le_normalClosure E (hmem i)
    have hs := (inferInstance : Normal K C).splits (⟨a i, hia⟩ : C)
    have heq : minpoly K (⟨a i, hia⟩ : C) = minpoly K (a i) := by
      exact (minpoly.algHom_eq C.val C.val.injective _).symm
    rw [heq] at hs
    rw [← hs.image_rootSet C.val] at hy
    obtain ⟨z, _, rfl⟩ := hy
    exact z.2

/-- Minimality identifies any embedded normal closure with the conjugate-root
adjoin of every finite generating list, including the empty list. -/
theorem generatedByConjugates : GeneratedByConjugates.{u, v} := by
  intro K Ω _ _ _ _ E N _hfinite hEN hN hmin r a hgen
  have hNC : N = normalClosure K E Ω := le_antisymm
    (hmin _ inferInstance (le_normalClosure E))
    (normalClosure_minimal K Ω E N hN hEN)
  exact hNC.trans (normalClosure_eq_adjoin_conjugates K Ω E r a hgen)

/-- An inseparable extension cannot be contained in a separable one. -/
theorem inseparableObstruction : InseparableObstruction.{u, v} := by
  intro K Ω _ _ _ E M hEM hE hM
  let : Algebra.IsSeparable K M := hM
  exact hE (Algebra.IsSeparable.of_algHom K M (inclusion hEM))

/-- In particular no inseparable element can belong to a separable extension. -/
theorem inseparableElementObstruction : InseparableElementObstruction.{u, v} := by
  intro K Ω _ _ _ x M hx hmem hM
  have hm : IsSeparable K (⟨x, hmem⟩ : M) := hM.isSeparable' _
  exact hx ((isSeparable_map_iff (F := K) (x := (⟨x, hmem⟩ : M))
    M.val M.val.injective).mpr hm)

end D07.Ch14.GaloisClosure
