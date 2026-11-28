import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerrePresentation

/-! The generators, relations, and universal property of the type A₂ Serre algebra. -/

namespace LieNotes.Quantum.SerrePresentation

universe u v w

abbrev serrePolynomial := @Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial
abbrev relationXY := @Specs.LieNotes.Quantum.SerrePresentation.relationXY
abbrev relationYX := @Specs.LieNotes.Quantum.SerrePresentation.relationYX
abbrev serreIdeal := @Specs.LieNotes.Quantum.SerrePresentation.serreIdeal
abbrev SerreAlgebra := Specs.LieNotes.Quantum.SerrePresentation.SerreAlgebra
abbrev quotientMap := @Specs.LieNotes.Quantum.SerrePresentation.quotientMap
abbrev generator := @Specs.LieNotes.Quantum.SerrePresentation.generator
abbrev x := @Specs.LieNotes.Quantum.SerrePresentation.x
abbrev y := @Specs.LieNotes.Quantum.SerrePresentation.y
abbrev z := @Specs.LieNotes.Quantum.SerrePresentation.z
abbrev lift := @Specs.LieNotes.Quantum.SerrePresentation.lift

variable {A : Type u} [CommRing A]
variable {B : Type v} [Ring B] [Algebra A B]

theorem relationXY_mem (q : Aˣ) : relationXY q ∈ serreIdeal q :=
  TwoSidedIdeal.subset_span (Set.mem_insert _ _)

theorem relationYX_mem (q : Aˣ) : relationYX q ∈ serreIdeal q :=
  TwoSidedIdeal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

@[simp]
theorem map_serrePolynomial {C : Type w} [Ring C] [Algebra A C]
    (f : B →ₐ[A] C) (q : Aˣ) (a b : B) :
    f (serrePolynomial q a b) = serrePolynomial q (f a) (f b) := by
  simp only [Specs.LieNotes.Quantum.SerrePresentation.serrePolynomial,
    map_add, map_sub, map_mul, map_pow, map_smul]

@[simp]
theorem relationXY_zero (q : Aˣ) : serrePolynomial q (x q) (y q) = 0 := by
  change serrePolynomial q (quotientMap q (FreeAlgebra.ι A 0))
    (quotientMap q (FreeAlgebra.ι A 1)) = 0
  rw [← map_serrePolynomial (quotientMap q) q (FreeAlgebra.ι A 0) (FreeAlgebra.ι A 1)]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr (relationXY_mem q))

@[simp]
theorem relationYX_zero (q : Aˣ) : serrePolynomial q (y q) (x q) = 0 := by
  change serrePolynomial q (quotientMap q (FreeAlgebra.ι A 1))
    (quotientMap q (FreeAlgebra.ι A 0)) = 0
  rw [← map_serrePolynomial (quotientMap q) q (FreeAlgebra.ι A 1) (FreeAlgebra.ι A 0)]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr (relationYX_mem q))

@[simp]
theorem lift_comp_quotientMap (q : Aˣ) (f : Fin 2 → B)
    (hxy : serrePolynomial q (f 0) (f 1) = 0)
    (hyx : serrePolynomial q (f 1) (f 0) = 0) :
    (lift q f hxy hyx).comp (quotientMap q) = FreeAlgebra.lift A f := by
  unfold lift quotientMap Specs.LieNotes.Quantum.SerrePresentation.lift
    Specs.LieNotes.Quantum.SerrePresentation.quotientMap
  apply Ideal.Quotient.liftₐ_comp

@[simp]
theorem lift_generator (q : Aˣ) (f : Fin 2 → B)
    (hxy : serrePolynomial q (f 0) (f 1) = 0)
    (hyx : serrePolynomial q (f 1) (f 0) = 0) (i : Fin 2) :
    lift q f hxy hyx (generator q i) = f i := by
  change ((lift q f hxy hyx).comp (quotientMap q)) (FreeAlgebra.ι A i) = f i
  rw [lift_comp_quotientMap, FreeAlgebra.lift_ι_apply]

/-- Two morphisms from the Serre algebra agree if they agree on the two generators. -/
theorem hom_ext {q : Aˣ} {F G : SerreAlgebra A q →ₐ[A] B}
    (h : ∀ i, F (generator q i) = G (generator q i)) : F = G := by
  apply Ideal.Quotient.algHom_ext A
  exact FreeAlgebra.hom_ext (funext h)

/-- An assignment to the two generators extends uniquely exactly when it satisfies
both Serre relations. -/
theorem universalProperty (q : Aˣ) (f : Fin 2 → B) :
    (∃! F : SerreAlgebra A q →ₐ[A] B, ∀ i, F (generator q i) = f i) ↔
      serrePolynomial q (f 0) (f 1) = 0 ∧ serrePolynomial q (f 1) (f 0) = 0 := by
  constructor
  · rintro ⟨F, hF, _⟩
    have hx : F (x q) = f 0 := hF 0
    have hy : F (y q) = f 1 := hF 1
    constructor
    · rw [← hx, ← hy, ← map_serrePolynomial, relationXY_zero, map_zero]
    · rw [← hx, ← hy, ← map_serrePolynomial, relationYX_zero, map_zero]
  · rintro ⟨hxy, hyx⟩
    refine ⟨lift q f hxy hyx, lift_generator q f hxy hyx, ?_⟩
    intro G hG
    exact hom_ext (fun i => (hG i).trans (lift_generator q f hxy hyx i).symm)

end LieNotes.Quantum.SerrePresentation
