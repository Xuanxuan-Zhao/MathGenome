import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FiniteLength

/-! Jordan–Hölder and natural-number length, paper.tex 536–565.
All results allow arbitrary unital rings, zero modules and the zero ring.
Right modules are covered by replacing the scalar ring with its opposite.
-/

universe u v

namespace P103.Ch02.FiniteLength

theorem composition_series_iff (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] :
    (∃ s : CompositionSeries (Submodule R M), s.head = ⊥ ∧ s.last = ⊤) ↔
      IsNoetherian R M ∧ IsArtinian R M :=
  isFiniteLength_iff_exists_compositionSeries.symm.trans
    isFiniteLength_iff_isNoetherian_isArtinian

theorem composition_factor_simple (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (CompositionFactor R M s i) := by
  exact (covBy_iff_quot_is_simple (s.lt_succ i).le).mp (s.step i)

theorem composition_factor_nonzero (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nontrivial (CompositionFactor R M s i) := by
  have := composition_factor_simple R M s i
  exact IsSimpleModule.nontrivial R _

theorem module_class_eq_iff (R : Type u) [Ring R] (X Y : ModuleCat.{v} R) :
    Quotient.mk (moduleIsomorphismSetoid R) X =
      Quotient.mk (moduleIsomorphismSetoid R) Y ↔ Nonempty (X ≃ₗ[R] Y) :=
  Quotient.eq

/-- A permutation of factors equipped with actual module isomorphisms. -/
theorem jordan_holder_isomorphisms (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s t : CompositionSeries (Submodule R M))
    (hs₀ : s.head = ⊥) (hs₁ : s.last = ⊤)
    (ht₀ : t.head = ⊥) (ht₁ : t.last = ⊤) :
    ∃ e : Fin s.length ≃ Fin t.length, ∀ i,
      Nonempty (CompositionFactor R M s i ≃ₗ[R] CompositionFactor R M t (e i)) := by
  obtain ⟨e, he⟩ := s.jordan_holder t (hs₀.trans ht₀.symm) (hs₁.trans ht₁.symm)
  exact ⟨e, fun i => ⟨(he i).linearEquiv⟩⟩

/-- Equality of multisets of simple-module isomorphism classes, with multiplicity. -/
theorem compositionFactors_eq (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s t : CompositionSeries (Submodule R M))
    (hs₀ : s.head = ⊥) (hs₁ : s.last = ⊤)
    (ht₀ : t.head = ⊥) (ht₁ : t.last = ⊤) :
    compositionFactors R M s = compositionFactors R M t := by
  obtain ⟨e, he⟩ := jordan_holder_isomorphisms R M s t hs₀ hs₁ ht₀ ht₁
  unfold compositionFactors
  apply Fintype.sum_equiv e
  intro i
  have h := (module_class_eq_iff R
    (ModuleCat.of R (CompositionFactor R M s i))
    (ModuleCat.of R (CompositionFactor R M t (e i)))).mpr (he i)
  rw [h]

/-- The module's length, defined independently of the choice of composition series. -/
noncomputable def length (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : ℕ :=
  P103.Specs.Ch02.FiniteLength.lengthValue R M

theorem length_eq_series (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
    (s : CompositionSeries (Submodule R M)) (hs₀ : s.head = ⊥) (hs₁ : s.last = ⊤) :
    length R M = s.length := by
  unfold length P103.Specs.Ch02.FiniteLength.lengthValue
  rw [← Module.length_compositionSeries s hs₀ hs₁]
  exact ENat.toNat_natCast s.length

theorem length_add_short_exact (R A B C : Type*) [Ring R]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g)
    (hA : IsFiniteLength R A) (_hB : IsFiniteLength R B) (hC : IsFiniteLength R C) :
    length R B = length R A + length R C := by
  unfold length P103.Specs.Ch02.FiniteLength.lengthValue
  rw [Module.length_eq_add_of_exact f g hf hg he]
  exact ENat.toNat_add (Module.length_ne_top_iff.mpr hA) (Module.length_ne_top_iff.mpr hC)

theorem length_zero (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] [Subsingleton M] :
    length R M = 0 := by
  simp [length, P103.Specs.Ch02.FiniteLength.lengthValue]

end P103.Ch02.FiniteLength
