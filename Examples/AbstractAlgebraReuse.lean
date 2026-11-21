import MathGenome

/-! Downstream compositions using the combined D05+D07 interfaces. -/
noncomputable section
open scoped TensorProduct

namespace MathGenome.AbstractAlgebraExamples

theorem field_embedding_separates {F R : Type*} [Field F] [Ring R] [Nontrivial R]
    (f : F →+* R) (x y : F) (h : f x = f y) : x = y :=
  D07.Ch08.FieldEmbedding.unital_injective F R f h

theorem eisenstein_prime_cube (p : ℕ) (hp : p.Prime) :
    Irreducible ((Polynomial.X : Polynomial ℚ) ^ 3 - Polynomial.C (p : ℚ)) := by
  simpa using (D07.Ch11.Eisenstein.xPowSubPrime p 3 hp (by decide)).2

theorem group_quotient_composes {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) :
    ∃ e : G ⧸ f.ker ≃* f.range,
      ((e (QuotientGroup.mk' f.ker a) : H) * (e (QuotientGroup.mk' f.ker b) : H)) = f (a * b) := by
  obtain ⟨e, he⟩ := D07.Ch04.FirstIsomorphism.first_isomorphism G H f
  exact ⟨e, by rw [he a, he b, map_mul]⟩

/-- A map packaged by the arbitrary-ring D07 API can be used by D05 rank-nullity. -/
theorem rank_nullity_of_d07_linear_map {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (f : V → W)
    (ha : ∀ x y, f (x + y) = f x + f y)
    (hs : ∀ (a : K) (x : V), f (a • x) = a • f x) :
    ∃ T : V →ₗ[K] W, (T : V → W) = f ∧
      Module.finrank K V = Module.finrank K T.ker + Module.finrank K T.range := by
  obtain ⟨T, hT⟩ := (D07.Ch16.MapsSubmodules.linearMapCharacterization K V W f).mp ⟨ha, hs⟩
  exact ⟨T, hT, D05.M03.RankNullity.rank_nullity T⟩

/-- The D07 elementary-tensor relation span agrees with D05's map-image convention. -/
theorem tensor_quotient_conventions_agree {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (U : Submodule K V) (S : Submodule K W) :
    Specs.D07.Ch22.TensorQuotients.relations U S =
      Specs.D05.M15.TensorQuotient.tensorRelations U S := by
  exact D07.Ch22.TensorQuotients.relationsImages K V W U S

/-- The release discloses Mathlib's Liouville proof as this FTA's actual source. -/
theorem fta_nonconstant_has_root (f : Polynomial ℂ) (h : ∀ c : ℂ, f ≠ Polynomial.C c) :
    ∃ z : ℂ, Polynomial.IsRoot f z :=
  D07.Appendix.AlgebraicFta.nonconstant_root_exists f h

end MathGenome.AbstractAlgebraExamples
