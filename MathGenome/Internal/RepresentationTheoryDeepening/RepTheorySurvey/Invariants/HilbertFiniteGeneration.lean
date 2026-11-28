import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.HomogeneousGenerators
import Mathlib.RingTheory.FiniteType

open LinearAlgebraicGroups

universe u v w

namespace RepTheorySurvey.Invariants

/-- The ideal of positive-degree homogeneous elements of `B` has a finite generating
family drawn from those elements. -/
private theorem exists_homogeneous_ideal_generators
    {k : Type u} {A : Type w} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (𝒜 : ℕ → Submodule k A) (B : Subalgebra k A) :
    ∃ (m : ℕ) (f : Fin m → B) (d : Fin m → ℕ),
      (∀ i, 0 < d i) ∧ (∀ i, (f i : A) ∈ 𝒜 (d i)) ∧
        Ideal.span (Set.range fun i ↦ (f i : A)) =
          Ideal.span (positiveHomogeneousInvariants 𝒜 B) := by
  let := Algebra.FiniteType.isNoetherianRing k A
  let S := positiveHomogeneousInvariants 𝒜 B
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (IsNoetherian.noetherian (Ideal.span S))
  obtain ⟨m, e, he⟩ := s.finite_toSet.fin_embedding
  have hmem (i : Fin m) : e i ∈ S := hs (he ▸ Set.mem_range_self i)
  let f (i : Fin m) : B := ⟨e i, (hmem i).1⟩
  choose d hpos hdegree using fun i ↦ (hmem i).2
  refine ⟨m, f, d, hpos, hdegree, ?_⟩
  change Ideal.span (Set.range e) = Ideal.span S
  rw [he]
  exact hspan.symm

/-- A grading-preserving group action with a degree-preserving Reynolds operator
has finitely many homogeneous algebra generators for its fixed subalgebra. -/
theorem GroupAlgebraAction.hilbert_finite_generation
    {k : Type u} {G : Type v} {A : Type w}
    [Field k] [Group G] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : GroupAlgebraAction k G A)
    (R : A →ₗ[k] ρ.fixedSubalgebra)
    (hzero : 𝒜 0 = (⊥ : Subalgebra k A).toSubmodule)
    (hgraded : ∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n)
    (hReynolds : ρ.IsReynolds R)
    (hR : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) :
    ∃ (m : ℕ) (f : Fin m → ρ.fixedSubalgebra) (d : Fin m → ℕ),
      (∀ i, 0 < d i) ∧ (∀ i, (f i : A) ∈ 𝒜 (d i)) ∧
        Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = ρ.fixedSubalgebra := by
  obtain ⟨m, f, d, hpos, hdegree, hspan⟩ :=
    exists_homogeneous_ideal_generators 𝒜 ρ.fixedSubalgebra
  exact ⟨m, f, d, hpos, hdegree,
    adjoin_homogeneous_eq_fixedSubalgebra 𝒜 ρ R f d hzero hgraded hReynolds hR hpos hdegree hspan⟩

/-- A grading-preserving rational action with a degree-preserving Reynolds operator
has finitely many homogeneous algebra generators for its fixed subalgebra. -/
theorem RationalAlgebraAction.hilbert_finite_generation
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {H : HopfAlgebraCategory k}
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] ρ.fixedSubalgebra)
    (hzero : 𝒜 0 = (⊥ : Subalgebra k A).toSubmodule)
    (hgraded : ∀ n, ρ.toRightComodule.IsSubcomodule (𝒜 n))
    (hReynolds : ρ.IsReynolds R)
    (hR : ∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) :
    ∃ (m : ℕ) (f : Fin m → ρ.fixedSubalgebra) (d : Fin m → ℕ),
      (∀ i, 0 < d i) ∧ (∀ i, (f i : A) ∈ 𝒜 (d i)) ∧
        Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = ρ.fixedSubalgebra := by
  obtain ⟨m, f, d, hpos, hdegree, hspan⟩ :=
    exists_homogeneous_ideal_generators 𝒜 ρ.fixedSubalgebra
  exact ⟨m, f, d, hpos, hdegree,
    adjoin_homogeneous_eq_fixedSubalgebra 𝒜 ρ R f d hzero hgraded hReynolds hR hpos hdegree hspan⟩

end RepTheorySurvey.Invariants
