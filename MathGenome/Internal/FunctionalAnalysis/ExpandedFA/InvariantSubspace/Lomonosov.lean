import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.InvariantSubspace.Lomonosov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.InvariantSubspace.TransitiveCompactLemma
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactDefectClosedRange
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace ExpandedFA.InvariantSubspace.Lomonosov

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A nonzero fixed vector of a compact operator commuting with T gives
an eigenvector of T, by restriction to the finite-dimensional fixed space. -/
theorem exists_eigenvector_of_compact_fixed_vector
    (T C : X →L[ℂ] X) (hTC : Commute T C)
    (hC : Compactness.IsCompactLinearMap C.toLinearMap)
    (x : X) (hx : x ≠ 0) (hCx : C x = x) :
    ∃ (c : ℂ) (y : X), y ≠ 0 ∧ T y = c • y := by
  let E : Submodule ℂ X := LinearMap.ker (LinearMap.id - C.toLinearMap)
  have hxE : x ∈ E := by
    change x - C x = 0
    rw [hCx, sub_self]
  have hfinite : FiniteDimensional ℂ E :=
    (Fredholm.identity_sub_compact_kernel_closed_finite_dimensional C hC).2
  let : FiniteDimensional ℂ E := hfinite
  have hne : (⟨x, hxE⟩ : E) ≠ 0 := by
    intro h
    exact hx (congrArg Subtype.val h)
  let : Nontrivial E := nontrivial_of_ne _ _ hne
  have hstable : ∀ y ∈ E, T.toLinearMap y ∈ E := by
    intro y hy
    have hCy : C y = y := (sub_eq_zero.mp hy).symm
    have hcomm : T (C y) = C (T y) :=
      congrArg (fun B : X →L[ℂ] X => B y) hTC.eq
    change T y - C (T y) = 0
    rw [← hcomm, hCy, sub_self]
  let R : Module.End ℂ E := T.toLinearMap.restrict hstable
  obtain ⟨c, hc⟩ := R.exists_eigenvalue
  obtain ⟨y, hy⟩ := hc.exists_hasEigenvector
  refine ⟨c, y, ?_, ?_⟩
  · intro hyzero
    exact hy.2 (Subtype.ext hyzero)
  · exact congrArg Subtype.val hy.apply_eq_smul

/-- Lomonosov's theorem, with invariance under the entire commutant. -/
theorem lomonosov : Spec.HyperinvariantSubspace.{u} := by
  intro X _ _ _ T hnonscalar K hcompact hK hTK
  classical
  let 𝒜 : Subalgebra ℂ (X →L[ℂ] X) := Subalgebra.centralizer ℂ {T}
  have mem_commutant (S : X →L[ℂ] X) : S ∈ 𝒜 ↔ Commute T S := by
    simp only [𝒜, Subalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, Commute, SemiconjBy]
  by_contra hnone
  have htrans : TransitiveCompactLemma.Spec.IsTransitive 𝒜 := by
    intro M hclosed hstable
    by_contra h
    have hbot : M ≠ ⊥ := fun hb => h (Or.inl hb)
    have htop : M ≠ ⊤ := fun ht => h (Or.inr ht)
    exact hnone ⟨M, hbot, htop, hclosed,
      fun S hS => hstable S ((mem_commutant S).mpr hS)⟩
  obtain ⟨A, hA, x, hx, hAKx⟩ :=
    TransitiveCompactLemma.transitive_compact X 𝒜 htrans K hcompact hK
  have hTA : Commute T A := (mem_commutant A).mp hA
  have hcomp : Compactness.IsCompactLinearMap (A * K).toLinearMap :=
    (Compactness.compact_iff_isCompactOperator _).mpr
      (((Compactness.compact_iff_isCompactOperator K.toLinearMap).mp hcompact).clm_comp A)
  obtain ⟨c, y, hy, hTy⟩ :=
    exists_eigenvector_of_compact_fixed_vector T (A * K) (hTA.mul_right hTK)
      hcomp x hx hAKx
  let M : Submodule ℂ X := (T - c • ContinuousLinearMap.id ℂ X).toLinearMap.ker
  have hclosed : IsClosed (M : Set X) :=
    (T - c • ContinuousLinearMap.id ℂ X).isClosed_ker
  have hyM : y ∈ M := by
    change T y - c • y = 0
    exact sub_eq_zero.mpr hTy
  have hstable : ∀ S ∈ 𝒜, ∀ z ∈ M, S z ∈ M := by
    intro S hS z hz
    have hTz : T z = c • z := sub_eq_zero.mp hz
    have hcomm : T (S z) = S (T z) :=
      congrArg (fun B : X →L[ℂ] X => B z) ((mem_commutant S).mp hS).eq
    change T (S z) - c • S z = 0
    rw [hcomm, hTz, map_smul, sub_self]
  rcases htrans M hclosed hstable with hbot | htop
  · exact hy (by simpa [hbot] using hyM)
  · apply hnonscalar c
    ext z
    have hz : z ∈ M := by rw [htop]; trivial
    exact sub_eq_zero.mp hz

/-- The hyperinvariant subspace is in particular invariant under T. -/
theorem lomonosov_invariant : Spec.InvariantSubspaceConsequence.{u} := by
  intro X _ _ _ T hT K hc hK hTK
  obtain ⟨M, hbot, htop, hclosed, hinv⟩ := lomonosov X T hT K hc hK hTK
  exact ⟨M, hbot, htop, hclosed, hinv T (Commute.refl T)⟩

end ExpandedFA.InvariantSubspace.Lomonosov
