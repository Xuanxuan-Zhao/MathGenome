import MathGenome.Internal.Specs.D05.M10.Triangularization
import MathGenome.Internal.D05.M08.CayleyHamilton
import MathGenome.Internal.D05.M08.EigenRoots
import MathGenome.Internal.D05.M08.RestrictionMinpoly
import MathGenome.Internal.D05.M06.QuotientDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! The triangularization criterion over the named field, including dimension zero.
The converse uses dimension induction, an invariant eigenline, and a lifted
quotient basis. The lift is the actual `Basis.sumQuot` construction. -/
noncomputable section
namespace D05.M10.Triangularization
open Module Polynomial
open Specs.D05.M10.Triangularization

/-- Joining triangular bases of an invariant subspace and its quotient gives
an upper triangular basis of the original space. -/
theorem upper_triangular_sumQuot {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (T : Module.End K V) (U : Submodule K V)
    (hU : ∀ x ∈ U, T x ∈ U) {m n : ℕ}
    (bU : Basis (Fin m) K U) (bQ : Basis (Fin n) K (V ⧸ U))
    (hleft : (LinearMap.toMatrix bU bU (T.restrict hU)).IsUpperTriangular)
    (hright : (LinearMap.toMatrix bQ bQ (U.mapQ U T hU)).IsUpperTriangular) :
    (LinearMap.toMatrix ((bU.sumQuot bQ).reindex finSumFinEquiv)
      ((bU.sumQuot bQ).reindex finSumFinEquiv) T).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [LinearMap.toMatrix_apply, Basis.repr_reindex_apply,
    Basis.reindex_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd] at hij
      rw [Basis.sumQuot_inl]
      change (bU.sumQuot bQ).repr ((T.restrict hU) (bU j) : V) (Sum.inl i) = 0
      rw [Basis.sumQuot_repr_inl]
      simpa only [LinearMap.toMatrix_apply] using hleft (i := i) (j := j) hij
    | inr j =>
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hij
      have hi := i.isLt
      have hj := j.isLt
      simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij
      omega
  | inr i =>
    cases j with
    | inl j =>
      rw [Basis.sumQuot_inl]
      exact Basis.sumQuot_repr_inr_of_mem bU bQ _ (hU _ (bU j).property) i
    | inr j =>
      simp only [finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd, Nat.add_lt_add_iff_left] at hij
      rw [Basis.sumQuot_repr_inr]
      have heq : U.mkQ (T (bU.sumQuot bQ (Sum.inr j))) =
          U.mapQ U T hU (bQ j) := by
        rw [← Basis.sumQuot_inr bU bQ j]
        rfl
      rw [heq]
      simpa only [LinearMap.toMatrix_apply] using hright (i := i) (j := j) hij

theorem triangular_implies_charpoly_splits :
    Specs.D05.M10.Triangularization.triangular_implies_charpoly_splits := by
  intro K V _ _ _ _ T ⟨n, b, hb⟩
  change T.charpoly.Splits
  rw [← LinearMap.charpoly_toMatrix T b,
    Matrix.charpoly_of_isUpperTriangular _ hb]
  exact Polynomial.Splits.prod (fun i _ => Polynomial.Splits.X_sub_C _)

theorem charpoly_splits_implies_minpoly_splits :
    Specs.D05.M10.Triangularization.charpoly_splits_implies_minpoly_splits := by
  intro K V _ _ _ _ T h
  exact h.of_dvd (D05.M08.Charpoly.monic T).ne_zero
    (D05.M08.CayleyHamilton.minpoly_divides_charpoly T)

/-- A split minimal polynomial supplies an eigenline; induction triangularizes
its quotient, and `upper_triangular_sumQuot` lifts the result. -/
theorem minpoly_splits_implies_triangular :
    Specs.D05.M10.Triangularization.minpoly_splits_implies_triangular := by
  intro K V _ _ _ _ T
  change (minpoly K T).Splits → HasUpperTriangularBasis T
  suffices ∀ n, Module.finrank K V = n →
      (minpoly K T).Splits → HasUpperTriangularBasis T by
    exact this _ rfl
  intro n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    intro hdim hs
    by_cases hn : n = 0
    · refine ⟨Module.finrank K V, Module.finBasis K V, ?_⟩
      intro i j hij
      have hi := i.isLt
      omega
    · have hpos : 0 < Module.finrank K V := by omega
      have hdeg : (minpoly K T).degree ≠ 0 :=
        Polynomial.degree_ne_of_natDegree_ne
          (Nat.ne_of_gt (D05.M08.Minpoly.positive_degree T hpos))
      obtain ⟨μ, hμ⟩ := hs.exists_eval_eq_zero hdeg
      have hker := (D05.M08.EigenRoots.kernel_iff_minpoly_root T μ).mpr hμ
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
      have heig : T v = μ • v := by
        have hz : (T - μ • (LinearMap.id : Module.End K V)) v = 0 := hv
        simpa only [LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, sub_eq_zero] using hz
      let L : Submodule K V := K ∙ v
      have hscalar (x : V) (hx : x ∈ L) : T x = μ • x := by
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [map_smul, heig, smul_comm]
      have hL : ∀ x ∈ L, T x ∈ L := by
        intro x hx
        rw [hscalar x hx]
        exact L.smul_mem μ hx
      let Q := D05.M06.Invariant.inducedMap K V L T hL
      have hsplitQ : (minpoly K Q).Splits :=
        hs.of_dvd (D05.M08.Minpoly.ne_zero T)
          (D05.M08.RestrictionMinpoly.quotient_minpoly_dvd L T hL)
      have hdimL : Module.finrank K L = 1 := finrank_span_singleton hv0
      have hdimQ : Module.finrank K (V ⧸ L) < n := by
        have hd := D05.M06.QuotientDimension.quotient_dimension L
        omega
      obtain ⟨r, bQ, hbQ⟩ := ih (Module.finrank K (V ⧸ L)) hdimQ Q rfl hsplitQ
      let bL := Module.finBasis K L
      have hbL : (LinearMap.toMatrix bL bL (T.restrict hL)).IsUpperTriangular := by
        intro i j hij
        change j < i at hij
        rw [LinearMap.toMatrix_apply]
        have hmap : T.restrict hL (bL j) = μ • bL j :=
          Subtype.ext (hscalar _ (bL j).property)
        rw [hmap, map_smul, Finsupp.smul_apply, bL.repr_self]
        simp [(ne_of_lt hij).symm]
      exact ⟨Module.finrank K L + r, (bL.sumQuot bQ).reindex finSumFinEquiv,
        upper_triangular_sumQuot T L hL bL bQ hbL hbQ⟩

theorem triangularization : Specs.D05.M10.Triangularization.triangularization := by
  intro K V _ _ _ _ T
  have h₁ := triangular_implies_charpoly_splits T
  have h₂ := charpoly_splits_implies_minpoly_splits T
  have h₃ := minpoly_splits_implies_triangular T
  exact ⟨⟨h₁, fun h => h₃ (h₂ h)⟩, ⟨fun h => h₂ (h₁ h), h₃⟩⟩

end D05.M10.Triangularization
