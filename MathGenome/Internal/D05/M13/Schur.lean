import MathGenome.Internal.Specs.D05.M13.Schur
import MathGenome.Internal.D05.M10.Triangularization
import MathGenome.Internal.D05.M12.GramSchmidt
import MathGenome.Internal.D05.Foundations.Fta

/-! Schur triangularization by preserving the flag under Gram–Schmidt.
Complex splitting uses the elementary FTA already proved upstream. -/
noncomputable section
namespace D05.M13.Schur
open Module

/-- The initial coordinate spans of an upper triangular basis are invariant. -/
theorem initial_span_invariant {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (T : Module.End K V) (b : Basis (Fin n) K V)
    (hb : (LinearMap.toMatrix b b T).IsUpperTriangular) (k : ℕ)
    {x : V} (hx : x ∈ Submodule.span K (b '' {i | i.val < k})) :
    T x ∈ Submodule.span K (b '' {i | i.val < k}) := by
  classical
  have hinv : Submodule.span K (b '' {i | i.val < k}) ≤
      (Submodule.span K (b '' {i | i.val < k})).comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change T (b j) ∈ Submodule.span K (b '' {i | i.val < k})
    apply b.mem_span_image.mpr
    intro i hi
    change i.val < k
    by_contra h
    change j.val < k at hj
    have hji : j < i := by
      change j.val < i.val
      omega
    apply (Finsupp.mem_support_iff.mp hi)
    simpa only [LinearMap.toMatrix_apply] using hb hji
  exact hinv hx

/-- Membership in an initial coordinate span forces all later coefficients to
vanish. This is the converse matrix step used after transporting the flag. -/
theorem upper_triangular_of_initial_spans {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {n : ℕ} (T : Module.End K V) (b : Basis (Fin n) K V)
    (h : ∀ j : Fin n, T (b j) ∈ Submodule.span K (b '' {i | i.val < j.val + 1})) :
    (LinearMap.toMatrix b b T).IsUpperTriangular := by
  classical
  intro i j hij
  change j < i at hij
  rw [LinearMap.toMatrix_apply]
  by_contra hne
  have hi := b.repr_support_subset_of_mem_span _ (h j) (Finsupp.mem_support_iff.mpr hne)
  change i.val < j.val + 1 at hi
  have hji : j.val < i.val := hij
  omega

theorem orthonormalize_triangular_basis :
    Specs.D05.M13.Schur.orthonormalize_triangular_basis := by
  intro F V _ _ _ n T b hb
  classical
  let v : Fin n → V := D05.gramSchmidtVectors (F := F) b
  have ho : Orthonormal F v :=
    (D05.M12.Orthonormal.orthonormal_iff_mathlib v).mp
      (D05.M12.GramSchmidt.orthonormal b b.linearIndependent)
  have hs (k : ℕ) (hk : k ≤ n) :
      Submodule.span F (v '' {i | i.val < k}) =
        Submodule.span F (b '' {i | i.val < k}) :=
    D05.M12.GramSchmidt.initial_spans b b.linearIndependent k hk
  have hfull : Submodule.span F (Set.range v) = ⊤ := by
    have hset : {i : Fin n | i.val < n} = Set.univ := by
      ext i
      simp
    simpa only [hset, Set.image_univ, b.span_eq] using hs n le_rfl
  let c : Basis (Fin n) F V := Basis.mk ho.linearIndependent hfull.ge
  let e : OrthonormalBasis (Fin n) F V := c.toOrthonormalBasis (by
    simpa only [c, Basis.coe_mk] using ho)
  have he : (e : Fin n → V) = v := by
    simp only [e, Basis.coe_toOrthonormalBasis, c, Basis.coe_mk]
  have heflag (k : ℕ) (hk : k ≤ n) :
      Submodule.span F (e '' {i | i.val < k}) =
        Submodule.span F (b '' {i | i.val < k}) := by rw [he]; exact hs k hk
  refine ⟨e, ?_, heflag⟩
  apply upper_triangular_of_initial_spans
  intro j
  have hk : j.val + 1 ≤ n := j.isLt
  have hej : e j ∈ Submodule.span F (b '' {i | i.val < j.val + 1}) := by
    rw [← heflag _ hk]
    exact Submodule.subset_span ⟨j, Nat.lt_succ_self _, rfl⟩
  have hT := initial_span_invariant T b hb (j.val + 1) hej
  simpa only [OrthonormalBasis.coe_toBasis, heflag _ hk] using hT

theorem triangularizable_orthonormal : Specs.D05.M13.Schur.triangularizable_orthonormal := by
  intro F V _ _ _ _ T ⟨n, b, hb⟩
  obtain ⟨e, he, _⟩ := orthonormalize_triangular_basis T b hb
  exact ⟨n, e, he⟩

theorem schur : Specs.D05.M13.Schur.schur := by
  intro V _ _ _ T
  apply triangularizable_orthonormal T
  exact (D05.M10.Triangularization.triangularization T).1.mpr
    (D05.Foundations.Fta.splits T.charpoly)

end D05.M13.Schur
