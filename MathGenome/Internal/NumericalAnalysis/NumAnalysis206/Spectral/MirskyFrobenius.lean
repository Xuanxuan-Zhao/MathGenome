import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.MirskyFrobenius
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.HoffmanWielandtSorted
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.HermitianDilation

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.MirskyFrobenius
open MatrixData HermitianDilationDefinitions

/-- The sorted Hermitian bound on a finite-dimensional inner product space.
This permits the sum-indexed coordinate space of a rectangular dilation. -/
lemma sorted_cost_le_frobenius {K V : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V] [FiniteDimensional K V]
    {d : ℕ} (T S : Module.End K V) (hT : T.IsSymmetric)
    (u v : OrthonormalBasis (Fin d) K V) (a b : Fin d → ℝ)
    (ha : Monotone a) (hb : Monotone b)
    (hTu : ∀ i, T (u i) = (a i : K) • u i)
    (hSv : ∀ j, S (v j) = (b j : K) • v j) :
    (∑ i, (a i - b i) ^ 2) ≤ D05.frobeniusNorm (T - S) ^ 2 := by
  have hP : (fun i j => ‖inner K (u i) (v j)‖ ^ 2) ∈ doublyStochastic ℝ (Fin d) := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨fun i j => sq_nonneg _, ?_, ?_⟩
    · intro i
      rw [v.sum_sq_norm_inner_left, u.norm_eq_one, one_pow]
    · intro j
      rw [u.sum_sq_norm_inner_right, v.norm_eq_one, one_pow]
  have hcost : D05.frobeniusNorm (T - S) ^ 2 =
      ∑ i, ∑ j, (a i - b j) ^ 2 * ‖inner K (u i) (v j)‖ ^ 2 := by
    rw [D05.M14.Frobenius.squared_basis_sum _ v]
    calc
      (∑ j, ‖(T - S) (v j)‖ ^ 2) =
          ∑ i, ∑ j, ‖inner K (u i) ((T - S) (v j))‖ ^ 2 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => (u.sum_sq_norm_inner_right _).symm)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have he : inner K (u i) ((T - S) (v j)) =
            ((a i - b j : ℝ) : K) * inner K (u i) (v j) := by
          rw [LinearMap.sub_apply, inner_sub_right, ← hT (u i) (v j), hTu, hSv,
            inner_smul_left, inner_smul_right, RCLike.conj_ofReal,
            RCLike.ofReal_sub, sub_mul]
        rw [he, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
  obtain ⟨p, hp⟩ := HoffmanWielandtNormal.exists_perm_cost_le
    (fun i j => ‖inner K (u i) (v j)‖ ^ 2)
    (fun i j => (a i - b j) ^ 2) hP
  exact (HoffmanWielandtSorted.sorted_squared_cost_le a b ha hb p).trans
    (hp.trans_eq hcost.symm)

lemma zipWith_ofFn {α β γ : Type*} {d : ℕ} (f : α → β → γ)
    (a : Fin d → α) (b : Fin d → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipWith, List.getElem_ofFn]

lemma signed_list_squared_cost {q : ℕ} (a b : Fin q → ℝ) (z : ℕ) :
    (List.zipWith (fun x y : ℝ => (x - y) ^ 2)
      (List.ofFn (fun i => -a i) ++ List.replicate z 0 ++ (List.ofFn a).reverse)
      (List.ofFn (fun i => -b i) ++ List.replicate z 0 ++ (List.ofFn b).reverse)).sum =
      2 * ∑ i, (a i - b i) ^ 2 := by
  rw [List.zipWith_append (by simp), List.zipWith_append (by simp),
    ← List.reverse_zipWith (by simp)]
  simp only [List.sum_append, List.sum_reverse, zipWith_ofFn, List.sum_ofFn,
    List.zipWith_replicate, min_self, sub_self, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, List.sum_replicate, nsmul_zero, add_zero]
  have hn : (∑ i, (-a i - -b i) ^ 2) = ∑ i, (a i - b i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn]
  ring

lemma dilation_list_cost_le {K : Type*} [RCLike K] {m n : ℕ} (A B : Mat K m n) :
    (List.zipWith (fun x y : ℝ => (x - y) ^ 2)
      (signedSingularValues A) (signedSingularValues B)).sum ≤
        2 * frobeniusNorm (A - B) ^ 2 := by
  let hA := HermitianDilation.isHermitian A
  let hB := HermitianDilation.isHermitian B
  let hT := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let hS := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hd : Module.finrank K (EuclideanSpace K (Fin m ⊕ Fin n)) = m + n := by simp
  let a := fun i : Fin (m + n) => hT.eigenvalues hd i.rev
  let b := fun i : Fin (m + n) => hS.eigenvalues hd i.rev
  let u := (hT.eigenvectorBasis hd).reindex Fin.revPerm
  let v := (hS.eigenvectorBasis hd).reindex Fin.revPerm
  have ha : Monotone a := fun i j hij =>
    hT.eigenvalues_antitone hd (Fin.rev_le_rev.mpr hij)
  have hb : Monotone b := fun i j hij =>
    hS.eigenvalues_antitone hd (Fin.rev_le_rev.mpr hij)
  have hTu : ∀ i, (hermitianDilation A).toEuclideanLin (u i) = (a i : K) • u i := by
    intro i
    simpa only [u, a, OrthonormalBasis.reindex_apply, Fin.revPerm_symm,
      Fin.revPerm_apply] using hT.apply_eigenvectorBasis hd i.rev
  have hSv : ∀ i, (hermitianDilation B).toEuclideanLin (v i) = (b i : K) • v i := by
    intro i
    simpa only [v, b, OrthonormalBasis.reindex_apply, Fin.revPerm_symm,
      Fin.revPerm_apply] using hS.apply_eigenvectorBasis hd i.rev
  have hc := sorted_cost_le_frobenius _ _ hT u v a b ha hb hTu hSv
  have hla : List.ofFn a = signedSingularValues A :=
    HermitianDilation.canonical_eigenvalue_list A hA
  have hlb : List.ofFn b = signedSingularValues B :=
    HermitianDilation.canonical_eigenvalue_list B hB
  rw [← hla, ← hlb, zipWith_ofFn, List.sum_ofFn]
  convert hc using 1
  rw [← map_sub, HermitianDilation.frobenius_difference_sq A B]

theorem mirsky_frobenius_min : Specs.NumAnalysis206.MirskyFrobenius.mirsky_frobenius_min := by
  intro K _ m n A B
  have h := dilation_list_cost_le A B
  unfold signedSingularValues at h
  rw [signed_list_squared_cost] at h
  change 2 * (∑ i : Fin (min m n),
    (MatrixDefinitions.singularValue A (i.val + 1) -
      MatrixDefinitions.singularValue B (i.val + 1)) ^ 2) ≤
        2 * MatrixDefinitions.frobeniusNorm (A - B) ^ 2 at h
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (MatrixDefinitions.singularValue A (i + 1) -
      MatrixDefinitions.singularValue B (i + 1)) ^ 2) (min m n)] at h
  linarith

theorem singular_difference_sum_eq_min :
    Specs.NumAnalysis206.MirskyFrobenius.singular_difference_sum_eq_min := by
  intro K _ m n A B N hN
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro i hi hqi
  have hqi' : min m n ≤ i :=
    Nat.le_of_not_gt (fun hi => hqi (Finset.mem_range.mpr hi))
  have ha := HermitianDilation.singularValues_zero_of_min_le A i hqi'
  have hb := HermitianDilation.singularValues_zero_of_min_le B i hqi'
  simp only [MatrixDefinitions.singularValue, Nat.add_sub_cancel, ha, hb,
    sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

theorem mirsky_frobenius : Specs.NumAnalysis206.MirskyFrobenius.mirsky_frobenius := by
  intro K _ m n A B
  rw [singular_difference_sum_eq_min A B n (min_le_right m n)]
  exact mirsky_frobenius_min A B

end NumAnalysis206.MirskyFrobenius
