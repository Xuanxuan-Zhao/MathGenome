import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.TraceIdeals.WeylProducts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Tactic.NormNum

noncomputable section
universe u
namespace ExpandedFA.TraceIdeals.WeylProducts

open CompactSpectral.SingularApproximation
section Algebra
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma exists_subspace_finrank [FiniteDimensional K V] (k : ℕ) (hk : k ≤ finrank K V) :
    ∃ U : Submodule K V, finrank K U = k := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank hk
  exact ⟨Submodule.span K (Set.range v), by simpa using finrank_span_eq_card hv⟩

/-- Every nilpotent endomorphism has invariant subspaces of all dimensions. -/
lemma nilpotent_invariant_subspace [FiniteDimensional K V] (N : Module.End K V)
    (hN : IsNilpotent N) (k : ℕ) (hk : k ≤ finrank K V) :
    ∃ U : Submodule K V, finrank K U = k ∧ ∀ x ∈ U, N x ∈ U := by
  classical
  suffices ∀ d : ℕ, finrank K V = d → ∀ k ≤ d,
      ∃ U : Submodule K V, finrank K U = k ∧ ∀ x ∈ U, N x ∈ U by
    exact this _ rfl k hk
  clear hk k
  intro d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
    intro hd k hk
    by_cases hk0 : k = 0
    · subst k
      exact ⟨⊥, by simp, by simp⟩
    by_cases hker : k ≤ finrank K (LinearMap.ker N)
    · obtain ⟨W, hW⟩ := exists_subspace_finrank k hker
      refine ⟨W.map (LinearMap.ker N).subtype, ?_, ?_⟩
      · simpa only [Submodule.finrank_map_subtype_eq] using hW
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hy0 : N y = 0 := y.property
        change N (y : V) ∈ _
        simpa only [hy0] using (W.map (LinearMap.ker N).subtype).zero_mem
    -- Nilpotence gives a nonzero kernel on every nonzero ambient space.
    have hdim : finrank K N.range < d := by
      have hr := N.finrank_range_add_finrank_ker
      have hpos : 0 < finrank K (LinearMap.ker N) := by
        by_contra hp
        have hbot : LinearMap.ker N = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
        have hinj : Function.Injective N := LinearMap.ker_eq_bot.mp hbot
        obtain ⟨p, hp⟩ := hN
        have hp_inj : Function.Injective (N ^ p) := by
          simpa only [Module.End.coe_pow] using hinj.iterate p
        have : Subsingleton V := ⟨fun x y => hp_inj (by simp [hp])⟩
        have : finrank K V = 0 := finrank_zero_of_subsingleton
        omega
      omega
    have hrinv : ∀ x ∈ N.range, N x ∈ N.range := fun x _ => ⟨x, rfl⟩
    let Nr : Module.End K N.range := N.restrict hrinv
    have hNr : IsNilpotent Nr := Module.End.isNilpotent.restrict hrinv hN
    have hkr : k - finrank K (LinearMap.ker N) ≤ finrank K N.range := by
      have := N.finrank_range_add_finrank_ker
      omega
    obtain ⟨W, hWdim, hWinv⟩ :=
      ih (finrank K N.range) hdim Nr hNr rfl _ hkr
    -- The preimage adds the whole kernel to the selected space in the range.
    let U : Submodule K V := W.comap N.rangeRestrict
    have hmap : U.map N = W.map N.range.subtype := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨N.rangeRestrict y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨v, hv⟩ := y.property
        refine ⟨v, ?_, hv⟩
        change N.rangeRestrict v ∈ W
        have he : N.rangeRestrict v = y := Subtype.ext hv
        rwa [he]
    have hkerle : LinearMap.ker N ≤ U := by
      intro x hx
      change N.rangeRestrict x ∈ W
      have he : N.rangeRestrict x = 0 := Subtype.ext hx
      rw [he]
      exact W.zero_mem
    -- Rank-nullity computes its dimension without choosing a Jordan basis.
    have hUdim : finrank K U = k := by
      let F := N.domRestrict U
      have hFr : LinearMap.range F = U.map N := LinearMap.range_domRestrict _ _
      have hFk : LinearMap.ker F = (LinearMap.ker N).comap U.subtype := rfl
      have hkd : finrank K (LinearMap.ker F) = finrank K (LinearMap.ker N) := by
        rw [hFk]
        exact (Submodule.comapSubtypeEquivOfLe hkerle).finrank_eq
      have hr := F.finrank_range_add_finrank_ker
      rw [hFr, hmap, Submodule.finrank_map_subtype_eq, hWdim, hkd] at hr
      omega
    refine ⟨U, hUdim, ?_⟩
    intro x hx
    change N.rangeRestrict (N x) ∈ W
    exact hWinv (N.rangeRestrict x) hx

lemma det_eq_of_intertwine {W : Type*} [AddCommGroup W] [Module K W]
    (e : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (e x) = e (f x)) : g.det = f.det := by
  have hg : g = e.toLinearMap.comp (f.comp e.symm.toLinearMap) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simpa using h y
  rw [hg]
  exact LinearMap.det_conj f e

lemma det_of_nilpotent_shift [FiniteDimensional K V] (A : Module.End K V) (z : K)
    (hA : IsNilpotent (A - z • 1)) : A.det = z ^ finrank K V := by
  have hn : IsNilpotent (z • (1 : Module.End K V) - A) := by
    simpa only [neg_sub] using hA.neg
  have he := congrArg (Polynomial.eval z) hn.charpoly_eq_X_pow_finrank
  rw [LinearMap.eval_charpoly] at he
  simpa only [Algebra.algebraMap_eq_smul_one, sub_sub_cancel,
    Polynomial.eval_pow, Polynomial.eval_X] using he

/-- A partial generalized eigenspace with the prescribed dimension, even
when that dimension cuts through a Jordan block. -/
lemma generalized_invariant_subspace (f : Module.End K V) (z : K)
    [FiniteDimensional K (f.maxGenEigenspace z)] (k : ℕ)
    (hk : k ≤ finrank K (f.maxGenEigenspace z)) :
    ∃ M : Submodule K V, M ≤ f.maxGenEigenspace z ∧ FiniteDimensional K M ∧
      ∃ hM : ∀ x ∈ M, f x ∈ M, finrank K M = k ∧ (f.restrict hM).det = z ^ k := by
  let E := f.maxGenEigenspace z
  have hfE : ∀ x ∈ E, f x ∈ E :=
    f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) z
  let g : Module.End K E := f.restrict hfE
  have hg : g.maxGenEigenspace z = ⊤ := by
    rw [Module.End.maxGenEigenspace, Module.End.genEigenspace_restrict]
    exact Submodule.comap_subtype_self E
  have hN : IsNilpotent (g - z • 1) := by
    apply ((LinearMap.charpoly_nilpotent_tfae (g - z • 1)).out 3 1).mp
    intro x
    exact (Module.End.mem_maxGenEigenspace g z x).mp (by rw [hg]; trivial)
  obtain ⟨U, hUdim, hU⟩ := nilpotent_invariant_subspace (g - z • 1) hN k hk
  have hgU : ∀ x ∈ U, g x ∈ U := by
    intro x hx
    have := U.add_mem (hU x hx) (U.smul_mem z hx)
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      sub_add_cancel] using this
  let M := U.map E.subtype
  have hM : ∀ x ∈ M, f x ∈ M := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨g y, hgU y hy, rfl⟩
  refine ⟨M, Submodule.map_subtype_le E U, inferInstance, hM, ?_, ?_⟩
  · simpa only [M, Submodule.finrank_map_subtype_eq] using hUdim
  · have hnU : IsNilpotent ((g.restrict hgU) - z • 1) := by
      have ht := Module.End.isNilpotent.restrict hU hN
      convert ht using 1
      ext x
      rfl
    have hd := det_of_nilpotent_shift (g.restrict hgU) z hnU
    rw [hUdim] at hd
    rw [← hd]
    exact det_eq_of_intertwine (Submodule.equivSubtypeMap E U)
      (g.restrict hgU) (f.restrict hM) (fun x => rfl)

/-- Add two disjoint invariant spaces, with their actual restriction
operators. This also supplies the finite-dimensional instance. -/
lemma invariant_direct_sum (f : Module.End K V) (U W : Submodule K V)
    [FiniteDimensional K U] [FiniteDimensional K W] (hUW : Disjoint U W)
    (hU : ∀ x ∈ U, f x ∈ U) (hW : ∀ x ∈ W, f x ∈ W) :
    ∃ M : Submodule K V, M ≤ U ⊔ W ∧ FiniteDimensional K M ∧
      ∃ hM : ∀ x ∈ M, f x ∈ M,
        finrank K M = finrank K U + finrank K W ∧
          (f.restrict hM).det = (f.restrict hU).det * (f.restrict hW).det := by
  let F : U × W →ₗ[K] V := U.subtype.coprod W.subtype
  have hinj : Function.Injective F := by
    apply LinearMap.ker_eq_bot.mp
    dsimp only [F]
    rw [LinearMap.ker_coprod_of_disjoint_range U.subtype W.subtype (by simpa using hUW)]
    simp
  let e := LinearEquiv.ofInjective F hinj
  let M := F.range
  have hM : ∀ x ∈ M, f x ∈ M := by
    rintro x ⟨⟨u, w⟩, rfl⟩
    exact ⟨(⟨f u, hU u u.property⟩, ⟨f w, hW w w.property⟩), (map_add f _ _).symm⟩
  refine ⟨M, ?_, inferInstance, hM, ?_, ?_⟩
  · rintro x ⟨⟨u, w⟩, rfl⟩
    exact Submodule.add_mem_sup u.property w.property
  · rw [← e.finrank_eq, Module.finrank_prod]
  · rw [← LinearMap.det_prodMap]
    exact det_eq_of_intertwine e _ (f.restrict hM) (fun x => by
      apply Subtype.ext
      exact map_add f _ _)

/-- Assemble independent generalized eigenspaces with chosen frequencies. -/
lemma finite_generalized_selection (f : Module.End K V) (s : Finset K) (m : K → ℕ)
    (hfin : ∀ z ∈ s, FiniteDimensional K (f.maxGenEigenspace z))
    (hm : ∀ z ∈ s, m z ≤ finrank K (f.maxGenEigenspace z)) :
    ∃ M : Submodule K V, M ≤ ⨆ z ∈ s, f.maxGenEigenspace z ∧ FiniteDimensional K M ∧
      ∃ hM : ∀ x ∈ M, f x ∈ M,
        finrank K M = ∑ z ∈ s, m z ∧ (f.restrict hM).det = ∏ z ∈ s, z ^ m z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⊥, bot_le, inferInstance, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [LinearMap.det_eq_one_of_finrank_eq_zero]
  | @insert z s hzs ih =>
    obtain ⟨M, hMle, hMfin, hM, hMdim, hMdet⟩ :=
      ih (fun a ha => hfin a (Finset.mem_insert_of_mem ha))
        (fun a ha => hm a (Finset.mem_insert_of_mem ha))
    let := hMfin
    let := hfin z (Finset.mem_insert_self z s)
    obtain ⟨U, hUle, hUfin, hU, hUdim, hUdet⟩ :=
      generalized_invariant_subspace f z (m z) (hm z (Finset.mem_insert_self z s))
    let := hUfin
    have hdis : Disjoint U M :=
      ((f.independent_maxGenEigenspace).disjoint_biSup (by simpa using hzs)).mono hUle hMle
    obtain ⟨P, hPle, hPfin, hP, hPdim, hPdet⟩ := invariant_direct_sum f U M hdis hU hM
    refine ⟨P, ?_, hPfin, hP, ?_, ?_⟩
    · apply hPle.trans
      apply sup_le
      · exact hUle.trans (le_iSup_of_le z (le_iSup_of_le (Finset.mem_insert_self z s) le_rfl))
      · apply hMle.trans
        exact iSup_mono fun a => iSup_mono' fun ha =>
          ⟨Finset.mem_insert_of_mem ha, le_rfl⟩
    · rw [hPdim, hUdim, hMdim, Finset.sum_insert hzs]
    · rw [hPdet, hUdet, hMdet, Finset.prod_insert hzs]
end Algebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The source's positive shift and Mathlib's negative shift have the same
power kernels. This keeps the algebraic multiplicity bridge explicit. -/
lemma shift_power_kernel (T : H →L[ℂ] H) (z : ℂ) (p : ℕ) :
    LinearMap.ker ((z • LinearMap.id - T.toLinearMap) ^ p) =
      Module.End.genEigenspace T.toLinearMap z p := by
  rw [Module.End.genEigenspace_nat]
  have hneg : z • LinearMap.id - T.toLinearMap =
      (-1 : ℂ) • (T.toLinearMap - z • (1 : Module.End ℂ H)) := by
    simp only [neg_one_smul, neg_sub, Module.End.one_eq_id]
  rw [hneg, smul_pow, LinearMap.ker_smul _ _ (pow_ne_zero p (by norm_num))]

/-- The multiplicity used here is finite at every nonzero scalar on the
original Hilbert space; no finite-dimensional or normality premise is added. -/
lemma compact_maxGenEigenspace_finiteDimensional (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    {z : ℂ} (hz : z ≠ 0) : FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z) := by
  obtain ⟨p, hp, hfin, hstable, hunion⟩ :=
    Fredholm.compact_generalized_eigenspace_stabilizes T hT z hz
  have heq : Module.End.maxGenEigenspace T.toLinearMap z =
      LinearMap.ker ((z • LinearMap.id - T.toLinearMap) ^ p) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
      have hxm : x ∈ Module.End.genEigenspace T.toLinearMap z m := by
        exact Module.End.mem_genEigenspace_nat.mpr hm
      by_cases hmp : m ≤ p
      · rw [shift_power_kernel]
        exact (Module.End.genEigenspace T.toLinearMap z).monotone (by exact_mod_cast hmp) hxm
      · rw [← shift_power_kernel] at hxm
        rwa [hstable m (Nat.le_of_not_ge hmp)] at hxm
    · rw [shift_power_kernel]
      exact Module.End.genEigenspace_le_maximal T.toLinearMap z p
  rw [heq]
  exact hfin

/-- Rank < 1 forces the approximant to be zero, including on the zero space. -/
lemma approximationNumber_one (T : H →L[ℂ] H) : approximationNumber T 1 = ‖T‖ := by
  change CompactSpectral.SingularApproximation.Spec.ApproximationNumberValue T 1 = ‖T‖
  apply le_antisymm
  · simpa only [sub_zero] using approximationNumber_le_error ℂ H H T 0 1 (by simp)
  · apply le_approximationNumber ℂ H H T 1 (by omega)
    intro F hF
    have hz : F = 0 := by
      have hrange : F.toLinearMap.range = ⊥ :=
        Submodule.rank_eq_zero.mp (Cardinal.lt_one_iff.mp hF)
      have hlin : F.toLinearMap = 0 := LinearMap.range_eq_bot.mp hrange
      ext x
      exact LinearMap.congr_fun hlin x
    simp [hz]

section FiniteDimensional
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
open Module

lemma native_norm_image_sum_sq (A : E →ₗ[ℂ] E) {J : Type*} (e : J → Fin (finrank ℂ E))
    (he : Function.Injective e) (a : J → ℂ) (q : Finset J) :
    ‖A (∑ j ∈ q, a j • A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl (e j))‖ ^ 2 =
      ∑ j ∈ q, ‖a j‖ ^ 2 * A.singularValues (e j) ^ 2 := by
  let b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let G := A.adjoint.comp A
  have hg (j : J) : G (b (e j)) =
      (A.isSymmetric_adjoint_comp_self.eigenvalues rfl (e j) : ℂ) • b (e j) :=
    A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl (e j)
  have hb : Orthonormal ℂ (fun j => b (e j)) := b.orthonormal.comp e he
  have hm : G (∑ j ∈ q, a j • b (e j)) =
      ∑ j ∈ q, (a j * (A.isSymmetric_adjoint_comp_self.eigenvalues rfl (e j) : ℂ)) • b (e j) := by
    simp only [map_sum, map_smul, hg, smul_smul]
  change ‖A (∑ j ∈ q, a j • b (e j))‖ ^ 2 = _
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [← A.adjoint_inner_right, ← LinearMap.comp_apply, hm]
  rw [hb.inner_sum]
  simp only [map_sum, ← mul_assoc, Complex.conj_mul']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp_rw [← A.sq_singularValues_fin rfl]
  norm_cast

lemma native_singularValue_le_error (A F : E →L[ℂ] E) (k : ℕ)
    (hF : F.toLinearMap.rank < (k + 1 : ℕ)) :
    A.toLinearMap.singularValues k ≤ ‖A - F‖ := by
  classical
  by_cases hk : finrank ℂ E ≤ k
  · rw [A.toLinearMap.singularValues_of_finrank_le hk]
    exact norm_nonneg _
  have hk : k < finrank ℂ E := Nat.lt_of_not_ge hk
  let b := A.toLinearMap.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let e : Fin (k+1) → Fin (finrank ℂ E) := fun j => ⟨j.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun j : Fin (finrank ℂ E) => j.val) hij
  have hb : Orthonormal ℂ (fun j => b (e j)) := b.orthonormal.comp e he
  let c := A.toLinearMap.singularValues k
  have hc : 0 ≤ c := A.toLinearMap.singularValues_nonneg k
  have hlow (a : Fin (k+1) → ℂ) :
      c * ‖∑ j, a j • b (e j)‖ ≤ ‖A (∑ j, a j • b (e j))‖ := by
    have hnorm : ‖∑ j, a j • b (e j)‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
      have h := congrArg RCLike.re (hb.inner_sum a a Finset.univ)
      simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_re, map_sum,
        RCLike.conj_mul, ← RCLike.ofReal_pow] using h
    have hnormA := native_norm_image_sum_sq A.toLinearMap e he a Finset.univ
    change ‖A (∑ j, a j • b (e j))‖ ^ 2 = _ at hnormA
    have hs : (c * ‖∑ j, a j • b (e j)‖)^2 ≤ ‖A (∑ j, a j • b (e j))‖^2 := by
      rw [mul_pow, hnorm, hnormA, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      rw [mul_comm (c^2)]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply pow_le_pow_left₀ hc
      exact A.toLinearMap.singularValues_antitone (by dsimp [e]; omega)
    nlinarith [norm_nonneg (A (∑ j, a j • b (e j)))]
  by_contra h
  have hlt : ‖A - F‖ < c := lt_of_not_ge h
  have hli : LinearIndependent ℂ (fun j => F (b (e j))) := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha
    let x := ∑ j, a j • b (e j)
    have hxF : F x = 0 := by simpa only [x, map_sum, map_smul] using ha
    have hxge := hlow a
    change c * ‖x‖ ≤ ‖A x‖ at hxge
    have hxle := (A - F).le_opNorm x
    rw [sub_apply, hxF, sub_zero] at hxle
    have hx : x = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg x]
    exact Fintype.linearIndependent_iff.mp hb.linearIndependent a hx
  let f : Fin (k+1) → F.range := fun j => ⟨F (b (e j)), ⟨b (e j), rfl⟩⟩
  have hli' : LinearIndependent ℂ f := hli.of_comp F.range.subtype
  have hh := hli'.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast] at hh
  have hlt' := Cardinal.lift_lt.mpr hF
  exact (not_lt_of_ge hh) (by simpa only [Cardinal.lift_natCast] using hlt')

lemma native_singularValue_le_approximationNumber (A : E →L[ℂ] E) (k : ℕ) :
    A.toLinearMap.singularValues k ≤
      ExpandedFA.CompactSpectral.SingularApproximation.approximationNumber A (k+1) := by
  apply ExpandedFA.CompactSpectral.SingularApproximation.le_approximationNumber ℂ E E A
    (k+1) (Nat.succ_pos _) _
  intro F hF
  exact native_singularValue_le_error A F k hF

lemma finiteDet_le_singularProduct (A : E →L[ℂ] E) :
    ‖A.toLinearMap.det‖ ≤
      ∏ i : Fin (finrank ℂ E),
        ExpandedFA.CompactSpectral.SingularApproximation.Spec.SingularValueValue A (i.val + 1) := by
  have hA : ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue A.toLinearMap := by
    exact ((isCompact_closedBall (0 : E) 1).image A.continuous).closure
  rw [← A.toLinearMap.normDet_eq_norm_det, A.toLinearMap.normDet_eq_prod_singularValues,
    ← Fin.prod_univ_eq_prod_range]
  change (∏ i : Fin (finrank ℂ E), A.toLinearMap.singularValues i) ≤ _
  apply Finset.prod_le_prod₀
  · intro i _
    exact A.toLinearMap.singularValues_nonneg i
  · intro i _
    rw [(ExpandedFA.CompactSpectral.SingularApproximation.best_approximation
      ℂ E E A hA (i.val + 1) (Nat.succ_pos _)).1]
    exact native_singularValue_le_approximationNumber A i

end FiniteDimensional

variable [CompleteSpace H]

lemma singularValue_one (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap) :
    CompactSpectral.SingularApproximation.Spec.SingularValueValue T 1 = ‖T‖ := by
  rw [(best_approximation ℂ H H T hT 1 (by omega)).1]
  exact approximationNumber_one T

lemma eigenvalue_norm_le_first_singularValue (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    {z : ℂ} (hz : Module.End.HasEigenvalue T.toLinearMap z) :
    ‖z‖ ≤ CompactSpectral.SingularApproximation.Spec.SingularValueValue T 1 := by
  obtain ⟨x, hx, hne⟩ := hz.exists_hasEigenvector
  have he : T x = z • x := Module.End.mem_eigenspace_iff.mp hx
  rw [singularValue_one T hT]
  have hbound := T.le_opNorm x
  rw [he, norm_smul] at hbound
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hne)).mp hbound

/-- Orthogonal compression cannot increase any of the canonical singular
values. The norm bounds also hold for the zero subspace. -/
lemma compression_singularValue_le (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M] (n : ℕ) (hn : 0 < n) :
    CompactSpectral.SingularApproximation.Spec.SingularValueValue
        (M.orthogonalProjectionOnto.comp (T.comp M.subtypeL)) n ≤
      CompactSpectral.SingularApproximation.Spec.SingularValueValue T n := by
  have h := singularValue_ideal ℂ H H M M T M.orthogonalProjectionOnto M.subtypeL hT n hn
  have hs := (singular_sequence_properties ℂ H H T hT).1 n hn
  apply h.trans
  calc
    ‖M.orthogonalProjectionOnto‖ * ‖M.subtypeL‖ *
        CompactSpectral.SingularApproximation.Spec.SingularValueValue T n ≤
      1 * 1 * CompactSpectral.SingularApproximation.Spec.SingularValueValue T n := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
            (norm_nonneg M.subtypeL) (by norm_num)) hs
    _ = _ := by ring

/-- The restriction and the orthogonal compression are the same actual
operator. Both sides have the inherited norm, not a transported auxiliary norm. -/
lemma invariantDet_le_singularProduct (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (M : Submodule ℂ H) [FiniteDimensional ℂ M]
    (hM : ∀ x ∈ M, T x ∈ M) :
    ‖(T.toLinearMap.restrict hM).det‖ ≤
      ∏ i : Fin (Module.finrank ℂ M),
        CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1) := by
  let A : M →L[ℂ] M := (T.toLinearMap.restrict hM).toContinuousLinearMap
  have hA : Compactness.DefinitionsSpec.IsCompactLinearMapValue A.toLinearMap :=
    ((isCompact_closedBall (0 : M) 1).image A.continuous).closure
  have heq : A = M.orthogonalProjectionOnto.comp (T.comp M.subtypeL) := by
    apply ContinuousLinearMap.ext
    intro x
    change (⟨T x, hM x x.property⟩ : M) = M.orthogonalProjectionOnto (T x)
    exact (M.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hM x x.property⟩).symm
  apply (finiteDet_le_singularProduct A).trans
  apply Finset.prod_le_prod₀
  · intro i _
    exact (singular_sequence_properties ℂ M M A hA).1 (i.val + 1) (Nat.succ_pos _)
  · intro i _
    rw [heq]
    exact compression_singularValue_le T hT M (i.val + 1) (Nat.succ_pos _)

/-- Take the norm of the realized determinant and apply the analytic
restriction bound. -/
lemma weylProduct_of_invariantRealization : Spec.RealizationImpliesWeyl.{u} := by
  intro h H _ _ _ T hT n ev hev
  obtain ⟨M, hfin, hM, hdim, hdet⟩ := h H T hT n ev hev
  let := hfin
  subst n
  calc
    (∏ i, ‖ev i‖) = ‖(T.toLinearMap.restrict hM).det‖ := by
      rw [hdet, norm_prod]
    _ ≤ _ := invariantDet_le_singularProduct T hT M hM

/-- A vanishing entry handles every padded finite-rank boundary case. -/
lemma product_le_of_zero_entry (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    {n : ℕ} (ev : Fin n → ℂ) (hzero : ∃ i, ev i = 0) :
    (∏ i, ‖ev i‖) ≤
      ∏ i : Fin n, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1) := by
  obtain ⟨i, hi⟩ := hzero
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
  apply Finset.prod_nonneg
  intro j _
  exact (singular_sequence_properties ℂ H H T hT).1 (j.val + 1) (Nat.succ_pos _)

/-- Padding is a consequence of the unpadded theorem, not an extra spectral
assumption. This lemma contains no unproved analytic or algebraic step. -/
lemma paddedWeylProduct_of_weylProduct (h : Spec.WeylProduct.{u}) :
    Spec.PaddedWeylProduct.{u} := by
  classical
  intro H _ _ _ T hT n ev hev
  by_cases hz : ∃ i, ev i = 0
  · exact product_le_of_zero_entry T hT ev hz
  · have hnonzero : ∀ i, ev i ≠ 0 := by simpa only [not_exists] using hz
    apply h H T hT n ev
    refine ⟨fun i => ⟨hnonzero i, hev.1 i (hnonzero i)⟩, ?_⟩
    intro z
    by_cases hz : z = 0
    · subst z
      simp [Finset.filter_eq_empty_iff.mpr (fun i _ => hnonzero i)]
    · exact hev.2 z hz

lemma weylProduct_empty (T : H →L[ℂ] H) (ev : Fin 0 → ℂ) :
    (∏ i, ‖ev i‖) ≤
      ∏ i : Fin 0, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1) := by
  simp

lemma weylProduct_one (T : H →L[ℂ] H)
    (hT : Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap)
    (ev : Fin 1 → ℂ) (hev : Spec.EigenvalueSelection T ev) :
    (∏ i, ‖ev i‖) ≤
      ∏ i : Fin 1, CompactSpectral.SingularApproximation.Spec.SingularValueValue T (i.val + 1) := by
  simpa using eigenvalue_norm_le_first_singularValue T hT (hev.1 0).2

/-- Realize the selected algebraic multiplicities on the original Hilbert
space, using compact Riesz theory only to ensure finite generalized spaces. -/
theorem compact_invariant_realization : Spec.CompactInvariantRealization.{u} := by
  classical
  intro H _ _ _ T hT n ev hev
  let s := Finset.univ.image ev
  let m : ℂ → ℕ := fun z => (Finset.univ.filter (fun i => ev i = z)).card
  have hfin : ∀ z ∈ s, FiniteDimensional ℂ (Module.End.maxGenEigenspace T.toLinearMap z) := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact compact_maxGenEigenspace_finiteDimensional T hT (hev.1 i).1
  obtain ⟨M, _, hMfin, hM, hdim, hdet⟩ :=
    finite_generalized_selection T.toLinearMap s m hfin (fun z _ => hev.2 z)
  refine ⟨M, hMfin, hM, ?_, ?_⟩
  · rw [hdim]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_eq_sum_card_image ev Finset.univ).symm
  · rw [hdet]
    exact (Finset.prod_comp (s := Finset.univ) (fun z : ℂ => z) ev).symm

/-- Weyl's product inequality for all finite selections with algebraic
multiplicity, without normality, separability, or invertibility assumptions. -/
theorem weyl_product : Spec.WeylProduct.{u} :=
  weylProduct_of_invariantRealization compact_invariant_realization

theorem padded_weyl_product : Spec.PaddedWeylProduct.{u} :=
  paddedWeylProduct_of_weylProduct weyl_product

end ExpandedFA.TraceIdeals.WeylProducts
