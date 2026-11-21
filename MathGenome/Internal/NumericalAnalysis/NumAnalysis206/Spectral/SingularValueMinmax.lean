import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.SingularValueMinmax
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData
import MathGenome.Internal.D05.M14.LowRank.LowerBound
import MathGenome.Internal.D05.M14.LowRank.Truncation

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.SingularValueMinmax
open MatrixDefinitions SingularValueMinmaxDefinitions

variable {K V : Type*} [RCLike K] [NormedAddCommGroup V]
  [InnerProductSpace K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Normalize a nonzero vector of a positive-dimensional subspace. -/
theorem exists_unit_mem (S : Submodule K V) (hS : 0 < Module.finrank K S) :
    ∃ x ∈ S, ‖x‖ = 1 := by
  have hne : S ≠ ⊥ := by
    intro h
    subst S
    rw [finrank_bot] at hS
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨(‖x‖⁻¹ : K) • x, S.smul_mem _ hx,
    by simp [norm_smul, norm_ne_zero_iff.mpr hx0]⟩

/-- A dimension inequality forces a unit vector in the orthogonal intersection. -/
theorem exists_unit_mem_inter_orthogonal (L M : Submodule K V)
    (hd : Module.finrank K L < Module.finrank K M) :
    ∃ x ∈ M, x ∈ L.orthogonal ∧ ‖x‖ = 1 := by
  let f : M →ₗ[K] L := L.orthogonalProjectionOnto.toLinearMap.comp M.subtype
  have hni : ¬ Function.Injective f := by
    intro h
    have := LinearMap.finrank_le_finrank_of_injective h
    omega
  have hk : f.ker ≠ ⊥ := fun h => hni (LinearMap.ker_eq_bot.mp h)
  obtain ⟨z, hz, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hz0 : (z : V) ≠ 0 := by simpa using hzne
  have hperp : (z : V) ∈ L.orthogonal :=
    L.orthogonalProjectionOnto_eq_zero_iff.mp hz
  exact ⟨(‖(z : V)‖⁻¹ : K) • (z : V), M.smul_mem _ z.property,
    L.orthogonal.smul_mem _ hperp,
    by simp [norm_smul, norm_ne_zero_iff.mpr hz0]⟩

omit [FiniteDimensional K V] in
/-- Select a subspace of an exact smaller dimension without losing kernel directions. -/
theorem exists_subspace_le_finrank (U : Submodule K V) (d : ℕ)
    (hd : d ≤ Module.finrank K U) :
    ∃ S : Submodule K V, S ≤ U ∧ Module.finrank K S = d := by
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := U) hd
  let g : Fin d → V := fun j => (f j : V)
  have hg : LinearIndependent K g :=
    hf.map' U.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨Submodule.span K (Set.range g), ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact (f j).property
  · simpa using finrank_span_eq_card hg

variable {m n : ℕ}

/-- Compactness gives an actual maximum on every nonempty trial sphere. -/
theorem exists_subspace_maximum (A : Mat K m n) (S : Submodule K (Vec K n))
    (hS : 0 < Module.finrank K S) :
    ∃ r, IsGreatest (unitImageNorms A S) r := by
  obtain ⟨x, hx, hxnorm⟩ := exists_unit_mem S hS
  have hne : (Metric.sphere (0 : S) 1).Nonempty :=
    ⟨⟨x, hx⟩, by simpa using hxnorm⟩
  have hc : Continuous (fun x : S => ‖A.toEuclideanLin (x : Vec K n)‖) :=
    (A.toEuclideanLin.continuous_of_finiteDimensional.comp continuous_subtype_val).norm
  obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : S) 1).exists_isMaxOn hne hc.continuousOn
  refine ⟨‖A.toEuclideanLin (y : Vec K n)‖, ⟨?_, ?_⟩⟩
  · exact ⟨y, y.property, by simpa using hy, rfl⟩
  · rintro _ ⟨z, hz, hznorm, rfl⟩
    exact (isMaxOn_iff.mp hmax) ⟨z, hz⟩ (by simpa using hznorm)

/-- Every trial space contains a unit vector whose image norm is at least sigma_i.
For positive sigma_i use the initial singular subspace; for zero sigma_i every
unit vector suffices. -/
theorem exists_unit_lower (A : Mat K m n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (S : Submodule K (Vec K n)) (hS : Module.finrank K S = n - i + 1) :
    ∃ x ∈ S, ‖x‖ = 1 ∧ singularValue A i ≤ ‖A.toEuclideanLin x‖ := by
  classical
  let T := A.toEuclideanLin
  let k := i - 1
  change ∃ x ∈ S, ‖x‖ = 1 ∧ T.singularValues k ≤ ‖T x‖
  by_cases hk : k < Module.finrank K T.range
  · obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
    let e : Fin (k + 1) → Vec K n := fun j =>
      d.domainBasis (Fin.castLE T.finrank_range_le
        (Fin.castLE (Nat.succ_le_of_lt hk) j))
    let E := Submodule.span K (Set.range e)
    have he : Orthonormal K e :=
      (d.domainBasis.orthonormal.comp _ (Fin.castLE_injective _)).comp _
        (Fin.castLE_injective _)
    have hE : Module.finrank K E = k + 1 := by
      simpa using finrank_span_eq_card he.linearIndependent
    have hperp : Module.finrank K S.orthogonal = k := by
      have hh := S.finrank_add_finrank_orthogonal
      rw [finrank_euclideanSpace_fin, hS] at hh
      dsimp only [k]
      omega
    obtain ⟨x, hxE, hxS, hxn⟩ := exists_unit_mem_inter_orthogonal S.orthogonal E
      (by rw [hperp, hE]; omega)
    have hx : x ∈ S := by simpa only [Submodule.orthogonal_orthogonal] using hxS
    refine ⟨x, hx, hxn, ?_⟩
    simpa only [hxn, mul_one] using
      D05.M14.LowRank.LowerBound.span_norm_lower T d k hk x hxE
  · obtain ⟨x, hx, hxn⟩ := exists_unit_mem S (by rw [hS]; omega)
    refine ⟨x, hx, hxn, ?_⟩
    rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hk)]
    exact norm_nonneg _

/-- The kernel of the truncated SVD has enough dimension. Restricting its
residual estimate to a subspace of the exact trial dimension proves the upper bound. -/
theorem exists_subspace_upper (A : Mat K m n) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ S : Submodule K (Vec K n), Module.finrank K S = n - i + 1 ∧
      ∀ x ∈ S, ‖x‖ = 1 → ‖A.toEuclideanLin x‖ ≤ singularValue A i := by
  let T := A.toEuclideanLin
  let k := i - 1
  obtain ⟨d⟩ := D05.M14.Svd.exists_svd T
  let B := D05.svdTruncation T d k
  have hr : Module.finrank K B.range ≤ k := D05.M14.LowRank.Truncation.rank_le T d k
  have hker : n - i + 1 ≤ Module.finrank K B.ker := by
    have hh := B.finrank_range_add_finrank_ker
    rw [finrank_euclideanSpace_fin] at hh
    dsimp only [k] at hr
    omega
  obtain ⟨S, hSB, hS⟩ := exists_subspace_le_finrank B.ker (n - i + 1) hker
  refine ⟨S, hS, ?_⟩
  intro x hx hxn
  have hxB : B x = 0 := hSB hx
  have hbound := D05.M14.LowRank.Truncation.residual_norm_le T d k x
  change ‖T x - B x‖ ≤ T.singularValues k * ‖x‖ at hbound
  change ‖T x‖ ≤ T.singularValues k
  simpa only [hxB, sub_zero, hxn, mul_one] using hbound

/-- The full attained min--max principle on the domain space. -/
theorem minmax : Specs.NumAnalysis206.SingularValueMinmax.minmax := by
  intro K _ m n A i hi hin
  have maxima (S : Submodule K (Vec K n)) (hS : Module.finrank K S = n - i + 1) :
      ∃ r, IsGreatest (unitImageNorms A S) r :=
    exists_subspace_maximum A S (by rw [hS]; omega)
  refine ⟨maxima, ?_⟩
  have lower (S : Submodule K (Vec K n)) (hS : Module.finrank K S = n - i + 1)
      (r : ℝ) (hr : IsGreatest (unitImageNorms A S) r) : singularValue A i ≤ r := by
    obtain ⟨x, hx, hxn, hTx⟩ := exists_unit_lower A i hi hin S hS
    exact hTx.trans (hr.2 ⟨x, hx, hxn, rfl⟩)
  constructor
  · obtain ⟨S, hS, hupp⟩ := exists_subspace_upper A i hi hin
    obtain ⟨r, hr⟩ := maxima S hS
    have hrle : r ≤ singularValue A i := by
      obtain ⟨x, hx, hxn, hTx⟩ := hr.1
      rw [← hTx]
      exact hupp x hx hxn
    have heq : r = singularValue A i := le_antisymm hrle (lower S hS r hr)
    exact ⟨S, hS, heq ▸ hr⟩
  · rintro r ⟨S, hS, hr⟩
    exact lower S hS r hr

/-- Taking the conditional infimum of the attained maxima gives the displayed formula. -/
theorem minmax_eq_sInf : Specs.NumAnalysis206.SingularValueMinmax.minmax_eq_sInf := by
  intro K _ m n A i hi hin
  obtain ⟨hmax, hmin⟩ := minmax A i hi hin
  have hsets : {r : ℝ | ∃ S : Submodule K (Vec K n),
      Module.finrank K S = n - i + 1 ∧ sSup (unitImageNorms A S) = r} =
      subspaceMaxima A (n - i + 1) := by
    ext r
    constructor
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨t, ht⟩ := hmax S hS
      exact ⟨S, hS, ht.csSup_eq.symm ▸ ht⟩
    · rintro ⟨S, hS, hr⟩
      exact ⟨S, hS, hr.csSup_eq⟩
  rw [hsets]
  exact hmin.csInf_eq.symm

end NumAnalysis206.SingularValueMinmax
