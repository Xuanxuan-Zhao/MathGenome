import MathGenome.Internal.Specs.D07.Ch16.SubmoduleFreeFirstDiagonalSummand
import MathGenome.Internal.D07.Ch10.Bezout
import MathGenome.Internal.D07.Ch10.PidAscendingChain
import MathGenome.Internal.D07.Ch16.PidPrimitiveBasis
import Mathlib.LinearAlgebra.Basis.Basic

/-! The maximal-image-ideal argument for the first diagonal summand.
Only Bézout, the ascending chain condition, and elementary basis operations
are needed; no classification of finitely generated modules is assumed. -/

universe u v

namespace D07.Ch16.SubmoduleFreeFirstDiagonalSummand

open Module Submodule
open scoped Pointwise

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Maximality forces the generator to divide every functional at a preimage
of the generator. This is the Bézout step, before any basis induction. -/
theorem maximal_image_dvd [IsDomain R] [IsPrincipalIdealRing R] {N : Submodule R M} {φ : M →ₗ[R] R} {a : R}
    (himage : N.map φ = Ideal.span {a})
    (hmax : ∀ ψ : M →ₗ[R] R, N.map φ ≤ N.map ψ → N.map ψ = N.map φ)
    {y : M} (hy : y ∈ N) (hφy : φ y = a) (ψ : M →ₗ[R] R) : a ∣ ψ y := by
  obtain ⟨d, hd, hda, r, s, hrs⟩ := D07.Ch10.Bezout.pidGcdBezout R a (ψ y)
  let θ : M →ₗ[R] R := r • φ + s • ψ
  have hdθ : d ∈ N.map θ := by
    refine ⟨y, hy, ?_⟩
    simpa [θ, hφy] using hrs.symm
  have had : Ideal.span {a} ≤ Ideal.span {d} :=
    Ideal.span_singleton_le_span_singleton.mpr hda.1
  have hdle : Ideal.span {d} ≤ N.map θ :=
    (Ideal.span_singleton_le_iff_mem _).mpr hdθ
  have hθ := hmax θ (himage ▸ had.trans hdle)
  apply Ideal.mem_span_singleton.mp
  have hψ : ψ y ∈ Ideal.span {d} := Ideal.mem_span_singleton.mpr hda.2.1
  rw [← himage, ← hθ]
  exact hdle hψ

/-- Divisible coordinates assemble into a divisible vector. -/
theorem exists_smul_of_coord_dvd {n : ℕ} (b : Basis (Fin n) R M) (a : R) (y : M)
    (h : ∀ i, a ∣ b.coord i y) : ∃ e : M, a • e = y := by
  classical
  choose c hc using h
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [Finset.smul_sum, ← b.sum_repr y]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_smul, ← hc i]
  rfl

/-- A section of a functional gives the ambient internal direct sum. -/
theorem span_isCompl_ker {φ : M →ₗ[R] R} {e : M} (he : φ e = 1) :
    IsCompl (span R {e}) (LinearMap.ker φ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hk
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hc : c = 0 := by simpa [he] using LinearMap.mem_ker.mp hk
    simp [hc]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hk : x - φ x • e ∈ LinearMap.ker φ := by
      simp [LinearMap.mem_ker, he]
    have hs : φ x • e ∈ span R {e} := mem_span_singleton.mpr ⟨φ x, rfl⟩
    exact (Submodule.mem_sup.mpr ⟨_, hs, _, hk, add_sub_cancel _ _⟩)

/-- Delete a basis vector on which the functional is one. The other vectors
are corrected by subtracting their functional value times that vector.
Their coordinates give an explicit equivalence from the kernel to `R^(n-1)`. -/
theorem kernel_basis_of_basis_vector {n : ℕ} (b : Basis (Fin n) R M) (i : Fin n)
    (φ : M →ₗ[R] R) (he : φ (b i) = 1) :
    Nonempty (Basis (Fin (n - 1)) R (LinearMap.ker φ)) := by
  classical
  let J := {j : Fin n // j ≠ i}
  let q : LinearMap.ker φ →ₗ[R] (J → R) :=
    LinearMap.pi (fun j => (b.coord j.val).comp (LinearMap.ker φ).subtype)
  have hq : Function.Bijective q := by
    constructor
    · intro x y hxy
      have hw : (x : M) - y = (b.coord i ((x : M) - y)) • b i := by
        apply b.ext_elem
        intro j
        by_cases hj : j = i
        · subst j
          simp
        · have hh := congrFun hxy (⟨j, hj⟩ : J)
          change b.coord j x = b.coord j y at hh
          simpa [Basis.coord_apply, hj, Ne.symm hj] using sub_eq_zero.mpr hh
      have hc : b.coord i ((x : M) - y) = 0 := by
        have h := congrArg φ hw
        simpa [he, LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property] using h.symm
      apply Subtype.ext
      exact sub_eq_zero.mp (by simpa [hc] using hw)
    · intro c
      let z : M := ∑ j : J, c j • (b j.val - φ (b j.val) • b i)
      have hz : z ∈ LinearMap.ker φ := by
        simp [z, LinearMap.mem_ker, map_sum, map_smul, he]
      refine ⟨⟨z, hz⟩, ?_⟩
      ext j
      change b.coord j.val z = c j
      simp only [z, map_sum, map_smul, Basis.coord_apply, map_sub, b.repr_self,
        Finsupp.single_apply, ite_eq_right (Ne.symm j.property), mul_zero, sub_zero, smul_eq_mul,
        ← Subtype.ext_iff, mul_ite, mul_one]
      exact Fintype.sum_ite_eq' j c
  let bk := Basis.ofEquivFun (LinearEquiv.ofBijective q hq)
  have hcard : Fintype.card J = n - 1 := by
    simp only [J, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  exact ⟨bk.reindex ((Fintype.equivFin J).trans (finCongr hcard))⟩
/-- The primitive section extends to a basis; deleting it gives the kernel basis. -/
theorem kernel_basis [IsDomain R] [IsPrincipalIdealRing R] {n : ℕ} (b : Basis (Fin n) R M)
    {φ : M →ₗ[R] R} {e : M} (he : φ e = 1) :
    Nonempty (Basis (Fin (n - 1)) R (LinearMap.ker φ)) := by
  classical
  have hp : Ideal.span (Set.range (b.equivFun e)) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    have hsum : φ e = ∑ i, b.repr e i * φ (b i) := by
      conv_lhs => rw [← b.sum_repr e]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [← he, hsum]
    apply Submodule.sum_mem
    intro i _
    apply Ideal.mul_mem_right
    exact Ideal.subset_span ⟨i, rfl⟩
  obtain ⟨bc, i, hi⟩ := D07.Ch16.PidPrimitiveBasis.primitiveExtendsToBasis R n (b.equivFun e) hp
  let b' := bc.map b.equivFun.symm
  have hbi : b' i = e := by simp [b', hi]
  exact kernel_basis_of_basis_vector b' i φ (hbi ▸ he)
theorem firstDiagonalSummand :
    Specs.D07.Ch16.SubmoduleFreeFirstDiagonalSummand.FirstDiagonalSummand.{u, v} := by
  intro R _ _ _ M _ _ n b _hn N hN
  classical
  let S : Set (Ideal R) := Set.range (fun ψ : M →ₗ[R] R => N.map ψ)
  have hpid : Specs.D07.Ch10.PidDefinition.pidPredicateValue R :=
    ⟨inferInstance, fun I => Submodule.IsPrincipal.principal I⟩
  obtain ⟨I, hI, hmaxI⟩ :=
    D07.Ch10.PidAscendingChain.nonempty_collection_has_maximal_member R hpid S
      ⟨N.map 0, 0, rfl⟩
  obtain ⟨φ, rfl⟩ := hI
  have hmax : ∀ ψ : M →ₗ[R] R, N.map φ ≤ N.map ψ → N.map ψ = N.map φ :=
    fun ψ h => hmaxI _ ⟨ψ, rfl⟩ h
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (N.map φ)
  change N.map φ = Ideal.span {a} at ha
  have ha0 : a ≠ 0 := by
    intro hz
    have hφ : N.map φ = ⊥ := by simpa [hz] using ha
    apply hN
    rw [Submodule.eq_bot_iff]
    intro y hy
    apply b.ext_elem
    intro i
    have hi : N.map (b.coord i) = ⊥ := by
      rw [← hφ]
      exact hmax _ (hφ ▸ bot_le)
    have hiy : b.coord i y ∈ N.map (b.coord i) := ⟨y, hy, rfl⟩
    simpa [hi] using hiy
  obtain ⟨y, hy, hφy⟩ := (show a ∈ N.map φ by rw [ha]; exact Ideal.mem_span_singleton_self a)
  obtain ⟨e, hae⟩ := exists_smul_of_coord_dvd b a y
    (fun i => maximal_image_dvd ha hmax hy hφy (b.coord i))
  have he : φ e = 1 := by
    apply mul_left_cancel₀ ha0
    simpa [map_smul] using (congrArg φ hae).trans hφy
  have hay : a • e ∈ N := hae ▸ hy
  have hsplit := span_isCompl_ker he
  have hdisj : Disjoint (span R {a • e}) (N ⊓ LinearMap.ker φ) := by
    apply hsplit.disjoint.mono _ inf_le_right
    exact span_le.mpr (Set.singleton_subset_iff.mpr (smul_mem _ a (mem_span_singleton_self e)))
  have hsup : span R {a • e} ⊔ (N ⊓ LinearMap.ker φ) = N := by
    apply le_antisymm
    · exact sup_le (span_le.mpr (Set.singleton_subset_iff.mpr hay)) inf_le_left
    · intro x hx
      have hxφ : a ∣ φ x := Ideal.mem_span_singleton.mp (ha ▸ (show φ x ∈ N.map φ from ⟨x, hx, rfl⟩))
      obtain ⟨c, hc⟩ := hxφ
      have hcy : c • (a • e) ∈ span R {a • e} := mem_span_singleton.mpr ⟨c, rfl⟩
      have hxk : x - c • (a • e) ∈ N ⊓ LinearMap.ker φ := by
        refine ⟨N.sub_mem hx (N.smul_mem c hay), ?_⟩
        simp [LinearMap.mem_ker, map_smul, he, hc, mul_comm]
      exact Submodule.mem_sup.mpr ⟨_, hcy, _, hxk, add_sub_cancel _ _⟩
  have hdiv : N ⊓ LinearMap.ker φ ≤ a • LinearMap.ker φ := by
    intro x hx
    have hdvd : ∀ ψ : M →ₗ[R] R, a ∣ ψ x := by
      intro ψ
      let η : M →ₗ[R] R := ψ - (ψ e) • φ
      have hη : η e = 0 := by simp [η, he]
      have hyη : (φ + η) y = a := by simp [← hae, hη, he, map_smul]
      have himg : N.map (φ + η) = N.map φ := by
        apply hmax
        rw [ha]
        exact (Ideal.span_singleton_le_iff_mem _).mpr ⟨y, hy, hyη⟩
      have hxη : (φ + η) x ∈ Ideal.span {a} := by
        rw [← ha, ← himg]
        exact ⟨x, hx.1, rfl⟩
      have hxφ := LinearMap.mem_ker.mp hx.2
      simpa [η, hxφ] using Ideal.mem_span_singleton.mp hxη
    obtain ⟨z, hz⟩ := exists_smul_of_coord_dvd b a x (fun i => hdvd (b.coord i))
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    refine ⟨z, ?_, hz⟩
    apply LinearMap.mem_ker.mpr
    have hzero : a * φ z = 0 := by simpa [map_smul] using (congrArg φ hz).trans (LinearMap.mem_ker.mp hx.2)
    exact (mul_eq_zero.mp hzero).resolve_left ha0
  exact ⟨a, φ, e, ha0, he, hay, ha, hsplit, hdisj, hsup, hdiv, kernel_basis b he⟩

end D07.Ch16.SubmoduleFreeFirstDiagonalSummand
