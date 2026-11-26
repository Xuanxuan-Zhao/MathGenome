import Specs.LinearAlgebraicGroups.Arithmetic.LocalCubicForms
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.Pi
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Data.Fintype.Pigeonhole

noncomputable section

open scoped Polynomial WithZero NNReal

namespace LinearAlgebraicGroups.Arithmetic
namespace LocalCubicForms

private abbrev Trilinear (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  V →ₗ[F] V →ₗ[F] V →ₗ[F] F

private lemma cubic_monomial_indices {ι : Type*} (d : ι →₀ ℕ) (hd : d.degree = 3) :
    ∃ i j k, ∀ {R : Type*} [CommMonoid R] (x : ι → R),
      d.prod (fun i n => x i ^ n) = x i * x j * x k := by
  classical
  obtain ⟨i, j, k, he⟩ := Multiset.card_eq_three.mp
    (show d.toMultiset.card = 3 by rwa [Finsupp.card_toMultiset])
  refine ⟨i, j, k, ?_⟩
  intro R _ x
  have hd' : d = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 := by
    apply (Finsupp.orderIsoMultiset (ι := ι)).injective
    change d.toMultiset = _
    simp [he, Finsupp.toMultiset_add, Finsupp.toMultiset_single, add_assoc,
      Multiset.singleton_add, Multiset.cons_swap]
  rw [hd']
  simp [Finsupp.prod_add_index, pow_add]

/-- A homogeneous cubic is the diagonal of a trilinear map in any characteristic.
The map is constructed monomial by monomial, without dividing by factorials. -/
private lemma exists_trilinear {F ι : Type*} [Field F] (p : MvPolynomial ι F)
    (hp : p.IsHomogeneous 3) :
    ∃ T : Trilinear F (ι → F), ∀ x, T x x x = MvPolynomial.eval x p := by
  classical
  have h (d : p.support) := cubic_monomial_indices d.val (by rw [Finsupp.degree_apply, ← hp.degree_eq_sum_deg_support d.property])
  choose i j k hk using h
  let term (d : p.support) : Trilinear F (ι → F) :=
    p.coeff d • (LinearMap.proj (i d)).smulRight
      ((LinearMap.proj (j d)).smulRight (LinearMap.proj (k d)))
  refine ⟨∑ d : p.support, term d, fun x => ?_⟩
  simp only [LinearMap.sum_apply, term, LinearMap.smul_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, smul_eq_mul, MvPolynomial.eval_eq, ← Finset.sum_attach p.support]
  apply Finset.sum_congr rfl
  intro d _
  change _ = p.coeff d * d.val.prod (fun i n => x i ^ n)
  rw [hk d]
  ring

section Trilinear

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable (T : Trilinear F V)

private def diagonal (x : V) : F := T x x x

private def mixed (x y : V) : F := T x x y + T x y x + T y x x

private lemma diagonal_add (x y : V) :
    diagonal T (x + y) = diagonal T x + mixed T x y + mixed T y x + diagonal T y := by
  simp only [diagonal, mixed, map_add, LinearMap.add_apply]
  abel

private lemma diagonal_smul (a : F) (x : V) :
    diagonal T (a • x) = a ^ 3 * diagonal T x := by
  simp only [diagonal, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma mixed_smul_left (a : F) (x y : V) :
    mixed T (a • x) y = a ^ 2 * mixed T x y := by
  simp only [mixed, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma mixed_smul_right (a : F) (x y : V) :
    mixed T x (a • y) = a * mixed T x y := by
  simp only [mixed, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma diagonal_zero : diagonal T 0 = 0 := by simp [diagonal]

end Trilinear

section Norm

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

open Polynomial in
/-- Coefficient bounds for an irreducible monic cubic over the complete base. -/
private lemma irreducible_cubic_coeff_le {p : F[X]} (hm : p.Monic) (hp : Irreducible p)
    (hd : p.natDegree = 3) {i : ℕ} (hi : i < 3) :
    ‖p.coeff i‖ ≤ ‖p.coeff 0‖ ^ ((3 - (i : ℝ)) / 3) := by
  let E := AlgebraicClosure F
  have hdeg : (p.map (algebraMap F E)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (algebraMap F E).injective, degree_eq_natDegree hm.ne_zero, hd]
    norm_num
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (p.map (algebraMap F E)) hdeg
  have hx' : aeval x p = 0 := by simpa [IsRoot, eval_map_algebraMap] using hx
  have hmin : p = minpoly F x := minpoly.eq_of_irreducible_of_monic hp hx' hm
  have hle := le_ciSup (spectralValueTerms_bddAbove p) i
  change spectralValueTerms p i ≤ spectralValue p at hle
  have hsp : spectralValue p = ‖p.coeff 0‖ ^ (1 / (3 : ℝ)) := by
    calc
      spectralValue p = spectralNorm F E x := by rw [hmin]; rfl
      _ = ‖p.coeff 0‖ ^ (1 / (3 : ℝ)) := by
        rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, ← hmin, hd]
        norm_num
  rw [spectralValueTerms_of_lt_natDegree p (hd ▸ hi), hsp, hd] at hle
  norm_num at hle
  have hs : 0 < (3 : ℝ) - i := by exact sub_pos.mpr (by exact_mod_cast hi)
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hle hs.le
  rw [← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _),
    inv_mul_cancel₀ hs.ne', Real.rpow_one] at hr
  convert hr using 2
  ring

variable {V : Type*} [AddCommGroup V] [Module F V] (T : Trilinear F V)

open Polynomial in
private lemma mixed_norm_cube_le
    (ha : ∀ x : V, diagonal T x = 0 → x = 0) (x y : V) :
    ‖mixed T x y‖ ^ 3 ≤ ‖diagonal T x‖ ^ 2 * ‖diagonal T y‖ := by
  by_cases hx : x = 0
  · subst x
    simp [mixed, diagonal]
  have hfx : diagonal T x ≠ 0 := fun h => hx (ha _ h)
  by_cases hind : ∀ a : F, a • x + y ≠ 0
  · let p : F[X] := X ^ 3 + C (mixed T x y / diagonal T x) * X ^ 2 +
        C (mixed T y x / diagonal T x) * X + C (diagonal T y / diagonal T x)
    have hcoeff (i : ℕ) (hi : 3 < i) : p.coeff i = 0 := by
      simp only [p, coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow, coeff_C,
        show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
        show i ≠ 3 by omega,
        ite_false, add_zero]
    have h3 : p.coeff 3 = 1 := by norm_num [p, coeff_C_mul_X_pow, coeff_X_pow, coeff_C]
    have hd : p.natDegree = 3 :=
      le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr hcoeff)
        (le_natDegree_of_ne_zero (by rw [h3]; exact one_ne_zero))
    have hm : p.Monic := by rw [Monic, leadingCoeff, hd, h3]
    have he (a : F) : p.eval a = diagonal T (a • x + y) / diagonal T x := by
      simp only [p, eval_add, eval_mul, eval_pow, eval_X, eval_C, diagonal_add,
        diagonal_smul, mixed_smul_left, mixed_smul_right]
      field_simp
    have hi : Irreducible p := by
      apply (hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr
      apply Multiset.eq_zero_iff_forall_notMem.mpr
      intro a h
      have he' := (mem_roots hm.ne_zero).mp h
      rw [IsRoot, he, div_eq_zero_iff] at he'
      exact hind a (ha _ (he'.resolve_right hfx))
    have hbound := irreducible_cubic_coeff_le hm hi hd (i := 2) (by decide)
    have h2 : p.coeff 2 = mixed T x y / diagonal T x := by
      norm_num [p, coeff_C_mul_X_pow, coeff_X_pow, coeff_C]
    have h0 : p.coeff 0 = diagonal T y / diagonal T x := by
      norm_num [p, coeff_C_mul_X_pow, coeff_X_pow, coeff_C]
    rw [h2, h0, norm_div, norm_div] at hbound
    norm_num at hbound
    have hcube := pow_le_pow_left₀ (by positivity) hbound 3
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ ‖diagonal T y‖ / ‖diagonal T x‖)]
      at hcube
    norm_num at hcube
    have hxpos := norm_pos_iff.mpr hfx
    rw [div_pow, div_le_iff₀ (pow_pos hxpos 3)] at hcube
    convert hcube using 1
    field_simp
  · obtain ⟨a, ha'⟩ := not_forall.mp hind
    have ha' := not_ne_iff.mp ha'
    have hy : y = (-a) • x := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact ha'
    rw [hy, mixed_smul_right, diagonal_smul]
    have hsame : mixed T x x = (3 : F) * diagonal T x := by
      unfold mixed diagonal
      ring
    rw [hsame, norm_mul, norm_mul, norm_mul, norm_pow]
    have hthree : ‖(3 : F)‖ ≤ 1 := by
      simpa using IsUltrametricDist.norm_natCast_le_one F 3
    calc
      (‖-a‖ * (‖(3 : F)‖ * ‖diagonal T x‖)) ^ 3 ≤
          (‖-a‖ * ‖diagonal T x‖) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by
          gcongr
          exact mul_le_of_le_one_left (norm_nonneg _) hthree) 3
      _ = _ := by ring

private lemma mixed_norm_le
    (ha : ∀ x : V, diagonal T x = 0 → x = 0) {r : ℝ} {x y : V}
    (hx : ‖diagonal T x‖ ≤ r) (hy : ‖diagonal T y‖ ≤ r) :
    ‖mixed T x y‖ ≤ r := by
  apply le_of_pow_le_pow_left₀ (n := 3) (by omega) ((norm_nonneg _).trans hx)
  calc
    ‖mixed T x y‖ ^ 3 ≤ ‖diagonal T x‖ ^ 2 * ‖diagonal T y‖ :=
      mixed_norm_cube_le T ha x y
    _ ≤ r ^ 2 * r := by gcongr
    _ = r ^ 3 := by ring

private lemma diagonal_norm_add_le
    (ha : ∀ x : V, diagonal T x = 0 → x = 0) (x y : V) :
    ‖diagonal T (x + y)‖ ≤ max ‖diagonal T x‖ ‖diagonal T y‖ := by
  let r := max ‖diagonal T x‖ ‖diagonal T y‖
  have hx : ‖diagonal T x‖ ≤ r := le_max_left _ _
  have hy : ‖diagonal T y‖ ≤ r := le_max_right _ _
  rw [diagonal_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans <| max_le
    ((IsUltrametricDist.norm_add_le_max _ _).trans <| max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans <| max_le hx (mixed_norm_le T ha hx hy))
      (mixed_norm_le T ha hy hx)) hy

omit [IsUltrametricDist F] [CompleteSpace F] in
private lemma diagonal_norm_neg (x : V) : ‖diagonal T (-x)‖ = ‖diagonal T x‖ := by
  rw [← neg_one_smul F x, diagonal_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]

omit [IsUltrametricDist F] [CompleteSpace F] in
/-- If the coordinate space is proper, bounded cubic values give a compact
set of vectors, by minimizing the norm of the form on the unit sphere. -/
private lemma isCompact_diagonal_norm_le {ι : Type*} [Fintype ι] [Nonempty ι]
    [ProperSpace F] (T : Trilinear F (ι → F))
    (ha : ∀ x, diagonal T x = 0 → x = 0) (hc : Continuous (diagonal T)) (r : ℝ) :
    IsCompact {x | ‖diagonal T x‖ ≤ r} := by
  let S := Metric.sphere (0 : ι → F) 1
  have hSne : S.Nonempty := ⟨fun _ => 1, by simp [S]⟩
  obtain ⟨z, hz, hzmin⟩ := (isCompact_sphere (0 : ι → F) 1).exists_isMinOn hSne
    hc.norm.continuousOn
  have hz1 : ‖z‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hz
  have hzpos : 0 < ‖diagonal T z‖ := by
    apply norm_pos_iff.mpr
    intro he
    simp [ha _ he] at hz1
  refine (isCompact_closedBall (0 : ι → F) (max 1 (r / ‖diagonal T z‖))).of_isClosed_subset
    (isClosed_le hc.norm continuous_const) ?_
  intro x hx
  change ‖diagonal T x‖ ≤ r at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hsmall : ‖x‖ ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hlarge : 1 < ‖x‖ := lt_of_not_ge hsmall
  obtain ⟨i, -, hi⟩ :=
    Finset.univ.exists_mem_eq_sup Finset.univ_nonempty (fun i => ‖x i‖₊)
  have hi' : ‖x i‖ = ‖x‖ := by
    rw [Pi.norm_def, hi]
    rfl
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hi'.symm ▸ (zero_lt_one.trans hlarge))
  let y := (x i)⁻¹ • x
  have hy : y ∈ S := by
    simp [S, y, norm_smul, norm_inv, ← hi', hxi]
  have hzle : ‖diagonal T z‖ ≤ ‖diagonal T y‖ := hzmin hy
  have hscale : x i • y = x := by simp [y, smul_smul, hxi]
  have he : ‖diagonal T x‖ = ‖x‖ ^ 3 * ‖diagonal T y‖ := by
    rw [← hi']
    conv_lhs => rw [← hscale]
    rw [diagonal_smul, norm_mul, norm_pow]
  have hpow : ‖x‖ ≤ ‖x‖ ^ 3 := le_self_pow₀ hlarge.le (by decide)
  have : ‖x‖ * ‖diagonal T z‖ ≤ r := by
    rw [he] at hx
    exact (mul_le_mul hpow hzle hzpos.le (by positivity)).trans hx
  exact ((le_div_iff₀ hzpos).2 this).trans (le_max_right _ _)

omit [IsUltrametricDist F] [CompleteSpace F] in
private lemma exists_minimal_diagonal_representative (T : Trilinear F V)
    [TopologicalSpace V] [IsTopologicalAddGroup V] (hc : Continuous (diagonal T))
    (hcompact : ∀ r, IsCompact {x | ‖diagonal T x‖ ≤ r})
    (W : Submodule F V) (hclosed : IsClosed (W : Set V)) (x : V) :
    ∃ y : V, y - x ∈ W ∧ ∀ w ∈ W, ‖diagonal T y‖ ≤ ‖diagonal T (y + w)‖ := by
  let S := {y : V | ‖diagonal T y‖ ≤ ‖diagonal T x‖} ∩ {y | y - x ∈ W}
  have hs : IsCompact S := (hcompact _).inter_right
    (hclosed.preimage (continuous_id.sub continuous_const))
  have hx : x ∈ S := ⟨show ‖diagonal T x‖ ≤ ‖diagonal T x‖ from le_rfl, by simp⟩
  obtain ⟨y, hy, hymin⟩ := hs.exists_isMinOn ⟨x, hx⟩ hc.norm.continuousOn
  refine ⟨y, hy.2, fun w hw => ?_⟩
  by_cases hw' : ‖diagonal T (y + w)‖ ≤ ‖diagonal T x‖
  · apply hymin
    refine ⟨hw', ?_⟩
    change y + w - x ∈ W
    rw [add_comm y w, add_sub_assoc]
    exact W.add_mem hw hy.2
  · exact hy.1.trans (le_of_not_ge hw')

private lemma diagonal_norm_add_of_minimal
    (ha : ∀ x : V, diagonal T x = 0 → x = 0) (W : Submodule F V) (v : V)
    (hmin : ∀ w ∈ W, ‖diagonal T v‖ ≤ ‖diagonal T (v + w)‖)
    (a : F) (w : V) (hw : w ∈ W) :
    ‖diagonal T (a • v + w)‖ = max ‖diagonal T (a • v)‖ ‖diagonal T w‖ := by
  by_cases ha0 : a = 0
  · simp [ha0, diagonal_zero, norm_nonneg]
  have hsc : a • (v + a⁻¹ • w) = a • v + w := by
    simp [smul_add, smul_smul, ha0]
  have h₁ : ‖diagonal T (a • v)‖ ≤ ‖diagonal T (a • v + w)‖ := by
    rw [← hsc, diagonal_smul, diagonal_smul, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hmin _ (W.smul_mem a⁻¹ hw)) (norm_nonneg _)
  have h₂ : ‖diagonal T w‖ ≤ ‖diagonal T (a • v + w)‖ := by
    have h := diagonal_norm_add_le T ha (a • v + w) (-(a • v))
    rwa [show a • v + w + -(a • v) = w by abel, diagonal_norm_neg, max_eq_left h₁] at h
  exact le_antisymm (diagonal_norm_add_le T ha _ _) (max_le h₁ h₂)

private def initialSubspace {n : ℕ} (i : Fin n) : Submodule F (Fin n → F) where
  carrier := {x | ∀ j : Fin n, i ≤ j → x j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb j hj
    change a j + b j = 0
    rw [ha j hj, hb j hj, add_zero]
  smul_mem' := by
    intro c a ha j hj
    change c * a j = 0
    rw [ha j hj, mul_zero]

/-- Choose representatives of the successive coordinate cosets minimizing the
cubic norm. They form a basis for which the norm of a sum is the maximum of
the norms of its terms. The equivalence below expresses this for any bound. -/
private lemma exists_orthogonal_family {n : ℕ} [Nonempty (Fin n)] [ProperSpace F]
    (T : Trilinear F (Fin n → F)) (ha : ∀ x, diagonal T x = 0 → x = 0)
    (hc : Continuous (diagonal T)) :
    ∃ v : Fin n → (Fin n → F), (∀ i, v i ≠ 0) ∧
      ∀ (s : Finset (Fin n)) (a : Fin n → F) (r : ℝ), 0 ≤ r →
        (‖diagonal T (∑ i ∈ s, a i • v i)‖ ≤ r ↔
          ∀ i ∈ s, ‖diagonal T (a i • v i)‖ ≤ r) := by
  classical
  let W := initialSubspace (F := F) (n := n)
  let e (i : Fin n) : Fin n → F := Pi.single i 1
  have hclosed (i : Fin n) : IsClosed (W i : Set (Fin n → F)) :=
    (W i).closed_of_finiteDimensional
  have h i := exists_minimal_diagonal_representative T hc
    (isCompact_diagonal_norm_le T ha hc) (W i) (hclosed i) (e i)
  choose v hv hmin using h
  have hdiag (i : Fin n) : v i i = 1 := by
    have he : (v i - e i) i = 0 := hv i i le_rfl
    simpa [e, sub_eq_zero] using he
  refine ⟨v, fun i hzero => ?_, ?_⟩
  · simpa [hzero] using hdiag i
  · intro s a r hr
    induction s using Finset.induction_on_max with
    | empty => simp [diagonal_zero, hr]
    | insert i s his ih =>
      have hin : i ∉ s := fun hi => (his _ hi).false
      have hmem : ∑ j ∈ s, a j • v j ∈ W i := by
        apply Submodule.sum_mem
        intro j hj
        apply (W i).smul_mem
        intro k hk
        have he : (v j - e j) k = 0 := hv j k ((his j hj).le.trans hk)
        have hjk : j ≠ k := ((his j hj).trans_le hk).ne
        simpa [e, hjk.symm] using he
      rw [Finset.sum_insert hin, diagonal_norm_add_of_minimal T ha (W i) _ (hmin i) _ _ hmem,
        max_le_iff, ih, Finset.forall_mem_insert]

end Norm

section FourVariables

private def symmetricMixed {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Trilinear F V) (x y z : V) : F :=
  T x y z + T x z y + T y x z + T y z x + T z x y + T z y x

private lemma symmetricMixed_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Trilinear F V) (x y z : V) :
    symmetricMixed T x y z = diagonal T (x + y + z) - diagonal T (x + y) -
      diagonal T (x + z) - diagonal T (y + z) + diagonal T x + diagonal T y +
      diagonal T z := by
  simp only [symmetricMixed, diagonal, map_add, LinearMap.add_apply]
  abel

private lemma symmetricMixed_norm_le {F V : Type*} [NontriviallyNormedField F]
    [IsUltrametricDist F] [CompleteSpace F] [AddCommGroup V] [Module F V]
    (T : Trilinear F V) (ha : ∀ x, diagonal T x = 0 → x = 0) {r : ℝ} {x y z : V}
    (hx : ‖diagonal T x‖ ≤ r) (hy : ‖diagonal T y‖ ≤ r) (hz : ‖diagonal T z‖ ≤ r) :
    ‖symmetricMixed T x y z‖ ≤ r := by
  have hadd {a b : F} (h₁ : ‖a‖ ≤ r) (h₂ : ‖b‖ ≤ r) : ‖a + b‖ ≤ r :=
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le h₁ h₂)
  have hsub {a b : F} (h₁ : ‖a‖ ≤ r) (h₂ : ‖b‖ ≤ r) : ‖a - b‖ ≤ r := by
    simpa only [sub_eq_add_neg] using hadd h₁ (b := -b) (by rwa [norm_neg])
  have hdiag {u w : V} (h₁ : ‖diagonal T u‖ ≤ r) (h₂ : ‖diagonal T w‖ ≤ r) :
      ‖diagonal T (u + w)‖ ≤ r := (diagonal_norm_add_le T ha u w).trans (max_le h₁ h₂)
  rw [symmetricMixed_eq]
  exact hadd (hadd (hadd
    (hsub (hsub (hsub (hdiag (hdiag hx hy) hz) (hdiag hx hy)) (hdiag hx hz)) (hdiag hy hz))
    hx) hy) hz

/-- The cubic expansion in four variables, grouped by the multiplicities of
the variable indices. -/
private def cubicExpression {R : Type*} [CommRing R] (d : Fin 4 → R)
    (m : Fin 4 → Fin 4 → R) (t : Fin 4 → Fin 4 → Fin 4 → R) (x : Fin 4 → R) : R :=
  (∑ i, d i * x i ^ 3) +
  (∑ i, ∑ j, if i = j then 0 else m i j * x i ^ 2 * x j) +
  (t 0 1 2 * x 0 * x 1 * x 2 + t 0 1 3 * x 0 * x 1 * x 3 +
   t 0 2 3 * x 0 * x 2 * x 3 + t 1 2 3 * x 1 * x 2 * x 3)

private lemma map_cubicExpression {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (d : Fin 4 → R) (m : Fin 4 → Fin 4 → R) (t : Fin 4 → Fin 4 → Fin 4 → R) (x : Fin 4 → R) :
    f (cubicExpression d m t x) =
      cubicExpression (fun i => f (d i)) (fun i j => f (m i j))
        (fun i j k => f (t i j k)) (fun i => f (x i)) := by
  simp only [cubicExpression, map_add, map_mul, map_pow, map_sum, apply_ite, map_zero]

private lemma diagonal_sum_four {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (T : Trilinear F V) (v : Fin 4 → V) (a : Fin 4 → F) :
    diagonal T (∑ i, a i • v i) =
      cubicExpression (fun i => diagonal T (v i)) (fun i j => mixed T (v i) (v j))
        (fun i j k => symmetricMixed T (v i) (v j) (v k)) a := by
  simp only [cubicExpression, Fin.sum_univ_four, diagonal, mixed, symmetricMixed]
  norm_num
  ring

private def fourVariableCubic {R : Type*} [CommRing R] (d : Fin 4 → R)
    (m : Fin 4 → Fin 4 → R) (t : Fin 4 → Fin 4 → Fin 4 → R) : MvPolynomial (Fin 4) R :=
  cubicExpression (fun i => MvPolynomial.C (d i)) (fun i j => MvPolynomial.C (m i j))
    (fun i j k => MvPolynomial.C (t i j k)) MvPolynomial.X

open MvPolynomial in
private lemma fourVariableCubic_homogeneous {R : Type*} [CommRing R] (d : Fin 4 → R)
    (m : Fin 4 → Fin 4 → R) (t : Fin 4 → Fin 4 → Fin 4 → R) :
    (fourVariableCubic d m t).IsHomogeneous 3 := by
  have triple (c : R) (i j k : Fin 4) :
      (C c * X i * X j * X k : MvPolynomial (Fin 4) R).IsHomogeneous 3 :=
    (((isHomogeneous_C_mul_X c i).mul (isHomogeneous_X R j)).mul (isHomogeneous_X R k))
  unfold fourVariableCubic cubicExpression
  refine .add (.add ?_ ?_) (.add (.add (.add (triple ..) (triple ..)) (triple ..)) (triple ..))
  · exact .sum _ _ _ fun i _ => isHomogeneous_C_mul_X_pow (d i) i 3
  · refine .sum _ _ _ fun i _ => .sum _ _ _ fun j _ => ?_
    split_ifs
    · exact isHomogeneous_zero (Fin 4) R 3
    · exact (isHomogeneous_C_mul_X_pow (m i j) i 2).mul (isHomogeneous_X R j)

private lemma cubicExpression_div {F : Type*} [Field F] (d : Fin 4 → F)
    (m : Fin 4 → Fin 4 → F) (t : Fin 4 → Fin 4 → Fin 4 → F) (x : Fin 4 → F) (c : F) :
    cubicExpression (fun i => d i / c) (fun i j => m i j / c)
      (fun i j k => t i j k / c) x = cubicExpression d m t x / c := by
  norm_num [cubicExpression, Fin.sum_univ_four]
  ring

open MvPolynomial in
private lemma not_finite_field_anisotropic_cubic {k : Type*} [Field k] [Finite k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (ha : ∀ x, eval x p = 0 → x = 0) : False := by
  classical
  let := Fintype.ofFinite k
  have hzero : eval (0 : Fin 4 → k) p = 0 := by
    rw [eval_zero, constantCoeff_eq]
    exact hp.coeff_eq_zero (by simp)
  let : Unique { x : Fin 4 → k // eval x p = 0 } :=
    ⟨⟨⟨0, hzero⟩⟩, fun x => Subtype.ext (ha _ x.property)⟩
  have hd : p.totalDegree < Fintype.card (Fin 4) := by
    simpa using hp.totalDegree_le.trans_lt (show 3 < 4 by decide)
  have h := char_dvd_card_solutions (ringChar k) hd
  rw [Fintype.card_unique, Nat.dvd_one] at h
  exact CharP.ringChar_ne_one h

/-- Four orthogonal vectors of the same cubic norm would give an anisotropic
four-variable cubic over the residue field. -/
private lemma not_four_orthogonal_vectors {F V Γ : Type*}
    [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [AddCommGroup V] [Module F V] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) [Finite (IsLocalRing.ResidueField v.valuationSubring)]
    (hunit : ∀ a : F, ‖a‖ ≤ 1 ↔ v a ≤ 1) (hsmall : ∀ a : F, ‖a‖ < 1 ↔ v a < 1)
    (T : Trilinear F V) (ha : ∀ x, diagonal T x = 0 → x = 0) (u : Fin 4 → V) (c : F)
    (hc : c ≠ 0) (hu : ∀ i, ‖diagonal T (u i)‖ = ‖c‖)
    (horth : ∀ (a : Fin 4 → F) (i : Fin 4),
      ‖diagonal T (a i • u i)‖ ≤ ‖diagonal T (∑ j, a j • u j)‖) : False := by
  classical
  let D := v.valuationSubring
  let res := IsLocalRing.residue D
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let integral (a : F) (h : ‖a‖ ≤ ‖c‖) : D :=
    ⟨a / c, (hunit _).mp (by rwa [norm_div, div_le_one₀ hcpos])⟩
  let d (i : Fin 4) := integral (diagonal T (u i)) (hu i).le
  let m (i j : Fin 4) := integral (mixed T (u i) (u j)) (mixed_norm_le T ha (hu i).le (hu j).le)
  let t (i j k : Fin 4) := integral (symmetricMixed T (u i) (u j) (u k))
    (symmetricMixed_norm_le T ha (hu i).le (hu j).le (hu k).le)
  let P := fourVariableCubic d m t
  let Pbar := MvPolynomial.map res P
  have hp : Pbar.IsHomogeneous 3 :=
    (fourVariableCubic_homogeneous d m t).map res
  refine not_finite_field_anisotropic_cubic Pbar hp fun x hx => ?_
  choose a ha' using fun i => IsLocalRing.residue_surjective (R := D) (x i)
  let s : D := cubicExpression d m t a
  have hs : (s : F) = diagonal T (∑ i, (a i : F) • u i) / c := by
    change D.subtype (cubicExpression d m t a) = _
    rw [map_cubicExpression, diagonal_sum_four]
    exact cubicExpression_div _ _ _ _ _
  have hres : res s = 0 := by
    rw [← MvPolynomial.eval₂_eq_eval_map] at hx
    change MvPolynomial.eval₂Hom res x P = 0 at hx
    have he : MvPolynomial.eval₂Hom res x P = res s := by
      unfold P fourVariableCubic s
      rw [map_cubicExpression, map_cubicExpression]
      simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
      exact congrArg _ (funext fun i => (ha' i).symm)
    exact he.symm.trans hx
  have hsv : ‖(s : F)‖ < 1 := (hsmall _).mpr <|
    v.mem_maximalIdeal_iff.mp ((IsLocalRing.residue_eq_zero_iff s).mp hres)
  rw [hs, norm_div, div_lt_one₀ hcpos] at hsv
  funext i
  have hi := (horth (fun j => (a j : F)) i).trans_lt hsv
  rw [diagonal_smul, norm_mul, norm_pow, hu, mul_lt_iff_lt_one_left hcpos] at hi
  have h' : ‖(a i : F)‖ < 1 := by
    by_contra! h
    exact hi.not_ge (one_le_pow₀ h)
  exact (ha' i).symm.trans <| (IsLocalRing.residue_eq_zero_iff (a i)).mpr <|
    v.mem_maximalIdeal_iff.mpr ((hsmall _).mp h')

end FourVariables

/-- In a family of at least ten nonzero cubic values, four have valuations
in the same class modulo three. Rescaling their vectors makes the four
valuations equal. -/
private lemma exists_four_equal_valuations {F : Type*} [Field F] [ValuativeRel F]
    (e : ValuativeRel.ValueGroupWithZero F ≃*o ℤᵐ⁰)
    {n : ℕ} (hn : 9 < n) (f : Fin n → F) (hf : ∀ i, f i ≠ 0) :
    ∃ j : Fin 4 ↪ Fin n, ∃ a : Fin 4 → F, ∃ c : F, c ≠ 0 ∧
      ∀ i, ValuativeRel.valuation F (a i ^ 3 * f (j i)) = ValuativeRel.valuation F c := by
  classical
  let v := ValuativeRel.valuation F
  let q (i : Fin n) : ℤ := WithZero.log (e (v (f i)))
  have hrem₀ (i : Fin n) : 0 ≤ q i % 3 := Int.emod_nonneg _ (by decide)
  have hrem₃ (i : Fin n) : q i % 3 < 3 := Int.emod_lt_of_pos _ (by decide)
  let cls (i : Fin n) : Fin 3 := ⟨(q i % 3).toNat, by have := hrem₃ i; omega⟩
  have hcard : n = ∑ r : Fin 3, Fintype.card {i // cls i = r} := by
    simpa [Fintype.card_sigma] using
      (Fintype.card_congr (Equiv.sigmaFiberEquiv cls)).symm
  have hr : ∃ r : Fin 3, 4 ≤ Fintype.card {i // cls i = r} := by
    by_contra h
    have hb (r : Fin 3) : Fintype.card {i // cls i = r} < 4 :=
      lt_of_not_ge (fun hr => h ⟨r, hr⟩)
    rw [Fin.sum_univ_three] at hcard
    have := hb 0
    have := hb 1
    have := hb 2
    omega
  obtain ⟨r, hr⟩ := hr
  obtain ⟨j₀⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin 4) (β := {i // cls i = r}) (by simpa using hr)
  let j : Fin 4 ↪ Fin n := j₀.trans (Function.Embedding.subtype _)
  have hval (z : ℤ) : ∃ b : F, e (v b) = WithZero.exp z := by
    obtain ⟨b, hb⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp z))
    exact ⟨b, by rw [hb, e.apply_symm_apply]⟩
  obtain ⟨c, hc⟩ := hval r.val
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  choose a ha using fun i : Fin 4 => hval (-(q (j i) / 3))
  refine ⟨j, a, c, hc0, fun i => e.injective ?_⟩
  have hf' : WithZero.exp (q (j i)) = e (v (f (j i))) :=
    WithZero.exp_log ((map_ne_zero e).mpr ((map_ne_zero v).mpr (hf _)))
  have hj : q (j i) % 3 = (r.val : ℤ) := by
    have hj' := congrArg (fun s : Fin 3 => (s.val : ℤ)) (j₀ i).property
    simpa [cls, j, max_eq_left (hrem₀ (j₀ i).val)] using hj'
  change e (v (a i ^ 3 * f (j i))) = e (v c)
  rw [map_mul, map_mul, map_pow, map_pow, ha, ← hf', hc, ← WithZero.exp_nsmul,
    ← WithZero.exp_add]
  apply congrArg WithZero.exp
  rw [← hj]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  omega

end LocalCubicForms

open LocalCubicForms in
/-- Every homogeneous cubic in more than nine variables over a nonarchimedean
local field has a nonzero zero. -/
theorem localCubic_exists_nonzero_zero
    {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} (p : MvPolynomial (Fin n) F)
    (hp : p.IsHomogeneous 3) (hn : 9 < n) :
    ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x p = 0 := by
  classical
  by_contra h
  obtain ⟨T, hT⟩ := exists_trilinear p hp
  have ha (x : Fin n → F) (hx : diagonal T x = 0) : x = 0 := by
    by_contra hx0
    exact h ⟨x, hx0, (hT x).symm.trans hx⟩
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  have : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let v := ValuativeRel.valuation F
  let hv := (inferInstance : ValuativeRel.IsRankLeOne F).nonempty.some
  let : (Valued.v (R := F)).RankOne :=
    { hom' := hv.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := hv.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValuativeRel.ValueGroupWithZero F)
  let : IsUltrametricDist F := Valued.instIsUltrametricDist F (ValuativeRel.ValueGroupWithZero F)
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hc : Continuous (diagonal T) :=
    (show diagonal T = fun x => MvPolynomial.eval x p from funext hT) ▸ p.continuous_eval
  obtain ⟨b, hb, horth⟩ := exists_orthogonal_family T ha hc
  obtain ⟨j, a, c, hc0, hc'⟩ := exists_four_equal_valuations
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) hn
    (fun i => diagonal T (b i)) (fun i h => hb i (ha _ h))
  let u (i : Fin 4) := a i • b (j i)
  have hu (i : Fin 4) : ‖diagonal T (u i)‖ = ‖c‖ := by
    rw [show diagonal T (u i) = _ from diagonal_smul T (a i) (b (j i))]
    exact le_antisymm (Valued.toNormedField.norm_le_iff.mpr (hc' i).le)
      (Valued.toNormedField.norm_le_iff.mpr (hc' i).ge)
  have : Finite (IsLocalRing.ResidueField v.valuationSubring) :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation F
  refine not_four_orthogonal_vectors v (fun _ => Valued.toNormedField.norm_le_one_iff)
    (fun _ => Valued.toNormedField.norm_lt_one_iff) T ha u c hc0 hu ?_
  intro d i
  let A : Fin n → F := Function.extend j (fun i => d i * a i) (fun _ => 0)
  have hA (k : Fin 4) : A (j k) • b (j k) = d k • u k := by
    rw [show A (j k) = d k * a k from j.injective.extend_apply _ _ k, mul_smul]
  have hs : ∑ k ∈ Finset.univ.map j, A k • b k = ∑ k, d k • u k := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun k _ => hA k)
  have hi : j i ∈ Finset.univ.map j := Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hle := (horth (Finset.univ.map j) A _ (norm_nonneg (diagonal T (∑ k, d k • u k)))).mp
    (by rw [hs]) (j i) hi
  rwa [hA] at hle

/-- The local cubic bound in the coordinates of any basis of a
finite-dimensional vector space. -/
theorem cubicForm_exists_nonzero_zero
    {F V : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (p : MvPolynomial (Fin (Module.finrank F V)) F) (hp : p.IsHomogeneous 3)
    (hn : 9 < Module.finrank F V) :
    ∃ x : V, x ≠ 0 ∧ MvPolynomial.eval (b.equivFun x) p = 0 := by
  obtain ⟨z, hz, hpz⟩ := localCubic_exists_nonzero_zero p hp hn
  refine ⟨b.equivFun.symm z, ?_, by rwa [b.equivFun.apply_symm_apply]⟩
  exact fun h => hz (b.equivFun.symm.injective (h.trans b.equivFun.symm.map_zero.symm))

end LinearAlgebraicGroups.Arithmetic
