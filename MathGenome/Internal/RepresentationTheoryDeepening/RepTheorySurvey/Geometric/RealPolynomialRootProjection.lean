import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.RealPolynomialRootProjection
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Polynomial.Resultant.Basic

namespace RepTheorySurvey.Geometric

open Polynomial
open scoped Matrix Polynomial

private theorem exists_rank_columns {K m n : Type*} [Field K] [Fintype n]
    (A : Matrix m n K) :
    ∃ c : Fin A.rank → n, (A.submatrix id c).rank = A.rank := by
  classical
  obtain ⟨ι, c, hc, hspan, hind⟩ := exists_linearIndependent' K A.col
  let : Fintype ι := Fintype.ofInjective c hc
  have hcard : Fintype.card ι = A.rank := by
    rw [Matrix.rank_eq_finrank_span_cols, ← hspan, ← Module.finrank_eq_card_basis (Module.Basis.span hind)]
  let e : ι ≃ Fin A.rank := Fintype.equivFinOfCardEq hcard
  refine ⟨c ∘ e.symm, ?_⟩
  have hrange : Set.range (A.submatrix id (c ∘ e.symm)).col = Set.range (A.col ∘ c) :=
    e.symm.surjective.range_comp (A.col ∘ c)
  rw [Matrix.rank_eq_finrank_span_cols, hrange, hspan, ← Matrix.rank_eq_finrank_span_cols]

private theorem exists_rank_minor {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    (A : Matrix m n K) :
    ∃ (r : Fin A.rank → m) (c : Fin A.rank → n), (A.submatrix r c).det ≠ 0 := by
  classical
  obtain ⟨c, hc⟩ := exists_rank_columns A
  let B := (A.submatrix id c)ᵀ
  have hB : B.rank = A.rank := (Matrix.rank_transpose _).trans hc
  obtain ⟨r, hr⟩ := exists_rank_columns B
  let r' : Fin A.rank → m := r ∘ (finCongr hB).symm
  have hminor : (A.submatrix r' c).rank = A.rank := by
    have htranspose :
        (A.submatrix r' c)ᵀ = (B.submatrix id r).submatrix (Equiv.refl _) (finCongr hB).symm := by
      ext i j
      rfl
    rw [← Matrix.rank_transpose, htranspose, Matrix.rank_submatrix, hr, hB]
  have hs : (A.submatrix r' c).mulVec.Surjective :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr (hminor.trans (Fintype.card_fin _).symm)
  exact ⟨r', c, ((A.submatrix r' c).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hs)).ne_zero⟩

/-- For a polynomial of positive degree over an algebraically closed field of characteristic
zero, removing the gcd with its derivative leaves one copy of every distinct root. -/
private theorem rootSet_ncard_add_gcd_degree {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    [DecidableEq K[X]] (p : K[X]) (hp : p.natDegree ≠ 0) :
    (p.rootSet K).ncard + (EuclideanDomain.gcd p p.derivative).natDegree = p.natDegree := by
  classical
  have hp₀ : p ≠ 0 := by rintro rfl; exact hp rfl
  have hd₀ : p.derivative ≠ 0 := derivative_ne_zero.mpr hp
  let g := EuclideanDomain.gcd p p.derivative
  have hg₀ : g ≠ 0 := fun h => hp₀ (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hdiv : g ∣ p := EuclideanDomain.gcd_dvd_left _ _
  have hsub : g.roots.toFinset ⊆ p.roots.toFinset := by
    intro z hz
    simp only [Multiset.mem_toFinset, mem_roots hg₀, mem_roots hp₀] at hz ⊢
    exact dvd_iff_isRoot.mp ((dvd_iff_isRoot.mpr hz).trans hdiv)
  have hmult (z : K) (hz : z ∈ p.roots.toFinset) :
      g.roots.count z + 1 = p.roots.count z := by
    have hz' : p.IsRoot z := (mem_roots hp₀).mp (Multiset.mem_toFinset.mp hz)
    have hder := derivative_rootMultiplicity_of_root hz'
    have hg : g.rootMultiplicity z = min (p.rootMultiplicity z)
        (p.derivative.rootMultiplicity z) := by
      apply eq_of_forall_le_iff
      intro k
      simp only [le_min_iff, le_rootMultiplicity_iff hp₀, le_rootMultiplicity_iff hg₀,
        le_rootMultiplicity_iff hd₀]
      exact ⟨fun h => ⟨h.trans hdiv, h.trans (EuclideanDomain.gcd_dvd_right _ _)⟩,
        fun h => EuclideanDomain.dvd_gcd h.1 h.2⟩
    rw [count_roots, count_roots, hg, hder, min_eq_right (Nat.sub_le ..)]
    exact Nat.sub_add_cancel (rootMultiplicity_pos hp₀ |>.mpr hz')
  change (p.rootSet K).ncard + g.natDegree = p.natDegree
  rw [rootSet_def, aroots_def, Algebra.algebraMap_self, map_id, Set.ncard_coe_finset,
    (IsAlgClosed.splits g).natDegree_eq_card_roots, (IsAlgClosed.splits p).natDegree_eq_card_roots,
    ← Multiset.toFinset_sum_count_eq g.roots, ← Multiset.toFinset_sum_count_eq p.roots]
  rw [Finset.sum_subset hsub (fun z _ hz => Multiset.count_eq_zero_of_notMem
    (fun hz' => hz (Multiset.mem_toFinset.mpr hz')))]
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun z hz => (Nat.add_comm _ _).trans (hmult z hz)

/-- The kernel of the Sylvester map consists of the multiples of the pair of
coprime cofactors, with the multiplier of degree less than the gcd degree. -/
private theorem sylvester_rank_add_gcd_degree {K : Type*} [Field K] [DecidableEq K[X]]
    (f g : K[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f.sylvester g f.natDegree g.natDegree).rank +
        (EuclideanDomain.gcd f g).natDegree = f.natDegree + g.natDegree := by
  classical
  let d := EuclideanDomain.gcd f g
  have hd : d ≠ 0 := fun h => hf (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  let a := f / d
  let b := g / d
  have ha : d * a = f := EuclideanDomain.mul_div_cancel' hd (EuclideanDomain.gcd_dvd_left _ _)
  have hb : d * b = g := EuclideanDomain.mul_div_cancel' hd (EuclideanDomain.gcd_dvd_right _ _)
  have ha₀ : a ≠ 0 := (mul_ne_zero_iff.mp (ha.symm ▸ hf)).2
  have hb₀ : b ≠ 0 := (mul_ne_zero_iff.mp (hb.symm ▸ hg)).2
  have hdeg_a : d.natDegree + a.natDegree = f.natDegree := by
    rw [← natDegree_mul hd ha₀, ha]
  have hdeg_b : d.natDegree + b.natDegree = g.natDegree := by
    rw [← natDegree_mul hd hb₀, hb]
  let L := sylvesterMap f g le_rfl le_rfl
  have mul_mem {u : K[X]} {n : ℕ} (hu : u ≠ 0)
      (hdeg : d.natDegree + u.natDegree = n) (r : K[X]_d.natDegree) :
      u * r.val ∈ degreeLT K n := by
    rw [mem_degreeLT]
    by_cases hr : r.val = 0
    · simp [hr]
    have hrdeg := (natDegree_lt_iff_degree_lt hr).2 (mem_degreeLT.mp r.property)
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero hu hr)).1
    rw [natDegree_mul hu hr]
    omega
  let T : K[X]_d.natDegree →ₗ[K] L.ker :=
    { toFun := fun r =>
        ⟨(⟨a * r.val, mul_mem ha₀ hdeg_a r⟩,
          ⟨-(b * r.val), by simpa only [mem_degreeLT, degree_neg] using mul_mem hb₀ hdeg_b r⟩),
          by
            apply LinearMap.mem_ker.mpr
            apply Subtype.ext
            change f * -(b * r.val) + g * (a * r.val) = 0
            rw [← ha, ← hb]
            ring⟩
      map_add' := by
        intro r s
        apply Subtype.ext
        apply Prod.ext <;> apply Subtype.ext
        · change a * (r.val + s.val) = a * r.val + a * s.val
          ring
        · change -(b * (r.val + s.val)) = -(b * r.val) + -(b * s.val)
          ring
      map_smul' := by
        intro k r
        apply Subtype.ext
        apply Prod.ext <;> apply Subtype.ext
        · change a * (k • r.val) = k • (a * r.val)
          rw [smul_eq_C_mul, smul_eq_C_mul]
          ring
        · change -(b * (k • r.val)) = k • -(b * r.val)
          rw [smul_eq_C_mul, smul_eq_C_mul]
          ring }
  have hTinj : Function.Injective T := by
    intro r s hrs
    apply Subtype.ext
    exact mul_left_cancel₀ ha₀ (congrArg (fun z : L.ker => z.val.1.val) hrs)
  have hTsurj : Function.Surjective T := by
    intro z
    let p := z.val.1.val
    let q := z.val.2.val
    have hpq : a * q + b * p = 0 := by
      have hz := congrArg Subtype.val (LinearMap.mem_ker.mp z.property)
      change f * q + g * p = 0 at hz
      rw [← ha, ← hb, mul_assoc, mul_assoc, ← mul_add, mul_eq_zero] at hz
      exact hz.resolve_left hd
    let A := EuclideanDomain.gcdA f g
    let B := EuclideanDomain.gcdB f g
    have hBezout : a * A + b * B = 1 := by
      apply mul_left_cancel₀ hd
      rw [mul_one, mul_add, ← mul_assoc, ← mul_assoc, ha, hb]
      exact (EuclideanDomain.gcd_eq_gcd_ab f g).symm
    let r := A * p - B * q
    have hpr : a * r = p := by
      dsimp only [r]
      linear_combination p * hBezout - B * hpq
    have hqr : -(b * r) = q := by
      dsimp only [r]
      linear_combination q * hBezout - A * hpq
    have hr : r ∈ degreeLT K d.natDegree := by
      rw [mem_degreeLT]
      by_cases hr : r = 0
      · simp [hr]
      have hp₀ : p ≠ 0 := hpr ▸ mul_ne_zero ha₀ hr
      have hpdeg := (natDegree_lt_iff_degree_lt hp₀).2 (mem_degreeLT.mp z.val.1.property)
      rw [← hpr, natDegree_mul ha₀ hr] at hpdeg
      exact (natDegree_lt_iff_degree_lt hr).1 (by omega)
    refine ⟨⟨r, hr⟩, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    exacts [hpr, hqr]
  have hker := (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩).finrank_eq
  rw [Module.finrank_eq_card_basis (degreeLT.basis K _), Fintype.card_fin] at hker
  have hrank := L.finrank_range_add_finrank_ker
  rw [← hker, Module.finrank_eq_card_basis
    ((degreeLT.basis K _).prod (degreeLT.basis K _)), Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin] at hrank
  rw [Matrix.rank_eq_finrank_range_toLin _
    (degreeLT.basis K _)
    (((degreeLT.basis K _).prod (degreeLT.basis K _)).reindex finSumFinEquiv),
    ← toMatrix_sylvesterMap' f g le_rfl le_rfl, Matrix.toLin_toMatrix]
  exact hrank

private theorem rank_eq_of_minors {K : Type*} [Field K] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) K)
    (h : ∀ (k : ℕ), k ≤ n → ∀ (r c : Fin k → Fin n),
      (A.submatrix r c).det = 0 ↔ (B.submatrix r c).det = 0) :
    A.rank = B.rank := by
  have le_of_minors (C D : Matrix (Fin n) (Fin n) K)
      (hne : ∀ (k : ℕ), k ≤ n → ∀ (r c : Fin k → Fin n),
        (D.submatrix r c).det = 0 → (C.submatrix r c).det = 0) :
      C.rank ≤ D.rank := by
    obtain ⟨r, c, hC⟩ := exists_rank_minor C
    have hD : (D.submatrix r c).det ≠ 0 :=
      fun hD => hC (hne _ C.rank_le_width r c hD)
    calc
      C.rank = (D.submatrix r c).rank := by
        rw [Matrix.rank_of_det_ne_zero hD, Fintype.card_fin]
      _ ≤ D.rank := Matrix.rank_submatrix_le D r c
  exact le_antisymm (le_of_minors A B fun k hk r c => (h k hk r c).mpr)
    (le_of_minors B A fun k hk r c => (h k hk r c).mp)

/-- Vanishing tests of real coefficient polynomials determine the distinct complex root count. -/
theorem exists_rootCountProjection :
    RealPolynomialRootProjectionSpecs.RealPolynomialRootProjection := by
  classical
  intro σ _ F ⟨c, hc, hlead⟩
  by_cases hconst : F.natDegree = 0
  · refine ⟨∅, fun x y _ => ?_⟩
    rw [eq_C_of_natDegree_eq_zero hconst]
    simp
  let d := F.natDegree
  let e := d - 1
  let n := d + e
  let A := F.sylvester F.derivative d e
  let I := Σ k : Fin (n + 1), (Fin k.val → Fin n) × (Fin k.val → Fin n)
  let minor : I → MvPolynomial σ ℝ := fun ⟨_, r, s⟩ => (A.submatrix r s).det
  refine ⟨Finset.univ.image minor, ?_⟩
  intro x y hzero
  let φ (z : σ → ℝ) := (algebraMap ℝ ℂ).comp (MvPolynomial.eval z)
  let p (z : σ → ℝ) := F.map (φ z)
  let B (z : σ → ℝ) := (φ z).mapMatrix A
  have hφ (z : σ → ℝ) (q : MvPolynomial σ ℝ) :
      φ z q = 0 ↔ MvPolynomial.eval z q = 0 :=
    map_eq_zero_iff _ (algebraMap ℝ ℂ).injective
  have hdeg (z : σ → ℝ) : (p z).natDegree = d := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    rw [hlead]
    intro hz
    exact hc (by simpa only [MvPolynomial.eval_C] using (hφ z _).mp hz)
  have hder (z : σ → ℝ) : (p z).derivative.natDegree = e := by
    rw [natDegree_derivative, hdeg]
  have hB (z : σ → ℝ) : B z = (p z).sylvester (p z).derivative d e := by
    exact (sylvester_map_map F F.derivative d e (φ z)).symm.trans
      (by rw [derivative_map])
  have hrank : (B x).rank = (B y).rank := by
    apply rank_eq_of_minors
    intro k hk r s
    let i : I := ⟨⟨k, Nat.lt_succ_of_le hk⟩, r, s⟩
    have hi : minor i ∈ Finset.univ.image minor := Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have hdet (z : σ → ℝ) : φ z (minor i) = ((B z).submatrix r s).det := by
      change φ z ((A.submatrix r s).det) = _
      rw [RingHom.map_det]
      rfl
    rw [← hdet x, ← hdet y, hφ, hφ]
    exact hzero _ hi
  have hrank_gcd (z : σ → ℝ) :
      (B z).rank + (EuclideanDomain.gcd (p z) (p z).derivative).natDegree = n := by
    have hp : (p z).natDegree ≠ 0 := (hdeg z).trans_ne hconst
    have hp₀ : p z ≠ 0 := fun hz => hp (by simp [hz])
    have hsize := congrArg₂ (fun m l => ((p z).sylvester (p z).derivative m l).rank)
      (hdeg z) (hder z)
    have h := sylvester_rank_add_gcd_degree (p z) (p z).derivative hp₀ (derivative_ne_zero.mpr hp)
    rw [hsize, ← hB z, hdeg z, hder z] at h
    exact h
  have hroot_gcd (z : σ → ℝ) :
      ((p z).rootSet ℂ).ncard + (EuclideanDomain.gcd (p z) (p z).derivative).natDegree = d := by
    have hp : (p z).natDegree ≠ 0 := (hdeg z).trans_ne hconst
    simpa only [hdeg] using rootSet_ncard_add_gcd_degree (p z) hp
  have hroots (z : σ → ℝ) : (p z).rootSet ℂ = (F.map (MvPolynomial.eval z)).rootSet ℂ := by
    dsimp only [p, φ]
    rw [← Polynomial.map_map, Polynomial.rootSet_map]
  rw [← hroots x, ← hroots y]
  have hx := hrank_gcd x
  have hy := hrank_gcd y
  have hx' := hroot_gcd x
  have hy' := hroot_gcd y
  omega

end RepTheorySurvey.Geometric
