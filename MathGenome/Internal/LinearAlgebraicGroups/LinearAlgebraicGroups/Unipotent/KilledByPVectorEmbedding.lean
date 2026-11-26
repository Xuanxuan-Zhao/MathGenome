import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.KilledByPVectorEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.Algebra.Polynomial.Div
import Mathlib.GroupTheory.NoncommPiCoprod
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

open AlgebraicGeometry CategoryTheory Opposite WithConv
open scoped TensorProduct

universe u

noncomputable section

namespace LinearAlgebraicGroups.Unipotent

open Specs.Unipotent

variable {k : Type u} [Field k]

set_option maxHeartbeats 600000 in
private theorem map_mem_extended {A R ι : Type u} [AddCommGroup A] [Module k A]
    [CommRing R] [Algebra k R] [Finite ι] (D : Matrix ι ι A) (L : A →ₗ[k] R) :
    D.map L ∈ extendMatrixSpan R (coordinateSpan (k := k) D) := by
  classical
  let W := Submodule.span k (Set.range fun ij : ι × ι ↦ D ij.1 ij.2)
  have hfin : Module.Finite k W := Module.Finite.span_of_finite k (Set.finite_range _)
  let b := Module.finBasis k W
  let entry (i j : ι) : W := ⟨D i j, Submodule.subset_span ⟨(i, j), rfl⟩⟩
  let proj := W.subtype.leftInverse
  let c (a : Fin (Module.finrank k W)) : Module.Dual k A := (b.coord a).comp proj
  have hc (a : Fin (Module.finrank k W)) (i j : ι) :
      c a (D i j) = b.repr (entry i j) a := by
    change b.coord a (proj (W.subtype (entry i j))) = _
    rw [LinearMap.leftInverse_apply_of_inj W.ker_subtype]
    rfl
  have hsum : D.map L = ∑ a, L ((b a).val) • (D.map (c a)).map (algebraMap k R) := by
    ext i j
    have h := congrArg (L.comp W.subtype) (b.sum_repr (entry i j))
    simp only [map_sum, map_smul, LinearMap.comp_apply] at h
    rw [Matrix.sum_apply]
    change L (D i j) = ∑ a, L ((b a).val) * algebraMap k R (c a (D i j))
    simp only [Algebra.smul_def] at h
    change (∑ a, (algebraMap k R (b.repr (entry i j) a)) * L ((b a).val)) = L (D i j) at h
    rw [← h]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [hc, mul_comm]
  rw [hsum]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ <|
    Submodule.subset_span ⟨D.map (c a), ⟨c a, rfl⟩, rfl⟩

theorem coordinateEvaluationMem : CoordinateEvaluationMem.{u} := by
  intro k K R ι _ _ _ _ _ _ D f
  exact map_mem_extended D f.toLinearMap

theorem coordinateSpanBaseChange : CoordinateSpanBaseChange.{u} := by
  intro k K A ι _ _ _ _ _ _ D
  let inc : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  change extendMatrixSpan K (coordinateSpan D) = coordinateSpan (k := K) (D.map inc)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    let lK : Module.Dual K (K ⊗[k] A) :=
      (Algebra.TensorProduct.rid k K K).toLinearMap.comp (l.baseChange K)
    refine ⟨lK, ?_⟩
    ext i j
    change lK (1 ⊗ₜ[k] D i j) = algebraMap k K (l (D i j))
    simp [lK, Algebra.smul_def]
  · rintro _ ⟨l, rfl⟩
    exact map_mem_extended D ((l.restrictScalars k).comp inc.toLinearMap)

private theorem zero_of_all_geometric_evaluations {K A : Type u} [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [_root_.IsReduced A]
    (a : A) (h : ∀ f : A →ₐ[K] K, f a = 0) : a = 0 := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K A)
  obtain ⟨z, rfl⟩ := hq a
  let I := RingHom.ker q.toRingHom
  have hz : z ∈ MvPolynomial.vanishingIdeal K (MvPolynomial.zeroLocus K I) := by
    intro x hx
    let g : MvPolynomial (Fin n) K →ₐ[K] K := MvPolynomial.aeval x
    let f : A →ₐ[K] K := q.liftOfSurjective hq g (fun v hv ↦ hx v hv)
    change g z = 0
    rw [← AlgHom.liftOfSurjective_apply q hq g (fun v hv ↦ hx v hv) z]
    exact h f
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hz
  obtain ⟨m, hm⟩ := hz
  have hn : IsNilpotent (q z) := ⟨m, by rw [← map_pow]; exact hm⟩
  exact hn.eq_zero

private theorem eval_matrix_linear {K A ι : Type u} [Field K] [AddCommGroup A] [Module K A]
    [Fintype ι] [DecidableEq ι] (D : Matrix ι ι A)
    (l : Module.Dual K (Matrix ι ι K)) (f : Module.Dual K A) :
    l (D.map f) = f (∑ i, ∑ j, l (Matrix.single i j 1) • D i j) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single (D.map f)]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.map_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have H : Matrix.single i j (f (D i j)) = f (D i j) • Matrix.single i j (1 : K) := by
    ext a b
    simp [Matrix.single, Matrix.smul_apply]
  rw [H, map_smul, smul_eq_mul, mul_comm]

theorem coordinateSpanLinearEquations : CoordinateSpanLinearEquations.{u} := by
  intro k A ι _ _ _ _ _ D v
  constructor
  · rintro ⟨f, rfl⟩ l h
    change l (D.map f) = 0
    rw [eval_matrix_linear, h, map_zero]
  · intro hv
    by_contra h
    let P := coordinateSpan (k := k) D
    obtain ⟨l, hl, hP⟩ := P.exists_dual_map_eq_bot_of_notMem h inferInstance
    let a := ∑ i, ∑ j, l (Matrix.single i j 1) • D i j
    have ha : a = 0 := by
      by_contra hn
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k hn
      have hm : D.map f ∈ P := ⟨f, rfl⟩
      have hzero : l (D.map f) = 0 := by
        have he := Submodule.mem_map_of_mem hm (f := l)
        simpa [hP] using he
      exact hf ((eval_matrix_linear D l f).symm.trans hzero)
    exact hl (hv l ha)

theorem coordinateSpanGeometricPoints : CoordinateSpanGeometricPoints.{u} := by
  intro K A ι _ _ _ _ _ _ _ D
  classical
  let := Fintype.ofFinite ι
  let P := Submodule.span K (Set.range fun f : A →ₐ[K] K ↦ D.map f)
  change coordinateSpan D = P
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    by_contra h
    change D.map f ∉ P at h
    obtain ⟨l, hl, hP⟩ := P.exists_dual_map_eq_bot_of_notMem h inferInstance
    let a := ∑ i, ∑ j, l (Matrix.single i j 1) • D i j
    have ha : a = 0 := by
      apply zero_of_all_geometric_evaluations (K := K) a
      intro g
      change g.toLinearMap a = 0
      rw [← eval_matrix_linear D l g.toLinearMap]
      have hg : D.map g.toLinearMap ∈ P := Submodule.subset_span ⟨g, rfl⟩
      have hg' := Submodule.mem_map_of_mem hg (f := l)
      simpa [hP] using hg'
    apply hl
    rw [eval_matrix_linear]
    change f a = 0
    rw [ha, map_zero]
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact ⟨g.toLinearMap, rfl⟩


private theorem matrix_mem_of_map_mem_extended {K ι : Type u} [Field K] [Algebra k K]
    (M : Submodule k (Matrix ι ι k)) {v : Matrix ι ι k}
    (hv : v.map (algebraMap k K) ∈ extendMatrixSpan K M) :
    v ∈ M := by
  let i : k →ₗ[k] K := Algebra.linearMap k K
  have hi : LinearMap.ker i = ⊥ := LinearMap.ker_eq_bot.mpr (algebraMap k K).injective
  obtain ⟨l, hl⟩ := i.exists_leftInverse_of_injective hi
  have hli (a : k) : l (algebraMap k K a) = a := LinearMap.congr_fun hl a
  have hlm : ∀ w ∈ extendMatrixSpan K M, ∀ f : K →ₗ[k] k, w.map f ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨z, hz, rfl⟩ := hw
      intro f
      have he : (z.map (algebraMap k K)).map f = f 1 • z := by
        ext a b
        change f (algebraMap k K (z a b)) = f 1 * z a b
        rw [show algebraMap k K (z a b) = z a b • (1 : K) by simp [Algebra.smul_def],
          map_smul, smul_eq_mul, mul_comm]
      rw [he]
      exact M.smul_mem _ hz
    | zero =>
      intro f
      have he : (0 : Matrix ι ι K).map f = 0 := by ext; exact map_zero f
      rw [he]
      exact M.zero_mem
    | add x y _ _ hx hy =>
      intro f
      have he : (x + y).map f = x.map f + y.map f := by ext a b; exact f.map_add _ _
      rw [he]
      exact M.add_mem (hx f) (hy f)
    | smul r x _ hx =>
      intro f
      let fr := f.comp ((LinearMap.id : K →ₗ[k] K).smulRight r)
      have he : (r • x).map f = x.map fr := by
        ext a b
        change f (r * x a b) = f (x a b * r)
        rw [mul_comm]
      exact he.symm ▸ hx fr
  have he : (v.map (algebraMap k K)).map l = v := by
    ext a b
    exact hli (v a b)
  exact he ▸ hlm _ hv l

private theorem commute_of_span {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    {S : Set B} (h : ∀ x ∈ S, ∀ y ∈ S, Commute x y) {x y : B}
    (hx : x ∈ Submodule.span R S) (hy : y ∈ Submodule.span R S) : Commute x y := by
  exact Submodule.span_induction₂ (p := fun x y _ _ ↦ Commute x y)
    (fun x y hx hy ↦ h x hx y hy) (fun _ _ ↦ Commute.zero_left _)
    (fun _ _ ↦ Commute.zero_right _) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.add_left h₂)
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.add_right h₂)
    (fun r _ _ _ _ h ↦ h.smul_left r) (fun r _ _ _ _ h ↦ h.smul_right r) hx hy

private theorem mul_mem_span {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    {S : Set B} (h : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span R S) {x y : B}
    (hx : x ∈ Submodule.span R S) (hy : y ∈ Submodule.span R S) : x * y ∈ Submodule.span R S := by
  let P := Submodule.span R S
  refine Submodule.span_induction₂ (p := fun x y _ _ ↦ x * y ∈ P)
    (fun x y hx hy ↦ h x hx y hy) ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro
    simp
  · intro
    simp
  · intro x y z _ _ _ h₁ h₂
    rw [add_mul]
    exact P.add_mem h₁ h₂
  · intro x y z _ _ _ h₁ h₂
    rw [mul_add]
    exact P.add_mem h₁ h₂
  · intro r x y _ _ h
    rw [smul_mul_assoc]
    exact P.smul_mem r h
  · intro r x y _ _ h
    rw [mul_smul_comm]
    exact P.smul_mem r h

private theorem add_pow_of_cast_eq_zero {B : Type*} [Ring B] {p : ℕ} (hp : p.Prime)
    (hc : (p : B) = 0) {x y : B} (h : Commute x y) :
    (x + y) ^ p = x ^ p + y ^ p := by
  obtain ⟨r, hr⟩ := h.exists_add_pow_prime_eq hp
  simpa [hc] using hr

private theorem pow_eq_zero_of_span {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    {p : ℕ} (hp : p.Prime) (hc : (p : B) = 0) {S : Set B}
    (h : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (hn : ∀ x ∈ S, x ^ p = 0)
    {x : B} (hx : x ∈ Submodule.span R S) : x ^ p = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hn x hx
  | zero => exact zero_pow hp.ne_zero
  | add x y hx hy hxp hyp => rw [add_pow_of_cast_eq_zero hp hc (commute_of_span h hx hy),
      hxp, hyp, add_zero]
  | smul r x hx hxp => rw [smul_pow, hxp, smul_zero]

private def pointMatrix {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) (R : TestAlgebra k)
    (x : (convolutionPoints A).obj R) : Matrix (Index.{u} n) (Index.{u} n) R :=
  (ρ.app R x).val.val

private theorem pointMatrix_mul {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) (R : TestAlgebra k)
    (x y : (convolutionPoints A).obj R) :
    pointMatrix ρ R (x * y) = pointMatrix ρ R x * pointMatrix ρ R y := by
  change (ρ.app R (x * y)).val.val = _
  rw [map_mul]
  rfl

private theorem pointMatrix_pow {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) (R : TestAlgebra k)
    (x : (convolutionPoints A).obj R) (m : ℕ) :
    pointMatrix ρ R (x ^ m) = pointMatrix ρ R x ^ m := by
  change (ρ.app R (x ^ m)).val.val = _
  rw [map_pow]
  rfl

private theorem pointMatrix_one {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) (R : TestAlgebra k) :
    pointMatrix ρ R 1 = 1 := by
  change (ρ.app R 1).val.val = _
  rw [map_one]
  rfl

private theorem universalDifference_map {A : HopfAlgebraCategory k} {n : ℕ}
    (ρ : convolutionPoints A ⟶ unitriangularPoints k n) (R : TestAlgebra k)
    (f : A →ₐ[k] R) :
    (universalDifference ρ).map f = pointMatrix ρ R (toConv f) - 1 := by
  have h := ConcreteCategory.congr_hom (ρ.naturality (CommAlgCat.ofHom f)).symm
    (toConv (AlgHom.id k A))
  have h' := congrArg (fun x : (unitriangularPoints k n).obj R ↦ x.val.val) h
  change f.mapMatrix (pointMatrix ρ (CommAlgCat.of k A) (toConv (AlgHom.id k A))) =
    pointMatrix ρ R (toConv (f.comp (AlgHom.id k A))) at h'
  rw [AlgHom.comp_id] at h'
  change f.mapMatrix (pointMatrix ρ (CommAlgCat.of k A) (toConv (AlgHom.id k A)) - 1) = _
  rw [map_sub, map_one, h']

set_option maxHeartbeats 1000000 in
theorem coordinateSpanNilAlgebra : CoordinateSpanNilAlgebra.{u} := by
  intro k _ p hp _ A _ _ n ρ hcomm hpow
  classical
  let D := universalDifference ρ
  let M := coordinateSpan (k := k) D
  let K := AlgebraicClosure k
  let R := CommAlgCat.of k K
  let S : Set (Matrix (Index.{u} n) (Index.{u} n) K) :=
    Set.range fun x : (convolutionPoints A).obj R ↦ pointMatrix ρ R x - 1
  have hS : extendMatrixSpan K M = Submodule.span K S := by
    apply le_antisymm
    · trans coordinateSpan (k := K)
        (D.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A))
      · exact (coordinateSpanBaseChange D).le
      · rw [coordinateSpanGeometricPoints]
        apply Submodule.span_mono
        rintro _ ⟨g, rfl⟩
        let f : A →ₐ[k] K := (g.restrictScalars k).comp Algebra.TensorProduct.includeRight
        exact ⟨toConv f, (universalDifference_map ρ R f).symm⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨x, rfl⟩
      change pointMatrix ρ R (toConv x.ofConv) - 1 ∈ _
      rw [← universalDifference_map ρ R x.ofConv]
      exact coordinateEvaluationMem D x.ofConv
  let φ := (algebraMap k K).mapMatrix (m := Index.{u} n)
  have hφ : Function.Injective φ := by
    intro v w he
    ext i j
    exact (algebraMap k K).injective
      (congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) K ↦ m i j) he)
  have cast_p : (p : Matrix (Index.{u} n) (Index.{u} n) K) = 0 := by
    have h : (p : K) = 0 := by
      rw [← map_natCast (algebraMap k K), CharP.cast_eq_zero, map_zero]
    exact (map_natCast (algebraMap K _) p).symm.trans (by rw [h, map_zero])
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have h : Commute (pointMatrix ρ R x) (pointMatrix ρ R y) := by
      show pointMatrix ρ R x * pointMatrix ρ R y = pointMatrix ρ R y * pointMatrix ρ R x
      rw [← pointMatrix_mul, ← pointMatrix_mul, (hcomm R x y).eq]
    exact (h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
  have hmulS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ Submodule.span K S := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    have hmem (z) : pointMatrix ρ R z - 1 ∈ Submodule.span K S :=
      Submodule.subset_span ⟨z, rfl⟩
    have he : (pointMatrix ρ R x - 1) * (pointMatrix ρ R y - 1) =
        pointMatrix ρ R (x * y) - 1 - (pointMatrix ρ R x - 1) -
          (pointMatrix ρ R y - 1) := by
      rw [pointMatrix_mul, sub_mul, mul_sub, one_mul, mul_one]
      abel
    rw [he]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (hmem _) (hmem _)) (hmem _)
  have hpowS : ∀ x ∈ S, x ^ p = 0 := by
    rintro _ ⟨x, rfl⟩
    have he := add_pow_of_cast_eq_zero hp.out cast_p (Commute.one_right (pointMatrix ρ R x - 1))
    rw [sub_add_cancel, one_pow, ← pointMatrix_pow, hpow R x, pointMatrix_one] at he
    exact add_right_cancel (he.symm.trans (zero_add 1).symm)
  have hmem {v} (hv : v ∈ M) : φ v ∈ Submodule.span K S := by
    rw [← hS]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  change IsMatrixNilAlgebra p M
  constructor
  · rintro _ ⟨l, rfl⟩ i j hij
    have hzero : D i j = 0 := by
      let g := ρ.app (CommAlgCat.of k A) (toConv (AlgHom.id k A))
      change (g.val.val - 1) i j = 0
      rcases lt_or_eq_of_le hij with hj | rfl
      · simp [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hj), g.property.1 hj]
      · simp [Matrix.sub_apply, g.property.2]
    change l (D i j) = 0
    rw [hzero, map_zero]
  · intro v w hv hw
    apply matrix_mem_of_map_mem_extended (K := K) M
    change φ (v * w) ∈ extendMatrixSpan K M
    rw [map_mul, hS]
    exact mul_mem_span hmulS (hmem hv) (hmem hw)
  · intro v w hv hw
    apply hφ
    rw [map_mul, map_mul]
    exact (commute_of_span hcommS (hmem hv) (hmem hw)).eq
  · intro v hv
    apply hφ
    rw [map_pow, map_zero]
    exact pow_eq_zero_of_span hp.out cast_p hcommS hpowS (hmem hv)


section Exponential

open Polynomial

variable (k) {p : ℕ} [Fact p.Prime] [CharP k p]
variable {R : Type u} [CommRing R] [Algebra k R]

private def expPolynomial (p : ℕ) (t : R) : R[X] :=
  ∑ j ∈ Finset.range p, monomial j (algebraMap k R ((j.factorial : k)⁻¹) * t ^ j)

omit [Fact p.Prime] [CharP k p] in
private theorem expPolynomial_coeff (t : R) {a : ℕ} (ha : a < p) :
    (expPolynomial k p t).coeff a = algebraMap k R ((a.factorial : k)⁻¹) * t ^ a := by
  rw [expPolynomial, finsetSum_coeff, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [coeff_monomial, hb]
  · simp [ha]

private theorem inverse_factorial_choose {a b : ℕ} (ha : a < p) (hb : b ≤ a) :
    ((a.factorial : k)⁻¹) * (a.choose b : k) =
      ((b.factorial : k)⁻¹) * (((a - b).factorial : k)⁻¹) := by
  have hn {j : ℕ} (hj : j < p) : (j.factorial : k) ≠ 0 :=
    isUnit_iff_ne_zero.mp ((IsUnit.natCast_factorial_iff_of_charP (A := k) p).mpr hj)
  have hA := hn ha
  have hB := hn (show b < p by omega)
  have hC := hn (show a - b < p by omega)
  have he : (a.choose b : k) * (b.factorial : k) * ((a - b).factorial : k) =
      (a.factorial : k) := by
    simpa only [Nat.cast_mul] using congrArg (fun m : ℕ ↦ (m : k))
      (Nat.choose_mul_factorial_mul_factorial hb)
  field_simp
  linear_combination he

private theorem expPolynomial_add_mod (s t : R) :
    (X : R[X]) ^ p ∣ expPolynomial k p (s + t) - expPolynomial k p s * expPolynomial k p t := by
  rw [X_pow_dvd_iff]
  intro a ha
  rw [coeff_sub, sub_eq_zero, expPolynomial_coeff k _ ha, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦
      (expPolynomial k p s).coeff i * (expPolynomial k p t).coeff j),
    add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hba : b ≤ a := by simpa using hb
  rw [expPolynomial_coeff k _ (show b < p by omega),
    expPolynomial_coeff k _ (show a - b < p by omega)]
  have h := congrArg (algebraMap k R) (inverse_factorial_choose k ha hba)
  push_cast at h
  calc
    _ = (algebraMap k R ((a.factorial : k)⁻¹) * (a.choose b : R)) *
          (s ^ b * t ^ (a - b)) := by ring
    _ = _ := by rw [h]; ring

variable {B : Type u} [Ring B] [Algebra R B]

private def truncatedExp (p : ℕ) (v : B) (t : R) : B :=
  Polynomial.aeval v (expPolynomial k p t)

omit [Fact p.Prime] [CharP k p] in
private theorem truncatedExp_eq_sum (v : B) (t : R) :
    truncatedExp k p v t =
      ∑ j ∈ Finset.range p, (algebraMap k R ((j.factorial : k)⁻¹) * t ^ j) • v ^ j := by
  simp only [truncatedExp, expPolynomial, map_sum, aeval_monomial, Algebra.smul_def]

private theorem truncatedExp_add (v : B) (hv : v ^ p = 0) (s t : R) :
    truncatedExp k p v (s + t) = truncatedExp k p v s * truncatedExp k p v t := by
  obtain ⟨q, hq⟩ := expPolynomial_add_mod (k := k) (p := p) s t
  have he := congrArg (Polynomial.aeval (R := R) v) hq
  simpa only [map_sub, map_mul, map_pow, aeval_X, hv, zero_mul, sub_eq_zero, truncatedExp] using he

omit [CharP k p] in
private theorem truncatedExp_zero (v : B) :
    truncatedExp k p v (0 : R) = 1 := by
  rw [truncatedExp_eq_sum, Finset.sum_eq_single 0]
  · simp
  · intro a _ ha
    simp [zero_pow ha]
  · simp [(Fact.out : p.Prime).pos]

end Exponential


section Filtration

open scoped Pointwise

private theorem exists_adapted_independent_set {V : Type u} [AddCommGroup V] [Module k V]
    (n : ℕ) (F : ℕ → Submodule k V) (hF : Antitone F) :
    ∃ s : Set V, s ⊆ F 0 ∧ LinearIndepOn k id s ∧
      ∀ j ≤ n, Submodule.span k (s ∩ (F j : Set V)) = F j := by
  induction n generalizing F with
  | zero =>
    have h : LinearIndepOn k id (∅ : Set V) := linearIndepOn_empty _ _
    let hs : (∅ : Set V) ⊆ (F 0 : Set V) := Set.empty_subset _
    let s := h.extend hs
    refine ⟨s, h.extend_subset hs, h.linearIndepOn_extend hs, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    rw [Set.inter_eq_left.mpr (h.extend_subset hs), h.span_extend_eq_span, Submodule.span_eq]
  | succ n ih =>
    obtain ⟨s, hs, hli, hsp⟩ := ih (fun j ↦ F (j + 1))
      (fun _ _ hj ↦ hF (Nat.add_le_add_right hj 1))
    have hs₁ : Submodule.span k s = F 1 := by
      simpa only [Nat.zero_add, Set.inter_eq_left.mpr hs] using hsp 0 (Nat.zero_le n)
    let hs₀ : s ⊆ (F 0 : Set V) := hs.trans (hF (by omega))
    let t := hli.extend hs₀
    have hst : s ⊆ t := hli.subset_extend hs₀
    have ht : t ⊆ (F 0 : Set V) := hli.extend_subset hs₀
    have htli : LinearIndepOn k id t := hli.linearIndepOn_extend hs₀
    refine ⟨t, ht, htli, ?_⟩
    intro j hj
    obtain rfl | j := j
    · rw [Set.inter_eq_left.mpr ht, hli.span_extend_eq_span, Submodule.span_eq]
    · have hts : t ∩ (F (j + 1) : Set V) ⊆ s := by
        apply le_of_span_le_span htli Set.inter_subset_left hst
        rw [hs₁]
        exact Submodule.span_le.mpr fun _ hx ↦ hF (by omega) hx.2
      have he : t ∩ (F (j + 1) : Set V) = s ∩ (F (j + 1) : Set V) :=
        Set.Subset.antisymm (Set.subset_inter hts Set.inter_subset_right)
          (Set.inter_subset_inter_left _ hst)
      rw [he]
      exact hsp j (by omega)

private def matrixHeight (R : Type u) [CommRing R] (n j : ℕ) :
    Submodule R (Matrix (Index.{u} n) (Index.{u} n) R) where
  carrier := {x | ∀ i l : Index.{u} n, l.down.val < i.down.val + j → x i l = 0}
  zero_mem' := by simp
  add_mem' hx hy i l h := by
    rw [Matrix.add_apply, hx i l h, hy i l h, add_zero]
  smul_mem' r x hx i l h := by
    change r * x i l = 0
    rw [hx i l h, mul_zero]

private theorem matrixHeight_antitone (R : Type u) [CommRing R] (n : ℕ) :
    Antitone (matrixHeight R n) :=
  fun _ _ h _ hx i j hj ↦ hx i j (lt_of_lt_of_le hj (Nat.add_le_add_left h _))

private theorem matrixHeight_mul {R : Type u} [CommRing R] {n a b : ℕ}
    {x y : Matrix (Index.{u} n) (Index.{u} n) R}
    (hx : x ∈ matrixHeight R n a) (hy : y ∈ matrixHeight R n b) :
    x * y ∈ matrixHeight R n (a + b) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases h : l.down.val < i.down.val + a
  · rw [hx i l h, zero_mul]
  · rw [hy l j (by omega), mul_zero]

private theorem matrixHeight_eq_bot (R : Type u) [CommRing R] (n : ℕ) :
    matrixHeight R n n = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  rw [Submodule.mem_bot]
  ext i j
  have h : j.down.val < n := j.down.isLt
  exact hx i j (by omega)

/-- The zeroth term is M, and the j-th term is its (j+1)-st power. -/
private def matrixFiltration {n : ℕ}
    (M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)) (j : ℕ) :
    Submodule k (Matrix (Index.{u} n) (Index.{u} n) k) :=
  M ^ (j + 1)

private theorem matrixFiltration_zero {n : ℕ}
    (M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)) :
    matrixFiltration M 0 = M := pow_one M

private theorem matrixFiltration_mul {n j : ℕ}
    {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}
    {x y : Matrix (Index.{u} n) (Index.{u} n) k}
    (hx : x ∈ matrixFiltration M j) (hy : y ∈ M) :
    x * y ∈ matrixFiltration M (j + 1) := Submodule.mul_mem_mul hx hy

private theorem matrixFiltration_antitone {n p : ℕ}
    {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}
    (hM : IsMatrixNilAlgebra p M) :
    Antitone (matrixFiltration M) := by
  apply antitone_nat_of_succ_le
  intro j
  induction j with
  | zero =>
    change matrixFiltration M 0 * M ≤ matrixFiltration M 0
    rw [matrixFiltration_zero]
    exact Submodule.mul_le.mpr fun _ hx _ hy ↦ hM.mul_mem hx hy
  | succ j ih =>
    change matrixFiltration M (j + 1) * M ≤ matrixFiltration M j * M
    exact mul_le_mul' ih le_rfl

private theorem matrixFiltration_le_height {n p : ℕ}
    {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}
    (hM : IsMatrixNilAlgebra p M) (j : ℕ) :
    matrixFiltration M j ≤ matrixHeight k n (j + 1) := by
  induction j with
  | zero =>
    rw [matrixFiltration_zero]
    intro x hx i l hl
    exact hM.strictUpper hx i l (by change l.down.val ≤ i.down.val; omega)
  | succ j ih =>
    change matrixFiltration M j * M ≤ matrixHeight k n ((j + 1) + 1)
    apply Submodule.mul_le.mpr
    intro x hx y hy
    apply matrixHeight_mul (ih hx)
    intro i l hl
    exact hM.strictUpper hy i l (by change l.down.val ≤ i.down.val; omega)

private theorem matrixFiltration_top_index {n p : ℕ}
    {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}
    (hM : IsMatrixNilAlgebra p M) : matrixFiltration M n = ⊥ := by
  apply le_bot_iff.mp
  exact (matrixFiltration_le_height hM n).trans
    ((matrixHeight_antitone k n (Nat.le_succ n)).trans_eq (matrixHeight_eq_bot k n))

private theorem matrixFiltration_le {n p : ℕ}
    {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}
    (hM : IsMatrixNilAlgebra p M) (j : ℕ) : matrixFiltration M j ≤ M :=
  (matrixFiltration_antitone hM (Nat.zero_le j)).trans_eq (matrixFiltration_zero M)

private theorem extendMatrixSpan_mono {ι R : Type u} [CommRing R] [Algebra k R]
    {M N : Submodule k (Matrix ι ι k)} (h : M ≤ N) : extendMatrixSpan R M ≤ extendMatrixSpan R N :=
  Submodule.span_mono (Set.image_mono h)

private theorem extendMatrixSpan_bot (ι R : Type u) [CommRing R] [Algebra k R] :
    extendMatrixSpan R (⊥ : Submodule k (Matrix ι ι k)) = ⊥ := by
  apply le_bot_iff.mp
  apply Submodule.span_le.mpr
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_bot] at hv
  subst v
  rw [SetLike.mem_coe, Submodule.mem_bot]
  ext
  exact map_zero (algebraMap k R)

private theorem mul_mem_extendMatrixSpan {ι R : Type u} [Fintype ι] [DecidableEq ι]
    [CommRing R] [Algebra k R] {M N P : Submodule k (Matrix ι ι k)}
    (h : M * N ≤ P) {x y : Matrix ι ι R}
    (hx : x ∈ extendMatrixSpan R M) (hy : y ∈ extendMatrixSpan R N) :
    x * y ∈ extendMatrixSpan R P := by
  let φ := (algebraMap k R).mapMatrix (m := ι)
  have hφ : extendMatrixSpan R M * extendMatrixSpan R N ≤ extendMatrixSpan R P := by
    unfold extendMatrixSpan
    rw [Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨v, hv, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨v * w, h (Submodule.mul_mem_mul hv hw), φ.map_mul v w⟩
  exact hφ (Submodule.mul_mem_mul hx hy)

end Filtration


section ExtendedCoordinates

variable {R : Type u} [CommRing R] [Algebra k R]
variable {I J : Type u} [Fintype I] [DecidableEq I] [Fintype J]

omit [Fintype I] [DecidableEq I] in
private theorem extendMatrixSpan_span (S : Set (Matrix I I k)) :
    extendMatrixSpan R (Submodule.span k S) =
      Submodule.span R ((fun v : Matrix I I k ↦ v.map (algebraMap k R)) '' S) := by
  let f : Matrix I I k →ₗ[k] Matrix I I R := (Algebra.linearMap k R).mapMatrix
  change Submodule.span R (f '' (Submodule.span k S : Set _)) = _
  rw [← Submodule.map_coe, Submodule.map_span, Submodule.span_span_of_tower]
  rfl

private def extendMatrixFunctional (f : Module.Dual k (Matrix I I k)) :
    Matrix I I R →ₗ[R] R :=
  ∑ i, ∑ j, algebraMap k R (f (Matrix.single i j 1)) • Matrix.entryLinearMap R R i j

private theorem extendMatrixFunctional_map (f : Module.Dual k (Matrix I I k)) (x : Matrix I I k) :
    extendMatrixFunctional (R := R) f (x.map (algebraMap k R)) = algebraMap k R (f x) := by
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [extendMatrixFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.entryLinearMap_apply, Matrix.map_apply, smul_eq_mul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h : Matrix.single i j (x i j) = x i j • Matrix.single i j (1 : k) := by
    ext a b
    simp [Matrix.single, Matrix.smul_apply]
  rw [h, map_smul, smul_eq_mul, map_mul, mul_comm]

private theorem linearIndependent_mapMatrix {b : J → Matrix I I k}
    (hb : LinearIndependent k b) :
    LinearIndependent R (fun j ↦ (b j).map (algebraMap k R)) := by
  classical
  let f := Fintype.linearCombination k b
  have hf : Function.Injective f := linearIndependent_iff_injective_fintypeLinearCombination.mp hb
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let l (j : J) : Module.Dual k (Matrix I I k) := (LinearMap.proj j).comp g
  have hl (i j) : l i (b j) = if j = i then 1 else 0 := by
    have he : f (Pi.single j 1) = b j := by simp [f]
    rw [← he]
    change (g (f (Pi.single j 1))) i = _
    rw [show g (f (Pi.single j 1)) = Pi.single j 1 from LinearMap.congr_fun hg _]
    by_cases hj : j = i <;> simp [Pi.single, hj, Ne.symm]
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun j ↦ extendMatrixFunctional (l j))
  · intro i j hij
    rw [extendMatrixFunctional_map, hl]
    simp [Ne.symm hij]
  · intro i
    rw [extendMatrixFunctional_map, hl]
    simp

omit [Fintype I] [DecidableEq I] in
private theorem exists_supported_coordinates {b : J → Matrix I I k} (F : Submodule k (Matrix I I k))
    (hF : Submodule.span k (Set.range fun j : {j // b j ∈ F} ↦ b j.val) = F)
    {x : Matrix I I R} (hx : x ∈ extendMatrixSpan R F) :
    ∃ t : J → R, (∀ j, b j ∉ F → t j = 0) ∧
      ∑ j, t j • (b j).map (algebraMap k R) = x := by
  classical
  rw [← hF, extendMatrixSpan_span, ← Set.range_comp] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
  let t (j : J) := if h : b j ∈ F then c ⟨j, h⟩ else 0
  refine ⟨t, fun j hj ↦ dite_eq_right hj, ?_⟩
  rw [← hc]
  calc
    _ = ∑ j ∈ Finset.univ.filter (fun j ↦ b j ∈ F), t j • (b j).map (algebraMap k R) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : b j ∈ F <;> simp [t, h]
    _ = _ := by
      rw [Finset.sum_subtype (p := fun j ↦ b j ∈ F) _ (fun j ↦ by simp)]
      apply Finset.sum_congr rfl
      intro j _
      simp [t, j.property]

end ExtendedCoordinates


section ExponentialProduct

open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable {R : Type u} [CommRing R] [Algebra k R]
variable {B : Type u} [Ring B] [Algebra R B]

private def exponentialFactor (v : B) (hv : v ^ p = 0) : Multiplicative R →* B where
  toFun t := truncatedExp k p v t.toAdd
  map_one' := truncatedExp_zero k v
  map_mul' s t := truncatedExp_add k v hv s.toAdd t.toAdd

omit [Fact p.Prime] [CharP k p] in
private theorem truncatedExp_commute {x y : B} (h : Commute x y) (s t : R) :
    Commute (truncatedExp k p x s) (truncatedExp k p y t) := by
  rw [truncatedExp_eq_sum, truncatedExp_eq_sum]
  apply Commute.sum_left
  intro i _
  apply Commute.smul_left
  apply Commute.sum_right
  intro j _
  apply Commute.smul_right
  exact (h.pow_pow i j)

variable {J : Type u} [Fintype J]

private def exponentialProduct (b : J → B) (hb : ∀ j, b j ^ p = 0)
    (hc : ∀ i j, Commute (b i) (b j)) : (J → Multiplicative R) →* B :=
  MonoidHom.noncommPiCoprod (fun j ↦ exponentialFactor (k := k) (b j) (hb j))
    (fun i j _ s t ↦ truncatedExp_commute (k := k) (p := p) (hc i j) s.toAdd t.toAdd)

omit [CharP k p] in
private theorem truncatedExp_sub_linear_mem {P Q : Submodule R B} (_hP : P ≤ Q)
    (hmul : P * Q ≤ P) (hnext : Q * Q ≤ P) {x : B} (hx : x ∈ Q) (t : R) :
    truncatedExp k p x t - 1 - t • x ∈ P := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp' : p = p - 2 + 1 + 1 := by omega
  have hpow (a : ℕ) : x ^ (a + 2) ∈ P := by
    induction a with
    | zero =>
      rw [zero_add, pow_two]
      exact hnext (Submodule.mul_mem_mul hx hx)
    | succ a ih =>
      rw [show a.succ + 2 = a + 2 + 1 by omega, pow_succ]
      exact hmul (Submodule.mul_mem_mul ih hx)
  let f (j : ℕ) : B := (algebraMap k R ((j.factorial : k)⁻¹) * t ^ j) • x ^ j
  have hf₀ : f 0 = 1 := by simp [f]
  have hf₁ : f 1 = t • x := by simp [f]
  have hsum : truncatedExp k p x t =
      f 0 + (f 1 + ∑ i ∈ Finset.range (p - 2), f (i + 2)) := by
    rw [truncatedExp_eq_sum]
    change (∑ i ∈ Finset.range p, f i) = _
    conv_lhs => rw [hp', Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.add_assoc]
    abel
  rw [hsum, hf₀, hf₁]
  have he : 1 + (t • x + ∑ i ∈ Finset.range (p - 2), f (i + 2)) - 1 - t • x =
      ∑ i ∈ Finset.range (p - 2), f (i + 2) := by abel
  rw [he]
  exact Submodule.sum_mem _ fun a _ ↦ P.smul_mem _ (hpow a)

set_option backward.isDefEq.respectTransparency false in
omit [CharP k p] [Fintype J] in
private theorem exponentialProduct_sub_linear_mem (b : J → B)
    (hc : ∀ i j, Commute (b i) (b j)) {P Q : Submodule R B} (hP : P ≤ Q)
    (hmul : P * Q ≤ P) (hnext : Q * Q ≤ P)
    (t : J → Multiplicative R) (ht : ∀ j, t j ≠ 1 → b j ∈ Q) (S : Finset J) :
    (S.noncommProd (fun j ↦ truncatedExp k p (b j) (t j).toAdd)
      (fun i _ j _ _ ↦ truncatedExp_commute (k := k) (p := p) (hc i j) (t i).toAdd (t j).toAdd)) -
      1 - ∑ j ∈ S, (t j).toAdd • b j ∈ P := by
  classical
  let e (j : J) := truncatedExp k p (b j) (t j).toAdd
  let v (j : J) := (t j).toAdd • b j
  have hvi (j) : v j ∈ Q := by
    by_cases h : t j = 1
    · have h0 : (t j).toAdd = 0 := congrArg Multiplicative.toAdd h
      simp [v, h0]
    · exact Q.smul_mem _ (ht j h)
  have hei (j) : e j - 1 - v j ∈ P := by
    by_cases h : t j = 1
    · have h0 : (t j).toAdd = 0 := congrArg Multiplicative.toAdd h
      simp [e, v, h0, truncatedExp_zero]
    · exact truncatedExp_sub_linear_mem (k := k) (p := p) hP hmul hnext (ht j h) _
  have hc' (i j : J) : Commute (e i) (e j) :=
    truncatedExp_commute (k := k) (p := p) (hc i j) _ _
  change S.noncommProd e (fun i _ j _ _ ↦ hc' i j) - 1 - ∑ j ∈ S, v j ∈ P
  induction S using Finset.induction_on with
  | empty => simp [Finset.noncommProd_empty]
  | insert j S hj ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Finset.sum_insert hj]
    let z := S.noncommProd e (fun i _ j _ _ ↦ hc' i j)
    have hcombine {x a : B} (hxa : x - 1 - a ∈ P) (ha : a ∈ Q) : x - 1 ∈ Q := by
      have he : x - 1 = (x - 1 - a) + a := by abel
      rw [he]
      exact Q.add_mem (hP hxa) ha
    have hz : z - 1 ∈ Q := hcombine ih (Submodule.sum_mem _ fun i _ ↦ hvi i)
    have hj' : e j - 1 ∈ Q := hcombine (hei j) (hvi j)
    have hcross : (e j - 1) * (z - 1) ∈ P := hnext (Submodule.mul_mem_mul hj' hz)
    change e j * z - 1 - (v j + ∑ i ∈ S, v i) ∈ P
    have he : e j * z - 1 - (v j + ∑ i ∈ S, v i) =
        (e j - 1 - v j) + (z - 1 - ∑ i ∈ S, v i) + (e j - 1) * (z - 1) := by
      noncomm_ring
    rw [he]
    exact P.add_mem (P.add_mem (hei j) ih) hcross

end ExponentialProduct


section MatrixExponential

open scoped Pointwise

variable {p n d : ℕ} [Fact p.Prime] [CharP k p]
variable {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}

private def extendedBasis (R : Type u) [CommRing R] [Algebra k R]
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (i : Index.{u} d) :
    Matrix (Index.{u} n) (Index.{u} n) R :=
  (b i).map (algebraMap k R)

private def matrixExponential (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k)
    (hb : ∀ i, b i ∈ M) (R : Type u) [CommRing R] [Algebra k R] :
    (Index.{u} d → Multiplicative R) →* Matrix (Index.{u} n) (Index.{u} n) R := by
  let φ := (algebraMap k R).mapMatrix (m := Index.{u} n)
  refine exponentialProduct (k := k) (extendedBasis R b) (fun i ↦ ?_) (fun i j ↦ ?_)
  · change φ (b i) ^ p = 0
    rw [← map_pow, hM.pow_eq_zero (hb i), map_zero]
  · exact (hM.commute (hb i) (hb j)).map φ

private theorem matrixExponential_apply (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M)
    (R : Type u) [CommRing R] [Algebra k R] (t : Index.{u} d → Multiplicative R) :
    matrixExponential hM b hb R t =
      Finset.univ.noncommProd (fun i ↦ truncatedExp k p (extendedBasis R b i) (t i).toAdd)
        (fun i _ j _ _ ↦ truncatedExp_commute
          ((hM.commute (hb i) (hb j)).map ((algebraMap k R).mapMatrix (m := Index.{u} n))) _ _) :=
  rfl

private theorem matrixExponential_approx (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M)
    (R : Type u) [CommRing R] [Algebra k R] (j : ℕ)
    (t : Index.{u} d → Multiplicative R) (ht : ∀ i, t i ≠ 1 → b i ∈ matrixFiltration M j) :
    matrixExponential hM b hb R t - 1 - ∑ i, (t i).toAdd • extendedBasis R b i ∈
      extendMatrixSpan R (matrixFiltration M (j + 1)) := by
  let φ := (algebraMap k R).mapMatrix (m := Index.{u} n)
  let F := fun j ↦ extendMatrixSpan R (matrixFiltration M j)
  have hstep (r s : ℕ) : F r * F s ≤ F (r + 1) :=
    Submodule.mul_le.mpr fun _ hx _ hy ↦
      mul_mem_extendMatrixSpan (M := matrixFiltration M r) (N := matrixFiltration M s)
        (Submodule.mul_le.mpr fun _ hx _ hy ↦ matrixFiltration_mul hx (matrixFiltration_le hM s hy)) hx hy
  have hmono : Antitone F := fun _ _ h ↦ extendMatrixSpan_mono (matrixFiltration_antitone hM h)
  have hcomm (i j) : Commute (extendedBasis R b i) (extendedBasis R b j) :=
    (hM.commute (hb i) (hb j)).map φ
  exact exponentialProduct_sub_linear_mem (k := k) (p := p) _ hcomm (hmono (Nat.le_succ j))
    ((hstep (j + 1) j).trans (hmono (Nat.le_succ _))) (hstep j j) t
    (fun i hi ↦ Submodule.subset_span ⟨b i, ht i hi, rfl⟩) Finset.univ

private theorem matrixExponential_mem (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M)
    (R : Type u) [CommRing R] [Algebra k R] (t : Index.{u} d → Multiplicative R) :
    matrixExponential hM b hb R t - 1 ∈ extendMatrixSpan R M := by
  have h := matrixExponential_approx hM b hb R 0 t
    (fun i _ ↦ by rw [matrixFiltration_zero M]; exact hb i)
  have hsum : ∑ i, (t i).toAdd • extendedBasis R b i ∈ extendMatrixSpan R M :=
    Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  have hh := extendMatrixSpan_mono (R := R) (matrixFiltration_le hM 1) h
  simpa only [sub_add_cancel] using Submodule.add_mem _ hh hsum

private def unitriangularExponential (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k)
    (hb : ∀ i, b i ∈ M) (R : Type u) [CommRing R] [Algebra k R] :
    (Index.{u} d → Multiplicative R) →* upperUnitriangular (Index.{u} n) R := by
  refine (matrixExponential hM b hb R).toHomUnits.codRestrict _ fun t ↦ ?_
  have ht := matrixExponential_mem hM b hb R t
  have htri (x : Matrix (Index.{u} n) (Index.{u} n) R)
      (hx : x ∈ extendMatrixSpan R M) :
      ∀ i j, j ≤ i → x i j = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      intro i j hij
      change algebraMap k R (v i j) = 0
      rw [hM.strictUpper hv i j hij, map_zero]
    | zero => simp
    | add x y _ _ h₁ h₂ =>
      intro i j hij
      rw [Matrix.add_apply, h₁ i j hij, h₂ i j hij, add_zero]
    | smul r x _ h =>
      intro i j hij
      rw [Matrix.smul_apply, h i j hij, smul_zero]
  let v := matrixExponential hM b hb R t
  change IsUpperUnitriangular v
  refine ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · change j < i at hij
    have hh : (v - 1) i j = 0 := htri _ ht i j (le_of_lt hij)
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt hij), sub_zero] using hh
  · have hh : (v - 1) i i = 0 := htri _ ht i i le_rfl
    simpa only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] using hh

set_option backward.isDefEq.respectTransparency false in
private theorem matrixExponential_natural (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M)
    (R S : TestAlgebra k) (a : R ⟶ S) (t : Index.{u} d → Multiplicative R) :
    a.hom.mapMatrix (matrixExponential hM b hb R t) =
      matrixExponential hM b hb S (fun i ↦ Multiplicative.ofAdd (a.hom (t i).toAdd)) := by
  rw [matrixExponential_apply, matrixExponential_apply, Finset.map_noncommProd]
  apply Finset.noncommProd_congr rfl
  intro i _
  change a.hom.mapMatrix (truncatedExp k p (extendedBasis R b i) (t i).toAdd) =
    truncatedExp k p (extendedBasis S b i) (a.hom (t i).toAdd)
  rw [truncatedExp_eq_sum, truncatedExp_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : a.hom.mapMatrix (extendedBasis R b i) = extendedBasis S b i := by
    ext row col
    exact a.hom.commutes (b i row col)
  rw [show ∀ (r : R) (x : Matrix (Index.{u} n) (Index.{u} n) R),
      a.hom.mapMatrix (r • x) = a.hom r • a.hom.mapMatrix x from fun r x ↦ by
        ext row col
        exact a.hom.map_mul _ _, map_pow, he, map_mul, map_pow, a.hom.commutes]

private def exponentialPoints (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M) :
    Specs.StandardGroups.additivePowerPoints k (Index.{u} d) ⟶ unitriangularPoints k n where
  app R := GrpCat.ofHom (unitriangularExponential hM b hb R)
  naturality R S a := by
    apply GrpCat.ext
    intro t
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrArg (fun x : Matrix (Index.{u} n) (Index.{u} n) S ↦ x i j)
      (matrixExponential_natural hM b hb R S a t).symm

end MatrixExponential


section Bijection

open scoped Pointwise

variable {p n d : ℕ} [Fact p.Prime] [CharP k p]
variable {M : Submodule k (Matrix (Index.{u} n) (Index.{u} n) k)}

-- For the kernel, push the linear coordinates down the filtration. For surjectivity,
-- lift one term at a time and remove its contribution by group multiplication.
set_option maxHeartbeats 1600000 in
private theorem exponentialPoints_image (hM : IsMatrixNilAlgebra p M)
    (b : Index.{u} d → Matrix (Index.{u} n) (Index.{u} n) k) (hb : ∀ i, b i ∈ M)
    (hli : LinearIndependent k b)
    (hsp : ∀ j ≤ n, Submodule.span k (Set.range fun i : {i // b i ∈ matrixFiltration M j} ↦
      b i.val) = matrixFiltration M j)
    (R : TestAlgebra k) :
    Function.Injective ((exponentialPoints hM b hb).app R) ∧
      Set.range ((exponentialPoints hM b hb).app R) =
        {g | g.val.val - 1 ∈ extendMatrixSpan R M} := by
  let U := upperUnitriangular (Index.{u} n) R
  let v : U →* Matrix (Index.{u} n) (Index.{u} n) R :=
    ⟨⟨fun g ↦ g.val.val, rfl⟩, fun _ _ ↦ rfl⟩
  let E := unitriangularExponential hM b hb R
  let F (j : ℕ) := extendMatrixSpan R (matrixFiltration M j)
  let D := Index.{u} d → Multiplicative R
  let L (t : D) := ∑ i, (t i).toAdd • extendedBasis R b i
  have hL : Function.Injective L := by
    intro t s h
    have hlin := linearIndependent_iff_injective_fintypeLinearCombination.mp
      (linearIndependent_mapMatrix (R := R) hli)
    have he : (fun i ↦ (t i).toAdd) = fun i ↦ (s i).toAdd := hlin h
    exact funext fun i ↦ congrArg Multiplicative.ofAdd (congrFun he i)
  have hLone : L 1 = 0 := by
    change (∑ i : Index.{u} d, (0 : R) • extendedBasis R b i) = 0
    simp
  have hF0 : F 0 = extendMatrixSpan R M := by
    unfold F
    rw [matrixFiltration_zero M]
  have hFn : F n = ⊥ := by
    unfold F
    rw [matrixFiltration_top_index hM, extendMatrixSpan_bot]
  have hmono : Antitone F := fun _ _ h ↦ extendMatrixSpan_mono (matrixFiltration_antitone hM h)
  have hmul (j : ℕ) : F j * F 0 ≤ F (j + 1) := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    rw [hF0] at hy
    exact mul_mem_extendMatrixSpan (M := matrixFiltration M j) (N := M)
      (Submodule.mul_le.mpr fun _ hx' _ hy' ↦ matrixFiltration_mul hx' hy') hx hy
  have hexists (j : ℕ) (hj : j ≤ n) {x} (hx : x ∈ F j) :
      ∃ t : D, (∀ i, t i ≠ 1 → b i ∈ matrixFiltration M j) ∧ L t = x := by
    obtain ⟨c, hs, hc⟩ := exists_supported_coordinates _ (hsp j hj) hx
    refine ⟨fun i ↦ Multiplicative.ofAdd (c i), fun i hi ↦ ?_, hc⟩
    by_contra h
    exact hi (congrArg Multiplicative.ofAdd (hs i h))
  have hsupport (j : ℕ) (hj : j ≤ n) (t : D) (ht : L t ∈ F j) :
      ∀ i, t i ≠ 1 → b i ∈ matrixFiltration M j := by
    obtain ⟨s, h, hs⟩ := hexists j hj ht
    rwa [hL hs] at h
  have happrox (j : ℕ) (t : D) (ht : ∀ i, t i ≠ 1 → b i ∈ matrixFiltration M j) :
      v (E t) - 1 - L t ∈ F (j + 1) :=
    matrixExponential_approx hM b hb R j t ht
  have hmem (t : D) : v (E t) - 1 ∈ F 0 := by
    rw [hF0]
    exact matrixExponential_mem hM b hb R t
  have hι : Function.Injective E := by
    apply (injective_iff_map_eq_one E).mpr
    intro t ht
    have hLt (j : ℕ) (hj : j ≤ n) : L t ∈ F j := by
      induction j with
      | zero =>
        rw [hF0]
        exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
          (Submodule.subset_span ⟨b i, hb i, rfl⟩)
      | succ j ih =>
        have he := happrox j t (hsupport j (by omega) t (ih (by omega)))
        rw [ht, map_one, sub_self, zero_sub] at he
        exact (F _).neg_mem_iff.mp he
    have h0 := hLt n le_rfl
    rw [hFn, Submodule.mem_bot] at h0
    exact hL (h0.trans hLone.symm)
  have hsurj (j : ℕ) (hj : j ≤ n) :
      ∀ g : U, v g - 1 ∈ F j → g ∈ Set.range E := by
    induction hj using Nat.decreasingInduction with
    | self =>
      intro g hg
      rw [hFn, Submodule.mem_bot, sub_eq_zero] at hg
      refine ⟨1, ?_⟩
      rw [map_one]
      apply Subtype.ext
      apply Units.ext
      exact hg.symm
    | of_succ j hj ih =>
      intro g hg
      obtain ⟨t, ht, hl⟩ := hexists j (by omega) hg
      have he := happrox j t ht
      rw [hl] at he
      let z := v g - v (E t)
      have hz : z ∈ F (j + 1) := by
        have heq : v (E t) - 1 - (v g - 1) = -z := by dsimp [z]; abel
        rw [heq] at he
        exact (F _).neg_mem_iff.mp he
      have heinv : v (E t)⁻¹ - 1 ∈ F 0 := by
        simpa only [map_inv] using hmem t⁻¹
      have hz' : v (g * (E t)⁻¹) - 1 ∈ F (j + 1) := by
        have h1 : v (E t) * v (E t)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
        have h2 : v (g * (E t)⁻¹) - 1 = z + z * (v (E t)⁻¹ - 1) := by
          rw [map_mul, mul_sub, mul_one, add_sub_cancel]
          dsimp [z]
          rw [sub_mul, h1]
        rw [h2]
        exact (F _).add_mem hz <| hmono (Nat.le_succ _) (hmul _ (Submodule.mul_mem_mul hz heinv))
      obtain ⟨s, hs⟩ := ih _ hz'
      exact ⟨s * t, by rw [map_mul, hs, inv_mul_cancel_right]⟩
  refine ⟨hι, Set.ext fun g ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, rfl⟩
    exact matrixExponential_mem hM b hb R t
  · intro hg
    exact hsurj 0 (Nat.zero_le _) g (by rw [hF0]; exact hg)

end Bijection

set_option maxHeartbeats 1000000 in
theorem truncatedExponentialIsomorphism : TruncatedExponentialIsomorphism.{u} := by
  intro k _ p _ _ n M hM
  classical
  let F := matrixFiltration M
  obtain ⟨s, hs, hli, hsp⟩ := exists_adapted_independent_set n F (matrixFiltration_antitone hM)
  let : Finite s := hli.linearIndependent.finite
  let : Fintype s := Fintype.ofFinite s
  let d := Fintype.card s
  let e : Index.{u} d ≃ s := Equiv.ulift.trans (Fintype.equivFin s).symm
  let b (i : Index.{u} d) := (e i).val
  have hb (i) : b i ∈ M := (matrixFiltration_zero M) ▸ hs (e i).property
  have hb' : LinearIndependent k b := hli.linearIndependent.comp e e.injective
  have hspan (j : ℕ) (hj : j ≤ n) :
      Submodule.span k (Set.range fun i : {i // b i ∈ F j} ↦ b i.val) = F j := by
    refine (congrArg (Submodule.span k) ?_).trans (hsp j hj)
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e i.val).property, i.property⟩
    · rintro ⟨hx, hx'⟩
      let i := e.symm ⟨x, hx⟩
      have hi : b i = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
      exact ⟨⟨i, hi.symm ▸ hx'⟩, hi⟩
  have hMspan : Submodule.span k s = M := by
    have h := hsp 0 (Nat.zero_le n)
    rw [Set.inter_eq_left.mpr hs] at h
    exact h.trans (matrixFiltration_zero M)
  have hd : d = Module.finrank k M := by
    rw [← hMspan, finrank_span_set_eq_ncard hli]
    exact ((Set.ncard_eq_toFinset_card' s).trans (Set.toFinset_card s)).symm
  exact ⟨d, exponentialPoints hM b hb, hd, exponentialPoints_image hM b hb hb' hspan⟩

private theorem factorsThroughPoints {F G J : TestAlgebra k ⥤ GrpCat.{u}}
    (f : F ⟶ J) (e : G ⟶ J) (hi : ∀ R, Function.Injective (e.app R))
    (hm : ∀ R (x : F.obj R), f.app R x ∈ Set.range (e.app R)) :
    ∃ g : F ⟶ G, g ≫ e = f := by
  classical
  let lift (R) (x : F.obj R) := Classical.choose (hm R x)
  have hl R (x : F.obj R) : e.app R (lift R x) = f.app R x :=
    Classical.choose_spec (hm R x)
  let g : F ⟶ G :=
    { app := fun R ↦ GrpCat.ofHom
        { toFun := lift R
          map_one' := hi R (by rw [hl, map_one, map_one])
          map_mul' := fun x y ↦ hi R (by
            rw [hl, map_mul (ConcreteCategory.hom (e.app R)), hl, hl, map_mul]) }
      naturality := by
        intro R S a
        apply GrpCat.ext
        intro x
        apply hi S
        change e.app S (lift S (F.map a x)) = e.app S (G.map a (lift R x))
        rw [hl]
        have he := ConcreteCategory.congr_hom (e.naturality a) (lift R x)
        have hf := ConcreteCategory.congr_hom (f.naturality a) x
        change e.app S (G.map a (lift R x)) = J.map a (e.app R (lift R x)) at he
        change f.app S (F.map a x) = J.map a (f.app R x) at hf
        rw [he, hl, hf] }
  refine ⟨g, ?_⟩
  apply NatTrans.ext
  funext R
  apply GrpCat.ext
  exact hl R

open private isReduced_of_smooth_algebra from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SmoothnessCriteria

set_option maxHeartbeats 1000000 in
theorem killedByPVectorEmbedding :
    KilledByPVectorEmbedding.{u} := by
  intro k _ p _ _ H _ _ hu hc hp
  obtain ⟨A, ⟨i⟩, huA⟩ := hu
  let HA := ((affineHopfSpec k).obj (op A)).val
  have hi : IsIso i.hom.hom.hom.left := by
    change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map i.hom)
    infer_instance
  have hs : Smooth HA.X.hom := by
    rw [← Over.w i.hom.hom.hom]
    infer_instance
  let hA : Algebra.Smooth k A := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k A))) at hs
    exact (RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp hs))
  let : Algebra.FiniteType k A := inferInstance
  let : _root_.IsReduced (AlgebraicClosure k ⊗[k] A) :=
    isReduced_of_smooth_algebra (AlgebraicClosure k) _
  have hunit : EmbedsUnitriangular H :=
    (unipotenceCriteria H A i).2.2.1.mp ((unipotenceCriteria H A i).2.1.mp huA)
  obtain ⟨n, N, ⟨j⟩, f, hf⟩ := hunit
  obtain ⟨c, _⟩ := hopfSpecPoints k
  let a := c A ≪≫ (groupPointsFunctor k).mapIso i
  let fU := (groupPointsFunctor k).map f ≫ j.hom
  let ρ := a.hom ≫ fU
  have ha (R : TestAlgebra k) : Function.Injective (a.hom.app R) := by
    intro x y hxy
    have h (z : (convolutionPoints A).obj R) : a.inv.app R (a.hom.app R z) = z :=
      ConcreteCategory.congr_hom (NatTrans.congr_app a.hom_inv_id R) z
    rw [← h x, ← h y, hxy]
  have hcA (R : TestAlgebra k) (x y : (convolutionPoints A).obj R) : Commute x y := by
    apply ha R
    rw [map_mul, map_mul]
    exact (hc R _ _).eq
  have hpA (R : TestAlgebra k) (x : (convolutionPoints A).obj R) : x ^ p = 1 := by
    apply ha R
    rw [map_pow, map_one, hp]
  let M := coordinateSpan (k := k) (universalDifference ρ)
  obtain ⟨d, e, _, he⟩ := truncatedExponentialIsomorphism p n M (coordinateSpanNilAlgebra p A n ρ hcA hpA)
  have hfactor (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj H.val).obj R) :
      fU.app R x ∈ Set.range (e.app R) := by
    let y := a.inv.app R x
    have hxy : a.hom.app R y = x := by
      exact ConcreteCategory.congr_hom (NatTrans.congr_app a.inv_hom_id R) x
    rw [(he R).2]
    change (fU.app R x).val.val - 1 ∈ extendMatrixSpan R M
    rw [← hxy]
    change pointMatrix ρ R (toConv y.ofConv) - 1 ∈ extendMatrixSpan R M
    rw [← universalDifference_map]
    exact coordinateEvaluationMem _ _
  obtain ⟨gP, hgP⟩ := factorsThroughPoints fU e (fun R ↦ (he R).1) hfactor
  let V := StandardGroups.additivePowerGroup k (Index.{u} d)
  let σ := StandardGroups.additivePowerGroupPointsIso k (Index.{u} d)
  obtain ⟨g, hg⟩ := (groupHomComparison k H.val V.val H.property.1).2 (gP ≫ σ.inv)
  obtain ⟨E, hE⟩ := (groupHomComparison k V.val N.val V.property.1).2 (σ.hom ≫ e ≫ j.inv)
  have hcomp : g ≫ E = f := by
    apply (groupHomComparison k H.val N.val H.property.1).1
    change (groupPointsFunctor k).map g = _ at hg
    change (groupPointsFunctor k).map E = _ at hE
    change (groupPointsFunctor k).map (g ≫ E) = (groupPointsFunctor k).map f
    rw [Functor.map_comp, hg, hE]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hgP]
    simp [fU]
  have hsep : IsSeparated E.hom.hom.left := by
    let : IsAffine V.val.X.left := V.property.1
    let : IsAffine N.val.X.left := N.property.1
    infer_instance
  have hi' : IsClosedImmersion (g.hom.hom.left ≫ E.hom.hom.left) := by
    change IsClosedImmersion (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map g ≫
      ((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map E)
    rw [← Functor.map_comp, hcomp]
    exact hf
  exact ⟨d, V, ⟨σ⟩, g, IsClosedImmersion.of_comp g.hom.hom.left E.hom.hom.left⟩

end LinearAlgebraicGroups.Unipotent
