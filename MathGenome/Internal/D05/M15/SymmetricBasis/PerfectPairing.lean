import MathGenome.Internal.Specs.D05.M15.SymmetricBasis.PerfectPairing
import MathGenome.Internal.D05.M15.SymmetricBasis
import MathGenome.Internal.D05.M07.DualBasis
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
open scoped Classical
/-! Permanent pairing on symmetric powers (paper.tex:3015–3024).

The tensor evaluation sum descends by the two proved symmetric universal
properties. Occurrence words identify the upstream monomial basis, and the
stabilizer of their label map counts the diagonal factorials. Integer factorial
divisibility makes every diagonal entry a unit under the stated hypothesis.
This proves both duality maps bijective, without choosing or assuming a
nondegenerate pairing. Nullary and positive-characteristic cases are explicit.
-/
namespace D05.M15.SymmetricBasis.PerfectPairing
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis.PerfectPairing
open D05.Foundations

universe u v
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

/-- The unnormalized sum of tensor evaluations, before passing to quotients. -/
def tensorPairing (p : ℕ) :
    TensorPower K p (Module.Dual K V) →ₗ[K] TensorPower K p V →ₗ[K] K :=
  ∑ σ : Equiv.Perm (Fin p),
    (PiTensorProduct.dualDistrib (R := K) (M := fun _ : Fin p => V)).compl₂
      (PiTensorProduct.reindex K (fun _ : Fin p => V) σ.symm).toLinearMap

@[simp] theorem tensorPairing_tprod (p : ℕ) (φ : Fin p → Module.Dual K V)
    (x : Fin p → V) :
    tensorPairing p (PiTensorProduct.tprod K φ) (PiTensorProduct.tprod K x) =
      permanent φ x := by
  simp [tensorPairing, permanent, PiTensorProduct.reindex_tprod]

/-- Reindex the summation permutations on the vector side. -/
theorem permanent_right {p : ℕ} (φ : Fin p → Module.Dual K V) (x : Fin p → V)
    (τ : Equiv.Perm (Fin p)) : permanent φ (x ∘ τ) = permanent φ x := by
  unfold permanent
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)

/-- Reindex both the product and the summation on the functional side. -/
theorem permanent_left {p : ℕ} (φ : Fin p → Module.Dual K V) (x : Fin p → V)
    (τ : Equiv.Perm (Fin p)) : permanent (φ ∘ τ) x = permanent φ x := by
  unfold permanent
  apply Fintype.sum_equiv (Equiv.mulRight τ.symm)
  intro σ
  change (∏ i, φ (τ i) (x (σ i))) = ∏ i, φ i (x (σ (τ.symm i)))
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp τ (fun j => φ j (x (σ (τ.symm j)))))

/-- Elementary tensors suffice to check a linear map out of either quotient. -/
theorem power_ext {W : Type*} [AddCommGroup W] [Module K W] (p : ℕ)
    {f g : symmetricPower K V p →ₗ[K] W}
    (h : ∀ x, f (elementary K V p x) = g (elementary K V p x)) : f = g := by
  have ht : f.comp (adjacentRelations K V p).mkQ = g.comp (adjacentRelations K V p).mkQ := by
    apply PiTensorProduct.ext
    exact MultilinearMap.ext h
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (adjacentRelations K V p).mkQ_surjective x
  exact LinearMap.congr_fun ht x

theorem tensorPairing_left_relations (p : ℕ) :
    adjacentRelations K (Module.Dual K V) p ≤ (tensorPairing (K := K) (V := V) p).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨φ,i,j,_,rfl⟩
  apply LinearMap.mem_ker.mpr
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change tensorPairing p (PiTensorProduct.tprod K φ -
    PiTensorProduct.tprod K (φ ∘ Equiv.swap i j)) (PiTensorProduct.tprod K x) = 0
  rw [map_sub, LinearMap.sub_apply, tensorPairing_tprod, tensorPairing_tprod]
  exact sub_eq_zero.mpr (permanent_left φ x (Equiv.swap i j)).symm

theorem tensorPairing_right_relations (p : ℕ) :
    adjacentRelations K V p ≤ (tensorPairing (K := K) (V := V) p).flip.ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,i,j,_,rfl⟩
  apply LinearMap.mem_ker.mpr
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro φ
  change tensorPairing p (PiTensorProduct.tprod K φ) (PiTensorProduct.tprod K x -
    PiTensorProduct.tprod K (x ∘ Equiv.swap i j)) = 0
  rw [map_sub, tensorPairing_tprod, tensorPairing_tprod]
  exact sub_eq_zero.mpr (permanent_right φ x (Equiv.swap i j)).symm

/-- The vector-slot universal property, with tensor functionals as target. -/
theorem right_descent_exists (p : ℕ) :
    ∃! L : symmetricPower K V p →ₗ[K] TensorPower K p (Module.Dual K V) →ₗ[K] K,
      ∀ x, L (elementary K V p x) = (tensorPairing p).flip (PiTensorProduct.tprod K x) := by
  apply (D05.M15.Symmetric.power_universal p
    ((tensorPairing (K := K) (V := V) p).flip.compMultilinearMap
      (PiTensorProduct.tprod K))).mp
  intro x σ
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro φ
  change tensorPairing p (PiTensorProduct.tprod K φ) (PiTensorProduct.tprod K (x ∘ σ)) =
    tensorPairing p (PiTensorProduct.tprod K φ) (PiTensorProduct.tprod K x)
  rw [tensorPairing_tprod, tensorPairing_tprod, permanent_right]

def rightDescent (p : ℕ) :
    symmetricPower K V p →ₗ[K] TensorPower K p (Module.Dual K V) →ₗ[K] K :=
  Classical.choose (right_descent_exists (K := K) (V := V) p)

theorem rightDescent_elementary (p : ℕ) (x : Fin p → V) (φ : Fin p → Module.Dual K V) :
    rightDescent (K := K) (V := V) p (elementary K V p x) (PiTensorProduct.tprod K φ) = permanent φ x := by
  have h := (Classical.choose_spec (right_descent_exists (K := K) (V := V) p)).1 x
  exact (LinearMap.congr_fun h (PiTensorProduct.tprod K φ)).trans (tensorPairing_tprod p φ x)

/-- The functional-slot universal property completes the bilinear descent. -/
theorem pairing_exists (p : ℕ) :
    ∃! P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K,
      ∀ φ, P (elementary K (Module.Dual K V) p φ) =
        (rightDescent (K := K) (V := V) p).flip (PiTensorProduct.tprod K φ) := by
  apply (D05.M15.Symmetric.power_universal p
    ((rightDescent (K := K) (V := V) p).flip.compMultilinearMap
      (PiTensorProduct.tprod K))).mp
  intro φ σ
  apply power_ext
  intro x
  change rightDescent (K := K) (V := V) p (elementary K V p x) (PiTensorProduct.tprod K (φ ∘ σ)) =
    rightDescent (K := K) (V := V) p (elementary K V p x) (PiTensorProduct.tprod K φ)
  rw [rightDescent_elementary, rightDescent_elementary, permanent_left]

/-- Canonical bilinear permanent pairing in every characteristic and dimension. -/
def pairing (p : ℕ) :
    symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K :=
  Classical.choose (pairing_exists (K := K) (V := V) p)

theorem pairing_elementary (p : ℕ) : IsPermanentPairing (K := K) (V := V) p (pairing p) := by
  intro φ x
  have h := (Classical.choose_spec (pairing_exists (K := K) (V := V) p)).1 φ
  exact (LinearMap.congr_fun h (elementary K V p x)).trans (rightDescent_elementary p x φ)

theorem exists_unique_pairing : Specs.D05.M15.SymmetricBasis.PerfectPairing.exists_unique_pairing := by
  intro K V _ _ _ p
  refine ⟨pairing p, pairing_elementary p, ?_⟩
  intro P hP
  apply power_ext
  intro φ
  apply power_ext
  intro x
  exact (hP φ x).trans (pairing_elementary p φ x).symm

theorem permanent_multilinear_symmetric :
    Specs.D05.M15.SymmetricBasis.PerfectPairing.permanent_multilinear_symmetric := by
  intro K V _ _ _ p
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨((tensorPairing p).flip (PiTensorProduct.tprod K x)).compMultilinearMap
      (PiTensorProduct.tprod K), fun φ => tensorPairing_tprod p φ x⟩
  · intro φ
    exact ⟨(tensorPairing p (PiTensorProduct.tprod K φ)).compMultilinearMap
      (PiTensorProduct.tprod K), fun x => tensorPairing_tprod p φ x⟩
  · intro φ x σ τ
    rw [permanent_left, permanent_right]

/-- Label the p occurrences in a monomial by their generator indices.
The order of the occurrences is immaterial in the quotient. -/
def wordEquiv {n p : ℕ} (a : NonnegativeTuples n p) :
    (Σ i : Fin n, Fin (a.val i)) ≃ Fin p :=
  Fintype.equivFinOfCardEq (by simpa using a.property)

def wordIndex {n p : ℕ} (a : NonnegativeTuples n p) : Fin p → Fin n :=
  fun j => ((wordEquiv a).symm j).1

@[simp] theorem wordIndex_card {n p : ℕ} (a : NonnegativeTuples n p) (i : Fin n) :
    Fintype.card {j : Fin p // wordIndex a j = i} = a.val i := by
  let e : {j : Fin p // wordIndex a j = i} ≃ Fin (a.val i) :=
    (Equiv.subtypeEquiv (wordEquiv a).symm (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype i)
  simpa using Fintype.card_congr e

theorem wordIndex_prod {A : Type*} [CommMonoid A] {n p : ℕ}
    (a : NonnegativeTuples n p) (f : Fin n → A) :
    ∏ j, f (wordIndex a j) = ∏ i, f i ^ a.val i := by
  calc
    _ = ∏ j : (Σ i : Fin n, Fin (a.val i)), f j.1 :=
      (Equiv.prod_comp (wordEquiv a).symm (fun j => f j.1))
    _ = _ := by simp [Fintype.prod_sigma]

/-- The occurrence word represents precisely the upstream ordinary monomial. -/
theorem monomialBasis_word {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p : ℕ) (a : NonnegativeTuples n p) :
    monomialBasis b p a = elementary K V p (b ∘ wordIndex a) := by
  apply inclusion_injective p
  rw [monomialBasis_inclusion, inclusion_elementary]
  exact (wordIndex_prod a (fun i => _root_.SymmetricAlgebra.ι K V (b i))).symm

/-- Matching permutations have the same cardinalities in every index fiber. -/
theorem wordIndex_eq_of_match {n p : ℕ} (a c : NonnegativeTuples n p)
    (σ : Equiv.Perm (Fin p)) (h : wordIndex c ∘ σ = wordIndex a) : a = c := by
  apply Subtype.ext
  funext i
  rw [← wordIndex_card a i, ← wordIndex_card c i, ← h]
  exact Fintype.card_congr (Equiv.subtypeEquiv σ (fun _ => Iff.rfl))

/-- The Kronecker product is the indicator of matching all occurrence labels. -/
theorem basis_product {n p : ℕ} (b : Module.Basis (Fin n) K V)
    (f g : Fin p → Fin n) (σ : Equiv.Perm (Fin p)) :
    (∏ i, b.dualBasis (f i) (b (g (σ i)))) = if g ∘ σ = f then 1 else 0 := by
  simp only [Module.Basis.dualBasis_apply, Module.Basis.repr_self_apply]
  by_cases h : g ∘ σ = f
  · have hi (i) : f i = g (σ i) := (congrFun h i).symm
    simp [h, hi]
  · have hi : ∃ i, f i ≠ g (σ i) := by
      by_contra hn
      push Not at hn
      exact h (funext (fun i => (hn i).symm))
    obtain ⟨i, hi⟩ := hi
    rw [ite_eq_right h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Ne.symm hi]

/-- Compute the permanent on every pair of ordinary monomials. -/
theorem monomialBasis_pairing {n : ℕ} (b : Module.Basis (Fin n) K V) (p : ℕ)
    (P : symmetricPower K (Module.Dual K V) p →ₗ[K] symmetricPower K V p →ₗ[K] K)
    (hP : IsPermanentPairing p P) (a c : NonnegativeTuples n p) :
    P (monomialBasis b.dualBasis p a) (monomialBasis b p c) =
      if a = c then ((∏ i, (a.val i).factorial : ℕ) : K) else 0 := by
  rw [monomialBasis_word, monomialBasis_word, hP]
  simp only [permanent, Function.comp_apply]
  simp_rw [basis_product]
  by_cases hac : a = c
  · subst c
    rw [ite_eq_left rfl, Finset.sum_boole, ← Fintype.card_subtype]
    rw [DomMulAct.stabilizer_card]
    simp only [wordIndex_card]
  · rw [ite_eq_right hac]
    apply Finset.sum_eq_zero
    intro σ _
    exact ite_eq_right (fun h => hac (wordIndex_eq_of_match a c σ h))

theorem monomial_values : Specs.D05.M15.SymmetricBasis.PerfectPairing.monomial_values := by
  intro K V _ _ _ n b p P hP a c α x hα hx
  have eα : α = monomialBasis b.dualBasis p a :=
    inclusion_injective p (hα.trans (monomialBasis_inclusion b.dualBasis p a).symm)
  have ex : x = monomialBasis b p c :=
    inclusion_injective p (hx.trans (monomialBasis_inclusion b p c).symm)
  rw [eα, ex]
  exact monomialBasis_pairing b p P hP a c

theorem diagonal_isUnit : Specs.D05.M15.SymmetricBasis.PerfectPairing.diagonal_isUnit := by
  intro K _ n p hp a
  have hd : (∏ i, (a.val i).factorial) ∣ p.factorial := by
    simpa only [a.property] using Nat.prod_factorial_dvd_factorial_sum Finset.univ a.val
  obtain ⟨m, hm⟩ := hd
  have hprod : IsUnit (((∏ i, (a.val i).factorial : ℕ) : K) * (m : K)) := by
    simpa only [← Nat.cast_mul, ← hm] using hp
  exact isUnit_of_mul_isUnit_left hprod

/-- Finite-dimensional duality for a matrix with invertible diagonal entries. -/
theorem perfect_of_diagonal {I A B : Type*} [Finite I]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    (a : Module.Basis I K A) (b : Module.Basis I K B)
    (P : A →ₗ[K] B →ₗ[K] K) (w : I → K) (hw : ∀ i, w i ≠ 0)
    (hP : ∀ i j, P (a i) (b j) = if i = j then w i else 0) : IsPerfect P := by
  let := Fintype.ofFinite I
  let := a.finiteDimensional_of_finite
  let := b.finiteDimensional_of_finite
  have ha (i : I) : P.flip (b i) = w i • a.coord i := by
    apply a.ext
    intro j
    change P (a j) (b i) = w i * a.repr (a j) i
    rw [hP, a.repr_self_apply]
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  have hb (i : I) : P (a i) = w i • b.coord i := by
    apply b.ext
    intro j
    change P (a i) (b j) = w i * b.repr (b j) i
    rw [hP, b.repr_self_apply]
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  have hinj : Function.Injective P := by
    intro x y hxy
    apply a.ext_elem
    intro i
    have h := LinearMap.congr_fun hxy (b i)
    change P.flip (b i) x = P.flip (b i) y at h
    rw [ha] at h
    exact (mul_left_cancel₀ (hw i)) h
  have hinj' : Function.Injective P.flip := by
    intro x y hxy
    apply b.ext_elem
    intro i
    have h := LinearMap.congr_fun hxy (a i)
    change P (a i) x = P (a i) y at h
    rw [hb] at h
    exact (mul_left_cancel₀ (hw i)) h
  have hd : Module.finrank K A = Module.finrank K B := by
    rw [Module.finrank_eq_card_basis a, Module.finrank_eq_card_basis b]
  constructor
  · exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := K)).symm)).mp hinj⟩
  · exact ⟨hinj', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.symm.trans (Subspace.dual_finrank_eq (K := K)).symm)).mp hinj'⟩

/-- Each exponent is bounded by the total degree, including degree zero. -/
theorem tuples_finite (n p : ℕ) : Finite (NonnegativeTuples n p) := by
  let f : NonnegativeTuples n p → (Fin n → Fin (p+1)) := fun a i =>
    ⟨a.val i, Nat.lt_succ_of_le (by
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (a.val j))
        (Finset.mem_univ i)
      exact h.trans_eq a.property)⟩
  apply Finite.of_injective f
  intro a c h
  apply Subtype.ext
  funext i
  exact congrArg Fin.val (congrFun h i)

theorem perfect : Specs.D05.M15.SymmetricBasis.PerfectPairing.perfect := by
  intro K V _ _ _ _ p hp P hP
  let b := Module.finBasis K V
  let := tuples_finite (Module.finrank K V) p
  exact perfect_of_diagonal (monomialBasis b.dualBasis p) (monomialBasis b p) P
    (fun a => ((∏ i, (a.val i).factorial : ℕ) : K))
    (fun a => (diagonal_isUnit _ _ hp a).ne_zero)
    (monomialBasis_pairing b p P hP)

theorem characteristic_zero : Specs.D05.M15.SymmetricBasis.PerfectPairing.characteristic_zero := by
  intro K V _ _ _ _ _ p P hP
  exact perfect p (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p))) P hP

theorem degree_zero : Specs.D05.M15.SymmetricBasis.PerfectPairing.degree_zero := by
  intro K V _ _ _ P hP E F hE hF α x
  let Q := (LinearMap.mul K K).compl₁₂ E.toLinearMap F.toLinearMap
  have heq : P = Q := by
    apply power_ext
    intro φ
    apply power_ext
    intro y
    change P (elementary K (Module.Dual K V) 0 φ) (elementary K V 0 y) =
      E (elementary K (Module.Dual K V) 0 φ) * F (elementary K V 0 y)
    rw [hP, hE, hF]
    simp [permanent]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq α) x

theorem degree_zero_scalar : Specs.D05.M15.SymmetricBasis.PerfectPairing.degree_zero_scalar := by
  intro K V _ _ _ P hP
  obtain ⟨E, hE⟩ := D05.M15.Symmetric.degree_zero (K := K) (V := Module.Dual K V)
  obtain ⟨F, hF⟩ := D05.M15.Symmetric.degree_zero (K := K) (V := V)
  exact ⟨E, F, hE, hF, degree_zero P hP E F hE hF⟩

/-- For repeated copies of one functional, every permutation gives the same
product. This holds before any characteristic restriction. -/
theorem permanent_constant {p : ℕ} (φ : Module.Dual K V) (x : Fin p → V) :
    permanent (fun _ => φ) x = (p.factorial : K) * ∏ i, φ (x i) := by
  unfold permanent
  have h (σ : Equiv.Perm (Fin p)) : (∏ i, φ (x (σ i))) = ∏ i, φ (x i) :=
    Equiv.prod_comp σ (fun i => φ (x i))
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem characteristic_failure :
    Specs.D05.M15.SymmetricBasis.PerfectPairing.characteristic_failure := by
  intro K _ ℓ _ hℓ P hP
  have hfac : (ℓ.factorial : K) = 0 :=
    (CharP.cast_eq_zero_iff K ℓ ℓ.factorial).mpr (Nat.dvd_factorial hℓ le_rfl)
  let α := elementary K (Module.Dual K K) ℓ (fun _ => (LinearMap.id : K →ₗ[K] K))
  have hz : P α = 0 := by
    apply power_ext
    intro x
    change P (elementary K (Module.Dual K K) ℓ (fun _ => LinearMap.id))
      (elementary K K ℓ x) = 0
    rw [hP, permanent_constant, hfac, zero_mul]
  have hα : α ≠ 0 := by
    let L := _root_.SymmetricAlgebra.lift (Module.Dual.eval K K 1)
    have h : L (powerInclusion (K := K) (V := Module.Dual K K) ℓ α) = 1 := by
      rw [show α = elementary K (Module.Dual K K) ℓ (fun _ => LinearMap.id) from rfl,
        inclusion_elementary, map_prod]
      simp [L]
    intro heq
    rw [heq, map_zero, map_zero] at h
    exact zero_ne_one h
  constructor
  · exact LinearMap.congr_fun hz (elementary K K ℓ (fun _ => 1))
  · intro hinj
    exact hα (hinj (hz.trans (map_zero P).symm))

end D05.M15.SymmetricBasis.PerfectPairing
