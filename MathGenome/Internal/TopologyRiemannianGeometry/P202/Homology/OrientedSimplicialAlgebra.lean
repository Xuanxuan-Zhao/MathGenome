import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.OrientedSimplicialAlgebra
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Batteries.Tactic.OpenPrivate

set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open scoped TensorProduct
universe u v w w'
open private P202Specs.OrientedSimplicialAlgebra.differential
  P202Specs.OrientedSimplicialAlgebra.faceMap
  P202Specs.OrientedSimplicialAlgebra.differential_squared
  from MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.OrientedSimplicialAlgebra

namespace P202.OrientedSimplicialAlgebra
open P202.Cellular P202Specs.OrientedSimplicialAlgebra
attribute [local instance] vertexOrder
variable {V : Type w} {K : AbstractSimplicialComplex V}
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

 theorem oriented_repeated {n : ℕ} (s : VertexTuple K n)
    (hs : ¬ Function.Injective s.1) (a : A) : oriented A s a = 0 := by
  simp [oriented, hs]

 theorem sorted_permute {n : ℕ} (s : VertexTuple K n)
    (hs : Function.Injective s.1) (σ : Equiv.Perm (Fin (n+1))) :
    sorted (permute s σ) (hs.comp σ.injective) = sorted s hs := by
  apply Subtype.ext
  apply DFunLike.ext
  intro i
  exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := s.1) (σ := σ)) i

 theorem sort_permute {n : ℕ} (s : VertexTuple K n)
    (hs : Function.Injective s.1) (σ : Equiv.Perm (Fin (n+1))) :
    σ * Tuple.sort (s.1 ∘ σ) = Tuple.sort s.1 := by
  apply Equiv.ext
  intro i
  apply hs
  exact congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := s.1) (σ := σ)) i

 theorem sign_sort_permute {n : ℕ} (s : VertexTuple K n)
    (hs : Function.Injective s.1) (σ : Equiv.Perm (Fin (n+1))) :
    Equiv.Perm.sign (Tuple.sort (s.1 ∘ σ)) =
      Equiv.Perm.sign σ * Equiv.Perm.sign (Tuple.sort s.1) := by
  have h : Tuple.sort (s.1 ∘ σ) = σ⁻¹ * Tuple.sort s.1 := by
    rw [← sort_permute s hs σ]
    group
  rw [h, map_mul, Equiv.Perm.sign_inv]

 theorem oriented_permute {n : ℕ} (s : VertexTuple K n)
    (σ : Equiv.Perm (Fin (n+1))) (a : A) :
    oriented A (permute s σ) a = (Equiv.Perm.sign σ : ℤ) • oriented A s a := by
  classical
  by_cases hs : Function.Injective s.1
  · have hperm : Function.Injective (permute s σ).1 := hs.comp σ.injective
    rw [oriented, dite_eq_left hperm, oriented, dite_eq_left hs,
        sorted_permute s hs σ]
    simp only [permute, sign_sort_permute s hs σ, Units.val_mul, mul_smul]
  · have hsp : ¬ Function.Injective (permute s σ).1 := by
      intro h
      exact hs (by simpa [permute, Function.comp_def] using h.comp σ.symm.injective)
    simp [oriented, hs, hsp]

 theorem oriented_increasing {n : ℕ} (s : Simplex K n) (a : A) :
    oriented A ⟨s.1, s.2⟩ a = Finsupp.single s a := by
  classical
  have hsort : Tuple.sort (s.1 : Fin (n+1) → V) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr s.1.monotone
  have hsorted : sorted (⟨s.1, s.2⟩ : VertexTuple K n) s.1.injective = s := by
    apply Subtype.ext
    apply DFunLike.ext
    intro i
    simp [sorted, hsort]
  simp [oriented, s.1.injective, hsort, hsorted]

 theorem boundary_single (n : ℕ) (s : Simplex K (n+1)) (a : A) :
    boundary R A n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (face i s) a := by
  classical
  simp [boundary, LinearMap.sum_apply, LinearMap.smul_apply]

 theorem face_comp {n : ℕ} (i : Fin (n+3)) (j : Fin (n+2))
    (h : i ≤ j.castSucc) :
    face (K := K) (i.castLT (Nat.lt_of_le_of_lt h j.is_lt)) ∘ face j.succ =
      face j ∘ face i := by
  funext s
  apply Subtype.ext
  apply DFunLike.ext
  intro k
  change s.1 (j.succ.succAbove ((i.castLT _).succAbove k)) =
    s.1 (i.succAbove (j.succAbove k))
  congr 1
  exact congrArg (fun f : SimplexCategory.mk n ⟶ SimplexCategory.mk (n+2) => f k)
    (SimplexCategory.δ_comp_δ'' h)

 theorem pushforward_single {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) (s : Simplex K n) (a : A) :
    pushforward R A f n (Finsupp.single s a) =
      oriented A (f.imageTuple ⟨s.1, s.2⟩) a := by
  classical
  rw [pushforward, Finsupp.lsum_single]
  rfl

 theorem pushforward_collapse {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) (s : Simplex K n)
    (hs : ¬ Function.Injective (f.vertices ∘ s.1)) (a : A) :
    pushforward R A f n (Finsupp.single s a) = 0 := by
  rw [pushforward_single]
  exact oriented_repeated A _ hs a

/-- The permutation induced after deleting position `i` and its image. -/
private def minorPerm {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    Equiv.Perm (Fin (n+1)) :=
  (Equiv.Perm.decomposeFin' (σ * i.cycleRange.symm)).2

private theorem minorPerm_decompose {n : ℕ} (σ : Equiv.Perm (Fin (n+2)))
    (i : Fin (n+2)) :
    Equiv.Perm.decomposeFin'Symm (σ i) (minorPerm σ i) = σ * i.cycleRange.symm := by
  have h := Equiv.Perm.decomposeFin'.symm_apply_apply (σ * i.cycleRange.symm)
  change Equiv.Perm.decomposeFin'Symm _ _ = _ at h
  have h0 : (Equiv.Perm.decomposeFin' (σ * i.cycleRange.symm)).1 = σ i := by
    have hh := congrArg (fun e : Equiv.Perm (Fin (n+2)) => e 0) h
    simpa only [Equiv.Perm.decomposeFin'Symm_zero, Equiv.Perm.mul_apply,
      Fin.cycleRange_symm_zero] using hh
  simpa only [minorPerm, h0] using h

private theorem minorPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin (n+2)))
    (i : Fin (n+2)) (j : Fin (n+1)) :
    (σ i).succAbove (minorPerm σ i j) = σ (i.succAbove j) := by
  have h := congrArg (fun e : Equiv.Perm (Fin (n+2)) => e j.succ)
    (minorPerm_decompose σ i)
  simpa using h

private theorem minorPerm_sign {n : ℕ} (σ : Equiv.Perm (Fin (n+2)))
    (i : Fin (n+2)) :
    (-1 : ℤ)^i.val * (Equiv.Perm.sign (minorPerm σ i) : ℤ) =
      (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ)^(σ i).val := by
  have h := congrArg (fun e : Equiv.Perm (Fin (n+2)) => (Equiv.Perm.sign e : ℤ))
    (minorPerm_decompose σ i)
  simp only [Equiv.Perm.sign_decomposeFin'Symm, map_mul, Equiv.Perm.sign_symm,
    Fin.sign_cycleRange, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one] at h
  have hi : ((-1 : ℤ)^i.val)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp only [neg_one_sq, one_pow]
  have hj : ((-1 : ℤ)^(σ i).val)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp only [neg_one_sq, one_pow]
  linear_combination (-1 : ℤ)^i.val * (-1 : ℤ)^(σ i).val * h -
    (-1 : ℤ)^i.val * (Equiv.Perm.sign (minorPerm σ i) : ℤ) * hj +
    (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ)^(σ i).val * hi

private theorem tupleFace_permute {n : ℕ} (s : VertexTuple K (n+1))
    (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    tupleFace i (permute s σ) = permute (tupleFace (σ i) s) (minorPerm σ i) := by
  apply Subtype.ext
  funext j
  exact congrArg s.1 (minorPerm_apply σ i j).symm

private theorem signed_face_permute {n : ℕ} (s : VertexTuple K (n+1))
    (σ : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) (a : A) :
    (-1 : ℤ)^i.val • oriented A (tupleFace i (permute s σ)) a =
      (Equiv.Perm.sign σ : ℤ) •
        ((-1 : ℤ)^(σ i).val • oriented A (tupleFace (σ i) s) a) := by
  rw [tupleFace_permute, oriented_permute, ← mul_smul, minorPerm_sign, mul_smul]

private theorem face_sum_permute {n : ℕ} (s : VertexTuple K (n+1))
    (σ : Equiv.Perm (Fin (n+2))) (a : A) :
    (∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i (permute s σ)) a) =
      (Equiv.Perm.sign σ : ℤ) •
        ∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a := by
  simp_rw [signed_face_permute]
  rw [← Finset.smul_sum]
  exact congrArg (fun x : Chains K A n => (Equiv.Perm.sign σ : ℤ) • x)
    (Equiv.sum_comp σ (fun i => (-1 : ℤ)^i.val • oriented A (tupleFace i s) a))

private theorem sign_smul_sign (σ : Equiv.Perm (Fin n))
    {M : Type*} [AddCommGroup M] (x : M) :
    (Equiv.Perm.sign σ : ℤ) • (Equiv.Perm.sign σ : ℤ) • x = x := by
  rw [← mul_smul]
  have h : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
    simp
  rw [h, one_smul]

 theorem boundary_oriented_injective {n : ℕ} (s : VertexTuple K (n+1))
    (hs : Function.Injective s.1) (a : A) :
    boundary R A n (oriented A s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a := by
  classical
  have hsface (i : Fin (n+2)) :
      tupleFace i (permute s (Tuple.sort s.1)) =
        (⟨(face i (sorted s hs)).1, (face i (sorted s hs)).2⟩ : VertexTuple K n) := by
    rfl
  rw [oriented, dite_eq_left hs, map_zsmul, boundary_single]
  have hfaces : (∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        Finsupp.single (face i (sorted s hs)) a) =
      (Equiv.Perm.sign (Tuple.sort s.1) : ℤ) •
        ∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a := by
    rw [← face_sum_permute A s (Tuple.sort s.1) a]
    simp_rw [hsface, oriented_increasing]
  rw [hfaces, sign_smul_sign]

private theorem face_repeated_away {n : ℕ} (s : VertexTuple K (n+1))
    (i j k : Fin (n+2)) (hij : i ≠ j) (hv : s.1 i = s.1 j)
    (hki : k ≠ i) (hkj : k ≠ j) :
    ¬ Function.Injective (tupleFace k s).1 := by
  obtain ⟨i', hi⟩ := Fin.exists_succAbove_eq hki.symm
  obtain ⟨j', hj⟩ := Fin.exists_succAbove_eq hkj.symm
  intro h
  apply hij
  have hh : i' = j' := h (by simpa [tupleFace, hi, hj] using hv)
  exact hi.symm.trans ((congrArg k.succAbove hh).trans hj)

 theorem boundary_oriented_repeated {n : ℕ} (s : VertexTuple K (n+1))
    (hs : ¬ Function.Injective s.1) (a : A) :
    (∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a) = 0 := by
  classical
  obtain ⟨i, j, hv, hij⟩ := Function.not_injective_iff.mp hs
  have hperm : permute s (Equiv.swap i j) = s := by
    apply Subtype.ext
    funext k
    change s.1 (Equiv.swap i j k) = s.1 k
    by_cases hki : k = i
    · subst k; simpa using hv.symm
    by_cases hkj : k = j
    · subst k; simpa using hv
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hpair := signed_face_permute A s (Equiv.swap i j) i a
  rw [hperm] at hpair
  simp only [Equiv.swap_apply_left, Equiv.Perm.sign_swap hij, Units.val_neg,
    Units.val_one, neg_one_zsmul] at hpair
  rw [Fintype.sum_eq_add i j hij]
  · rw [hpair, neg_add_cancel]
  · intro k hk
    rw [oriented_repeated A _ (face_repeated_away s i j k hij hv hk.1 hk.2), smul_zero]

 theorem boundary_oriented {n : ℕ} (s : VertexTuple K (n+1)) (a : A) :
    boundary R A n (oriented A s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • oriented A (tupleFace i s) a := by
  classical
  by_cases hs : Function.Injective s.1
  · exact boundary_oriented_injective R A s hs a
  · rw [oriented_repeated A s hs, map_zero, boundary_oriented_repeated A s hs a]

 theorem pushforward_oriented {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) {n : ℕ} (s : VertexTuple K n) (a : A) :
    pushforward R A f n (oriented A s a) = oriented A (f.imageTuple s) a := by
  classical
  by_cases hs : Function.Injective s.1
  · have htuple : f.imageTuple ⟨(sorted s hs).1, (sorted s hs).2⟩ =
        permute (f.imageTuple s) (Tuple.sort s.1) := rfl
    rw [oriented, dite_eq_left hs, map_zsmul, pushforward_single, htuple,
      oriented_permute, sign_smul_sign]
  · have himg : ¬ Function.Injective (f.imageTuple s).1 := by
      intro himg
      apply hs
      intro i j hij
      exact himg (congrArg f.vertices hij)
    rw [oriented_repeated A s hs, map_zero, oriented_repeated A _ himg]

 theorem pushforward_id (n : ℕ) :
    pushforward R A (SimplicialMap.id K) n = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro s a
  rw [pushforward_single]
  exact oriented_increasing A s a

 theorem pushforward_comp {W : Type w'} {U : Type*}
    {L : AbstractSimplicialComplex W} {M : AbstractSimplicialComplex U}
    (g : SimplicialMap (K := L) M) (f : SimplicialMap (K := K) L) (n : ℕ) :
    (pushforward R A g n).comp (pushforward R A f n) =
      pushforward R A (g.comp f) n := by
  apply Finsupp.lhom_ext
  intro s a
  change pushforward R A g n (pushforward R A f n (Finsupp.single s a)) = _
  rw [pushforward_single, pushforward_oriented, pushforward_single]
  rfl

 theorem pushforward_boundary {W : Type w'} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) :
    (boundary R A n).comp (pushforward R A f (n+1)) =
      (pushforward R A f n).comp (boundary R A n) := by
  apply Finsupp.lhom_ext
  intro s a
  change boundary R A n (pushforward R A f (n+1) (Finsupp.single s a)) =
    pushforward R A f n (boundary R A n (Finsupp.single s a))
  rw [pushforward_single, boundary_oriented, boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [pushforward_single]
  rfl

 theorem boundary_eq (n : ℕ) :
    ((complex R A (K := K)).d (n+1) n).hom = boundary R A n := by
  simp [complex, boundary, P202Specs.OrientedSimplicialAlgebra.differential,
    P202Specs.OrientedSimplicialAlgebra.faceMap]

 theorem boundary_zero (n : ℕ) : (complex R A (K := K)).d 0 n = 0 := by
  exact (complex R A (K := K)).shape 0 n (by simp [ComplexShape.down_Rel])

 theorem boundary_squared (n : ℕ) :
    (boundary R A (K := K) n).comp (boundary R A (n+1)) = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero,
    P202Specs.OrientedSimplicialAlgebra.differential, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, P202Specs.OrientedSimplicialAlgebra.faceMap,
    ModuleCat.hom_ofHom, boundary] using
    congrArg ModuleCat.Hom.hom
      (P202Specs.OrientedSimplicialAlgebra.differential_squared R A (K := K) n)

/-- The actual component maps, not just an unspecified chain map. -/
 theorem pushforward_chainMap {W : Type w} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) :
    ∃ F : complex R A (K := K) ⟶ complex R A (K := L),
      ∀ n, (F.f n).hom = pushforward R A f n := by
  refine ⟨ChainComplex.ofHom (fun n => ModuleCat.ofHom (pushforward R A f n)) ?_,
    fun _ => rfl⟩
  intro n
  apply ModuleCat.hom_ext
  change (((complex R A (K := L)).d (n+1) n).hom).comp (pushforward R A f (n+1)) =
    (pushforward R A f n).comp (((complex R A (K := K)).d (n+1) n).hom)
  rw [boundary_eq R A, boundary_eq R A]
  exact pushforward_boundary R A f n

 theorem pushforward_inclusion_single {L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) (n : ℕ) (s : Simplex K n) (a : A) :
    pushforward R A (SimplicialMap.inclusion h) n (Finsupp.single s a) =
      Finsupp.single (inclusionSimplex h s) a := by
  rw [pushforward_single]
  exact oriented_increasing A (inclusionSimplex h s) a

 theorem pushforward_inclusion_injective {L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) (n : ℕ) :
    Function.Injective (pushforward R A (SimplicialMap.inclusion h) n) := by
  have heq : pushforward R A (SimplicialMap.inclusion h) n =
      Finsupp.lmapDomain A R (inclusionSimplex h) := by
    apply Finsupp.lhom_ext
    intro s a
    rw [pushforward_inclusion_single]
    simp
  rw [heq]
  exact Finsupp.mapDomain_injective (fun s t hst => Subtype.ext (congrArg (fun x : Simplex L n => x.1) hst))

 theorem increasingBasis_apply (n : ℕ) (s : Simplex K n) :
    increasingBasis R (K := K) n s = Finsupp.single s (1 : R) := rfl

 theorem coefficientEquiv_single (n : ℕ) (s : Simplex K n) (a : A) :
    coefficientEquiv R A n (Finsupp.single s 1 ⊗ₜ[R] a) = Finsupp.single s a := by
  classical
  ext t
  simp [coefficientEquiv, Finsupp.single_apply, ite_smul]

 theorem coefficientEquiv_tmul_single (n : ℕ) (s : Simplex K n) (r : R) (a : A) :
    coefficientEquiv R A n (Finsupp.single s r ⊗ₜ[R] a) =
      Finsupp.single s (r • a) := by
  classical
  ext t
  simp [coefficientEquiv, Finsupp.single_apply, ite_smul]

 theorem coefficientEquiv_boundary (n : ℕ) (x : Chains K R (n+1) ⊗[R] A) :
    boundary R A n (coefficientEquiv R A (n+1) x) =
      coefficientEquiv R A n ((boundary R R n).rTensor A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
    | single s r =>
      rw [LinearMap.rTensor_tmul, boundary_single, coefficientEquiv_tmul_single,
        boundary_single, TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rcases neg_one_pow_eq_or ℤ i.val with hi | hi <;>
        simp [hi, TensorProduct.neg_tmul, coefficientEquiv_tmul_single]

/-- This alias fixes the actual chain complex used by downstream constructions. -/
def chainComplex : ChainComplex (ModuleCat.{max v w} R) ℕ := complex R A (K := K)

end P202.OrientedSimplicialAlgebra
