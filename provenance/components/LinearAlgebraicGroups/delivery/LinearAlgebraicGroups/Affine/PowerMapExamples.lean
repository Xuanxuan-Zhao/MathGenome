import Specs.LinearAlgebraicGroups.Affine.PowerMapExamples
import LinearAlgebraicGroups.Affine.RelativeFrobenius
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

open AlgebraicGeometry CategoryTheory LaurentPolynomial
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs.PowerMapExamples

universe u

namespace LinearAlgebraicGroups.PowerMapExamples

noncomputable section

variable {k : Type u} [Field k]

private theorem powerAlgebraHom_T (n : ℕ) (m : ℤ) :
    powerAlgebraHom k n (T m) = T ((n : ℤ) * m) := by
  exact AddMonoidAlgebra.mapDomain_single

private theorem scaleExponents_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (scaleExponents n) := by
  intro a b h
  change (n : ℤ) * a = (n : ℤ) * b at h
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne' : (n : ℤ) ≠ 0) h

private theorem powerAlgebraHom_range (n : ℕ) :
    (powerAlgebraHom k n).range =
      Algebra.adjoin k ({T (n : ℤ), T (-(n : ℤ))} : Set (LaurentPolynomial k)) := by
  let f := powerAlgebraHom k n
  let S := Algebra.adjoin k ({T (n : ℤ), T (-(n : ℤ))} : Set (LaurentPolynomial k))
  change f.range = S
  have hT : (T (n : ℤ) : LaurentPolynomial k) ∈ S := Algebra.subset_adjoin (by simp)
  have hTinv : (T (-(n : ℤ)) : LaurentPolynomial k) ∈ S :=
    Algebra.subset_adjoin (by simp)
  refine le_antisymm ?_ (Algebra.adjoin_le ?_)
  · rintro _ ⟨a, rfl⟩
    refine a.induction_on ?_ ?_ ?_ ?_
    · intro c
      change f (C c) ∈ S
      rw [C_eq_algebraMap, f.commutes]
      exact S.algebraMap_mem c
    · intro a b ha hb
      rw [map_add]
      exact S.add_mem ha hb
    · intro m c hm
      rw [T_add, ← mul_assoc, map_mul]
      exact S.mul_mem hm (by simpa [f, powerAlgebraHom_T] using hT)
    · intro m c hm
      rw [sub_eq_add_neg, T_add, ← mul_assoc, map_mul]
      exact S.mul_mem hm (by simpa [f, powerAlgebraHom_T] using hTinv)
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact ⟨T 1, by simp [f, powerAlgebraHom_T]⟩
    · exact ⟨T (-1), by simp [f, powerAlgebraHom_T]⟩

private theorem remainder_eq (n : ℕ) (i : Fin n) (q : ℤ) :
    ((n : ℤ) * q + (i : ℤ)) % (n : ℤ) = (i : ℤ) := by
  rw [Int.mul_add_emod_self_left]
  exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt)

-- The domain and codomain have the same type. Specify the module using the power
-- algebra map to avoid choosing the ordinary multiplication action.
private theorem powerBasis (n : ℕ) (hn : 0 < n) :
    letI a := (powerAlgebraHom k n).toRingHom.toAlgebra
    letI : Module (LaurentPolynomial k) (LaurentPolynomial k) := @Algebra.toModule _ _ _ _ a
    ∃ b : Module.Basis (Fin n) (LaurentPolynomial k) (LaurentPolynomial k),
      ∀ i, b i = (T 1 : LaurentPolynomial k) ^ (i : ℕ) := by
  let a := (powerAlgebraHom k n).toRingHom.toAlgebra
  let : Module (LaurentPolynomial k) (LaurentPolynomial k) := @Algebra.toModule _ _ _ _ a
  let : SMul (LaurentPolynomial k) (LaurentPolynomial k) := @Algebra.toSMul _ _ _ _ a
  let v (i : Fin n) : LaurentPolynomial k := T (i : ℤ)
  have hind : LinearIndependent (LaurentPolynomial k) v := by
    apply Fintype.linearIndependent_iff.mpr
    intro a ha i
    ext q
    let e : ℤ := (n : ℤ) * q + (i : ℤ)
    have hz := congrArg (fun x : LaurentPolynomial k => x.coeff e) ha
    simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] at hz
    have hcoeff (j : Fin n) :
        (a j • v j).coeff e =
          (Finsupp.mapDomain (scaleExponents n) (a j).coeff) (e - (j : ℤ)) := by
      change (powerAlgebraHom k n (a j) * T (j : ℤ)).coeff e = _
      rw [T, AddMonoidAlgebra.coeff_mul_single_apply, mul_one]
      rfl
    rw [Finset.sum_eq_single i] at hz
    · rw [hcoeff, show e - (i : ℤ) = scaleExponents n q by dsimp [e, scaleExponents]; omega,
        Finsupp.mapDomain_apply_of_injective (scaleExponents_injective hn)] at hz
      exact hz
    · intro j _ hji
      rw [hcoeff]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨s, hs⟩
      change (n : ℤ) * s = e - (j : ℤ) at hs
      have he : (n : ℤ) * s + (j : ℤ) = e := by omega
      apply hji
      apply Fin.ext
      have hmod := congrArg (fun x : ℤ => x % (n : ℤ)) he
      rw [remainder_eq n j s, show e % (n : ℤ) = (i : ℤ) from remainder_eq n i q] at hmod
      exact_mod_cast hmod
    · intro h
      exact (h (Finset.mem_univ i)).elim
  have hspan : ⊤ ≤ Submodule.span (LaurentPolynomial k) (Set.range v) := by
    intro a _
    refine a.induction_on' (fun _ _ => Submodule.add_mem _) fun m c => ?_
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    have hnonneg : 0 ≤ m % (n : ℤ) := Int.emod_nonneg _ hn'.ne'
    have hlt : m % (n : ℤ) < n := Int.emod_lt_of_pos _ hn'
    let i : Fin n := ⟨(m % (n : ℤ)).toNat, by omega⟩
    have hi : (i : ℤ) = m % (n : ℤ) := Int.toNat_of_nonneg hnonneg
    have he : (n : ℤ) * (m / (n : ℤ)) + (i : ℤ) = m := by
      rw [hi, Int.mul_comm, Int.ediv_mul_add_emod]
    have hm := Submodule.smul_mem (Submodule.span (LaurentPolynomial k) (Set.range v))
      (C c * T (m / (n : ℤ))) (Submodule.subset_span (Set.mem_range_self i))
    change powerAlgebraHom k n (C c * T (m / (n : ℤ))) * T (i : ℤ) ∈ _ at hm
    rw [map_mul, C_eq_algebraMap, AlgHom.commutes, ← C_eq_algebraMap, powerAlgebraHom_T,
      mul_assoc, ← T_add, he] at hm
    exact hm
  refine ⟨Module.Basis.mk hind hspan, fun i => ?_⟩
  rw [Module.Basis.mk_apply, T_pow, mul_one]

theorem powerMapFiniteFaithfullyFlat : PowerMapFiniteFaithfullyFlat.{u} := by
  intro k _ n hn
  let f := powerAlgebraHom k n
  let S := Algebra.adjoin k ({T (n : ℤ), T (-(n : ℤ))} : Set (LaurentPolynomial k))
  let M : Module S (LaurentPolynomial k) := inferInstance
  let a := f.toRingHom.toAlgebra
  let m : Module (LaurentPolynomial k) (LaurentPolynomial k) := @Algebra.toModule _ _ _ _ a
  obtain ⟨b, hb⟩ := powerBasis (k := k) n hn
  have hf : Function.Injective f :=
    AddMonoidAlgebra.mapDomain_injective (scaleExponents_injective hn)
  have hrange := powerAlgebraHom_range (k := k) n
  let e : LaurentPolynomial k ≃ₐ[k] S :=
    (AlgEquiv.ofInjective f hf).trans (Subalgebra.equivOfEq _ _ hrange)
  have hsmul (r x : LaurentPolynomial k) :
      @SMul.smul _ _ M.toSMul (e r) x = @SMul.smul _ _ m.toSMul r x := rfl
  refine ⟨hf, hrange, ⟨b.mapCoeffs e.toRingEquiv hsmul, fun i => ?_⟩, ?_⟩
  · rw [Module.Basis.mapCoeffs_apply, hb]
  let g := CommRingCat.ofHom f.toRingHom
  change IsFinite (Spec.map g) ∧ Flat (Spec.map g) ∧ Surjective (Spec.map g)
  let : Module.Free (LaurentPolynomial k) (LaurentPolynomial k) := Module.Free.of_basis b
  refine ⟨(IsFinite.SpecMap_iff g).mpr ?_, (flat_and_surjective_SpecMap_iff g).mpr ?_⟩
  · exact Module.Finite.of_basis b
  · exact (inferInstance : Module.FaithfullyFlat (LaurentPolynomial k) (LaurentPolynomial k))

theorem powerMapOnPoints : PowerMapOnPoints.{u} := by
  intro k _ n R _ _ a
  apply Units.ext
  change a (powerAlgebraHom k n _) = (a _ : R) ^ n
  rw [(isUnit_T (R := k) 1).unit_spec, powerAlgebraHom_T, mul_one]
  rw [← show (T 1 : LaurentPolynomial k) ^ n = T (n : ℤ) by rw [T_pow, mul_one], map_pow]

theorem realSquaringNotSurjective : RealSquaringNotSurjective := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  have hx' : (x.val : ℝ) ^ 2 = -1 := by
    simpa using congrArg Units.val hx
  exact (not_le_of_gt (neg_one_lt_zero : (-1 : ℝ) < 0)) (hx' ▸ sq_nonneg (x.val : ℝ))

open Specs.RelativeFrobenius in
theorem alphaIdentitySurjectiveNotFlat : AlphaIdentitySurjectiveNotFlat.{u} := by
  intro k _ p hp _
  let f := alphaIdentityPullback k p hp.out.pos
  let π := Ideal.Quotient.mk (alphaIdeal k p)
  have hf : Function.Surjective f := fun a => ⟨algebraMap k _ a, f.commutes a⟩
  have heval (a : Polynomial k) : f (π a) = a.eval 0 := by
    change Polynomial.aeval (0 : k) a = _
    exact Polynomial.aeval_def _ _ |>.trans (Polynomial.eval₂_at_apply _ _)
  have hpower : (π Polynomial.X) ^ p = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hs : Function.Surjective (PrimeSpectrum.comap f.toRingHom) := by
    let P : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
    intro Q
    refine ⟨P, PrimeSpectrum.comap_injective_of_surjective π Ideal.Quotient.mk_surjective ?_⟩
    apply PrimeSpectrum.ext
    change RingHom.ker (f.toRingHom.comp π) = Q.asIdeal.comap π
    refine (RingHom.ker_isMaximal_of_surjective (f.toRingHom.comp π)
      (hf.comp Ideal.Quotient.mk_surjective)).eq_of_le
      (Q.isPrime.comap π).ne_top ?_
    intro a ha
    change f (π a) = 0 at ha
    rw [heval, ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.X_dvd_iff] at ha
    obtain ⟨b, rfl⟩ := ha
    change π (Polynomial.X * b) ∈ Q.asIdeal
    rw [map_mul]
    exact Q.asIdeal.mul_mem_right _ (Q.isPrime.mem_of_pow_mem p (hpower ▸ Q.asIdeal.zero_mem))
  let g := CommRingCat.ofHom f.toRingHom
  have hsurj : Surjective (Spec.map g) := (surjective_iff _).mpr hs
  refine ⟨IsClosedImmersion.spec_of_surjective g hf, hsurj, fun hflat => ?_⟩
  have hinj := ((flat_and_surjective_SpecMap_iff g).mp ⟨hflat, hsurj⟩).injective
  have hx : π Polynomial.X = 0 := hinj (by
    change f (π Polynomial.X) = f 0
    rw [heval, Polynomial.eval_X, map_zero])
  have hdiv := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
  have hz := Polynomial.X_pow_dvd_iff.mp hdiv 1 hp.out.one_lt
  simp at hz

set_option backward.isDefEq.respectTransparency false in
open Specs.RelativeFrobenius in
theorem alphaIdentityInHopfPresentation : AlphaIdentityInHopfPresentation.{u} := by
  intro k _ p hp _ A e
  let f := alphaIdentityPullback k p hp.out.pos
  let c := Bialgebra.counitAlgHom k A
  obtain ⟨a, _, ha⟩ := (RelativeFrobenius.kernelFieldPoints k p k).1
  have hc : f.comp e.toAlgHom = c := by
    have h₁ := ha f trivial
    have h₂ := ha (c.comp e.symm.toAlgHom) trivial
    have h : f = c.comp e.symm.toAlgHom := h₁.trans h₂.symm
    ext x
    exact (DFunLike.congr_fun h (e x)).trans (congrArg c (e.symm_apply_apply x))
  let j := e.toRingEquiv.toCommRingCatIso
  let g := Spec.map (CommRingCat.ofHom f.toRingHom)
  let w := Spec.map (CommRingCat.ofHom c.toRingHom)
  have he : w = g ≫ Spec.map j.hom := by
    change Spec.map (CommRingCat.ofHom c.toRingHom) = _
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg (fun φ : A →ₐ[k] k => CommRingCat.ofHom φ.toRingHom) hc.symm)
  obtain ⟨hclosed, hsurj, hnotflat⟩ := alphaIdentitySurjectiveNotFlat k p
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) := by
    infer_instance
  change IsClosedImmersion w ∧ Surjective w ∧ ¬ Flat w
  rw [he,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion g (Spec.map j.hom),
    MorphismProperty.cancel_right_of_respectsIso @Surjective g (Spec.map j.hom),
    MorphismProperty.cancel_right_of_respectsIso @Flat g (Spec.map j.hom)]
  exact ⟨hclosed, hsurj, hnotflat⟩

open private additiveCoordinates from LinearAlgebraicGroups.Affine.RelativeFrobenius in
/-- The conclusion on the additive Frobenius kernel constructed in the preceding result. -/
theorem standardAlphaIdentity (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    let e := η[(RelativeFrobenius.alpha (k := k) p).X].left
    IsClosedImmersion e ∧ Surjective e ∧ ¬ Flat e := by
  let A := RelativeFrobenius.kernelHopf p (additiveCoordinates k)
  obtain ⟨_, _, _, e, _⟩ := (RelativeFrobenius.standardFrobeniusKernels (k := k) p).1
  exact alphaIdentityInHopfPresentation k p A e

open private laurentCoordinates_ext laurentEvaluation
  laurentEvaluation_T from LinearAlgebraicGroups.Affine.StandardGroups

/-- The power morphism on the multiplicative group constructed in the standard groups result. -/
def standardPowerMorphism (k : Type u) [Field k] (n : ℕ) :
    {f : (StandardGroups.multiplicativeGroup k).val ⟶ (StandardGroups.multiplicativeGroup k).val //
      f.hom.hom.left = Spec.map (CommRingCat.ofHom (powerAlgebraHom k n).toRingHom)} := by
  letI H := StandardGroups.multiplicativeHopf k
  letI : Bialgebra k (LaurentPolynomial k) := H.toBialgebra
  let A := CommHopfAlgCat.of k (LaurentPolynomial k)
  let f := powerAlgebraHom k n
  let t : LaurentPolynomial k := T 1
  have ht : f t = t ^ n := by
    dsimp [f, t]
    rw [powerAlgebraHom_T, T_pow]
  have he : Bialgebra.counitAlgHom k (LaurentPolynomial k) t = 1 := by
    change laurentEvaluation (k := k) (1 : kˣ) (T 1) = 1
    simp [laurentEvaluation_T]
  have hd : Bialgebra.comulAlgHom k (LaurentPolynomial k) t = t ⊗ₜ[k] t := by
    let u := (isUnit_T (R := k) 1).unit
    change laurentEvaluation
      (Units.map Algebra.TensorProduct.includeLeft.toMonoidHom u *
       Units.map Algebra.TensorProduct.includeRight.toMonoidHom u) t = _
    rw [show t = T 1 from rfl, laurentEvaluation_T, zpow_one]
    change Algebra.TensorProduct.includeLeft u.val * Algebra.TensorProduct.includeRight u.val = _
    rw [show u.val = T 1 from (isUnit_T (R := k) 1).unit_spec]
    simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  let b : A ⟶ A := CommHopfAlgCat.ofHom <| BialgHom.ofAlgHom f
    (laurentCoordinates_ext (by
      change Bialgebra.counitAlgHom k (LaurentPolynomial k) (f t) =
        Bialgebra.counitAlgHom k (LaurentPolynomial k) t
      simp only [ht, map_pow, he, one_pow]))
    (laurentCoordinates_ext (by
      change Algebra.TensorProduct.map f f (Bialgebra.comulAlgHom k (LaurentPolynomial k) t) =
        Bialgebra.comulAlgHom k (LaurentPolynomial k) (f t)
      simp only [ht, hd, map_pow, Algebra.TensorProduct.map_tmul,
        Algebra.TensorProduct.tmul_pow]))
  exact ⟨specGroupMap b, rfl⟩

end

end LinearAlgebraicGroups.PowerMapExamples
