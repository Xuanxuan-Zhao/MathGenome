import Specs.LinearAlgebraicGroups.Composition.QuaternionNorm
import LinearAlgebraicGroups.Composition.OrthogonalDoubling
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Etale.StandardEtale

namespace LinearAlgebraicGroups.Composition

open scoped Matrix TensorProduct QuadraticAlgebra
open QuaternionSpecification Algebra.TensorProduct
open Module (finrank)

universe u v w

/-- The cyclic quaternion algebra associated with an involution and a scalar parameter. -/
abbrev quaternionCyclicAlgebra := @QuaternionSpecification.cyclicAlgebra

/-- The element with coordinates `x + yj` in the cyclic quaternion algebra. -/
abbrev quaternionCyclicPair := @QuaternionSpecification.cyclicPair

/-- The orthogonal norm of the cyclic quaternion algebra. -/
abbrev quaternionCyclicNorm := @QuaternionSpecification.cyclicNorm

section Coordinates

variable {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
variable (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k)

theorem cyclic_pair_mul : QuaternionSpecification.cyclicProduct := by
  intro k D _ _ _ σ hσ param x y z t
  apply Subtype.ext
  change cyclicMatrix σ param x y * cyclicMatrix σ param z t =
    cyclicMatrix σ param (x * z + param • (σ t * y)) (t * x + y * σ z)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyclicMatrix, Matrix.mul_apply, Fin.sum_univ_two, hσ z, hσ t, Algebra.smul_def] <;> ring

private theorem cyclic_pair_injective :
    Function.Injective (fun xy : D × D => cyclicPair σ hσ param xy.1 xy.2) := by
  intro xy zt h
  apply Prod.ext
  · exact congrArg (fun q : cyclicAlgebra σ hσ param => (q : Matrix (Fin 2) (Fin 2) D) 0 0) h
  · apply σ.injective
    exact congrArg (fun q : cyclicAlgebra σ hσ param => (q : Matrix (Fin 2) (Fin 2) D) 1 0) h

private theorem cyclic_pair_surjective :
    Function.Surjective (fun xy : D × D => cyclicPair σ hσ param xy.1 xy.2) := by
  rintro ⟨M, x, y, rfl⟩
  exact ⟨(x, y), rfl⟩

private theorem cyclic_pair_scalar (c : k) :
    cyclicPair σ hσ param (algebraMap k D c) 0 = algebraMap k (cyclicAlgebra σ hσ param) c := by
  apply Subtype.ext
  change cyclicMatrix σ param (algebraMap k D c) 0 = algebraMap k (Matrix (Fin 2) (Fin 2) D) c
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cyclicMatrix, Matrix.algebraMap_matrix_apply]

@[simp]
private theorem cyclic_pair_one : cyclicPair σ hσ param 1 0 = 1 := by
  simpa only [map_one] using cyclic_pair_scalar σ hσ param 1

@[simp]
private theorem cyclic_pair_zero : cyclicPair σ hσ param 0 0 = 0 := by
  simpa only [map_zero] using cyclic_pair_scalar σ hσ param 0

/-- The two coordinates give the direct sum decomposition of the cyclic algebra. -/
private noncomputable def cyclicPairEquiv : (D × D) ≃ₗ[k] cyclicAlgebra σ hσ param :=
  LinearEquiv.ofBijective
    { toFun := fun xy => cyclicPair σ hσ param xy.1 xy.2
      map_add' := by
        rintro ⟨x, y⟩ ⟨z, t⟩
        apply Subtype.ext
        change cyclicMatrix σ param (x + z) (y + t) =
          cyclicMatrix σ param x y + cyclicMatrix σ param z t
        ext i j
        fin_cases i <;> fin_cases j <;> simp [cyclicMatrix, mul_add]
      map_smul' := by
        rintro c ⟨x, y⟩
        apply Subtype.ext
        change cyclicMatrix σ param (c • x) (c • y) = c • cyclicMatrix σ param x y
        ext i j
        fin_cases i <;> fin_cases j <;> simp [cyclicMatrix, Algebra.smul_def, mul_left_comm] }
    ⟨cyclic_pair_injective σ hσ param, cyclic_pair_surjective σ hσ param⟩

theorem cyclic_generators : QuaternionSpecification.cyclicGenerators := by
  intro k D _ _ _ σ hσ param
  refine ⟨cyclic_pair_one σ hσ param, ?_, ?_, ?_⟩
  · rw [pow_two, cyclic_pair_mul]
    simpa [Algebra.smul_def] using cyclic_pair_scalar σ hσ param param
  · intro x
    rw [cyclic_pair_mul, cyclic_pair_mul]
    simp
  · intro q
    obtain ⟨xy, hxy⟩ := cyclic_pair_surjective σ hσ param q
    exact ⟨xy, hxy, fun zt hzt => cyclic_pair_injective σ hσ param (hzt.trans hxy.symm)⟩

theorem composition_conjugation_automorphism : QuaternionSpecification.conjugationAutomorphism := by
  intro k D _ _ _ n hn
  have h := IsFieldCompositionNorm.toNormLaws hn
  let σ : D ≃ₐ[k] D :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.ofInvolutive (conjugate n) (conjugate_involutive h))
      (conjugate_one h) (fun x y => (conjugate_mul h x y).trans (mul_comm _ _))
  exact ⟨σ, conjugate_involutive h, fun _ => rfl⟩

@[simp]
theorem cyclic_norm_pair (n : QuadraticForm k D) (x y : D) :
    cyclicNorm n σ hσ param (cyclicPair σ hσ param x y) = n x - param * n y := by
  change n x - param * n (σ.symm (σ y)) = _
  rw [AlgEquiv.symm_apply_apply]

private theorem cyclic_finrank [Module.Finite k D] (hd : finrank k D = 2) :
    finrank k (cyclicAlgebra σ hσ param) = 4 := by
  rw [← (cyclicPairEquiv σ hσ param).finrank_eq, Module.finrank_prod, hd]

end Coordinates

section Etale

variable {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
variable {K : Type w} [Field K] [Algebra k K]
variable {n : QuadraticForm k D}

private noncomputable def etalePair [Algebra.Etale k D] [IsSepClosed K] [Module.Finite k D]
    (hd : finrank k D = 2) :
    K ⊗[k] D ≃ₐ[K] K × K := by
  classical
  let P := PrimeSpectrum (K ⊗[k] D)
  let e : K ⊗[k] D ≃ₐ[K] P → K := Algebra.FormallyEtale.equivPiOfIsSepClosed K _
  let : IsArtinianRing (K ⊗[k] D) := IsArtinianRing.of_finite K _
  let : Finite P := inferInstanceAs (Finite (PrimeSpectrum (K ⊗[k] D)))
  letI : Fintype P := Fintype.ofFinite P
  have hc : Fintype.card P = 2 := by
    rw [← Module.finrank_pi K, ← e.toLinearEquiv.finrank_eq, Module.finrank_baseChange, hd]
  let ep : P ≃ Fin 2 := Fintype.equivOfCardEq (hc.trans (Fintype.card_fin 2).symm)
  let e2 : (Fin 2 → K) ≃ₐ[K] K × K :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.piFinTwo K (fun _ => K)) rfl (fun _ _ => rfl)
  exact e.trans ((AlgEquiv.piCongrLeft K (fun _ : Fin 2 => K) ep).trans e2)

private theorem baseChange_normLaws (hn : IsFieldCompositionNorm n) :
    NormLaws (normBaseChange K n) := by
  let := hn.finite
  have hp : n.polarBilin.IsPerfPair := by
    apply LinearMap.IsPerfPair.of_injective
    · exact LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hn.nondegenerate.1)
    · rw [show n.polarBilin.flip = n.polarBilin from
          LinearMap.ext₂ fun x y => QuadraticMap.polar_comm n y x]
      exact LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hn.nondegenerate.1)
  refine ⟨?_, norm_comp_after_baseChange n hn.multiplicative K,
    (perfect_polar_normBaseChange K n hp).nondegenerate⟩
  change normBaseChange K n ((1 : K) ⊗ₜ[k] (1 : D)) = 1
  rw [normBaseChange_tmul, field_norm_one hn]
  simp

private theorem pair_conjugation (hn : IsFieldCompositionNorm n)
    (e : K ⊗[k] D ≃ₐ[K] K × K) (z : K ⊗[k] D) :
    e (conjugate (normBaseChange K n) z) = ((e z).2, (e z).1) := by
  let f := conjugate (normBaseChange K n)
  have hf := baseChange_normLaws (K := K) hn
  let p : K ⊗[k] D := e.symm (1, 0)
  have hp : e p = (1, 0) := e.apply_symm_apply _
  have hnorm := congrArg e (mul_conjugate hf p).1
  rw [map_mul, hp, Algebra.smul_def, mul_one, AlgEquiv.commutes] at hnorm
  have hzero : (e (f p)).1 = 0 := by
    have h1 := congrArg Prod.fst hnorm
    have h2 := congrArg Prod.snd hnorm
    change (1 : K) * (e (f p)).1 = normBaseChange K n p at h1
    change (0 : K) * (e (f p)).2 = normBaseChange K n p at h2
    simpa using h1.trans h2.symm
  have hone : (e (f p)).2 = 1 := by
    have hsum : e (f p) + e p =
        algebraMap K (K × K) (compositionTrace (normBaseChange K n) p) := by
      rw [← map_add, conjugate_apply, sub_add_cancel, Algebra.smul_def, mul_one, AlgEquiv.commutes]
    have h1 := congrArg Prod.fst hsum
    have h2 := congrArg Prod.snd hsum
    rw [hp] at h1 h2
    change (e (f p)).1 + 1 = compositionTrace (normBaseChange K n) p at h1
    change (e (f p)).2 + 0 = compositionTrace (normBaseChange K n) p at h2
    simpa [hzero] using h2.trans h1.symm
  have hswap : e (f p) = (0, 1) := Prod.ext hzero hone
  have hz : z = (e z).2 • (1 : K ⊗[k] D) + ((e z).1 - (e z).2) • p := by
    apply e.injective
    rw [map_add, map_smul, map_smul, hp, map_one]
    apply Prod.ext <;> simp [Prod.smul_mk, smul_eq_mul]
  have hcalc : e (f z) = (e z).2 • (1 : K × K) + ((e z).1 - (e z).2) • (0, 1) := by
    conv_lhs => rw [hz]
    rw [map_add, map_smul, map_smul, show f 1 = 1 from conjugate_one hf,
      map_add, map_smul, map_smul, map_one, hswap]
  rw [hcalc]
  apply Prod.ext <;> simp [Prod.smul_mk, smul_eq_mul]

private theorem pair_norm (hn : IsFieldCompositionNorm n)
    (e : K ⊗[k] D ≃ₐ[K] K × K) (z : K ⊗[k] D) :
    (e z).1 * (e z).2 = normBaseChange K n z := by
  have h := congrArg (fun w => (e w).1) (mul_conjugate (baseChange_normLaws (K := K) hn) z).1
  change (e (z * conjugate (normBaseChange K n) z)).1 = (e (_ • (1 : K ⊗[k] D))).1 at h
  rw [map_mul, pair_conjugation hn e, Algebra.smul_def, mul_one, AlgEquiv.commutes] at h
  exact h

private theorem pair_conjugation_tmul (hn : IsFieldCompositionNorm n)
    (e : K ⊗[k] D ≃ₐ[K] K × K) (x : D) :
    e (1 ⊗ₜ[k] conjugate n x) = ((e (1 ⊗ₜ[k] x)).2, (e (1 ⊗ₜ[k] x)).1) := by
  simpa only [conjugate_baseChange, LinearMap.baseChange_tmul] using
    pair_conjugation hn e (1 ⊗ₜ[k] x)

/-- Send the diagonal and off-diagonal pairs into their four matrix entries. -/
private noncomputable def matrixCoordinates (c : K) (hc : c ≠ 0) :
    ((K × K) × (K × K)) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun p := !![p.1.1, c * p.2.1; p.2.2, p.1.2]
  invFun M := ((M 0 0, M 1 1), (c⁻¹ * M 0 1, M 1 0))
  left_inv := by rintro ⟨⟨a,b⟩,⟨x, y⟩⟩; simp [hc]
  right_inv := by
    intro M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc]
  map_add' := by
    rintro ⟨⟨a,b⟩,⟨x, y⟩⟩ ⟨⟨a',b'⟩,⟨x',y'⟩⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_add]
  map_smul' := by
    rintro a ⟨⟨x, y⟩,⟨z, t⟩⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul, mul_left_comm]

private theorem cyclic_matrix_splitting_over (hn : IsFieldCompositionNorm n)
    (e : K ⊗[k] D ≃ₐ[K] K × K)
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (hs : ∀ x, σ x = conjugate n x)
    (param : k) (hp : param ≠ 0) :
    ∃ E : K ⊗[k] cyclicAlgebra σ hσ param ≃ₐ[K] Matrix (Fin 2) (Fin 2) K,
      ∀ q : cyclicAlgebra σ hσ param,
        (E (1 ⊗ₜ[k] q)).det = algebraMap k K (cyclicNorm n σ hσ param q) := by
  let Q := cyclicAlgebra σ hσ param
  let c := algebraMap k K param
  have hc : c ≠ 0 := by simpa [c] using (algebraMap k K).injective.ne hp
  let f : D →ₐ[k] K :=
    (((AlgHom.fst K K K).comp e.toAlgHom).restrictScalars k).comp includeRight
  have hf (x : D) : f x = (e (1 ⊗ₜ[k] x)).1 := rfl
  have hfbar (x : D) : f (σ x) = (e (1 ⊗ₜ[k] x)).2 := by
    rw [hf, hs, pair_conjugation_tmul hn e]
  let g : Q →ₐ[k] Matrix (Fin 2) (Fin 2) K := f.mapMatrix.comp Q.val
  let E : K ⊗[k] Q →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
    lift (Algebra.ofId K _) g (fun a q => Algebra.commutes a (g q))
  let L : K ⊗[k] Q ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
    (LinearEquiv.baseChange k K Q (D × D) (cyclicPairEquiv σ hσ param).symm).trans
      ((TensorProduct.prodRight k K K D D).trans
        ((e.toLinearEquiv.prodCongr e.toLinearEquiv).trans (matrixCoordinates c hc)))
  have hE (a : K) (x y : D) :
      E (a ⊗ₜ[k] cyclicPair σ hσ param x y) =
        a • matrixCoordinates c hc (e (1 ⊗ₜ[k] x), e (1 ⊗ₜ[k] y)) := by
    rw [show E _ = algebraMap K (Matrix (Fin 2) (Fin 2) K) a *
        g (cyclicPair σ hσ param x y) from lift_tmul .., ← Algebra.smul_def]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [g, c, cyclicPair, cyclicMatrix, matrixCoordinates, hfbar, ← hf]
  have hL : E.toLinearMap = L.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective σ hσ param q
    change E (a ⊗ₜ[k] cyclicPair σ hσ param x y) = L (a ⊗ₜ[k] cyclicPair σ hσ param x y)
    rw [hE]
    have hxy : (cyclicPairEquiv σ hσ param).symm (cyclicPair σ hσ param x y) = (x, y) :=
      (cyclicPairEquiv σ hσ param).symm_apply_apply (x, y)
    have htmul (z : D) : e (a ⊗ₜ[k] z) = a • e (1 ⊗ₜ[k] z) := by
      rw [← map_smul]
      simp [TensorProduct.smul_tmul']
    simp [L, LinearEquiv.baseChange_tmul, hxy, htmul, ← map_smul]
  let eQ := AlgEquiv.ofBijective E (show Function.Bijective E from by
    change Function.Bijective E.toLinearMap
    rw [hL]
    exact L.bijective)
  refine ⟨eQ, ?_⟩
  intro q
  obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective σ hσ param q
  change (E (1 ⊗ₜ[k] cyclicPair σ hσ param x y)).det = _
  rw [hE, one_smul, Matrix.det_fin_two, cyclic_norm_pair, map_sub, map_mul]
  change (e (1 ⊗ₜ[k] x)).1 * (e (1 ⊗ₜ[k] x)).2 -
    c * (e (1 ⊗ₜ[k] y)).1 * (e (1 ⊗ₜ[k] y)).2 = _
  rw [mul_assoc, pair_norm hn e, pair_norm hn e, normBaseChange_tmul, normBaseChange_tmul]
  simp [c]

theorem quaternion_matrix_splitting : QuaternionSpecification.matrixSplitting := by
  intro k D _ _ _ _ n hn hd σ hσ hs param hp
  let := hn.finite
  exact cyclic_matrix_splitting_over hn (etalePair (K := SeparableClosure k) hd) σ hσ hs param hp

end Etale


section Descent

variable {k : Type u} {K : Type w} {A : Type v}
variable [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

private theorem simple_of_baseChange [Nontrivial A] [IsSimpleRing (K ⊗[k] A)] : IsSimpleRing A := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  by_cases ht : I = ⊤
  · exact Or.inr ht
  left
  let f := I.ringCon.mk'
  let B := I.ringCon.Quotient
  let : Nontrivial B := ⟨⟨1, 0, fun h => ht (I.one_mem_iff.mp (Quotient.eq'.mp h))⟩⟩
  let : Algebra k B := (f.comp (algebraMap k A)).toAlgebra' (fun c b => by
    obtain ⟨a, rfl⟩ := I.ringCon.mk'_surjective b
    change f (algebraMap k A c) * f a = f a * f (algebraMap k A c)
    rw [← map_mul, ← map_mul, Algebra.commutes])
  let fA : A →ₐ[k] B := ⟨f, fun _ => rfl⟩
  let fK : K ⊗[k] A →ₐ[K] K ⊗[k] B := Algebra.TensorProduct.map (AlgHom.id K K) fA
  let : Nontrivial (K ⊗[k] B) :=
    (includeRight_injective (B := B) (algebraMap k K).injective).nontrivial
  have hinj : Function.Injective fK := fK.toRingHom.injective
  rw [← I.ker_ringCon_mk']
  apply (TwoSidedIdeal.ker_eq_bot f).mpr
  intro x y h
  apply includeRight_injective ((algebraMap k K).injective)
  apply hinj
  change fK (1 ⊗ₜ[k] x) = fK (1 ⊗ₜ[k] y)
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
  exact congrArg (fun b : B => (1 : K) ⊗ₜ[k] b) h

private theorem central_of_baseChange [Algebra.IsCentral K (K ⊗[k] A)] :
    Algebra.IsCentral k A := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  have hm : (1 : K) ⊗ₜ[k] z ∈ Subalgebra.center K (K ⊗[k] A) := by
    rw [Subalgebra.mem_center_iff]
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a y => simp [tmul_mul_tmul, hz y]
    | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hm)
  change c ⊗ₜ[k] (1 : A) = (1 : K) ⊗ₜ[k] z at hc
  let f := Algebra.linearMap k K
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap k K).injective)
  have hg1 : g 1 = 1 := by
    simpa [f] using congrArg (fun m : k →ₗ[k] k => m 1) hg
  have h := congrArg (fun t => TensorProduct.lid k A (TensorProduct.map g (LinearMap.id : A →ₗ[k] A) t)) hc
  exact Algebra.mem_bot.mpr ⟨g c, by simpa [hg1, Algebra.algebraMap_eq_smul_one] using h⟩

private theorem central_simple_of_matrix_splitting [Nontrivial A] [Module.Finite k A]
    (e : K ⊗[k] A ≃ₐ[K] Matrix (Fin 2) (Fin 2) K) : RM03.CSA.IsCentralSimple k A := by
  let : IsSimpleRing (K ⊗[k] A) := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  let : Algebra.IsCentral K (K ⊗[k] A) := ⟨by
    intro x hx
    rw [Subalgebra.mem_center_iff] at hx
    have he : e x ∈ Subalgebra.center K (Matrix (Fin 2) (Fin 2) K) := by
      rw [Subalgebra.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (hx y)
    obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out he)
    exact Algebra.mem_bot.mpr ⟨c, e.injective ((e.commutes c).trans hc)⟩⟩
  exact ⟨simple_of_baseChange (k := k) (K := K), central_of_baseChange (k := k) (K := K), inferInstance⟩

private theorem matrix2_of_nonunit (hA : RM03.CSA.IsCentralSimple k A)
    (hd : finrank k A = 4) {a : A} (ha : a ≠ 0) (hau : ¬ IsUnit a) :
    Nonempty (A ≃ₐ[k] Matrix (Fin 2) (Fin 2) k) := by
  obtain ⟨r, D, _, _, hD, hr, ⟨e⟩⟩ := RM03.CSA.MatrixDivision.exists_presentation k A hA
  have hf := e.toLinearEquiv.finrank_eq
  rw [hd, Module.finrank_matrix, Fintype.card_fin] at hf
  have h1 : r ≠ 1 := by
    rintro rfl
    let eval : Matrix (Fin 1) (Fin 1) D →ₐ[k] D :=
      { toFun := fun M => M 0 0
        map_zero' := rfl
        map_one' := by simp
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => by simp [Matrix.mul_apply]
        commutes' := fun _ => by simp [Matrix.algebraMap_matrix_apply] }
    have hinj : Function.Injective eval := by
      intro x y h
      ext i j
      fin_cases i
      fin_cases j
      exact h
    have hsurj : Function.Surjective eval := fun d => ⟨fun _ _ => d, rfl⟩
    let E := e.trans (AlgEquiv.ofBijective eval ⟨hinj, hsurj⟩)
    apply hau
    have hne : E a ≠ 0 := fun h => ha (E.injective (h.trans (map_zero E).symm))
    simpa using (isUnit_iff_ne_zero.mpr hne).map E.symm.toMonoidHom
  let := hD.2
  have hpos : 1 ≤ finrank k D := Module.finrank_pos
  have hrge : 2 ≤ r := by omega
  have hrle : r * r ≤ 4 := by
    simpa [← hf] using Nat.mul_le_mul_left (r * r) hpos
  have hr2 : r = 2 := by nlinarith
  subst r
  have hf1 : finrank k D = 1 := by omega
  obtain ⟨f⟩ : Nonempty (k ≃ₐ[k] D) := Module.nonempty_algEquiv_iff_finrank_eq_one.mpr hf1
  exact ⟨e.trans f.symm.mapMatrix⟩

private theorem reduced_norm_transport {B : Type w} [Ring B] [Algebra k B]
    (hA : RM03.CSA.IsCentralSimple k A) (hB : RM03.CSA.IsCentralSimple k B)
    (f : A ≃ₐ[k] B) (a : A) :
    RM03.CSA.reducedNorm hB (f a) = RM03.CSA.reducedNorm hA a := by
  have hd : RM03.CSA.degree k B = RM03.CSA.degree k A :=
    (RM03.CSA.degree_eq_iff hB).mpr ⟨RM03.CSA.degree_pos hA,
      f.toLinearEquiv.finrank_eq.symm.trans (RM03.CSA.finrank_eq_degree_sq hA)⟩
  let L := AlgebraicClosure k
  obtain ⟨e⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hA
  let E := (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) f.symm).trans e
  have h := @RM03.CSA.reducedNorm_map k _ B _ _ L _ _ hB (f a)
  rw [hd] at h
  apply (algebraMap k L).injective
  rw [h E, RM03.CSA.reducedNorm_map hA a e]
  have he : E (1 ⊗ₜ[k] f a) = e (1 ⊗ₜ[k] a) := by
    change e (1 ⊗ₜ[k] f.symm (f a)) = _
    simp
  rw [he]

end Descent

section Quaternion

variable {k : Type u} {D : Type v} [Field k] [CommRing D] [Algebra k D]
variable {n : QuadraticForm k D}

private theorem cyclic_polar_pair
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) (x y z t : D) :
    (cyclicNorm n σ hσ param).polarBilin (cyclicPair σ hσ param x y)
      (cyclicPair σ hσ param z t) = n.polarBilin x z - param * n.polarBilin y t := by
  have hadd := (cyclicPairEquiv σ hσ param).map_add (x, y) (z, t)
  change cyclicPair σ hσ param (x + z) (y + t) =
    cyclicPair σ hσ param x y + cyclicPair σ hσ param z t at hadd
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← hadd, cyclic_norm_pair]
  ring

private theorem cyclic_polar_regular (hn : IsFieldCompositionNorm n)
    (σ : D ≃ₐ[k] D) (hσ : Function.Involutive σ) (param : k) (hp : param ≠ 0) :
    (cyclicNorm n σ hσ param).polarBilin.Nondegenerate := by
  have hleft : (cyclicNorm n σ hσ param).polarBilin.SeparatingLeft := by
    intro q hq
    obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective σ hσ param q
    change ∀ w, (cyclicNorm n σ hσ param).polarBilin (cyclicPair σ hσ param x y) w = 0 at hq
    have hx : x = 0 := hn.nondegenerate.1 x (fun z => by
      simpa only [cyclic_polar_pair, map_zero, mul_zero, sub_zero] using
        hq (cyclicPair σ hσ param z 0))
    have hy : y = 0 := hn.nondegenerate.1 y (fun t => by
      have h := hq (cyclicPair σ hσ param 0 t)
      rw [cyclic_polar_pair, map_zero, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hp)
    change cyclicPair σ hσ param x y = 0
    rw [hx, hy, cyclic_pair_zero]
  refine ⟨hleft, fun q hq => hleft q (fun p => ?_)⟩
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm _ q p] using hq p

theorem quaternion_norm_and_splitting : QuaternionSpecification.quaternionNormAndSplitting := by
  intro k D _ _ _ _ n hn hd σ hσ hs param hp
  let := hn.finite
  let Q := cyclicAlgebra σ hσ param
  let N := cyclicNorm n σ hσ param
  let K := SeparableClosure k
  let : Module.Finite k Q := Module.Finite.of_surjective
    (cyclicPairEquiv σ hσ param).toLinearMap (cyclicPairEquiv σ hσ param).surjective
  have hdim : finrank k Q = 4 := cyclic_finrank σ hσ param hd
  let : Nontrivial Q := Module.finrank_pos_iff.mp (by rw [hdim]; decide)
  obtain ⟨e, he⟩ := quaternion_matrix_splitting hn hd σ hσ hs param hp
  have hQ : RM03.CSA.IsCentralSimple k Q := central_simple_of_matrix_splitting e
  have hdeg : RM03.CSA.degree k Q = 2 := (RM03.CSA.degree_eq_iff hQ).mpr (by simpa using hdim)
  have hN : ∀ q : Q, RM03.CSA.reducedNorm hQ q = N q := by
    intro q
    have h := @RM03.CSA.reducedNorm_map k _ Q _ _ K _ _ hQ q
    rw [hdeg] at h
    exact (algebraMap k K).injective ((h e).trans (he q))
  refine ⟨hQ, hdim, hdeg, ⟨inferInstance, inferInstance, cyclic_polar_regular hn σ hσ param hp, ?_⟩,
    hN, ?_⟩
  · intro a b
    change N (a * b) = N a * N b
    rw [← hN (a * b), ← hN a, ← hN b, RM03.CSA.reducedNorm_mul]
  constructor
  · rintro ⟨q, hq, hqN⟩
    apply matrix2_of_nonunit hQ hdim hq
    simpa [← RM03.CSA.reducedNorm_ne_zero_iff_isUnit hQ q, hN, hqN]
  · rintro ⟨f⟩
    let m : Matrix (Fin 2) (Fin 2) k := !![1, 0; 0, 0]
    have hm : m ≠ 0 := fun h => one_ne_zero (congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h)
    have hdet : m.det = 0 := by simp [m, Matrix.det_fin_two]
    have h := @RM03.CSA.reducedNorm_eq_det k _ Q _ _ hQ (f.symm m)
    rw [hdeg] at h
    exact ⟨f.symm m, fun hn => hm (f.symm.injective (hn.trans (map_zero f.symm).symm)),
      (hN _).symm.trans ((h f).trans (by simpa using hdet))⟩

end Quaternion

theorem quaternion_noncommutative : QuaternionSpecification.quaternionNoncommutative := by
  intro k Q _ _ _ hQ hdeg
  by_contra! hcomm
  have hs : Function.Surjective (Algebra.linearMap k Q) := by
    intro q
    have hc : q ∈ Subalgebra.center k Q := Subalgebra.mem_center_iff.mpr (fun x => hcomm x q)
    exact Algebra.mem_bot.mp (hQ.2.1.out hc)
  have hle := LinearMap.finrank_le_finrank_of_surjective hs
  have hdim := ((RM03.CSA.degree_eq_iff hQ).mp hdeg).2
  norm_num [hdim] at hle

section Local

theorem quadratic_composition_norm_eq_algebra_norm :
    QuaternionSpecification.quadraticNormIsAlgebraNorm := by
  intro k D _ _ _ _ n hn hd x
  let := hn.finite
  let K := SeparableClosure k
  let e := etalePair (K := K) hd
  let z : K ⊗[k] D := 1 ⊗ₜ[k] x
  have he : Algebra.norm K (e z) = (e z).1 * (e z).2 := by
    rw [Algebra.norm_apply]
    change (LinearMap.prodMap (LinearMap.mulLeft K (e z).1)
      (LinearMap.mulLeft K (e z).2)).det = _
    rw [LinearMap.det_prodMap, LinearMap.det_mulLeft, LinearMap.det_mulLeft]
  have hl : (Algebra.lmul k D x).baseChange K = Algebra.lmul K (K ⊗[k] D) z := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    rw [LinearMap.baseChange_tmul]
    change a ⊗ₜ[k] (x * y) = (1 ⊗ₜ[k] x) * (a ⊗ₜ[k] y)
    rw [tmul_mul_tmul, one_mul]
  apply (algebraMap k K).injective
  calc
    algebraMap k K (n x) = normBaseChange K n z := by
      simp [z, normBaseChange_tmul]
    _ = (e z).1 * (e z).2 := (pair_norm hn e z).symm
    _ = Algebra.norm K (e z) := he.symm
    _ = algebraMap k K (Algebra.norm k x) := by
      rw [Algebra.norm_eq_of_algEquiv e, Algebra.norm_apply, Algebra.norm_apply, ← hl,
        LinearMap.det_baseChange]

theorem local_cyclic_reduced_norm : QuaternionSpecification.localCyclicNorm := by
  intro k D B _ _ _ _ _ _ n hn hd σ hσ hs param hp f hB
  obtain ⟨hQ, _, _, _, hN, _⟩ := quaternion_norm_and_splitting hn hd σ hσ hs param hp
  have hmain (x y : D) : RM03.CSA.reducedNorm hB (f (cyclicPair σ hσ param x y)) =
      Algebra.norm k x - param * Algebra.norm k y := by
    rw [reduced_norm_transport hQ hB, hN, cyclic_norm_pair,
      quadratic_composition_norm_eq_algebra_norm hn hd x,
      quadratic_composition_norm_eq_algebra_norm hn hd y]
  refine ⟨hmain, ?_⟩
  rw [hmain, ← quadratic_composition_norm_eq_algebra_norm hn hd 0]
  simp

/-- The local formula with only the quadratic field and Galois data. -/
theorem local_quadratic_field_cyclic_reduced_norm :
    QuaternionSpecification.localQuadraticFieldCyclicNorm := by
  classical
  intro k D B _ _ _ _ _ _ hd σ hσne param hp
  let : Algebra.IsQuadraticExtension k D := ⟨hd⟩
  let : Algebra.Etale k D := ⟨Algebra.FormallyEtale.of_isSeparable k D,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hne : (1 : D ≃ₐ[k] D) ≠ σ := hσne.symm
  have hall : ({1, σ} : Finset (D ≃ₐ[k] D)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hd]
    exact (Finset.card_pair hne).ge
  have hσsq : σ * σ = 1 := by
    have hm : σ * σ ∈ ({1, σ} : Finset (D ≃ₐ[k] D)) := by rw [hall]; exact Finset.mem_univ _
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hm :
        σ * σ = 1 ∨ σ * σ = σ) with h | h
    · exact h
    · exact (hσne (mul_right_cancel (h.trans (one_mul σ).symm))).elim
  have hσ : Function.Involutive σ := fun x =>
    congrArg (fun τ : D ≃ₐ[k] D => τ x) hσsq
  have hnorm (x : D) : algebraMap k D (Algebra.norm k x) = x * σ x := by
    rw [Algebra.norm_eq_prod_automorphisms, ← hall, Finset.prod_insert (Finset.notMem_singleton.mpr hne)]
    simp
  have htrace (x : D) : algebraMap k D (Algebra.trace k D x) = x + σ x := by
    rw [trace_eq_sum_automorphisms, ← hall, Finset.sum_insert (Finset.notMem_singleton.mpr hne)]
    simp
  have hpolar (x y : D) : QuadraticMap.polar (Algebra.norm k) x y =
      Algebra.traceForm k D x (σ y) := by
    apply (algebraMap k D).injective
    simp only [QuadraticMap.polar, Algebra.traceForm_apply, map_sub, hnorm, htrace, map_add,
      map_mul]
    rw [hσ y]
    ring
  let n : QuadraticForm k D := QuadraticMap.ofPolar (Algebra.norm k)
    (fun c x => by
      apply (algebraMap k D).injective
      simp only [hnorm, Algebra.smul_def, map_mul, AlgEquiv.commutes, Algebra.algebraMap_self_apply])
    (fun x y z => by simp only [hpolar, LinearMap.map_add₂])
    (fun c x y => by simp only [hpolar, LinearMap.map_smul₂])
  have hbilin (x y : D) : n.polarBilin x y = Algebra.traceForm k D x (σ y) := hpolar x y
  have hn : IsFieldCompositionNorm n := by
    refine ⟨inferInstance, inferInstance, ⟨?_, ?_⟩, fun x y => map_mul (Algebra.norm k) x y⟩
    · intro x hx
      apply (traceForm_nondegenerate k D).1
      intro y
      obtain ⟨z, rfl⟩ := σ.surjective y
      exact (hbilin x z).symm.trans (hx z)
    · intro y hy
      apply σ.injective
      rw [map_zero]
      apply (traceForm_nondegenerate k D).2
      intro x
      exact (hbilin x y).symm.trans (hy x)
  have hconj (x : D) : σ x = conjugate n x := by
    rw [conjugate_apply, compositionTrace_apply, hbilin, map_one, Algebra.traceForm_apply,
      mul_one, ← Algebra.algebraMap_eq_smul_one, htrace, add_sub_cancel_left]
  exact ⟨hσ, fun e hB => local_cyclic_reduced_norm hn hd σ hσ hconj param hp e hB⟩

end Local

section ScalarDouble

variable {k : Type u} [Field k] {α : k}

private theorem scalar_double_norm_apply (x : scalarDouble α) :
    scalarDoubleNorm α x = x.re ^ 2 - α * x.im ^ 2 := by
  change x.re * x.re - α * (x.im * x.im) = _
  ring

private theorem scalar_double_polar (x y : scalarDouble α) :
    (scalarDoubleNorm α).polarBilin x y = 2 * x.re * y.re - 2 * α * x.im * y.im := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    scalar_double_norm_apply, QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  ring

private theorem scalar_double_norm_conditions (h2 : (2 : k) ≠ 0) (hα : α ≠ 0) :
    IsFieldCompositionNorm (scalarDoubleNorm α) := by
  have hregular : (scalarDoubleNorm α).polarBilin.SeparatingLeft := by
    intro x hx
    have hr := hx 1
    change (scalarDoubleNorm α).polarBilin x 1 = 0 at hr
    rw [scalar_double_polar] at hr
    simp only [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, mul_one, mul_zero, sub_zero] at hr
    have hi := hx QuadraticAlgebra.omega
    change (scalarDoubleNorm α).polarBilin x QuadraticAlgebra.omega = 0 at hi
    rw [scalar_double_polar] at hi
    simp only [QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, mul_zero, mul_one,
      zero_sub, neg_eq_zero] at hi
    ext
    · exact (mul_eq_zero.mp hr).resolve_left h2
    · exact (mul_eq_zero.mp hi).resolve_left (mul_ne_zero h2 hα)
  refine ⟨inferInstance, inferInstance, ⟨hregular, fun x hx => hregular x (fun y => ?_)⟩, ?_⟩
  · simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm _ x y] using hx y
  · intro x y
    have he (z : scalarDouble α) : scalarDoubleNorm α z = z.norm := by
      rw [scalar_double_norm_apply, QuadraticAlgebra.norm_def]
      ring
    simp only [he, map_mul]

private theorem scalar_double_involution_apply (x : scalarDouble α) :
    scalarDoubleInvolution α x = ⟨x.re, -x.im⟩ := by
  change x.re • (1 : scalarDouble α) + x.im • -QuadraticAlgebra.omega = _
  ext <;> simp

private theorem scalar_double_involution_conjugate (x : scalarDouble α) :
    scalarDoubleInvolution α x = conjugate (scalarDoubleNorm α) x := by
  rw [scalar_double_involution_apply, conjugate_apply, compositionTrace_apply,
    scalar_double_polar]
  ext <;> simp [two_mul]

open Polynomial in
private theorem scalar_double_etale (h2 : (2 : k) ≠ 0) (hα : α ≠ 0) :
    Algebra.Etale k (scalarDouble α) := by
  let f : k[X] := X ^ 2 - C α
  let P : StandardEtalePair k := ⟨f, monic_X_pow_sub_C α (by decide : 2 ≠ 0),
    f.derivative, ⟨1, 0, 1, by simp⟩⟩
  have hsquare :
      (QuadraticAlgebra.omega : scalarDouble α) ^ 2 = algebraMap k (scalarDouble α) α := by
    simp [QuadraticAlgebra.omega_pow_two_eq_add, Algebra.algebraMap_eq_smul_one]
  have hω : IsUnit (QuadraticAlgebra.omega : scalarDouble α) := by
    have h : IsUnit ((QuadraticAlgebra.omega : scalarDouble α) ^ 2) := by
      rw [hsquare]
      exact (isUnit_iff_ne_zero.mpr hα).map (algebraMap k (scalarDouble α))
    exact isUnit_of_dvd_unit (dvd_pow_self _ (by decide : 2 ≠ 0)) h
  have hp : P.HasMap (QuadraticAlgebra.omega : scalarDouble α) := by
    constructor
    · simp [P, f, hsquare]
    · have htwo := (isUnit_iff_ne_zero.mpr h2).map (algebraMap k (scalarDouble α))
      change IsUnit (aeval (QuadraticAlgebra.omega : scalarDouble α) f.derivative)
      rw [show f.derivative = C (2 : k) * X by
        simp [f, derivative_pow, C_ofNat, mul_comm]]
      rw [map_mul, aeval_C, aeval_X]
      exact htwo.mul hω
  let g := P.lift QuadraticAlgebra.omega hp
  have hPx : P.X * P.X = α • (1 : P.Ring) + (0 : k) • P.X := by
    have h := P.hasMap_X.1
    change aeval P.X f = 0 at h
    rw [show aeval P.X f = P.X ^ 2 - algebraMap k P.Ring α by simp [f]] at h
    simpa [pow_two, Algebra.algebraMap_eq_smul_one] using sub_eq_zero.mp h
  let t : scalarDouble α →ₐ[k] P.Ring := QuadraticAlgebra.lift ⟨P.X, hPx⟩
  have ht : t QuadraticAlgebra.omega = P.X := by simp [t]
  have hg : g P.X = QuadraticAlgebra.omega := P.lift_X _ _
  let e : P.Ring ≃ₐ[k] scalarDouble α := AlgEquiv.ofAlgHom g t
    (QuadraticAlgebra.algHom_ext (by simp [ht, hg])) (P.hom_ext (by simp [ht, hg]))
  exact Algebra.Etale.of_equiv e

theorem scalar_double_model : QuaternionSpecification.scalarDoubleModel := by
  intro k _ α h2 hα
  refine ⟨scalar_double_etale h2 hα, QuadraticAlgebra.finrank_eq_two _ _,
    scalar_double_norm_conditions h2 hα, ?_, fun s t => scalar_double_norm_apply ⟨s, t⟩,
    fun x => (QuadraticAlgebra.re_smul_add_im_smul x).symm⟩
  simp [QuadraticAlgebra.omega_pow_two_eq_add, Algebra.algebraMap_eq_smul_one]

end ScalarDouble

section ExternalDouble

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
variable {n : QuadraticForm k A} {γ : k}

private theorem cayley_dickson_norm_pair (x y : A) :
    CayleyDickson.norm n γ (CayleyDickson.pair n γ x y) = n x - γ * n y := rfl

private theorem cayley_dickson_polar_pair (x y z t : A) :
    (CayleyDickson.norm n γ).polarBilin (CayleyDickson.pair n γ x y)
      (CayleyDickson.pair n γ z t) = n.polarBilin x z - γ * n.polarBilin y t := by
  have hadd : CayleyDickson.pair n γ x y + CayleyDickson.pair n γ z t =
      CayleyDickson.pair n γ (x + z) (y + t) := rfl
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hadd,
    cayley_dickson_norm_pair]
  ring

private theorem cayley_dickson_polar_nondegenerate (hn : IsFieldCompositionNorm n)
    (hγ : γ ≠ 0) : (CayleyDickson.norm n γ).polarBilin.Nondegenerate := by
  have hleft : (CayleyDickson.norm n γ).polarBilin.SeparatingLeft := by
    rintro ⟨x, y⟩ h
    change ∀ p, (CayleyDickson.norm n γ).polarBilin (CayleyDickson.pair n γ x y) p = 0 at h
    have hx : x = 0 := hn.nondegenerate.1 x (fun z => by
      simpa only [cayley_dickson_polar_pair, map_zero, mul_zero, sub_zero] using
        h (CayleyDickson.pair n γ z 0))
    have hy : y = 0 := hn.nondegenerate.1 y (fun t => by
      have ht := h (CayleyDickson.pair n γ 0 t)
      rw [cayley_dickson_polar_pair, map_zero, zero_sub, neg_eq_zero] at ht
      exact (mul_eq_zero.mp ht).resolve_left hγ)
    subst x y
    rfl
  refine ⟨hleft, fun x h => hleft x (fun y => ?_)⟩
  simpa only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm _ x y] using h y

private theorem cayley_dickson_norm_conditions (hn : IsFieldCompositionNorm n)
    (hγ : γ ≠ 0) (h : conjugate n 1 = 1) :
    letI := CayleyDickson.ring n γ h
    letI := CayleyDickson.scalarTower n γ h
    letI := CayleyDickson.scalarComm n γ h
    IsFieldCompositionNorm (CayleyDickson.norm n γ) := by
  let := CayleyDickson.ring n γ h
  let := CayleyDickson.scalarTower n γ h
  let := CayleyDickson.scalarComm n γ h
  let := hn.finite
  let := hn.nontrivial
  have hL := hn.toNormLaws
  refine ⟨?_, ?_, cayley_dickson_polar_nondegenerate hn hγ, ?_⟩
  · change Module.Finite k (A × A)
    infer_instance
  · change Nontrivial (A × A)
    infer_instance
  · rintro ⟨x, y⟩ ⟨z, t⟩
    let N := CayleyDickson.norm n γ
    change N (CayleyDickson.pair n γ x y * CayleyDickson.pair n γ z t) =
      N (CayleyDickson.pair n γ x y) * N (CayleyDickson.pair n γ z t)
    have hcross : n.polarBilin (x * z) (conjugate n t * y) =
        n.polarBilin (t * x) (y * conjugate n z) := by
      rw [← compositionTrace_mul_conjugate hL, ← compositionTrace_mul_conjugate hL,
        conjugate_mul hL, conjugate_mul hL, conjugate_involutive hL t,
        conjugate_involutive hL z]
      simpa only [mul_assoc] using compositionTrace_mul_comm hL (x * z * conjugate n y) t
    simp only [N, CayleyDickson.mul_pair, cayley_dickson_norm_pair, QuadraticMap.map_add n,
      ← QuadraticMap.polarBilin_apply_apply, LinearMap.map_smul, hcross,
      QuadraticMap.map_smul, hn.multiplicative, norm_conjugate hL, smul_eq_mul]
    ring

end ExternalDouble

section ConsecutiveDoubles

variable {k : Type u} [Field k] {α β : k}

private theorem quaternion_model_norm_conditions (h2 : (2 : k) ≠ 0)
    (hα : α ≠ 0) (hβ : β ≠ 0) :
    finrank k (quaternionModel α β) = 4 ∧ IsFieldCompositionNorm (quaternionModelNorm α β) := by
  let : Algebra.Etale k (scalarDouble α) := scalar_double_etale h2 hα
  obtain ⟨_, hdim, _, hn, _, _⟩ := quaternion_norm_and_splitting
    (scalar_double_norm_conditions h2 hα) (QuadraticAlgebra.finrank_eq_two α 0)
    (scalarDoubleInvolution α) (scalarDoubleInvolution_involutive α)
    scalar_double_involution_conjugate β hβ
  exact ⟨hdim, hn⟩

theorem consecutive_doubling_models : QuaternionSpecification.consecutiveDoublingModels := by
  intro k _ α β γ h2 hα hβ hγ
  let Q := quaternionModel α β
  let nQ := quaternionModelNorm α β
  let σ := scalarDoubleInvolution α
  let hσ := scalarDoubleInvolution_involutive α
  let p := cyclicPair σ hσ β
  let omegaD : scalarDouble α := QuadraticAlgebra.omega
  let i := p omegaD 0
  let j := p 0 1
  let e := cyclicPairEquiv σ hσ β
  obtain ⟨hdim, hnQ⟩ := quaternion_model_norm_conditions h2 hα hβ
  have hiSq : i * i = α • (1 : Q) := by
    change p omegaD 0 * p omegaD 0 = _
    dsimp only [p]
    rw [cyclic_pair_mul]
    simpa [omegaD, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, Algebra.algebraMap_eq_smul_one]
      using cyclic_pair_scalar σ hσ β α
  have hjSq : j * j = β • (1 : Q) := by
    have hs := (cyclic_generators (scalarDoubleInvolution α)
      (scalarDoubleInvolution_involutive α) β).2.1
    simpa only [pow_two, Algebra.algebraMap_eq_smul_one] using hs
  have hiJ : i * j = p 0 omegaD := by
    dsimp only [i, j, p]
    rw [cyclic_pair_mul]
    simp
  have hjI : j * i = p 0 (-omegaD) := by
    have hω : σ omegaD = -omegaD := by
      change scalarDoubleInvolution α omegaD = -omegaD
      rw [scalar_double_involution_apply]
      ext <;> simp [omegaD]
    dsimp only [i, j, p]
    rw [cyclic_pair_mul]
    simp [hω]
  have hanti : i * j = -(j * i) := by
    rw [hiJ, hjI]
    change e (0, omegaD) = -e (0, -omegaD)
    rw [← map_neg]
    simp
  have hne : i * j ≠ j * i := by
    intro h
    rw [hiJ, hjI] at h
    have heq : e (0, omegaD) = e (0, -omegaD) := h
    have h' := congrArg (fun xy : scalarDouble α × scalarDouble α => xy.2.im) (e.injective heq)
    have hs : (1 : k) = -1 := by simpa [omegaD] using h'
    apply h2
    calc
      (2 : k) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun x : k => x + 1) hs
      _ = 0 := neg_add_cancel 1
  refine ⟨hdim, hnQ, hiSq, hjSq, hanti, hne, fun x y => cyclic_norm_pair _ _ _ _ x y, ?_⟩
  have h : AdjointSpecification.conjugate nQ (1 : Q) = 1 := conjugate_one hnQ.toNormLaws
  refine ⟨h, ?_⟩
  let C := CayleyDickson nQ γ
  let : NonAssocRing C := CayleyDickson.ring nQ γ h
  let : IsScalarTower k C C := CayleyDickson.scalarTower nQ γ h
  let : SMulCommClass k C C := CayleyDickson.scalarComm nQ γ h
  let := hnQ.finite
  let q := CayleyDickson.pair nQ γ
  have hnC := cayley_dickson_norm_conditions hnQ hγ h
  refine ⟨?_, hnC, ?_, ?_, cayley_dickson_norm_pair, composition_isAlternative hnC.toNormLaws, ?_⟩
  · change finrank k (Q × Q) = 8
    rw [Module.finrank_prod, hdim]
  · change q 0 1 * q 0 1 = γ • q 1 0
    simp [q, h]
  · intro x y
    change q x y = q x 0 + q y 0 * q 0 1
    simp only [q, CayleyDickson.mul_pair, mul_zero, zero_mul, smul_zero, add_zero, one_mul]
    change (x, y) = (x + 0, 0 + y)
    simp
  · refine ⟨q i 0, q j 0, q 0 1, ?_⟩
    have hl : (q i 0 * q j 0) * q 0 1 = q 0 (i * j) := by simp [q]
    have hr : q i 0 * (q j 0 * q 0 1) = q 0 (j * i) := by simp [q]
    rw [hl, hr]
    exact fun H => hne (congrArg (CayleyDickson.snd nQ γ) H)

end ConsecutiveDoubles

section RealDivision

variable {k : Type u} [Field k]

private theorem quaternion_model_coordinates (α β : k) :
    ∃ e : quaternionModel α β ≃ₐ[k] QuaternionAlgebra k α 0 β,
      ∀ x y : scalarDouble α, e (quaternionModelPair α β x y) = ⟨x.re, x.im, y.re, y.im⟩ := by
  let σ := scalarDoubleInvolution α
  let hσ := scalarDoubleInvolution_involutive α
  let p := cyclicPair σ hσ β
  let f := cyclicPairEquiv σ hσ β
  let coords : (scalarDouble α × scalarDouble α) ≃ₗ[k] QuaternionAlgebra k α 0 β :=
    { toFun := fun xy => ⟨xy.1.re, xy.1.im, xy.2.re, xy.2.im⟩
      invFun := fun q => (⟨q.re, q.imI⟩, ⟨q.imJ, q.imK⟩)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let g := f.symm.trans coords
  have hg (x y : scalarDouble α) : g (p x y) = ⟨x.re, x.im, y.re, y.im⟩ := by
    change coords (f.symm (f (x, y))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have h1 : g 1 = 1 := by
    rw [← cyclic_pair_one σ hσ β, show cyclicPair σ hσ β 1 0 = p 1 0 from rfl, hg]
    rfl
  have hm (a b : quaternionModel α β) : g (a * b) = g a * g b := by
    obtain ⟨⟨x, y⟩, rfl⟩ := f.surjective a
    obtain ⟨⟨z, t⟩, rfl⟩ := f.surjective b
    change g (p x y * p z t) = g (p x y) * g (p z t)
    rw [show p x y * p z t = p (x * z + β • (σ t * y)) (t * x + y * σ z) from
      cyclic_pair_mul σ hσ β x y z t, hg, hg, hg]
    have hσcoord (w : scalarDouble α) : σ w = ⟨w.re, -w.im⟩ := scalar_double_involution_apply w
    apply QuaternionAlgebra.ext <;> simp [hσcoord, QuaternionAlgebra.mk_mul_mk, smul_eq_mul] <;> ring
  exact ⟨AlgEquiv.ofLinearEquiv g h1 hm, hg⟩

theorem real_doubling_division : QuaternionSpecification.realDoublingDivision := by
  let Q := quaternionModel (-1 : ℝ) (-1)
  let nQ := quaternionModelNorm (-1 : ℝ) (-1)
  let C := CayleyDickson nQ (-1)
  let nC := CayleyDickson.norm nQ (-1)
  obtain ⟨e, he⟩ := quaternion_model_coordinates (-1 : ℝ) (-1)
  have hn (q : Q) : nQ q = Quaternion.normSq (e q) := by
    obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective (scalarDoubleInvolution (-1 : ℝ))
      (scalarDoubleInvolution_involutive (-1 : ℝ)) (-1) q
    change nQ (quaternionModelPair (-1 : ℝ) (-1) x y) = _
    rw [he, show nQ (quaternionModelPair (-1 : ℝ) (-1) x y) =
      scalarDoubleNorm (-1 : ℝ) x - (-1) * scalarDoubleNorm (-1 : ℝ) y from
      cyclic_norm_pair _ _ _ _ x y, scalar_double_norm_apply, scalar_double_norm_apply,
      Quaternion.normSq_def']
    ring
  have hQ0 (q : Q) : 0 ≤ nQ q := by
    rw [hn]
    exact Quaternion.normSq_nonneg
  have hQpos (q : Q) (hq : q ≠ 0) : 0 < nQ q := by
    refine lt_of_le_of_ne (hQ0 q) (fun h => hq (e.injective ?_))
    rw [map_zero, ← Quaternion.normSq_eq_zero, ← hn, ← h]
  obtain ⟨_, hnQ⟩ := quaternion_model_norm_conditions
    (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (-1 : ℝ) ≠ 0) (by norm_num : (-1 : ℝ) ≠ 0)
  have h := conjugate_one hnQ.toNormLaws
  let : NonAssocRing C := CayleyDickson.ring nQ (-1) h
  let : IsScalarTower ℝ C C := CayleyDickson.scalarTower nQ (-1) h
  let : SMulCommClass ℝ C C := CayleyDickson.scalarComm nQ (-1) h
  have hnC := cayley_dickson_norm_conditions hnQ (by norm_num : (-1 : ℝ) ≠ 0) h
  have hCpos (a : C) (ha : a ≠ 0) : 0 < nC a := by
    obtain ⟨x, y⟩ := a
    change (0 : ℝ) < nC (CayleyDickson.pair nQ (-1) x y)
    rw [show nC (CayleyDickson.pair nQ (-1) x y) = nQ x + nQ y from by
      simpa only [neg_mul, one_mul, sub_neg_eq_add] using
        (cayley_dickson_norm_pair (n := nQ) (γ := -1) x y)]
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        rintro rfl
        apply ha
        subst x
        rfl
      exact add_pos_of_nonneg_of_pos (hQ0 _) (hQpos _ hy)
    · exact add_pos_of_pos_of_nonneg (hQpos _ hx) (hQ0 _)
  have hQdiv := (division_iff_anisotropic hnQ).mpr (fun ⟨q, hq, hzero⟩ =>
    (hQpos q hq).ne' hzero)
  have hCdiv := (division_iff_anisotropic hnC).mpr (fun ⟨a, ha, hzero⟩ =>
    (hCpos a ha).ne' hzero)
  exact ⟨e, hn, fun q hq => ⟨hQpos q hq, hQdiv q hq⟩, fun a ha => ⟨hCpos a ha, hCdiv a ha⟩⟩

end RealDivision

theorem orthogonal_quaternion_model : QuaternionSpecification.orthogonalQuaternionModel := by
  intro k C _ _ _ _ _ n D a hn hD ha ha0 hassoc hcomm
  dsimp only
  let : CommRing D := commutativeSubalgebraRing D hassoc hcomm
  let : Algebra k D := Algebra.ofModule (R := k) (A := D) smul_mul_assoc
    mul_smul_comm
  intro hetale hd
  let := hetale
  obtain ⟨_, _, hdisj, hinj, ⟨E, hE, _⟩, hmul, hnorm, _⟩ :=
    orthogonal_doubling hn hD ha ha0
  obtain ⟨σ, hσ, hs⟩ := composition_conjugation_automorphism hD
  let param := -n a
  have hp : param ≠ 0 := neg_ne_zero.mpr ha0
  obtain ⟨hQ, hdimQ, _, _, hN, hsplit⟩ := quaternion_norm_and_splitting hD hd σ hσ hs param hp
  have hright (y : D) : (y : C) * a ∈ D.rightMultiple a :=
    UnitalSubalgebra.mem_rightMultiple.mpr ⟨y, rfl⟩
  let g : (D × D) →ₗ[k] E :=
    { toFun := fun xy => ⟨(xy.1 : C) + (xy.2 : C) * a, by
        change _ ∈ E.toSubmodule
        rw [hE]
        exact add_mem (Submodule.mem_sup_left xy.1.property) (Submodule.mem_sup_right (hright xy.2))⟩
      map_add' := by
        rintro ⟨x, y⟩ ⟨z, t⟩
        apply Subtype.ext
        change (x : C) + z + ((y : C) + t) * a = (x + (y : C) * a) + (z + (t : C) * a)
        rw [add_mul]
        abel
      map_smul' := by
        rintro c ⟨x, y⟩
        apply Subtype.ext
        change c • (x : C) + (c • (y : C)) * a = c • ((x : C) + (y : C) * a)
        rw [smul_mul_assoc, smul_add] }
  have hg : Function.Bijective g := by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      rw [Submodule.eq_bot_iff]
      rintro ⟨x, y⟩ hg
      have hz : (x : C) + (y : C) * a = 0 :=
        congrArg (fun b : E => (b : C)) (LinearMap.mem_ker.mp hg)
      have hxright : (x : C) ∈ D.rightMultiple a := by
        rw [eq_neg_of_add_eq_zero_left hz]
        exact neg_mem (hright y)
      have hx : (x : C) = 0 := Submodule.disjoint_def.mp hdisj (x : C) x.property hxright
      have hy : y = 0 := by
        apply hinj
        simpa [hx] using hz
      exact Prod.ext (Subtype.ext hx) hy
    · intro z
      have hz : (z : C) ∈ E.toSubmodule := z.property
      rw [hE, Submodule.mem_sup] at hz
      obtain ⟨x, hx, b, hb, hxb⟩ := hz
      obtain ⟨y, rfl⟩ := UnitalSubalgebra.mem_rightMultiple.mp hb
      exact ⟨(⟨x, hx⟩, y), Subtype.ext hxb⟩
  let f := (cyclicPairEquiv σ hσ param).symm.trans (LinearEquiv.ofBijective g hg)
  have hf (x y : D) : (f (cyclicPair σ hσ param x y) : C) = (x : C) + (y : C) * a := by
    have hh := (cyclicPairEquiv σ hσ param).symm_apply_apply (x, y)
    change (cyclicPairEquiv σ hσ param).symm (cyclicPair σ hσ param x y) = (x, y) at hh
    change (g ((cyclicPairEquiv σ hσ param).symm (cyclicPair σ hσ param x y)) : C) = _
    rw [hh]
    rfl
  have hfN (q : cyclicAlgebra σ hσ param) : n (f q : C) = RM03.CSA.reducedNorm hQ q := by
    obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective σ hσ param q
    rw [hf, hN, cyclic_norm_pair]
    exact hnorm x y
  have hfOne : f 1 = 1 := by
    apply Subtype.ext
    rw [← cyclic_pair_one σ hσ param, hf]
    simp
  have hfMul (q r : cyclicAlgebra σ hσ param) : f (q * r) = f q * f r := by
    obtain ⟨⟨x, y⟩, rfl⟩ := cyclic_pair_surjective σ hσ param q
    obtain ⟨⟨z, t⟩, rfl⟩ := cyclic_pair_surjective σ hσ param r
    apply Subtype.ext
    change (f (cyclicPair σ hσ param x y * cyclicPair σ hσ param z t) : C) =
      (f (cyclicPair σ hσ param x y) : C) * (f (cyclicPair σ hσ param z t) : C)
    rw [cyclic_pair_mul, hf, hf, hf, hmul, hs, hs]
    rfl
  have heAssoc (x y z : E) : (x * y) * z = x * (y * z) := by
    obtain ⟨x, rfl⟩ := f.surjective x
    obtain ⟨y, rfl⟩ := f.surjective y
    obtain ⟨z, rfl⟩ := f.surjective z
    simp only [← hfMul, mul_assoc]
  let : Ring E := associativeSubalgebraRing E heAssoc
  let : Algebra k E := Algebra.ofModule (R := k) (A := E) smul_mul_assoc mul_smul_comm
  let F := AlgEquiv.ofLinearEquiv f hfOne hfMul
  let := hQ.2.2
  let := hQ.1
  let := Module.Finite.of_surjective f.toLinearMap f.surjective
  let : Nontrivial E := f.injective.nontrivial
  let K := SeparableClosure k
  obtain ⟨e, _⟩ := quaternion_matrix_splitting hD hd σ hσ hs param hp
  let eE := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) F.symm).trans e
  have hCSA : RM03.CSA.IsCentralSimple k E := central_simple_of_matrix_splitting eE
  have hdim : Module.finrank k E = 4 :=
    f.finrank_eq.symm.trans hdimQ
  have degE : RM03.CSA.degree k E = 2 := (RM03.CSA.degree_eq_iff hCSA).mpr (by simpa using hdim)
  refine ⟨E, hE, σ, hσ, hs, heAssoc, F, hCSA, hdim, degE, hf, ?_, ?_⟩
  · intro z
    obtain ⟨q, rfl⟩ := F.surjective z
    rw [reduced_norm_transport hQ hCSA]
    exact hfN q
  · have hIso : Specification.isotropic (E.restrictNorm n) ↔
        Specification.isotropic (cyclicNorm (D.restrictNorm n) σ hσ param) := by
      constructor
      · rintro ⟨z, hz, hzN⟩
        refine ⟨f.symm z, fun h => hz (f.symm.injective (h.trans (map_zero f.symm).symm)), ?_⟩
        rw [← hN, ← hfN, f.apply_symm_apply]
        exact hzN
      · rintro ⟨q, hq, hqN⟩
        refine ⟨f q, fun h => hq (f.injective (h.trans (map_zero f).symm)), ?_⟩
        rw [UnitalSubalgebra.restrictNorm_apply, hfN, hN, hqN]
    rw [hIso, hsplit]
    exact ⟨fun ⟨g⟩ => ⟨F.symm.trans g⟩, fun ⟨g⟩ => ⟨F.trans g⟩⟩


section AbstractQuaternion

variable {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
  [IsScalarTower k C C] [SMulCommClass k C C]
variable {n : QuadraticForm k C}

omit [IsScalarTower k C C] [SMulCommClass k C C] in
private theorem polar_symmetric (x y : C) : n.polarBilin x y = n.polarBilin y x :=
  QuadraticMap.polar_comm n x y

private theorem exists_norm_ne_zero_orthogonal (hn : IsFieldCompositionNorm n)
    (W : Submodule k C)
    (hW : (LinearMap.BilinForm.restrict n.polarBilin W).Nondegenerate)
    (hproper : finrank k W < finrank k C) :
    ∃ a ∈ W.orthogonalBilin n.polarBilin, n a ≠ 0 := by
  let := hn.finite
  let B : LinearMap.BilinForm k C := n.polarBilin
  let U := B.orthogonal W
  have hsym : B.IsRefl := fun x y h => (polar_symmetric (n := n) y x).trans h
  have hc : IsCompl W U := B.isCompl_orthogonal_of_restrict_nondegenerate hsym hW
  have hU : (LinearMap.BilinForm.restrict B U).Nondegenerate := by
    apply B.nondegenerate_restrict_of_disjoint_orthogonal hsym
    change Disjoint U (B.orthogonal U)
    rw [B.orthogonal_orthogonal hn.nondegenerate hsym]
    exact hc.disjoint.symm
  have hp : 0 < finrank k U := by
    dsimp only [U]
    rw [B.finrank_orthogonal hn.nondegenerate]
    omega
  by_contra! hz
  let : Nontrivial U := Module.finrank_pos_iff.mp hp
  obtain ⟨a, ha⟩ := exists_ne (0 : U)
  apply ha
  apply hU.1
  intro b
  change n.polarBilin (a : C) (b : C) = 0
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hz _ a.property,
    hz _ b.property, hz _ (U.add_mem a.property b.property), sub_zero, sub_zero]

/-- Build the cyclic presentation inside an arbitrary rank-four composition
algebra and transfer the reduced norm to the original algebra. -/
theorem abstract_quaternion_norm_and_splitting : QuaternionSpecification.abstractQuaternion := by
  intro k C _ _ _ _ _ n h2 hn hdim
  let := hn.finite
  let := hn.nontrivial
  have hL := IsFieldCompositionNorm.toNormLaws hn
  let S : Submodule k C := k ∙ (1 : C)
  have hSdim : finrank k S = 1 := finrank_span_singleton one_ne_zero
  have hone : n.polarBilin (1 : C) 1 = (2 : k) := compositionTrace_one hL
  have hsym : n.polarBilin.IsRefl := fun x y h => (polar_symmetric (n := n) y x).trans h
  have hS : (LinearMap.BilinForm.restrict n.polarBilin S).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hsym
    exact (LinearMap.BilinForm.isCompl_span_singleton_orthogonal (hone.trans_ne h2)).disjoint
  obtain ⟨i, hi, hiN⟩ := exists_norm_ne_zero_orthogonal hn S hS (by rw [hSdim, hdim]; decide)
  have hit : compositionTrace n i = 0 := by
    rw [compositionTrace_apply, polar_symmetric]
    exact hi 1 (Submodule.mem_span_singleton_self 1)
  let α := -n i
  have hα : α ≠ 0 := neg_ne_zero.mpr hiN
  have hisq : i * i = α • (1 : C) := by
    have h := composition_quadratic_equation hL i
    rw [hit, zero_smul, sub_zero, ← sub_neg_eq_add, sub_eq_zero] at h
    simpa only [α, neg_smul] using h
  let f : scalarDouble α →ₗ[k] C :=
    (QuadraticAlgebra.reₗ α 0).smulRight (1 : C) + (QuadraticAlgebra.imₗ α 0).smulRight i
  have hf (x : scalarDouble α) : f x = x.re • (1 : C) + x.im • i := rfl
  have hf1 : f 1 = 1 := by simp [hf]
  have hfm (x y : scalarDouble α) : f (x * y) = f x * f y := by
    simp only [hf, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, zero_mul, add_zero,
      add_mul, mul_add, smul_mul_smul, one_mul, mul_one, hisq, smul_smul, add_smul]
    module
  have hfN (x : scalarDouble α) : n (f x) = scalarDoubleNorm α x := by
    have hbi : n.polarBilin (1 : C) i = 0 := hi 1 (Submodule.mem_span_singleton_self 1)
    rw [hf, QuadraticMap.map_add n, ← QuadraticMap.polarBilin_apply_apply,
      LinearMap.map_smul₂, LinearMap.map_smul, hbi, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hL.map_one, scalar_double_norm_apply]
    simp [α]
    ring
  have hfb (x y : scalarDouble α) :
      n.polarBilin (f x) (f y) = (scalarDoubleNorm α).polarBilin x y := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hfN]
  have hαnorm := scalar_double_norm_conditions h2 hα
  have hfinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    apply hαnorm.nondegenerate.1
    intro y
    rw [← hfb, hx, map_zero]
    rfl
  let D : UnitalSubalgebra k C :=
    { toSubmodule := LinearMap.range f
      one_mem' := ⟨1, hf1⟩
      mul_mem' := by
        rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
        exact ⟨x * y, hfm x y⟩ }
  let e : scalarDouble α ≃ₗ[k] D := LinearEquiv.ofInjective f hfinj
  have he (x : scalarDouble α) : (e x : C) = f x := rfl
  have he1 : e 1 = 1 := Subtype.ext hf1
  have hem (x y : scalarDouble α) : e (x * y) = e x * e y := Subtype.ext (hfm x y)
  have hassoc (x y z : D) : (x * y) * z = x * (y * z) := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    obtain ⟨z, rfl⟩ := e.surjective z
    simp only [← hem, mul_assoc]
  have hcomm (x y : D) : x * y = y * x := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp only [← hem, mul_comm]
  let : CommRing D := commutativeSubalgebraRing D hassoc hcomm
  let : Algebra k D := Algebra.ofModule (R := k) (A := D) smul_mul_assoc mul_smul_comm
  let et : scalarDouble α ≃ₐ[k] D := AlgEquiv.ofLinearEquiv e he1 hem
  let : Algebra.Etale k (scalarDouble α) := scalar_double_etale h2 hα
  have hEt : Algebra.Etale k D := Algebra.Etale.of_equiv et
  have hDdim : finrank k D = 2 := e.finrank_eq.symm.trans (QuadraticAlgebra.finrank_eq_two _ _)
  have hDreg : (D.restrictNorm n).polarBilin.Nondegenerate := by
    have hb (x y : scalarDouble α) :
        (D.restrictNorm n).polarBilin (e x) (e y) = (scalarDoubleNorm α).polarBilin x y := hfb x y
    constructor
    · intro z hz
      obtain ⟨x, rfl⟩ := e.surjective z
      have hx := hαnorm.nondegenerate.1 x (fun y => (hb x y).symm.trans (hz (e y)))
      rw [hx, map_zero]
    · intro z hz
      obtain ⟨y, rfl⟩ := e.surjective z
      have hy := hαnorm.nondegenerate.2 y (fun x => (hb x y).symm.trans (hz (e x)))
      rw [hy, map_zero]
  have hD : IsFieldCompositionNorm (D.restrictNorm n) :=
    ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, e.injective.nontrivial,
      hDreg, fun x y => hL.map_mul (x : C) (y : C)⟩
  have hDreg' : (LinearMap.BilinForm.restrict n.polarBilin D.toSubmodule).Nondegenerate := by
    convert hDreg using 1
    ext x y
    exact (UnitalSubalgebra.polarBilin_restrictNorm D n x y).symm
  obtain ⟨a, ha, haN⟩ := exists_norm_ne_zero_orthogonal hn D.toSubmodule hDreg'
    (by change finrank k D < finrank k C; rw [hDdim, hdim]; decide)
  obtain ⟨E, _, σ, hσ, _, heAssoc, F, hE, hEdim, hEdeg, _, hEN, hEsplit⟩ :=
    orthogonal_quaternion_model hn hD ha haN hassoc hcomm hEt hDdim
  have htop : E.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq (hEdim.trans hdim.symm)
  let incl : E →ₗ[k] C := SMulMemClass.subtype E
  have hiSurj : Function.Surjective incl := fun x =>
    ⟨⟨x, by change x ∈ E.toSubmodule; rw [htop]; trivial⟩, rfl⟩
  let g := LinearEquiv.ofBijective incl ⟨Subtype.val_injective, hiSurj⟩
  have hg (x : E) : g x = (x : C) := rfl
  have haC (x y z : C) : (x * y) * z = x * (y * z) := by
    obtain ⟨x, rfl⟩ := g.surjective x
    obtain ⟨y, rfl⟩ := g.surjective y
    obtain ⟨z, rfl⟩ := g.surjective z
    exact congrArg g (heAssoc x y z)
  refine ⟨haC, ?_⟩
  let : Ring C := { (inferInstance : NonAssocRing C) with mul_assoc := haC }
  let : Algebra k C := Algebra.ofModule (R := k) (A := C) smul_mul_assoc mul_smul_comm
  let : Ring E := associativeSubalgebraRing E heAssoc
  let : Algebra k E := Algebra.ofModule (R := k) (A := E) smul_mul_assoc mul_smul_comm
  let G : E ≃ₐ[k] C := AlgEquiv.ofLinearEquiv g rfl (fun _ _ => rfl)
  let K := AlgebraicClosure k
  obtain ⟨s⟩ := RM03.CSA.algEquiv_matrix_algebraicClosure hE
  rw [hEdeg] at s
  let eC := (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) G.symm).trans s
  have hC : RM03.CSA.IsCentralSimple k C := central_simple_of_matrix_splitting eC
  have hCdeg : RM03.CSA.degree k C = 2 := (RM03.CSA.degree_eq_iff hC).mpr (by simpa using hdim)
  refine ⟨hC, hCdeg, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := G.surjective x
    rw [reduced_norm_transport hE hC]
    exact hEN z
  · have hiso : Specification.isotropic n ↔ Specification.isotropic (E.restrictNorm n) := by
      constructor
      · rintro ⟨x, hx, hxN⟩
        obtain ⟨z, rfl⟩ := G.surjective x
        exact ⟨z, fun h => hx (h ▸ map_zero G), hxN⟩
      · rintro ⟨z, hz, hzN⟩
        exact ⟨G z, fun h => hz (G.injective (h.trans (map_zero G).symm)), hzN⟩
    rw [hiso, hEsplit]
    exact ⟨fun ⟨s⟩ => ⟨G.symm.trans s⟩, fun ⟨s⟩ => ⟨G.trans s⟩⟩

end AbstractQuaternion

end LinearAlgebraicGroups.Composition
