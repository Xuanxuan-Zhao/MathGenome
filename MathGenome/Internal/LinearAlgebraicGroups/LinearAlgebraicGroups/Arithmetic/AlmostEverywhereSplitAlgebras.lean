import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Enveloping
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Degree
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.NoncommRing
import Mathlib.Algebra.Central.End
import Mathlib.RingTheory.SimpleRing.Congr
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.MatrixDivision

noncomputable section

open scoped TensorProduct
open IsLocalRing

namespace LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras

universe u v w

section Adic

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

private theorem mem_ideal_smul_top_iff {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (I : Ideal R) (x : A) :
    x ∈ (I • ⊤ : Submodule R A) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun a => b.repr a i ∈ I) hx
      (fun r hr a _ => show b.repr (r • a) i ∈ I by
        simpa using I.mul_mem_right (b.repr a i) hr)
      (fun x y hx hy => show b.repr (x + y) i ∈ I by simpa using I.add_mem hx hy)
  · intro hx
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) trivial

private theorem precomplete_of_basis {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) (I : Ideal R) [IsPrecomplete I R] :
    IsPrecomplete I A := by
  classical
  constructor
  intro f hf
  have hc (i : ι) : ∃ l : R, ∀ n, b.repr (f n) i ≡ l [SMOD (I ^ n • ⊤ : Ideal R)] := by
    apply IsPrecomplete.prec' (I := I)
    intro m n h
    have h' := (mem_ideal_smul_top_iff b (I ^ m) (f m - f n)).mp
      (SModEq.sub_mem.mp (hf h)) i
    simpa [SModEq.sub_mem, Ideal.smul_eq_mul, ← Ideal.one_eq_top] using h'
  choose l hl using hc
  use b.equivFun.symm l
  intro n
  rw [SModEq.sub_mem, mem_ideal_smul_top_iff b]
  intro i
  have h := SModEq.sub_mem.mp (hl i n)
  have hcoord : b.repr (b.equivFun.symm l) i = l i := by
    exact congrFun (b.equivFun.apply_symm_apply l) i
  simpa only [map_sub, Finsupp.sub_apply, hcoord, Ideal.smul_eq_mul,
    ← Ideal.one_eq_top, mul_one] using h

/-- The residue map on an algebra, expressed by scalar extension to the residue field. -/
private abbrev reduce [IsLocalRing R] : A →ₐ[R] ResidueField R ⊗[R] A :=
  Algebra.TensorProduct.includeRight

private theorem reduce_surjective [IsLocalRing R] :
    Function.Surjective (reduce (R := R) (A := A)) :=
  Algebra.TensorProduct.includeRight_surjective A (residue_surjective (R := R))

private theorem reduce_eq_zero [IsLocalRing R] (x : A) :
    reduce (R := R) x = 0 ↔ x ∈ (maximalIdeal R • ⊤ : Submodule R A) := by
  let e := TensorProduct.quotTensorEquivQuotSMul A (maximalIdeal R)
  change (1 : ResidueField R) ⊗ₜ[R] x = 0 ↔ _
  calc
    _ ↔ e ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] x) = 0 := e.map_eq_zero_iff.symm
    _ ↔ _ := by
      dsimp only [e]
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]

open scoped Pointwise in
private theorem mem_principal_pow_smul {π : R} {n : ℕ} {x : A} :
    x ∈ ((Ideal.span {π} : Ideal R) ^ n • ⊤ : Submodule R A) ↔
      ∃ y : A, x = π ^ n • y := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp [eq_comm]

/-- Idempotents lift from reduction of a finite free algebra over an adically
complete DVR. The cubic correction squares the error in every characteristic. -/
private theorem lift_idempotent [IsLocalRing R] [IsPrincipalIdealRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) {z : ResidueField R ⊗[R] A} (hz : IsIdempotentElem z) :
    ∃ e : A, IsIdempotentElem e ∧ reduce e = z := by
  classical
  let I := maximalIdeal R
  obtain ⟨π, hπ⟩ : ∃ π : R, I = Ideal.span {π} :=
    ⟨Submodule.IsPrincipal.generator I, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  let err (x : A) := x * x - x
  let step (x : A) := x - (2 * x - 1) * err x
  have hstep (x : A) : err (step x) = err x * err x * (4 * err x - 3) := by
    dsimp [err, step]
    noncomm_ring
  obtain ⟨a, ha⟩ := reduce_surjective z
  let f : ℕ → A := fun n => Nat.rec a (fun _ x => step x) n
  have herr (n : ℕ) : ∃ y : A, err (f n) = π ^ (n + 1) • y := by
    induction n with
    | zero =>
      apply mem_principal_pow_smul.mp
      rw [← hπ, pow_one, ← reduce_eq_zero]
      change reduce (R := R) (a * a - a) = 0
      rw [map_sub, map_mul, ha, hz.eq, sub_self]
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      change ∃ y : A, err (step (f n)) = _
      refine ⟨π ^ n • (y * y * (4 * err (f n) - 3)), ?_⟩
      rw [hstep, hy]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add]
      rw [show n + 1 + (n + 1) = n + 1 + 1 + n by omega]
  have hdiff (n : ℕ) : f n ≡ f (n + 1) [SMOD (I ^ (n + 1) • ⊤ : Submodule R A)] := by
    obtain ⟨y, hy⟩ := herr n
    rw [SModEq.sub_mem, hπ, mem_principal_pow_smul]
    refine ⟨(2 * f n - 1) * y, ?_⟩
    change f n - step (f n) = _
    simp [step, hy]
  have hc' {m n : ℕ} (hmn : m ≤ n) :
      f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R A)] := by
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.rfl
    | succ n hmn ih =>
      exact ih.trans ((hdiff n).mono (Submodule.pow_smul_top_le I A (by omega)))
  obtain ⟨e, he⟩ := (precomplete_of_basis b I).prec hc'
  let : Module.Finite R A := Module.Finite.of_basis b
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    apply sub_eq_zero.mp
    apply IsHausdorff.haus (I := I) inferInstance
    intro n
    rw [SModEq.zero, hπ, mem_principal_pow_smul]
    have h := (he n).symm
    rw [SModEq.sub_mem, hπ, mem_principal_pow_smul] at h
    obtain ⟨t, ht⟩ := h
    obtain ⟨s, hs⟩ := herr n
    have hid : e * e - e = err (f n) + e * (e - f n) + (e - f n) * f n - (e - f n) := by
      dsimp [err]
      noncomm_ring
    rw [hid, ht, hs, pow_succ, ← smul_smul, mul_smul_comm, smul_mul_assoc,
      ← smul_add, ← smul_add, ← smul_sub]
    exact ⟨_, rfl⟩
  · have h' := (hdiff 0).trans (he 1)
    rw [SModEq.sub_mem, pow_one, ← reduce_eq_zero, map_sub, sub_eq_zero] at h'
    exact h'.symm.trans ha

end Adic

section EnvelopingMatrix

open Module MulOpposite

variable {R S A B ι : Type*} [CommRing R] [Ring A] [Algebra R A]
    [CommRing S] [Ring B] [Algebra R S] [Algebra S B] [algebraRB : Algebra R B]
    [tower : IsScalarTower R S B] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem repr_of_basis_image (b : Basis ι R A) (c : Basis ι S B) (f : A →ₐ[R] B)
    (hc : ∀ i, f (b i) = c i) (x : A) (i : ι) :
    c.repr (f x) i = algebraMap R S (b.repr x i) := by
  have hx : f x = c.equivFun.symm (fun j => algebraMap R S (b.repr x j)) := by
    calc
      f x = f (∑ j, b.repr x j • b j) := congrArg f (b.sum_repr x).symm
      _ = _ := by simp only [Basis.equivFun_symm_apply, map_sum, map_smul, hc,
        IsScalarTower.algebraMap_smul]
  rw [hx]
  exact congrFun (c.equivFun.apply_symm_apply _) i

private def envelopingMatrix (b : Basis ι R A) : Matrix (ι × ι) (ι × ι) R :=
  LinearMap.toMatrix (b.tensorProduct (b.map (opLinearEquiv R))) b.end
    (AlgHom.mulLeftRight R A).toLinearMap

private theorem envelopingMatrix_apply (b : Basis ι R A) (ij ab : ι × ι) :
    envelopingMatrix b ij ab = b.repr (b ab.1 * b ij.2 * b ab.2) ij.1 := by
  simp [envelopingMatrix, LinearMap.toMatrix_apply, Basis.tensorProduct_apply',
    Matrix.stdBasis]

private theorem envelopingMatrix_image (b : Basis ι R A) (c : Basis ι S B) (f : A →ₐ[R] B)
    (hc : ∀ i, f (b i) = c i) :
    envelopingMatrix c = (envelopingMatrix b).map (algebraMap R S) := by
  ext ij ab
  simp only [envelopingMatrix_apply, Matrix.map_apply, ← hc, ← map_mul,
    repr_of_basis_image b c f hc]

private theorem enveloping_det_unit (b : Basis ι R A)
    (h : Function.Bijective (AlgHom.mulLeftRight R A)) : IsUnit (envelopingMatrix b).det := by
  let d := b.tensorProduct (b.map (opLinearEquiv R))
  let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight R A).toLinearMap h
  apply Matrix.isUnit_det_of_left_inverse (B := LinearMap.toMatrix b.end d e.symm.toLinearMap)
  change LinearMap.toMatrix b.end d e.symm.toLinearMap *
    LinearMap.toMatrix d b.end e.toLinearMap = 1
  rw [← LinearMap.toMatrix_comp, LinearEquiv.symm_comp, LinearMap.toMatrix_id]

private theorem enveloping_surjective (b : Basis ι R A)
    (h : IsUnit (envelopingMatrix b).det) :
    Function.Surjective (AlgHom.mulLeftRight R A) := by
  let d := b.tensorProduct (b.map (opLinearEquiv R))
  let E := envelopingMatrix b
  intro y
  refine ⟨Matrix.toLin b.end d E⁻¹ y, ?_⟩
  change (AlgHom.mulLeftRight R A).toLinearMap (Matrix.toLin b.end d E⁻¹ y) = y
  have hE : Matrix.toLin d b.end E = (AlgHom.mulLeftRight R A).toLinearMap :=
    Matrix.toLin_toMatrix d b.end _
  have hh : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E h
  have hcomp : (Matrix.toLin d b.end E).comp (Matrix.toLin b.end d E⁻¹) = LinearMap.id := by
    rw [← Matrix.toLin_mul, hh, Matrix.toLin_one]
  exact congrArg (fun t : Module.End R (Module.End R A) => t y)
    (show (AlgHom.mulLeftRight R A).toLinearMap.comp (Matrix.toLin b.end d E⁻¹) = _ from
      hE ▸ hcomp)

end EnvelopingMatrix

section IntegralOrder

open Module

variable {R S B ι : Type*} [CommRing R] [Field S] [Algebra R S]
    [Ring B] [Algebra S B] [algebraRB : Algebra R B] [tower : IsScalarTower R S B]
    [Fintype ι] [DecidableEq ι]

/-- The integral-coordinate lattice is an order when the multiplication table
and the coordinates of the identity are integral. -/
private def integralOrder (b : Basis ι S B)
    (h₁ : ∀ i, b.repr 1 i ∈ (algebraMap R S).range)
    (hm : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R S).range) :
    Subalgebra R B where
  carrier := {x | ∀ i, b.repr x i ∈ (algebraMap R S).range}
  zero_mem' i := by simp
  add_mem' {x y} hx hy i := by simpa using (algebraMap R S).range.add_mem (hx i) (hy i)
  one_mem' := h₁
  mul_mem' {x y} hx hy k := by
    have hx' := b.sum_repr x
    have hy' := b.sum_repr y
    change b.repr (x * y) k ∈ (algebraMap R S).range
    rw [← hx', ← hy', Finset.sum_mul]
    simp_rw [Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul, map_sum,
      Finsupp.finsetSum_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (algebraMap R S).range.sum_mem fun i _ =>
      (algebraMap R S).range.sum_mem fun j _ =>
        (algebraMap R S).range.mul_mem ((algebraMap R S).range.mul_mem (hx i) (hy j)) (hm i j k)
  algebraMap_mem' r i := by
    rw [IsScalarTower.algebraMap_apply R S B, Algebra.algebraMap_eq_smul_one,
      map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (algebraMap R S).range.mul_mem ⟨r, rfl⟩ (h₁ i)

/-- The lattice basis maps to the given basis over the fraction field. -/
private theorem integralOrder_basis (b : Basis ι S B)
    (h₁ : ∀ i, b.repr 1 i ∈ (algebraMap R S).range)
    (hm : ∀ i j k, b.repr (b i * b j) k ∈ (algebraMap R S).range)
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ c : Basis ι R (integralOrder b h₁ hm), ∀ i, (c i : B) = b i := by
  classical
  let C := integralOrder b h₁ hm
  let shift (x : C) (i : ι) : R := (x.2 i).choose
  have hshift (x : C) (i : ι) : algebraMap R S (shift x i) = b.repr (x : B) i :=
    (x.2 i).choose_spec
  let f : C →ₗ[R] (ι → R) :=
    { toFun := shift
      map_add' := fun x y => funext fun i => hinj (by simp [hshift])
      map_smul' := fun r x => funext fun i => hinj (by
        simp only [hshift, Subalgebra.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← IsScalarTower.algebraMap_smul S r (x : B), map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply b.ext_elem_iff.mpr
      intro i
      rw [← hshift, ← hshift]
      exact congrArg (algebraMap R S) (congrFun hxy i)
    · intro a
      let y := b.equivFun.symm fun i => algebraMap R S (a i)
      have hy (i : ι) : b.repr y i = algebraMap R S (a i) :=
        congrFun (b.equivFun.apply_symm_apply _) i
      let x : C := ⟨y, fun i => ⟨a i, (hy i).symm⟩⟩
      exact ⟨x, funext fun i => hinj ((hshift x i).trans (hy i))⟩
  let e := LinearEquiv.ofBijective f hf
  refine ⟨Basis.ofEquivFun e, fun i => b.ext_elem_iff.mpr fun j => ?_⟩
  rw [← hshift]
  change algebraMap R S (e (Basis.ofEquivFun e i) j) = _
  simp [Basis.coe_ofEquivFun, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- Scalar extension of an order with a basis that extends to the ambient
basis recovers the ambient algebra. -/
private def extendOrder (b : Basis ι S B) (C : Subalgebra R B) (c : Basis ι R C)
    (hc : ∀ i, (c i : B) = b i) : S ⊗[R] C ≃ₐ[S] B := by
  have hc' (s : S) (x : C) : Commute ((Algebra.ofId S B) s) (C.val x) :=
    Algebra.commutes s (x : B)
  let f : S ⊗[R] C →ₐ[S] B := Algebra.TensorProduct.lift (Algebra.ofId S B) C.val hc'
  let e := (c.baseChange S).equivFun.trans b.equivFun.symm
  have he (i : ι) : e (c.baseChange S i) = b i := by
    change b.equivFun.symm ((c.baseChange S).equivFun (c.baseChange S i)) = b i
    apply b.equivFun.injective
    ext j
    rw [LinearEquiv.apply_symm_apply, Basis.equivFun_self, Basis.equivFun_self]
  have h : f.toLinearMap = e.toLinearMap := by
    apply (c.baseChange S).ext
    intro i
    change f (c.baseChange S i) = e (c.baseChange S i)
    rw [he, Basis.baseChange_apply]
    calc
      f (1 ⊗ₜ[R] c i) = (Algebra.ofId S B) 1 * C.val (c i) :=
        Algebra.TensorProduct.lift_tmul _ _ hc' _ _
      _ = b i := by rw [map_one, one_mul]; exact hc i
  apply AlgEquiv.ofBijective f
  change Function.Bijective f.toLinearMap
  rw [h]
  exact e.bijective

end IntegralOrder

section ResidueSplitting

open Module MulOpposite

variable {k A : Type*} [Field k] [Ring A] [Algebra k A] [Nontrivial A]

/-- Surjectivity of the enveloping action forces simplicity and centrality. -/
private theorem centralSimple_of_enveloping [FiniteDimensional k A]
    (h : Function.Surjective (AlgHom.mulLeftRight k A)) :
    RM03.CSA.IsCentralSimple k A := by
  classical
  let b := Module.finBasis k A
  refine ⟨IsSimpleRing.of_eq_bot_or_eq_top (fun I => ?_), ⟨?_⟩, inferInstance⟩
  · by_cases hI : I = ⊥
    · exact Or.inl hI
    · right
      obtain ⟨x, hxI, hx : x ≠ 0⟩ :=
        IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
      obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
        by_contra! hh
        exact hx (b.ext_elem_iff.mpr fun i => by simp [hh i])
      let f : Module.End k A := (b.coord i).smulRight ((b.repr x i)⁻¹ • (1 : A))
      obtain ⟨t, ht⟩ := h f
      have mem (t : A ⊗[k] Aᵐᵒᵖ) : AlgHom.mulLeftRight k A t x ∈ I := by
        induction t using TensorProduct.inductionOn with
        | tmul a c => simpa only [AlgHom.mulLeftRight_apply] using
            I.mul_mem_right _ _ (I.mul_mem_left a x hxI)
        | add a c ha hc => simpa only [map_add, LinearMap.add_apply] using I.add_mem ha hc
      have hf : f x = 1 := by
        change b.repr x i • ((b.repr x i)⁻¹ • (1 : A)) = 1
        rw [smul_smul, mul_inv_cancel₀ hi, one_smul]
      have hh := mem t
      rw [ht, hf] at hh
      exact I.one_mem_iff.mp hh
  · intro z hz
    have hz' := Subalgebra.mem_center_iff.mp hz
    have commute (t : A ⊗[k] Aᵐᵒᵖ) (x : A) :
        AlgHom.mulLeftRight k A t (z * x) = z * AlgHom.mulLeftRight k A t x := by
      induction t using TensorProduct.inductionOn with
      | tmul a c =>
        simp only [AlgHom.mulLeftRight_apply]
        rw [← mul_assoc a z x, hz' a]
        simp only [mul_assoc]
      | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc, mul_add]
    have hc : Algebra.lmul k A z ∈ Subalgebra.center k (Module.End k A) := by
      apply Subalgebra.mem_center_iff.mpr
      intro f
      obtain ⟨t, rfl⟩ := h f
      exact LinearMap.ext (commute t)
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hc)
    exact Algebra.mem_bot.mpr ⟨r, by
      simpa [Algebra.smul_def] using congrArg (fun f : Module.End k A => f 1) hr⟩

omit [Nontrivial A] in
/-- A central simple algebra over a finite field has matrix coefficients in the base field. -/
private theorem split_of_finite_field [Finite k] (h : RM03.CSA.IsCentralSimple k A) :
    ∃ (n : ℕ) (_ : NeZero n), Nonempty (A ≃ₐ[k] Matrix (Fin n) (Fin n) k) := by
  obtain ⟨n, E, hE, hAlg, hC, hn, ⟨e⟩⟩ :=
    RM03.CSA.MatrixDivision.exists_presentation k A h
  let := hE
  let := hAlg
  let : FiniteDimensional k E := hC.2
  let : Finite E := Module.finite_of_finite k
  let := littleWedderburn E
  have hs : Function.Surjective (algebraMap k E) := by
    intro x
    exact Algebra.mem_bot.mp (hC.1.out (Subalgebra.mem_center_iff.mpr fun y => mul_comm y x))
  let g : k ≃ₐ[k] E := AlgEquiv.ofBijective (Algebra.ofId k E)
    ⟨(algebraMap k E).injective, hs⟩
  exact ⟨n, ⟨Nat.ne_of_gt hn⟩, ⟨e.trans (g.symm.mapMatrix)⟩⟩

end ResidueSplitting

section IdempotentRank

open Module LinearMap

variable {R S A : Type*} [CommRing R] [Field S] [Algebra R S]
    [Ring A] [Algebra R A]

/-- The rank of right multiplication by an integral idempotent is preserved
by each extension of scalars to a field. -/
private theorem finrank_rightMul_scalarExtension {e : A} (he : IsIdempotentElem e) {m : ℕ}
    (b : Basis (Fin m) R (mulRight R e).range) :
    finrank S (mulRight S (Algebra.TensorProduct.includeRight (R := R) (A := S) e)).range = m := by
  let f := mulRight R e
  let i := f.range.subtype
  let p := f.rangeRestrict
  have split : p.comp i = LinearMap.id := by
    ext ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := hx
    change (a * e) * e = a * e
    rw [mul_assoc, he.eq]
  have hsplit : (p.baseChange S).comp (i.baseChange S) = LinearMap.id := by
    rw [← baseChange_comp, split, baseChange_id]
  have hleft : Function.LeftInverse (p.baseChange S) (i.baseChange S) :=
    fun x => congrArg (fun t : End S (S ⊗[R] f.range) => t x) hsplit
  have hi := hleft.injective
  have h₁ := hleft.surjective
  have h₂ : mulRight S (Algebra.TensorProduct.includeRight (R := R) (A := S) e) =
      (i.baseChange S).comp (p.baseChange S) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s a
    change (s ⊗ₜ[R] a) * (1 ⊗ₜ[R] e) = _
    rw [comp_apply, baseChange_tmul, baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one]
    rfl
  rw [h₂, LinearMap.range_comp, range_eq_top.mpr h₁, Submodule.map_top,
    finrank_range_of_inj hi, finrank_eq_card_basis (b.baseChange S), Fintype.card_fin]

private theorem finrank_rightMul_congr {B : Type*} [Ring B] [Algebra S B]
    {C : Type*} [Ring C] [Algebra S C] (g : B ≃ₐ[S] C) (e : B) :
    finrank S (mulRight S (g e)).range = finrank S (mulRight S e).range := by
  let f := g.toLinearEquiv.toLinearMap
  have h : f.comp (mulRight S e) = (mulRight S (g e)).comp f := by
    ext x
    exact map_mul g _ _
  have htop : f.range = ⊤ := range_eq_top.mpr g.surjective
  rw [← range_comp_of_range_eq_top _ htop, ← h, range_comp]
  exact ((mulRight S e).range.equivMapOfInjective f g.injective).finrank_eq.symm

private theorem finrank_matrix_column (n : ℕ) (i : Fin n) :
    finrank S (mulRight S (Matrix.single i i (1 : S))).range = n := by
  classical
  let P := (mulRight S (Matrix.single i i (1 : S))).range
  let f : P →ₗ[S] (Fin n → S) :=
    { toFun := fun x j => (x : Matrix (Fin n) (Fin n) S) j i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      ext j k
      by_cases hki : k = i
      · subst k
        exact congrFun hxy j
      · rw [← ha, ← hb]
        exact (Matrix.mul_single_apply_of_ne (1 : S) i i j k hki a).trans
          (Matrix.mul_single_apply_of_ne (1 : S) i i j k hki b).symm
    · intro x
      let a : Matrix (Fin n) (Fin n) S := Matrix.of fun j _ => x j
      exact ⟨⟨_, mem_range_self _ a⟩, funext fun j => by
        change (a * Matrix.single i i (1 : S)) j i = x j
        simp [Matrix.mul_single_apply_same, a]⟩
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi, Fintype.card_fin]

end IdempotentRank

private def algEquiv_of_injective_of_finrank {F B E : Type*} [Field F]
    [Ring B] [Ring E] [Algebra F B] [Algebra F E]
    [FiniteDimensional F B] [FiniteDimensional F E]
    (f : B →ₐ[F] E) (h : Module.finrank F B = Module.finrank F E)
    (hf : Function.Injective f) : B ≃ₐ[F] E := by
  have hi : Function.Injective f.toLinearMap := hf
  have hs : Function.Surjective f.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) h).mp hi
  exact AlgEquiv.ofBijective f ⟨hf, hs⟩

section LocalSplitting

open Module LinearMap

variable {R A F ι : Type*} [CommRing R] [IsLocalRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Finite (ResidueField R)] [Ring A] [Algebra R A] [Field F] [Algebra R F]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- An order with invertible enveloping determinant has split generic fiber
over a complete DVR with finite residue field. -/
private theorem split_of_integral_order (b : Basis ι R A)
    (hdet : IsUnit (envelopingMatrix b).det) [IsSimpleRing (F ⊗[R] A)] :
    ∃ n : ℕ, Nonempty ((F ⊗[R] A) ≃ₐ[F] Matrix (Fin n) (Fin n) F) := by
  classical
  let k := ResidueField R
  let B := F ⊗[R] A
  let b₀ := b.baseChange k
  let h := envelopingMatrix_image b b₀ (reduce (R := R)) (fun i => (Basis.baseChange_apply _ _ _).symm)
  have hu : IsUnit (envelopingMatrix b₀).det := by
    rw [h]
    exact (algebraMap R k).map_det (envelopingMatrix b) ▸ hdet.map (algebraMap R k)
  let : FiniteDimensional k (k ⊗[R] A) := Module.Finite.of_basis b₀
  let : Nontrivial (k ⊗[R] A) := b₀.equivFun.symm.injective.nontrivial
  obtain ⟨n, hn, ⟨g⟩⟩ := split_of_finite_field
    (centralSimple_of_enveloping (enveloping_surjective b₀ hu))
  let i : Fin n := 0
  let q := Matrix.single i i (1 : k)
  have hq : IsIdempotentElem q := by
    change q * q = q
    simp [q, Matrix.single_mul_single_same]
  let z := g.symm q
  have hz : IsIdempotentElem z := hq.map g.symm
  obtain ⟨e, he, hred⟩ := lift_idempotent b hz
  obtain ⟨m, c⟩ := Submodule.basisOfPid b (mulRight R e).range
  have hm : m = n := by
    rw [← finrank_rightMul_scalarExtension (S := k) he c]
    change finrank k (mulRight k (reduce e)).range = n
    rw [hred, ← finrank_rightMul_congr g z, AlgEquiv.apply_symm_apply]
    exact finrank_matrix_column n i
  let p : B := Algebra.TensorProduct.includeRight e
  let L : Ideal B := (mulRight B p).range
  have hrank : finrank F L = n :=
    (finrank_rightMul_scalarExtension (S := F) he c).trans hm
  let : FiniteDimensional F B := Module.Finite.of_basis (b.baseChange F)
  let : FiniteDimensional F L := inferInstanceAs
    (FiniteDimensional F (L.restrictScalars F))
  let : Nontrivial L := Module.nontrivial_of_finrank_pos (by rw [hrank]; exact NeZero.pos n)
  let d := Module.finBasisOfFinrankEq F L hrank
  let : FiniteDimensional F (End F L) := Module.Finite.of_basis d.end
  let φ := Algebra.lsmul F F (A := B) L
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hdim : finrank F B = finrank F (End F L) := by
    rw [Module.finrank_linearMap, hrank, finrank_eq_card_basis (b.baseChange F)]
    rw [← finrank_eq_card_basis b₀, g.toLinearEquiv.finrank_eq, Module.finrank_matrix]
    simp
  let eB : B ≃ₐ[F] End F L :=
    algEquiv_of_injective_of_finrank (F := F) (B := B) (E := End F L) φ hdim hφ
  exact ⟨n, ⟨eB.trans (LinearMap.toMatrixAlgEquiv d)⟩⟩

end LocalSplitting

open Module in
private theorem split_outside_integral_coefficients {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) {A : Type w} [Ring A] [Algebra K A]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple K A) (p : D.FinitePlace)
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (b : Basis ι K A)
    (h₁ : ∀ i, D.embedding (.inl p) (b.repr 1 i) ∈ D.integers p)
    (hm : ∀ i j k, D.embedding (.inl p) (b.repr (b i * b j) k) ∈ D.integers p)
    (hδ : D.embedding (.inl p) ((envelopingMatrix b).det⁻¹) ∈ D.integers p) :
    letI : Algebra K (D.FiniteCompletion p) := (D.embedding (.inl p)).toAlgebra
    let n := _root_.Specs.RM03.CSA.degree K A
    Nonempty ((D.FiniteCompletion p ⊗[K] A) ≃ₐ[D.FiniteCompletion p]
      Matrix (Fin n) (Fin n) (D.FiniteCompletion p)) := by
  classical
  let F := D.FiniteCompletion p
  let : Algebra K F := (D.embedding (.inl p)).toAlgebra
  let : UniformSpace F := IsTopologicalAddGroup.rightUniformSpace F
  let : IsUniformAddGroup F := isUniformAddGroup_of_addCommGroup (G := F)
  let O := (ValuativeRel.valuation F).valuationSubring
  let R : Type u := O
  let : IsDiscreteValuationRing R := inferInstanceAs
    (IsDiscreteValuationRing ((ValuativeRel.valuation F).integer))
  let : IsAdicComplete (maximalIdeal R) R := inferInstanceAs
    (IsAdicComplete (maximalIdeal ((ValuativeRel.valuation F).integer))
      ((ValuativeRel.valuation F).integer))
  let : Finite (ResidueField R) := inferInstanceAs
    (Finite (ResidueField ((ValuativeRel.valuation F).integer)))
  let B := F ⊗[K] A
  let algebraRB : Algebra R B := Algebra.compHom B (algebraMap R F)
  let scalarTower : IsScalarTower R F B := IsScalarTower.of_algebraMap_eq' rfl
  let bF : Basis ι F B := b.baseChange F
  have hf (i : ι) : (Algebra.TensorProduct.includeRight : A →ₐ[K] B) (b i) = bF i :=
    (Basis.baseChange_apply _ _ _).symm
  have toRange (x : K) (hx : D.embedding (.inl p) x ∈ D.integers p) :
      algebraMap K F x ∈ (algebraMap R F).range := by
    rw [D.integers_eq_valuationSubring p] at hx
    exact ⟨⟨_, hx⟩, rfl⟩
  have hc₁ (i : ι) : bF.repr 1 i ∈ (algebraMap R F).range := by
    have h := repr_of_basis_image b bF Algebra.TensorProduct.includeRight hf (1 : A) i
    rw [map_one] at h
    rw [h]
    exact toRange _ (h₁ i)
  have hcm (i j k : ι) : bF.repr (bF i * bF j) k ∈ (algebraMap R F).range := by
    have h := repr_of_basis_image b bF Algebra.TensorProduct.includeRight hf (b i * b j) k
    rw [map_mul, hf, hf] at h
    rw [h]
    exact toRange _ (hm i j k)
  let C := integralOrder (R := R) (S := F) (B := B)
    (algebraRB := algebraRB) (tower := scalarTower) bF hc₁ hcm
  have hRF : Function.Injective (algebraMap R F) := Subtype.val_injective
  obtain ⟨c, hc⟩ := integralOrder_basis (R := R) (S := F) (B := B)
    (algebraRB := algebraRB) (tower := scalarTower) bF hc₁ hcm hRF
  let e : F ⊗[R] C ≃ₐ[F] B :=
    extendOrder (algebraRB := algebraRB) (tower := scalarTower) bF C c hc
  have hcF := envelopingMatrix_image (algebraRB := algebraRB) (tower := scalarTower) c bF C.val hc
  have hbF := envelopingMatrix_image b bF Algebra.TensorProduct.includeRight hf
  have hdet : algebraMap R F (envelopingMatrix c).det =
      algebraMap K F (envelopingMatrix b).det := by
    rw [(algebraMap R F).map_det, (algebraMap K F).map_det]
    exact congrArg Matrix.det (hcF.symm.trans hbF)
  have hunit : IsUnit (envelopingMatrix c).det := by
    obtain ⟨a, ha⟩ := toRange _ hδ
    refine isUnit_iff_exists_inv.mpr ⟨a, hRF ?_⟩
    rw [map_mul, map_one, hdet, ha, ← map_mul, mul_inv_cancel₀, map_one]
    exact (enveloping_det_unit b (RM03.CSA.mulLeftRight_bijective hA)).ne_zero
  let : IsSimpleRing (F ⊗[R] C) := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv
    (RM03.CSA.isCentralSimple_baseChange (L := F) hA).1
  obtain ⟨n, ⟨g⟩⟩ := split_of_integral_order (F := F) c hunit
  let g' := e.symm.trans g
  have hn : _root_.Specs.RM03.CSA.degree K A = n := RM03.CSA.degree_eq_matrix_size hA g'
  exact hn ▸ ⟨g'⟩

theorem almost_everywhere_split : AlmostEverywhereSplit.{u, v, w} := by
  classical
  intro K _ D A _ _ hA
  let : FiniteDimensional K A := hA.2.2
  let : IsSimpleRing A := hA.1
  let b := Module.finBasis K A
  let δ := (envelopingMatrix b).det
  let S₁ := Set.range fun i => b.repr 1 i
  let S₂ := Set.range fun (i, j, k) => b.repr (b i * b j) k
  let S := S₁ ∪ S₂ ∪ {δ⁻¹}
  have hS : S.Finite :=
    ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_singleton _)
  refine (hS.biUnion (fun x _ => D.finite_nonintegral x)).subset ?_
  intro p hp
  by_contra h
  have good (x : K) (hx : x ∈ S) : D.embedding (.inl p) x ∈ D.integers p := by
    by_contra hx'
    exact h (Set.mem_iUnion₂.mpr ⟨x, hx, hx'⟩)
  have : Nonempty (Fin (Module.finrank K A)) := ⟨⟨0, Module.finrank_pos⟩⟩
  exact hp (split_outside_integral_coefficients D hA p b
    (fun i => good _ (Or.inl (Or.inl ⟨i, rfl⟩)))
    (fun i j k => good _ (Or.inl (Or.inr ⟨(i, j, k), rfl⟩)))
    (good _ (Or.inr rfl)))

end LinearAlgebraicGroups.Arithmetic.AlmostEverywhereSplitAlgebras
