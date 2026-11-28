import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.TriangularPBW
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerreBasis
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.SerreIdeal
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases

/-! Triangular PBW in type A₂. -/

noncomputable section

open scoped TensorProduct

namespace LieNotes.Quantum.TriangularPBW

open Specs.LieNotes.Quantum.TriangularPBW
open Specs.LieNotes.Quantum.Presentation hiding generic indeterminate truncated
open Specs.LieNotes.Quantum.SerreIdeal
open LinearMap

universe u v w

section Triangular

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

private def tensorQuotient (C : Cartan A T) :
    Specs.LieNotes.Quantum.BasicNormalForm.OrderedTensor A T →ₗ[A] SerreTensor C :=
  let p := (SerrePresentation.quotientMap C.q).toLinearMap
  TensorProduct.map (p.rTensor T) p

private theorem quotient_exact (q : Aˣ) :
    Function.Exact (freeSerreSubmodule q).subtype (SerrePresentation.quotientMap q).toLinearMap := by
  rw [LinearMap.exact_iff, Submodule.range_subtype]
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem tensorQuotient_surjective (C : Cartan A T) :
    Function.Surjective (tensorQuotient C) := by
  have hp := Ideal.Quotient.mkₐ_surjective A (SerrePresentation.serreIdeal C.q).asIdeal
  exact TensorProduct.map_surjective (rTensor_surjective T hp) hp

private theorem tensorQuotient_ker (C : Cartan A T) :
    ker (tensorQuotient C) = negativeRange C ⊔ positiveRange C := by
  have hp := Ideal.Quotient.mkₐ_surjective A (SerrePresentation.serreIdeal C.q).asIdeal
  unfold tensorQuotient
  rw [TensorProduct.map_ker (rTensor_exact T (quotient_exact C.q) hp)
    (rTensor_surjective T hp) (quotient_exact C.q) hp, sup_comm]
  rfl

private theorem multiplication_tmul (C : Cartan A T)
    (f : SerrePresentation.SerreAlgebra A C.q) (t : T)
    (e : SerrePresentation.SerreAlgebra A C.q) :
    multiplication C ((f ⊗ₜ[A] t) ⊗ₜ[A] e) = negative C f * cartan C t * positive C e := by
  simp [multiplication]

private theorem multiplication_comp_tensorQuotient (C : Cartan A T) :
    (multiplication C).comp (tensorQuotient C) =
      (serreQuotient C).toLinearMap.comp (Specs.LieNotes.Quantum.BasicNormalForm.multiplication C) := by
  have hneg : (negative C).comp (SerrePresentation.quotientMap C.q) =
      (serreQuotient C).comp (Specs.LieNotes.Quantum.BasicNormalForm.negative C) := by
    rw [negative, SerrePresentation.lift_comp_quotientMap]
    apply FreeAlgebra.hom_ext
    funext i
    simp [Specs.LieNotes.Quantum.BasicNormalForm.negative, F]
  have hpos : (positive C).comp (SerrePresentation.quotientMap C.q) =
      (serreQuotient C).comp (Specs.LieNotes.Quantum.BasicNormalForm.positive C) := by
    rw [positive, SerrePresentation.lift_comp_quotientMap]
    apply FreeAlgebra.hom_ext
    funext i
    simp [Specs.LieNotes.Quantum.BasicNormalForm.positive, E]
  apply TensorProduct.ext_threefold
  intro f t e
  simp only [LinearMap.comp_apply, tensorQuotient, TensorProduct.map_tmul, rTensor_tmul,
    AlgHom.toLinearMap_apply, multiplication_tmul,
    Specs.LieNotes.Quantum.BasicNormalForm.multiplication_tmul, map_mul,
    ← AlgHom.comp_apply, hneg, hpos, cartan]

private theorem multiplication_bijective (C : Cartan A T)
    (h : Specs.LieNotes.Quantum.BasicNormalForm.HasNormalForm C)
    (hi : IdealCorrespondence C) : Function.Bijective (multiplication C) := by
  have hk : ker ((multiplication C).comp (tensorQuotient C)) = ker (tensorQuotient C) := by
    have hq : ker (serreQuotient C).toLinearMap = (serreIdeal C).asIdeal.restrictScalars A := by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [multiplication_comp_tensorQuotient, ker_comp, hq, tensorQuotient_ker]
    exact hi
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    have hx : multiplication C (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := tensorQuotient_surjective C (x - y)
    have hz' : z ∈ ker ((multiplication C).comp (tensorQuotient C)) :=
      mem_ker.mpr (by simp only [LinearMap.comp_apply, hz, hx])
    rw [hk] at hz'
    exact hz.symm.trans (mem_ker.mp hz')
  · have hs : Function.Surjective ((multiplication C).comp (tensorQuotient C)) := by
      rw [multiplication_comp_tensorQuotient]
      exact (Ideal.Quotient.mkₐ_surjective A (serreIdeal C).asIdeal).comp h.surjective
    exact Function.Surjective.of_comp hs

private theorem hasTriangularPBW {ι : Type w} (C : Cartan A T)
    (h : Specs.LieNotes.Quantum.BasicNormalForm.HasNormalForm C)
    (hi : IdealCorrespondence C) (b : Module.Basis ι A T) :
    HasTriangularPBW C b := by
  have hb := multiplication_bijective C h hi
  let s := SerreBasis.basis C.q
  refine ⟨hb, ((s.tensorProduct b).tensorProduct s).map (multiplicationEquiv C hb), ?_⟩
  rintro ⟨⟨f, t⟩, e⟩
  simp only [Module.Basis.map_apply, Module.Basis.tensorProduct_apply,
    multiplicationEquiv, LinearEquiv.ofBijective_apply, multiplication_tmul, s,
    SerreBasis.basis_apply, Specs.LieNotes.Quantum.SerreBasis.orderedMonomial,
    Specs.LieNotes.Quantum.SerrePresentation.x, Specs.LieNotes.Quantum.SerrePresentation.y,
    Specs.LieNotes.Quantum.SerrePresentation.z, orderedMonomial, zMinus, zPlus,
    map_mul, map_pow, map_sub, map_smul, negative, positive, SerrePresentation.lift_generator]

theorem generic : genericProp.{u} := by
  intro k _ _ q hq
  exact hasTriangularPBW _ (BasicNormalForm.generic_normalForm q hq)
    (SerreIdeal.generic_crossingSerreIdeal q hq).2 (laurentBasis k)

theorem indeterminate : indeterminateProp.{u} := by
  intro k _ _
  exact generic (rationalQ k) (rationalQ_sq_ne k)

theorem truncated : truncatedProp.{u} := by
  intro k _ _ N hN
  let A := Specs.LieNotes.Quantum.Truncations.A k N
  have h := hasTriangularPBW _ (BasicNormalForm.truncated_normalForm k N hN)
    (SerreIdeal.truncated_crossingSerreIdeal k N hN).2 (polynomialBasis A)
  have heq : (⇑(polynomialBasis A)) = fun m => ∏ l : Root, (MvPolynomial.X l) ^ m l :=
    funext (Presentation.polynomialBasis_apply A)
  rw [heq] at h
  exact h

end Triangular

section RankOne

open Specs.LieNotes.Quantum.TriangularPBW.RankOne (Letter QuantumAlgebra generator)

variable {k : Type u} [Field k]

private abbrev rankOneQuotient (q : kˣ) : RankOne.Raw k →ₐ[k] QuantumAlgebra k q :=
  Ideal.Quotient.mkₐ k (RankOne.ideal q).asIdeal

private theorem rankOne_relation (q : kˣ) {x : RankOne.Raw k}
    (h : x ∈ RankOne.ideal q) : rankOneQuotient q x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr h)

private def rankOneK (q : kˣ) : (QuantumAlgebra k q)ˣ where
  val := generator q .K
  inv := generator q .Kinv
  val_inv := by
    apply sub_eq_zero.mp
    have h := rankOne_relation q
      (x := FreeAlgebra.ι k Letter.K * FreeAlgebra.ι k Letter.Kinv - 1)
      (TwoSidedIdeal.subset_span (by simp))
    simpa only [map_sub, map_mul, map_one, generator] using h
  inv_val := by
    apply sub_eq_zero.mp
    have h := rankOne_relation q
      (x := FreeAlgebra.ι k Letter.Kinv * FreeAlgebra.ι k Letter.K - 1)
      (TwoSidedIdeal.subset_span (by simp))
    simpa only [map_sub, map_mul, map_one, generator] using h

private theorem rankOne_E_weight (q : kˣ) :
    (rankOneK q : QuantumAlgebra k q) * generator q .E * ↑(rankOneK q)⁻¹ =
      ((q : k)^2) • generator q .E := by
  apply sub_eq_zero.mp
  have h := rankOne_relation q
    (x := FreeAlgebra.ι k Letter.K * FreeAlgebra.ι k Letter.E * FreeAlgebra.ι k Letter.Kinv -
      ((q : k)^2) • FreeAlgebra.ι k Letter.E)
    (TwoSidedIdeal.subset_span (by simp))
  simpa only [map_sub, map_mul, map_smul, rankOneK, Units.val_mk, Units.inv_mk, generator] using h

private theorem rankOne_F_weight (q : kˣ) :
    (rankOneK q : QuantumAlgebra k q) * generator q .F * ↑(rankOneK q)⁻¹ =
      ((↑(q⁻¹) : k)^2) • generator q .F := by
  apply sub_eq_zero.mp
  have h := rankOne_relation q
    (x := FreeAlgebra.ι k Letter.K * FreeAlgebra.ι k Letter.F * FreeAlgebra.ι k Letter.Kinv -
      ((↑(q⁻¹) : k)^2) • FreeAlgebra.ι k Letter.F)
    (TwoSidedIdeal.subset_span (by simp))
  simpa only [map_sub, map_mul, map_smul, rankOneK, Units.val_mk, Units.inv_mk, generator] using h

private theorem rankOne_EF (q : kˣ) :
    generator q .E * generator q .F - generator q .F * generator q .E =
      ((↑q - ↑(q⁻¹) : k)⁻¹) •
        ((rankOneK q : QuantumAlgebra k q) - ↑(rankOneK q)⁻¹) := by
  apply sub_eq_zero.mp
  have h := rankOne_relation q
    (x := FreeAlgebra.ι k Letter.E * FreeAlgebra.ι k Letter.F -
      FreeAlgebra.ι k Letter.F * FreeAlgebra.ι k Letter.E -
      ((↑q - ↑(q⁻¹) : k)⁻¹) • (FreeAlgebra.ι k Letter.K - FreeAlgebra.ι k Letter.Kinv))
    (TwoSidedIdeal.subset_span (by simp))
  simpa only [map_sub, map_mul, map_smul, rankOneK, Units.val_mk, Units.inv_mk, generator] using h

variable {B : Type v} [Ring B] [Algebra k B]

private theorem skew_of_conjugation {K : Bˣ} {x : B} {a : kˣ}
    (h : (K : B) * x * ↑K⁻¹ = (a : k) • x) :
    SemiconjBy (K : B) x ((a : k) • x) := by
  simpa only [SemiconjBy, mul_assoc, Units.inv_mul, mul_one, Algebra.smul_mul_assoc]
    using congrArg (· * (K : B)) h

private theorem inverse_skew {K : Bˣ} {x : B} {a : kˣ}
    (h : SemiconjBy (K : B) x ((a : k) • x)) :
    SemiconjBy (↑K⁻¹ : B) x ((↑a⁻¹ : k) • x) := by
  simpa only [SemiconjBy, Algebra.mul_smul_comm, smul_smul, Units.inv_mul, one_smul,
    Algebra.smul_mul_assoc]
    using congrArg ((↑a⁻¹ : k) • ·) h.units_inv_symm_left.eq

private theorem mul_zpow_of_skew {K : Bˣ} {x : B} {a : kˣ}
    (h : SemiconjBy (K : B) x ((a : k) • x)) (b : ℤ) :
    x * ↑(K ^ b) = (↑(a⁻¹ ^ b) : k) • (↑(K ^ b) * x) := by
  let s := Units.map (algebraMap k B).toMonoidHom a⁻¹
  have hs : Commute s K := Units.ext (Algebra.commutes _ _)
  have h' : SemiconjBy x (K : B) (↑(s * K) : B) := by
    change x * ↑K = (algebraMap k B ↑a⁻¹ * ↑K) * x
    rw [mul_assoc, ← Algebra.smul_def, h.eq, Algebra.smul_mul_assoc, smul_smul,
      Units.inv_mul, one_smul]
  have he := (h'.units_zpow_right b).eq
  rw [hs.mul_zpow, ← map_zpow] at he
  change x * ↑(K ^ b) = (algebraMap k B ↑(a⁻¹ ^ b) * ↑(K ^ b)) * x at he
  rw [mul_assoc, ← Algebra.smul_def] at he
  exact he

private def rankOneMonomial (q : kˣ) (m : ℕ × ℤ × ℕ) : QuantumAlgebra k q :=
  generator q .F ^ m.1 * ↑(rankOneK q ^ m.2.1) * generator q .E ^ m.2.2

/-- The ordered monomials span by stability under left multiplication by each generator. -/
private theorem rankOneMonomial_span (q : kˣ) :
    Submodule.span k (Set.range (rankOneMonomial q)) = ⊤ := by
  let Q := QuantumAlgebra k q
  let M := Submodule.span k (Set.range (rankOneMonomial q))
  let f := generator q .F
  let e := generator q .E
  let K := rankOneK q
  let c := (↑q - ↑(q⁻¹) : k)⁻¹
  have hm (a : ℕ) (b : ℤ) (d : ℕ) : f ^ a * ↑(K ^ b) * e ^ d ∈ M :=
    Submodule.subset_span (Set.mem_range_self (a, b, d))
  have hleft (g : Q)
      (h : ∀ (a : ℕ) (b : ℤ) (d : ℕ), g * (f ^ a * ↑(K ^ b) * e ^ d) ∈ M) :
      ∀ x ∈ M, g * x ∈ M := by
    have hle : M ≤ M.comap (LinearMap.mulLeft k g) := by
      apply Submodule.span_le.mpr
      rintro x ⟨⟨a, b, d⟩, rfl⟩
      exact h a b d
    exact fun x hx => hle hx
  have hF : ∀ x ∈ M, f * x ∈ M := by
    apply hleft
    intro a b d
    simpa only [pow_succ', mul_assoc] using hm (a + 1) b d
  have hKF : SemiconjBy (K : Q) f ((↑((q⁻¹) ^ 2) : k) • f) :=
    skew_of_conjugation (a := q⁻¹ ^ 2) (rankOne_F_weight q)
  have hKE : SemiconjBy (K : Q) e ((↑(q ^ 2) : k) • e) :=
    skew_of_conjugation (a := q ^ 2) (rankOne_E_weight q)
  have hCartan (j : ℤ) (r : k) (hr : SemiconjBy (↑(K ^ j) : Q) f (r • f)) :
      ∀ x ∈ M, ↑(K ^ j) * x ∈ M := by
    apply hleft
    intro a b d
    have hp := (hr.pow_right a).eq
    rw [smul_pow] at hp
    have heq : (↑(K ^ j) : Q) * (f ^ a * ↑(K ^ b) * e ^ d) =
        r ^ a • (f ^ a * ↑(K ^ (j + b)) * e ^ d) := by
      calc
        _ = (↑(K ^ j) * f ^ a) * ↑(K ^ b) * e ^ d := by simp only [mul_assoc]
        _ = _ := by
          rw [hp, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
            mul_assoc (f ^ a), ← Units.val_mul, ← zpow_add, Algebra.smul_mul_assoc]
    rw [heq]
    exact M.smul_mem _ (hm a (j + b) d)
  have hK : ∀ x ∈ M, (K : Q) * x ∈ M := by
    simpa only [zpow_one] using
      hCartan 1 (↑((q⁻¹) ^ 2) : k) (by simpa only [zpow_one] using hKF)
  have hKi : ∀ x ∈ M, (↑K⁻¹ : Q) * x ∈ M := by
    simpa only [zpow_neg_one] using
      hCartan (-1) (↑((q⁻¹ ^ 2)⁻¹) : k)
        (by simpa only [zpow_neg_one] using inverse_skew hKF)
  have hE : ∀ x ∈ M, e * x ∈ M := by
    apply hleft
    intro a b d
    induction a with
    | zero =>
      rw [pow_zero, one_mul, ← mul_assoc, mul_zpow_of_skew hKE b,
        Algebra.smul_mul_assoc, mul_assoc, ← pow_succ']
      simpa only [pow_zero, one_mul] using M.smul_mem (↑((q ^ 2)⁻¹ ^ b) : k) (hm 0 b (d + 1))
    | succ a ih =>
      have hef : e * f = f * e + c • ((K : Q) - ↑K⁻¹) := eq_add_of_sub_eq' (rankOne_EF q)
      let t := f ^ a * ↑(K ^ b) * e ^ d
      have heq : e * (f ^ (a + 1) * ↑(K ^ b) * e ^ d) =
          f * (e * t) + c • ((K : Q) * t - ↑K⁻¹ * t) := by
        simpa only [t, pow_succ', mul_assoc, add_mul, Algebra.smul_mul_assoc, sub_mul]
          using congrArg (· * t) hef
      rw [heq]
      exact M.add_mem (hF _ ih) (M.smul_mem _ (M.sub_mem (hK _ (hm a b d)) (hKi _ (hm a b d))))
  have hfree (v : RankOne.Raw k) : ∀ x ∈ M, rankOneQuotient q v * x ∈ M := by
    induction v using FreeAlgebra.induction with
    | grade0 r =>
      intro x hx
      rw [AlgHom.commutes, ← Algebra.smul_def]
      exact M.smul_mem r hx
    | grade1 g =>
      cases g
      exacts [hE, hF, hK, hKi]
    | mul a b ha hb =>
      intro x hx
      rw [map_mul, mul_assoc]
      exact ha _ (hb _ hx)
    | add a b ha hb =>
      intro x hx
      rw [map_add, add_mul]
      exact M.add_mem (ha _ hx) (hb _ hx)
  have h1 : (1 : Q) ∈ M := by simpa only [pow_zero, zpow_zero, Units.val_one, mul_one] using hm 0 0 0
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k (RankOne.ideal q).asIdeal x
  simpa only [mul_one] using hfree y 1 h1

variable [CharZero k]

private def rankOneMap (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) :
    QuantumAlgebra k q →ₐ[k] U (Presentation.generic q hq) := by
  let C := Presentation.generic q hq
  let K := Units.map (cartan C).toMonoidHom (C.K i)
  have hτ : C.tau i (C.K i : Laurent k) = ((q : k)^2) • (C.K i : Laurent k) := by
    simpa [C, cartanMatrix] using Presentation.generic_scale q hq i i
  have hτinv : (C.tau i).symm (C.K i : Laurent k) =
      ((↑(q⁻¹) : k)^2) • (C.K i : Laurent k) := by
    change laurentScale q⁻¹ i (AddMonoidAlgebra.single (coordinate i) 1) = _
    rw [laurentScale_single, Presentation.pairing_coordinate]
    simp [cartanMatrix, C, Specs.LieNotes.Quantum.Presentation.generic, laurentUnit]
  have hE : (K : U C) * E C i * ↑K⁻¹ = ((q : k)^2) • E C i := by
    have h := (relations C).eCartan i (C.tau i (C.K i))
    rw [AlgEquiv.symm_apply_apply, hτ, map_smul, Algebra.mul_smul_comm] at h
    have h' : (K : U C) * E C i = ((q : k)^2) • (E C i * ↑K) := h.symm
    simpa only [Algebra.smul_mul_assoc, Units.mul_inv_cancel_right]
      using congrArg (· * (↑K⁻¹ : U C)) h'
  have hF : (K : U C) * F C i * ↑K⁻¹ = ((↑(q⁻¹) : k)^2) • F C i := by
    have h := (relations C).cartanF (C.K i) i
    rw [hτinv, map_smul, Algebra.mul_smul_comm] at h
    have h' : (K : U C) * F C i = ((↑(q⁻¹) : k)^2) • (F C i * ↑K) := h
    simpa only [Algebra.smul_mul_assoc, Units.mul_inv_cancel_right]
      using congrArg (· * (↑K⁻¹ : U C)) h'
  have hEF : E C i * F C i - F C i * E C i =
      ((↑q - ↑(q⁻¹) : k)⁻¹) • ((K : U C) - ↑K⁻¹) := by
    have h := (relations C).comm i i
    rw [mixed, ite_eq_left rfl] at h
    change _ = cartan C (genericD q i) at h
    change _ = _ • (cartan C (C.K i : Laurent k) - cartan C (↑(C.K i)⁻¹ : Laurent k))
    rw [show C.K i = laurentUnit (A := k) (coordinate i) from rfl]
    simpa only [genericD, map_smul, map_sub] using h
  let ev := FreeAlgebra.lift k (RankOne.image C i)
  have hker : RankOne.ideal q ≤ TwoSidedIdeal.ker ev.toRingHom := by
    unfold RankOne.ideal
    apply TwoSidedIdeal.span_le.mpr
    intro x hx
    apply (TwoSidedIdeal.mem_ker _).mpr
    change ev x = 0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      simp only [ev, map_sub, map_mul, map_one, map_smul,
        FreeAlgebra.lift_ι_apply, RankOne.image, sub_eq_zero]
    exacts [Units.mul_inv K, Units.inv_mul K, hE, hF, hEF]
  exact Ideal.Quotient.liftₐ (RankOne.ideal q).asIdeal ev fun x hx =>
    (TwoSidedIdeal.mem_ker _).mp (hker (TwoSidedIdeal.mem_asIdeal.mp hx))

private theorem rankOneMap_comp_quotient (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) :
    (rankOneMap q hq i).comp (rankOneQuotient q) =
      FreeAlgebra.lift k (RankOne.image (Presentation.generic q hq) i) := by
  unfold rankOneMap
  apply Ideal.Quotient.liftₐ_comp

private theorem rankOneMap_generator (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) (g : Letter) :
    rankOneMap q hq i (generator q g) = RankOne.image (Presentation.generic q hq) i g := by
  change ((rankOneMap q hq i).comp (rankOneQuotient q)) (FreeAlgebra.ι k g) = _
  rw [rankOneMap_comp_quotient, FreeAlgebra.lift_ι_apply]

private theorem rankOneMap_range (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) :
    (rankOneMap q hq i).range = RankOne.subalgebra (Presentation.generic q hq) i := by
  rw [RankOne.subalgebra, Algebra.adjoin_range_eq_range_freeAlgebra_lift, ← rankOneMap_comp_quotient]
  apply SetLike.coe_injective
  exact ((Ideal.Quotient.mkₐ_surjective k (RankOne.ideal q).asIdeal).range_comp _).symm

private def latticeUnits (k : Type u) [Field k] : Multiplicative Lattice →* (Laurent k)ˣ where
  toFun m := laurentUnit m.toAdd
  map_one' := Units.ext (AddMonoidAlgebra.one_def.symm)
  map_mul' m n := Units.ext (by
    change AddMonoidAlgebra.single (m.toAdd + n.toAdd) (1 : k) =
      AddMonoidAlgebra.single m.toAdd 1 * AddMonoidAlgebra.single n.toAdd 1
    rw [AddMonoidAlgebra.single_mul_single, mul_one])

private def rootExponents (i : Root) (n : ℕ) : Exponents :=
  if i = 0 then (n, 0, 0) else (0, 0, n)

private theorem rootExponents_product {D : Type*} [Monoid D]
    (x : Root → D) (z : D) (i : Root) (n : ℕ) :
    x 0 ^ (rootExponents i n).1 * z ^ (rootExponents i n).2.1 *
      x 1 ^ (rootExponents i n).2.2 = x i ^ n := by
  fin_cases i <;> simp [rootExponents]

private theorem rootExponents_injective (i : Root) : Function.Injective (rootExponents i) := by
  intro a b h
  by_cases hi : i = 0 <;> simpa [rootExponents, hi] using h

private def rankOneIndex (i : Root) (m : ℕ × ℤ × ℕ) : PBWIndex Lattice :=
  ((rootExponents i m.1, m.2.1 • coordinate i), rootExponents i m.2.2)

private theorem rankOneIndex_injective (i : Root) : Function.Injective (rankOneIndex i) := by
  intro x y h
  have ha := rootExponents_injective i (congrArg (fun p : PBWIndex Lattice => p.1.1) h)
  have hd := rootExponents_injective i (congrArg (fun p : PBWIndex Lattice => p.2) h)
  have hb := congrArg (fun p : PBWIndex Lattice => p.1.2 i) h
  have hb' : x.2.1 = y.2.1 := by
    simpa [rankOneIndex, coordinate, Pi.smul_apply] using hb
  exact Prod.ext ha (Prod.ext hb' hd)

private theorem rankOneMap_monomial (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) (m : ℕ × ℤ × ℕ) :
    let C := Presentation.generic q hq
    let j := rankOneIndex i m
    rankOneMap q hq i (rankOneMonomial q m) =
      orderedMonomial C j.1.1 (AddMonoidAlgebra.single j.1.2 1) j.2 := by
  intro C j
  let φ := rankOneMap q hq i
  have hK : Units.map φ.toMonoidHom (rankOneK q) = Units.map (cartan C).toMonoidHom (C.K i) :=
    Units.ext (rankOneMap_generator q hq i .K)
  have hCartan (b : ℤ) : (↑(C.K i ^ b) : Laurent k) = AddMonoidAlgebra.single (b • coordinate i) 1 := by
    have h := congrArg Units.val (map_zpow (latticeUnits k) (Multiplicative.ofAdd (coordinate i)) b)
    exact h.symm
  have hz (b : ℤ) : φ (↑(rankOneK q ^ b)) = cartan C (AddMonoidAlgebra.single (b • coordinate i) 1) := by
    change (↑(Units.map φ.toMonoidHom (rankOneK q ^ b)) : U C) = _
    rw [map_zpow, hK, ← map_zpow]
    exact congrArg (cartan C) (hCartan b)
  change φ (rankOneMonomial q m) = _
  have hF : φ (generator q .F) = F C i := rankOneMap_generator q hq i .F
  have hE : φ (generator q .E) = E C i := rankOneMap_generator q hq i .E
  simp only [rankOneMonomial, map_mul, map_pow, hF, hE, hz, j, rankOneIndex,
    orderedMonomial, rootExponents_product]

theorem generic_rankOne : genericRankOneProp.{u} := by
  intro k _ _ q hq i
  let φ := rankOneMap q hq i
  obtain ⟨b, hb⟩ := (generic q hq).2
  have hmon : φ.toLinearMap ∘ rankOneMonomial q = b ∘ rankOneIndex i := by
    funext m
    change φ (rankOneMonomial q m) = b (rankOneIndex i m)
    rw [hb]
    exact rankOneMap_monomial q hq i m
  have hli : LinearIndependent k (φ.toLinearMap ∘ rankOneMonomial q) := by
    rw [hmon]
    exact b.linearIndependent.comp _ (rankOneIndex_injective i)
  have hinj : Function.Injective φ :=
    LinearMap.injective_of_linearIndependent (rankOneMonomial_span q) hli
  refine ⟨(AlgEquiv.ofInjective φ hinj).trans (Subalgebra.equivOfEq _ _ (rankOneMap_range q hq i)), ?_⟩
  intro g
  exact rankOneMap_generator q hq i g

theorem indeterminate_rankOne : indeterminateRankOneProp.{u} := by
  intro k _ _ i
  exact generic_rankOne (rationalQ k) (rationalQ_sq_ne k) i

end RankOne

end LieNotes.Quantum.TriangularPBW
