import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.ReducedPbw
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.ReducedEnveloping
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedCenter
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedPolynomialBasis
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-! Specialization of the free polynomial basis to the reduced enveloping algebra. -/

namespace LieNotes.SuperRestricted.ReducedPbw

open _root_.Shared.Lie (U)
open _root_.Specs.LieNotes.SuperRestricted.ReducedPbw
open ReducedEnveloping RestrictedCenter RestrictedLie RestrictedPolynomialBasis
open scoped BigOperators Pointwise

universe u v w

variable {k : Type u} [Field k] {G : Type v} [LieRing G] [LieAlgebra k G]
  {n p : ℕ} [CharP k p] [NeZero p]

/-- Semilinearity lets the basis relations generate the whole reduced ideal. -/
theorem reducedRelations_eq_span_basis (power : RestrictedPower k p G)
    (b : Module.Basis (Fin n) k G) (χ : G →ₗ[k] k) :
    reducedRelations power χ =
      (TwoSidedIdeal.span (Set.range fun i =>
        pCenterElement power (b i) - algebraMap k (U k G) (χ (b i) ^ p))).asIdeal := by
  classical
  let : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let z : G →+ U k G :=
    { toFun := pCenterElement power
      map_zero' := by
        simpa only [zero_smul, zero_pow (NeZero.ne p)] using pCenterElement_smul power 0 (0 : G)
      map_add' := pCenterElement_add power }
  let c : G →+ U k G :=
    (algebraMap k (U k G)).toAddMonoidHom.comp
      ((frobenius k p).toAddMonoidHom.comp χ.toAddMonoidHom)
  let rel := z - c
  have hrel (x : G) : rel x = pCenterElement power x - algebraMap k (U k G) (χ x ^ p) :=
    rfl
  have hsmul (a : k) (x : G) : rel (a • x) = a ^ p • rel x := by
    rw [hrel, hrel, pCenterElement_smul, map_smul, smul_eq_mul, mul_pow, map_mul,
      smul_sub, Algebra.smul_def (a ^ p) (algebraMap k (U k G) (χ x ^ p))]
  change (TwoSidedIdeal.span (Set.range rel)).asIdeal =
    (TwoSidedIdeal.span (Set.range fun i => rel (b i))).asIdeal
  apply congrArg TwoSidedIdeal.asIdeal
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    apply (TwoSidedIdeal.span (Set.range fun i => rel (b i))).asIdeal.sum_mem
    intro i _
    rw [hsmul, Algebra.smul_def]
    exact TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span (Set.mem_range_self i))
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact TwoSidedIdeal.subset_span (Set.mem_range_self (b i))

/-- Evaluating the polynomial coordinates at the character leaves the images of the
bounded ordered monomials as a basis over the ground field. -/
theorem reducedBasis (power : RestrictedPower k p G)
    (b : Module.Basis (Fin n) k G) (χ : G →ₗ[k] k) :
    ∃ D : Module.Basis (Fin n → Fin p) k (ReducedEnvelopingAlgebra power χ),
      ∀ r, D r = quotientMap power χ (restrictedMonomial b r) := by
  classical
  obtain ⟨e, he, B, hB⟩ := polynomialBasis power b
  let P := MvPolynomial (Fin n) k
  let R := Fin n → Fin p
  let Q := ReducedEnvelopingAlgebra power χ
  let q : U k G →ₐ[k] Q := quotientMap power χ
  let ψ : P →ₐ[k] U k G := (pCenter power).val.comp e.toAlgHom
  let : Module P (U k G) := ψ.toRingHom.toModule
  let ev : P →ₐ[k] k := MvPolynomial.aeval fun i => χ (b i) ^ p
  have hX (i : Fin n) : ψ (MvPolynomial.X i) = pCenterElement power (b i) := he i
  have hevX (i : Fin n) : ev (MvPolynomial.X i) = χ (b i) ^ p := MvPolynomial.aeval_X _ _
  have hevC (a : k) : ev (MvPolynomial.C a) = a := MvPolynomial.aeval_C _ _
  obtain ⟨hqSurj, hqZero, hqGen⟩ := quotientMap_spec power χ
  have hqEval (f : P) : q (ψ f) = algebraMap k Q (ev f) := by
    have h : q.comp ψ = (Algebra.ofId k Q).comp ev := by
      apply MvPolynomial.algHom_ext
      intro i
      change q (ψ (MvPolynomial.X i)) = algebraMap k Q (ev (MvPolynomial.X i))
      rw [hX, hevX]
      exact hqGen (b i)
    exact DFunLike.congr_fun h f
  let E : U k G →+ (R → k) :=
    { toFun := fun x r => ev (B.equivFun x r)
      map_zero' := by
        funext r
        simp only [map_zero, Pi.zero_apply]
      map_add' := by
        intro x y
        funext r
        simp only [map_add, Pi.add_apply] }
  have hEvalMul (f : P) (x : U k G) : E (ψ f * x) = ev f • E x := by
    change E (f • x) = _
    funext r
    change ev (B.equivFun (f • x) r) = ev f * ev (B.equivFun x r)
    rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  have hKill (x : U k G) (hx : x ∈ reducedRelations power χ) : E x = 0 := by
    rw [reducedRelations_eq_span_basis power b χ, TwoSidedIdeal.mem_asIdeal,
      TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
    induction hx using AddSubgroup.closure_induction with
    | mem _ hy =>
      rcases hy with ⟨_, ⟨a, _, _, ⟨i, rfl⟩, rfl⟩, d, _, rfl⟩
      let f : P := MvPolynomial.X i - MvPolynomial.C (χ (b i) ^ p)
      have hf : ψ f = pCenterElement power (b i) - algebraMap k (U k G) (χ (b i) ^ p) := by
        change ψ (_ - _) = _
        rw [map_sub, hX]
        exact congrArg (_ - ·) (ψ.commutes _)
      have hc : Commute (ψ f) a := by
        rw [hf]
        exact (pCenterElement_commute power (b i) a).sub_left (Algebra.commutes _ _)
      change E (a * (pCenterElement power (b i) - algebraMap k (U k G) (χ (b i) ^ p)) * d) = 0
      rw [← hf, ← hc.eq, mul_assoc, hEvalMul]
      have hf0 : ev f = 0 := by
        change ev (_ - _) = 0
        rw [map_sub, hevX, hevC, sub_self]
      rw [hf0, zero_smul]
    | zero => exact map_zero E
    | add _ _ _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | neg _ _ hx => rw [map_neg, hx, neg_zero]
  let J : (R → k) →ₗ[k] Q := Fintype.linearCombination k (fun r => q (B r))
  have hJ (x : U k G) : J (E x) = q x := by
    rw [Fintype.linearCombination_apply]
    calc
      ∑ r, E x r • q (B r) = ∑ r, q (B.repr x r • B r) := by
        apply Finset.sum_congr rfl
        intro r _
        change ev (B.equivFun x r) • q (B r) = q (ψ (B.repr x r) * B r)
        rw [B.equivFun_apply, map_mul, hqEval, Algebra.smul_def]
      _ = q x := by rw [← map_sum, B.sum_repr]
  have hJInj : Function.Injective J := by
    apply (injective_iff_map_eq_zero J).mpr
    intro c hc
    let x : U k G := B.equivFun.symm (fun r => MvPolynomial.C (c r))
    have hx : E x = c := by
      funext r
      change ev (B.equivFun (B.equivFun.symm _) r) = c r
      rw [LinearEquiv.apply_symm_apply, hevC]
    have hqx : q x = 0 := by rw [← hJ x, hx, hc]
    exact hx.symm.trans (hKill x ((hqZero x).mp hqx))
  have hJSurj : Function.Surjective J := by
    intro y
    obtain ⟨x, rfl⟩ := hqSurj y
    exact ⟨E x, hJ x⟩
  let j := LinearEquiv.ofBijective J ⟨hJInj, hJSurj⟩
  refine ⟨(Pi.basisFun k R).map j, fun r => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  change J (Pi.single r 1) = q (restrictedMonomial b r)
  rw [Fintype.linearCombination_apply_single, one_smul, hB]

/-- The reduced enveloping algebra of an (n)-dimensional Lie algebra has dimension (p^n). -/
theorem reducedFinrank [Module.Finite k G] (power : RestrictedPower k p G)
    (χ : G →ₗ[k] k) :
    Module.Finite k (ReducedEnvelopingAlgebra power χ) ∧
      Module.finrank k (ReducedEnvelopingAlgebra power χ) = p ^ Module.finrank k G := by
  obtain ⟨B, _⟩ := reducedBasis power (Module.finBasis k G) χ
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [Module.finrank_eq_card_basis B, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The full polynomial p-center and reduced PBW theorem. -/
theorem polynomialCenterAndReducedPbw : polynomialCenterAndReducedPbwType.{u,v,w} := by
  refine ⟨pCenterElement_commute, pCenter_le_center, pCenterElement_add, pCenterElement_smul,
    pCenter_eq_adjoin_basis, polynomialBasis, centerBasis, reducedRelations_eq_span_basis, reducedBasis,
    reducedFinrank, ?_⟩
  intro k _ G _ _ p _ _ power
  exact ⟨zeroCharacterEquiv power, zeroCharacterEquiv_quotientMap power⟩

end LieNotes.SuperRestricted.ReducedPbw
