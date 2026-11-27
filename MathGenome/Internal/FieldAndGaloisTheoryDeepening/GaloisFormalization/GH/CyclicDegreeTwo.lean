import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.CyclicDegreeTwo
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Abel

namespace GaloisFormalization.GH

noncomputable section

/-- The cyclic norm on the coefficient module. -/
abbrev cyclicNorm := @CyclicDegreeTwo.norm

/-- The carry cochain for a specified generator and invariant coefficient. -/
abbrev cyclicCarryCochain := @CyclicDegreeTwo.carryCochain

open scoped BigOperators
open Model (continuousSMul_of_discrete)
open CyclicDegreeTwo
open private vec_two from MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.Cochains

universe u v

section Cyclic

variable {C : Type u} [Group C] [Finite C]
variable {A : Type v} [AddCommGroup A] [DistribMulAction C A]
variable [TopologicalSpace C] [DiscreteTopology C]
variable [TopologicalSpace A] [DiscreteTopology A]

omit [TopologicalSpace C] [DiscreteTopology C] in
private theorem powerEquiv_symm_pow (s : C) (hs : Subgroup.zpowers s = ⊤) (n : ℕ) :
    (powerEquiv s hs).symm (s ^ n) = ⟨n % orderOf s, Nat.mod_lt _ (orderOf_pos s)⟩ := by
  apply (powerEquiv s hs).injective
  rw [Equiv.apply_symm_apply, powerEquiv_apply]
  exact (pow_mod_orderOf s n).symm

/-- Sum the values in the column corresponding to the generator. -/
private def generatorSum (s : C) (c : continuousCochains C A 2) : A :=
  ∑ i : Fin (orderOf s), c.val ![s ^ (i : ℕ), s]

omit [DistribMulAction C A] [DiscreteTopology C] in
private theorem generatorSum_eq_sum [Fintype C] (s : C) (hs : Subgroup.zpowers s = ⊤)
    (c : continuousCochains C A 2) :
    generatorSum s c = ∑ g : C, c.val ![g, s] :=
  Fintype.sum_equiv (powerEquiv s hs) _ _ (fun _ => rfl)

private theorem generatorSum_mem_invariants (s : C) (hs : Subgroup.zpowers s = ⊤)
    (c : continuousCocycles C A 2) : generatorSum s c.val ∈ Invariants C A := by
  classical
  let := Fintype.ofFinite C
  -- Sum the cocycle identity and reindex both translated columns.
  rw [Model.mem_fixedCoefficients, generatorSum_eq_sum s hs]
  intro g _
  have hc := (mem_continuousCocycles_two c.val).mp c.property
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset C)) rfl (fun x _ => hc g x s)
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum] at h
  have leftShift : (∑ x : C, c.val.val ![g * x, s]) = ∑ x : C, c.val.val ![x, s] :=
    Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)
  have rightShift : (∑ x : C, c.val.val ![g, x * s]) = ∑ x : C, c.val.val ![g, x] :=
    Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun _ => rfl)
  rw [leftShift, rightShift, add_comm (g • _)] at h
  exact (add_left_cancel h).symm

private def generatorSumMap (s : C) (hs : Subgroup.zpowers s = ⊤) :
    continuousCocycles C A 2 →ₗ[ℤ] Invariants C A :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun c => ⟨generatorSum s c.val, generatorSum_mem_invariants s hs c⟩
      map_zero' := by
        apply Subtype.ext
        change (∑ _ : Fin (orderOf s), (0 : A)) = 0
        simp
      map_add' := by
        intro c z
        apply Subtype.ext
        change (∑ i : Fin (orderOf s), (c.val.val ![s ^ (i : ℕ), s] +
          z.val.val ![s ^ (i : ℕ), s])) = _
        exact Finset.sum_add_distrib }

private theorem generatorSum_differential (s : C) (hs : Subgroup.zpowers s = ⊤)
    (f : continuousCochains C A 1) :
    generatorSum s (continuousDifferential C A 1 f) = (cyclicNorm s hs (f.val ![s])).val := by
  classical
  let := Fintype.ofFinite C
  rw [generatorSum_eq_sum s hs, CyclicDegreeTwo.norm_val]
  simp only [differential_one, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have rightShift : (∑ x : C, f.val ![x * s]) = ∑ x : C, f.val ![x] :=
    Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun _ => rfl)
  have reindex : (∑ i : Fin (orderOf s), s ^ (i : ℕ) • f.val ![s]) =
      ∑ x : C, x • f.val ![s] :=
    Fintype.sum_equiv (powerEquiv s hs) _ _ (fun _ => rfl)
  rw [rightShift, reindex]
  abel

private def cohomologyToNormQuotient (s : C) (hs : Subgroup.zpowers s = ⊤) :
    ContinuousH C A 2 →ₗ[ℤ] NormQuotient s hs A :=
  (continuousCoboundaries C A 2).liftQ
    ((LinearMap.range (cyclicNorm s hs)).mkQ.comp (generatorSumMap (A := A) s hs)) (by
      intro c hc
      rcases hc with ⟨f, hf⟩
      rw [LinearMap.mem_ker]
      change (LinearMap.range (cyclicNorm s hs)).mkQ (generatorSumMap (A := A) s hs c) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      refine ⟨f.val ![s], Subtype.ext ?_⟩
      change (cyclicNorm s hs (f.val ![s])).val = generatorSum s c.val
      rw [← generatorSum_differential s hs f, ← hf]
      rfl)

private theorem cohomologyToNormQuotient_class (s : C) (hs : Subgroup.zpowers s = ⊤)
    (c : continuousCocycles C A 2) :
    cohomologyToNormQuotient (A := A) s hs (continuousClass C A 2 c) =
      (LinearMap.range (cyclicNorm s hs)).mkQ (generatorSumMap (A := A) s hs c) := rfl

private theorem exists_differential_of_generatorSum_eq_norm (s : C)
    (hs : Subgroup.zpowers s = ⊤) (c : continuousCocycles C A 2) (b : A)
    (hb : generatorSum s c.val = (cyclicNorm s hs b).val) :
    ∃ t : continuousCochains C A 1, continuousDifferential C A 1 t = c.val := by
  have hc := (mem_continuousCocycles_two c.val).mp c.property
  have hleft : c.val.val ![1, s] = c.val.val ![1, 1] := by
    simpa only [one_mul, one_smul, add_right_cancel_iff] using (hc 1 1 s).symm
  have hright (g : C) : c.val.val ![g, 1] = g • c.val.val ![1, 1] := by
    simpa only [mul_one, add_right_cancel_iff] using hc g 1 1
  -- Summing the coboundary recurrence gives a primitive on the powers of the generator.
  let F (n : ℕ) : A :=
    c.val.val ![1, 1] + ∑ i ∈ Finset.range n, (s ^ i • b - c.val.val ![s ^ i, s])
  have hFzero : F 0 = c.val.val ![1, 1] := by simp [F]
  have hFone : F 1 = b := by
    simp only [F, Finset.sum_range_one, pow_zero, one_smul, hleft]
    abel
  have hFperiod : F (orderOf s) = F 0 := by
    rw [generatorSum, Fin.sum_univ_eq_sum_range (fun i => c.val.val ![s ^ i, s]),
      CyclicDegreeTwo.norm_val, Fin.sum_univ_eq_sum_range (fun i => s ^ i • b)] at hb
    simp only [F, Finset.sum_sub_distrib, Finset.sum_range_zero, add_zero, hb, sub_self]
  have hFsucc (i : ℕ) : F (i + 1) = F i + (s ^ i • b - c.val.val ![s ^ i, s]) := by
    simp only [F, Finset.sum_range_succ, add_assoc]
  let f (g : C) : A := F ((powerEquiv s hs).symm g : ℕ)
  have hf (i : ℕ) (hi : i ≤ orderOf s) : f (s ^ i) = F i := by
    simp only [f, powerEquiv_symm_pow]
    rcases lt_or_eq_of_le hi with h | rfl
    · rw [Nat.mod_eq_of_lt h]
    · rw [Nat.mod_self, hFperiod]
  have hfone : f 1 = c.val.val ![1, 1] := by
    simpa only [pow_zero, hFzero] using hf 0 (Nat.zero_le _)
  have hfs : f s = b := by
    simpa only [pow_one, hFone] using hf 1 (orderOf_pos s)
  let t : continuousCochains C A 1 := cochainOne f continuous_of_discreteTopology
  let dt := continuousDifferential C A 1 t
  have hdt (g h : C) : dt.val ![g, h] = f g + g • f h - f (g * h) := by
    rw [differential_one]
    rfl
  have hcolumn (g : C) : c.val.val ![g, s] = dt.val ![g, s] := by
    obtain ⟨i, rfl⟩ := (powerEquiv s hs).surjective g
    change c.val.val ![s ^ (i : ℕ), s] = dt.val ![s ^ (i : ℕ), s]
    rw [hdt, hfs, ← pow_succ, hf _ i.isLt.le, hf _ i.isLt, hFsucc]
    abel
  -- The cocycle identity propagates agreement from the generator column to every column.
  have hdc := (mem_continuousCocycles_two dt).mp (Model.continuousDifferential_sq C A 1 t)
  have hrow (g : C) (n : ℕ) : c.val.val ![g, s ^ n] = dt.val ![g, s ^ n] := by
    induction n with
    | zero => rw [pow_zero, hright, hdt, hfone, mul_one]; abel
    | succ n ih =>
      have hcstep := hc g (s ^ n) s
      have hdstep := hdc g (s ^ n) s
      rw [← pow_succ] at hcstep hdstep
      rw [← ih, ← hcolumn (g * s ^ n), ← hcolumn (s ^ n)] at hdstep
      exact add_left_cancel (hcstep.symm.trans hdstep)
  refine ⟨t, Subtype.ext (funext fun x => ?_)⟩
  rw [← vec_two x]
  obtain ⟨i, hi⟩ := (powerEquiv s hs).surjective (x 1)
  rw [← hi]
  exact (hrow (x 0) i).symm

private theorem cohomologyToNormQuotient_injective (s : C) (hs : Subgroup.zpowers s = ⊤) :
    Function.Injective (cohomologyToNormQuotient (A := A) s hs) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨c, rfl⟩ := continuousClass_surjective (G := C) (M := A) 2 x
  rw [cohomologyToNormQuotient_class, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨b, hb⟩ := hx
  have hbc : generatorSum s c.val = (cyclicNorm s hs b).val :=
    (congrArg Subtype.val hb).symm
  obtain ⟨t, ht⟩ := exists_differential_of_generatorSum_eq_norm s hs c b hbc
  rw [← map_zero (continuousClass C A 2), continuousClass_succ_eq_iff]
  exact ⟨t, by simpa only [Submodule.coe_zero, sub_zero] using ht⟩

private def carryBit (d i j : ℕ) : ℕ := if i + j < d then 0 else 1

private theorem add_eq_mod_add_carry (d i j : ℕ) (hi : i < d) (hj : j < d) :
    i + j = (i + j) % d + d * carryBit d i j := by
  have h := @Nat.mod_add_mod_eq i j d
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
  by_cases hij : i + j < d <;> simpa [carryBit, hij] using h

private theorem carryBit_assoc (d i j k : ℕ) (hi : i < d) (hj : j < d) (hk : k < d) :
    carryBit d i j + carryBit d ((i + j) % d) k =
      carryBit d j k + carryBit d i ((j + k) % d) := by
  have hd : 0 < d := by omega
  have h₁ := add_eq_mod_add_carry d i j hi hj
  have h₂ := add_eq_mod_add_carry d ((i + j) % d) k (Nat.mod_lt _ hd) hk
  have h₃ := add_eq_mod_add_carry d j k hj hk
  have h₄ := add_eq_mod_add_carry d i ((j + k) % d) hi (Nat.mod_lt _ hd)
  rw [Nat.mod_add_mod] at h₂
  rw [Nat.add_mod_mod, ← Nat.add_assoc] at h₄
  apply Nat.eq_of_mul_eq_mul_left hd
  simp only [Nat.mul_add]
  omega

private theorem carryCochain_apply_pow_nsmul (s : C) (hs : Subgroup.zpowers s = ⊤)
    (a : Invariants C A) (i j : Fin (orderOf s)) :
    (cyclicCarryCochain s hs a).val ![s ^ (i : ℕ), s ^ (j : ℕ)] =
      carryBit (orderOf s) i j • (a : A) := by
  rw [carryCochain_apply_pow]
  by_cases h : (i : ℕ) + (j : ℕ) < orderOf s <;> simp [carryBit, h]

/-- The normalized carry cochain is a cocycle. -/
def cyclicCarryCocycle (s : C) (hs : Subgroup.zpowers s = ⊤) (a : Invariants C A) :
    continuousCocycles C A 2 :=
  ⟨cyclicCarryCochain s hs a, (mem_continuousCocycles_two _).mpr (by
    intro g h l
    obtain ⟨i, rfl⟩ := (powerEquiv s hs).surjective g
    obtain ⟨j, rfl⟩ := (powerEquiv s hs).surjective h
    obtain ⟨k, rfl⟩ := (powerEquiv s hs).surjective l
    let c := cyclicCarryCochain s hs a
    let addIndex (i j : Fin (orderOf s)) : Fin (orderOf s) :=
      ⟨(i.val + j.val) % orderOf s, Nat.mod_lt _ (orderOf_pos s)⟩
    have hmul (i j : Fin (orderOf s)) :
        s ^ i.val * s ^ j.val = s ^ (addIndex i j).val :=
      (pow_add s i.val j.val).symm.trans (pow_mod_orderOf s _).symm
    change c.val ![s ^ i.val, s ^ j.val] + c.val ![s ^ i.val * s ^ j.val, s ^ k.val] =
      s ^ i.val • c.val ![s ^ j.val, s ^ k.val] + c.val ![s ^ i.val, s ^ j.val * s ^ k.val]
    rw [hmul i j, hmul j k]
    simp only [c, carryCochain_apply_pow_nsmul]
    have hfixed : s ^ i.val • (a : A) = a :=
      (Model.mem_fixedCoefficients C A ⊤ a).mp a.property _ (Subgroup.mem_top _)
    have hsmul (n : ℕ) : s ^ i.val • (n • (a : A)) = n • (a : A) :=
      (map_nsmul (DistribSMul.toAddMonoidHom A (s ^ i.val)) n (a : A)).trans
        (congrArg (fun x : A => n • x) hfixed)
    rw [hsmul, ← add_nsmul, ← add_nsmul]
    exact congrArg (fun n : ℕ => n • (a : A))
      (carryBit_assoc _ _ _ _ i.isLt j.isLt k.isLt))⟩

private theorem generatorSum_carry (s : C) (hs : Subgroup.zpowers s = ⊤)
    (a : Invariants C A) (hd : 1 < orderOf s) :
    generatorSumMap (A := A) s hs (cyclicCarryCocycle s hs a) = a := by
  apply Subtype.ext
  let last : Fin (orderOf s) := ⟨orderOf s - 1, by omega⟩
  let j : Fin (orderOf s) := ⟨1, hd⟩
  change (∑ i : Fin (orderOf s), (cyclicCarryCochain s hs a).val ![s ^ i.val, s]) = a.val
  have hsum : (∑ i : Fin (orderOf s), (cyclicCarryCochain s hs a).val ![s ^ i.val, s]) =
      ∑ i : Fin (orderOf s), (cyclicCarryCochain s hs a).val ![s ^ i.val, s ^ j.val] := by
    simp only [j, pow_one]
  rw [hsum]
  simp only [carryCochain_apply_pow]
  rw [Finset.sum_eq_single last]
  · exact ite_eq_right (show ¬ last.val + j.val < orderOf s from by
      change ¬ orderOf s - 1 + 1 < orderOf s
      omega)
  · intro i _ hi
    apply ite_eq_left
    have hne : i.val ≠ orderOf s - 1 := fun h => hi (Fin.ext h)
    change i.val + 1 < orderOf s
    have := i.isLt
    omega
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace A] [DiscreteTopology A] in
private theorem normQuotient_subsingleton_of_order_one (s : C) (hs : Subgroup.zpowers s = ⊤)
    (hd : orderOf s = 1) : Subsingleton (NormQuotient s hs A) := by
  have hz (q : NormQuotient s hs A) : q = 0 := by
    obtain ⟨a, rfl⟩ := (LinearMap.range (cyclicNorm (A := A) s hs)).mkQ_surjective q
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨a.val, Subtype.ext ?_⟩
    rw [CyclicDegreeTwo.norm_val, Fin.sum_univ_eq_sum_range (fun i => s ^ i • (a : A)),
      hd, Finset.sum_range_one, pow_zero, one_smul]
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem cohomologyToNormQuotient_carry (s : C) (hs : Subgroup.zpowers s = ⊤)
    (a : Invariants C A) :
    cohomologyToNormQuotient (A := A) s hs (continuousClass C A 2 (cyclicCarryCocycle s hs a)) =
      (LinearMap.range (cyclicNorm s hs)).mkQ a := by
  by_cases hd : orderOf s = 1
  · exact @Subsingleton.elim _ (normQuotient_subsingleton_of_order_one s hs hd) _ _
  · have hp := orderOf_pos s
    rw [cohomologyToNormQuotient_class, generatorSum_carry s hs a (by omega)]

private theorem cohomologyToNormQuotient_surjective (s : C) (hs : Subgroup.zpowers s = ⊤) :
    Function.Surjective (cohomologyToNormQuotient (A := A) s hs) := by
  intro q
  obtain ⟨a, rfl⟩ := (LinearMap.range (cyclicNorm (A := A) s hs)).mkQ_surjective q
  exact ⟨_, cohomologyToNormQuotient_carry s hs a⟩

/-- Second cohomology of a finite cyclic group as invariants modulo norms. -/
def cyclicDegreeTwoEquiv (s : C) (hs : Subgroup.zpowers s = ⊤) :
    ContinuousH C A 2 ≃+ NormQuotient s hs A :=
  AddEquiv.ofBijective (cohomologyToNormQuotient (A := A) s hs).toAddMonoidHom
    ⟨cohomologyToNormQuotient_injective s hs, cohomologyToNormQuotient_surjective s hs⟩

theorem cyclicDegreeTwoEquiv_symm_mk (s : C) (hs : Subgroup.zpowers s = ⊤)
    (a : Invariants C A) :
    (cyclicDegreeTwoEquiv (A := A) s hs).symm ((LinearMap.range (cyclicNorm s hs)).mkQ a) =
      continuousClass C A 2 (cyclicCarryCocycle s hs a) :=
  (cyclicDegreeTwoEquiv (A := A) s hs).symm_apply_eq.mpr (cohomologyToNormQuotient_carry s hs a).symm

end Cyclic

theorem cyclic_degree_two : CyclicDegreeTwo.Specification.EquivalenceWithCarry.{u, v} := by
  intro C A _ _ _ _ _ _ _ _ s hs
  exact ⟨cyclicDegreeTwoEquiv s hs, fun a =>
    ⟨cyclicCarryCocycle s hs a, rfl, cyclicDegreeTwoEquiv_symm_mk s hs a⟩⟩

theorem cyclic_degree_two_order_one : CyclicDegreeTwo.Specification.OrderOneTriviality.{u, v} := by
  intro C A _ _ _ _ _ _ _ _ s hs hd
  let := normQuotient_subsingleton_of_order_one (A := A) s hs hd
  exact ⟨⟨fun x y => (cyclicDegreeTwoEquiv (A := A) s hs).injective
    (Subsingleton.elim _ _)⟩, inferInstance⟩

private def submoduleQuotientEquivOfSurjective {M N : Type*} [AddCommGroup M] [AddGroup N]
    (p : Submodule ℤ M) (f : M →+ N) (hker : p.toAddSubgroup = f.ker)
    (hf : Function.Surjective f) : M ⧸ p ≃+ N := by
  let e := QuotientAddGroup.quotientKerEquivOfSurjective f hf
  let ep := QuotientAddGroup.quotientAddEquivOfEq hker
  exact ep.trans e

section Fields

open scoped CyclicDegreeTwo
open Model (additiveCoefficientAction)

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]

private def baseUnitToInvariant : Additive kˣ →+ Invariants (E ≃ₐ[k] E) (Additive Eˣ) :=
  let e : Additive kˣ →+ Additive Eˣ := (Units.map (algebraMap k E).toMonoidHom).toAdditive
  { toFun := fun a => ⟨e a, (Model.mem_fixedCoefficients _ _ ⊤ _).mpr (by
      intro g _
      apply Units.ext
      exact g.commutes (a.toMul : k))⟩
    map_zero' := Subtype.ext (map_zero e)
    map_add' := fun a b => Subtype.ext (map_add e a b) }

variable [FiniteDimensional k E] [IsGalois k E]

private def baseUnitEquivInvariant : Additive kˣ ≃+ Invariants (E ≃ₐ[k] E) (Additive Eˣ) :=
  AddEquiv.ofBijective (baseUnitToInvariant k E) (by
    constructor
    · intro a b h
      exact Units.map_injective (algebraMap k E).injective (congrArg Subtype.val h)
    · intro a
      have hfix (g : E ≃ₐ[k] E) : g (a.val.toMul : E) = (a.val.toMul : E) :=
        congrArg (fun x : Additive Eˣ => (x.toMul : E))
          ((Model.mem_fixedCoefficients _ _ ⊤ _).mp a.property g (Subgroup.mem_top _))
      obtain ⟨x, hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
        (F := k) (a.val.toMul : E)).mpr hfix
      have hx0 : x ≠ 0 := by
        intro h
        exact a.val.toMul.ne_zero (by simpa [h] using hx.symm)
      exact ⟨Additive.ofMul (Units.mk0 x hx0), Subtype.ext (Units.ext hx)⟩)

private theorem norm_eq_baseUnitEquivInvariant (s : E ≃ₐ[k] E) (hs : Subgroup.zpowers s = ⊤)
    (b : Additive Eˣ) :
    cyclicNorm s hs b = baseUnitEquivInvariant k E (Additive.ofMul (fieldUnitNorm k E b.toMul)) := by
  classical
  apply Subtype.ext
  apply Units.ext
  change (((cyclicNorm s hs b).val.toMul : Eˣ) : E) = algebraMap k E (Algebra.norm k (b.toMul : E))
  rw [CyclicDegreeTwo.norm_val, toMul_sum, Units.coe_prod]
  exact (Fintype.prod_equiv (powerEquiv s hs) _ _ (fun _ => rfl)).trans
    (Algebra.norm_eq_prod_automorphisms k (b.toMul : E)).symm

private def invariantToFieldNormQuotient :
    Invariants (E ≃ₐ[k] E) (Additive Eˣ) →+ Additive (kˣ ⧸ (fieldUnitNorm k E).range) :=
  (QuotientGroup.mk' (fieldUnitNorm k E).range).toAdditive.comp
    (baseUnitEquivInvariant k E).symm.toAddMonoidHom

private theorem invariantToFieldNormQuotient_ker (s : E ≃ₐ[k] E) (hs : Subgroup.zpowers s = ⊤) :
    (LinearMap.range (cyclicNorm (A := Additive Eˣ) s hs)).toAddSubgroup =
      (invariantToFieldNormQuotient k E).ker := by
  let e := baseUnitEquivInvariant k E
  apply SetLike.ext
  intro a
  change a ∈ LinearMap.range (cyclicNorm (A := Additive Eˣ) s hs) ↔
    (↑((e.symm a).toMul) : kˣ ⧸ (fieldUnitNorm k E).range) = 1
  rw [QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨b.toMul, ?_⟩
    have hn : cyclicNorm s hs b = e (Additive.ofMul (fieldUnitNorm k E b.toMul)) :=
      norm_eq_baseUnitEquivInvariant k E s hs b
    rw [hn]
    exact congrArg Additive.toMul (e.symm_apply_apply _).symm
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    have hn : cyclicNorm s hs (Additive.ofMul b) = e (Additive.ofMul (fieldUnitNorm k E b)) :=
      norm_eq_baseUnitEquivInvariant k E s hs (Additive.ofMul b)
    exact hn.trans ((congrArg (fun x : kˣ => e (Additive.ofMul x)) hb).trans (e.apply_symm_apply a))

private theorem invariantToFieldNormQuotient_surjective :
    Function.Surjective (invariantToFieldNormQuotient k E) := by
  intro q
  let e := baseUnitEquivInvariant k E
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (fieldUnitNorm k E).range q.toMul
  refine ⟨e (Additive.ofMul a), ?_⟩
  change Additive.ofMul (QuotientGroup.mk' (fieldUnitNorm k E).range
    ((e.symm (e (Additive.ofMul a))).toMul)) = q
  rw [e.symm_apply_apply]
  exact congrArg Additive.ofMul ha

set_option backward.isDefEq.respectTransparency false in
private def invariantQuotientEquivFieldNorm (s : E ≃ₐ[k] E) (hs : Subgroup.zpowers s = ⊤) :
    NormQuotient s hs (Additive Eˣ) ≃+ Additive (kˣ ⧸ (fieldUnitNorm k E).range) :=
  submoduleQuotientEquivOfSurjective (N := Additive (kˣ ⧸ (fieldUnitNorm k E).range))
    (LinearMap.range (cyclicNorm (A := Additive Eˣ) s hs))
    (invariantToFieldNormQuotient k E) (invariantToFieldNormQuotient_ker k E s hs)
    (invariantToFieldNormQuotient_surjective k E)

/-- The cyclic cohomology formula for the natural action on the units of a finite Galois extension. -/
def cyclicFieldDegreeTwoEquiv (s : E ≃ₐ[k] E) (hs : Subgroup.zpowers s = ⊤) :
    ContinuousMulH (E ≃ₐ[k] E) Eˣ 2 ≃* (kˣ ⧸ (fieldUnitNorm k E).range) :=
  AddEquiv.toMultiplicativeLeft ((cyclicDegreeTwoEquiv (A := Additive Eˣ) s hs).trans
    (invariantQuotientEquivFieldNorm k E s hs))

end Fields

theorem cyclic_field_degree_two : CyclicDegreeTwo.Specification.FieldEquivalence.{u, v} := by
  intro k E _ _ _ _ _ hcyc
  obtain ⟨s, hs⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  exact ⟨cyclicFieldDegreeTwoEquiv k E s hs⟩

end

end GaloisFormalization.GH
