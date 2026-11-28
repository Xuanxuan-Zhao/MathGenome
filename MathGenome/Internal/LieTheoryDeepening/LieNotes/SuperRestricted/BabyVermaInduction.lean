import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.SuperRestricted.BabyVermaInduction
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.ReducedEnveloping
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.ReducedPbw
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import MathGenome.Internal.LieTheoryDeepening.LieNotes.SuperRestricted.RestrictedSlTwo
import Mathlib.Tactic.FinCases

/-! Induction from the upper triangular Borel of restricted sl₂. -/

namespace LieNotes.SuperRestricted.BabyVermaInduction

open _root_.Specs.LieNotes.SuperRestricted.BabyVermaInduction
open _root_.Specs.LieNotes.SuperRestricted.RestrictedLie (restrictedPowerValue)
open _root_.Specs.LieNotes.SuperRestricted.ReducedEnveloping
  (reducedEnvelopingValue reducedRelationsValue pCenterElementValue quotientMapValue)
open _root_.Shared.Lie (U inclusion)
open _root_.Specs.LieNotes.SuperRestricted.RestrictedPolynomialBasis (restrictedMonomialValue)
open _root_.Specs.LieAlgebrasAndRepresentations.Sl2Model (Model H E F)

abbrev borel := @borelValue
abbrev Induced := @inducedValue
abbrev BabyVerma := @Specs.LieNotes.SuperRestricted.BabyVermaInduction.BabyVerma

universe u w

/-- The Borel basis is ordered as h, e. -/
theorem borelBasis : borelBasisType.{u} := by
  intro k _
  have hH : (H k).val = !![1, 0; 0, -1] := LieAlgebrasAndRepresentations.sl2_h_val k
  have hE : (E k).val = !![0, 1; 0, 0] := LieAlgebrasAndRepresentations.sl2_e_val k
  let coords : Borel k →ₗ[k] (Fin 2 → k) :=
    { toFun := fun x j => x.val.val 0 j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hInjective : Function.Injective coords := by
    intro x y h
    have hx : x.val.val 1 0 = 0 := x.property
    have hy : y.val.val 1 0 = 0 := y.property
    have ht (z : Borel k) : z.val.val 1 1 = -z.val.val 0 0 := by
      have htrace : z.val.val.trace = 0 := z.val.property
      rw [Matrix.trace_fin_two, add_comm, add_eq_zero_iff_eq_neg] at htrace
      exact htrace
    have h00 : x.val.val 0 0 = y.val.val 0 0 := congrFun h 0
    have h01 : x.val.val 0 1 = y.val.val 0 1 := congrFun h 1
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact hx.trans hy.symm
    · change x.val.val 1 1 = y.val.val 1 1
      rw [ht, ht, h00]
  have hh : coords (borelH k) = Pi.single 0 1 := by
    funext i
    change (H k).val 0 i = _
    rw [hH]
    fin_cases i <;> simp
  have he : coords (borelE k) = Pi.single 1 1 := by
    funext i
    change (E k).val 0 i = _
    rw [hE]
    fin_cases i <;> simp
  have hSurjective : Function.Surjective coords := by
    intro c
    refine ⟨c 0 • borelH k + c 1 • borelE k, ?_⟩
    rw [map_add, map_smul, map_smul, hh, he]
    funext i
    fin_cases i <;> simp
  let e := LinearEquiv.ofBijective coords ⟨hInjective, hSurjective⟩
  refine ⟨(Pi.basisFun k (Fin 2)).map e.symm, ?_, ?_⟩
  · apply hInjective
    change e (e.symm ((Pi.basisFun k (Fin 2)) 0)) = _
    rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, hh]
  · apply hInjective
    change e (e.symm ((Pi.basisFun k (Fin 2)) 1)) = _
    rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply, he]

section Tensor

variable {k A B : Type*} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (j : B →ₐ[k] A) (θ : B →ₐ[k] k)

private theorem mkQ_eq_smul_highest (a : A) :
    (balance j θ).mkQ a = a • highest j θ := by
  rw [highest, ← LinearMap.map_smul]
  change _ = (balance j θ).mkQ (a * 1)
  rw [mul_one]

private theorem balance_generator (b : B) :
    (balance j θ).mkQ (j b) = (balance j θ).mkQ (algebraMap k A (θ b)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span ⟨b, rfl⟩

/-- Multiplying the highest tensor by the image of a Borel element
    acts through the scalar-line character. -/
theorem smul_highest (b : B) :
    j b • highest j θ = θ b • highest j θ := by
  rw [highest, ← LinearMap.map_smul, ← LinearMap.map_smul_of_tower]
  change (balance j θ).mkQ (j b * 1) = _
  rw [mul_one, ← Algebra.algebraMap_eq_smul_one]
  exact balance_generator j θ b

/-- The pure tensors satisfy balancing over the reduced Borel algebra. -/
theorem tensor_balance (a : A) (b : B) (t : k) :
    tensor j θ (a * j b) t = tensor j θ a (θ b * t) := by
  unfold tensor
  rw [(balance j θ).mkQ.map_smul_of_tower t (a * j b),
    (balance j θ).mkQ.map_smul_of_tower (θ b * t) a,
    mkQ_eq_smul_highest, mkQ_eq_smul_highest, mul_smul, smul_highest,
    smul_comm a, smul_smul, mul_comm t]

end Tensor

section ReducedPower

variable {k G : Type*} [Field k] [LieRing G] [LieAlgebra k G] {p : ℕ} [CharP k p] [NeZero p]
  (P : restrictedPowerValue k p G) (χ : G →ₗ[k] k)

/-- The defining power identity in the reduced quotient on a Lie generator. -/
theorem generator_pow (x : G) :
    generator P χ x ^ p =
      generator P χ (P.val x) + algebraMap k (reducedEnvelopingValue P χ) (χ x ^ p) := by
  have h := (ReducedEnveloping.quotientMap_spec P χ).2.2 x
  change quotientMapValue P χ (pCenterElementValue P x) = _ at h
  rw [pCenterElementValue, map_sub, map_pow, sub_eq_iff_eq_add] at h
  exact h.trans (add_comm _ _)

end ReducedPower

open scoped BigOperators

private theorem quotient_lift_mk {k A C : Type*} [Field k] [Ring A] [Ring C]
    [Algebra k A] [Algebra k C] (I : Ideal A) [I.IsTwoSided]
    (g : A →ₐ[k] C) (hg : ∀ a ∈ I, g a = 0) (a : A) :
    Ideal.Quotient.liftₐ I g hg (Ideal.Quotient.mkₐ k I a) = g a :=
  DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I g hg) a

private theorem kills_span {k A C : Type*} [Field k] [Ring A] [Ring C]
    [Algebra k A] [Algebra k C] (g : A →ₐ[k] C) {s : Set A}
    (h : ∀ a ∈ s, g a = 0) :
    ∀ a ∈ (TwoSidedIdeal.span s).asIdeal, g a = 0 := by
  intro a ha
  have hle : TwoSidedIdeal.span s ≤ TwoSidedIdeal.ker g :=
    TwoSidedIdeal.span_le.mpr fun x hx => (TwoSidedIdeal.mem_ker g).mpr (h x hx)
  exact (TwoSidedIdeal.mem_ker g).mp (hle (TwoSidedIdeal.mem_asIdeal.mp ha))

private theorem upper_pow_zero {k : Type*} [Field k] (x : Matrix (Fin 2) (Fin 2) k)
    (hx : x 1 0 = 0) (n : ℕ) : (x ^ n) 1 0 = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, hx, ih]

section InducedBasis

variable {k A B : Type*} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (j : B →ₐ[k] A) (θ : B →ₐ[k] k)

private theorem induced_basis {ι : Type*} [Fintype ι] {x : ι → A}
    (h : RightBasis j x) :
    ∃ v : Module.Basis ι k (Induced j θ), ∀ i, v i = x i • highest j θ := by
  classical
  obtain ⟨d, hd, hr⟩ := h
  let S := balance j θ
  let T : A →ₗ[k] (ι → k) :=
    (LinearMap.pi fun i => θ.toLinearMap.comp (LinearMap.proj i)).comp d.symm.toLinearMap
  have hT (a : A) (b : B) : T (a * j b) = θ b • T a := by
    have hcoord : d.symm (a * j b) = fun i => d.symm a i * b := by
      apply d.injective
      rw [d.apply_symm_apply, hr, d.apply_symm_apply]
    funext i
    change θ (d.symm (a * j b) i) = θ b * θ (d.symm a i)
    rw [hcoord, map_mul, mul_comm]
  have kill (a : A) (ha : a ∈ S.restrictScalars k) : a ∈ LinearMap.ker T := by
    change a ∈ S at ha
    have vanish (z : A) (hz : z ∈ S) : ∀ t : A, T (t * z) = 0 := by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨b, rfl⟩ := hz
        intro t
        rw [mul_sub, map_sub, hT, ← Algebra.commutes (θ b) t,
          ← Algebra.smul_def, map_smul, sub_self]
      | zero => intro t; simp
      | add a b _ _ ha hb =>
        intro t
        rw [mul_add, map_add, ha, hb, add_zero]
      | smul c a _ ha =>
        intro t
        change T (t * (c * a)) = 0
        rw [← mul_assoc, ha]
    exact LinearMap.mem_ker.mpr (by simpa using vanish a ha 1)
  let ev : Induced j θ →ₗ[k] (ι → k) :=
    ((S.restrictScalars k).liftQ T kill).comp
      (Submodule.Quotient.restrictScalarsEquiv k S).symm.toLinearMap
  have hev (a : A) : ev (S.mkQ a) = T a := rfl
  have hcoord (i : ι) : d.symm (x i) = Pi.single i 1 := by
    apply d.injective
    rw [d.apply_symm_apply, hd, Finset.sum_eq_single i]
    · simp
    · intro z _ hz
      simp [Pi.single_eq_of_ne hz]
    · simp
  have hunit (i : ι) : ev (x i • highest j θ) = Pi.single i 1 := by
    rw [← mkQ_eq_smul_highest, hev]
    funext z
    change θ (d.symm (x i) z) = (Pi.single i 1 : ι → k) z
    rw [hcoord]
    by_cases hz : z = i
    · subst z; simp
    · simp [Pi.single_eq_of_ne hz]
  have expand (a : A) : S.mkQ a = ∑ i, T a i • (x i • highest j θ) := by
    have h := hd (d.symm a)
    rw [d.apply_symm_apply] at h
    conv_lhs => rw [h, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change S.mkQ (x i * j (d.symm a i)) = θ (d.symm a i) • (x i • highest j θ)
    rw [mkQ_eq_smul_highest, mul_smul, smul_highest, smul_comm]
  have hinj : Function.Injective ev := by
    apply (injective_iff_map_eq_zero ev).mpr
    intro z hz
    obtain ⟨a, rfl⟩ := S.mkQ_surjective z
    rw [hev] at hz
    rw [expand, hz]
    simp
  have hsurj : Function.Surjective ev := by
    intro c
    refine ⟨S.mkQ (d fun i => algebraMap k B (c i)), ?_⟩
    rw [hev]
    funext i
    change θ (d.symm (d fun j => algebraMap k B (c j)) i) = c i
    rw [d.symm_apply_apply, θ.commutes]
    rfl
  let e := LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩
  refine ⟨(Pi.basisFun k ι).map e.symm, fun i => hinj ?_⟩
  rw [hunit, Module.Basis.map_apply]
  change e (e.symm ((Pi.basisFun k ι) i)) = _
  rw [e.apply_symm_apply, Pi.basisFun_apply]

private theorem induced_map {V : Type*} [AddCommGroup V] [Module A V] (v : V)
    (hv : ∀ b : B, j b • v = algebraMap k A (θ b) • v) :
    (∃! f : Induced j θ →ₗ[A] V, f (highest j θ) = v) ∧
    (Submodule.span A {v} = ⊤ →
      ∃ f : Induced j θ →ₗ[A] V, f (highest j θ) = v ∧ Function.Surjective f) := by
  let L : A →ₗ[A] V := LinearMap.toSpanSingleton A V v
  have hk : balance j θ ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (j b - algebraMap k A (θ b)) • v = 0
    rw [sub_smul, hv, sub_self]
  let f := (balance j θ).liftQ L hk
  have hf : f (highest j θ) = v := by
    change (1 : A) • v = v
    rw [one_smul]
  refine ⟨⟨f, hf, ?_⟩, fun hspan => ⟨f, hf, ?_⟩⟩
  · intro g hg
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ := (balance j θ).mkQ_surjective z
    rw [mkQ_eq_smul_highest, map_smul, map_smul, hf, hg]
  · intro z
    have hz : z ∈ Submodule.span A {v} := by simp [hspan]
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨a • highest j θ, (map_smul f _ _).trans (congrArg (a • ·) hf)⟩

end InducedBasis

section SlTwo
attribute [local instance 100] LieRing.ofAssociativeRing

variable {k : Type u} [Field k] {p : ℕ} [CharP k p] [NeZero p]
  {P : restrictedPowerValue k p (Model k)} {Q : restrictedPowerValue k p (Borel k)}
  (χ : Model k →ₗ[k] k)

private theorem borel_closed (hP : MatrixPower P) (x : Borel k) :
    P.val (x : Model k) ∈ borelValue k := by
  change (P.val (x : Model k)).val 1 0 = 0
  rw [hP x]
  exact upper_pow_zero x.val.val x.property p

private theorem matrix_basis_powers (hP : MatrixPower P) :
    P.val (E k) = 0 ∧ P.val (F k) = 0 ∧ P.val (H k) = H k := by
  have heq : P = RestrictedMatrices.restrictedPower (p := p) 2 := by
    apply Subtype.ext
    funext x
    apply Subtype.ext
    rw [hP x, RestrictedMatrices.coe_restrictedPower_apply]
  rw [heq]
  exact RestrictedSlTwo.basis_powers

private theorem reduced_borel_map (hQ : InheritedPower P Q) :
    ∃ j : BorelAlgebra Q χ →ₐ[k] Ambient P χ, CanonicalInclusion P Q χ j := by
  let ρ : Borel k →ₗ⁅k⁆ Ambient P χ :=
    (quotientMapValue P χ).toLieHom.comp
      ((UniversalEnvelopingAlgebra.ι k).comp (borelValue k).incl)
  let g := UniversalEnvelopingAlgebra.lift k ρ
  have hg (x : Borel k) : g (inclusion k (Borel k) x) = generator P χ (x : Model k) :=
    UniversalEnvelopingAlgebra.lift_ι_apply k ρ x
  have kill (a : U k (Borel k)) (ha : a ∈ reducedRelationsValue Q (restrictCharacter χ)) :
      g a = 0 := by
    apply kills_span g _ a ha
    rintro _ ⟨x, rfl⟩
    change g (pCenterElementValue Q x - algebraMap k _ (restrictCharacter χ x ^ p)) = 0
    rw [pCenterElementValue, map_sub, map_sub, map_pow, hg, hg, g.commutes, hQ x,
      generator_pow P χ, add_sub_cancel_left]
    exact sub_self _
  refine ⟨Ideal.Quotient.liftₐ _ g kill, ?_⟩
  intro x
  exact (quotient_lift_mk _ g kill _).trans (hg x)

private def borelWeight (weight : k) : Borel k →ₗ⁅k⁆ k where
  toFun x := weight * x.val.val 0 0
  map_add' x y := by
    change weight * (x.val.val 0 0 + y.val.val 0 0) = _
    exact mul_add _ _ _
  map_smul' c x := by
    change weight * (c * x.val.val 0 0) = c * (weight * x.val.val 0 0)
    rw [mul_left_comm]
  map_lie' {x y} := by
    have hx : x.val.val 1 0 = 0 := x.property
    have hy : y.val.val 1 0 = 0 := y.property
    change weight * ((x.val.val * y.val.val) 0 0 - (y.val.val * x.val.val) 0 0) =
      weight * x.val.val 0 0 * (weight * y.val.val 0 0) -
        weight * y.val.val 0 0 * (weight * x.val.val 0 0)
    simp [Matrix.mul_apply, Fin.sum_univ_two, hx, hy, mul_comm]

private theorem line_character (hP : MatrixPower P) (hQ : InheritedPower P Q)
    (hχ : χ (E k) = 0) (weight : k) (hw : weight ^ p - weight = χ (H k) ^ p) :
    ∃ θ : BorelAlgebra Q χ →ₐ[k] k, LineCharacter Q χ weight θ := by
  obtain ⟨b, bh, be⟩ := borelBasis k
  obtain ⟨pe, _, ph⟩ := matrix_basis_powers hP
  have pqh : Q.val (borelH k) = borelH k := Subtype.ext ((hQ _).trans ph)
  have pqe : Q.val (borelE k) = 0 := Subtype.ext ((hQ _).trans pe)
  let g := UniversalEnvelopingAlgebra.lift k (borelWeight weight)
  have hg (x : Borel k) : g (inclusion k (Borel k) x) = borelWeight weight x :=
    UniversalEnvelopingAlgebra.lift_ι_apply k (borelWeight weight) x
  have hh : borelWeight weight (borelH k) = weight := by
    change weight * (H k).val 0 0 = weight
    rw [show (H k).val = _ from LieAlgebrasAndRepresentations.sl2_h_val k]
    simp
  have he : borelWeight weight (borelE k) = 0 := by
    change weight * (E k).val 0 0 = 0
    rw [show (E k).val = _ from LieAlgebrasAndRepresentations.sl2_e_val k]
    simp
  have kill (a : U k (Borel k)) (ha : a ∈ reducedRelationsValue Q (restrictCharacter χ)) :
      g a = 0 := by
    rw [show reducedRelationsValue Q (restrictCharacter χ) = _ from
      ReducedPbw.reducedRelations_eq_span_basis Q b (restrictCharacter χ)] at ha
    apply kills_span g _ a ha
    rintro _ ⟨i, rfl⟩
    change g (pCenterElementValue Q (b i) -
      algebraMap k _ (restrictCharacter χ (b i) ^ p)) = 0
    rw [pCenterElementValue, map_sub, map_sub, map_pow, hg, hg, g.commutes]
    change borelWeight weight (b i) ^ p - borelWeight weight (Q.val (b i)) -
      restrictCharacter χ (b i) ^ p = 0
    fin_cases i
    · change borelWeight weight (b 0) ^ p - borelWeight weight (Q.val (b 0)) - restrictCharacter χ (b 0) ^ p = 0
      rw [bh, pqh, hh]
      exact sub_eq_zero.mpr hw
    · change borelWeight weight (b 1) ^ p - borelWeight weight (Q.val (b 1)) - restrictCharacter χ (b 1) ^ p = 0
      rw [be, pqe, he, map_zero]
      have hc : restrictCharacter χ (borelE k) = 0 := hχ
      simp [hc, NeZero.ne p]
  exact ⟨Ideal.Quotient.liftₐ _ g kill,
    ((quotient_lift_mk _ g kill _).trans (hg _)).trans hh,
    ((quotient_lift_mk _ g kill _).trans (hg _)).trans he⟩

private theorem borel_pbw :
    ∃ b : Module.Basis (Fin 2 → Fin p) k (BorelAlgebra Q χ),
      ∀ r, b r = generator Q (restrictCharacter χ) (borelH k) ^ (r 0).val *
        generator Q (restrictCharacter χ) (borelE k) ^ (r 1).val := by
  obtain ⟨b, bh, be⟩ := borelBasis k
  obtain ⟨d, hd⟩ := ReducedPbw.reducedBasis Q b (restrictCharacter χ)
  refine ⟨d, fun r => ?_⟩
  rw [hd]
  change quotientMapValue Q (restrictCharacter χ) (restrictedMonomialValue b r) = _
  simp only [restrictedMonomialValue, show List.finRange 2 = [0, 1] by decide,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, bh, be,
    map_mul, map_pow, generator]

private theorem ambient_pbw :
    ∃ b : Module.Basis (Fin 3 → Fin p) k (Ambient P χ),
      ∀ r, b r = generator P χ (F k) ^ (r 0).val *
        (generator P χ (H k) ^ (r 1).val * generator P χ (E k) ^ (r 2).val) := by
  obtain ⟨b, be, bf, bh⟩ := RestrictedSlTwo.basis k
  let perm : Fin 3 ≃ Fin 3 := (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  let b' := b.reindex perm
  have b0 : b' 0 = F k := by
    rw [Module.Basis.reindex_apply, show perm.symm 0 = 1 by decide, bf]
  have b1 : b' 1 = H k := by
    rw [Module.Basis.reindex_apply, show perm.symm 1 = 2 by decide, bh]
  have b2 : b' 2 = E k := by
    rw [Module.Basis.reindex_apply, show perm.symm 2 = 0 by decide, be]
  obtain ⟨d, hd⟩ := ReducedPbw.reducedBasis P b' χ
  refine ⟨d, fun r => ?_⟩
  rw [hd]
  change quotientMapValue P χ (restrictedMonomialValue b' r) = _
  simp only [restrictedMonomialValue, show List.finRange 3 = [0, 1, 2] by decide,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, b0, b1, b2,
    map_mul, map_pow, generator]

private theorem reduced_right_basis (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ)
    (hj : CanonicalInclusion P Q χ j) :
    RightBasis j (fun i : Fin p => generator P χ (F k) ^ i.val) := by
  classical
  obtain ⟨b, hb⟩ := borel_pbw (Q := Q) χ
  obtain ⟨a, ha⟩ := ambient_pbw (P := P) χ
  let I := Fin p
  let J := Fin 2 → Fin p
  let K := Fin 3 → Fin p
  let e : I × J ≃ K :=
    { toFun := fun ij => Fin.cons ij.1 ij.2
      invFun := fun r => (r 0, Fin.tail r)
      left_inv := by intro ij; simp
      right_inv := by intro r; exact Fin.cons_self_tail r }
  let x (i : I) := generator P χ (F k) ^ i.val
  have hword (i : I) (r : J) : a (e (i, r)) = x i * j (b r) := by
    rw [ha, hb, map_mul, map_pow, map_pow, hj, hj]
    have h0 : e (i, r) 0 = i := by
      change (Fin.cons (α := fun _ : Fin 3 => Fin p) i r) 0 = i
      exact Fin.cons_zero _ _
    have h1 : e (i, r) 1 = r 0 :=
      Fin.cons_succ (α := fun _ : Fin 3 => Fin p) i r (0 : Fin 2)
    have h2 : e (i, r) 2 = r 1 :=
      Fin.cons_succ (α := fun _ : Fin 3 => Fin p) i r (1 : Fin 2)
    rw [h0, h1, h2]
    rfl
  let d : (I → BorelAlgebra Q χ) ≃ₗ[k] Ambient P χ :=
    (LinearEquiv.piCongrRight fun _ : I => b.equivFun) ≪≫ₗ
      (LinearEquiv.curry k k I J).symm ≪≫ₗ
      (LinearEquiv.piCongrLeft' k (fun _ : I × J => k) e) ≪≫ₗ a.equivFun.symm
  have hd (c : I → BorelAlgebra Q χ) : d c = ∑ i, x i * j (c i) := by
    change a.equivFun.symm (fun r => b.equivFun (c (e.symm r).1) (e.symm r).2) = _
    rw [a.equivFun_symm_apply, ← Equiv.sum_comp e, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Equiv.symm_apply_apply, hword]
    conv_rhs => rw [← b.sum_equivFun (c i), map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [map_smul, mul_smul_comm]
  refine ⟨d, hd, fun c z => ?_⟩
  simp only [hd, map_mul, Finset.sum_mul, mul_assoc]

private theorem right_basis_injective {A B : Type*} [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    {ι : Type*} [Fintype ι] (j : B →ₐ[k] A) {x : ι → A}
    (h : RightBasis j x) (i : ι) (hi : x i = 1) : Function.Injective j := by
  classical
  obtain ⟨d, hd, _⟩ := h
  have hsingle (b : B) : d (Pi.single i b) = j b := by
    rw [hd, Finset.sum_eq_single i]
    · simp [hi]
    · intro r _ hr
      simp [Pi.single_eq_of_ne hr]
    · simp
  intro a b h
  have heq : Pi.single i a = Pi.single i b := d.injective ((hsingle a).trans (h.trans (hsingle b).symm))
  simpa using congrFun heq i

private theorem action_formulas (hP : MatrixPower P)
    (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ) (hj : CanonicalInclusion P Q χ j)
    (θ : BorelAlgebra Q χ →ₐ[k] k) (weight : k) (hθ : LineCharacter Q χ weight θ)
    (hr : RightBasis j (fun i : Fin p => generator P χ (F k) ^ i.val)) :
    BasisAndActions j θ weight := by
  let e := generator P χ (E k)
  let f := generator P χ (F k)
  let h := generator P χ (H k)
  let v₀ := highest j θ
  have hH := smul_highest j θ (generator Q (restrictCharacter χ) (borelH k))
  rw [hj, hθ.1] at hH
  have hE := smul_highest j θ (generator Q (restrictCharacter χ) (borelE k))
  rw [hj, hθ.2, zero_smul] at hE
  have hh : h • v₀ = weight • v₀ := hH
  have he : e • v₀ = 0 := hE
  let ρ : Model k →ₗ⁅k⁆ Ambient P χ :=
    (quotientMapValue P χ).toLieHom.comp (UniversalEnvelopingAlgebra.ι k)
  obtain ⟨_, hHF, hEF⟩ := RestrictedSlTwo.brackets k
  have hf_comm : h * f = f * h + (-2 : k) • f := by
    have hhf : h * f - f * h = (-2 : k) • f := calc
      _ = ρ ⁅H k, F k⁆ := (ρ.map_lie _ _).symm
      _ = _ := by rw [hHF, map_smul]; rfl
    exact (sub_eq_iff_eq_add.mp hhf).trans (add_comm _ _)
  have ef_comm : e * f = f * e + h := by
    have hef : e * f - f * e = h := calc
      _ = ρ ⁅E k, F k⁆ := (ρ.map_lie _ _).symm
      _ = _ := congrArg ρ hEF
    exact (sub_eq_iff_eq_add.mp hef).trans (add_comm _ _)
  let v (i : ℕ) := f ^ i • v₀
  have fv (i : ℕ) : f • v i = v (i + 1) := by
    change f • (f ^ i • v₀) = f ^ (i + 1) • v₀
    rw [pow_succ', mul_smul]
  have hv (i : ℕ) : h • v i = (weight - 2 * (i : k)) • v i := by
    induction i with
    | zero => simpa [v] using hh
    | succ i ih =>
      rw [← fv, ← mul_smul, hf_comm, add_smul, mul_smul, smul_assoc, ih,
        smul_comm f, fv, ← add_smul]
      congr 1
      push_cast
      ring
  have ev_step (i : ℕ) : e • v (i + 1) = f • (e • v i) + h • v i := by
    rw [← fv, ← mul_smul, ef_comm, add_smul, mul_smul]
  have ev (i : ℕ) : e • v (i + 1) = (((i : k) + 1) * (weight - (i : k))) • v i := by
    induction i with
    | zero =>
      have he₀ : e • v 0 = 0 := by simpa [v] using he
      rw [ev_step, he₀, smul_zero, zero_add, hv]
      simp
    | succ i ih =>
      rw [ev_step, ih, hv, smul_comm f, fv, ← add_smul]
      congr 1
      push_cast
      ring
  obtain ⟨D, hD⟩ := induced_basis j θ hr
  have hDv (i : Fin p) : D i = v i.val := hD i
  refine ⟨D, hD, ?_, he, ?_, ?_, ?_⟩
  · intro i
    rw [hDv]
    exact hv i.val
  · intro i j' hij
    rw [hDv, hDv, hij]
    change e • v (j'.val + 1) = (((j'.val + 1 : ℕ) : k) *
      (weight - ((j'.val + 1 : ℕ) : k) + 1)) • v j'.val
    rw [ev]
    congr 1
    push_cast
    ring
  · intro i j' hij
    rw [hDv, hDv, hij]
    exact fv i.val
  · intro i hip
    have hpF := generator_pow P χ (F k)
    rw [(matrix_basis_powers hP).2.1] at hpF
    have hzero : generator P χ (0 : Model k) = 0 := map_zero ρ
    rw [hzero, zero_add] at hpF
    rw [hDv]
    change f • v i.val = _
    rw [fv, hip]
    change generator P χ (F k) ^ p • v₀ = _
    rw [hpF, IsScalarTower.algebraMap_smul]

private theorem induction_property
    (j : BorelAlgebra Q χ →ₐ[k] Ambient P χ) (hj : CanonicalInclusion P Q χ j)
    (θ : BorelAlgebra Q χ →ₐ[k] k) (weight : k) (hθ : LineCharacter Q χ weight θ) :
    InductionProperty.{u,w} j θ weight := by
  intro V _ _ v
  let A := Ambient P χ
  let _ : Module k V := Module.compHom V (algebraMap k A)
  let _ : IsScalarTower k A V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : SMulCommClass A k V := ⟨fun a c z => by
    change a • (algebraMap k A c • z) = algebraMap k A c • (a • z)
    rw [← mul_smul, ← mul_smul, Algebra.commutes c a]⟩
  intro hh he
  have eigen_pow (a : A) (c : k) (hc : a • v = c • v) (n : ℕ) :
      a ^ n • v = c ^ n • v := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, ih, smul_comm a, hc, smul_smul, pow_succ]
  let h := generator Q (restrictCharacter χ) (borelH k)
  let e := generator Q (restrictCharacter χ) (borelE k)
  have hjh : j h = generator P χ (H k) := hj (borelH k)
  have hje : j e = generator P χ (E k) := hj (borelE k)
  have hhw : j h • v = θ h • v := by rw [hjh, hθ.1]; exact hh
  have hew : j e • v = θ e • v := by rw [hje, hθ.2, zero_smul]; exact he
  obtain ⟨D, hD⟩ := borel_pbw (Q := Q) χ
  let L : BorelAlgebra Q χ →ₗ[k] V :=
    ((LinearMap.toSpanSingleton A V v).restrictScalars k).comp j.toLinearMap
  let R : BorelAlgebra Q χ →ₗ[k] V :=
    (LinearMap.toSpanSingleton k V v).comp θ.toLinearMap
  have hlr : L = R := by
    apply D.ext
    intro r
    change j (D r) • v = θ (D r) • v
    rw [hD, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow]
    change (j h ^ (r 0).val * j e ^ (r 1).val) • v =
      (θ h ^ (r 0).val * θ e ^ (r 1).val) • v
    rw [mul_smul, eigen_pow (j e) (θ e) hew, smul_comm (j h ^ (r 0).val),
      eigen_pow (j h) (θ h) hhw, smul_smul, mul_comm]
  exact induced_map j θ v (fun b => DFunLike.congr_fun hlr b)

end SlTwo

/-- Induction from the reduced Borel character and the ordered baby Verma basis. -/
theorem babyVermaInduction : babyVermaInductionType.{u,w} := by
  intro k _ _ p _ hp
  let _ : NeZero p := ⟨by omega⟩
  intro P hP χ hχ
  let Q := RestrictedLie.restrict P (borelValue k) (borel_closed hP)
  have hQ : InheritedPower P Q := fun _ => rfl
  obtain ⟨j, hj⟩ := reduced_borel_map χ hQ
  have hr := reduced_right_basis χ j hj
  have hjInj : Function.Injective j := right_basis_injective j hr (0 : Fin p) (pow_zero _)
  refine ⟨Q, j, hQ, hj, hjInj, hr, fun weight hw => ?_⟩
  obtain ⟨θ, hθ⟩ := line_character χ hP hQ hχ weight hw
  exact ⟨θ, hθ, action_formulas χ hP j hj θ weight hθ hr, induction_property χ j hj θ weight hθ⟩

end LieNotes.SuperRestricted.BabyVermaInduction
