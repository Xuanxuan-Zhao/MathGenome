import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.HomTensorExactness
import MathGenome.Internal.AlgebraCore.P103.Ch01.ModuleExactness
import MathGenome.Internal.AlgebraCore.P103.Ch01.BalancedTensor
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace P103.HomTensorExactness

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

 theorem homCovariant : Specification.HomCovariant := by
  intro R L M N P _ _ _ _ _ _ _ _ _ i p hi he
  have hker : ∀ h : P →ₗ[R] M, p.comp h = 0 → ∃ k : P →ₗ[R] L, i.comp k = h := by
    intro h hh
    classical
    have hex : ∀ x : P, ∃ l, i l = h x := fun x =>
      (he (h x)).mp (DFunLike.congr_fun hh x)
    choose k hk using hex
    let k' : P →ₗ[R] L := {
      toFun := k
      map_add' := fun x y => hi (by simp only [hk, map_add])
      map_smul' := fun r x => hi (by simp only [hk, map_smul, RingHom.id_apply]) }
    exact ⟨k', LinearMap.ext hk⟩
  constructor
  · intro h k hh
    ext x
    exact hi (DFunLike.congr_fun hh x)
  · intro h
    change p.comp h = 0 ↔ ∃ k, i.comp k = h
    refine ⟨hker h, ?_⟩
    rintro ⟨k, rfl⟩
    ext x
    exact he.apply_apply_eq_zero (k x)

 theorem homContravariant : Specification.HomContravariant := by
  intro R L M N Q _ _ _ _ _ _ _ _ _ i p he hp
  constructor
  · intro h k hh
    ext n
    obtain ⟨m, rfl⟩ := hp n
    exact DFunLike.congr_fun hh m
  · intro h
    change h.comp i = 0 ↔ ∃ k : N →ₗ[R] Q, k.comp p = h
    constructor
    · intro hh
      have hk : LinearMap.ker p ≤ LinearMap.ker h := by
        intro m hm
        obtain ⟨l, rfl⟩ := (he m).mp hm
        exact DFunLike.congr_fun hh l
      refine ⟨p.liftOfSurjective hp ⟨h, hk⟩, ?_⟩
      ext m
      exact LinearMap.equivOfSurjective_apply hp hk
    · rintro ⟨k, rfl⟩
      ext l
      change k (p (i l)) = 0
      rw [he.apply_apply_eq_zero, map_zero]

 theorem homFactorEquivariance : Specification.HomFactorEquivariance := by
  intro R S L M N P _ _ _ _ _ _ _ _ _ _ _ _ _ _ i p hi hp
  constructor
  · intro h k hinj hk hh s x
    apply hinj
    calc
      i (k (s • x)) = h (s • x) := DFunLike.congr_fun hk _
      _ = s • h x := hh s x
      _ = s • i (k x) := congrArg (s • ·) (DFunLike.congr_fun hk x).symm
      _ = i (s • k x) := (hi s _).symm
  · intro h k hsur hk hh s x
    obtain ⟨m, rfl⟩ := hsur x
    rw [← hp]
    calc
      k (p (s • m)) = h (s • m) := DFunLike.congr_fun hk _
      _ = s • h m := hh s m
      _ = s • k (p m) := congrArg (s • ·) (DFunLike.congr_fun hk m).symm

 theorem homNaturality : Specification.HomNaturality := by
  unfold Specification.HomNaturality
  intros
  exact ⟨rfl, rfl⟩

@[simp] theorem double_apply (z : ℤ) : double z = 2 * z := by
  simp [double]

@[simp] theorem modTwo_apply (z : ℤ) : modTwo z = (z : ZMod 2) := rfl

 theorem integerSequence : Specification.IntegerSequence := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    simp only [double_apply] at h
    omega
  · intro z
    change (z : ZMod 2) = 0 ↔ ∃ k : ℤ, double k = z
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [double_apply] using hk.symm⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa [double_apply] using hk.symm⟩
  · exact ZMod.intCast_surjective

 theorem homNoLift : Specification.HomNoLift := by
  rintro ⟨h, hh⟩
  have hz : (2 : ℤ) • (1 : ZMod 2) = 0 := by decide
  have hzero : h 1 = 0 := by
    have := congrArg h hz
    rw [map_smul, map_zero] at this
    change 2 * h 1 = 0 at this
    omega
  have := DFunLike.congr_fun hh (1 : ZMod 2)
  change modTwo (h 1) = 1 at this
  rw [hzero, map_zero] at this
  exact zero_ne_one this

 theorem homRestriction : Specification.HomRestriction := by
  constructor
  · intro h
    apply LinearMap.ext
    intro z
    change h (double z) = (2 : ℤ) • h z
    rw [double_apply]
    exact h.map_smul (2 : ℤ) z
  · intro hs
    obtain ⟨h, hh⟩ := hs (LinearMap.id : ℤ →ₗ[ℤ] ℤ)
    have := DFunLike.congr_fun hh 1
    change h (double 1) = 1 at this
    have h2 : h (double 1) = 2 * h 1 := by
      rw [double_apply]
      exact h.map_smul (2 : ℤ) (1 : ℤ)
    rw [h2] at this
    omega

open P103.BalancedTensor

section FirstTensor
variable {R L A C B : Type*} [Ring R]
variable [AddCommGroup L] [AddCommGroup A] [AddCommGroup C] [AddCommGroup B]
variable [Module Rᵐᵒᵖ L] [Module Rᵐᵒᵖ A] [Module Rᵐᵒᵖ C] [Module R B]

theorem tensor_first_rightExact
    (i : L →ₗ[Rᵐᵒᵖ] A) (p : A →ₗ[Rᵐᵒᵖ] C)
    (hi : Function.Exact i p) (hp : Function.Surjective p)
    (F : Tensor R L B →+ Tensor R A B)
    (hF : ∀ l b, F (tmul R l b) = tmul R (i l) b)
    (G : Tensor R A B →+ Tensor R C B)
    (hG : ∀ a b, G (tmul R a b) = tmul R (p a) b) :
    Function.Exact F G ∧ Function.Surjective G := by
  let J := LinearMap.range F.toIntLinearMap
  let q := J.mkQ
  let H : Pairing R (A := A) (B := B) ((Tensor R A B) ⧸ J) :=
    Pairing.ofFun (fun a b => q (tmul R a b))
      (by intros; simp [add_tmul]) (by intros; simp [tmul_add])
      (by intros; rw [balance])
  have hkill : LinearMap.ker p.toAddMonoidHom.toIntLinearMap ≤
      LinearMap.ker H.toBiadditive.toIntLinearMap := by
    intro a ha
    change H.toBiadditive a = 0
    obtain ⟨l, rfl⟩ := (hi a).mp ha
    apply AddMonoidHom.ext
    intro b
    change q (tmul R (i l) b) = 0
    rw [← hF]
    change Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨tmul R l b, rfl⟩
  have hpZ : Function.Surjective p.toAddMonoidHom.toIntLinearMap := hp
  let D : C →+ B →+ ((Tensor R A B) ⧸ J) :=
    ((p.toAddMonoidHom.toIntLinearMap.liftOfSurjective hpZ)
      ⟨H.toBiadditive.toIntLinearMap, hkill⟩).toAddMonoidHom
  have hD (a : A) (b : B) : D (p a) b = q (tmul R a b) := by
    change (((p.toAddMonoidHom.toIntLinearMap.liftOfSurjective hpZ)
      ⟨H.toBiadditive.toIntLinearMap, hkill⟩) (p a)) b = _
    exact congrArg (fun k : B →+ ((Tensor R A B) ⧸ J) => k b)
      (LinearMap.equivOfSurjective_apply hpZ hkill (m := a))
  let K : Tensor R C B →+ ((Tensor R A B) ⧸ J) :=
    lift { toBiadditive := D
           balance := by
             intro r c b
             obtain ⟨a, rfl⟩ := hp c
             rw [← p.map_smul, hD, hD, balance] }
  have hKG (z : Tensor R A B) : K (G z) = q z := by
    induction z using induction_on with
    | h0 => simp
    | ht a b => rw [hG, lift_tmul]; exact hD a b
    | ha z z' hz hz' => simp [hz, hz']
  have hGF (z : Tensor R L B) : G (F z) = 0 := by
    induction z using induction_on with
    | h0 => simp
    | ht l b => rw [hF, hG, hi.apply_apply_eq_zero, zero_tmul]
    | ha z z' hz hz' => simp [hz, hz']
  constructor
  · intro z
    constructor
    · intro hz
      have hzq : q z = 0 := by rw [← hKG, hz, map_zero]
      change Submodule.Quotient.mk z = 0 at hzq
      rw [Submodule.Quotient.mk_eq_zero] at hzq
      exact hzq
    · rintro ⟨w, rfl⟩
      exact hGF w
  · intro z
    induction z using induction_on with
    | h0 => exact ⟨0, map_zero G⟩
    | ht c b =>
      obtain ⟨a, rfl⟩ := hp c
      exact ⟨tmul R a b, hG a b⟩
    | ha z z' hz hz' =>
      obtain ⟨w, rfl⟩ := hz
      obtain ⟨w', rfl⟩ := hz'
      exact ⟨w+w', map_add G w w'⟩

theorem tensor_first_quotient
    (U : Submodule Rᵐᵒᵖ A)
    (F : Tensor R U B →+ Tensor R A B)
    (hF : ∀ (u : U) b, F (tmul R u b) = tmul R (u : A) b) :
    ∃ e : Tensor R (A ⧸ U) B ≃+ ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap),
      (∀ a b, e (tmul R (U.mkQ a) b) =
        (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) ∧
      (∀ a b, e.symm ((LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) =
        tmul R (U.mkQ a) b) := by
  let G : Tensor R A B →+ Tensor R (A ⧸ U) B :=
    P103.BalancedTensor.map U.mkQ LinearMap.id
  have hG (a : A) (b : B) : G (tmul R a b) = tmul R (U.mkQ a) b := by
    simp [G]
  obtain ⟨hex, hsurj⟩ := tensor_first_rightExact U.subtype U.mkQ
    (LinearMap.exact_subtype_mkQ U) U.mkQ_surjective F hF G hG
  have hker : LinearMap.ker G.toIntLinearMap = LinearMap.range F.toIntLinearMap :=
    LinearMap.exact_iff.mp hex
  have hsurjZ : Function.Surjective G.toIntLinearMap := hsurj
  let e : Tensor R (A ⧸ U) B ≃ₗ[ℤ] ((Tensor R A B) ⧸ LinearMap.range F.toIntLinearMap) :=
    (G.toIntLinearMap.quotKerEquivOfSurjective hsurjZ).symm.trans
      (Submodule.quotEquivOfEq _ _ hker)
  have he (a : A) (b : B) : e (tmul R (U.mkQ a) b) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b) := by
    rw [← hG]
    change (Submodule.quotEquivOfEq _ _ hker)
      ((G.toIntLinearMap.quotKerEquivOfSurjective hsurjZ).symm
        (G.toIntLinearMap (tmul R a b))) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨e.toAddEquiv, he, ?_⟩
  intro a b
  change e.symm _ = _
  apply e.injective
  rw [e.apply_symm_apply]
  exact (he a b).symm

end FirstTensor
theorem satisfiesTensorFirstRightExact : Specification.TensorFirstRightExact := by
  intro R L A C B _ _ _ _ _ _ _ _ _ i p hi hp F hF G hG
  exact tensor_first_rightExact i p hi hp F hF G hG

theorem satisfiesTensorFirstQuotient : Specification.TensorFirstQuotient := by
  intro R A B _ _ _ _ _ U F hF
  exact tensor_first_quotient U F hF


section TensorSecond
variable {R A B B' B'' : Type*} [Ring R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup B'] [AddCommGroup B'']
variable [Module Rᵐᵒᵖ A] [Module R B] [Module R B'] [Module R B'']

theorem tensorSecond_surjective (g : B →ₗ[R] B') (hg : Function.Surjective g)
    (G : Tensor R A B →+ Tensor R A B')
    (hG : ∀ a b, G (tmul R a b) = tmul R a (g b)) :
    Function.Surjective G := by
  intro z
  induction z using induction_on with
  | h0 => exact ⟨0, G.map_zero⟩
  | ht a b =>
    obtain ⟨b, rfl⟩ := hg b
    exact ⟨tmul R a b, hG a b⟩
  | ha z w hz hw =>
    obtain ⟨x, rfl⟩ := hz
    obtain ⟨y, rfl⟩ := hw
    exact ⟨x+y, G.map_add x y⟩

theorem tensorSecond_exact (f : B →ₗ[R] B') (g : B' →ₗ[R] B'')
    (hfg : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g)
    (F : Tensor R A B →+ Tensor R A B')
    (G : Tensor R A B' →+ Tensor R A B'')
    (hF : ∀ a b, F (tmul R a b) = tmul R a (f b))
    (hG : ∀ a b, G (tmul R a b) = tmul R a (g b)) :
    F.range = G.ker := by
  classical
  let q := QuotientAddGroup.mk' F.range
  have hzero (a : A) (b : B) : q (tmul R a (f b)) = 0 := by
    change QuotientAddGroup.mk' F.range _ = 0
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨tmul R a b, hF a b⟩
  have hdesc (a : A) {b c : B'} (hbc : g b = g c) :
      q (tmul R a b) = q (tmul R a c) := by
    have hker : b - c ∈ LinearMap.ker g := by simpa using sub_eq_zero.mpr hbc
    rw [← hfg] at hker
    obtain ⟨d, hd⟩ := hker
    have hh := hzero a d
    rw [hd] at hh
    change q (pairing.toBiadditive a (b-c)) = 0 at hh
    rw [map_sub, map_sub, sub_eq_zero] at hh
    exact hh
  let s : B'' → B' := Function.surjInv hg
  have hs (b : B'') : g (s b) = b := Function.surjInv_eq hg b
  let p : Pairing R (A := A) (B := B'') (Tensor R A B' ⧸ F.range) :=
    Pairing.ofFun (fun a b => q (tmul R a (s b)))
      (by intros; simp [add_tmul])
      (by
        intro a b c
        calc
          q (tmul R a (s (b+c))) = q (tmul R a (s b + s c)) :=
            hdesc a (by simp [hs])
          _ = q (tmul R a (s b)) + q (tmul R a (s c)) := by simp [tmul_add])
      (by
        intro r a b
        calc
          q (tmul R (MulOpposite.op r • a) (s b)) = q (tmul R a (r • s b)) :=
            congrArg q (balance r a (s b))
          _ = q (tmul R a (s (r • b))) := hdesc a (by simp [hs]))
  let H := lift p
  have hHG : H.comp G = q := by
    apply hom_ext
    intro a b
    change H (G (tmul R a b)) = q (tmul R a b)
    rw [hG]
    change q (tmul R a (s (g b))) = q (tmul R a b)
    exact hdesc a (hs (g b))
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change G (F x) = 0
    have hGF : G.comp F = 0 := by
      apply hom_ext
      intro a b
      change G (F (tmul R a b)) = 0
      rw [hF, hG]
      have hfker : g (f b) = 0 := by
        have hm : f b ∈ LinearMap.range f := ⟨b, rfl⟩
        rw [hfg] at hm
        exact hm
      simp [hfker]
    exact DFunLike.congr_fun hGF x
  · intro x hx
    apply (QuotientAddGroup.eq_zero_iff x).mp
    change q x = 0
    rw [← hHG]
    change H (G x) = 0
    rw [show G x = 0 from hx, H.map_zero]

theorem tensorSecond_rightExact (f : B →ₗ[R] B') (g : B' →ₗ[R] B'')
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (F : Tensor R A B →+ Tensor R A B')
    (G : Tensor R A B' →+ Tensor R A B'')
    (hF : ∀ a b, F (tmul R a b) = tmul R a (f b))
    (hG : ∀ a b, G (tmul R a b) = tmul R a (g b)) :
    Function.Exact F G ∧ Function.Surjective G := by
  have hex := tensorSecond_exact f g (LinearMap.exact_iff.mp hfg).symm hg F G hF hG
  refine ⟨?_, tensorSecond_surjective g hg G hG⟩
  intro z
  change z ∈ G.ker ↔ z ∈ F.range
  rw [hex]

theorem tensorSecond_quotient (V : Submodule R B)
    (F : Tensor R A V →+ Tensor R A B)
    (hF : ∀ a v, F (tmul R a v) = tmul R a (v : B)) :
    ∃ e : Tensor R A (B ⧸ V) ≃+
        (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap),
      (∀ a b, e (tmul R a (V.mkQ b)) =
        (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) ∧
      (∀ a b, e.symm ((LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) =
        tmul R a (V.mkQ b)) := by
  let G : Tensor R A B →+ Tensor R A (B ⧸ V) := map LinearMap.id V.mkQ
  have hG : ∀ a b, G (tmul R a b) = tmul R a (V.mkQ b) := by intros; rfl
  have he : Function.Exact V.subtype V.mkQ := by
    apply LinearMap.exact_iff.mpr
    simp
  have hex := tensorSecond_rightExact V.subtype V.mkQ he V.mkQ_surjective F G hF hG
  have hker : LinearMap.ker G.toIntLinearMap = LinearMap.range F.toIntLinearMap :=
    LinearMap.exact_iff.mp hex.1
  let E : (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap) ≃ₗ[ℤ]
      Tensor R A (B ⧸ V) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      (G.toIntLinearMap.quotKerEquivOfSurjective hex.2)
  have hE (z : Tensor R A B) :
      E ((LinearMap.range F.toIntLinearMap).mkQ z) = G z := by
    change (G.toIntLinearMap.quotKerEquivOfSurjective hex.2) (Submodule.Quotient.mk z) = G z
    rfl
  refine ⟨E.symm.toAddEquiv, ?_, ?_⟩
  · intro a b
    apply E.injective
    change E (E.symm _) = _
    rw [E.apply_symm_apply, hE, hG]
  · intro a b
    exact (hE (tmul R a b)).trans (hG a b)

end TensorSecond

theorem satisfiesTensorRightExactSecond : Specification.TensorRightExactSecond := by
  intro R A B B' B'' _ _ _ _ _ _ _ _ _ f g hfg hg F G hF hG
  exact tensorSecond_rightExact f g hfg hg F G hF hG

theorem satisfiesTensorQuotientSecond : Specification.TensorQuotientSecond := by
  intro R A B _ _ _ _ _ V F hF
  exact tensorSecond_quotient V F hF

open P103.BalancedTensor

theorem tensorCounterexample : Specification.TensorCounterexample := by
  have hdouble (z : ℤ) (b : ZMod 2) : tmul ℤ (double z) b = 0 := by
    have hz : double z = MulOpposite.op (2 : ℤ) • z := by
      simp [double, mul_comm]
    rw [hz, balance]
    have hb : (2 : ℤ) • b = 0 := by
      rw [← Int.cast_smul_eq_zsmul (R := ZMod 2)]
      have htwo : (2 : ZMod 2) = 0 := by decide
      simp only [Int.cast_ofNat, htwo, zero_smul]
    rw [hb, tmul_zero]
  have hnonzero : tmul ℤ (1 : ℤ) (1 : ZMod 2) ≠ 0 := by
    intro h
    have := congrArg (leftUnit : Tensor ℤ ℤ (ZMod 2) ≃+ ZMod 2) h
    simpa using this
  refine ⟨0, ?_, rfl, hnonzero, ?_⟩
  · intro z b
    simp only [AddMonoidHom.zero_apply, hdouble]
  · intro hinj
    apply hnonzero
    exact hinj (by simp)


 theorem tensorMapFirstEquivariance : Specification.TensorMapFirstEquivariance := by
  intro R S A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g F hF hf hT hT' s z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b => rw [hT, hF, hf, hF, hT']
  | ha z w hz hw => simp [smul_add, hz, hw]

 theorem tensorMapSecondEquivariance : Specification.TensorMapSecondEquivariance := by
  intro R S A B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g F hF hg hT hT' s z
  induction z using P103.BalancedTensor.induction_on with
  | h0 => simp
  | ht a b => rw [hT, hF, hg, hF, hT']
  | ha z w hz hw => simp [smul_add, hz, hw]

 theorem quotientOuterActions : Specification.QuotientOuterActions := by
  intro R S X _ _ _ _ _ U hU
  letI : SMul S (X ⧸ U) := ⟨fun s z => Quotient.map' (s • ·) (by
    intro x y h
    apply U.quotientRel_def.mpr
    have h := U.quotientRel_def.mp h
    rw [← smul_sub]
    exact hU s (x-y) h) z⟩
  have hq : ∀ (s : S) x, U.mkQ (s • x) = s • U.mkQ x := fun _ _ => rfl
  letI : Module S (X ⧸ U) := Function.Surjective.module S U.mkQ.toAddMonoidHom
    (Submodule.mkQ_surjective U) hq
  exact ⟨inferInstance, hq⟩

 theorem imageOuterStability : Specification.ImageOuterStability := by
  intro S X Y _ _ _ _ _ F hF s y hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨s • x, hF s x⟩

 theorem quotientOuterCommutation : Specification.QuotientOuterCommutation := by
  intro R S T X _ _ _ _ _ _ _ _ U _ _ hS hT
  constructor
  intro s t z
  induction z using Submodule.Quotient.induction_on with
  | _ x =>
    change s • (t • U.mkQ x) = t • (s • U.mkQ x)
    rw [← hT, ← hS, ← hS, ← hT, smul_comm s t x]

theorem homOuterActions :
  (∀ (R S M N P : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module S M] [Module S N] [SMulCommClass R S M] [SMulCommClass R S N]
    (f : M →ₗ[R] N) (hf : ∀ (s : S) x, f (s • x) = s • f x),
    ∀ (s : S) (h : P →ₗ[R] M), post f (s • h) = s • post f h) ∧
  (∀ (R S M N P : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module S P] [SMulCommClass S R P] (f : M →ₗ[R] N),
    letI := homSourceModule R S P M
    letI := homSourceModule R S P N
    ∀ (s : Sᵐᵒᵖ) (h : P →ₗ[R] M), post f (s • h) = s • post f h) ∧
  (∀ (R S L M Q : Type*) [Ring R] [Ring S]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup Q]
    [Module R L] [Module R M] [Module R Q]
    [Module S Q] [SMulCommClass R S Q] (f : L →ₗ[R] M),
    ∀ (s : S) (h : M →ₗ[R] Q), pre f (s • h) = s • pre f h) ∧
  (∀ (R S L M Q : Type*) [Ring R] [Ring S]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup Q]
    [Module R L] [Module R M] [Module R Q]
    [Module S L] [Module S M] [SMulCommClass S R L] [SMulCommClass S R M]
    (f : L →ₗ[R] M) (hf : ∀ (s : S) x, f (s • x) = s • f x),
    letI := homSourceModule R S M Q
    letI := homSourceModule R S L Q
    ∀ (s : Sᵐᵒᵖ) (h : M →ₗ[R] Q), pre f (s • h) = s • pre f h) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro R S M N P _ _ _ _ _ _ _ _ _ _ _ _ f hf s h
    ext x
    exact hf s (h x)
  · intros
    rfl
  · intros
    rfl
  · intro R S L M Q _ _ _ _ _ _ _ _ _ _ _ _ f hf s h
    ext x
    change h (s.unop • f x) = h (f (s.unop • x))
    rw [hf]



theorem satisfiesTensorFirstQuotientFirstAction :
    Specification.TensorFirstQuotientFirstAction := by
  intro R S A B _ _ _ _ _ _ U F _ _ _ _ _ hqA hX hY hqX e he
  have hef : ∀ (s : S) z, e (s • z) = s • e z := by
    intro s z
    induction z using induction_on with
    | h0 => rw [smul_zero, e.map_zero, smul_zero]
    | ht a b =>
      obtain ⟨a, rfl⟩ := U.mkQ_surjective a
      rw [hY, ← hqA, he, he, ← hX, hqX]
    | ha z z' hz hz' => rw [smul_add, e.map_add, hz, hz', e.map_add, smul_add]
  refine ⟨hef, ?_⟩
  intro s z
  apply e.injective
  simp only [hef, e.apply_symm_apply]

theorem satisfiesTensorFirstQuotientSecondAction :
    Specification.TensorFirstQuotientSecondAction := by
  intro R S A B _ _ _ _ _ _ U F _ _ _ _ hX hY hqX e he
  have hef : ∀ (s : S) z, e (s • z) = s • e z := by
    intro s z
    induction z using induction_on with
    | h0 => rw [smul_zero, e.map_zero, smul_zero]
    | ht a b =>
      obtain ⟨a, rfl⟩ := U.mkQ_surjective a
      rw [hY, he, he, ← hX, hqX]
    | ha z z' hz hz' => rw [smul_add, e.map_add, hz, hz', e.map_add, smul_add]
  refine ⟨hef, ?_⟩
  intro s z
  apply e.injective
  simp only [hef, e.apply_symm_apply]

section SecondQuotientOuter
variable {R S A B : Type*} [Ring R] [Ring S]
variable [AddCommGroup A] [AddCommGroup B] [Module Rᵐᵒᵖ A] [Module R B]
variable (V : Submodule R B) (F : Tensor R A V →+ Tensor R A B)

theorem tensorSecondQuotient_first_equivariant
    [Module S A] [Module S (Tensor R A B)] [Module S (Tensor R A (B ⧸ V))]
    [Module S (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap)]
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R (s • a) b)
    (hY : ∀ (s : S) (a : A) (b : B ⧸ V), s • tmul R a b = tmul R (s • a) b)
    (hQ : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R A (B ⧸ V) ≃+
      (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R a (V.mkQ b)) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) :
    (∀ (s : S) z, e (s • z) = s • e z) ∧
      (∀ (s : S) z, e.symm (s • z) = s • e.symm z) := by
  have hlin : ∀ (s : S) z, e (s • z) = s • e z := by
    intro s z
    induction z using induction_on with
    | h0 => simp only [smul_zero, e.map_zero]
    | ht a b =>
      obtain ⟨b, rfl⟩ := V.mkQ_surjective b
      rw [hY, he, he, ← hX, hQ]
    | ha z w hz hw => simp only [smul_add, e.map_add, hz, hw]
  refine ⟨hlin, ?_⟩
  intro s z
  apply e.injective
  rw [e.apply_symm_apply, hlin, e.apply_symm_apply]

theorem tensorSecondQuotient_second_equivariant
    [Module S B] [Module S (B ⧸ V)] [Module S (Tensor R A B)]
    [Module S (Tensor R A (B ⧸ V))]
    [Module S (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap)]
    (hB : ∀ (s : S) b, V.mkQ (s • b) = s • V.mkQ b)
    (hX : ∀ (s : S) (a : A) (b : B), s • tmul R a b = tmul R a (s • b))
    (hY : ∀ (s : S) (a : A) (b : B ⧸ V), s • tmul R a b = tmul R a (s • b))
    (hQ : ∀ (s : S) (z : Tensor R A B),
      (LinearMap.range F.toIntLinearMap).mkQ (s • z) =
        s • (LinearMap.range F.toIntLinearMap).mkQ z)
    (e : Tensor R A (B ⧸ V) ≃+
      (Tensor R A B ⧸ LinearMap.range F.toIntLinearMap))
    (he : ∀ a b, e (tmul R a (V.mkQ b)) =
      (LinearMap.range F.toIntLinearMap).mkQ (tmul R a b)) :
    (∀ (s : S) z, e (s • z) = s • e z) ∧
      (∀ (s : S) z, e.symm (s • z) = s • e.symm z) := by
  have hlin : ∀ (s : S) z, e (s • z) = s • e z := by
    intro s z
    induction z using induction_on with
    | h0 => simp only [smul_zero, e.map_zero]
    | ht a b =>
      obtain ⟨b, rfl⟩ := V.mkQ_surjective b
      rw [hY, ← hB, he, he, ← hX, hQ]
    | ha z w hz hw => simp only [smul_add, e.map_add, hz, hw]
  refine ⟨hlin, ?_⟩
  intro s z
  apply e.injective
  rw [e.apply_symm_apply, hlin, e.apply_symm_apply]

end SecondQuotientOuter
theorem satisfiesTensorQuotientSecondFirstEquivariance :
    Specification.TensorQuotientSecondFirstEquivariance := by
  intro R S A B _ _ _ _ _ _ V F _ _ _ _ hX hY hQ e he
  exact tensorSecondQuotient_first_equivariant V F hX hY hQ e he

theorem satisfiesTensorQuotientSecondSecondEquivariance :
    Specification.TensorQuotientSecondSecondEquivariance := by
  intro R S A B _ _ _ _ _ _ V F _ _ _ _ _ hB hX hY hQ e he
  exact tensorSecondQuotient_second_equivariant V F hB hX hY hQ e he


theorem submoduleOuterActions : Specification.SubmoduleOuterActions := by
  intro R S X _ _ _ _ _ _ U hstable
  let V : Submodule S X := {
    carrier := U
    zero_mem' := U.zero_mem
    add_mem' := U.add_mem
    smul_mem' := hstable }
  letI m : Module S U := inferInstanceAs (Module S V)
  refine ⟨m, (fun _ _ => rfl), ?_⟩
  constructor
  intro s r u
  apply Subtype.ext
  change s • (r • (u : X)) = r • (s • (u : X))
  exact smul_comm s r (u : X)
end P103.HomTensorExactness
