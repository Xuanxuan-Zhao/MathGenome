import Specs.LinearAlgebraicGroups.Arithmetic.KummerObstructions
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Arithmetic.CentralCover
import Mathlib.NumberTheory.ClassNumber.FunctionField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.CategoryTheory.Sites.LocalProperties

noncomputable section

open IsDedekindDomain
open scoped nonZeroDivisors NumberField Polynomial RatFunc WithZero

namespace LinearAlgebraicGroups.Arithmetic.Kummer

private theorem finite_of_finite_ker {G H : Type*} [Group G] [Group H] [Finite H]
    (f : G →* H) [Finite f.ker] : Finite G := by
  classical
  have hs : ∀ z : f.range, ∃ y : G, f y = z.1 := fun z => z.2
  choose s hs using hs
  let d (x : G) := f.rangeRestrict x
  let e (x : G) : f.ker := ⟨(s (d x))⁻¹ * x, by simp [d, hs, MonoidHom.mem_ker]⟩
  apply Finite.of_injective (fun x => (d x, e x))
  intro x y h
  have h₁ : d x = d y := congrArg Prod.fst h
  have h₂ := congrArg Subtype.val (congrArg Prod.snd h)
  change (s (d x))⁻¹ * x = (s (d y))⁻¹ * y at h₂
  rw [h₁] at h₂
  exact mul_left_cancel h₂

section Dedekind

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

private abbrev IdealGroup (R K : Type*) [CommRing R] [Field K] [Algebra R K] :=
  (FractionalIdeal R⁰ K)ˣ

private def idealOrder (w : HeightOneSpectrum R) : IdealGroup R K →* Multiplicative ℤ where
  toFun I := Multiplicative.ofAdd (FractionalIdeal.count K w I)
  map_one' := congrArg Multiplicative.ofAdd (FractionalIdeal.count_one K w)
  map_mul' I J := congrArg Multiplicative.ofAdd
    (FractionalIdeal.count_mul K w I.ne_zero J.ne_zero)

private def orderModulo (w : HeightOneSpectrum R) (n : ℕ) : Kˣ →* Multiplicative (ZMod n) :=
  ((Int.castAddHom (ZMod n)).toMultiplicative).comp
    ((idealOrder w).comp (toPrincipalIdeal R K))

private def classOrder (w : HeightOneSpectrum R) (n : ℕ) : Classes K n →* Multiplicative (ZMod n) :=
  QuotientGroup.lift _ (orderModulo w n) (by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow]
    change Multiplicative.ofAdd
      (n • ((FractionalIdeal.count K w ((toPrincipalIdeal R K x).val)) : ZMod n)) = 1
    simp [nsmul_eq_mul])

private theorem classOrder_mk (w : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    classOrder w n (QuotientGroup.mk' _ x) = 1 ↔
      (n : ℤ) ∣ FractionalIdeal.count K w (toPrincipalIdeal R K x).val := by
  change Multiplicative.ofAdd
    ((FractionalIdeal.count K w (toPrincipalIdeal R K x).val : ℤ) : ZMod n) = 1 ↔ _
  exact (Multiplicative.ofAdd.injective.eq_iff (b := 0)).trans (ZMod.intCast_zmod_eq_zero_iff_dvd _ _)

private theorem ideals_ext {I J : IdealGroup R K}
    (h : ∀ w : HeightOneSpectrum R, FractionalIdeal.count K w I = FractionalIdeal.count K w J) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K J.ne_zero]
  exact finprod_congr fun w => by rw [h w]

private theorem ideal_pow_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun I : IdealGroup R K => I ^ n) := by
  intro I J h
  apply ideals_ext
  intro w
  have e := congrArg (fun x : IdealGroup R K => FractionalIdeal.count K w x.val) h
  simp only [Units.val_pow_eq_pow_val, FractionalIdeal.count_pow] at e
  exact mul_left_cancel₀ (by exact_mod_cast hn.ne') e

private theorem exists_ideal_root {n : ℕ} (I : IdealGroup R K)
    (h : ∀ w : HeightOneSpectrum R, (n : ℤ) ∣ FractionalIdeal.count K w I) :
    ∃ J : IdealGroup R K, J ^ n = I := by
  let f (w : HeightOneSpectrum R) := FractionalIdeal.count K w I / (n : ℤ)
  let P := ∏ᶠ w : HeightOneSpectrum R, (w.asIdeal : FractionalIdeal R⁰ K) ^ f w
  have hP : P ≠ 0 := finprod_ne_zero fun w =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)
  refine ⟨Units.mk0 P hP, ideals_ext fun w => ?_⟩
  change FractionalIdeal.count K w (P ^ n) = _
  rw [FractionalIdeal.count_pow, FractionalIdeal.count_finprod]
  · exact Int.mul_ediv_cancel' (h w)
  · filter_upwards [FractionalIdeal.finite_factors I.val] with v hv
    simp [f, hv]

omit [IsDedekindDomain R] in
private theorem principal_eq_one_iff (x : Kˣ) :
    toPrincipalIdeal R K x = 1 ↔ x ∈ (Units.map (algebraMap R K).toMonoidHom).range := by
  constructor
  · intro h
    have hx (y : Kˣ) (hy : toPrincipalIdeal R K y = 1) :
        ∃ r : R, algebraMap R K r = y.val := by
      apply (FractionalIdeal.mem_one_iff R⁰).1
      rw [← show (toPrincipalIdeal R K y).val = 1 from congrArg Units.val hy,
        coe_toPrincipalIdeal]
      exact (FractionalIdeal.mem_spanSingleton R⁰).2 ⟨1, one_smul _ _⟩
    obtain ⟨a, ha⟩ := hx x h
    obtain ⟨b, hb⟩ := hx x⁻¹ (by rw [map_inv, h, inv_one])
    have hab : a * b = 1 := (IsFractionRing.injective R K) (by rw [map_mul, ha, hb, ← Units.val_mul]; simp)
    exact ⟨⟨a, b, hab, by simpa [mul_comm] using hab⟩, Units.ext ha⟩
  · rintro ⟨a, rfl⟩
    apply Units.ext
    rw [coe_toPrincipalIdeal, Units.val_one]
    have h₁ : FractionalIdeal.spanSingleton R⁰ (1 : K) = 1 := map_one _
    apply le_antisymm
    · exact FractionalIdeal.spanSingleton_le_iff_mem.mpr
        ((FractionalIdeal.mem_one_iff R⁰).mpr ⟨a, rfl⟩)
    · rw [← h₁]
      apply FractionalIdeal.spanSingleton_le_iff_mem.mpr
      exact (FractionalIdeal.mem_spanSingleton R⁰).mpr
        ⟨(a⁻¹ : Rˣ), by
          change ((↑a⁻¹ : R) • algebraMap R K (a : R) : K) = 1
          rw [Algebra.smul_def]
          rw [← map_mul, ← Units.val_mul]
          simp⟩

private theorem finite_everywhere [Finite (ClassGroup R)] [Group.FG Rˣ]
    {n : ℕ} (hn : 0 < n) :
    Finite (↥(⨅ w : HeightOneSpectrum R, (classOrder (K := K) w n).ker)) := by
  classical
  let H : Subgroup (Classes K n) := ⨅ w : HeightOneSpectrum R, (classOrder w n).ker
  change Finite H
  let q := QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range
  let c := QuotientGroup.mk' (toPrincipalIdeal R K).range
  let : Finite ((IdealGroup R K) ⧸ (toPrincipalIdeal R K).range) :=
    Finite.of_equiv (ClassGroup R) (ClassGroup.equiv K).toEquiv
  have hroot (a : Kˣ) (ha : q a ∈ H) : ∃ I : IdealGroup R K, I ^ n = toPrincipalIdeal R K a := by
    apply exists_ideal_root
    intro w
    exact (classOrder_mk w n a).1
      (MonoidHom.mem_ker.mp ((Subgroup.mem_iInf.mp ha) w))
  let P := H.comap q
  let r (a : P) := (hroot a.val a.property).choose
  have hr (a : P) : r a ^ n = toPrincipalIdeal R K a.val :=
    (hroot a.val a.property).choose_spec
  let f : P →* (IdealGroup R K) ⧸ (toPrincipalIdeal R K).range :=
    { toFun := fun a => c (r a)
      map_one' := by
        have h : r 1 = 1 := ideal_pow_injective hn (by simp [hr])
        rw [h, map_one]
      map_mul' := fun a b => by
        have h : r (a * b) = r a * r b := ideal_pow_injective hn (by
          change r (a * b) ^ n = (r a * r b) ^ n
          rw [mul_pow, hr, hr, hr, Subgroup.coe_mul, map_mul])
        rw [h, map_mul] }
  let g : P →* H := (q.comp P.subtype).codRestrict H fun a => a.property
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective _ x.val
    exact ⟨⟨a, by change q a ∈ H; rw [ha]; exact x.property⟩, Subtype.ext ha⟩
  have hk : g.ker ≤ f.ker := by
    intro a ha
    have ha' : q a.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 ha'
    change b ^ n = a.val at hb
    have h : r a = toPrincipalIdeal R K b := ideal_pow_injective hn (by
      change r a ^ n = toPrincipalIdeal R K b ^ n
      rw [hr, ← map_pow, hb])
    exact MonoidHom.mem_ker.mpr (by
      change c (r a) = 1
      exact (QuotientGroup.eq_one_iff _).2 ⟨b, h.symm⟩)
  let F : H →* (IdealGroup R K) ⧸ (toPrincipalIdeal R K).range :=
    (QuotientGroup.lift g.ker f hk).comp (QuotientGroup.quotientKerEquivOfSurjective g hg).symm.toMonoidHom
  have hF (a : P) : F (g a) = f a := by
    change QuotientGroup.lift g.ker f hk
      ((QuotientGroup.quotientKerEquivOfSurjective g hg).symm (g a)) = f a
    have he : QuotientGroup.quotientKerEquivOfSurjective g hg (QuotientGroup.mk' g.ker a) =
        g a := rfl
    rw [← he, MulEquiv.symm_apply_apply]
    rfl
  let U : Rˣ →* H := (q.comp (Units.map (algebraMap R K).toMonoidHom)).codRestrict H (by
    intro a
    apply Subgroup.mem_iInf.mpr
    intro w
    apply MonoidHom.mem_ker.mpr
    apply (classOrder_mk w n _).2
    rw [(principal_eq_one_iff _).2 ⟨a, rfl⟩]
    simp [FractionalIdeal.count_one])
  have hUk : U.range = F.ker := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      let y : P := ⟨Units.map (algebraMap R K).toMonoidHom a, (U a).property⟩
      apply MonoidHom.mem_ker.mpr
      change F (g y) = 1
      rw [hF]
      have hy : r y = 1 := ideal_pow_injective hn (by
        change r y ^ n = (1 : IdealGroup R K) ^ n
        rw [hr, one_pow]
        exact (principal_eq_one_iff _).2 ⟨a, rfl⟩)
      change c (r y) = 1
      rw [hy, map_one]
    · intro x hx
      obtain ⟨a, rfl⟩ := hg x
      have e := MonoidHom.mem_ker.mp hx
      rw [hF] at e
      obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff (r a)).mp e
      have hp : toPrincipalIdeal R K (a.val * (b ^ n)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_pow, hb, hr, mul_inv_cancel]
      obtain ⟨z, hz⟩ := (principal_eq_one_iff _).mp hp
      refine ⟨z, Subtype.ext ?_⟩
      change q (Units.map (algebraMap R K).toMonoidHom z) = q a.val
      have hq : q (b ^ n) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨b, rfl⟩
      rw [hz, map_mul, map_inv, hq, inv_one]
      exact @mul_one (Classes K n) _ (q a.val)
  let : (powMonoidHom (α := Rˣ) n).range.FiniteIndex :=
    Subgroup.finiteIndex_range_powMonoidHom_of_fg Rˣ hn.ne'
  let U' : Classes R n →* H := QuotientGroup.lift _ U (by
    rintro _ ⟨a, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    change q (Units.map (algebraMap R K).toMonoidHom (a ^ n)) = 1
    rw [map_pow]
    exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩)
  have hsurj : Function.Surjective (U'.codRestrict F.ker fun x => by
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
      rw [← hUk]
      exact ⟨a, rfl⟩) := by
    intro x
    have hx : x.val ∈ U.range := hUk.symm ▸ x.property
    obtain ⟨a, ha⟩ := hx
    exact ⟨QuotientGroup.mk' _ a, Subtype.ext ha⟩
  let : Finite F.ker := Finite.of_surjective _ hsurj
  exact finite_of_finite_ker F

private theorem finite_outside [Finite (ClassGroup R)] [Group.FG Rˣ]
    (S : Set (HeightOneSpectrum R)) (hS : S.Finite) {n : ℕ} (hn : 0 < n) :
    Finite (↥(⨅ w : {w : HeightOneSpectrum R // w ∉ S}, (classOrder (K := K) w.val n).ker)) := by
  classical
  let H : Subgroup (Classes K n) := ⨅ w : {w : HeightOneSpectrum R // w ∉ S}, (classOrder w.val n).ker
  change Finite H
  let : Finite S := hS
  let : NeZero n := ⟨hn.ne'⟩
  let f : H →* (S → Multiplicative (ZMod n)) :=
    MonoidHom.pi fun w => (classOrder w.val n).comp H.subtype
  let J : Subgroup (Classes K n) := ⨅ w : HeightOneSpectrum R, (classOrder w n).ker
  let : Finite J := finite_everywhere hn
  let g (x : f.ker) : J := ⟨x.val.val, Subgroup.mem_iInf.mpr fun w => by
    apply MonoidHom.mem_ker.mpr
    by_cases h : w ∈ S
    · exact congrFun (MonoidHom.mem_ker.mp x.property) ⟨w, h⟩
    · exact MonoidHom.mem_ker.mp ((Subgroup.mem_iInf.mp x.val.property) ⟨w, h⟩)⟩
  let : Finite f.ker := Finite.of_injective g fun _ _ h =>
    Subtype.ext (Subtype.ext (congrArg (fun j : J => j.val) h))
  exact finite_of_finite_ker f

private theorem valuation_principal (w : HeightOneSpectrum R) (a : Kˣ) :
    w.valuation K a.val =
      WithZero.exp (-FractionalIdeal.count K w (toPrincipalIdeal R K a).val) := by
  classical
  obtain ⟨r, s, e⟩ := IsLocalization.exists_mk'_eq R⁰ (a : K)
  have hr : r ≠ 0 := by
    intro h
    have := a.ne_zero
    exact this (by rw [← e, h, IsFractionRing.mk'_eq_div, map_zero, zero_div])
  have hs := nonZeroDivisors.ne_zero s.property
  rw [coe_toPrincipalIdeal, ← e, w.valuation_of_mk', w.intValuation_if_neg hr,
    w.intValuation_if_neg hs, IsFractionRing.mk'_eq_div, map_div₀,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
    div_eq_mul_inv (↑(Ideal.span {r}) : FractionalIdeal R⁰ K), FractionalIdeal.count_mul K w
      (FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hr))
      (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (Ideal.span_singleton_eq_bot.not.mpr hs))),
    FractionalIdeal.count_inv, FractionalIdeal.count_coe K w (Ideal.span_singleton_eq_bot.not.mpr hr),
    FractionalIdeal.count_coe K w (Ideal.span_singleton_eq_bot.not.mpr hs),
    div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]
  congr 1
  ring

end Dedekind

section Local

variable {L T : Type*} [Field L] [Field T] (v : Valuation L ℤᵐ⁰)

private theorem valuation_of_subring_unit (b : v.valuationSubringˣ) :
    v (b.val : L) = 1 := by
  have h₁ : v (b.val : L) ≤ 1 := b.val.property
  have h₂ : v (b.inv : L) ≤ 1 := b.inv.property
  have hmul : v (b.val : L) * v (b.inv : L) = 1 := by
    rw [← map_mul]
    have h : (b.val : L) * (b.inv : L) = 1 := congrArg Subtype.val b.val_inv
    rw [h, map_one]
  have hle : 1 ≤ v (b.val : L) := calc
    1 = v (b.val : L) * v (b.inv : L) := hmul.symm
    _ ≤ v (b.val : L) * 1 := by gcongr
    _ = v (b.val : L) := mul_one _
  exact h₁.antisymm hle

private def subringUnit (x : Lˣ) (hx : v x.val = 1) : v.valuationSubringˣ where
  val := ⟨x.val, hx.le⟩
  inv := ⟨x.inv, by change v (↑x⁻¹ : L) ≤ 1; rw [Units.val_inv_eq_inv_val, v.map_inv, hx, inv_one]⟩
  val_inv := Subtype.ext x.val_inv
  inv_val := Subtype.ext x.inv_val

private theorem valuation_power_condition (hs : Function.Surjective v) (n : ℕ) (a : Lˣ) :
    QuotientGroup.mk' _ a ∈ (map v.valuationSubring.subtype n).range ↔
      (n : ℤ) ∣ (v a.val).log := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    change QuotientGroup.mk' (powMonoidHom n).range (Units.map v.valuationSubring.subtype.toMonoidHom b') =
      QuotientGroup.mk' (powMonoidHom n).range a at hb
    obtain ⟨d, ⟨c, rfl⟩, hd⟩ := (QuotientGroup.mk'_eq_mk' _).mp hb
    have ha : v a.val = v c.val ^ n := by
      rw [← hd, Units.val_mul, map_mul, powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow]
      change v (b'.val : L) * v c.val ^ n = _
      rw [valuation_of_subring_unit, one_mul]
    refine ⟨(v c.val).log, ?_⟩
    rw [ha, WithZero.log_pow, nsmul_eq_mul]
  · rintro ⟨k, hk⟩
    obtain ⟨c, hc⟩ := hs (WithZero.exp k)
    have hc₀ : c ≠ 0 := fun h => WithZero.exp_ne_zero (by simpa only [h, map_zero] using hc.symm)
    let d := Units.mk0 c hc₀
    have hval : v a.val = v d.val ^ n := by
      have hlog : (v a.val).log = (v d.val ^ n).log := by
        rw [hk, WithZero.log_pow]
        change (n : ℤ) * k = n • (v c).log
        rw [hc, WithZero.log_exp, nsmul_eq_mul]
      have h := congrArg WithZero.exp hlog
      simpa only [WithZero.exp_log ((map_ne_zero v).mpr a.ne_zero),
        WithZero.exp_log (pow_ne_zero n ((map_ne_zero v).mpr d.ne_zero))] using h
    let x := a / d ^ n
    have hx : v x.val = 1 := by
      dsimp only [x]
      rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
      rw [map_div₀, map_pow, hval, div_self (pow_ne_zero _ ((map_ne_zero v).mpr d.ne_zero))]
    refine ⟨QuotientGroup.mk' _ (subringUnit v x hx), ?_⟩
    change QuotientGroup.mk' _ (Units.map _ (subringUnit v x hx)) = QuotientGroup.mk' _ a
    have hy : Units.map v.valuationSubring.subtype.toMonoidHom (subringUnit v x hx) = x :=
      Units.ext rfl
    rw [hy]
    exact (QuotientGroup.mk'_eq_mk' _).mpr ⟨d ^ n, ⟨d, rfl⟩, div_mul_cancel a (d ^ n)⟩

end Local


section PlaceComparison

variable {L T : Type*} [Field L] [Field T]

private theorem map_class {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (n : ℕ) (a : Aˣ) :
    map f n (QuotientGroup.mk' _ a) = QuotientGroup.mk' _ (Units.map f.toMonoidHom a) :=
  rfl

private theorem chart_condition {K R : Type*} [Field K] [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] (w : HeightOneSpectrum R)
    (e : L ≃+* w.adicCompletion K) (V : ValuationSubring L)
    (he : ∀ x, e x ∈ w.adicCompletionIntegers K ↔ x ∈ V)
    (f : K →+* L) (hf : ∀ x, e (f x) = algebraMap K (w.adicCompletion K) x)
    (n : ℕ) (a : Kˣ) :
    map f n (QuotientGroup.mk' _ a) ∈ (map V.subtype n).range ↔
      classOrder w n (QuotientGroup.mk' _ a) = 1 := by
  let W : Valuation (w.adicCompletion K) ℤᵐ⁰ := Valued.v
  let vL := W.comap e.toRingHom
  have hV : V = vL.valuationSubring := by
    ext x
    exact (he x).symm
  have hsurj : Function.Surjective vL := (w.valuedAdicCompletion_surjective K).comp e.surjective
  have hvaluation (x : K) : vL (f x) = w.valuation K x :=
    (congrArg W (hf x)).trans (w.valuedAdicCompletion_eq_valuation' x)
  rw [map_class, hV, valuation_power_condition vL hsurj, classOrder_mk]
  change (n : ℤ) ∣ (vL (f a.val)).log ↔ _
  rw [hvaluation, valuation_principal, WithZero.log_exp, Int.dvd_neg]

private theorem finite_unramified_on_chart {K : Type u} [Field K]
    (D : GlobalFieldData.{u, v} K) {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Algebra R K] [IsFractionRing R K] [Finite (ClassGroup R)] [Group.FG Rˣ]
    (j : HeightOneSpectrum R → D.FinitePlace) (hj : Function.Injective j)
    (S : Set D.Place) (hS : S.Finite) {n : ℕ} (hn : 0 < n)
    (hj' : ∀ w : HeightOneSpectrum R, localUnitCondition D (j w) n ≤ (classOrder w n).ker) :
    Finite (UnramifiedOutside D S n) := by
  let E := (Sum.inl ∘ j) ⁻¹' S
  have hE : E.Finite := Set.Finite.preimage (Sum.inl_injective.comp hj).injOn hS
  let H : Subgroup (Classes K n) := ⨅ w : {w : HeightOneSpectrum R // w ∉ E}, (classOrder w.val n).ker
  have : Finite H := finite_outside E hE hn
  let d (a : UnramifiedOutside D S n) : H :=
    ⟨a.val, Subgroup.mem_iInf.mpr fun w => hj' w (Subgroup.mem_iInf.mp a.property ⟨j w, w.property⟩)⟩
  exact Finite.of_injective d fun _ _ h =>
    Subtype.ext (congrArg (fun x : H => x.val) h)


private theorem local_criterion_of_chart {E : Type u} [Field E]
    (D : GlobalFieldData.{u, v} E) (w : D.FinitePlace) {R : Type*} [CommRing R]
    [IsDedekindDomain R] [Algebra R E] [IsFractionRing R E] (p : HeightOneSpectrum R)
    (e : D.FiniteCompletion w ≃+* p.adicCompletion E)
    (he : ∀ x, e x ∈ p.adicCompletionIntegers E ↔ x ∈ D.integers w) :
    ∃ ν : Valuation (D.FiniteCompletion w) ℤᵐ⁰,
      Function.Surjective ν ∧ ν.valuationSubring = D.integers w ∧
      ∀ (n : ℕ) (a : Eˣ), classOf n a ∈ localUnitCondition D w n ↔
        (n : ℤ) ∣ (ν (D.embedding (.inl w) (a : E))).log := by
  let W : Valuation (p.adicCompletion E) ℤᵐ⁰ := Valued.v
  let ν := W.comap e.toRingHom
  have hv : ν.valuationSubring = D.integers w := by
    ext x
    exact he x
  have hs : Function.Surjective ν := (p.valuedAdicCompletion_surjective E).comp e.surjective
  refine ⟨ν, hs, hv, fun n a => ?_⟩
  change map (D.embedding (.inl w)) n (classOf n a) ∈ (map (D.integers w).subtype n).range ↔ _
  rw [map_class, ← hv]
  exact valuation_power_condition ν hs n (Units.map (D.embedding (.inl w)).toMonoidHom a)

/-- The definition of the subgroup agrees with the normalized valuation
condition at every nonarchimedean place. -/
theorem valuationCriterion : ValuationCriterion.{u, v} := by
  intro E _ D
  cases D with
  | number h =>
    let := h
    intro w
    exact local_criterion_of_chart (.number h) w w (RingEquiv.refl _) (fun _ => Iff.rfl)
  | @function F _ _ _ t =>
    intro w
    have hw : w ∈ Set.range t.placeOfPrime ∪ Set.range t.inverse.placeOfPrime := by
      rw [t.range_placeOfPrime_union_inverse]
      trivial
    rcases hw with ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact local_criterion_of_chart (.function F t) (t.placeOfPrime p) p
        (t.completionEquiv p) (t.completionEquiv_mem_integers p)
    · exact local_criterion_of_chart (.function F t) (t.inverse.placeOfPrime p) p
        (t.inverse.completionEquiv p) (t.inverse.completionEquiv_mem_integers p)

end PlaceComparison


section FunctionFieldUnits

open Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

private theorem inverse_adjoin (t : SeparatingParameter F K) :
    IntermediateField.adjoin F {t.element⁻¹} = IntermediateField.adjoin F {t.element} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (inv_mem (IntermediateField.mem_adjoin_simple_self F t.element))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa only [inv_inv] using inv_mem (IntermediateField.mem_adjoin_simple_self F t.element⁻¹)

private def parameterInversion (t : SeparatingParameter F K) : F⟮X⟯ ≃ₐ[F] F⟮X⟯ :=
  ((RatFunc.algEquivOfTranscendental t.inverse.element t.inverse.transcendental).trans
    (IntermediateField.equivOfEq (inverse_adjoin t))).trans
    (RatFunc.algEquivOfTranscendental t.element t.transcendental).symm

private theorem rationalMap_inversion (t : SeparatingParameter F K) (x : F⟮X⟯) :
    t.rationalMap (parameterInversion t x) = t.inverse.rationalMap x := by
  simp [SeparatingParameter.rationalMap, parameterInversion]
  rfl

private theorem rationalMap_X (t : SeparatingParameter F K) :
    t.rationalMap RatFunc.X = t.element := by
  simp [SeparatingParameter.rationalMap, RatFunc.algEquivOfTranscendental_X]

private theorem parameterInversion_X (t : SeparatingParameter F K) :
    parameterInversion t RatFunc.X = RatFunc.X⁻¹ := by
  apply t.rationalMap.injective
  change t.rationalMap (parameterInversion t RatFunc.X) = t.rationalMap RatFunc.X⁻¹
  rw [rationalMap_inversion, rationalMap_X, map_inv₀, rationalMap_X]
  rfl

private theorem invertedPolynomial_le_one (t : SeparatingParameter F K) [DecidableEq F⟮X⟯]
    (p : F[X]) :
    RatFunc.inftyValuation F (parameterInversion t (algebraMap F[X] F⟮X⟯ p)) ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg =>
      rw [map_add, map_add]
      exact ((RatFunc.inftyValuation F).map_add _ _).trans (max_le hf hg)
  | monomial n a =>
      rw [RatFunc.algebraMap_monomial, map_mul, map_pow, parameterInversion_X,
        ← RatFunc.algebraMap_eq_C, (parameterInversion t).commutes]
      by_cases ha : a = 0
      · simp [ha]
      · rw [RatFunc.algebraMap_eq_C, map_mul, RatFunc.inftyValuation.C _ ha, one_mul, map_pow]
        apply pow_le_one'
        rw [← one_div, RatFunc.inftyValuation.X_inv]
        exact WithZero.exp_le_exp.mpr (by decide : (-1 : ℤ) ≤ 0)

private theorem parameter_minpoly_coeff (t : SeparatingParameter F K) (x : K)
    (hx : x ∈ t.integerSubalgebra) (hy : x ∈ t.inverse.integerSubalgebra) :
    letI := t.rationalAlgebra
    ∀ i, ∃ a : F, (minpoly F⟮X⟯ x).coeff i = RatFunc.C a := by
  classical
  let Ap := t.polynomialAlgebra
  let Aq := t.inverse.polynomialAlgebra
  let Ar := t.rationalAlgebra
  let As := t.inverse.rationalAlgebra
  change @IsIntegral F[X] K _ _ Ap x at hx
  change @IsIntegral F[X] K _ _ Aq x at hy
  let p := @minpoly F[X] K _ _ Ap x
  let q := @minpoly F[X] K _ _ Aq x
  have hp : @minpoly F⟮X⟯ K _ _ Ar x = p.map (algebraMap F[X] F⟮X⟯) := by
    let := Ap
    let := Ar
    simpa only [Algebra.algebraMap_self_apply] using
      (minpoly.isIntegrallyClosed_eq_field_fractions F⟮X⟯ K hx)
  have hq : @minpoly F⟮X⟯ K _ _ As x = q.map (algebraMap F[X] F⟮X⟯) := by
    let := Aq
    let := As
    simpa only [Algebra.algebraMap_self_apply] using
      (minpoly.isIntegrallyClosed_eq_field_fractions F⟮X⟯ K hy)
  have hcomp : (@algebraMap F⟮X⟯ K _ _ Ar).comp (parameterInversion t).toRingHom =
      (RingEquiv.refl K).toRingHom.comp (@algebraMap F⟮X⟯ K _ _ As) := by
    ext z
    exact rationalMap_inversion t z
  have hiAs : @Algebra.IsIntegral F⟮X⟯ K _ _ As := by
    let := As
    exact Algebra.IsIntegral.of_finite _ _
  have hm := @minpoly.map_eq_of_equiv_equiv F⟮X⟯ _ F⟮X⟯ K K
    _ _ _ _ _ _ As Ar hiAs (parameterInversion t).toRingEquiv
    (RingEquiv.refl K) hcomp x
  change Polynomial.map (parameterInversion t).toRingHom (@minpoly F⟮X⟯ K _ _ As x) =
    @minpoly F⟮X⟯ K _ _ Ar x at hm
  rw [hp, hq] at hm
  intro i
  rw [hp, Polynomial.coeff_map]
  have hi := congrArg (fun r : F⟮X⟯[X] => r.coeff i) hm
  simp only [Polynomial.coeff_map] at hi
  change parameterInversion t (algebraMap F[X] F⟮X⟯ (q.coeff i)) =
    algebraMap F[X] F⟮X⟯ (p.coeff i) at hi
  have hv := invertedPolynomial_le_one t (q.coeff i)
  rw [hi] at hv
  by_cases h : p.coeff i = 0
  · exact ⟨0, by simp [h]⟩
  have hv' : WithZero.exp (↑(p.coeff i).natDegree : ℤ) ≤ 1 := by
    simpa only [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial F h] using hv
  have hd : (p.coeff i).natDegree = 0 := by
    have hn := (WithZero.exp_le_exp (b := (0 : ℤ))).mp hv'
    omega
  exact ⟨(p.coeff i).coeff 0, by rw [Polynomial.eq_C_of_natDegree_eq_zero hd, RatFunc.algebraMap_C, Polynomial.coeff_C_zero]⟩

private theorem finite_integral_both [Finite F] (t : SeparatingParameter F K) :
    {x : K | x ∈ t.integerSubalgebra ∧ x ∈ t.inverse.integerSubalgebra}.Finite := by
  classical
  let := t.rationalAlgebra
  let d := Module.finrank F⟮X⟯ K
  let P := {p : F[X] // p.natDegree ≤ d}
  have : Finite P := Finite.of_injective (fun (p : P) (i : Fin (d + 1)) => p.val.coeff i) (by
    intro p q h
    apply Subtype.ext
    ext i
    by_cases hi : i < d + 1
    · exact congrFun h ⟨i, hi⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p.property.trans_lt (by omega)),
        Polynomial.coeff_eq_zero_of_natDegree_lt (q.property.trans_lt (by omega))])
  refine (Set.finite_iUnion fun p : P => Polynomial.rootSet_finite p.val K).subset ?_
  intro x hx
  obtain ⟨a, ha⟩ := Classical.skolem.mp (parameter_minpoly_coeff t x hx.1 hx.2)
  let p := ∑ i ∈ Finset.range (d + 1), Polynomial.monomial i (a i)
  have hcoeff (i : ℕ) : p.coeff i = if i < d + 1 then a i else 0 := by
    classical
    simp [p, Polynomial.coeff_monomial, eq_comm]
  have hd : p.natDegree ≤ d := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun i hi => by
    rw [hcoeff, ite_eq_right (by omega)]
  have hp : Polynomial.map RatFunc.C p = minpoly F⟮X⟯ x := by
    ext i
    rw [Polynomial.coeff_map, hcoeff]
    split_ifs with hi
    · exact (ha i).symm
    · rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt ((minpoly.natDegree_le x).trans_lt (by omega))]
  have hs : IsScalarTower F F⟮X⟯ K := IsScalarTower.of_algebraMap_eq' t.rationalMap.comp_algebraMap.symm
  have hxint : IsIntegral F⟮X⟯ x := Algebra.IsIntegral.isIntegral _
  have hp₀ : p ≠ 0 := fun h => (minpoly.ne_zero hxint) (by simpa [h] using hp.symm)
  have hroot : Polynomial.aeval x p = 0 := by
    rw [← Polynomial.aeval_map_algebraMap F⟮X⟯ x p]
    exact hp ▸ minpoly.aeval F⟮X⟯ x
  exact Set.mem_iUnion.mpr ⟨⟨p, hd⟩, Polynomial.mem_rootSet.mpr ⟨hp₀, hroot⟩⟩

private theorem function_units_fg [Finite F] (t : SeparatingParameter F K) :
    Group.FG t.integerRingˣ := by
  classical
  let P := {w : HeightOneSpectrum t.inverse.integerRing // t.element ∉ (t.inverse.placeOfPrime w).1}
  have hP : Finite P := (t.finite_poles.preimage (t.inverse.placeOfPrime_injective).injOn : _)
  let U := Units.map (algebraMap t.integerRing K).toMonoidHom
  let f : t.integerRingˣ →* (P → Multiplicative ℤ) := MonoidHom.pi fun w =>
    (idealOrder w.val).comp ((toPrincipalIdeal t.inverse.integerRing K).comp U)
  have hk : Finite f.ker := by
    let j (a : f.ker) :
        {x : K | x ∈ t.integerSubalgebra ∧ x ∈ t.inverse.integerSubalgebra} :=
      ⟨U a.val, a.val.val.property, by
        have hi : ∀ w : HeightOneSpectrum t.inverse.integerRing, w.valuation K (U a.val : K) ≤ 1 := by
          intro w
          by_cases hw : t.element ∈ (t.inverse.placeOfPrime w).1
          · have hr : t.inverse.placeOfPrime w ∈ Set.range t.placeOfPrime := by
              rw [t.range_placeOfPrime]
              exact hw
            obtain ⟨w', h⟩ := hr
            have ha : (U a.val : K) ∈ (t.placeOfPrime w').1 :=
              w'.valuation_le_one (a.val.val)
            change (U a.val : K) ∈ (t.inverse.placeOfPrime w).1
            rw [← h]
            exact ha
          · have hh := congrFun (MonoidHom.mem_ker.mp a.property) ⟨w, hw⟩
            change Multiplicative.ofAdd (FractionalIdeal.count K w
              (toPrincipalIdeal t.inverse.integerRing K (U a.val)).val) = 1 at hh
            rw [valuation_principal, Multiplicative.ofAdd.injective hh, neg_zero, WithZero.exp_zero]
        obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K _ hi
        exact hb ▸ b.property⟩
    have : Finite {x : K | x ∈ t.integerSubalgebra ∧ x ∈ t.inverse.integerSubalgebra} :=
      finite_integral_both t
    exact Finite.of_injective j fun _ _ e =>
      Subtype.ext (Units.ext (IsFractionRing.injective t.integerRing K
        (congrArg (fun x => x.val) e)))
  let g₀ : Additive t.integerRingˣ →+ (P → ℤ) :=
    { toFun := fun a w => (f a.toMul w).toAdd
      map_zero' := by
        funext w
        exact congrFun (map_one f) w
      map_add' := fun a b => by
        funext w
        exact congrFun (map_mul f a.toMul b.toMul) w }
  let g := g₀.toIntLinearMap
  have hkg : Finite g.ker :=
    Finite.of_injective (fun a : g.ker => (⟨a.val.toMul, by
      have ha := LinearMap.mem_ker.mp a.property
      apply MonoidHom.mem_ker.mpr
      funext w
      exact congrFun ha w⟩ : f.ker)) (fun _ _ h =>
        Subtype.ext (Additive.toMul.injective (congrArg (fun x : f.ker => x.val) h)))
  have : Module.Finite ℤ g.ker := Module.Finite.of_finite
  have : Module.Finite ℤ (Additive t.integerRingˣ) := by
    refine ⟨(⊤ : Submodule ℤ _).fg_of_fg_map_of_fg_inf_ker g ?_ ?_⟩
    · exact IsNoetherian.noetherian _
    · rw [top_inf_eq]
      exact Module.Finite.iff_fg.mp (by infer_instance)
  exact GroupFG.iff_add_fg.mpr (Module.Finite.iff_addGroup_fg.mp ‹_›)

end FunctionFieldUnits


/-- Positive power classes subject to the local unit conditions are finite
over both types of global field. -/
theorem globalFiniteness : GlobalFiniteness.{u, v} := by
  intro K _ D
  cases D with
  | number h =>
    let := h
    intro S hS n hn
    let j : HeightOneSpectrum (𝓞 K) → (GlobalFieldData.number.{u, v} h).FinitePlace := id
    apply finite_unramified_on_chart (.number h) j Function.injective_id S hS hn
    intro w c hc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
    exact MonoidHom.mem_ker.mpr
      ((chart_condition w (RingEquiv.refl _) (w.adicCompletionIntegers K)
        (fun _ => Iff.rfl) (algebraMap K _) (fun _ => rfl) n a).mp hc)
  | @function F _ hFin _ t =>
    let : Fintype F := Fintype.ofFinite F
    let := t.polynomialAlgebra
    let := t.rationalAlgebra
    let : Finite (ClassGroup t.integerRing) :=
      Finite.of_fintype (ClassGroup (FunctionField.ringOfIntegers F K))
    let : Group.FG t.integerRingˣ := function_units_fg t
    intro S hS n hn
    apply finite_unramified_on_chart (.function F t) t.placeOfPrime t.placeOfPrime_injective S hS hn
    intro w c hc
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
    exact MonoidHom.mem_ker.mpr
      ((chart_condition w (t.completionEquiv w) (t.placeOfPrime w).integers
        (t.completionEquiv_mem_integers w) (t.placeOfPrime w).embedding
        (t.completionEquiv_embedding w) n a).mp hc)


/-- An integral pullback family has finite image once each local class
is obtained from a torsor over the local ring of integers. -/
theorem finiteIntegralCoordinates : FiniteIntegralCoordinates.{u, v} := by
  intro E _ D S hS I _ n hn X c hc
  let d (x : X) (i : I) : UnramifiedOutside D S (n i) :=
    ⟨c x i, Subgroup.mem_iInf.mpr fun w => hc x i w.val w.property⟩
  let (i : I) : Finite (UnramifiedOutside D S (n i)) :=
    globalFiniteness D S hS (n i) (hn i)
  have h : Set.range c ⊆
      Set.range (fun f : (i : I) → UnramifiedOutside D S (n i) => fun i => (f i).val) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨d x, rfl⟩
  exact (Set.finite_range _).subset h

section AffineTorsors

open scoped TensorProduct
open Algebra.TensorProduct

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

private abbrev character (R : Type*) [CommRing R] {n : ℕ} (m : Characters n) : Mu R n :=
  MonoidAlgebra.of R (Characters n) m

private def coefficient (X : Type*) [AddCommGroup X] [Module R X] (m : Characters n) :
    X ⊗[R] Mu R n →ₗ[R] X := by
  classical
  exact (Finsupp.lapply m).comp
    (TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis (Characters n) R)).toLinearMap

private theorem coefficient_tmul (X : Type*) [AddCommGroup X] [Module R X]
    (m l : Characters n) (x : X) :
    coefficient (R := R) X m (x ⊗ₜ[R] character R l) = if l = m then x else 0 := by
  classical
  change TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis (Characters n) R)
    (x ⊗ₜ[R] character R l) m = _
  rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  change ((MonoidAlgebra.basis (Characters n) R).repr ((MonoidAlgebra.basis _ R) l)) m • x = _
  rw [Module.Basis.repr_self, Finsupp.single_apply]
  split <;> simp

private theorem sum_coefficient [Fintype (Characters n)] (t : A ⊗[R] Mu R n) :
    ∑ m : Characters n, coefficient A m t ⊗ₜ[R] character R m = t := by
  classical
  let F : A ⊗[R] Mu R n ≃ₗ[R] (Characters n →₀ A) :=
    TensorProduct.equivFinsuppOfBasisRight (MonoidAlgebra.basis (Characters n) R)
  calc
    _ = F.symm (F t) := by
      rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply, Finsupp.sum_fintype]
      · rfl
      · intro
        exact TensorProduct.zero_tmul _ _
    _ = t := F.symm_apply_apply t

private def piece (ρ : Coaction R A n) (m : Characters n) : A →ₗ[R] A :=
  (coefficient A m).comp ρ.hom.toLinearMap

private def HasDegree (ρ : Coaction R A n) (m : Characters n) (a : A) : Prop :=
  ρ.hom a = a ⊗ₜ[R] character R m

variable (ρ : Coaction R A n)

private theorem degree_mul {m l : Characters n} {a b : A}
    (ha : HasDegree ρ m a) (hb : HasDegree ρ l b) : HasDegree ρ (m * l) (a * b) := by
  unfold HasDegree at *
  rw [map_mul, ha, hb, tmul_mul_tmul]
  exact congrArg (fun c : Mu R n => (a * b) ⊗ₜ[R] c)
    ((MonoidAlgebra.of R (Characters n)).map_mul m l).symm

private theorem degree_pow {m : Characters n} {a : A} (ha : HasDegree ρ m a) (i : ℕ) :
    HasDegree ρ (m ^ i) (a ^ i) := by
  unfold HasDegree at *
  rw [map_pow, ha, tmul_pow]
  exact congrArg (fun c : Mu R n => (a ^ i) ⊗ₜ[R] c)
    ((MonoidAlgebra.of R (Characters n)).map_pow m i).symm

private theorem degree_inv (m : Characters n) (a : Aˣ)
    (ha : HasDegree ρ m a.val) : HasDegree ρ m⁻¹ (↑a⁻¹ : A) := by
  unfold HasDegree at *
  apply (IsUnit.mul_right_inj (a.isUnit.map ρ.hom)).mp
  change ρ.hom a.val * ρ.hom a.inv = ρ.hom a.val * (a.inv ⊗ₜ[R] character R m⁻¹)
  rw [← map_mul, a.val_inv, map_one, ha, tmul_mul_tmul, a.val_inv,
    ← map_mul (MonoidAlgebra.of R (Characters n)), mul_inv_cancel,
    map_one (MonoidAlgebra.of R (Characters n)), Algebra.TensorProduct.one_def]

private theorem degree_piece [Fintype (Characters n)] (m : Characters n) (a : A) :
    HasDegree ρ m (piece ρ m a) := by
  classical
  have h := congrArg (coefficient (A ⊗[R] Mu R n) m) (ρ.coassoc a)
  have hs : ρ.hom a = ∑ l : Characters n, piece ρ l a ⊗ₜ[R] character R l :=
    (sum_coefficient _).symm
  rw [hs, map_sum, map_sum, map_sum, map_sum, map_sum] at h
  unfold HasDegree
  simpa only [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
    (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := Characters n) _).comul_eq_tmul_self,
    TensorProduct.assoc_symm_tmul, AlgHom.toLinearMap_apply, coefficient_tmul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

private theorem piece_of_degree (a : A) (m l : Characters n) (ha : HasDegree ρ l a) :
    piece ρ m a = if l = m then a else 0 := by
  classical
  change coefficient A m (ρ.hom a) = _
  rw [ha, coefficient_tmul]

private theorem sum_piece [Fintype (Characters n)] (a : A) :
    ∑ m : Characters n, piece ρ m a = a := by
  have hc := ρ.counit a
  have hs : ρ.hom a = ∑ l : Characters n, piece ρ l a ⊗ₜ[R] character R l :=
    (sum_coefficient _).symm
  rw [hs, map_sum, map_sum] at hc
  simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    show ∀ m : Characters n, Coalgebra.counit (R := R) (character R m) = 1 from
      fun m => (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := Characters n) m).counit_eq_one,
    one_smul] using hc

private theorem degree_zero_scalar (h : IsAffineTorsor ρ) {a : A}
    (ha : HasDegree ρ 1 a) : ∃ r : R, algebraMap R A r = a := by
  have : Module.FaithfullyFlat R A := h.1
  have he : (a ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] a := by
    apply h.2.2.1
    rw [comparison, lift_tmul, lift_tmul, map_one, map_one, mul_one, one_mul, ha]
    exact congrArg (fun c : Mu R n => a ⊗ₜ[R] c)
      ((MonoidAlgebra.of R (Characters n)).map_one).symm
  exact (Algebra.IsEffective.of_faithfullyFlat R A a).mp
    (by rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]; exact he)

private theorem scalar_isUnit (h : IsAffineTorsor ρ) {r : R}
    (hr : IsUnit (algebraMap R A r)) : IsUnit r := by
  have : Module.FaithfullyFlat R A := h.1
  exact IsUnit.of_map (algebraMap R A) r hr

private theorem coefficient_left_mul (a : A) (m : Characters n) (t : A ⊗[R] Mu R n) :
    coefficient A m ((a ⊗ₜ[R] (1 : Mu R n)) * t) = a * coefficient A m t := by
  classical
  induction t using TensorProduct.inductionOn with
  | tmul x c =>
    rw [tmul_mul_tmul]
    simp only [coefficient, LinearMap.comp_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
    rw [one_mul, mul_smul_comm]
  | add x y hx hy => simp [mul_add, hx, hy]

private theorem sum_opposite_degrees [Fintype (Characters n)]
    (h : IsAffineTorsor ρ) (m : Characters n) :
    ∃ (d : ℕ) (a b : Fin d → A), (∀ i, HasDegree ρ m⁻¹ (a i)) ∧
      (∀ i, HasDegree ρ m (b i)) ∧ ∑ i, a i * b i = 1 := by
  classical
  obtain ⟨t, ht⟩ := h.2.2.2 ((1 : A) ⊗ₜ[R] character R m)
  obtain ⟨d, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq t
  have hf := congrArg (coefficient A m) ht
  simp only [map_sum, comparison, lift_tmul, includeLeft_apply, coefficient_left_mul,
    coefficient_tmul, ite_true] at hf
  change (∑ i, a i * piece ρ m (b i)) = 1 at hf
  have hg := congrArg (piece ρ 1) hf
  have hOne : HasDegree ρ 1 (1 : A) := by
    unfold HasDegree
    rw [map_one, Algebra.TensorProduct.one_def]
    exact congrArg (fun c : Mu R n => (1 : A) ⊗ₜ[R] c)
      ((MonoidAlgebra.of R (Characters n)).map_one).symm
  rw [map_sum, piece_of_degree ρ 1 1 1 hOne, ite_eq_left rfl] at hg
  refine ⟨d, fun i => piece ρ m⁻¹ (a i), fun i => piece ρ m (b i),
    fun i => degree_piece ρ _ _, fun i => degree_piece ρ _ _, ?_⟩
  rw [← hg]
  apply Finset.sum_congr rfl
  intro i hi
  conv_rhs => rw [← sum_piece ρ (a i)]
  rw [Finset.sum_mul, map_sum, Finset.sum_eq_single m⁻¹]
  · rw [piece_of_degree ρ _ _ _ (degree_mul ρ (degree_piece ρ _ _) (degree_piece ρ _ _)),
      inv_mul_cancel, ite_eq_left rfl]
  · intro l _ hl
    rw [piece_of_degree ρ _ _ _ (degree_mul ρ (degree_piece ρ _ _) (degree_piece ρ _ _))]
    exact ite_eq_right (by rwa [mul_eq_one_iff_eq_inv])
  · simp

private theorem degree_has_unit [IsLocalRing R] [Fintype (Characters n)]
    (h : IsAffineTorsor ρ) (m : Characters n) :
    ∃ x : Aˣ, HasDegree ρ m x.val := by
  classical
  obtain ⟨d, a, b, ha, hb, hab⟩ := sum_opposite_degrees ρ h m
  have hs (i : Fin d) : HasDegree ρ 1 (a i * b i) := by
    simpa only [inv_mul_cancel] using degree_mul ρ (ha i) (hb i)
  choose r hr using fun i => degree_zero_scalar ρ h (hs i)
  have : Module.FaithfullyFlat R A := h.1
  have hinj := FaithfulSMul.algebraMap_injective R A
  have hsum : (∑ i, r i) = 1 := hinj (by rw [map_sum, map_one]; simpa only [hr] using hab)
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum.symm ▸ isUnit_one)
  have haunit : IsUnit (a i * b i) := hr i ▸ hi.map (algebraMap R A)
  obtain ⟨x, hx⟩ := isUnit_of_mul_isUnit_right haunit
  exact ⟨x, hx ▸ hb i⟩

private theorem scalar_unit_of_degree_zero (h : IsAffineTorsor ρ)
    (a : Aˣ) (ha : HasDegree ρ 1 a.val) :
    ∃ r : Rˣ, Units.map (algebraMap R A).toMonoidHom r = a := by
  obtain ⟨r, hr⟩ := degree_zero_scalar ρ h ha
  have hui : IsUnit r := scalar_isUnit ρ h (hr.symm ▸ a.isUnit)
  obtain ⟨u, rfl⟩ := hui
  exact ⟨u, Units.ext hr⟩

private theorem rootEquation_monic {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 0 < n) (a : Rˣ) : (rootEquation n a).Monic :=
  Polynomial.monic_X_pow_sub_C _ hn.ne'

private theorem rootEquation_degree {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}
    (_hn : 0 < n) (a : Rˣ) : (rootEquation n a).natDegree = n := by
  unfold rootEquation
  exact Polynomial.natDegree_X_pow_sub_C

private abbrev generator (n : ℕ) : Characters n := Multiplicative.ofAdd 1

private theorem generator_pow (i : ℕ) : (generator n) ^ i = Multiplicative.ofAdd (i : ZMod n) := by
  change Multiplicative.ofAdd (i • (1 : ZMod n)) = _
  rw [nsmul_one]

private theorem generator_pow_order : generator n ^ n = 1 := by
  simp [generator_pow]

private theorem generator_pow_val [NeZero n] (m : Characters n) :
    generator n ^ m.toAdd.val = m := by
  rw [generator_pow, ZMod.natCast_zmod_val]
  rfl

private theorem power_has_coefficient (h : IsAffineTorsor ρ) {x : Aˣ}
    (hx : HasDegree ρ (generator n) x.val) {d : A} {i : ℕ}
    (hd : HasDegree ρ (generator n ^ i) d) :
    ∃ r : R, d = r • (x.val ^ i) := by
  let a := d * (((x ^ i)⁻¹ : Aˣ) : A)
  have ha : HasDegree ρ 1 a := by
    have hg := degree_mul ρ hd (degree_inv ρ _ (x ^ i) (by simpa using degree_pow ρ hx i))
    exact (mul_inv_cancel (generator n ^ i)) ▸ hg
  obtain ⟨r, hr⟩ := degree_zero_scalar ρ h ha
  refine ⟨r, ?_⟩
  rw [Algebra.smul_def, hr]
  change d = (d * ↑(x ^ i)⁻¹) * (x.val ^ i)
  rw [← Units.val_pow_eq_pow_val, mul_assoc, ← Units.val_mul]
  simp


private theorem root_presentation [IsLocalRing R] (hn : 0 < n) (h : IsAffineTorsor ρ)
    (a : Rˣ) (x : Aˣ) (hx : HasDegree ρ (generator n) x.val)
    (hpow : x.val ^ n = algebraMap R A (a : R)) :
    ∃ e : RootAlgebra n a ≃ₐ[R] A, e (AdjoinRoot.root (rootEquation n a)) = x.val := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let f : RootAlgebra n a →ₐ[R] A :=
    AdjoinRoot.liftAlgHom (rootEquation n a) (Algebra.ofId R A) x.val
      (by simp [rootEquation, hpow])
  have hf : f (AdjoinRoot.root (rootEquation n a)) = x.val := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hsurj : Function.Surjective f := by
    intro z
    choose c hc using fun m : Characters n => power_has_coefficient ρ h hx
      (i := m.toAdd.val) (by rw [generator_pow_val]; exact degree_piece ρ m z)
    refine ⟨∑ m : Characters n, c m • (AdjoinRoot.root (rootEquation n a)) ^ m.toAdd.val, ?_⟩
    simp only [map_sum, AlgHom.map_smul_of_tower, map_pow, hf, ← hc, sum_piece]
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot.mp ?_ : Function.Injective f.toLinearMap)
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hz0 : f z = 0 := hz
    let p := AdjoinRoot.powerBasis' (rootEquation_monic hn a)
    let b := p.basis
    have hb (i : Fin p.dim) : f (b i) = x.val ^ (i : ℕ) := by
      change f (p.basis i) = _
      rw [p.basis_eq_pow, map_pow]
      exact congrArg (· ^ (i : ℕ)) hf
    have he : (∑ j, (b.repr z j) • (x.val ^ (j : ℕ))) = 0 := by
      simpa only [map_sum, AlgHom.map_smul_of_tower, hb] using congrArg f (b.sum_repr z) |>.trans hz0
    have hf' : Module.FaithfullyFlat R A := h.1
    have hcoef (i : Fin p.dim) : b.repr z i = 0 := by
      let m := generator n ^ (i : ℕ)
      have eu := congrArg (piece ρ m) he
      rw [map_sum, map_zero] at eu
      rw [Finset.sum_eq_single i (s := (Finset.univ : Finset (Fin p.dim)))] at eu
      · rw [map_smul, piece_of_degree ρ _ _ _ (degree_pow ρ hx _), ite_eq_left rfl,
          Algebra.smul_def] at eu
        exact FaithfulSMul.algebraMap_injective R A (by
          rw [map_zero]
          exact (x.isUnit.pow (i : ℕ)).mul_left_inj.mp (eu.trans (zero_mul _).symm))
      · intro j _ hji
        rw [map_smul, piece_of_degree ρ _ _ _ (degree_pow ρ hx _), ite_eq_right, smul_zero]
        intro e
        apply hji
        apply Fin.ext
        have hc := congrArg (fun k : Characters n => k.toAdd.val) e
        simpa [m, generator_pow, ZMod.val_natCast_of_lt
          (j.isLt.trans_le (rootEquation_degree hn a).le), ZMod.val_natCast_of_lt
          (i.isLt.trans_le (rootEquation_degree hn a).le)] using hc
      · simp
    exact b.repr.injective (Finsupp.ext fun i => (hcoef i).trans (by simp))
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

/-- Over a local ring, the degree-one part of an affine roots-of-unity torsor has
a homogeneous unit generator. Its nth power determines the unit class. -/
theorem affineTorsorPresentation : AffineTorsorPresentation.{u} := by
  intro R A _ _ _ _ n hn ρ h
  classical
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨x, hx⟩ := degree_has_unit ρ h (generator n)
  have hdeg : HasDegree ρ 1 (x ^ n).val := by
    simpa only [Units.val_pow_eq_pow_val, generator_pow_order] using degree_pow ρ hx n
  obtain ⟨a, ha⟩ := scalar_unit_of_degree_zero ρ h (x ^ n) hdeg
  have hpow : x.val ^ n = algebraMap R A (a : R) := (congrArg Units.val ha).symm
  obtain ⟨e, he⟩ := root_presentation ρ hn h a x hx hpow
  refine ⟨a, e, ?_, ?_⟩
  · rw [he]
    exact hx
  · intro b y hy hy'
    have hdeg' : HasDegree ρ 1 (y * x⁻¹).val := by
      simpa only [mul_inv_cancel, Units.val_mul] using degree_mul ρ hy (degree_inv ρ _ x hx)
    obtain ⟨r, hr⟩ := scalar_unit_of_degree_zero ρ h _ hdeg'
    have heq : (Units.map (algebraMap R A).toMonoidHom r) * x = y := by
      rw [hr, mul_assoc, inv_mul_cancel, mul_one]
    have : Module.FaithfullyFlat R A := h.1
    have hb : a * r ^ n = b := by
      apply Units.ext
      apply FaithfulSMul.algebraMap_injective R A
      have h' := congrArg (fun t : Aˣ => (t : A) ^ n) heq
      change algebraMap R A ((a : R) * (r : R) ^ n) = (algebraMap R A) (b : R)
      have hu : ((Units.map (algebraMap R A).toMonoidHom r : Aˣ) : A) =
          algebraMap R A (r : R) := rfl
      rw [Units.val_mul, hu, mul_pow, hpow, hy'] at h'
      rw [map_mul, map_pow, mul_comm]
      exact h'
    exact ((QuotientGroup.mk'_eq_mk' (powMonoidHom (α := Rˣ) n).range).mpr
      ⟨r ^ n, ⟨r, rfl⟩, hb⟩).symm


end AffineTorsors


section RootTorsor

open scoped TensorProduct
open Algebra.TensorProduct

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 0 < n) (a : Rˣ)

local notation "𝓑" => RootAlgebra n a
local notation "𝓗" => Mu R n
local notation "X₀" => AdjoinRoot.root (rootEquation n a)

omit [Nontrivial R] in
private theorem root_pow : X₀ ^ n = algebraMap R 𝓑 (a : R) := by
  have h := AdjoinRoot.eval₂_root (rootEquation n a)
  unfold rootEquation at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] at h
  exact h

private def rootUnit : 𝓑ˣ := ((isUnit_pow_iff hn.ne').mp
  ((root_pow a).symm ▸ a.isUnit.map (algebraMap R 𝓑))).unit

omit [Nontrivial R] in
private theorem rootUnit_val : (rootUnit hn a : 𝓑) = X₀ := IsUnit.unit_spec _

private def rootActionHom : 𝓑 →ₐ[R] 𝓑 ⊗[R] 𝓗 :=
  AdjoinRoot.liftAlgHom (rootEquation n a) (Algebra.ofId R _) (X₀ ⊗ₜ[R] character R (generator n))
    (by
      unfold rootEquation
      simp only [ Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, sub_eq_zero]
      change (X₀ ⊗ₜ[R] character R (generator n)) ^ n = algebraMap R (𝓑 ⊗[R] 𝓗) (a : R)
      rw [tmul_pow, root_pow]
      have hχ : character R (generator n) ^ n = (1 : 𝓗) := by
        rw [← (MonoidAlgebra.of R (Characters n)).map_pow, generator_pow_order,
          (MonoidAlgebra.of R (Characters n)).map_one]
      rw [hχ]
      exact (includeLeft (R := R) (S := R) (A := 𝓑) (B := 𝓗)).commutes _)

omit [Nontrivial R] in
private theorem rootActionHom_apply :
    rootActionHom a X₀ = X₀ ⊗ₜ[R] character R (generator n) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private def rootAction : Coaction R 𝓑 n where
  hom := rootActionHom a
  coassoc x := by
    let G := Bialgebra.comulAlgHom R 𝓗
    have h₁ : (rootActionHom (n := n) a).toLinearMap.rTensor 𝓗 =
        (Algebra.TensorProduct.map (rootActionHom (n := n) a) (AlgHom.id R 𝓗)).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp
    have h₂ : (Coalgebra.comul (R := R) (A := 𝓗)).lTensor 𝓑 =
        (Algebra.TensorProduct.map (AlgHom.id R 𝓑) G).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp [G, Bialgebra.comulAlgHom]
    rw [h₁, h₂]
    let l := (Algebra.TensorProduct.map (rootActionHom (n := n) a) (AlgHom.id R 𝓗)).comp (rootActionHom (n := n) a)
    let r := (Algebra.TensorProduct.assoc R R R 𝓑 𝓗 𝓗).symm.toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R 𝓑) G).comp (rootActionHom (n := n) a))
    change l x = r x
    apply DFunLike.congr_fun
    apply AdjoinRoot.algHom_ext
    change l X₀ = r X₀
    dsimp only [l, r, AlgHom.comp_apply]
    rw [rootActionHom_apply, map_tmul, map_tmul, rootActionHom_apply]
    have hb : G (character R (generator n)) =
        character R (generator n) ⊗ₜ[R] character R (generator n) :=
      (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := Characters n) _).comul_eq_tmul_self
    rw [hb]
    rfl
  counit x := by
    let G := Bialgebra.counitAlgHom R 𝓗
    have h : (Coalgebra.counit (R := R) (A := 𝓗)).lTensor 𝓑 =
        (Algebra.TensorProduct.map (AlgHom.id R 𝓑) G).toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp [G, Bialgebra.counitAlgHom]
    rw [h]
    let l := (Algebra.TensorProduct.rid R R 𝓑).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R 𝓑) G).comp (rootActionHom (n := n) a))
    change l x = (AlgHom.id R 𝓑) x
    apply DFunLike.congr_fun
    apply AdjoinRoot.algHom_ext
    change l X₀ = X₀
    dsimp only [l, AlgHom.comp_apply]
    rw [rootActionHom_apply, map_tmul]
    have hb : G (character R (generator n)) = 1 :=
      (MonoidAlgebra.isGroupLikeElem_of (R := R) (M := Characters n) _).counit_eq_one
    rw [hb]
    simp

private def cyclicUnit {T : Type*} [CommRing T] (t : Tˣ) (ht : t ^ n = 1) :
    Characters n →* Tˣ :=
  let h : Multiplicative ℤ →* Tˣ :=
    { toFun := fun i => t ^ i.toAdd
      map_one' := zpow_zero _
      map_mul' := fun i j => zpow_add _ _ _ }
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift n
    ⟨h.toAdditiveRight, by change t ^ (n : ℤ) = 1; simpa using ht⟩)

private theorem cyclicUnit_generator {T : Type*} [CommRing T] (t : Tˣ) (ht : t ^ n = 1) :
    cyclicUnit t ht (generator n) = t := by
  unfold cyclicUnit
  change Additive.toMul (ZMod.lift n _ (1 : ZMod n) : Additive Tˣ) = t
  rw [← Int.cast_one (R := ZMod n), ZMod.lift_coe]
  exact zpow_one t

private def ratio : (𝓑 ⊗[R] 𝓑)ˣ :=
  (Units.map (includeLeft (R := R) (S := R) (A := 𝓑) (B := 𝓑)).toMonoidHom (rootUnit hn a))⁻¹ *
    Units.map (includeRight (R := R) (A := 𝓑) (B := 𝓑)).toMonoidHom (rootUnit hn a)

omit [Nontrivial R] in
private theorem ratio_val :
    (ratio hn a : 𝓑 ⊗[R] 𝓑) = (↑((rootUnit hn a)⁻¹) : 𝓑) ⊗ₜ[R] X₀ := by
  change ((↑((rootUnit hn a)⁻¹) : 𝓑) ⊗ₜ[R] (1 : 𝓑)) *
    ((1 : 𝓑) ⊗ₜ[R] ((rootUnit hn a : 𝓑ˣ) : 𝓑)) = _
  rw [rootUnit_val, tmul_mul_tmul, mul_one, one_mul]

omit [Nontrivial R] in
private theorem ratio_pow : ratio hn a ^ n = 1 := by
  have hr : (rootUnit hn a : 𝓑) ^ n = algebraMap R 𝓑 (a : R) := by rw [rootUnit_val, root_pow]
  have hu : rootUnit hn a ^ n = Units.map (algebraMap R 𝓑).toMonoidHom a := Units.ext hr
  let l : 𝓑 →ₐ[R] 𝓑 ⊗[R] 𝓑 := includeLeft
  let r : 𝓑 →ₐ[R] 𝓑 ⊗[R] 𝓑 := includeRight
  have hlef : Units.map l.toMonoidHom (Units.map (algebraMap R 𝓑).toMonoidHom a) =
      Units.map r.toMonoidHom (Units.map (algebraMap R 𝓑).toMonoidHom a) := by
    apply Units.ext
    change l (algebraMap R 𝓑 (a : R)) = r (algebraMap R 𝓑 (a : R))
    exact (l.commutes _).trans (r.commutes _).symm
  change ((Units.map l.toMonoidHom (rootUnit hn a))⁻¹ *
    Units.map r.toMonoidHom (rootUnit hn a)) ^ n = 1
  rw [mul_pow, inv_pow, ← map_pow, ← map_pow, hu, hlef, inv_mul_cancel]

private def rootComparisonInverse : 𝓑 ⊗[R] 𝓗 →ₐ[R] 𝓑 ⊗[R] 𝓑 :=
  lift includeLeft
    ((MonoidAlgebra.lift R _ (Characters n))
      ((Units.coeHom _).comp (cyclicUnit (ratio hn a) (ratio_pow hn a)))) (fun _ _ => Commute.all _ _)

omit [Nontrivial R] in
include hn in
private theorem rootComparison_bijective : Function.Bijective (comparison (rootAction (n := n) a)) := by
  let f := comparison (rootAction (n := n) a)
  let g := rootComparisonInverse hn a
  have hf (x y : 𝓑) : f (x ⊗ₜ[R] y) = (x ⊗ₜ[R] (1 : 𝓗)) * rootActionHom a y := rfl
  have hg (x : 𝓑) (y : 𝓗) : g (x ⊗ₜ[R] y) = (x ⊗ₜ[R] (1 : 𝓑)) *
      (MonoidAlgebra.lift R _ (Characters n))
        ((Units.coeHom _).comp (cyclicUnit (ratio hn a) (ratio_pow hn a))) y := rfl
  have hfL (x : 𝓑) : f (x ⊗ₜ[R] (1 : 𝓑)) = x ⊗ₜ[R] (1 : 𝓗) := by simp [hf]
  have hgL (x : 𝓑) : g (x ⊗ₜ[R] (1 : 𝓗)) = x ⊗ₜ[R] (1 : 𝓑) := by simp [hg]
  have hgX : g ((1 : 𝓑) ⊗ₜ[R] character R (generator n)) = ratio hn a := by
    rw [hg, ← one_def, one_mul, MonoidAlgebra.lift_of]
    exact congrArg Units.val (cyclicUnit_generator _ _)
  have hfX : f ((1 : 𝓑) ⊗ₜ[R] X₀) = X₀ ⊗ₜ[R] character R (generator n) := by
    rw [hf, ← one_def, one_mul, rootActionHom_apply]
  have hfgX : f (g ((1 : 𝓑) ⊗ₜ[R] character R (generator n))) =
      (1 : 𝓑) ⊗ₜ[R] character R (generator n) := by
    rw [hgX, ratio_val, hf, rootActionHom_apply, tmul_mul_tmul, ← rootUnit_val hn a]
    have hm : (↑((rootUnit hn a)⁻¹) : 𝓑) * ↑(rootUnit hn a) = 1 := (rootUnit hn a).inv_val
    rw [hm, one_mul]
  have hgfX : g (f ((1 : 𝓑) ⊗ₜ[R] X₀)) = (1 : 𝓑) ⊗ₜ[R] X₀ := by
    have he : X₀ ⊗ₜ[R] character R (generator n) =
        (X₀ ⊗ₜ[R] (1 : 𝓗)) * ((1 : 𝓑) ⊗ₜ[R] character R (generator n)) := by
      rw [tmul_mul_tmul, mul_one, one_mul]
    rw [hfX, he, map_mul, hgL, hgX, ratio_val, tmul_mul_tmul, ← rootUnit_val hn a]
    have hm : (rootUnit hn a : 𝓑) * (↑((rootUnit hn a)⁻¹) : 𝓑) = 1 := (rootUnit hn a).val_inv
    rw [hm, one_mul]
  have hfg : f.comp g = AlgHom.id R _ := by
    have hright : (f.comp g).comp includeRight = (AlgHom.id R _).comp includeRight := by
      apply MonoidAlgebra.algHom_ext
      · intro m
        let : NeZero n := ⟨hn.ne'⟩
        change f (g ((1 : 𝓑) ⊗ₜ[R] character R m)) = 1 ⊗ₜ[R] character R m
        have he : (1 : 𝓑) ⊗ₜ[R] character R m =
            ((1 : 𝓑) ⊗ₜ[R] character R (generator n)) ^ m.toAdd.val := by
          rw [tmul_pow, one_pow]
          exact congrArg (fun y : 𝓗 => (1 : 𝓑) ⊗ₜ[R] y)
            ((congrArg (MonoidAlgebra.of R (Characters n)) (generator_pow_val m).symm).trans
              ((MonoidAlgebra.of R (Characters n)).map_pow _ _))
        rw [he, map_pow, map_pow, hfgX]
      · ext
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [← mul_one x, ← one_mul y, ← tmul_mul_tmul, map_mul, map_mul]
    exact congrArg₂ (· * ·) (by simp [hfL, hgL]) (DFunLike.congr_fun hright y)
  have hgf : g.comp f = AlgHom.id R _ := by
    have hright : (g.comp f).comp includeRight = (AlgHom.id R _).comp includeRight :=
      AdjoinRoot.algHom_ext hgfX
    apply Algebra.TensorProduct.ext'
    intro x y
    rw [← mul_one x, ← one_mul y, ← tmul_mul_tmul, map_mul, map_mul]
    exact congrArg₂ (· * ·) (by simp [hfL, hgL]) (DFunLike.congr_fun hright y)
  exact ⟨Function.LeftInverse.injective (DFunLike.congr_fun hgf),
    Function.RightInverse.surjective (DFunLike.congr_fun hfg)⟩

end RootTorsor

/-- Adjoining the (n)-th root of a unit gives the standard affine Kummer torsor. -/
theorem rootTorsor : RootTorsor.{u} := by
  intro R _ _ n hn a
  have hm := rootEquation_monic hn a
  have hB : Nontrivial (RootAlgebra n a) := (AdjoinRoot.nontrivial_iff_of_monic hm).mpr
    (by rw [Polynomial.degree_eq_natDegree hm.ne_zero, rootEquation_degree hn a]; exact_mod_cast hn)
  have : Module.Free R (RootAlgebra n a) := hm.free_adjoinRoot
  exact ⟨rootAction a, ⟨inferInstance, inferInstance, rootComparison_bijective hn a⟩,
    rootActionHom_apply a⟩


/-- The class of the scalar read off from the degree-one line is unique. -/
theorem affineTorsorClass : AffineTorsorClass.{u} := by
  intro R A _ _ _ _ n hn ρ h
  classical
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨x, hx⟩ := degree_has_unit ρ h (generator n)
  have hdeg : HasDegree ρ 1 (x ^ n).val := by
    simpa only [Units.val_pow_eq_pow_val, generator_pow_order] using degree_pow ρ hx n
  obtain ⟨a, ha⟩ := scalar_unit_of_degree_zero ρ h (x ^ n) hdeg
  have hpow : x.val ^ n = algebraMap R A (a : R) := (congrArg Units.val ha).symm
  refine ⟨classOf n a, ⟨a, x, rfl, hx, hpow⟩, ?_⟩
  obtain ⟨b, _, _, hb⟩ := affineTorsorPresentation n hn ρ h
  rintro _ ⟨c, y, rfl, hy, hy'⟩
  exact (hb c y hy hy').trans (hb a x hx hpow).symm

open Algebra.TensorProduct in
open scoped TensorProduct in
private theorem coactionTensorMap_character {R T A B : Type*}
    [CommRing R] [CommRing T] [CommRing A] [CommRing B] [Algebra R A] [Algebra T B]
    (f : R →+* T) (g : A →+* B) (hg : g.comp (algebraMap R A) = (algebraMap T B).comp f)
    {n : ℕ} (x : A) (m : Characters n) :
    coactionTensorMap f g hg n (x ⊗ₜ[R] character R m) = g x ⊗ₜ[T] character T m := by
  let : Algebra R (B ⊗[T] Mu T n) :=
    ((algebraMap T (B ⊗[T] Mu T n)).comp f).toAlgebra
  change (Algebra.TensorProduct.lift (R := R) (S := R) _ _ _) (x ⊗ₜ[R] character R m) = _
  rw [Algebra.TensorProduct.lift_tmul]
  rw [MonoidAlgebra.lift_of]
  change (includeLeft : B →ₐ[T] B ⊗[T] Mu T n) (g x) *
      (includeRight : Mu T n →ₐ[T] B ⊗[T] Mu T n) (character T m) = _
  rw [includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one, one_mul]

open scoped TensorProduct in
/-- The degree-one description commutes with restriction to a fraction field. -/
theorem affineClassNaturality : AffineClassNaturality.{u} := by
  intro R T A B _ _ _ _ _ _ n ρ σ f g hg h c hc
  obtain ⟨a, x, rfl, hx, he⟩ := hc
  refine ⟨Units.map f.toMonoidHom a, Units.map g.toMonoidHom x, rfl, ?_, ?_⟩
  · change σ.hom (g x.val) = g x.val ⊗ₜ[T] character T (generator n)
    rw [← h, hx, coactionTensorMap_character]
  · change g x.val ^ n = algebraMap T B (f a.val)
    rw [← map_pow, he]
    exact DFunLike.congr_fun hg a.val


section Classification

open scoped TensorProduct
open Algebra.TensorProduct

/-- Equivariant affine torsors over a local ring are classified by unit classes. -/
theorem affineTorsorClassification : AffineTorsorClassification.{u} := by
  intro R _ _ n hn
  constructor
  · intro c
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ c
    obtain ⟨ρ, hρ, hx⟩ := rootTorsor n hn a
    exact ⟨RootAlgebra n a, inferInstance, inferInstance, ρ, hρ,
      ⟨a, rootUnit hn a, rfl, by rw [rootUnit_val]; exact hx, by rw [rootUnit_val]; exact root_pow a⟩⟩
  · intro A B _ _ _ _ ρ σ hρ hσ
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨c, hc, _⟩ := affineTorsorClass n hn ρ hρ
      refine ⟨c, hc, ?_⟩
      obtain ⟨a, x, hax, hdeg, hp⟩ := hc
      refine ⟨a, Units.map e.toMonoidHom x, hax, ?_, ?_⟩
      · change σ.hom (e x.val) = (e x.val) ⊗ₜ[R] character R (generator n)
        rw [← he, hdeg, map_tmul]
        rfl
      · change e x.val ^ n = _
        rw [← map_pow, hp]
        exact e.commutes _
    · rintro ⟨c, ⟨a, x, ha, hdeg, hp⟩, ⟨b, y, hb, hdeg', hp'⟩⟩
      obtain ⟨r, ⟨s, rfl⟩, hr⟩ := (QuotientGroup.mk'_eq_mk' (powMonoidHom (α := Rˣ) n).range).mp
        (ha.trans hb.symm)
      change a * s ^ n = b at hr
      let Y := Units.map (algebraMap R B).toMonoidHom s
      let z := Y⁻¹ * y
      have hY : HasDegree σ 1 (↑Y⁻¹ : B) := by
        unfold HasDegree
        change σ.hom (algebraMap R B ((↑s⁻¹ : R))) = _ ⊗ₜ[R] character R 1
        rw [σ.hom.commutes]
        exact ((includeLeft : B →ₐ[R] B ⊗[R] Mu R n).commutes _).symm.trans
          (congrArg (fun h : Mu R n => ((↑Y⁻¹ : B)) ⊗ₜ[R] h)
            ((MonoidAlgebra.of R (Characters n)).map_one).symm)
      have hz : HasDegree σ (generator n) z.val := by
        change HasDegree σ (Multiplicative.ofAdd 1) ((↑Y⁻¹ : B) * (y : B))
        exact (one_mul (Multiplicative.ofAdd (1 : ZMod n))) ▸ degree_mul σ hY hdeg'
      have hpz : z.val ^ n = algebraMap R B (a : R) := by
        apply (Y.isUnit.pow n).mul_right_injective
        change Y.val ^ n * z.val ^ n = Y.val ^ n * algebraMap R B (a : R)
        have eqz : Y * z = y := mul_inv_cancel_left Y y
        rw [← mul_pow, ← Units.val_mul, eqz, hp']
        have hs : Y.val ^ n = algebraMap R B ((s : R) ^ n) :=
          ((algebraMap R B).map_pow _ _).symm
        rw [hs, ← map_mul, mul_comm, ← Units.val_pow_eq_pow_val, ← Units.val_mul, hr]
      obtain ⟨e, he⟩ := root_presentation ρ hn hρ a x hdeg hp
      obtain ⟨e', he'⟩ := root_presentation σ hn hσ a z hz hpz
      let e₀ := e.symm.trans e'
      refine ⟨e₀, fun w => ?_⟩
      let l := ((Algebra.TensorProduct.map e₀.toAlgHom (AlgHom.id R (Mu R n))).comp ρ.hom).comp
        e.toAlgHom
      let r := σ.hom.comp e'.toAlgHom
      have h : l = r := by
        apply AdjoinRoot.algHom_ext
        change Algebra.TensorProduct.map e₀.toAlgHom (AlgHom.id R (Mu R n))
          (ρ.hom (e (AdjoinRoot.root (rootEquation n a)))) =
            σ.hom (e' (AdjoinRoot.root (rootEquation n a)))
        rw [he, he', hdeg, hz, map_tmul]
        change e' (e.symm x.val) ⊗ₜ[R] character R (generator n) = _
        rw [← he, e.symm_apply_apply, he']
      have hw := DFunLike.congr_fun h (e.symm w)
      simpa [l, r, e₀] using hw

end Classification

section CoverGeometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Algebra.TensorProduct
open Specs.IntegralCentralQuotient (OverBase HopfSpectrum spectrumOfHopfHom spectrumOfAlgHom
  rightCoaction IsRightTorsor)
open Specs.CentralCover (FiniteKernelTorsor)
open Arithmetic.CentralCover (coordinateHom spectrum_coordinateHom property_of_groupIso)

open private specProductIso specProductIso_fst rightCoaction_product
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient

set_option backward.isDefEq.respectTransparency false in
private theorem cover_coordinate_torsor {R B A M : Type u} [CommRing R] [CommRing B] [CommRing A]
    [HopfAlgebra R B] [HopfAlgebra R A] [CommGroup M]
    {G H Z : Grp (OverBase R)} {q : H ⟶ G} {j : Z ⟶ H}
    (h : FiniteKernelTorsor q j) (eG : HopfSpectrum R B ≅ G)
    (eH : HopfSpectrum R A ≅ H) (eZ : HopfSpectrum R (MonoidAlgebra R M) ≅ Z) :
    let q₀ := coordinateHom (eH.hom ≫ q ≫ eG.inv)
    let j₀ := coordinateHom (eZ.hom ≫ j ≫ eH.inv)
    IsRightTorsor q₀ j₀ := by
  dsimp only
  let q₀ := coordinateHom (eH.hom ≫ q ≫ eG.inv)
  let j₀ := coordinateHom (eZ.hom ≫ j ≫ eH.inv)
  have hq : spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ q := by
    rw [spectrum_coordinateHom]
    simp
  have hj : spectrumOfHopfHom j₀ ≫ eH.hom = eZ.hom ≫ j := by
    rw [spectrum_coordinateHom]
    simp
  refine ⟨property_of_groupIso eH eG hq _ h.finite,
    property_of_groupIso eH eG hq _ h.flat, property_of_groupIso eH eG hq _ h.surjective,
    property_of_groupIso eH eG hq _ h.finitePresentation, ?_⟩
  let F := Grp.forget (OverBase R)
  let Q := Over.forget (Spec (CommRingCat.of R))
  let E : (HopfSpectrum R A).X ≅ H.X := F.mapIso eH
  let D : (HopfSpectrum R (MonoidAlgebra R M)).X ≅ Z.X := F.mapIso eZ
  let V := (HopfSpectrum R A).X
  let W := (HopfSpectrum R (MonoidAlgebra R M)).X
  let f := (spectrumOfHopfHom q₀).hom.hom
  let g := (spectrumOfHopfHom j₀).hom.hom
  have hq' : E.hom ≫ q.hom.hom = f ≫ (F.mapIso eG).hom :=
    (congrArg F.map hq).symm
  have hj' : D.hom ≫ j.hom.hom = g ≫ E.hom := (congrArg F.map hj).symm
  have hfirst : (tensorIso E D).hom ≫ fst H.X Z.X = fst V W ≫ E.hom :=
    tensorHom_fst E.hom D.hom
  have hsec : (tensorIso E D).hom ≫ (snd H.X Z.X ≫ j.hom.hom) =
      (snd V W ≫ g) ≫ E.hom :=
    (tensorHom_snd_assoc E.hom D.hom _).trans (by rw [hj', Category.assoc])
  let : IsMonHom E.hom := inferInstanceAs (IsMonHom eH.hom.hom.hom)
  have hact : (tensorIso E D).hom ≫ (fst H.X Z.X * (snd H.X Z.X ≫ j.hom.hom)) =
      (fst V W * (snd V W ≫ g)) ≫ E.hom :=
    (MonObj.comp_mul _ _ _).trans
      ((congrArg₂ (· * ·) hfirst hsec).trans (MonObj.mul_comp _ _ _).symm)
  have hpb := h.torsor.of_iso' (tensorIso E D) E E (F.mapIso eG) hfirst hact hq' hq'
  let P := specProductIso R A (MonoidAlgebra R M)
  have hf : P.inv ≫ fst V W = spectrumOfAlgHom (includeLeft : A →ₐ[R] A ⊗[R] _) := by
    have h : P.hom ≫ spectrumOfAlgHom (includeLeft : A →ₐ[R] A ⊗[R] _) = fst V W :=
      specProductIso_fst R A (MonoidAlgebra R M)
    exact (Iso.inv_comp_eq P).2 h.symm
  have ha : P.inv ≫ (fst V W * (snd V W ≫ g)) = spectrumOfAlgHom (rightCoaction j₀) :=
    (Iso.inv_comp_eq P).2 (rightCoaction_product j₀).symm
  exact (hpb.of_iso' P.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (hf.trans (Category.comp_id _).symm) (ha.trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)).map Q

set_option backward.isDefEq.respectTransparency false in
private theorem cover_invariants {R B A M : Type u} [CommRing R] [CommRing B] [CommRing A]
    [HopfAlgebra R B] [HopfAlgebra R A] [CommGroup M]
    (q : B →ₐc[R] A) (π : A →ₐc[R] MonoidAlgebra R M) (h : IsRightTorsor q π) :
    letI : Algebra B A := q.toAlgHom.toAlgebra
    Module.FaithfullyFlat B A ∧
      (∀ a : A, rightCoaction π a = (a ⊗ₜ[R] (1 : MonoidAlgebra R M)) ↔
        ∃ b : B, q b = a) := by
  have hFF := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom q.toAlgHom.toRingHom)).mp
    ⟨h.2.1, h.2.2.1⟩
  -- Use the target algebra map to form the double fibre product.
  let : Algebra B A := q.toAlgHom.toAlgebra
  have hflat : Module.FaithfullyFlat B A := RingHom.faithfullyFlat_algebraMap_iff.mp hFF
  refine ⟨hflat, ?_⟩
  let f := CommRingCat.ofHom (algebraMap B A)
  let l := CommRingCat.ofHom (includeLeftRingHom : A →+* A ⊗[R] MonoidAlgebra R M)
  let r := CommRingCat.ofHom (rightCoaction π).toRingHom
  have hpb : IsPullback (Spec.map l) (Spec.map r) (Spec.map f) (Spec.map f) := h.2.2.2.2
  have hp : IsPushout f f l r :=
    (IsPullback.of_map_of_faithful Scheme.Spec hpb.flip).unop
  intro a
  constructor
  · intro ha
    let s := CommRingCat.isPushout_tensorProduct B A A
    let g := hp.desc
      (CommRingCat.ofHom (includeLeftRingHom : A →+* A ⊗[B] A))
      (CommRingCat.ofHom (includeRight : A →ₐ[B] A ⊗[B] A).toRingHom) s.w
    have hl := ConcreteCategory.congr_hom (hp.inl_desc _ _ s.w) a
    have hr := ConcreteCategory.congr_hom (hp.inr_desc _ _ s.w) a
    change g (a ⊗ₜ[R] (1 : MonoidAlgebra R M)) = _ at hl
    change g (rightCoaction π a) = _ at hr
    have hh : a ⊗ₜ[B] (1 : A) = (1 : A) ⊗ₜ[B] a := hl.symm.trans ((congrArg g ha).symm.trans hr)
    exact (Algebra.IsEffective.of_faithfullyFlat B A a).mp
      (by rwa [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero])
  · rintro ⟨b, rfl⟩
    exact (ConcreteCategory.congr_hom hp.w b).symm

end CoverGeometry

section PullbackClasses

open scoped TensorProduct
open Algebra.TensorProduct
open Specs.IntegralCentralQuotient (rightCoaction StrongGrading)
open Specs.CentralCoverSpreading (KernelCoordinates)

variable {R B A T U : Type u} [CommRing R] [CommRing B] [CommRing A]
  [CommRing T] [CommRing U] [HopfAlgebra R A] [Algebra R B] [Algebra R T] [Algebra R U]
  {I : Type} (n : I → ℕ) (q : B →ₐ[R] A) (π : A →ₐc[R] KernelCoordinates R n)

private theorem coordinateCharacter_pow (i : I) :
    coordinateCharacter n i ^ n i = 1 := by
  classical
  apply ULift.ext
  funext j
  change (Pi.mulSingle (M := fun j => Characters (n j)) i (Multiplicative.ofAdd (1 : ZMod (n i))) j) ^ n i = 1
  rcases eq_or_ne j i with rfl | h
  · rw [Pi.mulSingle_eq_same]
    exact generator_pow_order
  · rw [Pi.mulSingle_eq_of_ne h, one_pow]

private abbrev fibreElement [Algebra B A] (p : B →ₐ[R] T) (b : A) :
    letI : Algebra B T := p.toAlgebra
    T ⊗[B] A :=
  let : Algebra B T := p.toAlgebra
  (1 : T) ⊗ₜ[B] b

private theorem fibreElement_scalar (p : B →ₐ[R] T) (r : B) :
    letI : Algebra B A := q.toAlgebra
    letI : Algebra B T := p.toAlgebra
    fibreElement p (q r) = algebraMap T (T ⊗[B] A) (p r) := by
  let : Algebra B A := q.toAlgebra
  let : Algebra B T := p.toAlgebra
  change (1 : T) ⊗ₜ[B] algebraMap B A r = (p r) ⊗ₜ[B] (1 : A)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul]
  exact congrArg (fun t : T => t ⊗ₜ[B] (1 : A)) (Algebra.smul_def r (1 : T) |>.trans (mul_one _))

private theorem pullbackClass_existsUnique [IsLocalRing T]
    (hFF : let : Algebra B A := q.toAlgebra; Module.FaithfullyFlat B A)
    (hdeg₀ : ∀ b : A, rightCoaction π b = b ⊗ₜ[R] (1 : KernelCoordinates R n) →
      ∃ r : B, q r = b)
    (hgraded : StrongGrading π)
    (p : B →ₐ[R] T) (i : I) :
    letI : Algebra B A := q.toAlgebra
    ∃! c : Classes T (n i), PullbackHasClass n π p i c := by
  let : Algebra B A := q.toAlgebra
  let : Algebra B T := p.toAlgebra
  let F := T ⊗[B] A
  let ι : A →ₐ[B] F := includeRight
  let m := coordinateCharacter n i
  let χ := MonoidAlgebra.of R (ULift.{u} (∀ j, Characters (n j)))
  let ρ := rightCoaction π
  let : Module.FaithfullyFlat B A := hFF
  have : Module.FaithfullyFlat T F := inferInstanceAs (Module.FaithfullyFlat T (T ⊗[B] A))
  have hprod {x y : A} (hx : ρ x = x ⊗ₜ[R] χ m⁻¹) (hy : ρ y = y ⊗ₜ[R] χ m) :
      ∃ r : B, q r = x * y := by
    apply hdeg₀
    rw [map_mul, hx, hy, tmul_mul_tmul, ← map_mul, inv_mul_cancel, map_one]
  obtain ⟨d, a, b, ha, hb, hab⟩ := hgraded m
  choose r hr using fun t => hprod (ha t) (hb t)
  have hsum : ∑ t, r t = 1 := by
    apply FaithfulSMul.algebraMap_injective B A
    change q (∑ t, r t) = q 1
    rw [map_sum, map_one]
    simpa only [hr] using hab
  obtain ⟨k, _, hk⟩ := IsLocalRing.exists_of_isUnit_sum (by rw [← map_sum, hsum, map_one]; exact isUnit_one
    : IsUnit (∑ t, p (r t)))
  have hxprod : ι (a k) * ι (b k) = algebraMap T F (p (r k)) := by
    rw [← map_mul, ← hr]
    exact fibreElement_scalar q p _
  have hxIsUnit : IsUnit (ι (a k) * ι (b k)) := hxprod.symm ▸ hk.map _
  let x := (isUnit_of_mul_isUnit_right hxIsUnit).unit
  have hx : x.val = ι (b k) := IsUnit.unit_spec _
  have hxdeg : ρ ((b k) ^ (n i)) = ((b k) ^ (n i)) ⊗ₜ[R] (1 : KernelCoordinates R n) := by
    rw [map_pow, hb k, tmul_pow, ← map_pow, coordinateCharacter_pow n i, map_one]
  obtain ⟨s, hs⟩ := hdeg₀ _ hxdeg
  have hxpow : x.val ^ n i = algebraMap T F (p s) := by
    rw [hx, ← map_pow, ← hs]
    exact fibreElement_scalar q p s
  have hv : IsUnit (p s) := IsUnit.of_map (algebraMap T F) _ (hxpow ▸ x.isUnit.pow _)
  let v := hv.unit
  refine ⟨classOf (n i) v, ⟨b k, v, hb k, ?_, ?_, rfl⟩, ?_⟩
  · change IsUnit (ι (b k))
    rw [← hx]
    exact x.isUnit
  · change ι (b k) ^ n i = algebraMap T F (p s)
    rw [← hx]
    exact hxpow
  rintro c ⟨y, w, hdy, hy, hwy, rfl⟩
  have hy' : IsUnit (ι y) := hy
  have hwy' : ι y ^ n i = algebraMap T F (w : T) := hwy
  obtain ⟨t, ht⟩ := hprod (ha k) hdy
  have ht' : ι (a k) * ι y = algebraMap T F (p t) := by
    rw [← map_mul, ← ht]
    exact fibreElement_scalar q p t
  have hleft : IsUnit (ι (a k)) := isUnit_of_mul_isUnit_left hxIsUnit
  have htunit : IsUnit (p t) := IsUnit.of_map (algebraMap T F) _ (ht' ▸ hleft.mul hy')
  let e : Tˣ := htunit.unit * hk.unit⁻¹
  have he : algebraMap T F (e : T) * x.val = ι y := by
    apply hleft.mul_right_injective
    change ι (a k) * (algebraMap T F (e : T) * x.val) = ι (a k) * ι y
    rw [mul_left_comm, hx, hxprod, ← map_mul, ht']
    congr 1
    change (htunit.unit.val * (hk.unit⁻¹ : Tˣ).val) * hk.unit.val = htunit.unit.val
    rw [mul_assoc, Units.inv_mul, mul_one]
  have he' : v * e ^ n i = w := by
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective T F
    have h := congrArg (fun z : F => z ^ n i) he
    change algebraMap T F (v.val * e.val ^ n i) = algebraMap T F w.val
    rw [mul_pow, ← map_pow, hxpow, hwy'] at h
    rw [map_mul, mul_comm]
    exact h
  exact ((QuotientGroup.mk'_eq_mk' (powMonoidHom (α := Tˣ) (n i)).range).mpr
    ⟨e ^ n i, ⟨e, rfl⟩, he'⟩).symm

private theorem pullbackClass_map [Algebra B A]
    (p : B →ₐ[R] T) (p' : B →ₐ[R] U) (f : T →+* U)
    (hf : f.comp p.toRingHom = p'.toRingHom) (i : I)
    (c : Classes T (n i)) (hc : PullbackHasClass n π p i c) :
    PullbackHasClass n π p' i (map f (n i) c) := by
  let : Algebra B T := p.toAlgebra
  let : Algebra B U := p'.toAlgebra
  let fB : T →ₐ[B] U := { f with commutes' := DFunLike.congr_fun hf }
  let g : T ⊗[B] A →ₐ[B] U ⊗[B] A := Algebra.TensorProduct.map fB (AlgHom.id B A)
  have hg (z : A) : g (fibreElement p z) = fibreElement p' z := by
    simp [g, fibreElement]
  have hscalar (r : T) : g (algebraMap T (T ⊗[B] A) r) = algebraMap U (U ⊗[B] A) (f r) := by
    change g (r ⊗ₜ[B] (1 : A)) = f r ⊗ₜ[B] (1 : A)
    rfl
  obtain ⟨b, a, hdeg, hunit, hpow, rfl⟩ := hc
  refine ⟨b, Units.map f.toMonoidHom a, hdeg, ?_, ?_, rfl⟩
  · change IsUnit (fibreElement p' b)
    rw [← hg]
    exact hunit.map g
  · change fibreElement p' b ^ n i = algebraMap U (U ⊗[B] A) (f a.val)
    have h := congrArg g hpow
    change g (fibreElement p b ^ n i) = g (algebraMap T (T ⊗[B] A) a.val) at h
    simpa only [map_pow, hg, hscalar] using h

theorem closedModelPointLift : ClosedModelPointLift.{u} := by
  intro R C B V L _ _ _ _ _ _ _ _ _ j hj ι hι p a ha
  let p' : B →ₐ[R] ι.range := p.codRestrict ι.range fun b => by
    obtain ⟨c, rfl⟩ := hj b
    exact ⟨a c, (DFunLike.congr_fun ha c).symm⟩
  let e := AlgEquiv.ofInjective ι hι
  refine ⟨e.symm.toAlgHom.comp p', ?_⟩
  exact AlgHom.ext fun b => congrArg Subtype.val (e.apply_symm_apply (p' b))

theorem pullbackClassNaturality : PullbackClassNaturality.{u} := by
  intro R B A T U _ _ _ _ _ _ _ _ _ _ I n π p p' f hf i c hc
  exact pullbackClass_map n π p p' f hf i c hc

theorem pullbackRootMap : PullbackRootMap.{u} := by
  intro R B A T _ _ _ _ _ _ _ _ I n π p i c hc
  let : Algebra B T := p.toAlgebra
  obtain ⟨b, a, hdeg, _, hp, rfl⟩ := hc
  let e := AdjoinRoot.liftAlgHom (rootEquation (n i) a) (Algebra.ofId T (T ⊗[B] A))
    ((1 : T) ⊗ₜ[B] b) (by simp [rootEquation, hp])
  refine ⟨a, b, e, rfl, AdjoinRoot.liftAlgHom_root _ _ _ _, ?_⟩
  intro L _ _ x z
  constructor
  · let χ := MonoidAlgebra.of R (ULift.{u} (∀ j, Characters (n j)))
    change z (χ (coordinateCharacter n i)) ^ n i = 1
    rw [← map_pow z, ← map_pow χ, coordinateCharacter_pow n i, map_one, map_one]
  · rw [hdeg, lift_tmul]

end PullbackClasses

section IntegralCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Specs.IntegralCentralQuotient (OverBase HopfSpectrum spectrumOfHopfHom IsRightTorsor)
open Specs.CentralCover (integersOutside)
open Arithmetic.CentralCover (coordinateHom spectrum_coordinateHom property_of_groupIso)

set_option backward.isDefEq.respectTransparency false in
/-- The Kummer coordinates of the pullbacks at integral points have finite image. -/
theorem coverPullbackFiniteness : CoverPullbackFiniteness.{u, v} := by
  intro E _ D S hS
  dsimp only
  intro I _ n hn G H Z q j hG hH ht eZ
  classical
  let R := ↥(integersOutside D S)
  obtain ⟨B, ⟨eG⟩⟩ := essImage_hopfSpec.mpr hG
  obtain ⟨A, ⟨eH⟩⟩ := essImage_hopfSpec.mpr hH
  let q₀ := coordinateHom (eH.hom ≫ q ≫ eG.inv)
  let π := coordinateHom (eZ.inv ≫ j ≫ eH.inv)
  have hq : spectrumOfHopfHom q₀ ≫ eG.hom = eH.hom ≫ q := by
    rw [spectrum_coordinateHom]
    simp
  have hj : spectrumOfHopfHom π ≫ eH.hom = eZ.inv ≫ j := by
    rw [spectrum_coordinateHom]
    simp
  have hT : IsRightTorsor q₀ π := cover_coordinate_torsor ht eG eH eZ.symm
  have hπ : Function.Surjective π := by
    let φ := CommRingCat.ofHom π.toAlgHom.toRingHom
    have : IsClosedImmersion (Spec.map φ) :=
      property_of_groupIso eZ.symm eH hj @IsClosedImmersion ht.closed
    have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map φ)).2
    have hφ : (Scheme.ΓSpecIso _).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso _).hom = φ := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    change Function.Surjective φ
    rw [← hφ]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
      (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)
  let (i : I) : NeZero (n i) := ⟨(hn i).ne'⟩
  have hgr := Classification.IntegralCentralQuotient.strongGrading π hπ
  let : Algebra B.unop A.unop := q₀.toAlgHom.toAlgebra
  obtain ⟨hFF, hinv⟩ := cover_invariants q₀ π hT
  have hcoord {T : Type u} [CommRing T] [Algebra R T] [IsLocalRing T]
      (p : B.unop →ₐ[R] T) (i : I) :=
    pullbackClass_existsUnique n q₀.toAlgHom π hFF (fun t ht => (hinv t).mp ht) hgr p i
  let c (p : B.unop →ₐ[R] E) (i : I) : Classes E (n i) := (hcoord p i).exists.choose
  refine ⟨B.unop, A.unop, inferInstance, inferInstance, inferInstance, inferInstance, eG, eH,
    q₀, π, hq, hj, hT, hcoord, c, fun p i => ⟨(hcoord p i).exists.choose_spec, ?_⟩, ?_⟩
  · intro d hd
    exact (hcoord p i).unique hd (hcoord p i).exists.choose_spec
  · let X := IntegralModelPoints (B := B.unop) D S (integersOutsideToLocal D S)
    apply finiteIntegralCoordinates D (Sum.inl '' S) (hS.image _) n hn (fun p : X => c p.val)
    intro p i w hw
    have hw' : w ∉ S := fun h => hw ⟨w, h, rfl⟩
    let η := D.embedding (.inl w)
    let j := (D.integers w).subtype
    let : Algebra R (D.integers w) := (integersOutsideToLocal D S w hw').toAlgebra
    let : Algebra R (D.FiniteCompletion w) := (η.comp (algebraMap R E)).toAlgebra
    obtain ⟨p₀, hp₀⟩ := p.property w hw'
    let p₁ : B.unop →ₐ[R] D.FiniteCompletion w :=
      { η.comp p.val.toRingHom with
        commutes' := fun r => congrArg η (p.val.commutes r) }
    have : IsLocalRing (D.integers w) := inferInstance
    obtain ⟨a, ha⟩ := (hcoord p₀ i).exists
    refine ⟨a, (hcoord p₁ i).unique ?_ ?_⟩
    · exact pullbackClass_map n π p₀ p₁ j hp₀ i a ha
    · exact pullbackClass_map n π p.val p₁ η rfl i (c p.val i)
        (hcoord p.val i).exists.choose_spec

end IntegralCover

section SchemeTorsors

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.IntegralCentralQuotient (OverBase spectrumOfAlgHom)
open Specs.Fppf (RightAction RightActionIso IsTorsor)
open Algebra.TensorProduct
open scoped TensorProduct

open private singleton_mem_fppfOver specProductIso specProductIso_fst specProductIso_snd
  from LinearAlgebraicGroups.Classification.IntegralCentralQuotient

private theorem restrict_comp {C : Type*} [Category C]
    {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat} (P : RightAction J G)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : P.Section U) :
    P.res (g ≫ f) x = P.res g (P.res f x) :=
  ConcreteCategory.congr_hom (P.sheaf.obj.map_comp f.op g.op) x

private theorem restrict_act {C : Type*} [Category C]
    {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat} (P : RightAction J G)
    {U V : C} (f : V ⟶ U) (x : P.Section U) (g : G.obj (op U)) :
    P.res f (P.act x g) = P.act (P.res f x) (G.map f.op g) :=
  P.map_act f x g

@[simp]
private theorem restrict_id {C : Type*} [Category C]
    {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat} (P : RightAction J G)
    (U : C) (x : P.Section U) : P.res (𝟙 U) x = x :=
  ConcreteCategory.congr_hom (P.sheaf.obj.map_id (op U)) x

private theorem glueTorsorIso {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {J : GrothendieckTopology C} {G : Cᵒᵖ ⥤ GrpCat} {P Q : RightAction J G}
    (hP : IsTorsor P) (hQ : IsTorsor Q) (U : C) (x : P.Section U) (y : Q.Section U)
    (hcov : ∀ W : C, Sieve.generate (Presieve.singleton (snd U W)) ∈ J W)
    (hTop : J.CoversTop (fun _ : Unit => U))
    (hcompat : ∀ {W : C} (r s : W ⟶ U) (g : G.obj (op W)),
      P.act (P.res r x) g = P.res s x → Q.act (Q.res r y) g = Q.res s y) :
    Nonempty (RightActionIso P Q) := by
  let d {W : C} (r : W ⟶ U) (z : P.Section W) : G.obj (op W) :=
    ((hP.1 W (P.res r x)).2 z).choose
  have hd {W : C} (r : W ⟶ U) (z : P.Section W) :
      P.act (P.res r x) (d r z) = z := ((hP.1 W (P.res r x)).2 z).choose_spec
  let k {W : C} (r : W ⟶ U) (z : P.Section W) : Q.Section W := Q.act (Q.res r y) (d r z)
  have knat {V W : C} (f : V ⟶ W) (r : W ⟶ U) (z : P.Section W) :
      Q.res f (k r z) = k (f ≫ r) (P.res f z) := by
    have hh : G.map f.op (d r z) = d (f ≫ r) (P.res f z) := by
      apply (hP.1 V (P.res (f ≫ r) x)).1
      rw [hd, restrict_comp, ← restrict_act P, hd]
    unfold k
    rw [restrict_act Q, hh, restrict_comp]
  have kindep {W : C} (r s : W ⟶ U) (z : P.Section W) : k r z = k s z := by
    obtain ⟨g, hg⟩ := (hP.1 W (P.res r x)).2 (P.res s x)
    have h := hcompat r s g hg
    have hh : d r z = g * d s z := by
      apply (hP.1 W (P.res r x)).1
      rw [hd, ← P.act_mul, hg, hd]
    unfold k
    rw [hh, ← Q.act_mul, h]
  have equiv {W : C} (r : W ⟶ U) (z : P.Section W) (g : G.obj (op W)) :
      k r (P.act z g) = Q.act (k r z) g := by
    have hh : d r (P.act z g) = d r z * g := by
      apply (hP.1 W (P.res r x)).1
      rw [hd, ← P.act_mul, hd]
    exact (congrArg (Q.act (Q.res r y)) hh).trans (Q.act_mul _ _ _).symm
  have hLift (W : C) (z : P.Section W) : ∃ t : Q.Section W,
      ∀ {V : C} (g : V ⟶ W) (r : V ⟶ U), Q.res g t = k r (P.res g z) := by
    let p := snd U W
    let l := fst U W
    have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 Q.sheaf.property).isSheafFor
      (Presieve.singleton p) (hcov W)
    obtain ⟨t, ht, _⟩ := Presieve.isSheafFor_singleton.1 hs (k l (P.res p z)) (by
      intro V f g hfg
      change Q.res f (k l (P.res p z)) = Q.res g (k l (P.res p z))
      rw [knat, knat, ← restrict_comp, ← restrict_comp, hfg]
      exact kindep _ _ _)
    refine ⟨t, fun {V} g r => ?_⟩
    change Q.res p t = k l (P.res p z) at ht
    let a := lift r g
    have hp : a ≫ p = g := lift_snd _ _
    have hl : a ≫ l = r := lift_fst _ _
    rw [← hp, restrict_comp, ht, knat, hl, ← restrict_comp]
  have hequal {W : C} (t t' : Q.Section W) (h : Q.res (snd U W) t = Q.res (snd U W) t') :
      t = t' := by
    have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 Q.sheaf.property).isSheafFor
      (Presieve.singleton (snd U W)) (hcov W)
    obtain ⟨_, _, hu⟩ := Presieve.isSheafFor_singleton.1 hs (Q.res (snd U W) t') (by
      intro V f g e
      change Q.res f (Q.res (snd U W) t') = Q.res g (Q.res (snd U W) t')
      rw [← restrict_comp, ← restrict_comp, e])
    exact (hu _ h).trans (hu _ rfl).symm
  let fa (W : C) (z : P.Section W) := (hLift W z).choose
  have hfa {W V : C} (g : V ⟶ W) (r : V ⟶ U) (z : P.Section W) :
      Q.res g (fa W z) = k r (P.res g z) := (hLift W z).choose_spec g r
  let f : P.sheaf ⟶ Q.sheaf := ⟨{
    app W := ↾fa W.unop
    naturality W V g := by
      apply ConcreteCategory.hom_ext
      intro z
      apply hequal
      change Q.res (snd U V.unop) (fa V.unop (P.res g.unop z)) =
        Q.res (snd U V.unop) (Q.res g.unop (fa W.unop z))
      rw [hfa _ (fst U V.unop), ← restrict_comp Q, hfa _ (fst U V.unop), restrict_comp P] }⟩
  have hIso : IsIso f := by
    apply Sheaf.isIso_of_coversTop hTop
    intro j
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro W
    rw [isIso_iff_bijective]
    let V := W.unop.left
    let r : V ⟶ U := W.unop.hom
    change Function.Bijective (fa V)
    have hlocal : fa V = k r := by
      funext z
      simpa using (hfa (𝟙 V) r z)
    rw [hlocal]
    have hd' : Function.Bijective (d r) := by
      have h := hP.1 V (P.res r x)
      exact ⟨fun a b hab => by rw [← hd r a, ← hd r b, hab],
        fun a => ⟨P.act (P.res r x) a, h.1 (hd _ _)⟩⟩
    exact (hQ.1 V (Q.res r y)).comp hd'
  refine ⟨⟨asIso f, ?_⟩⟩
  intro W z g
  apply hequal
  change Q.res (snd U W) (fa W (P.act z g)) = Q.res (snd U W) (Q.act (fa W z) g)
  rw [restrict_act Q, hfa _ (fst U W), hfa _ (fst U W), restrict_act P, equiv]

section FlatCocycle

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

private abbrev overlap12 : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) includeLeft

private abbrev overlap13 : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) includeRight

private abbrev overlap23 : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) := includeRight

private def twist (c : (B ⊗[R] B)ˣ) : B →ₗ[R] B ⊗[R] B :=
  (LinearMap.mulLeft R (c : B ⊗[R] B)).comp includeRight.toLinearMap

private theorem tensor_twist (c : (B ⊗[R] B)ˣ) (z : B ⊗[R] B) :
    (twist c).lTensor B z = overlap23 (c : B ⊗[R] B) * overlap13 z := by
  induction z with
  | tmul b y =>
    change b ⊗ₜ[R] ((c : B ⊗[R] B) * (1 ⊗ₜ[R] y)) =
      (1 ⊗ₜ[R] (c : B ⊗[R] B)) * (b ⊗ₜ[R] (1 ⊗ₜ[R] y))
    rw [tmul_mul_tmul, one_mul]
  | add x y hx hy => simp [hx, hy, mul_add]

private theorem cocycle_expansion [Module.Flat R B] (c : (B ⊗[R] B)ˣ)
    (hc : overlap13 (c : B ⊗[R] B) = overlap12 (c : B ⊗[R] B) * overlap23 (c : B ⊗[R] B)) :
    ∃ (d : ℕ) (a b : Fin d → B),
      (∀ i, (b i ⊗ₜ[R] 1) = (c : B ⊗[R] B) * (1 ⊗ₜ[R] b i)) ∧
      (∑ i, a i ⊗ₜ[R] b i) = (↑c⁻¹ : B ⊗[R] B) := by
  let f : B →ₗ[R] B ⊗[R] B := (includeLeft : B →ₐ[R] B ⊗[R] B).toLinearMap
  let g := twist c
  have hEq : f.lTensor B (↑c⁻¹ : B ⊗[R] B) = g.lTensor B (↑c⁻¹ : B ⊗[R] B) := by
    change overlap12 (↑c⁻¹ : B ⊗[R] B) = (twist c).lTensor B (↑c⁻¹ : B ⊗[R] B)
    rw [tensor_twist]
    let L := Units.map (overlap12 (R := R) (B := B)).toMonoidHom
    let M := Units.map (overlap13 (R := R) (B := B)).toMonoidHom
    let N := Units.map (overlap23 (R := R) (B := B)).toMonoidHom
    have hu : M c = L c * N c := Units.ext hc
    change (L c⁻¹).val = (N c * M c⁻¹).val
    rw [map_inv L, map_inv M, hu, mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  have hExact := Module.Flat.lTensor_exact (R := R) B (LinearMap.exact_subtype_ker_map (f - g))
  have hker : (↑c⁻¹ : B ⊗[R] B) ∈ LinearMap.ker ((f - g).lTensor B) := by
    rw [LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero]
    exact hEq
  obtain ⟨z, hz⟩ := (LinearMap.exact_iff.mp hExact) ▸ hker
  obtain ⟨d, a, b, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  refine ⟨d, a, fun i => (b i).val, fun i => ?_, ?_⟩
  · have h := LinearMap.mem_ker.mp (b i).property
    exact sub_eq_zero.mp h
  · simpa only [map_sum, LinearMap.lTensor_tmul, Submodule.subtype_apply] using hz

/-- Multiplicative faithfully flat descent for a trivialized line over a local ring. -/
private theorem local_unit_cocycle [IsLocalRing R] [Module.FaithfullyFlat R B]
    (c : (B ⊗[R] B)ˣ)
    (hc : overlap13 (c : B ⊗[R] B) = overlap12 (c : B ⊗[R] B) * overlap23 (c : B ⊗[R] B)) :
    ∃ b : Bˣ, (b.val ⊗ₜ[R] 1) = (c : B ⊗[R] B) * (1 ⊗ₜ[R] b.val) := by
  classical
  let L : B →ₐ[R] B ⊗[R] B := includeLeft
  let Q : B →ₐ[R] B ⊗[R] B := includeRight
  obtain ⟨l, b, x, hx, h₁⟩ := cocycle_expansion c hc
  have hcinv : overlap13 (↑c⁻¹ : B ⊗[R] B) =
      overlap12 (↑c⁻¹ : B ⊗[R] B) * overlap23 (↑c⁻¹ : B ⊗[R] B) := by
    let F := Units.map (overlap13 (R := R) (B := B)).toMonoidHom
    let G := Units.map (overlap12 (R := R) (B := B)).toMonoidHom
    let H := Units.map (overlap23 (R := R) (B := B)).toMonoidHom
    have h : F c = G c * H c := Units.ext hc
    change (F c⁻¹).val = (G c⁻¹ * H c⁻¹).val
    rw [map_inv F, map_inv G, map_inv H, h]
    exact congrArg Units.val ((mul_inv_rev (G c) (H c)).trans
      (mul_comm ((H c)⁻¹) ((G c)⁻¹)))
  obtain ⟨m, d, y, hy, h₂⟩ := cocycle_expansion c⁻¹ hcinv
  rw [inv_inv] at h₂
  have hxy (i : Fin l) (j : Fin m) : ∃ r : R, algebraMap R B r = x i * y j := by
    apply (Algebra.IsEffective.of_faithfullyFlat R B _).mp
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero]
    change L (x i * y j) = Q (x i * y j)
    rw [map_mul, map_mul, show L (x i) = c.val * Q (x i) from hx i,
      show L (y j) = (c⁻¹ : (B ⊗[R] B)ˣ).val * Q (y j) from hy j,
      mul_mul_mul_comm, c.mul_inv, one_mul]
  choose r hr using hxy
  let μ := lmul' R (S := B)
  have hsum : (∑ i, ∑ j, b i * d j * algebraMap R B (r i j)) = 1 := by
    have h := congrArg μ (congrArg₂ (· * ·) h₁ h₂)
    rw [Units.inv_mul] at h
    dsimp only [μ] at h
    rw [Finset.sum_comm]
    simpa only [Finset.sum_mul, Finset.mul_sum, tmul_mul_tmul, map_sum,
      Algebra.TensorProduct.lmul'_apply_tmul, map_one, hr] using h
  have hex : ∃ i j, IsUnit (r i j) := by
    by_contra! hn
    let M := IsLocalRing.maximalIdeal R
    let J := M.map (algebraMap R B)
    have hJ : J ≠ ⊤ := by
      intro hi
      have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) M
      rw [show M.map (algebraMap R B) = ⊤ from hi, Ideal.comap_top] at h
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top h.symm
    have hmem : (1 : B) ∈ J := by
      rw [← hsum]
      exact Submodule.sum_mem J fun i _ => Submodule.sum_mem J fun j _ =>
        J.mul_mem_left _ (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal (r i j)).mpr (hn i j)))
    exact hJ (Ideal.eq_top_of_isUnit_mem J hmem isUnit_one)
  obtain ⟨i, j, h⟩ := hex
  have hu : IsUnit (x i * y j) := hr i j ▸ h.map (algebraMap R B)
  obtain ⟨v, hv⟩ := isUnit_of_mul_isUnit_left hu
  exact ⟨v, hv.symm ▸ hx i⟩

end FlatCocycle

section Sites

variable {R : Type u} [CommRing R]

private abbrev affineTest (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : OverBase R :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

private theorem productCover (U : OverBase R) [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] (W : OverBase R) :
    Sieve.generate (Presieve.singleton (snd U W)) ∈ topology R W := by
  let : Flat (snd U W).left := inferInstanceAs (Flat (pullback.snd U.hom W.hom))
  let : Surjective (snd U W).left := inferInstanceAs (Surjective (pullback.snd U.hom W.hom))
  let : LocallyOfFinitePresentation (snd U W).left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd U.hom W.hom))
  exact singleton_mem_fppfOver _

private theorem coverTop (U : OverBase R) [Flat U.hom] [Surjective U.hom]
    [LocallyOfFinitePresentation U.hom] : (topology R).CoversTop (fun _ : Unit => U) := by
  let t := Over.mk (𝟙 (Spec (CommRingCat.of R)))
  let f : U ⟶ t := Over.mkIdTerminal.from U
  have hf : f.left = U.hom := Over.mkIdTerminal_from_left U
  let : Flat f.left := hf.symm ▸ ‹Flat U.hom›
  let : Surjective f.left := hf.symm ▸ ‹Surjective U.hom›
  let : LocallyOfFinitePresentation f.left := hf.symm ▸ ‹LocallyOfFinitePresentation U.hom›
  apply ((topology R).coversTop_iff_of_isTerminal t Over.mkIdTerminal (fun _ : Unit => U)).2
  apply (topology R).superset_covering _ (singleton_mem_fppfOver f)
  apply (Sieve.generate_le_iff _ _).2
  intro W g hg
  cases hg
  exact ⟨(), ⟨𝟙 U⟩⟩

private theorem exists_affine_section [IsLocalRing R] {n : ℕ} (P : MuTorsor R n) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B),
      let U := affineTest R B
      Flat U.hom ∧ Surjective U.hom ∧ LocallyOfFinitePresentation U.hom ∧
        Nonempty (P.val.Section U) := by
  let S := Spec (CommRingCat.of R)
  let T := Over.mk (𝟙 S)
  let J := Sieve.overEquiv T (P.val.sectionSieve T)
  have hJ : J ∈ Scheme.fppfTopology S := P.property.2 T
  let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ => f.singleton_mem_fppfPrecoverage⟩
  obtain ⟨_, hC, hle⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
    (J := Scheme.fppfPrecoverage)).mp hJ
  obtain ⟨C, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hC
  let V : S.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := C
  obtain ⟨i, p, hp⟩ := V.exists_eq (IsLocalRing.closedPoint R)
  let X := V.X i
  let f : X ⟶ S := V.f i
  let W := X.affineCover.X (X.affineCover.idx p)
  let B := Γ(W, ⊤)
  let j : Spec B ⟶ X := W.isoSpec.inv ≫ X.affineCover.f (X.affineCover.idx p)
  let g := j ≫ f
  have : Flat f := (V.map_prop i).1
  have : LocallyOfFinitePresentation f := (V.map_prop i).2
  have : IsOpenImmersion j := inferInstance
  have : Flat g := inferInstanceAs (Flat (j ≫ f))
  have : LocallyOfFinitePresentation g := inferInstanceAs (LocallyOfFinitePresentation (j ≫ f))
  have hsurj : Surjective g := by
    constructor
    have hOpen := g.isOpenMap (Set.univ : Set (Spec B)) isOpen_univ
    rw [Set.image_univ] at hOpen
    let O : TopologicalSpace.Opens (PrimeSpectrum R) := ⟨Set.range g, hOpen⟩
    have hO : IsLocalRing.closedPoint R ∈ O := by
      obtain ⟨z, hz⟩ := X.affineCover.covers p
      refine ⟨W.isoSpec.hom z, ?_⟩
      change f p = IsLocalRing.closedPoint R at hp
      have hzz : W.isoSpec.inv (W.isoSpec.hom z) = z := by
        exact (congrArg (fun k : W ⟶ W => k z) W.isoSpec.hom_inv_id).trans rfl
      change g (W.isoSpec.hom z) = (IsLocalRing.closedPoint R : S)
      calc
        _ = f (X.affineCover.f (X.affineCover.idx p) (W.isoSpec.inv (W.isoSpec.hom z))) := rfl
        _ = _ := by rw [hzz, hz]; exact hp
    have he := (IsLocalRing.closedPoint_mem_iff O).mp hO
    intro x
    exact show x ∈ O from he.symm ▸ TopologicalSpace.Opens.mem_top x
  obtain ⟨φ, hf⟩ := Spec.map_surjective g
  let : Algebra R B := φ.hom.toAlgebra
  let U := affineTest R B
  have hu : U.hom = g := hf
  let a : U ⟶ T := Over.mkIdTerminal.from U
  have ha : J a.left := by
    rw [show a.left = U.hom from Over.mkIdTerminal_from_left U, hu]
    exact J.downward_closed (hle _ _ (C.toPreZeroHypercover.presieve₀_f i)) j
  refine ⟨B, inferInstance, inferInstance, hu.symm ▸ ‹Flat g›,
    hu.symm ▸ hsurj, hu.symm ▸ ‹LocallyOfFinitePresentation g›, ?_⟩
  have hh := (Sieve.overEquiv_symm_iff J a).2 ha
  change (Sieve.overEquiv T).symm (Sieve.overEquiv T (P.val.sectionSieve T)) a at hh
  have hs : (P.val.sectionSieve T).arrows a := by
    rwa [OrderIso.symm_apply_apply] at hh
  exact hs

end Sites

section RepresentRoot

variable {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ} (hn : 0 < n) (a : Rˣ)

private def rootsAlgEquiv (T : Type u) [CommRing T] [Algebra R T] :
    (RootAlgebra n a →ₐ[R] T) ≃ RootSolutions n a T where
  toFun f := ⟨Units.map f.toMonoidHom (rootUnit hn a), by
    apply Units.ext
    change f (rootUnit hn a : RootAlgebra n a) ^ n = algebraMap R T a.val
    rw [rootUnit_val, ← map_pow, root_pow, f.commutes]⟩
  invFun b := AdjoinRoot.liftAlgHom (rootEquation n a) (Algebra.ofId R T) b.val.val (by
    have h := congrArg Units.val b.property
    change (b.val : T) ^ n = algebraMap R T a.val at h
    simp [rootEquation, h])
  left_inv f := by
    apply AdjoinRoot.algHom_ext
    rw [AdjoinRoot.liftAlgHom_root]
    exact congrArg f (rootUnit_val hn a)
  right_inv b := by
    apply Subtype.ext
    apply Units.ext
    change AdjoinRoot.liftAlgHom _ _ _ _ (rootUnit hn a : RootAlgebra n a) = _
    rw [rootUnit_val, AdjoinRoot.liftAlgHom_root]

private def rootRepresentable (X : OverBase R) :
    (X ⟶ affineTest R (RootAlgebra n a)) ≃ RootSolutions n a (globalRing X) :=
  ((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv X _).symm.trans
    ((Equiv.ofBijective (fun f : (algΓ (CommRingCat.of R)).obj X ⟶
        op (CommAlgCat.of R (RootAlgebra n a)) => f.unop.hom) ⟨
          fun _ _ e => Quiver.Hom.unop_inj (CommAlgCat.hom_ext e),
          fun f => ⟨(CommAlgCat.ofHom f).op, rfl⟩⟩).trans (rootsAlgEquiv hn a (globalRing X)))

omit [Nontrivial R] in
private theorem rootRepresentable_natural {X Y : OverBase R} (f : X ⟶ Y)
    (b : Y ⟶ affineTest R (RootAlgebra n a)) :
    rootRepresentable hn a X (f ≫ b) = RootSolutions.map (globalMap f) (rootRepresentable hn a Y b) := by
  dsimp [rootRepresentable]
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

private def rootPresheaf : (OverBase R)ᵒᵖ ⥤ Type u where
  obj X := RootSolutions n a (globalRing X.unop)
  map f := ↾RootSolutions.map (globalMap f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun f => f.unop.hom x.val.val) ((algΓ (CommRingCat.of R)).map_id X.unop)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply Units.ext
    exact congrArg (fun f => f.unop.hom x.val.val)
      ((algΓ (CommRingCat.of R)).map_comp g.unop f.unop)

private def rootSheaf : Sheaf (topology R) (Type u) := by
  let V := affineTest R (RootAlgebra n a)
  let e : yoneda.obj V ≅ rootPresheaf a :=
    NatIso.ofComponents (fun X => (rootRepresentable hn a X.unop).toIso) fun f => by
      apply ConcreteCategory.hom_ext
      exact rootRepresentable_natural hn a f.unop
  exact ⟨_, (Presheaf.isSheaf_of_iso_iff e).mp ((topology R).yoneda.obj V).property⟩

private def rootSheafAction : RightAction (topology R) (rootsGroup R n) where
  sheaf := rootSheaf hn a
  act {U} x g := RootSolutions.act (T := globalRing U) x g
  act_one x := Subtype.ext (mul_one x.val)
  act_mul x g h := Subtype.ext (mul_assoc x.val g.val h.val)
  map_act f x g := Subtype.ext (map_mul (Units.map (globalMap f).toMonoidHom) x.val g.val)

private theorem rootSheaf_isTorsor : IsTorsor (rootSheafAction hn a) := by
  constructor
  · intro W b
    change Function.Bijective (RootSolutions.act b)
    constructor
    · intro x y h
      exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h))
    · intro c
      let g := b.val⁻¹ * c.val
      have hg : g ∈ rootsOfUnity n (globalRing W) := by
        change (b.val⁻¹ * c.val) ^ n = 1
        rw [mul_pow, inv_pow, b.property, c.property, inv_mul_cancel]
      exact ⟨⟨g, hg⟩, Subtype.ext (mul_inv_cancel_left _ _)⟩
  · intro W
    let V := affineTest R (RootAlgebra n a)
    obtain ⟨ρ, hρ, _⟩ := rootTorsor n hn a
    let : Module.FaithfullyFlat R (RootAlgebra n a) := hρ.1
    have hff : Flat V.hom ∧ Surjective V.hom :=
      (flat_and_surjective_SpecMap_iff _).mpr (RingHom.faithfullyFlat_algebraMap_iff.mpr hρ.1)
    let : Flat V.hom := hff.1
    let : Surjective V.hom := hff.2
    have hfp : (algebraMap R (RootAlgebra n a)).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.mpr hρ.2.1
    let : LocallyOfFinitePresentation V.hom := (LocallyOfFinitePresentation.SpecMap_iff _).mpr hfp
    apply (topology R).superset_covering _ (productCover V W)
    apply (Sieve.generate_le_iff _ _).2
    intro X f hf
    cases hf
    exact ⟨rootRepresentable hn a (V ⊗ W) (fst V W)⟩

private def rootMuTorsor : MuTorsor R n := ⟨rootSheafAction hn a, rootSheaf_isTorsor hn a⟩

private def rootMuPresentation : RootPresentation (rootMuTorsor hn a) a where
  equiv _ := Equiv.refl _
  natural _ _ := rfl
  equivariant _ _ := rfl

end RepresentRoot

section AffineTests

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

private def affineGlobalEquiv (A : Type u) [CommRing A] [Algebra R A] :
    globalRing (affineTest R A) ≃ₐ[R] A :=
  let adj := algΓAlgSpecAdjunction (CommRingCat.of R)
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  (CommAlgCat.algEquivOfIso (asIso (adj.counit.app (op (CommAlgCat.of R A)))).unop).symm

private theorem affineGlobalEquiv_natural (f : A →ₐ[R] B)
    (x : globalRing (affineTest R A)) :
    affineGlobalEquiv (R := R) B (globalMap (spectrumOfAlgHom f) x) = f (affineGlobalEquiv (R := R) A x) := by
  apply (affineGlobalEquiv (R := R) B).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  have h := (algΓAlgSpecAdjunction (CommRingCat.of R)).counit.naturality (CommAlgCat.ofHom f).op
  have he := congrArg (fun g => g.unop.hom (affineGlobalEquiv (R := R) A x)) h
  change globalMap (spectrumOfAlgHom f) ((affineGlobalEquiv (R := R) A).symm (affineGlobalEquiv (R := R) A x)) =
    (affineGlobalEquiv (R := R) B).symm (f (affineGlobalEquiv (R := R) A x)) at he
  simpa only [AlgEquiv.symm_apply_apply] using he

private def affineUnits (A : Type u) [CommRing A] [Algebra R A] :
    (globalRing (affineTest R A))ˣ ≃* Aˣ :=
  Units.mapEquiv (affineGlobalEquiv (R := R) A).toMulEquiv

private theorem affineUnits_natural (f : A →ₐ[R] B)
    (x : (globalRing (affineTest R A))ˣ) :
    affineUnits B (Units.map (globalMap (spectrumOfAlgHom f)).toMonoidHom x) =
      Units.map f.toMonoidHom (affineUnits A x) :=
  Units.ext (affineGlobalEquiv_natural f x.val)

private theorem affineUnits_scalar (A : Type u) [CommRing A] [Algebra R A] (x : Rˣ) :
    affineUnits A (Units.map (algebraMap R (globalRing (affineTest R A))).toMonoidHom x) =
      Units.map (algebraMap R A).toMonoidHom x :=
  Units.ext ((affineGlobalEquiv (R := R) A).commutes x.val)

private theorem affine_map_comp {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    spectrumOfAlgHom g ≫ spectrumOfAlgHom f = spectrumOfAlgHom (g.comp f) :=
  ((algSpec (CommRingCat.of R)).map_comp (CommAlgCat.ofHom g).op (CommAlgCat.ofHom f).op).symm

end AffineTests

section TorsorCocycle

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {n : ℕ}

private abbrev leftTest : affineTest R (B ⊗[R] B) ⟶ affineTest R B :=
  spectrumOfAlgHom (includeLeft : B →ₐ[R] B ⊗[R] B)

private abbrev rightTest : affineTest R (B ⊗[R] B) ⟶ affineTest R B :=
  spectrumOfAlgHom (includeRight : B →ₐ[R] B ⊗[R] B)

private theorem overlap_cocycle (P : MuTorsor R n) (x : P.val.Section (affineTest R B)) :
    ∃ z : (rootsGroup R n).obj (op (affineTest R (B ⊗[R] B))),
      P.val.act (P.val.res leftTest x) z = P.val.res rightTest x ∧
        let c := affineUnits (B ⊗[R] B) z.val
        c ^ n = 1 ∧
        overlap13 c.val = overlap12 c.val * overlap23 c.val := by
  let U := affineTest R B
  let V := affineTest R (B ⊗[R] B)
  let W := affineTest R (B ⊗[R] (B ⊗[R] B))
  let l : V ⟶ U := leftTest
  let r : V ⟶ U := rightTest
  obtain ⟨z, hz⟩ := (P.property.1 V (P.val.res l x)).2 (P.val.res r x)
  refine ⟨z, hz, ?_, ?_⟩
  · exact (map_pow (affineUnits _) _ _).symm.trans
      (by rw [(mem_rootsOfUnity n z.val).mp z.property, map_one])
  let p12 : W ⟶ V := spectrumOfAlgHom overlap12
  let p13 : W ⟶ V := spectrumOfAlgHom overlap13
  let p23 : W ⟶ V := spectrumOfAlgHom overlap23
  have h1 : p12 ≫ l = p13 ≫ l := by
    change spectrumOfAlgHom (overlap12 (R := R) (B := B)) ≫ spectrumOfAlgHom includeLeft =
      spectrumOfAlgHom overlap13 ≫ spectrumOfAlgHom includeLeft
    rw [affine_map_comp, affine_map_comp]
    congr 1
  have h2 : p12 ≫ r = p23 ≫ l := by
    change spectrumOfAlgHom (overlap12 (R := R) (B := B)) ≫ spectrumOfAlgHom includeRight =
      spectrumOfAlgHom overlap23 ≫ spectrumOfAlgHom includeLeft
    rw [affine_map_comp, affine_map_comp]
    congr 1
  have h3 : p13 ≫ r = p23 ≫ r := by
    change spectrumOfAlgHom (overlap13 (R := R) (B := B)) ≫ spectrumOfAlgHom includeRight =
      spectrumOfAlgHom overlap23 ≫ spectrumOfAlgHom includeRight
    rw [affine_map_comp, affine_map_comp]
    congr 1
  have hh (p : W ⟶ V) :
      P.val.act (P.val.res (p ≫ l) x) ((rootsGroup R n).map p.op z) =
        P.val.res (p ≫ r) x := by
    rw [restrict_comp, restrict_comp, ← restrict_act, hz]
  have hmul : (rootsGroup R n).map p13.op z =
      ((rootsGroup R n).map p12.op z) * ((rootsGroup R n).map p23.op z) := by
    apply (P.property.1 W (P.val.res (p13 ≫ l) x)).1
    rw [hh p13, ← P.val.act_mul, ← h1, hh p12, h2, hh p23, h3]
  have h := congrArg (fun g : (rootsGroup R n).obj (op W) =>
    (affineUnits (B ⊗[R] (B ⊗[R] B)) g.val).val) hmul
  change (affineUnits _ (Units.map (globalMap p13).toMonoidHom z.val)).val =
    (affineUnits _
      (Units.map (globalMap p12).toMonoidHom z.val * Units.map (globalMap p23).toMonoidHom z.val)).val at h
  rw [map_mul, affineUnits_natural, affineUnits_natural, affineUnits_natural] at h
  exact h

private theorem sameTorsor_from_overlap [Flat (affineTest R B).hom]
    [Surjective (affineTest R B).hom] [LocallyOfFinitePresentation (affineTest R B).hom]
    (P Q : MuTorsor R n) (x : P.val.Section (affineTest R B)) (y : Q.val.Section (affineTest R B))
    (z : (rootsGroup R n).obj (op (affineTest R (B ⊗[R] B))))
    (hx : P.val.act (P.val.res leftTest x) z = P.val.res rightTest x)
    (hy : Q.val.act (Q.val.res leftTest y) z = Q.val.res rightTest y) :
    Nonempty (RightActionIso P.val Q.val) := by
  let U := affineTest R B
  let e := specProductIso R B B
  apply glueTorsorIso P.property Q.property U x y (productCover U) (coverTop U)
  intro V l r g hg
  let k := lift l r ≫ e.hom
  have hl : k ≫ leftTest = l :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => lift l r ≫ f) (specProductIso_fst R B B)).trans (lift_fst _ _))
  have hr : k ≫ rightTest = r :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun f => lift l r ≫ f) (specProductIso_snd R B B)).trans (lift_snd _ _))
  have h' : P.val.act (P.val.res l x) ((rootsGroup R n).map k.op z) = P.val.res r x := by
    rw [← hl, ← hr, restrict_comp P.val leftTest k, restrict_comp P.val rightTest k,
      ← restrict_act, hx]
  have hgz := (P.property.1 V (P.val.res l x)).1 (hg.trans h'.symm)
  rw [hgz, ← hl, ← hr, restrict_comp Q.val leftTest k, restrict_comp Q.val rightTest k,
    ← restrict_act, hy]

end TorsorCocycle

section Classify

variable {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ}

omit [IsLocalRing R] in
private theorem rootPresentation_transport {P Q : MuTorsor R n} {a : Rˣ}
    (e : RightActionIso P.val Q.val) (h : RootPresentation Q a) : Nonempty (RootPresentation P a) := by
  let e₀ (X : OverBase R) := (e.iso.hom.hom.app (op X))
  let f (X : OverBase R) : P.val.Section X ≃ Q.val.Section X :=
    Equiv.ofBijective (e₀ X) ((isIso_iff_bijective (e₀ X)).1 inferInstance)
  refine ⟨⟨fun X => (f X).trans (h.equiv X), ?_, ?_⟩⟩
  · intro X Y g x
    change h.equiv X (e₀ X (P.val.res g x)) = RootSolutions.map (globalMap g) (h.equiv Y (e₀ Y x))
    rw [← h.natural]
    exact congrArg (h.equiv X) (ConcreteCategory.congr_hom (e.iso.hom.hom.naturality g.op) x)
  · intro X x g
    change h.equiv X (e₀ X (P.val.act x g)) = (h.equiv X (e₀ X x)).act g
    rw [e.equivariant, h.equivariant]

private theorem fppf_root_presentation (P : MuTorsor R n) (hn : 0 < n) :
    ∃ a : Rˣ, Nonempty (RootPresentation P a) := by
  obtain ⟨B, _, _, hflat, hsurj, hfp, ⟨x⟩⟩ := exists_affine_section P
  let U := affineTest R B
  let D := B ⊗[R] B
  have : Module.FaithfullyFlat R B := RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff _).mp ⟨hflat, hsurj⟩)
  obtain ⟨z, hz, hnz, hc⟩ := overlap_cocycle P x
  let c : Dˣ := affineUnits D z.val
  let l := Units.map (includeLeft : B →ₐ[R] D).toMonoidHom
  let r := Units.map (includeRight : B →ₐ[R] D).toMonoidHom
  obtain ⟨b, hb⟩ := local_unit_cocycle c hc
  have h : l b = c * r b := Units.ext hb
  let v := b⁻¹
  have hv : r v = l v * c := by
    change r b⁻¹ = l b⁻¹ * c
    rw [map_inv, map_inv, h, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  have hvpow : r (v ^ n) = l (v ^ n) := by rw [map_pow, map_pow, hv, mul_pow, hnz, mul_one]
  have heq : ((v.val ^ n) ⊗ₜ[R] (1 : B)) = (1 : B) ⊗ₜ[R] (v.val ^ n) := by
    exact (congrArg Units.val hvpow).symm
  obtain ⟨a, ha⟩ := (Algebra.IsEffective.of_faithfullyFlat R B (v.val ^ n)).mp
    (by rwa [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero])
  have hau : IsUnit a := IsUnit.of_map (algebraMap R B) _ (ha.symm ▸ v.isUnit.pow n)
  let a₀ := hau.unit
  let Q := rootMuTorsor hn a₀
  let e := rootMuPresentation hn a₀
  let y := (e.equiv U).symm ⟨(affineUnits B).symm v, by
    apply (affineUnits B).injective
    rw [map_pow, MulEquiv.apply_symm_apply, affineUnits_scalar]
    exact Units.ext ha.symm⟩
  have hy : affineUnits B (e.equiv U y).val = v := by
    dsimp [y]
    rw [Equiv.apply_symm_apply]
    exact MulEquiv.apply_symm_apply _ _
  have hy' : Q.val.act (Q.val.res leftTest y) z = Q.val.res rightTest y := by
    apply (e.equiv _).injective
    rw [e.equivariant, e.natural, e.natural]
    apply Subtype.ext
    apply (affineUnits D).injective
    change affineUnits D (Units.map (globalMap leftTest).toMonoidHom (e.equiv U y).val * z.val) =
      affineUnits D (Units.map (globalMap rightTest).toMonoidHom (e.equiv U y).val)
    rw [map_mul, affineUnits_natural, affineUnits_natural, hy]
    exact hv.symm
  obtain ⟨e'⟩ := sameTorsor_from_overlap P Q x y z hz hy'
  exact ⟨a₀, rootPresentation_transport e' e⟩

private theorem unique_root_class (P : MuTorsor R n) (a b : Rˣ)
    (e : RootPresentation P a) (f : RootPresentation P b) :
    classOf n a = classOf n b := by
  obtain ⟨B, _, _, hflat, hsurj, _, ⟨x⟩⟩ := exists_affine_section P
  let U := affineTest R B
  let D := B ⊗[R] B
  have : Module.FaithfullyFlat R B := RingHom.faithfullyFlat_algebraMap_iff.mp
    ((flat_and_surjective_SpecMap_iff _).mp ⟨hflat, hsurj⟩)
  obtain ⟨z, hz, _, _⟩ := overlap_cocycle P x
  let c : Dˣ := affineUnits D z.val
  let l := Units.map (includeLeft : B →ₐ[R] D).toMonoidHom
  let r := Units.map (includeRight : B →ₐ[R] D).toMonoidHom
  have hroot (d : Rˣ) (g : RootPresentation P d) :
      let u := affineUnits B (g.equiv U x).val
      r u = l u * c ∧ u ^ n = Units.map (algebraMap R B).toMonoidHom d := by
    dsimp only
    have h := congrArg (g.equiv (affineTest R D)) hz
    rw [g.equivariant, g.natural, g.natural] at h
    have hh := congrArg (fun a : RootSolutions n d (globalRing (affineTest R D)) =>
      affineUnits D a.val) h
    change affineUnits D (Units.map (globalMap leftTest).toMonoidHom (g.equiv U x).val * z.val) =
      affineUnits D (Units.map (globalMap rightTest).toMonoidHom (g.equiv U x).val) at hh
    rw [map_mul, affineUnits_natural, affineUnits_natural] at hh
    refine ⟨hh.symm, ?_⟩
    rw [← map_pow, (g.equiv U x).property, affineUnits_scalar]
  let v := affineUnits B (f.equiv U x).val / affineUnits B (e.equiv U x).val
  have hv : r v = l v := by
    dsimp only [v]
    rw [map_div, map_div, (hroot b f).1, (hroot a e).1]
    rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, ← mul_assoc c, mul_inv_cancel, one_mul,
      ← div_eq_mul_inv]
  have heq : v.val ⊗ₜ[R] (1 : B) = (1 : B) ⊗ₜ[R] v.val :=
    (congrArg Units.val hv).symm
  obtain ⟨d, hd⟩ := (Algebra.IsEffective.of_faithfullyFlat R B v.val).mp
    (by rwa [Algebra.TensorProduct.includeLeftSubRight_apply, sub_eq_zero])
  have hdu : IsUnit d := IsUnit.of_map (algebraMap R B) _ (hd.symm ▸ v.isUnit)
  let w := hdu.unit
  have hw : Units.map (algebraMap R B).toMonoidHom w = v := Units.ext hd
  have hpow : a * w ^ n = b := by
    apply Units.ext
    apply FaithfulSMul.algebraMap_injective R B
    have h := congrArg Units.val (show
        Units.map (algebraMap R B).toMonoidHom (a * w ^ n) =
          Units.map (algebraMap R B).toMonoidHom b from by
      rw [map_mul, map_pow, hw]
      dsimp only [v]
      rw [div_pow, (hroot a e).2, (hroot b f).2, ← mul_div_assoc, mul_div_cancel_left])
    exact h
  exact (QuotientGroup.mk'_eq_mk' (powMonoidHom (α := Rˣ) n).range).2
    ⟨w ^ n, ⟨w, rfl⟩, hpow⟩

omit [IsLocalRing R] in
private theorem same_class_isomorphic (P Q : MuTorsor R n) (a b : Rˣ)
    (e : RootPresentation P a) (f : RootPresentation Q b) (h : classOf n a = classOf n b) :
    Nonempty (RightActionIso P.val Q.val) := by
  obtain ⟨_, ⟨d, rfl⟩, hd⟩ := (QuotientGroup.mk'_eq_mk' (powMonoidHom (α := Rˣ) n).range).mp h
  change a * d ^ n = b at hd
  let u (X : OverBase R) := Units.map (algebraMap R (globalRing X)).toMonoidHom d
  have heq (X : OverBase R) : Units.map (algebraMap R (globalRing X)).toMonoidHom a *
      u X ^ n = Units.map (algebraMap R (globalRing X)).toMonoidHom b := by
    rw [← map_pow, ← map_mul, hd]
  let k (X : OverBase R) : RootSolutions n a (globalRing X) ≃ RootSolutions n b (globalRing X) :=
    { toFun := fun t => ⟨t.val * u X, by rw [mul_pow, t.property, heq]⟩
      invFun := fun t => ⟨t.val * (u X)⁻¹, by
        rw [mul_pow, inv_pow, t.property, ← heq, mul_inv_cancel_right]⟩
      left_inv := fun t => Subtype.ext (mul_inv_cancel_right _ _)
      right_inv := fun t => Subtype.ext (inv_mul_cancel_right _ _) }
  let φ (X : OverBase R) := ((e.equiv X).trans (k X)).trans (f.equiv X).symm
  have hφ (X : OverBase R) (t : P.val.Section X) :
      f.equiv X (φ X t) = k X (e.equiv X t) := Equiv.apply_symm_apply _ _
  let m : P.val.sheaf ⟶ Q.val.sheaf := ⟨{
    app X := ↾φ X.unop
    naturality X Y g := by
      apply ConcreteCategory.hom_ext
      intro t
      apply (f.equiv Y.unop).injective
      change f.equiv Y.unop (φ Y.unop (P.val.res g.unop t)) =
        f.equiv Y.unop (Q.val.res g.unop (φ X.unop t))
      simp only [f.natural, hφ, e.natural]
      apply Subtype.ext
      change Units.map (globalMap g.unop).toMonoidHom (e.equiv X.unop t).val * u Y.unop =
        Units.map (globalMap g.unop).toMonoidHom ((e.equiv X.unop t).val * u X.unop)
      rw [map_mul]
      exact congrArg (_ * ·) (Units.ext ((globalMap g.unop).commutes d.val)).symm }⟩
  have : IsIso m := by
    rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
    intro X
    exact (isIso_iff_bijective _).2 (φ X.unop).bijective
  refine ⟨⟨asIso m, fun {X} x g => ?_⟩⟩
  apply (f.equiv X).injective
  change f.equiv X (φ X (P.val.act x g)) = f.equiv X (Q.val.act (φ X x) g)
  simp only [f.equivariant, hφ, e.equivariant]
  apply Subtype.ext
  exact mul_right_comm _ _ _

private theorem roots_group_isSheaf {R : Type u} [CommRing R] [Nontrivial R] {n : ℕ}
    (hn : 0 < n) : Presheaf.IsSheaf (topology R) (rootsGroup R n ⋙ forget GrpCat) := by
  let e (X : OverBase R) : rootsOfUnity n (globalRing X) ≃ RootSolutions n (1 : Rˣ) (globalRing X) :=
    { toFun := fun z => ⟨z.val, (mem_rootsOfUnity n z.val).1 z.property |>.trans (map_one _).symm⟩
      invFun := fun z => ⟨z.val, (mem_rootsOfUnity n z.val).2 (z.property.trans (map_one _))⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
  let i : (rootsGroup R n ⋙ forget GrpCat) ≅ rootPresheaf (1 : Rˣ) :=
    NatIso.ofComponents (fun X => (e X.unop).toIso) fun f => by
      apply ConcreteCategory.hom_ext
      intro x
      exact Subtype.ext rfl
  exact (Presheaf.isSheaf_of_iso_iff i).2 (rootSheaf hn (1 : Rˣ)).property

/-- A right fppf roots-of-unity torsor over a local ring is the torsor of
nth roots of a unit, unique up to an nth power. -/
theorem fppfTorsorClassification : FppfTorsorClassification.{u} := by
  intro R _ _ n hn
  refine ⟨roots_group_isSheaf hn, fun a => ⟨rootMuTorsor hn a, ⟨rootMuPresentation hn a⟩⟩,
    fun P => fppf_root_presentation P hn, ?_⟩
  intro P Q a b e f
  constructor
  · rintro ⟨g⟩
    obtain ⟨f'⟩ := rootPresentation_transport g f
    exact unique_root_class P a b e f'
  · exact same_class_isomorphic P Q a b e f

end Classify

end SchemeTorsors

end LinearAlgebraicGroups.Arithmetic.Kummer
