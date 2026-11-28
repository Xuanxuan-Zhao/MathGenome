import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Presentation
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Quantum.Truncations

noncomputable section

namespace LieNotes.Quantum.Presentation

universe u v w

open Specs.LieNotes.Quantum.Presentation
open LieNotes.Quantum.Truncations (A expH cartanTruncate truncate)

abbrev Root := Specs.LieNotes.Quantum.Presentation.Root
abbrev Cartan := Specs.LieNotes.Quantum.Presentation.Cartan
abbrev cartanMatrix := Specs.LieNotes.Quantum.Presentation.cartanMatrix
abbrev Laurent := Specs.LieNotes.Quantum.Presentation.Laurent
abbrev laurentBasis := Specs.LieNotes.Quantum.Presentation.laurentBasis
abbrev generic := @Specs.LieNotes.Quantum.Presentation.generic
abbrev rationalQ := Specs.LieNotes.Quantum.Presentation.rationalQ
abbrev indeterminate := Specs.LieNotes.Quantum.Presentation.indeterminate
abbrev PolynomialCartan := Specs.LieNotes.Quantum.Presentation.PolynomialCartan
abbrev polynomialBasis := Specs.LieNotes.Quantum.Presentation.polynomialBasis
abbrev TruncatedCartan := Specs.LieNotes.Quantum.Presentation.TruncatedCartan
abbrev truncatedQ := Specs.LieNotes.Quantum.Presentation.truncatedQ
abbrev truncatedK := Specs.LieNotes.Quantum.Presentation.truncatedK
abbrev truncatedD := Specs.LieNotes.Quantum.Presentation.truncatedD
abbrev truncated := Specs.LieNotes.Quantum.Presentation.truncated
abbrev dividedSinh := @Specs.LieNotes.Quantum.Presentation.dividedSinh
abbrev sinhRatio := @Specs.LieNotes.Quantum.Presentation.sinhRatio
abbrev B₀ := @Specs.LieNotes.Quantum.Presentation.B₀
abbrev U := @Specs.LieNotes.Quantum.Presentation.U
abbrev Uₙ := Specs.LieNotes.Quantum.Presentation.Uₙ
abbrev basicIdeal := @Specs.LieNotes.Quantum.Presentation.basicIdeal
abbrev basicQuotient := @Specs.LieNotes.Quantum.Presentation.basicQuotient
abbrev serreIdeal := @Specs.LieNotes.Quantum.Presentation.serreIdeal
abbrev serreQuotient := @Specs.LieNotes.Quantum.Presentation.serreQuotient
abbrev cartan₀ := @Specs.LieNotes.Quantum.Presentation.cartan₀
abbrev E₀ := @Specs.LieNotes.Quantum.Presentation.E₀
abbrev F₀ := @Specs.LieNotes.Quantum.Presentation.F₀
abbrev cartan := @Specs.LieNotes.Quantum.Presentation.cartan
abbrev E := @Specs.LieNotes.Quantum.Presentation.E
abbrev F := @Specs.LieNotes.Quantum.Presentation.F
abbrev mixed := @Specs.LieNotes.Quantum.Presentation.mixed
abbrev SatisfiesBasic := @Specs.LieNotes.Quantum.Presentation.SatisfiesBasic
abbrev SatisfiesSerre := @Specs.LieNotes.Quantum.Presentation.SatisfiesSerre
abbrev liftBasic := @Specs.LieNotes.Quantum.Presentation.liftBasic
abbrev liftU := @Specs.LieNotes.Quantum.Presentation.liftU

set_option linter.unusedSectionVars false

theorem laurentBasis_apply (R : Type u) [CommRing R] (m : Root → ℤ) :
    laurentBasis R m = AddMonoidAlgebra.single m 1 :=
  AddMonoidAlgebra.basis_apply R m

theorem polynomialBasis_apply (R : Type u) [CommRing R] (m : Root → ℕ) :
    polynomialBasis R m = ∏ l : Root, (MvPolynomial.X l : PolynomialCartan R) ^ m l := by
  change (MvPolynomial.basisMonomials Root R).reindex Finsupp.equivFunOnFinite m = _
  rw [Module.Basis.reindex_apply, MvPolynomial.coe_basisMonomials]
  change MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm m) 1 = _
  rw [MvPolynomial.monomial_eq, map_one, one_mul]
  exact Finsupp.prod_fintype _ (fun l d => (MvPolynomial.X l : PolynomialCartan R) ^ d)
    (fun _ => pow_zero _)

section Laurent

variable {k : Type u} [Field k] [CharZero k]

theorem generic_denominator_ne_zero (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    (↑q - ↑(q⁻¹) : k) ≠ 0 := by
  intro h
  apply hq
  calc
    (q : k)^2 = (↑(q⁻¹) : k) * ↑q := by exact (pow_two (q : k)).trans (congrArg (· * (q : k)) (sub_eq_zero.mp h))
    _ = 1 := Units.inv_mul q

@[simp] theorem pairing_coordinate (i l : Root) : pairing i (coordinate l) = cartanMatrix l i := by
  simp [pairing, coordinate, mul_ite]

@[simp] theorem pairing_neg (i : Root) (m : Lattice) : pairing i (-m) = -pairing i m := by
  simp [pairing, Finset.sum_neg_distrib]

@[simp] theorem laurentKappa_single (m : Lattice) (r : k) :
    laurentKappa k (AddMonoidAlgebra.single m r) = AddMonoidAlgebra.single (-m) r := by
  exact AddMonoidAlgebra.domCongr_single _ _ _

theorem generic_scale (q : kˣ) (hq : (q : k)^2 ≠ 1) (i l : Root) :
    (generic q hq).tau i ((generic q hq).K l : Laurent k) =
      (↑(q ^ cartanMatrix l i) : k) • ((generic q hq).K l : Laurent k) := by
  change laurentScale q i (AddMonoidAlgebra.single (coordinate l) 1) = _
  rw [laurentScale_single, pairing_coordinate]
  rfl

theorem generic_commute (q : kˣ) (hq : (q : k)^2 ≠ 1) (i j : Root) :
    Function.Commute ((generic q hq).tau i) ((generic q hq).tau j) := by
  have he : (laurentScale q i).comp (laurentScale q j) =
      (laurentScale q j).comp (laurentScale q i) := by
    apply laurent_ext
    intro m
    simp only [AlgHom.comp_apply, laurentScale_single, map_smul]
    rw [smul_comm]
  exact fun t => DFunLike.congr_fun he t

theorem generic_kappa_K (q : kˣ) (hq : (q : k)^2 ≠ 1) (l : Root) :
    (generic q hq).kappa ((generic q hq).K l : Laurent k) =
      ↑((generic q hq).K l)⁻¹ :=
  laurentKappa_single (coordinate l) 1

theorem generic_kappa_involutive (q : kˣ) (hq : (q : k)^2 ≠ 1) :
    Function.Involutive (generic q hq).kappa := by
  have he : (laurentKappa k).toAlgHom.comp (laurentKappa k).toAlgHom =
      AlgHom.id k (Laurent k) := by
    apply laurent_ext
    intro m
    simp
  exact fun t => DFunLike.congr_fun he t

theorem generic_kappa_tau (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) (t : Laurent k) :
    (generic q hq).kappa ((generic q hq).tau i t) =
      ((generic q hq).tau i).symm ((generic q hq).kappa t) := by
  have he : (laurentKappa k).toAlgHom.comp (laurentScale q i) =
      (laurentScale q⁻¹ i).comp (laurentKappa k).toAlgHom := by
    apply laurent_ext
    intro m
    simp [zpow_neg]
  exact DFunLike.congr_fun he t

theorem generic_kappa_D (q : kˣ) (hq : (q : k)^2 ≠ 1) (i : Root) :
    (generic q hq).kappa ((generic q hq).D i) = -(generic q hq).D i := by
  change laurentKappa k (((↑q - ↑(q⁻¹) : k)⁻¹) •
    (AddMonoidAlgebra.single (coordinate i) 1 - AddMonoidAlgebra.single (-coordinate i) 1)) = _
  rw [map_smul, map_sub, laurentKappa_single, laurentKappa_single, neg_neg]
  change _ = -(_ • (AddMonoidAlgebra.single (coordinate i) 1 - AddMonoidAlgebra.single (-coordinate i) 1))
  rw [← smul_neg, neg_sub]

end Laurent

section Series

variable {S T : Type u} [CommRing S] [CommRing T] [Algebra ℚ S] [Algebra ℚ T]

@[simp] theorem exponentialUnit_val (a : S) :
    (exponentialUnit a : PowerSeries S) = expH a :=
  IsUnit.unit_spec _

@[simp] theorem sinhDenominator_val :
    (sinhDenominator S : PowerSeries S) = dividedSinh (1 : S) :=
  IsUnit.unit_spec _

theorem exponentialUnit_add (a b : S) :
    exponentialUnit (a + b) = exponentialUnit a * exponentialUnit b := by
  apply Units.ext
  simpa only [Units.val_mul, exponentialUnit_val] using Truncations.expH_add a b

def exponentialHom (S : Type u) [CommRing S] [Algebra ℚ S] :
    Multiplicative S →* (PowerSeries S)ˣ where
  toFun a := exponentialUnit a.toAdd
  map_one' := by apply Units.ext; exact exponentialUnit_val (0 : S) |>.trans Truncations.expH_zero
  map_mul' a b := exponentialUnit_add a.toAdd b.toAdd

theorem exponentialUnit_int (n : ℤ) :
    exponentialUnit (n : S) = exponentialUnit (1 : S) ^ n := by
  have h := map_zpow (exponentialHom S) (Multiplicative.ofAdd (1 : S)) n
  simp only [exponentialHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_zpow] at h
  change exponentialUnit (n • (1 : S)) = exponentialUnit (1 : S) ^ n at h
  rwa [zsmul_one] at h

theorem map_dividedSinh (f : S →+* T) (a : S) :
    (dividedSinh a).map f = dividedSinh (f a) := by
  ext n
  simp only [Specs.LieNotes.Quantum.Presentation.dividedSinh, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    Truncations.coeff_expH, map_mul, map_sub, map_pow, map_neg, f.map_rat_algebraMap]

theorem dividedSinh_neg (a : S) : dividedSinh (-a) = -dividedSinh a := by
  ext n
  simp only [Specs.LieNotes.Quantum.Presentation.dividedSinh, PowerSeries.coeff_mk, map_neg, neg_neg, ← mul_neg, neg_sub]

theorem map_sinhRatio (f : S →+* T) (a : S) :
    (sinhRatio a).map f = sinhRatio (f a) := by
  let g : PowerSeries S →+* PowerSeries T := PowerSeries.map f
  have he : Units.map g.toMonoidHom (sinhDenominator S) = sinhDenominator T := by
    apply Units.ext
    change (dividedSinh (1 : S)).map f = dividedSinh (1 : T)
    rw [map_dividedSinh, map_one]
  change g (dividedSinh a * Units.val ((sinhDenominator S)⁻¹)) =
    dividedSinh (f a) * ↑((sinhDenominator T)⁻¹)
  rw [map_mul]
  change (dividedSinh a).map f * ↑(Units.map g.toMonoidHom ((sinhDenominator S)⁻¹)) = _
  rw [map_dividedSinh, map_inv, he]

theorem sinhRatio_neg (a : S) : sinhRatio (-a) = -sinhRatio a := by
  simp only [Specs.LieNotes.Quantum.Presentation.sinhRatio, dividedSinh_neg, neg_mul]

/-- Clearing the shifted series restores the difference of the two exponentials. -/
theorem two_X_mul_dividedSinh (a : S) :
    (2 : PowerSeries S) * PowerSeries.X * dividedSinh a = expH a - expH (-a) := by
  have htwo : (2 : S) * algebraMap ℚ S (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ S) 2, ← map_mul]
    norm_num
  rw [mul_assoc, ← map_ofNat (PowerSeries.C (R := S)) 2]
  ext n
  rw [PowerSeries.coeff_C_mul]
  cases n with
  | zero =>
    simp only [map_sub, Truncations.coeff_expH, pow_zero, one_mul, sub_self]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X,
      zero_mul, mul_zero]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [Specs.LieNotes.Quantum.Presentation.dividedSinh, PowerSeries.coeff_mk,
      map_sub, ← mul_assoc, htwo, one_mul]

theorem exponential_difference_mul_sinhRatio (a : S) :
    (expH (1 : S) - expH (-1 : S)) * sinhRatio a = expH a - expH (-a) := by
  rw [← two_X_mul_dividedSinh (1 : S), ← two_X_mul_dividedSinh a]
  change (2 : PowerSeries S) * PowerSeries.X * dividedSinh 1 *
    (dividedSinh a * Units.val ((sinhDenominator S)⁻¹)) = _
  rw [← sinhDenominator_val (S := S)]
  calc
    _ = ((2 : PowerSeries S) * PowerSeries.X * dividedSinh a) *
          (Units.val (sinhDenominator S) * Units.val ((sinhDenominator S)⁻¹)) := by ac_rfl
    _ = _ := by rw [Units.mul_inv, mul_one]

theorem sinhRatio_constantCoeff (a : S) :
    PowerSeries.constantCoeff (sinhRatio a) = a := by
  have h : PowerSeries.constantCoeff (↑((sinhDenominator S)⁻¹) : PowerSeries S) = 1 := by
    have hu := congrArg (PowerSeries.constantCoeff (R := S)) (Units.mul_inv (sinhDenominator S))
    simpa only [map_mul, map_one, sinhDenominator_val, dividedSinh_const, one_mul] using hu
  change PowerSeries.constantCoeff (dividedSinh a * Units.val ((sinhDenominator S)⁻¹)) = _
  rw [map_mul, dividedSinh_const, h, mul_one]

end Series

section Polynomial

variable {k : Type u} [Field k] [CharZero k]

@[simp] theorem translation_X {R : Type u} [CommRing R] (b : Root → R) (l : Root) :
    translation b (MvPolynomial.X l) = MvPolynomial.X l + MvPolynomial.C (b l) :=
  MvPolynomial.aeval_X _ _

@[simp] theorem polynomialKappa_X (R : Type u) [CommRing R] (l : Root) :
    polynomialKappa R (MvPolynomial.X l) = -MvPolynomial.X l :=
  MvPolynomial.aeval_X _ _

theorem truncated_tau_H (N : ℕ) (i l : Root) :
    (truncated k N).tau i (MvPolynomial.X l) =
      MvPolynomial.X l + MvPolynomial.C (cartanMatrix l i : A k N) :=
  translation_X _ _

theorem truncated_kappa_H (N : ℕ) (l : Root) :
    (truncated k N).kappa (MvPolynomial.X l) = -MvPolynomial.X l :=
  polynomialKappa_X _ _

theorem truncated_commute (N : ℕ) (i j : Root) :
    Function.Commute ((truncated k N).tau i) ((truncated k N).tau j) := by
  let C := truncated k N
  have he : (C.tau i).toAlgHom.comp (C.tau j).toAlgHom =
      (C.tau j).toAlgHom.comp (C.tau i).toAlgHom := by
    ext l : 1
    simp [C, Specs.LieNotes.Quantum.Presentation.truncated, add_right_comm]
  exact fun t => DFunLike.congr_fun he t

theorem truncated_kappa_involutive (N : ℕ) :
    Function.Involutive (truncated k N).kappa := by
  let C := truncated k N
  have he : C.kappa.toAlgHom.comp C.kappa.toAlgHom = AlgHom.id _ _ := by
    ext l : 1
    simp [C, Specs.LieNotes.Quantum.Presentation.truncated]
  exact fun t => DFunLike.congr_fun he t

theorem truncated_kappa_tau (N : ℕ) (i : Root) (t : TruncatedCartan k N) :
    (truncated k N).kappa ((truncated k N).tau i t) =
      ((truncated k N).tau i).symm ((truncated k N).kappa t) := by
  let C := truncated k N
  have he : C.kappa.toAlgHom.comp (C.tau i).toAlgHom =
      (C.tau i).symm.toAlgHom.comp C.kappa.toAlgHom := by
    ext l : 1
    simp [C, Specs.LieNotes.Quantum.Presentation.truncated, sub_eq_add_neg, add_comm]
  exact DFunLike.congr_fun he t

/-- Truncation intertwines polynomial substitutions over the ground field and
their matching substitutions over the truncated coefficient ring. -/
theorem cartanTruncate_map (N : ℕ)
    (f : PolynomialCartan k →ₐ[k] PolynomialCartan k)
    (g : TruncatedCartan k N →ₐ[A k N] TruncatedCartan k N)
    (h : ∀ l, g (MvPolynomial.X l) =
      MvPolynomial.map (algebraMap k (A k N)) (f (MvPolynomial.X l)))
    (p : PowerSeries (PolynomialCartan k)) :
    g (cartanTruncate Root N p) = cartanTruncate Root N (p.map f.toRingHom) := by
  let a := MvPolynomial.map (σ := Root) (algebraMap k (A k N))
  have he : ∀ x, g (a x) = a (f x) := by
    intro x
    induction x using MvPolynomial.induction_on with
    | C r => simp [a]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p l hp =>
      simp only [map_mul, hp]
      rw [show a (MvPolynomial.X l) = MvPolynomial.X l from MvPolynomial.map_X _ _, h]
  simp only [Truncations.cartanTruncate_eq_sum, map_sum, map_mul, map_pow, PowerSeries.coeff_map]
  congr 1
  funext j
  rw [show g (MvPolynomial.C (Truncations.h k N)) = MvPolynomial.C (Truncations.h k N) from g.commutes _, he]
  rfl

theorem truncated_kappa_D (N : ℕ) (i : Root) :
    (truncated k N).kappa ((truncated k N).D i) = -(truncated k N).D i := by
  change polynomialKappa (A k N) (cartanTruncate Root N (sinhRatio (MvPolynomial.X i))) = _
  change (polynomialKappa (A k N)).toAlgHom _ = _
  rw [cartanTruncate_map N (polynomialKappa k).toAlgHom (polynomialKappa (A k N)).toAlgHom,
    map_sinhRatio]
  · change cartanTruncate Root N (sinhRatio (polynomialKappa k (MvPolynomial.X i))) = _
    rw [polynomialKappa_X, sinhRatio_neg, map_neg]
    rfl
  · intro l
    simp

theorem truncated_scale (N : ℕ) (i l : Root) :
    (truncated k N).tau i ((truncated k N).K l : TruncatedCartan k N) =
      (↑((truncated k N).q ^ cartanMatrix l i) : A k N) •
        ((truncated k N).K l : TruncatedCartan k N) := by
  let n := cartanMatrix l i
  let f := translation (fun j => (cartanMatrix j i : k))
  let g := (truncated k N).tau i
  have hg : ∀ j, g.toAlgHom (MvPolynomial.X j) =
      MvPolynomial.map (algebraMap k (A k N)) (f.toAlgHom (MvPolynomial.X j)) := by
    intro j
    change g (MvPolynomial.X j) = MvPolynomial.map _ (f (MvPolynomial.X j))
    rw [truncated_tau_H, translation_X, map_add, MvPolynomial.map_X, MvPolynomial.map_C]
    simp only [map_intCast]
  have hs : cartanTruncate Root N (expH (MvPolynomial.C (σ := Root) (n : k))) =
      MvPolynomial.C (↑(truncatedQ k N ^ n) : A k N) := by
    rw [← Truncations.map_expH MvPolynomial.C, Truncations.cartanTruncate_scalar]
    congr 1
    rw [← exponentialUnit_val (n : k), exponentialUnit_int]
    exact congrArg Units.val (map_zpow
      (Units.map (truncate (R := k) N).toRingHom.toMonoidHom) (exponentialUnit (1 : k)) n)
  have hK : ((truncated k N).K l : TruncatedCartan k N) =
      cartanTruncate Root N (expH (MvPolynomial.X l)) := by
    change cartanTruncate (R := k) Root N (Units.val (exponentialUnit (MvPolynomial.X l : PolynomialCartan k))) = _
    rw [exponentialUnit_val]
  calc
    g ((truncated k N).K l : TruncatedCartan k N) =
        cartanTruncate Root N (expH (f (MvPolynomial.X l))) := by
      rw [hK]
      change g.toAlgHom _ = _
      rw [cartanTruncate_map N f.toAlgHom g.toAlgHom hg, Truncations.map_expH]
      rfl
    _ = MvPolynomial.C (↑(truncatedQ k N ^ n) : A k N) *
          cartanTruncate Root N (expH (MvPolynomial.X l)) := by
      rw [translation_X, Truncations.expH_add, map_mul, mul_comm, hs]
    _ = _ := by rw [hK, Algebra.smul_def]; rfl

end Polynomial

section Presentation

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
variable (C : Cartan R T)

theorem basic_relations : SatisfiesBasic C (cartan₀ C) (E₀ C) (F₀ C) :=
  Specs.LieNotes.Quantum.Presentation.basic_relations C

theorem relations : SatisfiesBasic C (cartan C) (E C) (F C) :=
  Specs.LieNotes.Quantum.Presentation.relations C

theorem serre_relations : SatisfiesSerre C.q (E C) (F C) :=
  Specs.LieNotes.Quantum.Presentation.serre_relations C

variable {B : Type w} [Ring B] [Algebra R B]

theorem basic_hom_ext {f g : B₀ C →ₐ[R] B}
    (ht : ∀ x, f (cartan₀ C x) = g (cartan₀ C x))
    (he : ∀ i, f (E₀ C i) = g (E₀ C i))
    (hf : ∀ i, f (F₀ C i) = g (F₀ C i)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  apply FreeAlgebra.hom_ext
  funext x
  rcases x with t | (i | i)
  · exact ht t
  · exact he i
  · exact hf i

theorem hom_ext {f g : U C →ₐ[R] B}
    (ht : ∀ x, f (cartan C x) = g (cartan C x))
    (he : ∀ i, f (E C i) = g (E C i))
    (hf : ∀ i, f (F C i) = g (F C i)) : f = g := by
  apply Ideal.Quotient.algHom_ext R
  exact basic_hom_ext C ht he hf

@[simp] theorem liftU_cartan (t : T →ₐ[R] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (x : T) :
    liftU C t e f h hs (cartan C x) = t x :=
  Specs.LieNotes.Quantum.Presentation.liftU_cartan C t e f h hs x

@[simp] theorem liftU_E (t : T →ₐ[R] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (i : Root) :
    liftU C t e f h hs (E C i) = e i :=
  Specs.LieNotes.Quantum.Presentation.liftU_E C t e f h hs i

@[simp] theorem liftU_F (t : T →ₐ[R] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (i : Root) :
    liftU C t e f h hs (F C i) = f i :=
  Specs.LieNotes.Quantum.Presentation.liftU_F C t e f h hs i

theorem basic_universal (t : T →ₐ[R] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) :
    ∃! g : B₀ C →ₐ[R] B,
      (∀ x, g (cartan₀ C x) = t x) ∧ (∀ i, g (E₀ C i) = e i) ∧
        (∀ i, g (F₀ C i) = f i) := by
  refine ⟨liftBasic C t e f h, ⟨liftBasic_cartan C t e f h, liftBasic_E C t e f h, liftBasic_F C t e f h⟩, ?_⟩
  rintro g ⟨ht, he, hf⟩
  exact basic_hom_ext C (fun x => (ht x).trans (liftBasic_cartan C t e f h x).symm)
    (fun i => (he i).trans (liftBasic_E C t e f h i).symm)
    (fun i => (hf i).trans (liftBasic_F C t e f h i).symm)

theorem universal (t : T →ₐ[R] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) :
    ∃! g : U C →ₐ[R] B,
      (∀ x, g (cartan C x) = t x) ∧ (∀ i, g (E C i) = e i) ∧
        (∀ i, g (F C i) = f i) := by
  refine ⟨liftU C t e f h hs, ⟨liftU_cartan C t e f h hs, liftU_E C t e f h hs, liftU_F C t e f h hs⟩, ?_⟩
  rintro g ⟨ht, he, hf⟩
  exact hom_ext C (fun x => (ht x).trans (liftU_cartan C t e f h hs x).symm)
    (fun i => (he i).trans (liftU_E C t e f h hs i).symm)
    (fun i => (hf i).trans (liftU_F C t e f h hs i).symm)

theorem ringHom_ext {B : Type w} [Ring B] {f g : U C →+* B}
    (ha : ∀ a, f (algebraMap R (U C) a) = g (algebraMap R (U C) a))
    (ht : ∀ x, f (cartan C x) = g (cartan C x))
    (he : ∀ i, f (E C i) = g (E C i))
    (hf : ∀ i, f (F C i) = g (F C i)) : f = g := by
  apply RingHom.ext
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (serreIdeal C).asIdeal x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R (basicIdeal C).asIdeal b
  change f (serreQuotient C (basicQuotient C a)) = g (serreQuotient C (basicQuotient C a))
  induction a using FreeAlgebra.induction with
  | grade0 r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact ha r
  | grade1 x =>
    rcases x with t | (i | i)
    · exact ht t
    · exact he i
    · exact hf i
  | mul a b fa fb => simp only [map_mul, fa, fb]
  | add a b fa fb => simp only [map_add, fa, fb]

end Presentation

section Reduction

variable {k : Type u} [Field k] [CharZero k] {L M N : ℕ}

abbrev cartanReduce := @Specs.LieNotes.Quantum.Presentation.cartanReduce
abbrev reduce := @Specs.LieNotes.Quantum.Presentation.reduce

theorem cartanReduce_tau (e : M ≤ N) (i : Root) (t : TruncatedCartan k N) :
    cartanReduce e (((truncated k N).tau i).symm t) =
      ((truncated k M).tau i).symm (cartanReduce e t) :=
  Specs.LieNotes.Quantum.Presentation.cartanReduce_tau e i t

@[simp] theorem truncatedQ_reduce (e : M ≤ N) :
    Units.map (Truncations.reduce (R := k) e).toRingHom.toMonoidHom ((truncated k N).q) =
      (truncated k M).q :=
  Specs.LieNotes.Quantum.Presentation.truncatedQ_reduce e


@[simp] theorem reduce_cartan (e : M ≤ N) (t : TruncatedCartan k N) :
    reduce e (cartan (truncated k N) t) = cartan (truncated k M) (cartanReduce e t) :=
  Specs.LieNotes.Quantum.Presentation.reduce_cartan e t

@[simp] theorem reduce_E (e : M ≤ N) (i : Root) :
    reduce e (E (truncated k N) i) = E (truncated k M) i :=
  Specs.LieNotes.Quantum.Presentation.reduce_E e i

@[simp] theorem reduce_F (e : M ≤ N) (i : Root) :
    reduce e (F (truncated k N) i) = F (truncated k M) i :=
  Specs.LieNotes.Quantum.Presentation.reduce_F e i

@[simp] theorem reduce_scalar (e : M ≤ N) (a : A k N) :
    reduce e (algebraMap (A k N) (Uₙ k N) a) =
      algebraMap (A k M) (Uₙ k M) (Truncations.reduce e a) :=
  Specs.LieNotes.Quantum.Presentation.reduce_scalar e a

@[simp] theorem reduce_H (e : M ≤ N) (i : Root) :
    reduce e (cartan (truncated k N) (MvPolynomial.X i)) =
      cartan (truncated k M) (MvPolynomial.X i) := by
  rw [reduce_cartan]
  exact congrArg (cartan (truncated k M)) (MvPolynomial.map_X _ _)

@[simp] theorem reduce_K (e : M ≤ N) (i : Root) :
    reduce e (cartan (truncated k N) ((truncated k N).K i : TruncatedCartan k N)) =
      cartan (truncated k M) ((truncated k M).K i : TruncatedCartan k M) := by
  rw [reduce_cartan, cartanReduce_K]

@[simp] theorem reduce_D (e : M ≤ N) (i : Root) :
    reduce e (cartan (truncated k N) ((truncated k N).D i)) =
      cartan (truncated k M) ((truncated k M).D i) := by
  rw [reduce_cartan, cartanReduce_D]

@[simp] theorem reduce_refl (N : ℕ) :
    reduce (k := k) (le_refl N) = RingHom.id (Uₙ k N) := by
  have h : (Truncations.reduce (R := k) (le_refl N)).toRingHom = RingHom.id (A k N) :=
    congrArg AlgHom.toRingHom (Truncations.reduce_refl N)
  apply ringHom_ext (truncated k N)
  · intro a
    rw [reduce_scalar]
    exact congrArg (algebraMap (A k N) (Uₙ k N)) (DFunLike.congr_fun h a)
  · intro t
    rw [reduce_cartan]
    change cartan (truncated k N) (MvPolynomial.map _ t) = _
    rw [h, MvPolynomial.map_id]
    rfl
  · exact reduce_E _
  · exact reduce_F _

theorem reduce_comp (d : L ≤ M) (e : M ≤ N) :
    (reduce (k := k) d).comp (reduce e) = reduce (d.trans e) := by
  have h : (Truncations.reduce (R := k) d).toRingHom.comp (Truncations.reduce e).toRingHom =
      (Truncations.reduce (d.trans e)).toRingHom :=
    congrArg AlgHom.toRingHom (Truncations.reduce_comp e d)
  apply ringHom_ext (truncated k N)
  · intro a
    simp only [RingHom.comp_apply, reduce_scalar]
    exact congrArg (algebraMap (A k L) (Uₙ k L)) (DFunLike.congr_fun h a)
  · intro t
    simp only [RingHom.comp_apply, reduce_cartan, cartanReduce, MvPolynomial.map_map, h]
  · intro i
    simp
  · intro i
    simp

end Reduction

end LieNotes.Quantum.Presentation
