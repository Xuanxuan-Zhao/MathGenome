import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerrePresentation
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Truncations
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

noncomputable section

namespace Specs.LieNotes.Quantum.Presentation

universe u v w

abbrev Root := Fin 2

def cartanMatrix (l i : Root) : ℤ := if l = i then 2 else -1

/-- The coefficient ring and Cartan algebra are explicit parameters. -/
structure Cartan (A : Type u) (T : Type v) [CommRing A] [CommRing T] [Algebra A T] where
  q : Aˣ
  K : Root → Tˣ
  tau : Root → T ≃ₐ[A] T
  D : Root → T
  kappa : T ≃ₐ[A] T

section Laurent

abbrev Lattice := Root → ℤ

abbrev Laurent (A : Type u) [CommRing A] := AddMonoidAlgebra A Lattice

def coordinate (l : Root) : Lattice := fun i => if i = l then 1 else 0

variable {A : Type u} [CommRing A]

def laurentUnit (m : Lattice) : (Laurent A)ˣ where
  val := AddMonoidAlgebra.single m 1
  inv := AddMonoidAlgebra.single (-m) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one, ← AddMonoidAlgebra.one_def]
  inv_val := by rw [AddMonoidAlgebra.single_mul_single, neg_add_cancel, mul_one, ← AddMonoidAlgebra.one_def]

def laurentBasis (A : Type u) [CommRing A] : Module.Basis Lattice A (Laurent A) :=
  AddMonoidAlgebra.basis Lattice A

def pairing (i : Root) (m : Lattice) : ℤ := ∑ l, cartanMatrix l i * m l

theorem pairing_add (i : Root) (m n : Lattice) :
    pairing i (m + n) = pairing i m + pairing i n := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

def laurentScale (q : Aˣ) (i : Root) : Laurent A →ₐ[A] Laurent A :=
  AddMonoidAlgebra.lift A (Laurent A) Lattice {
    toFun := fun m => (↑(q ^ pairing i m.toAdd) : A) •
      AddMonoidAlgebra.single m.toAdd 1
    map_one' := by simp [pairing, ← AddMonoidAlgebra.one_def]
    map_mul' := by
      intro m n
      change (↑(q ^ pairing i (m.toAdd + n.toAdd)) : A) •
        AddMonoidAlgebra.single (m.toAdd + n.toAdd) 1 = _
      simp only [pairing_add, zpow_add, Units.val_mul, Algebra.smul_mul_assoc,
        Algebra.mul_smul_comm, AddMonoidAlgebra.single_mul_single, mul_one]
      rw [mul_smul, smul_comm]
  }

theorem laurent_ext {B : Type w} [Semiring B] [Algebra A B]
    {f g : Laurent A →ₐ[A] B}
    (h : ∀ m : Lattice, f (AddMonoidAlgebra.single m 1) = g (AddMonoidAlgebra.single m 1)) :
    f = g := by
  apply (AddMonoidAlgebra.lift A B Lattice).symm.injective
  ext m
  exact h m

@[simp] theorem laurentScale_single (q : Aˣ) (i : Root) (m : Lattice) :
    laurentScale q i (AddMonoidAlgebra.single m 1) =
      (↑(q ^ pairing i m) : A) • AddMonoidAlgebra.single m 1 := by
  simp [laurentScale]

theorem laurentScale_cancel (q : Aˣ) (i : Root) :
    (laurentScale q i).comp (laurentScale q⁻¹ i) = AlgHom.id A (Laurent A) := by
  apply laurent_ext
  intro m
  rw [AlgHom.comp_apply, laurentScale_single, map_smul, laurentScale_single, ← mul_smul,
    ← Units.val_mul, inv_zpow, inv_mul_cancel, Units.val_one, one_smul]
  rfl

def laurentTau (q : Aˣ) (i : Root) : Laurent A ≃ₐ[A] Laurent A :=
  AlgEquiv.ofAlgHom (laurentScale q i) (laurentScale q⁻¹ i)
    (laurentScale_cancel q i) (by simpa using laurentScale_cancel q⁻¹ i)

def laurentKappa (A : Type u) [CommRing A] : Laurent A ≃ₐ[A] Laurent A :=
  AddMonoidAlgebra.domCongr A A (AddEquiv.neg Lattice)

variable {k : Type u} [Field k] [CharZero k]

def genericD (q : kˣ) (i : Root) : Laurent k :=
  ((↑q - ↑(q⁻¹) : k)⁻¹) •
    ((laurentUnit (A := k) (coordinate i) : Laurent k) -
      ↑((laurentUnit (A := k) (coordinate i))⁻¹))

def generic (q : kˣ) (_hq : (q : k)^2 ≠ 1) : Cartan k (Laurent k) where
  q := q
  K l := laurentUnit (coordinate l)
  tau := laurentTau q
  D := genericD q
  kappa := laurentKappa k

def rationalQ (k : Type u) [Field k] : (RatFunc k)ˣ :=
  Units.mk0 RatFunc.X RatFunc.X_ne_zero

theorem rationalQ_sq_ne (k : Type u) [Field k] : (rationalQ k : RatFunc k)^2 ≠ 1 := by
  intro h
  have hp : (Polynomial.X : Polynomial k)^2 = 1 := by
    apply RatFunc.algebraMap_injective
    change (algebraMap (Polynomial k) (RatFunc k) Polynomial.X)^2 = 1 at h
    simpa only [map_pow, map_one] using h
  have hcoeff := congrArg (fun p : Polynomial k => p.coeff 2) hp
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one] at hcoeff

def indeterminate (k : Type u) [Field k] [CharZero k] :
    Cartan (RatFunc k) (Laurent (RatFunc k)) :=
  generic (rationalQ k) (rationalQ_sq_ne k)

end Laurent

section Polynomial

abbrev PolynomialCartan (A : Type u) [CommRing A] := MvPolynomial Root A

variable {A : Type u} [CommRing A]

def translate (b : Root → A) : PolynomialCartan A →ₐ[A] PolynomialCartan A :=
  MvPolynomial.aeval (fun l => MvPolynomial.X l + MvPolynomial.C (b l))

theorem translate_cancel (b : Root → A) :
    (translate b).comp (translate (-b)) = AlgHom.id A (PolynomialCartan A) := by
  ext l
  simp [translate]

def translation (b : Root → A) : PolynomialCartan A ≃ₐ[A] PolynomialCartan A :=
  AlgEquiv.ofAlgHom (translate b) (translate (-b))
    (translate_cancel b) (by simpa using translate_cancel (-b))

@[simp] theorem translation_symm_X  (b : Root → A) (l : Root) :
    (translation b).symm (MvPolynomial.X l) = MvPolynomial.X l - MvPolynomial.C (b l) := by
  change MvPolynomial.aeval _ (MvPolynomial.X _) = _
  simp [sub_eq_add_neg]

def negateCartan : PolynomialCartan A →ₐ[A] PolynomialCartan A :=
  MvPolynomial.aeval (fun l => -(MvPolynomial.X l))

def polynomialKappa (A : Type u) [CommRing A] : PolynomialCartan A ≃ₐ[A] PolynomialCartan A :=
  AlgEquiv.ofAlgHom negateCartan negateCartan (by ext l; simp [negateCartan])
    (by ext l; simp [negateCartan])

def polynomialBasis (A : Type u) [CommRing A] :
    Module.Basis (Root → ℕ) A (PolynomialCartan A) :=
  (MvPolynomial.basisMonomials Root A).reindex Finsupp.equivFunOnFinite

variable {S : Type u} [CommRing S] [Algebra ℚ S]

open Specs.LieNotes.Quantum.Truncations (expH)

/-- The divided hyperbolic sine is defined by the one-place shift in h-degree. -/
def dividedSinh (a : S) : PowerSeries S :=
  PowerSeries.mk fun n => algebraMap ℚ S (1 / 2) *
    (PowerSeries.coeff (n + 1) (expH a) - PowerSeries.coeff (n + 1) (expH (-a)))

theorem dividedSinh_const (a : S) : PowerSeries.constantCoeff (dividedSinh a) = a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [dividedSinh, PowerSeries.coeff_mk, zero_add, expH, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp, pow_one, Nat.factorial_one, Nat.cast_one, div_one, map_one, mul_one,
    sub_neg_eq_add]
  rw [← two_mul, ← mul_assoc]
  have hh : algebraMap ℚ S (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap ℚ S) 2, ← map_mul]
    norm_num
  rw [hh, one_mul]

def sinhDenominator (S : Type u) [CommRing S] [Algebra ℚ S] : (PowerSeries S)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr
    (by rw [dividedSinh_const]; exact isUnit_one : IsUnit (PowerSeries.constantCoeff (dividedSinh (1 : S))))).unit

def sinhRatio (a : S) : PowerSeries S :=
  dividedSinh a * (↑((sinhDenominator S)⁻¹) : PowerSeries S)

def exponentialUnit (a : S) : (PowerSeries S)ˣ :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr
    (by simp [expH, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale] :
      IsUnit (PowerSeries.constantCoeff (expH a)))).unit

open Specs.LieNotes.Quantum.Truncations (truncate cartanTruncate)

variable (k : Type u) [Field k] [CharZero k]

abbrev TruncatedCartan (N : ℕ) := PolynomialCartan (Truncations.A k N)

def truncatedQ (N : ℕ) : (Truncations.A k N)ˣ :=
  Units.map (truncate (R := k) N).toRingHom.toMonoidHom (exponentialUnit (1 : k))

def truncatedK (N : ℕ) (i : Root) : (TruncatedCartan k N)ˣ :=
  Units.map (cartanTruncate (R := k) Root N).toMonoidHom
    (exponentialUnit (MvPolynomial.X i : PolynomialCartan k))

def truncatedD (N : ℕ) (i : Root) : TruncatedCartan k N :=
  cartanTruncate Root N (sinhRatio (MvPolynomial.X i : PolynomialCartan k))

def truncated (N : ℕ) : Cartan (Truncations.A k N) (TruncatedCartan k N) where
  q := truncatedQ k N
  K := truncatedK k N
  tau i := translation (fun l => (cartanMatrix l i : Truncations.A k N))
  D := truncatedD k N
  kappa := polynomialKappa _

end Polynomial

section Presentation

variable {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]

abbrev Letters (T : Type v) := T ⊕ (Root ⊕ Root)

abbrev Raw (A : Type u) [CommRing A] (T : Type v) := FreeAlgebra A (Letters T)

def rawCartan (t : T) : Raw A T := FreeAlgebra.ι A (.inl t)
def rawE (i : Root) : Raw A T := FreeAlgebra.ι A (.inr (.inl i))
def rawF (i : Root) : Raw A T := FreeAlgebra.ι A (.inr (.inr i))

def mixed (C : Cartan A T) (i j : Root) : T := if i = j then C.D i else 0

/-- The additive, multiplicative, and scalar relations force the Cartan letters to
come from an algebra homomorphism. The other relations are the basic relations. -/
inductive BasicRelation (C : Cartan A T) : Raw A T → Prop
  | add (s t : T) : BasicRelation C (rawCartan (s + t) - (rawCartan s + rawCartan t))
  | mul (s t : T) : BasicRelation C (rawCartan (s * t) - rawCartan s * rawCartan t)
  | scalar (a : A) : BasicRelation C (rawCartan (algebraMap A T a) - algebraMap A (Raw A T) a)
  | cartanF (t : T) (j : Root) :
      BasicRelation C (rawCartan t * rawF j - rawF j * rawCartan ((C.tau j).symm t))
  | eCartan (i : Root) (t : T) :
      BasicRelation C (rawE i * rawCartan t - rawCartan ((C.tau i).symm t) * rawE i)
  | comm (i j : Root) :
      BasicRelation C (rawE i * rawF j - rawF j * rawE i - rawCartan (mixed C i j))

def basicIdeal (C : Cartan A T) : TwoSidedIdeal (Raw A T) :=
  TwoSidedIdeal.span {r | BasicRelation C r}

abbrev B₀ (C : Cartan A T) := Raw A T ⧸ (basicIdeal C).asIdeal

def basicQuotient (C : Cartan A T) : Raw A T →ₐ[A] B₀ C :=
  Ideal.Quotient.mkₐ A (basicIdeal C).asIdeal

theorem basic_eq_zero (C : Cartan A T) {r : Raw A T} (hr : BasicRelation C r) :
    basicQuotient C r = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr
    (TwoSidedIdeal.subset_span hr))

def cartan₀ (C : Cartan A T) : T →ₐ[A] B₀ C where
  toFun t := basicQuotient C (rawCartan t)
  map_add' s t := by
    exact sub_eq_zero.mp (by simpa only [map_sub, map_add] using basic_eq_zero C (.add s t))
  map_mul' s t := by
    exact sub_eq_zero.mp (by simpa only [map_sub, map_mul] using basic_eq_zero C (.mul s t))
  map_zero' := sub_eq_zero.mp (by simpa using basic_eq_zero C (.scalar 0))
  map_one' := sub_eq_zero.mp (by simpa using basic_eq_zero C (.scalar 1))
  commutes' a := by
    exact sub_eq_zero.mp (by simpa only [map_sub, AlgHom.commutes] using basic_eq_zero C (.scalar a))

def E₀ (C : Cartan A T) (i : Root) : B₀ C := basicQuotient C (rawE i)
def F₀ (C : Cartan A T) (i : Root) : B₀ C := basicQuotient C (rawF i)

open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)

def serreIdeal (C : Cartan A T) : TwoSidedIdeal (B₀ C) :=
  TwoSidedIdeal.span {r | ∃ i j : Root, i ≠ j ∧
    (r = serrePolynomial C.q (E₀ C i) (E₀ C j) ∨
     r = serrePolynomial C.q (F₀ C i) (F₀ C j))}

abbrev U (C : Cartan A T) := B₀ C ⧸ (serreIdeal C).asIdeal

def serreQuotient (C : Cartan A T) : B₀ C →ₐ[A] U C :=
  Ideal.Quotient.mkₐ A (serreIdeal C).asIdeal

def cartan (C : Cartan A T) : T →ₐ[A] U C := (serreQuotient C).comp (cartan₀ C)
def E (C : Cartan A T) (i : Root) : U C := serreQuotient C (E₀ C i)
def F (C : Cartan A T) (i : Root) : U C := serreQuotient C (F₀ C i)

abbrev Uₙ (k : Type u) [Field k] [CharZero k] (N : ℕ) := U (truncated k N)

section Universal

variable {B : Type w} [Ring B] [Algebra A B]

/-- The basic relations evaluated at a candidate Cartan algebra map and root letters. -/
structure SatisfiesBasic (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B) : Prop where
  cartanF : ∀ x j, t x * f j = f j * t ((C.tau j).symm x)
  eCartan : ∀ i x, e i * t x = t ((C.tau i).symm x) * e i
  comm : ∀ i j, e i * f j - f j * e i = t (mixed C i j)

def assign (t : T →ₐ[A] B) (e f : Root → B) : Letters T → B :=
  Sum.elim t (Sum.elim e f)

def liftBasic (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) : B₀ C →ₐ[A] B :=
  Ideal.Quotient.liftₐ (basicIdeal C).asIdeal (FreeAlgebra.lift A (assign t e f)) (by
    intro r hr
    have hker : basicIdeal C ≤ TwoSidedIdeal.ker (FreeAlgebra.lift A (assign t e f)).toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      intro x hx
      change x ∈ TwoSidedIdeal.ker (FreeAlgebra.lift A (assign t e f)).toRingHom
      apply (TwoSidedIdeal.mem_ker _).mpr
      change BasicRelation C x at hx
      cases hx <;>
        simp [rawCartan, rawE, rawF, assign, h.cartanF, h.eCartan, h.comm]
    exact (TwoSidedIdeal.mem_ker _).mp (hker (TwoSidedIdeal.mem_asIdeal.mp hr)))

structure SatisfiesSerre (q : Aˣ) (e f : Root → B) : Prop where
  pos : ∀ i j, i ≠ j → serrePolynomial q (e i) (e j) = 0
  neg : ∀ i j, i ≠ j → serrePolynomial q (f i) (f j) = 0

@[simp] theorem liftBasic_cartan (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (x : T) : liftBasic C t e f h (cartan₀ C x) = t x := by
  change liftBasic C t e f h (basicQuotient C (FreeAlgebra.ι A (.inl x))) = _
  exact FreeAlgebra.lift_ι_apply (assign t e f) (.inl x)

@[simp] theorem liftBasic_E (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (i : Root) : liftBasic C t e f h (E₀ C i) = e i := by
  exact FreeAlgebra.lift_ι_apply (assign t e f) (.inr (.inl i))

@[simp] theorem liftBasic_F (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (i : Root) : liftBasic C t e f h (F₀ C i) = f i := by
  exact FreeAlgebra.lift_ι_apply (assign t e f) (.inr (.inr i))

def liftU (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) : U C →ₐ[A] B :=
  Ideal.Quotient.liftₐ (serreIdeal C).asIdeal (liftBasic C t e f h) (by
    intro r hr
    have hker : serreIdeal C ≤ TwoSidedIdeal.ker (liftBasic C t e f h).toRingHom := by
      apply TwoSidedIdeal.span_le.mpr
      intro x hx
      change x ∈ TwoSidedIdeal.ker (liftBasic C t e f h).toRingHom
      apply (TwoSidedIdeal.mem_ker _).mpr
      obtain ⟨i, j, hij, rfl | rfl⟩ := hx
      · simpa [serrePolynomial] using hs.pos i j hij
      · simpa [serrePolynomial] using hs.neg i j hij
    exact (TwoSidedIdeal.mem_ker _).mp (hker (TwoSidedIdeal.mem_asIdeal.mp hr)))

@[simp] theorem liftU_cartan (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (x : T) :
    liftU C t e f h hs (cartan C x) = t x :=
  liftBasic_cartan C t e f h x

@[simp] theorem liftU_E (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (i : Root) :
    liftU C t e f h hs (E C i) = e i :=
  liftBasic_E C t e f h i

@[simp] theorem liftU_F (C : Cartan A T) (t : T →ₐ[A] B) (e f : Root → B)
    (h : SatisfiesBasic C t e f) (hs : SatisfiesSerre C.q e f) (i : Root) :
    liftU C t e f h hs (F C i) = f i :=
  liftBasic_F C t e f h i


end Universal

theorem basic_relations (C : Cartan A T) : SatisfiesBasic C (cartan₀ C) (E₀ C) (F₀ C) where
  cartanF x j := sub_eq_zero.mp (by
    simpa only [map_sub, map_mul, Specs.LieNotes.Quantum.Presentation.cartan₀,
      Specs.LieNotes.Quantum.Presentation.E₀, Specs.LieNotes.Quantum.Presentation.F₀,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using basic_eq_zero C (.cartanF x j))
  eCartan i x := sub_eq_zero.mp (by
    simpa only [map_sub, map_mul, Specs.LieNotes.Quantum.Presentation.cartan₀,
      Specs.LieNotes.Quantum.Presentation.E₀, Specs.LieNotes.Quantum.Presentation.F₀,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using basic_eq_zero C (.eCartan i x))
  comm i j := sub_eq_zero.mp (by
    simpa only [map_sub, map_mul, Specs.LieNotes.Quantum.Presentation.cartan₀,
      Specs.LieNotes.Quantum.Presentation.E₀, Specs.LieNotes.Quantum.Presentation.F₀,
      AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using basic_eq_zero C (.comm i j))

theorem relations (C : Cartan A T) : SatisfiesBasic C (cartan C) (E C) (F C) where
  cartanF x j := by
    simpa only [map_mul, Specs.LieNotes.Quantum.Presentation.cartan, AlgHom.comp_apply,
      Specs.LieNotes.Quantum.Presentation.E, Specs.LieNotes.Quantum.Presentation.F] using congrArg (serreQuotient C) ((basic_relations C).cartanF x j)
  eCartan i x := by
    simpa only [map_mul, Specs.LieNotes.Quantum.Presentation.cartan, AlgHom.comp_apply,
      Specs.LieNotes.Quantum.Presentation.E, Specs.LieNotes.Quantum.Presentation.F] using congrArg (serreQuotient C) ((basic_relations C).eCartan i x)
  comm i j := by
    simpa only [map_mul, map_sub, Specs.LieNotes.Quantum.Presentation.cartan, AlgHom.comp_apply,
      Specs.LieNotes.Quantum.Presentation.E, Specs.LieNotes.Quantum.Presentation.F] using congrArg (serreQuotient C) ((basic_relations C).comm i j)

theorem serre_relations (C : Cartan A T) : SatisfiesSerre C.q (E C) (F C) where
  pos i j hij := by
    change serrePolynomial C.q (serreQuotient C (E₀ C i)) (serreQuotient C (E₀ C j)) = 0
    rw [show serrePolynomial C.q (serreQuotient C (E₀ C i)) (serreQuotient C (E₀ C j)) =
      serreQuotient C (serrePolynomial C.q (E₀ C i) (E₀ C j)) by
        simp only [serrePolynomial, map_add, map_sub, map_mul, map_pow, map_smul]]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (show ∃ i' j' : Root, i' ≠ j' ∧ _ from
        ⟨i, j, hij, Or.inl rfl⟩)))
  neg i j hij := by
    change serrePolynomial C.q (serreQuotient C (F₀ C i)) (serreQuotient C (F₀ C j)) = 0
    rw [show serrePolynomial C.q (serreQuotient C (F₀ C i)) (serreQuotient C (F₀ C j)) =
      serreQuotient C (serrePolynomial C.q (F₀ C i) (F₀ C j)) by
        simp only [serrePolynomial, map_add, map_sub, map_mul, map_pow, map_smul]]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (show ∃ i' j' : Root, i' ≠ j' ∧ _ from
        ⟨i, j, hij, Or.inr rfl⟩)))


end Presentation

section Reduction
set_option linter.style.haveILetI false

open Truncations (A truncate cartanTruncate)
open Specs.LieNotes.Quantum.SerrePresentation (serrePolynomial)

variable {k : Type u} [Field k] [CharZero k] {L M N : ℕ}

abbrev cartanReduce (e : M ≤ N) : TruncatedCartan k N →+* TruncatedCartan k M :=
  MvPolynomial.map (Truncations.reduce (R := k) e).toRingHom

open private mk_trunc_coe from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.Truncations

private theorem truncate_natural {R : Type u} [CommRing R] (e : M ≤ N) (p : PowerSeries R) :
    Truncations.reduce e (truncate N p) = truncate M p := by
  change Truncations.mk R M (PowerSeries.trunc N p) = Truncations.mk R M (PowerSeries.trunc M p)
  rw [← PowerSeries.trunc_trunc_of_le p e]
  exact (mk_trunc_coe M (PowerSeries.trunc N p)).symm

omit [CharZero k] in
private theorem cartanTruncate_natural (e : M ≤ N) (p : PowerSeries (PolynomialCartan k)) :
    cartanReduce e (cartanTruncate Root N p) = cartanTruncate Root M p := by
  let ev (n : ℕ) := Polynomial.eval₂RingHom
    (MvPolynomial.map (σ := Root) (algebraMap k (Truncations.A k n)))
    (MvPolynomial.C (Truncations.h k n))
  let r := (Truncations.reduce (R := k) e).toRingHom
  have hcoeff : (cartanReduce e).comp (MvPolynomial.map (σ := Root) (algebraMap k (A k N))) =
      MvPolynomial.map (algebraMap k (A k M)) := by
    have hbase : r.comp (algebraMap k (A k N)) = algebraMap k (A k M) :=
      RingHom.ext fun a => (Truncations.reduce e).commutes a
    apply RingHom.ext
    intro x
    simp only [RingHom.comp_apply, cartanReduce, MvPolynomial.map_map]
    exact congrArg (fun h => MvPolynomial.map h x) hbase
  have hparam : cartanReduce e (MvPolynomial.C (Truncations.h k N)) =
      (MvPolynomial.C (σ := Root)) (Truncations.h k M) :=
    MvPolynomial.map_C _ _
  change cartanReduce e ((PowerSeries.trunc N p).eval₂
    (MvPolynomial.map (algebraMap k (A k N))) (MvPolynomial.C (Truncations.h k N))) =
      ev M (PowerSeries.trunc M p)
  rw [Polynomial.hom_eval₂, hcoeff, hparam]
  have he (q : Polynomial (PolynomialCartan k)) : cartanTruncate Root M (q : PowerSeries _) = ev M q := by
    unfold Truncations.cartanTruncate Truncations.evalTrunc
    rw [RingHom.comp_apply]
    have hq : (truncate M).toRingHom (q : PowerSeries _) = Truncations.mk _ M q :=
      mk_trunc_coe M q
    rw [hq]
    rfl
  have h := he (PowerSeries.trunc N p)
  change ev M (PowerSeries.trunc M ((PowerSeries.trunc N p : Polynomial _) : PowerSeries _)) =
    ev M (PowerSeries.trunc N p) at h
  rw [PowerSeries.trunc_trunc_of_le p e] at h
  exact h.symm

theorem cartanReduce_tau (e : M ≤ N) (i : Root) (t : TruncatedCartan k N) :
    cartanReduce e (((truncated k N).tau i).symm t) =
      ((truncated k M).tau i).symm (cartanReduce e t) := by
  induction t using MvPolynomial.induction_on with
  | C a =>
    have hN : ((truncated k N).tau i).symm (MvPolynomial.C a) = MvPolynomial.C a :=
      ((truncated k N).tau i).symm.commutes a
    have hM : ((truncated k M).tau i).symm (MvPolynomial.C (Truncations.reduce e a)) = _ :=
      ((truncated k M).tau i).symm.commutes _
    rw [hN, MvPolynomial.map_C]
    exact hM.symm
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p l hp =>
    have hx : cartanReduce e (((truncated k N).tau i).symm (MvPolynomial.X l)) =
        ((truncated k M).tau i).symm (cartanReduce e (MvPolynomial.X l)) := by
      change cartanReduce e ((translation (fun j => (cartanMatrix j i : A k N))).symm
        (MvPolynomial.X l)) = (translation (fun j => (cartanMatrix j i : A k M))).symm
        (cartanReduce e (MvPolynomial.X l))
      simp only [translation_symm_X, map_sub, MvPolynomial.map_X, map_intCast]
    simp only [map_mul, hp, hx]

@[simp] theorem cartanReduce_D (e : M ≤ N) (i : Root) :
    cartanReduce e ((truncated k N).D i) = (truncated k M).D i :=
  cartanTruncate_natural e _

@[simp] theorem cartanReduce_K (e : M ≤ N) (i : Root) :
    cartanReduce e ((truncated k N).K i : TruncatedCartan k N) =
      ((truncated k M).K i : TruncatedCartan k M) :=
  cartanTruncate_natural e _

@[simp] theorem truncatedQ_reduce (e : M ≤ N) :
    Units.map (Truncations.reduce (R := k) e).toRingHom.toMonoidHom ((truncated k N).q) =
      (truncated k M).q := by
  apply Units.ext
  exact truncate_natural e (Units.val (exponentialUnit (1 : k)))

private abbrev reductionAlgebra (e : M ≤ N) : Algebra (A k N) (Uₙ k M) :=
  Algebra.compHom (Uₙ k M) (Truncations.reduce (R := k) e).toRingHom

private def reductionCartan (e : M ≤ N) :
    letI := reductionAlgebra (k := k) e
    TruncatedCartan k N →ₐ[A k N] Uₙ k M :=
  letI := reductionAlgebra (k := k) e
  { (cartan (truncated k M)).toRingHom.comp (cartanReduce e) with
    commutes' := fun a => by
      change cartan (truncated k M) (cartanReduce e (MvPolynomial.C a)) = _
      rw [MvPolynomial.map_C]
      exact (cartan (truncated k M)).commutes (Truncations.reduce e a) }

private theorem reductionBasic (e : M ≤ N) :
    letI := reductionAlgebra (k := k) e
    SatisfiesBasic (truncated k N) (reductionCartan e)
      (E (truncated k M)) (F (truncated k M)) := by
  letI := reductionAlgebra (k := k) e
  let C := truncated k M
  refine ⟨?_, ?_, ?_⟩
  · intro t j
    change cartan C (cartanReduce e t) * F C j =
      F C j * cartan C (cartanReduce e (((truncated k N).tau j).symm t))
    rw [cartanReduce_tau]
    exact (relations C).cartanF _ _
  · intro i t
    change E C i * cartan C (cartanReduce e t) =
      cartan C (cartanReduce e (((truncated k N).tau i).symm t)) * E C i
    rw [cartanReduce_tau]
    exact (relations C).eCartan _ _
  · intro i j
    change E C i * F C j - F C j * E C i =
      cartan C (cartanReduce e (mixed (truncated k N) i j))
    have hm : cartanReduce e (mixed (truncated k N) i j) = mixed C i j := by
      by_cases h : i = j <;> simp [Specs.LieNotes.Quantum.Presentation.mixed, C, h]
    rw [hm]
    exact (relations C).comm _ _

private theorem reductionSerre (e : M ≤ N) :
    letI := reductionAlgebra (k := k) e
    SatisfiesSerre (truncated k N).q (E (truncated k M)) (F (truncated k M)) := by
  letI := reductionAlgebra (k := k) e
  let C := truncated k M
  let r := (Truncations.reduce (R := k) e).toRingHom
  let qN := (truncated k N).q
  have hq : Units.map r.toMonoidHom qN = C.q := truncatedQ_reduce e
  have hqv : r qN.val = C.q.val := congrArg Units.val hq
  have hiv : r (qN⁻¹).val = (C.q⁻¹).val := by
    change (Units.map r.toMonoidHom qN⁻¹).val = _
    rw [map_inv, hq]
  have he (x y : Uₙ k M) : serrePolynomial qN x y = serrePolynomial C.q x y := by
    change x ^ 2 * y - r (qN.val + (qN⁻¹).val) • (x * y * x) + y * x ^ 2 =
      x ^ 2 * y - (C.q.val + (C.q⁻¹).val) • (x * y * x) + y * x ^ 2
    rw [map_add, hqv, hiv]
  exact ⟨fun i j h => (he ..).trans ((serre_relations C).pos i j h),
    fun i j h => (he ..).trans ((serre_relations C).neg i j h)⟩

/-- The coefficientwise reduction, with its associated change of scalars. -/
def reduce (e : M ≤ N) : Uₙ k N →+* Uₙ k M :=
  letI := reductionAlgebra (k := k) e
  (liftU (truncated k N) (reductionCartan e) (E (truncated k M)) (F (truncated k M))
    (reductionBasic e) (reductionSerre e)).toRingHom

@[simp] theorem reduce_cartan (e : M ≤ N) (t : TruncatedCartan k N) :
    reduce e (cartan (truncated k N) t) = cartan (truncated k M) (cartanReduce e t) := by
  letI := reductionAlgebra (k := k) e
  exact liftU_cartan (truncated k N) (reductionCartan e) _ _ (reductionBasic e) (reductionSerre e) t

@[simp] theorem reduce_E (e : M ≤ N) (i : Root) :
    reduce e (E (truncated k N) i) = E (truncated k M) i := by
  letI := reductionAlgebra (k := k) e
  exact liftU_E (truncated k N) (reductionCartan e) _ _ (reductionBasic e) (reductionSerre e) i

@[simp] theorem reduce_F (e : M ≤ N) (i : Root) :
    reduce e (F (truncated k N) i) = F (truncated k M) i := by
  letI := reductionAlgebra (k := k) e
  exact liftU_F (truncated k N) (reductionCartan e) _ _ (reductionBasic e) (reductionSerre e) i

@[simp] theorem reduce_scalar (e : M ≤ N) (a : A k N) :
    reduce e (algebraMap (A k N) (Uₙ k N) a) =
      algebraMap (A k M) (Uₙ k M) (Truncations.reduce e a) := by
  letI := reductionAlgebra (k := k) e
  exact (liftU (truncated k N) (reductionCartan e) (E (truncated k M)) (F (truncated k M))
    (reductionBasic e) (reductionSerre e)).commutes a

end Reduction

section Bindings

set_option linter.checkUnivs false

abbrev cartanData := Cartan
abbrev basicPredicate := @SatisfiesBasic
abbrev serrePredicate := @SatisfiesSerre

def rationalQType := type_of% (@rationalQ)
def truncatedQType := type_of% (@truncatedQ)
def truncatedKType := type_of% (@truncatedK)
def truncatedDType := type_of% (@truncatedD)

def laurentBasis_applyProp : Prop :=
  ∀ (R : Type u) [CommRing R] (m : Root → ℤ),
    laurentBasis R m = AddMonoidAlgebra.single m 1

def polynomialBasis_applyProp : Prop :=
  ∀ (R : Type u) [CommRing R] (m : Root → ℕ),
    polynomialBasis R m = ∏ l : Root, (MvPolynomial.X l : PolynomialCartan R) ^ m l

def RootType := type_of% (@Root)
def CartanType := type_of% (@Cartan)
def cartanMatrixType := type_of% (@cartanMatrix)
def LaurentType := type_of% (@Laurent)
def laurentBasisType := type_of% (@laurentBasis)
def genericType := type_of% (@generic)
def indeterminateType := type_of% (@indeterminate)
def PolynomialCartanType := type_of% (@PolynomialCartan)
def polynomialBasisType := type_of% (@polynomialBasis)
def TruncatedCartanType := type_of% (@TruncatedCartan)
def truncatedType := type_of% (@truncated)
def dividedSinhType := type_of% (@dividedSinh)
def sinhRatioType := type_of% (@sinhRatio)
def B₀Type := type_of% (@B₀)
def UType := type_of% (@U)
def UₙType := type_of% (@Uₙ)
def basicIdealType := type_of% (@basicIdeal)
def basicQuotientType := type_of% (@basicQuotient)
def serreIdealType := type_of% (@serreIdeal)
def serreQuotientType := type_of% (@serreQuotient)
def cartan₀Type := type_of% (@cartan₀)
def E₀Type := type_of% (@E₀)
def F₀Type := type_of% (@F₀)
def cartanType := type_of% (@cartan)
def EType := type_of% (@E)
def FType := type_of% (@F)
def mixedType := type_of% (@mixed)
def SatisfiesBasicType := type_of% (@SatisfiesBasic)
def SatisfiesSerreType := type_of% (@SatisfiesSerre)
def liftBasicType := type_of% (@liftBasic)
def liftUType := type_of% (@liftU)
def cartanReduceType := type_of% (@cartanReduce)
def reduceType := type_of% (@reduce)

def generic_denominator_ne_zeroProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (_hq : (q : k)^2 ≠ 1),
    (↑q - ↑(q⁻¹) : k) ≠ 0

def generic_scaleProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1), ∀ i l : Root,
    (generic q hq).tau i ((generic q hq).K l : Laurent k) =
      (↑(q ^ cartanMatrix l i) : k) • ((generic q hq).K l : Laurent k)

def generic_commuteProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1), ∀ i j : Root,
    Function.Commute ((generic q hq).tau i) ((generic q hq).tau j)

def generic_kappa_KProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1), ∀ l : Root,
    (generic q hq).kappa ((generic q hq).K l : Laurent k) = ↑((generic q hq).K l)⁻¹

def generic_kappa_involutiveProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1),
    Function.Involutive (generic q hq).kappa

def generic_kappa_tauProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1), ∀ (i : Root) (t : Laurent k),
    (generic q hq).kappa ((generic q hq).tau i t) =
      ((generic q hq).tau i).symm ((generic q hq).kappa t)

def generic_kappa_DProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (q : kˣ) (hq : (q : k)^2 ≠ 1), ∀ i : Root,
    (generic q hq).kappa ((generic q hq).D i) = -(generic q hq).D i

def truncated_tau_HProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ i l : Root,
    (truncated k N).tau i (MvPolynomial.X l) =
      MvPolynomial.X l + MvPolynomial.C (cartanMatrix l i : Truncations.A k N)

def truncated_kappa_HProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ l : Root,
    (truncated k N).kappa (MvPolynomial.X l) = -MvPolynomial.X l

def truncated_scaleProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ i l : Root,
    (truncated k N).tau i ((truncated k N).K l : TruncatedCartan k N) =
      (↑((truncated k N).q ^ cartanMatrix l i) : Truncations.A k N) •
        ((truncated k N).K l : TruncatedCartan k N)

def truncated_commuteProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ i j : Root,
    Function.Commute ((truncated k N).tau i) ((truncated k N).tau j)

def truncated_kappa_involutiveProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ),
    Function.Involutive (truncated k N).kappa

def truncated_kappa_tauProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ (i : Root) (t : TruncatedCartan k N),
    (truncated k N).kappa ((truncated k N).tau i t) =
      ((truncated k N).tau i).symm ((truncated k N).kappa t)

def truncated_kappa_DProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ), ∀ i : Root,
    (truncated k N).kappa ((truncated k N).D i) = -(truncated k N).D i

def basic_relationsProp : Prop :=
  ∀ {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T), SatisfiesBasic C (cartan₀ C) (E₀ C) (F₀ C)

def relationsProp : Prop :=
  ∀ {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T), SatisfiesBasic C (cartan C) (E C) (F C)

def serre_relationsProp : Prop :=
  ∀ {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T), SatisfiesSerre C.q (E C) (F C)

def basic_universalProp : Prop :=
  ∀ {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T) {B : Type w} [Ring B] [Algebra A B]
    (t : T →ₐ[A] B) (e f : Root → B),
    SatisfiesBasic C t e f →
    ∃! g : B₀ C →ₐ[A] B,
      (∀ x, g (cartan₀ C x) = t x) ∧ (∀ i, g (E₀ C i) = e i) ∧
        (∀ i, g (F₀ C i) = f i)

def universalProp : Prop :=
  ∀ {A : Type u} {T : Type v} [CommRing A] [CommRing T] [Algebra A T]
    (C : Cartan A T) {B : Type w} [Ring B] [Algebra A B]
    (t : T →ₐ[A] B) (e f : Root → B),
    SatisfiesBasic C t e f → SatisfiesSerre C.q e f →
    ∃! g : U C →ₐ[A] B,
      (∀ x, g (cartan C x) = t x) ∧ (∀ i, g (E C i) = e i) ∧
        (∀ i, g (F C i) = f i)

def reduce_cartanProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (e : M ≤ N) (t : TruncatedCartan k N),
    reduce e (cartan (truncated k N) t) = cartan (truncated k M) (cartanReduce e t)

def reduce_EProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (e : M ≤ N) (i : Root),
    reduce e (E (truncated k N) i) = E (truncated k M) i

def reduce_FProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (e : M ≤ N) (i : Root),
    reduce e (F (truncated k N) i) = F (truncated k M) i

def reduce_scalarProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {M N : ℕ} (e : M ≤ N) (a : Truncations.A k N),
    reduce e (algebraMap (Truncations.A k N) (Uₙ k N) a) =
      algebraMap (Truncations.A k M) (Uₙ k M) (Truncations.reduce e a)

def reduce_reflProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (N : ℕ),
    reduce (k := k) (le_refl N) = RingHom.id (Uₙ k N)

def reduce_compProp : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {L M N : ℕ} (d : L ≤ M) (e : M ≤ N),
    (reduce (k := k) d).comp (reduce e) = reduce (d.trans e)

end Bindings

end Specs.LieNotes.Quantum.Presentation
