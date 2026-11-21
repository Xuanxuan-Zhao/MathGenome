import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch02.QuadraticRootReduction
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch01.FactorizationValuations
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

namespace P203.Ch02
open P203Specs.Ch01 P203Specs.Ch02

/-- Square divisibility, including the zero square. -/
theorem prime_pow_dvd_square (p : ℕ) (hp : p.Prime) (k : ℕ) (x : ℤ) :
    (p : ℤ)^k ∣ x^2 ↔ (p : ℤ)^((k+1)/2) ∣ x := by
  by_cases hx : x = 0
  · simp [hx]
  have hv := (P203.Ch01.valuationFactorizationBridge p hp x hx).1
  rw [P203.Ch01.valuationPrimePowers p hp, P203.Ch01.valuationPrimePowers p hp]
  change (k : ℕ∞) ≤ emultiplicity (p : ℤ) (x^2) ↔ _
  rw [emultiplicity_pow (Nat.prime_iff_prime_int.mp hp)]
  change (k : ℕ∞) ≤ 2 * primeValuation p x ↔ _
  rw [hv]
  exact_mod_cast (show k ≤ 2 * x.natAbs.factorization p ↔
    (k+1)/2 ≤ x.natAbs.factorization p by omega)

/-- Congruence by a higher prime power preserves a finite valuation. -/
theorem valuation_congr (p : ℕ) (hp : p.Prime) {k s : ℕ} {a b : ℤ}
    (ha : primeValuation p a = (s : ℕ∞)) (hs : s < k)
    (hab : (p : ℤ)^k ∣ b-a) : primeValuation p b = (s : ℕ∞) := by
  have hd : (p : ℤ)^(s+1) ∣ b-a := (pow_dvd_pow _ (by omega)).trans hab
  simpa only [add_sub_cancel] using P203.Ch01.unequalValuationSum p hp a (b-a) s ha hd

/-- A root of a nonzero residue has twice its own finite valuation. -/
theorem root_valuation (p : ℕ) (hp : p.Prime) {k s : ℕ} {a x : ℤ}
    (ha : primeValuation p a = (s : ℕ∞)) (hs : s < k)
    (hx : (p : ℤ)^k ∣ x^2-a) :
    x ≠ 0 ∧ s = 2 * (primeValuation p x).toNat := by
  have he := valuation_congr p hp ha hs hx
  have hxn : x ≠ 0 := by
    intro h
    have htop : primeValuation p (x^2) = ⊤ := by
      rw [h]; exact (P203.Ch01.valuationZeroAndUnits p hp).1
    rw [htop] at he
    exact ENat.natCast_ne_top s he.symm
  refine ⟨hxn, ?_⟩
  have hv := (P203.Ch01.valuationFactorizationBridge p hp x hxn).1
  change emultiplicity (p : ℤ) (x^2) = _ at he
  rw [emultiplicity_pow (Nat.prime_iff_prime_int.mp hp)] at he
  change 2 * primeValuation p x = (s : ℕ∞) at he
  rw [hv] at he
  have he' : 2 * x.natAbs.factorization p = s := by exact_mod_cast he
  simpa only [hv, ENat.toNat_natCast] using he'.symm

/-- Multiples in a complete interval are parametrized without repetition. -/
noncomputable def multiplesEquiv (d n : ℕ) (hd : 0 < d) :
    Fin n ≃ {x : Fin (d*n) // d ∣ x.val} := by
  let f : Fin n → {x : Fin (d*n) // d ∣ x.val} := fun y =>
    ⟨⟨d*y.val, Nat.mul_lt_mul_of_pos_left y.isLt hd⟩, dvd_mul_right d y.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro y z h
    apply Fin.ext
    have he : d*y.val = d*z.val := congrArg (fun w => w.val.val) h
    exact Nat.eq_of_mul_eq_mul_left hd he
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := hx
    have hylt : y < n := Nat.lt_of_mul_lt_mul_left (hy ▸ x.isLt)
    refine ⟨⟨y, hylt⟩, ?_⟩
    exact Subtype.ext (Fin.ext hy.symm)

/-- Cancelling the square of the extracted factor in the integer congruence. -/
theorem scale_congruence (d n : ℕ) (hd : 0 < d) (b y : ℤ) :
    ((d^2*n : ℕ) : ℤ) ∣ ((d : ℤ)*y)^2 - (d : ℤ)^2*b ↔
      (n : ℤ) ∣ y^2-b := by
  have hd0 : (d : ℤ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hd.ne')
  have he : ((d : ℤ)*y)^2 - (d : ℤ)^2*b = (d : ℤ)^2*(y^2-b) := by ring
  rw [he, Nat.cast_mul, Nat.cast_pow, mul_dvd_mul_iff_left hd0]

/-- Integer congruence depends only on the residue of the representative. -/
theorem square_congr_add (n : ℕ) (b y z : ℤ) :
    (n : ℤ) ∣ (y+(n : ℤ)*z)^2-b ↔ (n : ℤ) ∣ y^2-b := by
  have he : (y+(n : ℤ)*z)^2-b = (y^2-b) + (n : ℤ)*(2*y*z+n*z^2) := by ring
  rw [he]
  constructor
  · intro h
    convert dvd_sub h (dvd_mul_right (n : ℤ) (2*y*z+n*z^2)) using 1; ring
  · intro h
    exact dvd_add h (dvd_mul_right _ _)

/-- All lifts of a congruence from `n` to `d*n`, in quotient/remainder order. -/
noncomputable def liftedRootsEquiv (d n : ℕ) (b : ℤ) :
    (QuadraticRoots n b × Fin d) ≃
      {y : Fin (d*n) // (n : ℤ) ∣ (y.val : ℤ)^2-b} := by
  let e : Fin n × Fin d ≃ Fin (d*n) :=
    (Equiv.prodComm _ _).trans finProdFinEquiv
  apply Equiv.prodSubtypeFstEquivSubtypeProd.symm.trans
    (e.subtypeEquiv ?_)
  rintro ⟨u, v⟩
  change (n : ℤ) ∣ (u.val : ℤ)^2-b ↔
    (n : ℤ) ∣ ((u.val+n*v.val : ℕ) : ℤ)^2-b
  push_cast
  exact (square_congr_add n b u.val v.val).symm

@[simp] theorem liftedRootsEquiv_val (d n : ℕ) (b : ℤ)
    (z : QuadraticRoots n b × Fin d) :
    (liftedRootsEquiv d n b z).val.val = z.1.val.val+n*z.2.val := rfl

/-- Multiplication by `d` bijects the reduced congruence onto the roots,
once divisibility by `d` has been established. -/
noncomputable def scaleRootsEquiv (d n : ℕ) (hd : 0 < d) (b : ℤ)
    (hdiv : ∀ x : QuadraticRoots (d^2*n) ((d : ℤ)^2*b), d ∣ x.val.val) :
    {y : Fin (d*n) // (n : ℤ) ∣ (y.val : ℤ)^2-b} ≃
      QuadraticRoots (d^2*n) ((d : ℤ)^2*b) := by
  let f : {y : Fin (d*n) // (n : ℤ) ∣ (y.val : ℤ)^2-b} →
      QuadraticRoots (d^2*n) ((d : ℤ)^2*b) := fun y =>
    ⟨⟨d*y.val.val, by
        have h := Nat.mul_lt_mul_of_pos_left y.val.isLt hd
        nlinarith⟩,
      by simpa only [Nat.cast_mul] using (scale_congruence d n hd b y.val.val).mpr y.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro y z h
    apply Subtype.ext
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hd (congrArg (fun w => w.val.val) h)
  · intro x
    obtain ⟨y, hy⟩ := hdiv x
    have hylt : y < d*n := by
      apply Nat.lt_of_mul_lt_mul_left (a := d)
      calc d*y = x.val.val := hy.symm
           _ < d*(d*n) := by nlinarith [x.val.isLt]
    have hroot : (n : ℤ) ∣ (y : ℤ)^2-b := by
      apply (scale_congruence d n hd b y).mp
      simpa only [hy, Nat.cast_mul] using x.property
    exact ⟨⟨⟨y, hylt⟩, hroot⟩, Subtype.ext (Fin.ext hy.symm)⟩

@[simp] theorem scaleRootsEquiv_val (d n : ℕ) (hd : 0 < d) (b : ℤ)
    (hdiv : ∀ x : QuadraticRoots (d^2*n) ((d : ℤ)^2*b), d ∣ x.val.val)
    (y : {y : Fin (d*n) // (n : ℤ) ∣ (y.val : ℤ)^2-b}) :
    (scaleRootsEquiv d n hd b hdiv y).val.val = d*y.val.val := rfl

theorem zeroResidueRoots : ZeroResidueRoots := by
  intro p hp k _ a ha
  have hcrit : ∀ x : ℤ, (p : ℤ)^k ∣ x^2-a ↔ (p : ℤ)^((k+1)/2) ∣ x := by
    intro x
    rw [← prime_pow_dvd_square p hp k x]
    exact ⟨fun h => by simpa only [sub_add_cancel] using dvd_add h ha,
      fun h => dvd_sub h ha⟩
  refine ⟨hcrit, ?_⟩
  let e : QuadraticRoots (p^k) a ≃
      {x : Fin (p^k) // p^((k+1)/2) ∣ x.val} :=
    Equiv.subtypeEquivRight fun x => by
      rw [Nat.cast_pow, hcrit]
      exact_mod_cast (Iff.rfl : p^((k+1)/2) ∣ x.val ↔ p^((k+1)/2) ∣ x.val)
  unfold quadraticRootCount
  rw [Nat.card_congr e]
  have hm : p^k = p^((k+1)/2)*p^(k/2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hm]
  rw [← Nat.card_congr (multiplesEquiv (p^((k+1)/2)) (p^(k/2)) (pow_pos hp.pos _))]
  simp

theorem nonzeroResidueValuation : NonzeroResidueValuation := by
  intro p hp k _ a ha
  have han : a ≠ 0 := by rintro rfl; exact ha (dvd_zero _)
  obtain ⟨hv, _⟩ := P203.Ch01.valuationFactorizationBridge p hp a han
  have hs : a.natAbs.factorization p < k := by
    have hnot := mt (P203.Ch01.valuationPrimePowers p hp a k).mpr ha
    rw [hv] at hnot
    exact lt_of_not_ge (by exact_mod_cast hnot)
  exact ⟨han, a.natAbs.factorization p, hv, hs,
    fun b hb => valuation_congr p hp hv hs hb⟩

theorem oddValuationNoRoots : OddValuationNoRoots := by
  intro p hp k s a ha hs hodd
  have hnone : ∀ x : ℤ, ¬(p : ℤ)^k ∣ x^2-a := by
    intro x hx
    obtain ⟨_, he⟩ := root_valuation p hp ha hs hx
    obtain ⟨r, hr⟩ := hodd
    omega
  refine ⟨hnone, ?_⟩
  have : IsEmpty (QuadraticRoots (p^k) a) := ⟨fun x =>
    hnone x.val.val (by simpa only [Nat.cast_pow] using x.property)⟩
  exact Nat.card_of_isEmpty

/-- The even-valuation case forces every integer root to contain the
extracted prime power. -/
theorem root_divisible (p : ℕ) (hp : p.Prime) {k t : ℕ} {a x : ℤ}
    (ha : primeValuation p a = ((2*t : ℕ) : ℕ∞)) (ht : 2*t < k)
    (hx : (p : ℤ)^k ∣ x^2-a) : (p : ℤ)^t ∣ x := by
  obtain ⟨hxn, he⟩ := root_valuation p hp ha ht hx
  have hv := (P203.Ch01.valuationFactorizationBridge p hp x hxn).1
  rw [hv] at he
  simp only [ENat.toNat_natCast] at he
  rw [P203.Ch01.valuationPrimePowers p hp, hv]
  exact_mod_cast (show t ≤ x.natAbs.factorization p by omega)

/-- Generic parametrization after extracting a square factor. -/
theorem roots_parameterization (m d n : ℕ) (hd : 0 < d) (hm : m = d^2*n)
    (a b : ℤ) (ha : a = (d : ℤ)^2*b)
    (hdiv : ∀ x : QuadraticRoots m a, d ∣ x.val.val) :
    ∃ e : (QuadraticRoots n b × Fin d) ≃ QuadraticRoots m a,
      ∀ z, (e z).val.val = d*(z.1.val.val+n*z.2.val) := by
  subst m
  subst a
  refine ⟨(liftedRootsEquiv d n b).trans (scaleRootsEquiv d n hd b hdiv), ?_⟩
  intro z
  rfl

theorem evenValuationReduction : EvenValuationReduction := by
  intro p hp k t a hv ht
  dsimp only
  let j := k-2*t
  let b := a / (p : ℤ)^(2*t)
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hd : (p : ℤ)^(2*t) ∣ a := by
    rw [P203.Ch01.valuationPrimePowers p hp, hv]
  have ha : a = (p : ℤ)^(2*t)*b := (Int.mul_ediv_cancel' hd).symm
  have hu : ¬(p : ℤ) ∣ b := by
    intro hb
    have hnext : (p : ℤ)^(2*t+1) ∣ a := by
      obtain ⟨c, hc⟩ := hb
      refine ⟨c, ?_⟩
      rw [ha, hc, pow_succ]
      ring
    rw [P203.Ch01.valuationPrimePowers p hp, hv] at hnext
    have : 2*t+1 ≤ 2*t := by exact_mod_cast hnext
    omega
  have hm : p^k = (p^t)^2*p^j := by
    rw [← pow_mul, ← pow_add]
    congr 1
    dsimp [j]
    omega
  have ha2 : a = ((p^t : ℕ) : ℤ)^2*b := by
    rw [Nat.cast_pow, ← pow_mul]
    simpa only [Nat.mul_comm t 2] using ha
  have hscale : ∀ y : ℤ, (p : ℤ)^k ∣ ((p : ℤ)^t*y)^2-a ↔
      (p : ℤ)^j ∣ y^2-b := by
    intro y
    have h := scale_congruence (p^t) (p^j) (pow_pos hp.pos _) b y
    rw [ha2]
    simpa only [← hm, Nat.cast_pow] using h
  have hdiv : ∀ x : QuadraticRoots (p^k) a, p^t ∣ x.val.val := by
    intro x
    have hx := root_divisible p hp hv ht
      (by simpa only [Nat.cast_pow] using x.property)
    exact_mod_cast hx
  obtain ⟨e, he⟩ := roots_parameterization (p^k) (p^t) (p^j)
    (pow_pos hp.pos _) hm a b ha2 hdiv
  refine ⟨hj, ha, hu, ?_, ⟨e, he⟩, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := root_divisible p hp hv ht hx
      exact ⟨y, hy, (hscale y).mp (by simpa only [hy] using hx)⟩
    · rintro ⟨y, rfl, hy⟩
      exact (hscale y).mpr hy
  · unfold quadraticRootCount
    rw [← Nat.card_congr e, Nat.card_prod, Nat.card_fin, mul_comm]

/-- The chosen complete representatives are exactly the roots in `ZMod`. -/
theorem quadraticRootsResidueBridge : QuadraticRootsResidueBridge := by
  intro m hm a
  have : NeZero m := ⟨hm.ne'⟩
  let e : Fin m ≃ ZMod m := {
    toFun := fun x => (x.val : ZMod m)
    invFun := fun x => ⟨x.val, x.val_lt⟩
    left_inv := fun x => Fin.ext (ZMod.val_natCast_of_lt x.isLt)
    right_inv := ZMod.natCast_zmod_val }
  have he : ∀ x : Fin m,
      (m : ℤ) ∣ (x.val : ℤ)^2-a ↔ (e x)^2 = (a : ZMod m) := by
    intro x
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero
  let er : QuadraticRoots m a ≃ {x : ZMod m // x^2 = (a : ZMod m)} :=
    e.subtypeEquiv he
  exact ⟨⟨er, fun _ => rfl⟩, Nat.card_congr er⟩

end P203.Ch02
