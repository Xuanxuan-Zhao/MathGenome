import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRankOneExtension
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

open AlgebraicGeometry CategoryTheory Opposite
open scoped Matrix CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.IntegralRankOneExtension

open Specs.IntegralRankOneExtension
open Specs.IntegralRootRelations (upper lower diagonal)

noncomputable section

private abbrev SL (R : Type u) [CommRing R] := Matrix.SpecialLinearGroup (Fin 2) R

section MatrixCalculations
variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The determinant-one equation makes the two first-column pivot opens
cover the whole rank-one source. -/
private theorem rankOne_pivots_generate (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    Ideal.span {m.val 0 0, m.val 1 0} = ⊤ := by
  let I := Ideal.span {m.val 0 0, m.val 1 0}
  have ha : m.val 0 0 ∈ I := Ideal.subset_span (by simp)
  have hc : m.val 1 0 ∈ I := Ideal.subset_span (by simp)
  have hdet : m.val 0 0 * m.val 1 1 - m.val 0 1 * m.val 1 0 = 1 :=
    (Matrix.det_fin_two m.val).symm.trans m.property
  rw [Ideal.eq_top_iff_one]
  change (1 : R) ∈ I
  exact (congrArg (fun a : R => a ∈ I) hdet).mp
    (I.sub_mem (I.mul_mem_right _ ha) (I.mul_mem_left _ hc))

/-- The coordinates on the principal chart where the top-left entry is
invertible. This is the rank-one Gauss product over an arbitrary ring. -/
private theorem rankOne_pivot_factorization (m : Matrix.SpecialLinearGroup (Fin 2) R)
    (a : Rˣ) (ha : (a : R) = m.val 0 0) :
    m = lower (m.val 1 0 * ↑a⁻¹) * diagonal a * upper (m.val 0 1 * ↑a⁻¹) := by
  have hdet : (a : R) * m.val 1 1 - m.val 0 1 * m.val 1 0 = 1 := by
    rw [ha, ← Matrix.det_fin_two]
    exact m.property
  have hdiag : m.val 1 1 = ↑a⁻¹ * (1 + m.val 0 1 * m.val 1 0) := by
    have h := congrArg (fun r : R => (↑a⁻¹ : R) * r) (sub_eq_iff_eq_add.mp hdet)
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using h
  apply Subtype.ext
  change m.val = (!![1, 0; m.val 1 0 * ↑a⁻¹, 1] : Matrix (Fin 2) (Fin 2) R) *
    !![(a : R), 0; 0, ↑a⁻¹] * !![1, m.val 0 1 * ↑a⁻¹; 0, 1]
  have hal : (↑a⁻¹ : R) * (a : R) = 1 := Units.inv_mul a
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using ha.symm
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [mul_left_comm (a : R), Units.mul_inv, mul_one]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, hal]
  · simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, hal]
    rw [hdiag]
    ring

/-- The integral Weyl word sends the bottom-left pivot to the top-left entry. -/
private theorem rankOne_weyl_pivot (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    ((upper (1 : R) * lower (-1) * upper 1) * m).val 0 0 = m.val 1 0 := by
  change ((!![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1] *
    m.val : Matrix (Fin 2) (Fin 2) R) 0 0) = _
  simp [Matrix.mul_apply, Fin.sum_univ_two]


private structure Gauss (R : Type u) [CommRing R] where
  l : R
  a : Rˣ
  r : R

private def Gauss.matrix (b : Gauss R) : SL R :=
  lower b.l * diagonal b.a * upper b.r

private def Gauss.ofMatrix (m : SL R) (a : Rˣ) : Gauss R :=
  ⟨m.val 1 0 * ↑a⁻¹, a, m.val 0 1 * ↑a⁻¹⟩

@[simp] private theorem Gauss.matrix_ofMatrix (m : SL R) (a : Rˣ) (ha : (a : R) = m.val 0 0) :
    (Gauss.ofMatrix m a).matrix = m :=
  (rankOne_pivot_factorization m a ha).symm

private theorem Gauss.matrix_val (b : Gauss R) :
    b.matrix.val = !![↑b.a, ↑b.a * b.r; b.l * ↑b.a, b.l * ↑b.a * b.r + ↑b.a⁻¹] := by
  change (!![1, 0; b.l, 1] : Matrix (Fin 2) (Fin 2) R) *
    !![(b.a : R), 0; 0, ↑b.a⁻¹] * !![1, b.r; 0, 1] = _
  simp

private theorem Gauss.matrix_injective : Function.Injective (Gauss.matrix (R := R)) := by
  intro b c h
  have hentry (i j : Fin 2) := congrArg (fun m : SL R => m.val i j) h
  have ha : b.a = c.a := Units.ext (by simpa [Gauss.matrix_val] using hentry 0 0)
  have hl : b.l * (b.a : R) = c.l * (c.a : R) := by simpa [Gauss.matrix_val] using hentry 1 0
  have hr : (b.a : R) * b.r = (c.a : R) * c.r := by simpa [Gauss.matrix_val] using hentry 0 1
  rw [← ha] at hl hr
  have hl' := congrArg (fun x : R => x * (↑b.a⁻¹ : R)) hl
  have hr' := congrArg (fun x : R => (↑b.a⁻¹ : R) * x) hr
  simp only [mul_assoc, Units.mul_inv, mul_one] at hl'
  simp only [← mul_assoc, Units.inv_mul, one_mul] at hr'
  cases b
  cases c
  congr

private def Gauss.upperFactor (x : R) : Gauss R := ⟨0, 1, x⟩
private def Gauss.lowerFactor (y : R) : Gauss R := ⟨y, 1, 0⟩
private def Gauss.diagonalFactor (s : Rˣ) : Gauss R := ⟨0, s, 0⟩

@[simp] private theorem Gauss.matrix_upper (x : R) : (Gauss.upperFactor x).matrix = upper x := by
  apply Subtype.ext
  rw [Gauss.matrix_val]
  simp [Gauss.upperFactor, upper]

@[simp] private theorem Gauss.matrix_lower (y : R) : (Gauss.lowerFactor y).matrix = lower y := by
  apply Subtype.ext
  rw [Gauss.matrix_val]
  simp [Gauss.lowerFactor, lower]

@[simp] private theorem Gauss.matrix_diagonal (s : Rˣ) :
    (Gauss.diagonalFactor s).matrix = diagonal s := by
  apply Subtype.ext
  rw [Gauss.matrix_val]
  simp [Gauss.diagonalFactor, diagonal]

private theorem Gauss.product_matrix (b c : Gauss R) (s : Rˣ) (hs : (s : R) = 1 + b.r * c.l) :
    b.matrix * c.matrix =
      (⟨b.l + (↑b.a⁻¹ : R) ^ 2 * (c.l * ↑s⁻¹), b.a * s * c.a,
        (↑c.a⁻¹ : R) ^ 2 * (b.r * ↑s⁻¹) + c.r⟩ : Gauss R).matrix := by
  let a := b.a * s * c.a
  let m := b.matrix * c.matrix
  let l := b.l + (↑b.a⁻¹ : R) ^ 2 * (c.l * ↑s⁻¹)
  let r := (↑c.a⁻¹ : R) ^ 2 * (b.r * ↑s⁻¹) + c.r
  have hm : m.val = b.matrix.val * c.matrix.val := rfl
  rw [b.matrix_val, c.matrix_val] at hm
  have ha : (a : R) = m.val 0 0 := by
    rw [hm]
    change (b.a : R) * (s : R) * (c.a : R) = _
    simp [hs]
    ring
  have hl : m.val 1 0 = l * (a : R) := by
    rw [hm]
    calc
      _ = b.l * ((b.a : R) * (s : R) * (c.a : R)) +
          (↑b.a⁻¹ : R) * c.l * (c.a : R) := by
        simp [hs]
        ring
      _ = b.l * ((b.a : R) * (s : R) * (c.a : R)) +
          (↑b.a⁻¹ : R) * c.l * (c.a : R) * (↑b.a⁻¹ * (b.a : R)) * (↑s⁻¹ * (s : R)) := by
        rw [Units.inv_mul, Units.inv_mul, mul_one, mul_one]
      _ = _ := by
        change _ = (b.l + (↑b.a⁻¹ : R) ^ 2 * (c.l * ↑s⁻¹)) * (↑b.a * ↑s * ↑c.a)
        ring
  have hr : m.val 0 1 = (a : R) * r := by
    rw [hm]
    calc
      _ = ((b.a : R) * (s : R) * (c.a : R)) * c.r +
          (b.a : R) * b.r * (↑c.a⁻¹ : R) := by
        simp [hs]
        ring
      _ = ((b.a : R) * (s : R) * (c.a : R)) * c.r +
          (b.a : R) * b.r * (↑c.a⁻¹ : R) * ((c.a : R) * ↑c.a⁻¹) * ((s : R) * ↑s⁻¹) := by
        rw [Units.mul_inv, Units.mul_inv, mul_one, mul_one]
      _ = _ := by
        change _ = ((b.a : R) * ↑s * ↑c.a) * ((↑c.a⁻¹ : R) ^ 2 * (b.r * ↑s⁻¹) + c.r)
        ring
  change m = (⟨l, a, r⟩ : Gauss R).matrix
  rw [rankOne_pivot_factorization m a ha, hl, hr, mul_assoc l, Units.mul_inv, mul_one,
    mul_comm (a : R) r, mul_assoc r, Units.mul_inv, mul_one]
  rfl

private def Gauss.map {S : Type u} [CommRing S] (f : R →+* S) (b : Gauss R) : Gauss S :=
  ⟨f b.l, Units.map f.toMonoidHom b.a, f b.r⟩

private theorem Gauss.map_matrix {S : Type u} [CommRing S] (f : R →+* S) (b : Gauss R) :
    (b.map f).matrix = Matrix.SpecialLinearGroup.map f b.matrix := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gauss.matrix_val, Gauss.map,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

end MatrixCalculations

section GaussProduct
variable {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- The Gauss multiplication law on the open locus where both factors and
their product have a unit first pivot. -/
private theorem rankOne_gauss_mul
    (upper lower : Multiplicative R →* G) (diagonal : Rˣ →* G)
    (opposite : ∀ (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      upper (.ofAdd x) * lower (.ofAdd y) =
        lower (.ofAdd (y * (↑s⁻¹ : R))) * diagonal s * upper (.ofAdd (x * (↑s⁻¹ : R))))
    (conjugationUpper : ∀ (a : Rˣ) (x : R),
      diagonal a * upper (.ofAdd x) * (diagonal a)⁻¹ = upper (.ofAdd ((a : R) ^ 2 * x)))
    (conjugationLower : ∀ (a : Rˣ) (x : R),
      diagonal a * lower (.ofAdd x) * (diagonal a)⁻¹ = lower (.ofAdd ((↑a⁻¹ : R) ^ 2 * x)))
    (u v x y : R) (a b s : Rˣ) (hs : (s : R) = 1 + v * x) :
    let U (z : R) := upper (Multiplicative.ofAdd z)
    let L (z : R) := lower (Multiplicative.ofAdd z)
    (L u * diagonal a * U v) * (L x * diagonal b * U y) =
      L (u + (↑a⁻¹ : R) ^ 2 * (x * ↑s⁻¹)) * diagonal (a * s * b) *
        U ((↑b⁻¹ : R) ^ 2 * (v * ↑s⁻¹) + y) := by
  let U (z : R) := upper (Multiplicative.ofAdd z)
  let L (z : R) := lower (Multiplicative.ofAdd z)
  have hU (z w : R) : U (z + w) = U z * U w :=
    upper.map_mul (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)
  have hL (z w : R) : L (z + w) = L z * L w :=
    lower.map_mul (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)
  have moveUpper (z : R) (t : Rˣ) :
      U z * diagonal t = diagonal t * U ((↑t⁻¹ : R) ^ 2 * z) := by
    have h := congrArg (fun g : G => diagonal t * g) (conjugationUpper t⁻¹ z)
    simpa only [← map_inv, inv_inv, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] using h
  have moveLower (z : R) (t : Rˣ) :
      diagonal t * L z = L ((↑t⁻¹ : R) ^ 2 * z) * diagonal t := by
    have h := congrArg (fun g : G => g * diagonal t) (conjugationLower t z)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  change (L u * diagonal a * U v) * (L x * diagonal b * U y) = _
  calc
    _ = L u * diagonal a * (U v * L x) * diagonal b * U y := by simp only [mul_assoc]
    _ = L u * (diagonal a * L (x * ↑s⁻¹)) * diagonal s * (U (v * ↑s⁻¹) * diagonal b) * U y := by
      rw [opposite v x s hs]
      simp only [mul_assoc, L, U]
    _ = (L u * L ((↑a⁻¹ : R) ^ 2 * (x * ↑s⁻¹))) * (diagonal a * diagonal s * diagonal b) *
        (U ((↑b⁻¹ : R) ^ 2 * (v * ↑s⁻¹)) * U y) := by
      rw [moveLower, moveUpper]
      simp only [mul_assoc]
    _ = _ := by rw [← hL, ← hU, ← diagonal.map_mul, ← diagonal.map_mul]


end GaussProduct

section PivotExtension
variable {R : Type u} [CommRing R]

private def rankOnePivotPolynomial (m : Matrix.SpecialLinearGroup (Fin 2) R) : Polynomial R :=
  Polynomial.C (m.val 0 0) + Polynomial.C (m.val 1 0) * Polynomial.X

private theorem rankOnePivotPolynomial_regular (m : Matrix.SpecialLinearGroup (Fin 2) R) :
    rankOnePivotPolynomial m ∈ nonZeroDivisors (Polynomial R) := by
  apply Polynomial.mem_nonZeroDivisors_iff.mpr
  intro r hr
  have ha : r * m.val 0 0 = 0 := by
    simpa [rankOnePivotPolynomial, Polynomial.coeff_smul, smul_eq_mul] using
      congrArg (fun p : Polynomial R => p.coeff 0) hr
  have hc : r * m.val 1 0 = 0 := by
    simpa [rankOnePivotPolynomial, Polynomial.coeff_smul, smul_eq_mul] using
      congrArg (fun p : Polynomial R => p.coeff 1) hr
  have hd : m.val 0 0 * m.val 1 1 - m.val 0 1 * m.val 1 0 = 1 :=
    (Matrix.det_fin_two m.val).symm.trans m.property
  calc
    r = r * (m.val 0 0 * m.val 1 1 - m.val 0 1 * m.val 1 0) := by rw [hd, mul_one]
    _ = (r * m.val 0 0) * m.val 1 1 - m.val 0 1 * (r * m.val 1 0) := by ring
    _ = 0 := by rw [ha, hc, zero_mul, mul_zero, sub_zero]

/-- One upper transvection arranges all of a finite list of first-column
pivots to be units after an injective extension of the test ring. -/
private theorem exists_rankOne_pivots_after_injective_extension
    (l : List (Matrix.SpecialLinearGroup (Fin 2) R)) :
    ∃ (S : Type u) (_ : CommRing S) (f : R →+* S) (t : S), Function.Injective f ∧
      ∀ m ∈ l, IsUnit ((upper t * Matrix.SpecialLinearGroup.map f m).val 0 0) := by
  let a := (l.map rankOnePivotPolynomial).prod
  have ha : a ∈ nonZeroDivisors (Polynomial R) := by
    change (l.map rankOnePivotPolynomial).prod ∈ nonZeroDivisors (Polynomial R)
    induction l with
    | nil => simp
    | cons m l ih =>
      exact (nonZeroDivisors (Polynomial R)).mul_mem (rankOnePivotPolynomial_regular m) ih
  let S := Localization.Away a
  let g := algebraMap (Polynomial R) S
  let f := g.comp Polynomial.C
  have hg : Function.Injective g := IsLocalization.injective S (Submonoid.powers_le.mpr ha)
  refine ⟨S, inferInstance, f, g Polynomial.X, hg.comp Polynomial.C_injective, ?_⟩
  intro m hm
  have hc : ((upper (g Polynomial.X) * Matrix.SpecialLinearGroup.map f m).val 0 0) =
      g (rankOnePivotPolynomial m) := by
    change (!![1, g Polynomial.X; 0, 1] * f.mapMatrix m.val : Matrix (Fin 2) (Fin 2) S) 0 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_two, f, rankOnePivotPolynomial]
    ring
  rw [hc]
  have hd : rankOnePivotPolynomial m ∣ a :=
    List.dvd_prod (List.mem_map_of_mem hm)
  exact isUnit_of_dvd_unit (map_dvd g hd) (IsLocalization.Away.algebraMap_isUnit a)


end PivotExtension

section WordEvaluation

variable {G : IntegralGroup.{u}} (h : RootHomomorphisms G)
variable {R S : IntegralAlgebra.{u}}

private def Gauss.value (b : Gauss R) : IntegralPoints G R :=
  h.negative R (.ofAdd b.l) * h.coroot R b.a * h.positive R (.ofAdd b.r)

@[simp] private theorem Gauss.value_upper (x : R) :
    (Gauss.upperFactor x).value h = h.positive R (.ofAdd x) := by
  simp [Gauss.value, Gauss.upperFactor, show Multiplicative.ofAdd (0 : R) = 1 from rfl]

@[simp] private theorem Gauss.value_lower (x : R) :
    (Gauss.lowerFactor x).value h = h.negative R (.ofAdd x) := by
  simp [Gauss.value, Gauss.lowerFactor, show Multiplicative.ofAdd (0 : R) = 1 from rfl]

@[simp] private theorem Gauss.value_diagonal (s : Rˣ) :
    (Gauss.diagonalFactor s).value h = h.coroot R s := by
  simp [Gauss.value, Gauss.diagonalFactor, show Multiplicative.ofAdd (0 : R) = 1 from rfl]

private theorem Gauss.map_value (f : R ⟶ S) (b : Gauss R) :
    (b.map f.hom.toRingHom).value h = (integralPointFunctor G).map f (b.value h) := by
  change h.negative S (.ofAdd (f.hom b.l)) *
      h.coroot S (Units.map f.hom.toMonoidHom b.a) * h.positive S (.ofAdd (f.hom b.r)) =
    (integralPointFunctor G).map f (b.value h)
  simp only [Gauss.value, map_mul, h.map_negative, h.map_positive, h.map_coroot]

private theorem Gauss.value_mul (b c d : Gauss R) (hd : b.matrix * c.matrix = d.matrix) :
    b.value h * c.value h = d.value h := by
  have hp : (d.a : R) = (b.a : R) * (1 + b.r * c.l) * (c.a : R) := by
    have he := congrArg (fun m : SL R => m.val 0 0) hd
    change (b.matrix.val * c.matrix.val) 0 0 = d.matrix.val 0 0 at he
    rw [b.matrix_val, c.matrix_val, d.matrix_val] at he
    simp [Matrix.mul_apply, Fin.sum_univ_two] at he
    rw [← he]
    ring
  let s := b.a⁻¹ * d.a * c.a⁻¹
  have hs : (s : R) = 1 + b.r * c.l := by
    change (↑b.a⁻¹ : R) * (d.a : R) * (↑c.a⁻¹ : R) = _
    rw [hp]
    calc
      _ = ((↑b.a⁻¹ : R) * b.a) * ((c.a : R) * ↑c.a⁻¹) * (1 + b.r * c.l) := by ring
      _ = _ := by rw [Units.inv_mul, Units.mul_inv, one_mul, one_mul]
  let e : Gauss R :=
    ⟨b.l + (↑b.a⁻¹ : R) ^ 2 * (c.l * ↑s⁻¹), b.a * s * c.a,
      (↑c.a⁻¹ : R) ^ 2 * (b.r * ↑s⁻¹) + c.r⟩
  have he : b.matrix * c.matrix = e.matrix :=
    Gauss.product_matrix b c s hs
  have hed : e = d := Gauss.matrix_injective (he.symm.trans hd)
  rw [← hed]
  exact rankOne_gauss_mul (h.positive R) (h.negative R) (h.coroot R) (h.opposite R)
    (h.positive_conjugation R) (h.negative_conjugation R) b.l b.r c.l c.r b.a c.a s hs

private def prefixes {B : Type u} [CommRing B] (m : SL B) : List (Gauss B) → List (SL B)
  | [] => [m]
  | b :: l => m :: prefixes (m * b.matrix) l

private theorem map_prefixes {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (m : SL A) (l : List (Gauss A)) :
    prefixes (Matrix.SpecialLinearGroup.map f m) (l.map (Gauss.map f)) =
      (prefixes m l).map (Matrix.SpecialLinearGroup.map f) := by
  induction l generalizing m with
  | nil => rfl
  | cons b l ih =>
    simp only [prefixes, List.map_cons, Gauss.map_matrix, ← map_mul, ih]

private theorem translate_word (m : SL R) (l : List (Gauss R))
    (hgood : ∀ n ∈ prefixes m l, IsUnit (n.val 0 0))
    (b : Gauss R) (hb : b.matrix = m) :
    ∃ c : Gauss R, c.matrix = m * (l.map Gauss.matrix).prod ∧
      c.value h = b.value h * (l.map (Gauss.value h)).prod := by
  induction l generalizing m b with
  | nil => exact ⟨b, by simpa using hb, by simp⟩
  | cons d l ih =>
    have hgood' : ∀ n ∈ prefixes (m * d.matrix) l, IsUnit (n.val 0 0) :=
      fun n hn => hgood n (List.mem_cons_of_mem _ hn)
    have hmd : IsUnit ((m * d.matrix).val 0 0) := hgood' _ (by cases l <;> simp [prefixes])
    let e := Gauss.ofMatrix (m * d.matrix) hmd.unit
    have he : e.matrix = m * d.matrix := Gauss.matrix_ofMatrix _ _ hmd.unit_spec
    obtain ⟨c, hc, hv⟩ := ih _ hgood' e he
    have hbe : b.value h * d.value h = e.value h := Gauss.value_mul h _ _ _ (by rw [hb, he])
    refine ⟨c, ?_, ?_⟩
    · simpa only [List.map_cons, List.prod_cons, mul_assoc] using hc
    · simpa only [List.map_cons, List.prod_cons, ← mul_assoc, hbe] using hv

/-- A graph pair obtained by multiplying finitely many Gauss factors. -/
private def Evaluates (m : SL R) (p : IntegralPoints G R) : Prop :=
  ∃ l : List (Gauss R), (l.map Gauss.matrix).prod = m ∧ (l.map (Gauss.value h)).prod = p

private theorem evaluates_gauss (b : Gauss R) : Evaluates h b.matrix (b.value h) :=
  ⟨[b], by simp, by simp⟩

private theorem Evaluates.mul {m n : SL R} {p q : IntegralPoints G R}
    (hm : Evaluates h m p) (hn : Evaluates h n q) : Evaluates h (m * n) (p * q) := by
  obtain ⟨l, hl, hl'⟩ := hm
  obtain ⟨l', hk, hk'⟩ := hn
  exact ⟨l ++ l', by simp [hl, hk], by simp [hl', hk']⟩

private theorem Evaluates.map {m : SL R} {p : IntegralPoints G R}
    (hm : Evaluates h m p) (f : R ⟶ S) :
    Evaluates h (Matrix.SpecialLinearGroup.map f.hom.toRingHom m)
      ((integralPointFunctor G).map f p) := by
  obtain ⟨l, rfl, rfl⟩ := hm
  refine ⟨l.map (Gauss.map f.hom.toRingHom), ?_, ?_⟩
  · simp only [List.map_map, Function.comp_def, Gauss.map_matrix, map_list_prod]
  · simp only [List.map_map, Function.comp_def, Gauss.map_value]
    simpa only [List.map_map, Function.comp_def] using
      (map_list_prod ((integralPointFunctor G).map f).hom (l.map (Gauss.value h))).symm

private theorem evaluates_eq_of_injective_maps
    (hInj : ∀ {R S : IntegralAlgebra.{u}} (f : R ⟶ S), Function.Injective f.hom →
      Function.Injective ((integralPointFunctor G).map f))
    {m : SL R} {p q : IntegralPoints G R}
    (hp : Evaluates h m p) (hq : Evaluates h m q) : p = q := by
  obtain ⟨l, hm, hp⟩ := hp
  obtain ⟨k, hn, hq⟩ := hq
  obtain ⟨S, _, f, t, hf, hunit⟩ :=
    exists_rankOne_pivots_after_injective_extension
      (prefixes 1 l ++ prefixes 1 k)
  let : Algebra Integers.{u} S := (f.comp (algebraMap Integers.{u} R)).toAlgebra
  let T := CommAlgCat.of Integers.{u} S
  let g : R ⟶ T := CommAlgCat.ofHom ⟨f, fun _ => rfl⟩
  let translate : Gauss T := Gauss.upperFactor t
  let mapSL : SL R →* SL S := Matrix.SpecialLinearGroup.map f
  let mapG := (integralPointFunctor G).map g
  have htranslate (v : List (Gauss R)) (hv : ∀ n ∈ prefixes 1 v,
      n ∈ prefixes 1 l ++ prefixes 1 k) :
      ∃ c : Gauss T, c.matrix = translate.matrix * mapSL ((v.map Gauss.matrix).prod) ∧
        c.value h = translate.value h * mapG ((v.map (Gauss.value h)).prod) := by
    -- Translated prefixes are precisely the prefixes beginning at the translating factor.
    have hleft (b : SL S) (n : SL S) (w : List (Gauss S)) :
        n ∈ prefixes (b * (1 : SL S)) w →
          ∃ z ∈ prefixes 1 w, n = b * z := by
      have aux (s : SL S) (w : List (Gauss S)) : ∀ n ∈ prefixes (b * s) w,
          ∃ z ∈ prefixes s w, n = b * z := by
        induction w generalizing s with
        | nil =>
          intro n hn
          simp only [prefixes, List.mem_singleton] at hn ⊢
          exact ⟨s, rfl, hn⟩
        | cons c w ih =>
          intro n hn
          rw [prefixes, List.mem_cons] at hn
          rcases hn with rfl | hn
          · exact ⟨s, by simp [prefixes], rfl⟩
          · obtain ⟨z, hz, rfl⟩ := ih (s * c.matrix) n (by simpa only [mul_assoc] using hn)
            exact ⟨z, List.mem_cons_of_mem _ hz, rfl⟩
      exact aux 1 w n
    let w := v.map (Gauss.map f)
    have hw : ∀ n ∈ prefixes translate.matrix w, IsUnit (n.val 0 0) := by
      intro n hn
      obtain ⟨z, hz, rfl⟩ := hleft translate.matrix n w (by simpa only [mul_one] using hn)
      have he : prefixes (1 : SL S) w = (prefixes (1 : SL R) v).map mapSL := by
        simpa only [map_one] using map_prefixes f (1 : SL R) v
      rw [he, List.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      change IsUnit (((Gauss.upperFactor t).matrix * Matrix.SpecialLinearGroup.map f a).val 0 0)
      rw [Gauss.matrix_upper]
      exact hunit a (hv a ha)
    obtain ⟨c, hc, hcv⟩ := translate_word (R := T) h translate.matrix w hw translate rfl
    have hm' : (w.map Gauss.matrix).prod = mapSL ((v.map Gauss.matrix).prod) := by
      simp only [w, mapSL, List.map_map, Function.comp_def, Gauss.map_matrix, map_list_prod]
    have hv' : (w.map (Gauss.value h)).prod = mapG ((v.map (Gauss.value h)).prod) := by
      simp only [w, List.map_map, Function.comp_def]
      rw [map_list_prod mapG.hom, List.map_map]
      apply congrArg List.prod
      exact List.map_congr_left (fun b _ => Gauss.map_value h g b)
    exact ⟨c, by simpa only [hm'] using hc, by simpa only [hv'] using hcv⟩
  obtain ⟨a, ha, hav⟩ := htranslate l (fun n hn => List.mem_append_left _ hn)
  obtain ⟨b, hb, hbv⟩ := htranslate k (fun n hn => List.mem_append_right _ hn)
  have hab := Gauss.matrix_injective (ha.trans (by rw [hm, ← hn, ← hb]))
  apply hInj g hf
  rw [← hp, ← hq]
  change mapG _ = mapG _
  apply mul_left_cancel (a := translate.value h)
  rw [← hav, ← hbv, hab]

end WordEvaluation

section Descent

variable {G : IntegralGroup.{u}}
variable {A R S : IntegralAlgebra.{u}}
variable (e : integralSpec.obj (op A) ≅ G.X)

private def pointOfCoordinates (x : A →ₐ[Integers.{u}] R) : IntegralPoints G R :=
  integralSpec.map (CommAlgCat.ofHom x).op ≫ e.hom

private theorem pointOfCoordinates_bijective :
    Function.Bijective (pointOfCoordinates (R := R) e) := by
  constructor
  · intro x y hxy
    have h' := (cancel_mono e.hom).mp hxy
    exact congrArg CommAlgCat.Hom.hom
      (Quiver.Hom.op_inj ((algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).map_injective h'))
  · intro p
    change (integralSpec.obj (op R) ⟶ G.X) at p
    let x := (algSpec.fullyFaithful (R := CommRingCat.of Integers.{u})).preimage (p ≫ e.inv)
    refine ⟨x.unop.hom, ?_⟩
    change integralSpec.map x ≫ e.hom = p
    rw [Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def pointsEquiv : (A →ₐ[Integers.{u}] R) ≃ IntegralPoints G R :=
  Equiv.ofBijective (pointOfCoordinates e) (pointOfCoordinates_bijective e)

private theorem pointOfCoordinates_natural (f : R ⟶ S) (x : A →ₐ[Integers.{u}] R) :
    (integralPointFunctor G).map f (pointOfCoordinates e x) =
      pointOfCoordinates e (f.hom.comp x) := by
  change integralSpec.map f.op ≫ (integralSpec.map (CommAlgCat.ofHom x).op ≫ e.hom) = _
  rw [← Category.assoc, ← Functor.map_comp]
  rfl

private theorem coordinates_natural (f : R ⟶ S) (p : IntegralPoints G R) :
    (pointsEquiv e).symm ((integralPointFunctor G).map f p) =
      f.hom.comp ((pointsEquiv e).symm p) := by
  apply (pointsEquiv e).injective
  rw [Equiv.apply_symm_apply]
  change _ = pointOfCoordinates e _
  rw [← pointOfCoordinates_natural]
  exact congrArg ((integralPointFunctor G).map f) ((pointsEquiv e).apply_symm_apply p).symm

include e in
private theorem pointMap_injective (f : R ⟶ S) (hf : Function.Injective f.hom) :
    Function.Injective ((integralPointFunctor G).map f) := by
  intro p q hpq
  apply (pointsEquiv e).symm.injective
  ext x
  apply hf
  exact DFunLike.congr_fun ((coordinates_natural e f p).symm.trans
    ((congrArg (pointsEquiv e).symm hpq).trans (coordinates_natural e f q))) x

private abbrev awayObj (a : R) : IntegralAlgebra.{u} :=
  CommAlgCat.of Integers.{u} (Localization.Away a)

private def awayHom (a : R) : R ⟶ awayObj a :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom Integers.{u} R (Localization.Away a))

private def awayLift (a : R) (f : R ⟶ S) (hf : IsUnit (f.hom a)) : awayObj a ⟶ S :=
  CommAlgCat.ofHom (IsLocalization.Away.liftAlgHom a hf)

private theorem awayHom_lift (a : R) (f : R ⟶ S) (hf : IsUnit (f.hom a)) :
    awayHom a ≫ awayLift a f hf = f := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq a hf x

include e in
private theorem points_ext_on_cover (s : Set R) (hs : Ideal.span s = ⊤)
    {p q : IntegralPoints G R}
    (h : ∀ a : s, (integralPointFunctor G).map (awayHom a.val) p =
      (integralPointFunctor G).map (awayHom a.val) q) : p = q := by
  apply (pointsEquiv e).symm.injective
  ext x
  apply Localization.algebraMap_injective_of_span_eq_top s hs
  funext a
  exact DFunLike.congr_fun ((coordinates_natural e (awayHom a.val) p).symm.trans
    ((congrArg (pointsEquiv e).symm (h a)).trans (coordinates_natural e (awayHom a.val) q))) x

private def pivotSet (m : SL R) : Set R := {m.val 0 0, m.val 1 0}

private theorem pivotSet_span (m : SL R) : Ideal.span (pivotSet m) = ⊤ :=
  rankOne_pivots_generate m

private abbrev mapMatrix (f : R ⟶ S) : SL R →* SL S := Matrix.SpecialLinearGroup.map f.hom.toRingHom

private theorem pivot_mem_map (f : R ⟶ S) (m : SL R) (a : pivotSet (mapMatrix f m)) :
    ∃ b : pivotSet m, f.hom b.val = a.val := by
  rcases a.property with h | h
  · exact ⟨⟨_, Set.mem_insert _ _⟩, h.symm⟩
  · exact ⟨⟨_, Set.mem_insert_of_mem _ (Set.mem_singleton _)⟩, h.symm⟩

variable (h : RootHomomorphisms G)

private theorem exists_eval_of_unit_pivot (m : SL R) (a : pivotSet m) (ha : IsUnit a.val) :
    ∃ p : IntegralPoints G R, Evaluates h m p := by
  rcases a.property with ha' | ha'
  · have hua : (ha.unit : R) = m.val 0 0 := ha.unit_spec.trans ha'
    let b := Gauss.ofMatrix m ha.unit
    exact ⟨b.value h, Gauss.matrix_ofMatrix m ha.unit hua ▸ evaluates_gauss h b⟩
  · have hua : (ha.unit : R) = m.val 1 0 := ha.unit_spec.trans ha'
    let W : SL R := upper (1 : R) * lower (-1) * upper 1
    let b := Gauss.ofMatrix (W * m) ha.unit
    have hb : b.matrix = W * m :=
      Gauss.matrix_ofMatrix _ _ (hua.trans (rankOne_weyl_pivot m).symm)
    let l : List (Gauss R) := [Gauss.upperFactor (-1), Gauss.lowerFactor 1, Gauss.upperFactor (-1), b]
    refine ⟨(l.map (Gauss.value h)).prod, l, ?_, rfl⟩
    suffices hw : upper (-1) * lower (1 : R) * upper (-1) * W = 1 by
      simp only [l, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        Gauss.matrix_upper, Gauss.matrix_lower, hb, ← mul_assoc, hw, one_mul]
    apply Subtype.ext
    change (!![1, (-1 : R); 0, 1] : Matrix (Fin 2) (Fin 2) R) *
      !![1, 0; 1, 1] * !![1, -1; 0, 1] *
      (!![1, 1; 0, 1] * !![1, 0; -1, 1] * !![1, 1; 0, 1]) = 1
    simp [Matrix.one_fin_two]


private theorem exists_eval_after_map (f : R ⟶ S) (m : SL R) (a : pivotSet m)
    (ha : IsUnit (f.hom a.val)) : ∃ p, Evaluates h (mapMatrix f m) p :=
  exists_eval_of_unit_pivot h _ ⟨f.hom a.val, by
    rcases a.property with h₁ | h₁
    · exact Or.inl (congrArg f.hom h₁)
    · exact Or.inr (congrArg f.hom h₁)⟩ ha

private def localPoint (m : SL R) (a : pivotSet m) :
    IntegralPoints G (awayObj a.val) :=
  (exists_eval_after_map h (awayHom a.val) m a
    (IsLocalization.Away.algebraMap_isUnit a.val)).choose

private theorem localPoint_evaluates (m : SL R) (a : pivotSet m) :
    Evaluates h (mapMatrix (awayHom a.val) m) (localPoint h m a) :=
  (exists_eval_after_map h (awayHom a.val) m a
    (IsLocalization.Away.algebraMap_isUnit a.val)).choose_spec

include e in
private theorem exists_glued_point (m : SL R) :
    ∃ p : IntegralPoints G R, ∀ a : pivotSet m,
      (integralPointFunctor G).map (awayHom a.val) p = localPoint h m a := by
  let s := pivotSet m
  let f (a : s) := (pointsEquiv e).symm (localPoint h m a)
  have hf (a b : s) (x : A) :
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.val * b.val))
        a.val b.val (f a x) =
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a.val * b.val))
        b.val a.val (f b x) := by
    let u := awayHom (a.val * b.val)
    have hab : IsUnit (u.hom a.val * u.hom b.val) := by
      rw [← map_mul]
      exact IsLocalization.Away.algebraMap_isUnit _
    let u₁ := awayLift a.val u (isUnit_of_mul_isUnit_left hab)
    let u₂ := awayLift b.val u (isUnit_of_mul_isUnit_right hab)
    have c₁ : awayHom a.val ≫ u₁ = u := awayHom_lift _ _ _
    have c₂ : awayHom b.val ≫ u₂ = u := awayHom_lift _ _ _
    have h₁ := (localPoint_evaluates h m a).map h u₁
    have h₂ := (localPoint_evaluates h m b).map h u₂
    change Evaluates h (mapMatrix (awayHom a.val ≫ u₁) m) _ at h₁
    change Evaluates h (mapMatrix (awayHom b.val ≫ u₂) m) _ at h₂
    rw [c₁] at h₁
    rw [c₂] at h₂
    have hp := evaluates_eq_of_injective_maps h (pointMap_injective e) h₁ h₂
    have hc : u₁.hom.comp (f a) = u₂.hom.comp (f b) := by
      rw [← coordinates_natural, ← coordinates_natural, hp]
    exact DFunLike.congr_fun hc x
  let P := ∀ a : s, Localization.Away a.val
  let l : R →ₐ[Integers.{u}] P := AlgHom.pi (fun a => (awayHom a.val).hom)
  have hl : Function.Injective l := Localization.algebraMap_injective_of_span_eq_top s (pivotSet_span m)
  let j := AlgHom.pi f
  have hj (x : A) : j x ∈ l.range := by
    obtain ⟨y, hy, _⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top s (pivotSet_span m)
      (fun a => f a x) (fun a b => hf a b x)
    exact ⟨y, funext hy⟩
  let k := j.codRestrict l.range hj
  let r := AlgEquiv.ofInjective l hl
  let g := r.symm.toAlgHom.comp k
  refine ⟨pointsEquiv e g, fun a => ?_⟩
  apply (pointsEquiv e).symm.injective
  rw [coordinates_natural, Equiv.symm_apply_apply]
  apply AlgHom.ext
  intro x
  exact congrArg (fun z : l.range => z.val a) (r.apply_symm_apply (k x))

private def value (m : SL R) : IntegralPoints G R :=
  (exists_glued_point e h m).choose

private theorem value_restricts (m : SL R) (a : pivotSet m) :
    (integralPointFunctor G).map (awayHom a.val) (value e h m) = localPoint h m a :=
  (exists_glued_point e h m).choose_spec a

private theorem value_evaluates_after_map (f : R ⟶ S) (m : SL R)
    (a : pivotSet m) (ha : IsUnit (f.hom a.val)) :
    Evaluates h (mapMatrix f m) ((integralPointFunctor G).map f (value e h m)) := by
  let g := awayLift a.val f ha
  have hg : awayHom a.val ≫ g = f := awayHom_lift _ _ _
  have he := (localPoint_evaluates h m a).map h g
  rw [← value_restricts e h m a] at he
  change Evaluates h (mapMatrix (awayHom a.val ≫ g) m)
    ((integralPointFunctor G).map g ((integralPointFunctor G).map (awayHom a.val) (value e h m))) at he
  rwa [← GrpCat.comp_apply, ← Functor.map_comp, hg] at he

private theorem value_eq_of_evaluates {m : SL R} {p : IntegralPoints G R} (hp : Evaluates h m p) :
    value e h m = p := by
  apply points_ext_on_cover e (pivotSet m) (pivotSet_span m)
  intro a
  exact evaluates_eq_of_injective_maps h (pointMap_injective e)
    (value_evaluates_after_map e h _ m a (IsLocalization.Away.algebraMap_isUnit a.val))
    (hp.map h (awayHom a.val))

private theorem value_natural (f : R ⟶ S) (m : SL R) :
    (integralPointFunctor G).map f (value e h m) = value e h (mapMatrix f m) := by
  apply points_ext_on_cover e (pivotSet (mapMatrix f m)) (pivotSet_span _)
  intro a
  obtain ⟨b, hb⟩ := pivot_mem_map f m a
  have hu : IsUnit ((f ≫ awayHom a.val).hom b.val) := by
    change IsUnit (algebraMap S (Localization.Away a.val) (f.hom b.val))
    rw [hb]
    exact IsLocalization.Away.algebraMap_isUnit _
  have h₁ := value_evaluates_after_map e h (f ≫ awayHom a.val) m b hu
  have h₂ := value_evaluates_after_map e h (awayHom a.val) (mapMatrix f m) a
    (IsLocalization.Away.algebraMap_isUnit a.val)
  have hp := evaluates_eq_of_injective_maps h (pointMap_injective e) h₁ h₂
  simpa only [Functor.map_comp, GrpCat.comp_apply] using hp

private theorem value_mul (m n : SL R) :
    value e h (m * n) = value e h m * value e h n := by
  apply points_ext_on_cover e (pivotSet m) (pivotSet_span m)
  intro a
  let f := awayHom a.val
  change (integralPointFunctor G).map f (value e h (m * n)) =
    (integralPointFunctor G).map f (value e h m * value e h n)
  rw [map_mul, value_natural, value_natural, value_natural, map_mul]
  have hm := value_evaluates_after_map e h f m a (IsLocalization.Away.algebraMap_isUnit a.val)
  rw [value_natural] at hm
  apply points_ext_on_cover e (pivotSet (mapMatrix f n)) (pivotSet_span _)
  intro b
  let g := awayHom b.val
  change (integralPointFunctor G).map g (value e h (mapMatrix f m * mapMatrix f n)) =
    (integralPointFunctor G).map g (value e h (mapMatrix f m) * value e h (mapMatrix f n))
  have hn := value_evaluates_after_map e h g (mapMatrix f n) b
    (IsLocalization.Away.algebraMap_isUnit b.val)
  rw [value_natural]
  apply value_eq_of_evaluates e h
  rw [(mapMatrix g).map_mul, map_mul]
  exact (hm.map h g).mul h hn

end Descent

/-- The integral rank-one relations extend the marked root and coroot maps
to a natural homomorphism on all determinant-one matrices of size two. -/
theorem rankOneExtension : Extension.{u} := by
  intro G hG h
  obtain ⟨A, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hG
  let F : rankOnePoints.{u} ⟶ integralPointFunctor G :=
    { app := fun R => GrpCat.ofHom
        { toFun := value e h
          map_one' := value_eq_of_evaluates e h ⟨[], rfl, rfl⟩
          map_mul' := value_mul e h }
      naturality := fun R S f => by
        apply GrpCat.ext
        intro m
        exact (value_natural e h f m).symm }
  refine ⟨F, ?_, ?_, ?_⟩
  · intro R x
    change value e h (upper x) = h.positive R (.ofAdd x)
    apply value_eq_of_evaluates e h
    simpa using evaluates_gauss h (Gauss.upperFactor x)
  · intro R y
    change value e h (lower y) = h.negative R (.ofAdd y)
    apply value_eq_of_evaluates e h
    simpa using evaluates_gauss h (Gauss.lowerFactor y)
  · intro R a
    change value e h (diagonal a) = h.coroot R a
    apply value_eq_of_evaluates e h
    simpa using evaluates_gauss h (Gauss.diagonalFactor a)

end

end LinearAlgebraicGroups.Classification.IntegralRankOneExtension
