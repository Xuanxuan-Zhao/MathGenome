import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.TorusLimitFactorization
import Mathlib.Algebra.Polynomial.Roots
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusAdaptedTriangularModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.TorusLimitFactorRestriction
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.UnitriangularSupportSubgroups
import Batteries.Tactic.OpenPrivate

universe u

namespace LinearAlgebraicGroups.TorusLimitFactorization

open Specs.TorusLimitFactorization Specs.Unipotent
open Specs.TorusAdaptedTriangularModel (characterValue DiagonalWeights)
open Specs.UnitriangularSupportSubgroups (HasSupport)

noncomputable section

variable {n : ℕ} {R : Type u} [CommRing R]

private abbrev Mat (n : ℕ) (R : Type u) := Matrix (Index.{u} n) (Index.{u} n) R

private def mask (q : Index.{u} n → Index.{u} n → Prop) [DecidableRel q] (x : Mat n R) : Mat n R :=
  fun i j ↦ if i < j ∧ q i j then x i j else 0

private def height (p : Index.{u} n × Index.{u} n) : ℕ :=
  p.2.down.val - p.1.down.val

private theorem left_height {i l j : Index.{u} n} (h : i < l ∧ l < j) :
    height (i, l) < height (i, j) := by
  change i.down.val < l.down.val ∧ l.down.val < j.down.val at h
  simp only [height]
  omega

private theorem right_height {i l j : Index.{u} n} (h : i < l ∧ l < j) :
    height (l, j) < height (i, j) := by
  change i.down.val < l.down.val ∧ l.down.val < j.down.val at h
  simp only [height]
  omega

private def recurrence (r q : Index.{u} n → Index.{u} n → Prop) [DecidableRel r] [DecidableRel q] (g : Mat n R)
    (p : Index.{u} n × Index.{u} n) (x : (a : Index.{u} n × Index.{u} n) → height a < height p → R) : R :=
  if p.1 < p.2 ∧ r p.1 p.2 then
    g p.1 p.2 - ∑ l : Index.{u} n, if h : p.1 < l ∧ l < p.2 then
      if (r p.1 l ∧ q p.1 l) ∧ (r l p.2 ∧ ¬ q l p.2) then
        x (p.1, l) (left_height h) * x (l, p.2) (right_height h)
      else 0
    else 0
  else 0

private def solve (r q : Index.{u} n → Index.{u} n → Prop) [DecidableRel r] [DecidableRel q] (g : Mat n R) : Mat n R :=
  fun i j ↦ (measure height).wf.fix (recurrence r q g) (i, j)

private theorem solve_eq (r q : Index.{u} n → Index.{u} n → Prop) [DecidableRel r] [DecidableRel q] (g : Mat n R)
    (i j : Index.{u} n) :
    solve r q g i j = if i < j ∧ r i j then
      g i j - (mask (fun a b ↦ r a b ∧ q a b) (solve r q g) *
        mask (fun a b ↦ r a b ∧ ¬ q a b) (solve r q g)) i j
    else 0 := by
  conv_lhs =>
    unfold solve
    rw [WellFounded.fix_eq]
  simp only [recurrence, Matrix.mul_apply]
  split
  · congr 1
    apply Finset.sum_congr rfl
    intro l _
    by_cases h : i < l ∧ l < j
    · by_cases hl : r i l ∧ q i l <;> by_cases hr : r l j ∧ ¬ q l j <;>
        simp [h, hl, hr, mask, solve]
    · rcases not_and_or.mp h with hl | hr
      · simp [hl, mask]
      · simp [hr, mask]
  · rfl

private theorem mul_mem_support {q r s : Index.{u} n → Index.{u} n → Prop} {a b : Mat n R}
    (ha : HasSupport q a) (hb : HasSupport r b)
    (hqr : ∀ i l j, q i l → r l j → s i j) :
    HasSupport s (a * b) := by
  intro i j h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro l _
  by_cases hl : i < l ∧ q i l
  · by_cases hr : l < j ∧ r l j
    · exact (h ⟨hl.1.trans hr.1, hqr i l j hl.2 hr.2⟩).elim
    · rw [hb _ _ hr, mul_zero]
  · rw [ha _ _ hl, zero_mul]

private theorem mask_support (q : Index.{u} n → Index.{u} n → Prop) [DecidableRel q] (x : Mat n R) :
    HasSupport q (mask q x) := fun _ _ h ↦ ite_eq_right h

private theorem binarySplit (r q : Index.{u} n → Index.{u} n → Prop)
    (hr : ∀ i l j, r i l → r l j → r i j)
    (g : Mat n R) (hg : HasSupport r g) :
    ∃! p : Mat n R × Mat n R, HasSupport (fun i j ↦ r i j ∧ q i j) p.1 ∧
      HasSupport (fun i j ↦ r i j ∧ ¬ q i j) p.2 ∧ p.1 + p.2 + p.1 * p.2 = g := by
  classical
  let x := solve r q g
  let a := mask (fun i j ↦ r i j ∧ q i j) x
  let b := mask (fun i j ↦ r i j ∧ ¬ q i j) x
  have ha : HasSupport (fun i j ↦ r i j ∧ q i j) a := mask_support (fun i j ↦ r i j ∧ q i j) x
  have hb : HasSupport (fun i j ↦ r i j ∧ ¬ q i j) b := mask_support (fun i j ↦ r i j ∧ ¬ q i j) x
  have hab := mul_mem_support ha hb (fun i l j h₁ h₂ ↦ hr i l j h₁.1 h₂.1)
  have hx (i j : Index.{u} n) : x i j = if i < j ∧ r i j then g i j - (a * b) i j else 0 :=
    solve_eq r q g i j
  have add_eq (i j : Index.{u} n) : a i j + b i j = x i j := by
    by_cases h : i < j ∧ r i j
    · by_cases hq : q i j <;> simp [a, b, mask, h.1, h.2, hq]
    · rw [hx, ite_eq_right h, ha _ _ (fun h' ↦ h ⟨h'.1, h'.2.1⟩),
        hb _ _ (fun h' ↦ h ⟨h'.1, h'.2.1⟩), zero_add]
  refine ⟨(a, b), ⟨ha, hb, ?_⟩, ?_⟩
  · ext i j
    change a i j + b i j + (a * b) i j = g i j
    rw [add_eq, hx]
    split
    · abel
    · rw [hab _ _ (by assumption), hg _ _ (by assumption), add_zero]
  · rintro ⟨c, d⟩ ⟨hc, hd, hcd⟩
    change HasSupport (fun i j ↦ r i j ∧ q i j) c at hc
    change HasSupport (fun i j ↦ r i j ∧ ¬ q i j) d at hd
    change c + d + c * d = g at hcd
    have c_eq (i j : Index.{u} n) : c i j = (mask (fun i j ↦ r i j ∧ q i j) (c + d)) i j := by
      unfold mask
      split
      · rename_i h
        change c i j = c i j + d i j
        rw [hd _ _ (fun h' ↦ h'.2.2 h.2.2), add_zero]
      · exact hc _ _ (by assumption)
    have d_eq (i j : Index.{u} n) : d i j = (mask (fun i j ↦ r i j ∧ ¬ q i j) (c + d)) i j := by
      unfold mask
      split
      · rename_i h
        change d i j = c i j + d i j
        rw [hc _ _ (fun h' ↦ h.2.2 h'.2.2), zero_add]
      · exact hd _ _ (by assumption)
    have u (p : Index.{u} n × Index.{u} n) : c p.1 p.2 + d p.1 p.2 = x p.1 p.2 := by
      induction p using (measure height).wf.induction with
      | h p ih =>
        obtain ⟨i, j⟩ := p
        rw [hx]
        split
        · have e : (c * d) i j = (a * b) i j := by
            simp only [Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro l _
            by_cases h : i < l ∧ l < j
            · rw [c_eq i l, d_eq l j]
              have h₁ := ih (i, l) (left_height h)
              have h₂ := ih (l, j) (right_height h)
              simp only [a, b, mask, Matrix.add_apply, h₁, h₂]
            · rcases not_and_or.mp h with h' | h'
              · rw [hc _ _ (fun h ↦ h' h.1), ha _ _ (fun h ↦ h' h.1), zero_mul, zero_mul]
              · rw [hd _ _ (fun h ↦ h' h.1), hb _ _ (fun h ↦ h' h.1), mul_zero, mul_zero]
          have h' := congrArg (fun f : Mat n R ↦ f i j) hcd
          change c i j + d i j + (c * d) i j = g i j at h'
          rw [← h', e]
          abel
        · rename_i h
          rw [hc _ _ (fun h' ↦ h ⟨h'.1, h'.2.1⟩),
            hd _ _ (fun h' ↦ h ⟨h'.1, h'.2.1⟩), zero_add]
    have u' : c + d = x := Matrix.ext fun i j ↦ u (i, j)
    apply Prod.ext
    · apply Matrix.ext
      intro i j
      change c i j = a i j
      rw [c_eq, u']
    · apply Matrix.ext
      intro i j
      change d i j = b i j
      rw [d_eq, u']

private theorem support_mono {q r : Index.{u} n → Index.{u} n → Prop} {a : Mat n R} (ha : HasSupport q a)
    (h : ∀ i j, q i j → r i j) : HasSupport r a :=
  fun i j h' ↦ ha i j (fun ⟨hij, hq⟩ ↦ h' ⟨hij, h i j hq⟩)

private theorem add_mem_support {q : Index.{u} n → Index.{u} n → Prop} {a b : Mat n R}
    (ha : HasSupport q a) (hb : HasSupport q b) : HasSupport q (a + b) :=
  fun i j h ↦ by simp only [Matrix.add_apply, ha i j h, hb i j h, add_zero]

private abbrev UT := upperUnitriangular (Index.{u} n) R

private def offDiagonal (g : UT (n := n) (R := R)) : Mat n R := g.val.val - 1

private theorem offDiagonal_support (g : UT (n := n) (R := R)) :
    HasSupport (fun _ _ ↦ True) (offDiagonal g) := by
  intro i j h
  have hij : j ≤ i := le_of_not_gt fun hl ↦ h ⟨hl, trivial⟩
  rcases lt_or_eq_of_le hij with hl | rfl
  · rw [offDiagonal, Matrix.sub_apply, g.property.1 hl, Matrix.one_apply_ne (ne_of_gt hl), sub_zero]
  · rw [offDiagonal, Matrix.sub_apply, g.property.2, Matrix.one_apply_eq, sub_self]

private def unitriangularOfStrict {q : Index.{u} n → Index.{u} n → Prop} (a : Mat n R) (ha : HasSupport q a) :
    UT (n := n) (R := R) := by
  classical
  have h : IsUpperUnitriangular (1 + a) := by
    refine ⟨fun i j h ↦ ?_, fun i ↦ ?_⟩
    · change j < i at h
      simp [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h),
        ha i j (fun h' ↦ (asymm h) h'.1)]
    · simp [Matrix.add_apply, ha i i (by simp)]
  have hd : (1 + a).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular h.1]
    simp [h.2]
  exact ⟨Matrix.GeneralLinearGroup.mk'' (1 + a) (hd ▸ isUnit_one), h⟩

private theorem offDiagonal_ofStrict {q : Index.{u} n → Index.{u} n → Prop} (a : Mat n R) (ha : HasSupport q a) :
    offDiagonal (unitriangularOfStrict a ha) = a := by
  change 1 + a - 1 = a
  abel

private theorem offDiagonal_injective : Function.Injective (offDiagonal (n := n) (R := R)) := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  exact sub_left_inj.mp e

private theorem offDiagonal_mul (g h : UT (n := n) (R := R)) :
    offDiagonal (g * h) = offDiagonal g + offDiagonal h + offDiagonal g * offDiagonal h := by
  change g.val.val * h.val.val - 1 =
    (g.val.val - 1) + (h.val.val - 1) + (g.val.val - 1) * (h.val.val - 1)
  simp only [sub_mul, mul_sub, one_mul, mul_one]
  abel

private theorem offDiagonal_one : offDiagonal (1 : UT (n := n) (R := R)) = 0 :=
  sub_self _

private theorem offDiagonal_inv_support {q : Index.{u} n → Index.{u} n → Prop}
    (hq : ∀ i j l, q i j → q j l → q i l)
    (a : UT (n := n) (R := R)) (ha : HasSupport q (offDiagonal a)) :
    HasSupport q (offDiagonal a⁻¹) := by
  classical
  let x := offDiagonal a
  let y := offDiagonal a⁻¹
  have hxy : x + y + x * y = 0 := by
    change offDiagonal a + offDiagonal a⁻¹ + offDiagonal a * offDiagonal a⁻¹ = 0
    rw [← offDiagonal_mul, mul_inv_cancel, offDiagonal_one]
  have main (p : Index.{u} n × Index.{u} n) :
      ¬ (p.1 < p.2 ∧ q p.1 p.2) → y p.1 p.2 = 0 := by
    induction p using (measure height).wf.induction with
    | h p ih =>
      obtain ⟨i, j⟩ := p
      intro h
      have hm : (x * y) i j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hil : i < l ∧ q i l
        · by_cases hlj : l < j
          · have hq' : ¬ q l j := fun h' ↦ h ⟨hil.1.trans hlj, hq i l j hil.2 h'⟩
            have hy : y l j = 0 :=
              ih (l, j) (right_height ⟨hil.1, hlj⟩) (fun h ↦ hq' h.2)
            rw [hy, mul_zero]
          · have hy : y l j = 0 := offDiagonal_support a⁻¹ l j (fun h ↦ hlj h.1)
            rw [hy, mul_zero]
        · have hx : x i l = 0 := ha i l hil
          rw [hx, zero_mul]
      have he := congrArg (fun m : Mat n R ↦ m i j) hxy
      change x i j + y i j + (x * y) i j = 0 at he
      have hx : x i j = 0 := ha i j h
      rwa [hx, hm, zero_add, add_zero] at he
  exact fun i j ↦ main (i, j)

/-- A transitive support condition on strict upper entries is closed under all group operations. -/
theorem transitiveSupportSubgroup : TransitiveSupportSubgroup.{u} := by
  intro R _ n q hq
  let S : Subgroup (UT (n := n) (R := R)) :=
    { carrier := {g | HasSupport q (offDiagonal g)}
      one_mem' := by
        change HasSupport q (offDiagonal 1)
        rw [offDiagonal_one]
        exact fun _ _ _ ↦ rfl
      mul_mem' := by
        intro a b ha hb
        change HasSupport q (offDiagonal a) at ha
        change HasSupport q (offDiagonal b) at hb
        change HasSupport q (offDiagonal (a * b))
        rw [offDiagonal_mul]
        exact add_mem_support (add_mem_support ha hb) (mul_mem_support ha hb hq)
      inv_mem' := fun {a} ha ↦ offDiagonal_inv_support hq a ha }
  exact ⟨S, fun _ ↦ Iff.rfl⟩

/-- Multiplication in sign order is bijective over every commutative coefficient ring. -/
theorem ambientFactorization : AmbientFactorization.{u} := by
  intro R _ n w g
  let neg : Index.{u} n → Index.{u} n → Prop := fun i j ↦ w i < w j
  let pos : Index.{u} n → Index.{u} n → Prop := fun i j ↦ w j < w i
  let nonneg : Index.{u} n → Index.{u} n → Prop := fun i j ↦ w j ≤ w i
  let same : Index.{u} n → Index.{u} n → Prop := fun i j ↦ w i = w j
  have hnonneg (i l j : Index.{u} n) (h₁ : nonneg i l) (h₂ : nonneg l j) : nonneg i j :=
    h₂.trans h₁
  obtain ⟨⟨a, bc⟩, ⟨ha, hbc, hg⟩, huniq⟩ :=
    binarySplit (fun _ _ ↦ True) neg (fun _ _ _ _ _ ↦ trivial) _ (offDiagonal_support g)
  have hbc' : HasSupport nonneg bc := support_mono hbc fun _ _ h ↦ le_of_not_gt h.2
  obtain ⟨⟨b, c⟩, ⟨hb, hc, hbc_eq⟩, huniq'⟩ := binarySplit nonneg pos hnonneg bc hbc'
  let na := unitriangularOfStrict a ha
  let pb := unitriangularOfStrict b hb
  let zc := unitriangularOfStrict c hc
  have ha' : offDiagonal na = a := offDiagonal_ofStrict a ha
  have hb' : offDiagonal pb = b := offDiagonal_ofStrict b hb
  have hc' : offDiagonal zc = c := offDiagonal_ofStrict c hc
  have hpbzc : offDiagonal (pb * zc) = bc := by
    rw [offDiagonal_mul, hb', hc']
    exact hbc_eq
  refine ⟨(na, pb, zc), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · change HasSupport neg (offDiagonal na)
    rw [ha']
    exact support_mono ha fun _ _ h ↦ h.2
  · change HasSupport pos (offDiagonal pb)
    rw [hb']
    exact support_mono hb fun _ _ h ↦ h.2
  · change HasSupport same (offDiagonal zc)
    rw [hc']
    exact support_mono hc fun _ _ h ↦ (le_antisymm h.1 (le_of_not_gt h.2)).symm
  · apply offDiagonal_injective
    rw [mul_assoc, offDiagonal_mul, ha', hpbzc]
    exact hg
  · rintro ⟨a', b', c'⟩ ⟨han, hbp, hcz, hprod⟩
    change HasSupport neg (offDiagonal a') at han
    change HasSupport pos (offDiagonal b') at hbp
    change HasSupport same (offDiagonal c') at hcz
    change a' * b' * c' = g at hprod
    have ha₁ : HasSupport (fun i j ↦ True ∧ neg i j) (offDiagonal a') :=
      support_mono han fun _ _ h ↦ ⟨trivial, h⟩
    have hb₁ : HasSupport (fun i j ↦ nonneg i j ∧ pos i j) (offDiagonal b') :=
      support_mono hbp fun _ _ h ↦ ⟨le_of_lt h, h⟩
    have hc₁ : HasSupport (fun i j ↦ nonneg i j ∧ ¬ pos i j) (offDiagonal c') :=
      support_mono hcz fun _ _ h ↦ ⟨le_of_eq h.symm, by rw [show pos _ _ = (_ < _) from rfl, h]; exact lt_irrefl _⟩
    have hsum : HasSupport nonneg (offDiagonal (b' * c')) := by
      rw [offDiagonal_mul]
      exact add_mem_support
        (add_mem_support (support_mono hb₁ fun _ _ h ↦ h.1) (support_mono hc₁ fun _ _ h ↦ h.1))
        (mul_mem_support hb₁ hc₁ fun i l j h₁ h₂ ↦ hnonneg i l j h₁.1 h₂.1)
    have heq : (offDiagonal a', offDiagonal (b' * c')) = (a, bc) := by
      apply huniq
      refine ⟨ha₁, support_mono hsum (fun _ _ h ↦ ⟨trivial, not_lt_of_ge h⟩), ?_⟩
      rw [← offDiagonal_mul, ← mul_assoc, hprod]
    have e₁ : offDiagonal a' = a := congrArg Prod.fst heq
    have e₂ : offDiagonal (b' * c') = bc := congrArg Prod.snd heq
    have heq' : (offDiagonal b', offDiagonal c') = (b, c) := by
      apply huniq'
      exact ⟨hb₁, hc₁, (offDiagonal_mul b' c').symm.trans e₂⟩
    exact Prod.ext (offDiagonal_injective (e₁.trans ha'.symm))
      (Prod.ext (offDiagonal_injective ((congrArg Prod.fst heq').trans hb'.symm))
        (offDiagonal_injective ((congrArg Prod.snd heq').trans hc'.symm)))

/-- A negative Laurent coefficient of an ordinary polynomial vanishes. -/
private theorem coeff_toLaurent_eq_zero_of_neg (f : Polynomial R) {m : ℤ} (hm : m < 0) :
    f.toLaurent.coeff m = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [LaurentPolynomial.support_coeff_toLaurent]
  rintro h
  obtain ⟨a, _, e⟩ := Finset.mem_map.mp h
  change (a : ℤ) = m at e
  omega

private theorem coeff_toLaurent_zero (f : Polynomial R) :
    f.toLaurent.coeff 0 = f.coeff 0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  have h := Finsupp.mapDomain_apply_of_injective (Nat.castEmbedding (R := ℤ)).injective f.toFinsupp.coeff 0
  exact h

/-- The two affine charts of the projective line have only constants in common. -/
theorem polynomialChartIntersection : PolynomialChartIntersection.{u} := by
  intro R _ f g h
  have hcoeff (m : ℤ) : f.toLaurent.coeff m = g.toLaurent.coeff (-m) :=
    (congrArg (fun p : LaurentPolynomial R ↦ p.coeff m) h).trans
      (LaurentPolynomial.invert_apply _ _)
  have h₀ : f.coeff 0 = g.coeff 0 := by
    simpa only [neg_zero, coeff_toLaurent_zero] using hcoeff 0
  refine ⟨LaurentPolynomial.ext (fun m ↦ ?_), h₀⟩
  change f.toLaurent.coeff m = (Finsupp.single 0 (f.coeff 0)) m
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · rw [coeff_toLaurent_eq_zero_of_neg f hm, Finsupp.single_eq_of_ne hm.ne]
  · rw [coeff_toLaurent_zero, Finsupp.single_eq_same]
  · rw [hcoeff, coeff_toLaurent_eq_zero_of_neg g (by omega), Finsupp.single_eq_of_ne hm.ne']

private theorem polynomialChart_constant (f g : Polynomial R)
    (h : f.toLaurent = LaurentPolynomial.invert g.toLaurent) :
    ∃ c : R, (∀ x, f.eval x = c) ∧ ∀ x, g.eval x = c := by
  obtain ⟨hf, _⟩ := polynomialChartIntersection f g h
  have hA : f = Polynomial.C (f.coeff 0) :=
    Polynomial.toLaurent_injective (hf.trans (Polynomial.toLaurent_C _).symm)
  have hB : g = Polynomial.C (f.coeff 0) := by
    apply Polynomial.toLaurent_injective
    calc
      g.toLaurent = LaurentPolynomial.invert (LaurentPolynomial.invert g.toLaurent) :=
        (LaurentPolynomial.involutive_invert _).symm
      _ = LaurentPolynomial.invert (LaurentPolynomial.C (f.coeff 0)) :=
        congrArg LaurentPolynomial.invert (h.symm.trans hf)
      _ = (Polynomial.C (f.coeff 0)).toLaurent := by simp
  exact ⟨f.coeff 0, fun x ↦ by rw [hA]; simp, fun x ↦ by rw [hB]; simp⟩

/-- Equal chart expressions force each of the three factors to preserve the line. -/
theorem stabilizingLineCharts : StabilizingLineCharts.{u} := by
  classical
  intro R J _ _ _ i A B Z c hA hB hchart
  let F (j : J) : Polynomial R := ∑ l, A j l * Polynomial.C (Z l i)
  let G (j : J) : Polynomial R := Polynomial.C (c : R) * B j i
  have eF (j : J) (x : R) :
      (F j).eval x = (A.map (Polynomial.evalRingHom x) * Z) j i := by
    simp only [F, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Matrix.mul_apply]
    rfl
  have eG (j : J) (x : R) : (G j).eval x = (c : R) * (B j i).eval x :=
    Polynomial.eval_C_mul
  have hB' (j : J) : (B j i).eval 0 = (1 : Matrix J J R) j i :=
    congrArg (fun m : Matrix J J R ↦ m j i) hB
  have constant (j : J) := polynomialChart_constant (F j) (G j) (hchart j)
  have hZ (j : J) : Z j i = (c : R) * (1 : Matrix J J R) j i := by
    obtain ⟨d, hf, hg⟩ := constant j
    have h := (hf 0).trans (hg 0).symm
    rwa [eF, hA, one_mul, eG, hB'] at h
  refine ⟨hZ, ?_, ?_⟩
  · intro j
    obtain ⟨d, hf, hg⟩ := constant j
    have h := (hf 1).trans (hg 0).symm
    rw [eF, eG, hB', Matrix.mul_apply, Finset.sum_eq_single i] at h
    · change (A j i).eval 1 * Z i i = (c : R) * (1 : Matrix J J R) j i at h
      rw [hZ i, Matrix.one_apply_eq, mul_one, mul_comm (c : R)] at h
      exact c.mul_left_inj.mp h
    · intro l _ hl
      simp [hZ l, Matrix.one_apply_ne hl]
    · simp
  · intro j
    obtain ⟨d, hf, hg⟩ := constant j
    have h := (hg 1).trans (hg 0).symm
    rw [eG, eG, hB'] at h
    exact c.mul_right_inj.mp h

/-- Conjugation by the universal diagonal cocharacter multiplies each entry
by the Laurent monomial of its weight difference. -/
theorem laurentConjugationFormula : LaurentConjugationFormula.{u} := by
  classical
  intro R _ n w a
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, laurentConjugate,
    sub_eq_add_neg, LaurentPolynomial.T_add]
  change (LaurentPolynomial.T (w i) * LaurentPolynomial.C (a i j)) *
    LaurentPolynomial.T (-w j) = _
  ac_rfl

/-- Fixing the universal Laurent parameter detects every nonzero weight difference. -/
theorem laurentFixedCriterion : LaurentFixedCriterion.{u} := by
  classical
  intro R _ n w g
  constructor
  · intro h i j hij
    by_cases hlt : i < j
    · have hne : w i ≠ w j := fun he ↦ hij ⟨hlt, he⟩
      have he := congrArg (fun a : Matrix (Index.{u} n) (Index.{u} n)
        (LaurentPolynomial R) ↦ a i j) h
      change LaurentPolynomial.C (g.val.val i j) * LaurentPolynomial.T (w i - w j) =
        LaurentPolynomial.C (g.val.val i j) at he
      rw [← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C] at he
      have hc := congrArg (fun p : LaurentPolynomial R ↦ p.coeff (w i - w j)) he
      change Finsupp.single (w i - w j) (g.val.val i j) (w i - w j) =
        Finsupp.single 0 (g.val.val i j) (w i - w j) at hc
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne (sub_ne_zero.mpr hne)] at hc
      change g.val.val i j - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j = 0
      rw [Matrix.one_apply_ne hlt.ne, sub_zero, hc]
    · exact offDiagonal_support g i j (fun h ↦ hlt h.1)
  · intro h
    apply Matrix.ext
    intro i j
    change LaurentPolynomial.C (g.val.val i j) * LaurentPolynomial.T (w i - w j) =
      LaurentPolynomial.C (g.val.val i j)
    by_cases he : w i = w j
    · simp [he]
    · have hne : i ≠ j := fun e ↦ he (congrArg w e)
      have hz := h i j (fun h' ↦ he h'.2)
      change g.val.val i j - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j = 0 at hz
      rw [Matrix.one_apply_ne hne, sub_zero] at hz
      simp [hz]

/-- The exponent of a pulled-back character is its pairing with the cocharacter. -/
theorem characterOnCocharacter : CharacterOnCocharacter.{u} := by
  classical
  intro k _ R r l m a
  change (∏ i : Index.{u} r, (a ^ l i) ^ m i) = a ^ cocharacterWeight l m
  unfold cocharacterWeight
  induction (Finset.univ : Finset (Index.{u} r)) using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      rw [Finset.prod_insert his, Finset.sum_insert his, ih, zpow_add, mul_comm (m i), zpow_mul]

/-- A unitriangular conjugation orbit extends to the identity precisely on
the positive-weight support. -/
theorem identityLimitCriterion : IdentityLimitCriterion.{u} := by
  classical
  intro R _ n w g
  constructor
  · rintro ⟨b, hb, hb₀⟩ i j hij
    by_cases hlt : i < j
    · have hle : w i ≤ w j := le_of_not_gt fun h ↦ hij ⟨hlt, h⟩
      have hentry := congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n)
        (LaurentPolynomial R) ↦ m i j) hb
      change (b.val i j).toLaurent =
        LaurentPolynomial.C (g.val.val i j) * LaurentPolynomial.T (w i - w j) at hentry
      have hcoeff := congrArg (fun p : LaurentPolynomial R ↦ p.coeff (w i - w j)) hentry
      rw [← LaurentPolynomial.single_eq_C_mul_T] at hcoeff
      change (b.val i j).toLaurent.coeff (w i - w j) =
        (Finsupp.single (w i - w j) (g.val.val i j)) (w i - w j) at hcoeff
      rw [Finsupp.single_eq_same] at hcoeff
      change g.val.val i j - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j = 0
      rw [Matrix.one_apply_ne hlt.ne, sub_zero, ← hcoeff]
      rcases lt_or_eq_of_le hle with h | h
      · exact coeff_toLaurent_eq_zero_of_neg _ (sub_neg.mpr h)
      · rw [h, sub_self, coeff_toLaurent_zero]
        have hzero := congrArg (fun m : Matrix (Index.{u} n) (Index.{u} n) R ↦ m i j) hb₀
        change (Polynomial.evalRingHom 0) (b.val i j) =
          (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j at hzero
        rw [Polynomial.coeff_zero_eq_eval_zero]
        simpa only [Polynomial.coe_evalRingHom, Matrix.one_apply_ne hlt.ne] using hzero
    · exact offDiagonal_support g i j (fun h ↦ hlt h.1)
  · intro h
    let a : Matrix (Index.{u} n) (Index.{u} n) (Polynomial R) :=
      fun i j ↦ if i < j ∧ w j < w i then
        Polynomial.monomial (w i - w j).toNat (g.val.val i j)
      else (1 : Matrix (Index.{u} n) (Index.{u} n) (Polynomial R)) i j
    have ha : IsUpperUnitriangular a := by
      refine ⟨fun i j h ↦ ?_, fun i ↦ ?_⟩
      · change j < i at h
        simp [a, not_lt_of_ge h.le, Matrix.one_apply_ne (ne_of_gt h)]
      · simp [a]
    have hd : a.det = 1 := by
      rw [Matrix.det_of_isUpperTriangular ha.1]
      simp [ha.2]
    refine ⟨Matrix.GeneralLinearGroup.mk'' a (hd ▸ isUnit_one), ?_, ?_⟩
    · apply Matrix.ext
      intro i j
      change (a i j).toLaurent =
        LaurentPolynomial.C (g.val.val i j) * LaurentPolynomial.T (w i - w j)
      by_cases hp : i < j ∧ w j < w i
      · rw [show a i j = Polynomial.monomial (w i - w j).toNat (g.val.val i j) by simp [a, hp],
          ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.toLaurent_C_mul_X_pow,
          Int.toNat_of_nonneg (sub_nonneg.mpr hp.2.le)]
      · rw [show a i j = (1 : Matrix (Index.{u} n) (Index.{u} n) (Polynomial R)) i j by simp [a, hp]]
        by_cases he : i = j
        · subst j
          simp [g.property.2]
        · have hzero : g.val.val i j = 0 := by
            have hz := h i j hp
            change g.val.val i j - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j = 0 at hz
            simpa only [Matrix.one_apply_ne he, sub_zero] using hz
          simp [Matrix.one_apply_ne he, hzero]
    · ext i j
      change (Polynomial.evalRingHom 0) (a i j) = (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j
      by_cases hp : i < j ∧ w j < w i
      · have ht : (w i - w j).toNat ≠ 0 := by
          have hpos := sub_pos.mpr hp.2
          omega
        simp [a, hp, ht,
          Matrix.one_apply_ne hp.1.ne]
      · by_cases he : i = j <;> simp [a, hp, Matrix.one_apply, he]

/-- Avoid the finitely many roots of the differences of the weight polynomials. -/
theorem separatingCocharacter : SeparatingCocharacter.{u} := by
  classical
  intro n r m
  let poly (i j : Index.{u} n) : Polynomial ℤ :=
    ∑ a : Index.{u} r, Polynomial.monomial a.down.val (m i a - m j a)
  let roots : Finset ℤ := (Finset.univ : Finset (Index.{u} n × Index.{u} n)).biUnion
    fun ij ↦ (poly ij.1 ij.2).roots.toFinset
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset roots
  refine ⟨fun a ↦ z ^ a.down.val, fun i j ↦ ⟨fun he ↦ ?_, fun h ↦ congrArg _ h⟩⟩
  by_contra hm
  have hp : poly i j ≠ 0 := by
    intro h0
    apply hm
    funext a
    have hc : (poly i j).coeff a.down.val = m i a - m j a := by
      simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        apply ite_eq_right
        intro e
        exact hb (ULift.ext (Fin.ext e))
      · simp
    rw [h0, Polynomial.coeff_zero] at hc
    exact sub_eq_zero.mp hc.symm
  apply hz
  apply Finset.mem_biUnion.mpr
  refine ⟨(i, j), Finset.mem_univ _, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr ?_)⟩
  change (poly i j).eval z = 0
  simp only [poly, Polynomial.eval_finsetSum, Polynomial.eval_monomial, sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr he

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs

set_option backward.isDefEq.respectTransparency.types false in
/-- The multiplication product identifies the right quotient with the first two factors
and the product of those factors gives its section. -/
theorem splitQuotient : SplitQuotient.{u} := by
  intro k _ U N P Z h
  let X := N.group.X ⊗ P.group.X
  let m := tripleProduct N P Z
  let s := pairProduct N P
  let z := Z.inclusion.hom.hom
  let q : U.X ⟶ X := inv m ≫ fst X Z.group.X
  have hm {S : SchemeOver k} (x : S ⟶ X) (b : S ⟶ Z.group.X) :
      lift x b ≫ m = (x ≫ s) * (b ≫ z) := by
    simp only [m, tripleProduct, MonObj.comp_mul]
    exact congrArg₂ (· * ·)
      (by simpa only [Category.assoc] using congrArg (· ≫ s) (lift_fst x b))
      (by simpa only [Category.assoc] using congrArg (· ≫ z) (lift_snd x b))
  have hq {S : SchemeOver k} (x : S ⟶ X) (b : S ⟶ Z.group.X) :
      ((x ≫ s) * (b ≫ z)) ≫ q = x := by
    rw [← hm]
    simp [q]
  have hs : s ≫ q = 𝟙 X := by
    have hz : (1 : X ⟶ Z.group.X) ≫ z = (1 : X ⟶ U.X) :=
      map_one (((yonedaGrp.map Z.inclusion).app (op X)).hom)
    simpa only [hz, one_mul, mul_one, Category.id_comp] using
      (hq (𝟙 X) (1 : X ⟶ Z.group.X))
  let last {S : SchemeOver k} (g : S ⟶ U.X) := g ≫ inv m ≫ snd X Z.group.X
  have decompose {S : SchemeOver k} (g : S ⟶ U.X) :
      g = (g ≫ q ≫ s) * (last g ≫ z) := by
    rw [← Category.assoc g q s, ← hm]
    have h' : lift (g ≫ q) (last g) = g ≫ inv m := by
      apply hom_ext <;> simp [q, last]
    simp [h']
  have rightInvariant {S : SchemeOver k} (g : S ⟶ U.X) (b : S ⟶ Z.group.X) :
      (g * (b ≫ z)) ≫ q = g ≫ q := by
    conv_lhs => rw [decompose g]
    rw [mul_assoc]
    have hb : (last g * b) ≫ z = (last g ≫ z) * (b ≫ z) :=
      map_mul (((yonedaGrp.map Z.inclusion).app (op S)).hom) _ _
    rw [← hb, ← Category.assoc g q s, hq]
  have canonical {S : SchemeOver k} (g : S ⟶ U.X) :
      QuotientGroup.mk (s := SubgroupSections Z S) (g ≫ q ≫ s) = QuotientGroup.mk g := by
    apply QuotientGroup.eq.mpr
    refine ⟨last g, ?_⟩
    change last g ≫ z = (g ≫ q ≫ s)⁻¹ * g
    calc
      last g ≫ z = (g ≫ q ≫ s)⁻¹ * ((g ≫ q ≫ s) * (last g ≫ z)) := by simp
      _ = (g ≫ q ≫ s)⁻¹ * g :=
        congrArg (fun y ↦ (g ≫ q ≫ s)⁻¹ * y) (decompose g).symm
  let C := rightCosetPresheaf Z
  let J := fppfOver k
  let Y := schemeFppfSheaf X
  let c : C ⟶ Y.obj :=
    { app := fun S ↦ ↾fun a ↦
        ⟨Quotient.lift (fun (g : S.unop ⟶ U.X) ↦ g ≫ q) (by
          intro g g' he
          obtain ⟨b, hb⟩ := QuotientGroup.leftRel_apply.mp he
          change b ≫ z = g⁻¹ * g' at hb
          have hb' : g * (b ≫ z) = g' := by rw [hb]; simp
          rw [← hb', rightInvariant]) a.down⟩
      naturality := by
        intro S T f
        ext ⟨a⟩
        induction a using QuotientGroup.induction_on with
        | H g =>
          change ULift.up ((f.unop ≫ g) ≫ q) = ULift.up (f.unop ≫ g ≫ q)
          rw [Category.assoc] }
  have hc : rightCosetProjection Z ≫ c = (J.uliftYoneda.map q).hom := rfl
  have hcb (S) : Function.Bijective (c.app S) := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ he
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective b
      change ULift.up (g ≫ q) = ULift.up (g' ≫ q) at he
      have hq' := ULift.up.inj he
      have hq'' := congrArg (fun x : S.unop ⟶ X ↦
        QuotientGroup.mk (s := SubgroupSections Z S.unop) (x ≫ s)) hq'
      exact congrArg ULift.up ((canonical g).symm.trans (hq''.trans (canonical g')))
    · rintro ⟨x⟩
      refine ⟨⟨QuotientGroup.mk (x ≫ s)⟩, ?_⟩
      change ULift.up ((x ≫ s) ≫ q) = ULift.up x
      rw [Category.assoc, hs, Category.comp_id]
  have hci (S) : IsIso (c.app S) := (CategoryTheory.isIso_iff_bijective _).2 (hcb S)
  have : IsIso c := NatIso.isIso_of_isIso_app c
  have hC : Presheaf.IsSheaf J C := (Presheaf.isSheaf_of_iso_iff (asIso c)).mpr Y.property
  have hu : IsIso (toSheafify J C) := isIso_toSheafify J hC
  let e₀ := (asIso (toSheafify J C)).symm ≪≫ asIso c
  let e : rightQuotientSheaf Z ≅ Y :=
    { hom := ⟨e₀.hom⟩
      inv := ⟨e₀.inv⟩
      hom_inv_id := by
        apply Sheaf.hom_ext
        exact e₀.hom_inv_id
      inv_hom_id := by
        apply Sheaf.hom_ext
        exact e₀.inv_hom_id }
  refine ⟨q, ⟨e, ?_⟩, hs⟩
  apply Sheaf.hom_ext
  change (rightCosetProjection Z ≫ toSheafify J C) ≫ e₀.hom = _
  have he : toSheafify J C ≫ e₀.hom = c := by simp [e₀]
  rw [Category.assoc, he, hc]

private theorem isAffineTensor {k : Type u} [Field k] {X Y : SchemeOver k}
    [IsAffine X.left] [IsAffine Y.left] : IsAffine (X ⊗ Y).left :=
  IsAffine.of_isPullback <| Over.isPullback_of_binaryFan_isLimit _
    (tensorProductIsBinaryProduct X Y)

private theorem isIsoOfAffinePoints {k : Type u} [Field k] {X Y : SchemeOver k}
    (f : X ⟶ Y) (hX : IsAffine X.left) (hY : IsAffine Y.left)
    (hf : ∀ R : TestAlgebra k, Function.Bijective (fun g : Points X R ↦ g ≫ f)) :
    IsIso f := by
  obtain ⟨A, ⟨eX⟩⟩ := essImage_algSpec.mpr hX
  obtain ⟨B, ⟨eY⟩⟩ := essImage_algSpec.mpr hY
  obtain ⟨g, hg⟩ := (hf B.unop).2 eY.hom
  change g ≫ f = eY.hom at hg
  have hgf : (eY.inv ≫ g) ≫ f = 𝟙 Y := by
    rw [Category.assoc, hg, eY.inv_hom_id]
  refine ⟨eY.inv ≫ g, ?_, hgf⟩
  apply (cancel_epi eX.hom).mp
  rw [Category.comp_id]
  apply (hf A.unop).1
  simp only [Category.assoc, hgf, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift existence and uniqueness of matrix factorizations to the affine scheme. -/
theorem multiplicationFromPointFactors : MultiplicationFromPointFactors.{u} := by
  intro k _ U N P Z n w E hinj hs hclosed
  let m := tripleProduct N P Z
  have hU := U.property.1
  have hN : IsAffine N.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup N).property.1
  have hP : IsAffine P.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup P).property.1
  have hZ : IsAffine Z.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup Z).property.1
  have hNP : IsAffine (N.group.X ⊗ P.group.X).left := isAffineTensor
  apply isIsoOfAffinePoints m isAffineTensor hU
  intro R
  let fi (a : Points N.group.X R) := a ≫ N.inclusion.hom.hom
  let fj (b : Points P.group.X R) := b ≫ P.inclusion.hom.hom
  let fk (c : Points Z.group.X R) := c ≫ Z.inclusion.hom.hom
  have eval (a : Points N.group.X R) (b : Points P.group.X R) (c : Points Z.group.X R) :
      lift (lift a b) c ≫ m = fi a * fj b * fk c := by
    have e₁ := congrArg (· ≫ pairProduct N P) (lift_fst (lift a b) c)
    have e₂ := congrArg (· ≫ Z.inclusion.hom.hom) (lift_snd (lift a b) c)
    simp only [Category.assoc] at e₁ e₂
    simp only [m, tripleProduct, MonObj.comp_mul, e₁, e₂, fk]
    apply congrArg (· * (c ≫ Z.inclusion.hom.hom))
    simp only [pairProduct, MonObj.comp_mul, fi, fj]
    exact congrArg₂ (· * ·)
      (by simpa only [Category.assoc] using congrArg (· ≫ N.inclusion.hom.hom) (lift_fst a b))
      (by simpa only [Category.assoc] using congrArg (· ≫ P.inclusion.hom.hom) (lift_snd a b))
  constructor
  · intro u v huv
    let proj₁ (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :=
      (y ≫ fst (N.group.X ⊗ P.group.X) Z.group.X) ≫ fst N.group.X P.group.X
    let proj₂ (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :=
      (y ≫ fst (N.group.X ⊗ P.group.X) Z.group.X) ≫ snd N.group.X P.group.X
    let proj₃ (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :=
      y ≫ snd (N.group.X ⊗ P.group.X) Z.group.X
    have expand (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :
        lift (lift (proj₁ y) (proj₂ y)) (proj₃ y) = y := by
      apply hom_ext
      · have e := lift_fst (lift (proj₁ y) (proj₂ y)) (proj₃ y)
        rw [e]
        apply hom_ext
        · exact lift_fst (proj₁ y) (proj₂ y)
        · exact lift_snd (proj₁ y) (proj₂ y)
      · exact lift_snd _ _
    let p (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :=
      (E R (fi (proj₁ y)), E R (fj (proj₂ y)), E R (fk (proj₃ y)))
    have hp (y : Points ((N.group.X ⊗ P.group.X) ⊗ Z.group.X) R) :
        HasSupport (fun i j ↦ w i < w j) ((p y).1.val.val - 1) ∧
        HasSupport (fun i j ↦ w j < w i) ((p y).2.1.val.val - 1) ∧
        HasSupport (fun i j ↦ w i = w j) ((p y).2.2.val.val - 1) ∧
        (p y).1 * (p y).2.1 * (p y).2.2 = E R (y ≫ m) := by
      refine ⟨(hs R _).1.mpr ⟨proj₁ y, rfl⟩, (hs R _).2.1.mpr ⟨proj₂ y, rfl⟩,
        (hs R _).2.2.mpr ⟨proj₃ y, rfl⟩, ?_⟩
      have e := eval (proj₁ y) (proj₂ y) (proj₃ y)
      rw [expand] at e
      rw [e, map_mul, map_mul]
    have heq : p u = p v := (ambientFactorization n w (E R (u ≫ m))).unique (hp u)
      ⟨(hp v).1, (hp v).2.1, (hp v).2.2.1, (hp v).2.2.2.trans (congrArg (E R) huv).symm⟩
    have h₁ : proj₁ u = proj₁ v := by
      have := N.isClosedImmersion
      have : Mono N.inclusion.hom.hom := Over.mono_of_mono_left _
      exact (cancel_mono N.inclusion.hom.hom).mp (hinj R (congrArg Prod.fst heq))
    have h₂ : proj₂ u = proj₂ v := by
      have := P.isClosedImmersion
      have : Mono P.inclusion.hom.hom := Over.mono_of_mono_left _
      exact (cancel_mono P.inclusion.hom.hom).mp (hinj R (congrArg (Prod.fst ∘ Prod.snd) heq))
    have h₃ : proj₃ u = proj₃ v := by
      have := Z.isClosedImmersion
      have : Mono Z.inclusion.hom.hom := Over.mono_of_mono_left _
      exact (cancel_mono Z.inclusion.hom.hom).mp (hinj R (congrArg (Prod.snd ∘ Prod.snd) heq))
    calc
      u = lift (lift (proj₁ u) (proj₂ u)) (proj₃ u) := (expand u).symm
      _ = lift (lift (proj₁ v) (proj₂ v)) (proj₃ v) := by rw [h₁, h₂, h₃]
      _ = v := expand v
  · intro x
    obtain ⟨⟨a, b, c⟩, ⟨ha, hb, hc, he⟩, _⟩ := ambientFactorization n w (E R x)
    obtain ⟨⟨u, eu⟩, ⟨v, ev⟩, ⟨z, ez⟩⟩ := hclosed R x a b c ha hb hc he
    obtain ⟨u', hu⟩ := (hs R u).1.mp (eu.symm ▸ ha)
    obtain ⟨v', hv⟩ := (hs R v).2.1.mp (ev.symm ▸ hb)
    obtain ⟨z', hz⟩ := (hs R z).2.2.mp (ez.symm ▸ hc)
    refine ⟨lift (lift u' v') z', ?_⟩
    change lift (lift u' v') z' ≫ m = x
    rw [eval]
    change (u' ≫ N.inclusion.hom.hom) * (v' ≫ P.inclusion.hom.hom) *
      (z' ≫ Z.inclusion.hom.hom) = x
    apply hinj R
    rw [hu, hv, hz, map_mul, map_mul, eu, ev, ez]
    exact he

open Specs.StandardGroups Specs.SmoothDiagonalKernel

private def laurentMonomialUnits (R : Type u) [CommRing R] :
    Multiplicative ℤ →* (LaurentPolynomial R)ˣ where
  toFun a := (LaurentPolynomial.isUnit_T (R := R) a.toAdd).unit
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by
    simpa only [Units.val_mul, IsUnit.unit_spec, toAdd_mul] using
      (LaurentPolynomial.T_add (R := R) a.toAdd b.toAdd))

private theorem laurentMonomialUnits_zpow (R : Type u) [CommRing R] (d : ℤ) :
    ((laurentMonomialUnits R (Multiplicative.ofAdd 1) ^ d :
      (LaurentPolynomial R)ˣ) : LaurentPolynomial R) = LaurentPolynomial.T d := by
  rw [← map_zpow, ← ofAdd_zsmul]
  simp [laurentMonomialUnits, IsUnit.unit_spec]

variable {k : Type u} [Field k]

private abbrev matrixPointHom {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    (R : TestAlgebra k) : Points G.X R →* Matrix.GeneralLinearGroup (Index.{u} n) R :=
  (e.hom.app R).hom.comp (((groupPointsFunctor k).map j).app R).hom

set_option maxHeartbeats 1000000 in
private theorem matrixPoint_natural {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    {R S : TestAlgebra k} (f : R ⟶ S) (x : Points G.X R) :
    matrixPoint j e S (mapPoints f x) =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (matrixPoint j e R x) :=
  (((groupPointsFunctor k).map j) ≫ e.hom).naturality_apply f x

private theorem matrixPoint_injective {n : ℕ} {G H : GroupScheme k} (j : G ⟶ H)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    (hj : IsClosedImmersion j.hom.hom.left) (R : TestAlgebra k) :
    Function.Injective (matrixPointHom j e R) := by
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  intro x y hxy
  apply (cancel_mono j.hom.hom).mp
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1 hxy

private theorem diagonal_commute_iff {J S : Type u} [Fintype J] [DecidableEq J] [CommRing S]
    (a : Matrix J J S) (d : J → S) :
    Commute a (Matrix.diagonal d) ↔ ∀ i j, a i j * d j = d i * a i j := by
  constructor
  · intro h i j
    simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using
      congrArg (fun a : Matrix J J S ↦ a i j) h.eq
  · intro h
    exact Matrix.ext fun i j ↦ by
      simpa only [Matrix.mul_diagonal, Matrix.diagonal_mul] using h i j

set_option backward.isDefEq.respectTransparency.types false in
/-- The universal Laurent torus point detects all nonzero weight differences,
including over finite fields and over nonreduced coefficient rings. -/
theorem torusCentralizerCriterion : TorusCentralizerCriterion.{u} := by
  classical
  intro k _ G H n r j U T e t m l hj hd hsep R x
  let w : Index.{u} n → ℤ := fun i ↦ cocharacterWeight l (m i)
  let A := matrixPoint (U.inclusion ≫ j) e R x
  change IsUpperUnitriangular A.val →
    (HasSupport (fun i j' ↦ w i = w j') (A.val - 1) ↔
      CentralizesTorus U.inclusion T x)
  intro hA
  constructor
  · intro h S f a
    apply Commute.of_map (f := matrixPointHom j e S) (matrixPoint_injective j e hj S)
    let d (i : Index.{u} n) : S := characterValue (m i) (t.hom.app S a)
    have hdiag : (matrixPoint (T.inclusion ≫ j) e S a).val = Matrix.diagonal d :=
      Matrix.ext fun i j' ↦ hd S a i j'
    change Commute (matrixPoint (U.inclusion ≫ j) e S (mapPoints f x))
      (matrixPoint (T.inclusion ≫ j) e S a)
    apply Units.ext
    change Commute (matrixPoint (U.inclusion ≫ j) e S (mapPoints f x)).val
      (matrixPoint (T.inclusion ≫ j) e S a).val
    rw [hdiag, matrixPoint_natural]
    apply (diagonal_commute_iff _ _).2
    intro i j'
    by_cases hm : m i = m j'
    · have hh : d i = d j' := congrArg (fun v ↦ (characterValue v (t.hom.app S a) : S)) hm
      rw [hh, mul_comm]
    · have hw : w i ≠ w j' := fun he ↦ hm ((hsep i j').mp he)
      have hij : i ≠ j' := fun he ↦ hw (congrArg w he)
      have hz := h i j' (fun h' ↦ hw h'.2)
      change A.val i j' - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j' = 0 at hz
      rw [Matrix.one_apply_ne hij, sub_zero] at hz
      change f.hom (A.val i j') * d j' = d i * f.hom (A.val i j')
      rw [hz, map_zero, zero_mul, mul_zero]
  · intro h i j' hneg
    by_cases hlt : i < j'
    · have hne : w i ≠ w j' := fun he ↦ hneg ⟨hlt, he⟩
      let S := CommAlgCat.of k (LaurentPolynomial R)
      let f : R ⟶ S := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (LaurentPolynomial R))
      let tau : Sˣ := laurentMonomialUnits R (Multiplicative.ofAdd 1)
      let a : Points T.group.X S := t.inv.app S (fun i ↦ tau ^ l i)
      have hat : t.hom.app S a = (fun i ↦ tau ^ l i) :=
        t.inv_hom_id_app_apply S _
      have hd' : (matrixPoint (T.inclusion ≫ j) e S a).val =
          Matrix.diagonal (fun i ↦ LaurentPolynomial.T (w i)) := by
        apply Matrix.ext
        intro i j'
        have hc : characterValue (m i) (fun i ↦ tau ^ l i) = tau ^ cocharacterWeight l (m i) :=
          characterOnCocharacter r l (m i) tau
        rw [hd S a, hat, hc]
        exact congrArg (fun z : LaurentPolynomial R ↦ if i = j' then z else 0)
          (laurentMonomialUnits_zpow R _)
      have hcomm := (h S f a).map (matrixPointHom j e S)
      change Commute (matrixPoint (U.inclusion ≫ j) e S (mapPoints f x))
        (matrixPoint (T.inclusion ≫ j) e S a) at hcomm
      have hmat := hcomm.map (Units.coeHom (M := Matrix (Index.{u} n) (Index.{u} n) S))
      change Commute (matrixPoint (U.inclusion ≫ j) e S (mapPoints f x)).val
        (matrixPoint (T.inclusion ≫ j) e S a).val at hmat
      rw [matrixPoint_natural, hd'] at hmat
      have hi := (diagonal_commute_iff _ _).mp hmat i j'
      change LaurentPolynomial.C (A.val i j') * LaurentPolynomial.T (w j') =
        LaurentPolynomial.T (w i) * LaurentPolynomial.C (A.val i j') at hi
      rw [mul_comm (LaurentPolynomial.T (w i)), ← LaurentPolynomial.single_eq_C_mul_T,
        ← LaurentPolynomial.single_eq_C_mul_T] at hi
      have hv := congrArg (fun p : LaurentPolynomial R ↦ p.coeff (w j')) hi
      change Finsupp.single (w j') (A.val i j') (w j') =
        Finsupp.single (w i) (A.val i j') (w j') at hv
      rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne.symm] at hv
      change A.val i j' - (1 : Matrix (Index.{u} n) (Index.{u} n) R) i j' = 0
      rw [Matrix.one_apply_ne hlt.ne, sub_zero, hv]
    · exact offDiagonal_support (⟨A, hA⟩ : UT (n := n) (R := R)) i j' (fun e ↦ hlt e.1)

open private affineSpec quotientProjection factorsThrough_affineQuotient
  closedImmersion_over_affineSpec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.FixedPointSchemes

set_option backward.isDefEq.respectTransparency.types false in
/-- If the pullback of an affine family along an injective test-ring map lies in a
closed subscheme, its defining ideal already vanishes on the original family. -/
theorem closedPointsAlongInjection : ClosedPointsAlongInjection.{u} := by
  intro k _ X Y j hY hj R S f hf x ⟨y, hy⟩
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hY
  let j' := j ≫ e.inv
  let x' := x ≫ e.inv
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  have hj' : IsClosedImmersion j'.left := by
    have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
    change IsClosedImmersion (j.left ≫ e.inv.left)
    infer_instance
  obtain ⟨I, d, hd⟩ := closedImmersion_over_affineSpec (A := A.unop) j' hj'
  let q := (testSpec k).map (quotientProjection I).op
  let g := (F.preimage x').unop
  have hg : (testSpec k).map g.op = x' := F.map_preimage _
  have hfg : (testSpec k).map (g ≫ f).op = mapPoints f x' := by
    change (testSpec k).map (f.op ≫ g.op) = (testSpec k).map f.op ≫ x'
    rw [Functor.map_comp, hg]
  have hfac : (y ≫ d.hom) ≫ q = (testSpec k).map (g ≫ f).op := by
    rw [hfg, Category.assoc]
    change y ≫ (d.hom ≫ (testSpec k).map (quotientProjection I).op) = _
    rw [← hd]
    change y ≫ j ≫ e.inv = mapPoints f (x ≫ e.inv)
    rw [← Category.assoc, hy]
    exact Category.assoc _ _ _
  have hin := (factorsThrough_affineQuotient I ((testSpec k).map (g ≫ f).op)).mp
    ⟨y ≫ d.hom, hfac⟩
  change I ≤ RingHom.ker (F.preimage ((testSpec k).map (g ≫ f).op)).unop.hom.toRingHom at hin
  rw [F.preimage_map] at hin
  have hk : I ≤ RingHom.ker g.hom.toRingHom := by
    intro a ha
    apply RingHom.mem_ker.mpr
    apply hf
    have hh := RingHom.mem_ker.mp (hin ha)
    change f.hom (g.hom a) = 0 at hh
    change f.hom (g.hom a) = f.hom 0
    rw [hh, map_zero]
  obtain ⟨z, hz⟩ := (factorsThrough_affineQuotient I x').mpr hk
  refine ⟨z ≫ d.inv, ?_⟩
  apply (cancel_mono e.inv).mp
  calc
    (z ≫ d.inv) ≫ j ≫ e.inv = z ≫ d.inv ≫ j' := by simp [j']
    _ = z ≫ q := by simp [hd, q]
    _ = x' := hz

private theorem matrixPoint_comp {n : ℕ} {A B C : GroupScheme k} (f : A ⟶ B) (g : B ⟶ C)
    (e : (groupPointsFunctor k).obj C ≅ generalLinearPoints k (Index.{u} n))
    (R : TestAlgebra k) (x : Points A.X R) :
    matrixPoint (f ≫ g) e R x = matrixPoint g e R (x ≫ f.hom.hom) := by
  simp only [matrixPoint, Functor.map_comp]
  rfl

open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

/-- In a triangular realization the radical consists of the points with unit diagonal. -/
private theorem radicalPoints_iff_unitriangular {n : ℕ} {G H : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (hs : SchemeDerivedGroup.IsSplitSolvable G.val)
    (hj : IsClosedImmersion j.hom.hom.left) (htri : IsUpperTriangular j e)
    (U : ClosedSubgroup G.val) (hu : IsUnipotent (closedSubgroupAlgebraicGroup U))
    (hmax : ∀ V : ClosedSubgroup G.val, IsUnipotent (closedSubgroupAlgebraicGroup V) →
      SchemeDerivedGroup.IsSubgroupOf V U) :
    ∀ (R : TestAlgebra k) (x : Points G.val.X R),
      IsUpperUnitriangular (matrixPoint j e R x).val ↔
        ∃ y : Points U.group.X R, y ≫ U.inclusion.hom.hom = x := by
  let A := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroup k (Index.{u} n)
  let t := LinearAlgebraicGroups.StandardGroups.multiplicativePowerGroupPointsIso k (Index.{u} n)
  obtain ⟨d, D, p, i, V, hV, _⟩ :=
    SplitSolvableRadical.splitKernelOfTriangularization n G H A j e t hs hj htri
  obtain ⟨hd, _, _, hker, _, _, _, _, _, hv, hvmax⟩ := hV
  obtain ⟨f, hf⟩ := hvmax U hu
  obtain ⟨g, hg⟩ := hmax V hv
  intro R x
  have hx : IsUpperUnitriangular (matrixPoint j e R x).val ↔
      x ≫ d.hom.hom = 1 := by
    let v : Points A.val.X R := x ≫ d.hom.hom
    let tR : Points A.val.X R →* (Index.{u} n → Rˣ) := (t.hom.app R).hom
    have htR : Function.Injective tR := (ConcreteCategory.bijective_of_isIso (t.hom.app R)).injective
    have hdiag (i : Index.{u} n) : (tR v i : R) = (matrixPoint j e R x).val i i := hd R x i
    refine ⟨fun h ↦ htR ?_, fun h ↦ ⟨htri R x, fun i ↦ ?_⟩⟩
    · change tR v = tR 1
      rw [map_one]
      funext i
      apply Units.ext
      exact (hdiag i).trans (h.2 i)
    · change v = 1 at h
      exact (hdiag i).symm.trans (by simp only [h, map_one, Pi.one_apply, Units.val_one])
  have hxV : (∃ y : Points V.group.X R, y ≫ V.inclusion.hom.hom = x) ↔
      x ≫ d.hom.hom = 1 := schemeKernel_sections hker x
  rw [hx, ← hxV]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ g.hom.hom, ?_⟩
    rw [Category.assoc, show g.hom.hom ≫ U.inclusion.hom.hom = V.inclusion.hom.hom
      from congrArg (fun a : V.group ⟶ G.val ↦ a.hom.hom) hg, hy]
  · rintro ⟨y, hy⟩
    refine ⟨y ≫ f.hom.hom, ?_⟩
    rw [Category.assoc, show f.hom.hom ≫ V.inclusion.hom.hom = U.inclusion.hom.hom
      from congrArg (fun a : U.group ⟶ G.val ↦ a.hom.hom) hf, hy]

/-- The universal Laurent unit to an integral power gives the diagonal cocharacter
matrix for that power of the parameter. -/
private theorem cocharacterLaurentMatrix {n r : ℕ} {G H T : GroupScheme k}
    (j : G ⟶ H) (iT : T ⟶ G)
    (e : (groupPointsFunctor k).obj H ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} r))
    (m : Index.{u} n → Index.{u} r → ℤ) (l : Index.{u} r → ℤ)
    (hd : ∀ (S : TestAlgebra k) (a : Points T.X S) (i j' : Index.{u} n),
      (matrixPoint (iT ≫ j) e S a).val i j' =
        if i = j' then (characterValue (m i) (t.hom.app S a) : S) else 0)
    (R : TestAlgebra k) (d : ℤ) :
    let S := CommAlgCat.of k (LaurentPolynomial R)
    let τ : Sˣ := laurentMonomialUnits R (Multiplicative.ofAdd 1)
    let a := (cocharacterPoints t l).app S (τ ^ d)
    (matrixPoint (iT ≫ j) e S a).val =
      Matrix.diagonal (fun i ↦ LaurentPolynomial.T (d * cocharacterWeight l (m i))) := by
  intro S τ a
  have ha : t.hom.app S a = (fun i ↦ (τ ^ d) ^ l i) :=
    t.inv_hom_id_app_apply S _
  apply Matrix.ext
  intro i j'
  refine (hd S a i j').trans ?_
  have hp : characterValue (m i) (fun s ↦ (τ ^ d) ^ l s) =
      (τ ^ d) ^ cocharacterWeight l (m i) :=
    characterOnCocharacter r l (m i) (τ ^ d)
  rw [ha, hp, ← zpow_mul]
  change (if i = j' then ((τ ^ (d * cocharacterWeight l (m i)) : Sˣ) : S) else 0) =
    (Matrix.diagonal (fun i ↦ LaurentPolynomial.T (d * cocharacterWeight l (m i)))) i j'
  rw [laurentMonomialUnits_zpow]
  by_cases hij : i = j' <;> simp [hij]

set_option backward.isDefEq.respectTransparency.types false in
/-- A polynomial extension of the matrix orbit lifts to the radical by closedness.
In both charts the restriction to the Laurent algebra is the conjugate in the radical. -/
private theorem groupIdentityLimit_iff_matrix {n r : ℕ} {G H : AffineAlgebraicGroup k}
    (j : G.val ⟶ H.val) (U T : ClosedSubgroup G.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
    (m : Index.{u} n → Index.{u} r → ℤ) (l : Index.{u} r → ℤ)
    (hj : IsClosedImmersion j.hom.hom.left) (hn : IsNormalSubgroup U.inclusion)
    (hd : DiagonalWeights (T.inclusion ≫ j) e t m)
    (atInfinity : Bool) (R : TestAlgebra k) (x : Points U.group.X R) :
    HasGroupIdentityLimit U T t l atInfinity x ↔
      HasIdentityLimit (fun i ↦ (if atInfinity then (-1 : ℤ) else 1) * cocharacterWeight l (m i))
        (matrixPoint (U.inclusion ≫ j) e R x) := by
  let RP := CommAlgCat.of k (Polynomial R)
  let RL := CommAlgCat.of k (LaurentPolynomial R)
  let zero : RP ⟶ R := CommAlgCat.ofHom ((Polynomial.aeval (0 : R) :
    Polynomial R →ₐ[R] R).restrictScalars k)
  let punctured : RP ⟶ RL := CommAlgCat.ofHom (Polynomial.toLaurentAlg.restrictScalars k)
  let constant : R ⟶ RL := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (LaurentPolynomial R))
  let τ : RLˣ := laurentMonomialUnits R (Multiplicative.ofAdd 1)
  let d : ℤ := if atInfinity then -1 else 1
  let w (i : Index.{u} n) := d * cocharacterWeight l (m i)
  let c : RLˣ →* Points T.group.X RL := ((cocharacterPoints t l).app RL).hom
  let a : Points T.group.X RL := c (τ ^ d)
  let b : Points G.val.X RL := a ≫ T.inclusion.hom.hom
  let f := U.inclusion ≫ j
  let orbit : Points G.val.X RL :=
    b * (mapPoints constant x ≫ U.inclusion.hom.hom) * b⁻¹
  have hparameter : (if atInfinity then τ⁻¹ else τ) = τ ^ d := by
    cases atInfinity <;> simp [d]
  change (∃ y : Points U.group.X RP, mapPoints zero y = 1 ∧
    mapPoints punctured y ≫ U.inclusion.hom.hom =
      (c (if atInfinity then τ⁻¹ else τ) ≫ T.inclusion.hom.hom) *
        (mapPoints constant x ≫ U.inclusion.hom.hom) *
        (c (if atInfinity then τ⁻¹ else τ) ≫ T.inclusion.hom.hom)⁻¹) ↔
    HasIdentityLimit w (matrixPoint f e R x)
  rw [hparameter]
  change (∃ y : Points U.group.X RP, mapPoints zero y = 1 ∧
    mapPoints punctured y ≫ U.inclusion.hom.hom = orbit) ↔ _
  have hf : IsClosedImmersion f.hom.hom.left := by
    have := U.isClosedImmersion
    exact IsClosedImmersion.comp U.inclusion.hom.hom.left j.hom.hom.left
  have hb : (matrixPoint j e RL b).val = Matrix.diagonal (fun i ↦ LaurentPolynomial.T (w i)) := by
    change (matrixPoint j e RL (a ≫ T.inclusion.hom.hom)).val = _
    rw [← matrixPoint_comp]
    exact cocharacterLaurentMatrix j T.inclusion e t m l hd R d
  have hbi : b⁻¹ = c (τ ^ (-d)) ≫ T.inclusion.hom.hom := by
    let iT : Points T.group.X RL →* Points G.val.X RL :=
      (((groupPointsFunctor k).map T.inclusion).app RL).hom
    change (iT (c (τ ^ d)))⁻¹ = iT (c (τ ^ (-d)))
    rw [zpow_neg, map_inv, map_inv]
  have hb_inv : (matrixPoint j e RL b⁻¹).val =
      Matrix.diagonal (fun i ↦ LaurentPolynomial.T (-w i)) := by
    erw [hbi]
    rw [← matrixPoint_comp]
    have h := cocharacterLaurentMatrix j T.inclusion e t m l hd R (-d)
    change (matrixPoint (T.inclusion ≫ j) e RL (c (τ ^ (-d)))).val =
      Matrix.diagonal (fun i ↦ LaurentPolynomial.T ((-d) * cocharacterWeight l (m i))) at h
    simpa only [w, neg_mul] using h
  have horbit : (matrixPoint j e RL orbit).val = laurentConjugate w (matrixPoint f e R x).val := by
    change (matrixPointHom j e RL (b * (mapPoints constant x ≫ U.inclusion.hom.hom) * b⁻¹)).val = _
    rw [map_mul, map_mul]
    change (matrixPoint j e RL b).val * (matrixPoint j e RL
      (mapPoints constant x ≫ U.inclusion.hom.hom)).val * (matrixPoint j e RL b⁻¹).val = _
    rw [hb, hb_inv, ← matrixPoint_comp, matrixPoint_natural]
    exact laurentConjugationFormula n w _
  have hzero (y : Points U.group.X RP) :
      (matrixPoint f e RP y).val.map (Polynomial.evalRingHom 0) =
        (matrixPoint f e R (mapPoints zero y)).val := by
    exact (congrArg Units.val (matrixPoint_natural f e zero y)).symm
  have hpunctured (y : Points U.group.X RP) :
      (matrixPoint f e RP y).val.map Polynomial.toLaurent =
        (matrixPoint f e RL (mapPoints punctured y)).val :=
    (congrArg Units.val (matrixPoint_natural f e punctured y)).symm
  have hone : (matrixPoint f e R (1 : Points U.group.X R)).val = 1 :=
    congrArg Units.val (map_one (matrixPointHom f e R))
  constructor
  · rintro ⟨y, hy₀, hy⟩
    refine ⟨matrixPoint f e RP y, ?_, ?_⟩
    · rw [hpunctured, matrixPoint_comp, hy, horbit]
    · rw [hzero, hy₀, hone]
  · rintro ⟨p, hp, hp₀⟩
    let v : Points H.val.X RP := e.inv.app RP p
    have hv : e.hom.app RP v = p := e.inv_hom_id_app_apply RP p
    have hvL : (e.hom.app RL (mapPoints punctured v)).val = p.val.map Polynomial.toLaurent := by
      have hvn := e.hom.naturality_apply punctured v
      change e.hom.app RL (mapPoints punctured v) =
        Matrix.GeneralLinearGroup.map Polynomial.toLaurent (e.hom.app RP v) at hvn
      rw [hvn, hv]
      rfl
    obtain ⟨yL, hyL⟩ := normalSubgroup_conjugate_sections hn b (mapPoints constant x)
    have hrestrict : yL ≫ f.hom.hom = mapPoints punctured v := by
      apply (ConcreteCategory.bijective_of_isIso (e.hom.app RL)).injective
      apply Units.ext
      change (matrixPoint f e RL yL).val = (e.hom.app RL (mapPoints punctured v)).val
      rw [matrixPoint_comp, hyL, hvL, hp]
      exact horbit
    obtain ⟨y, hy⟩ := closedPointsAlongInjection f.hom.hom H.property.1 hf punctured
      Polynomial.toLaurent_injective v ⟨yL, hrestrict⟩
    have hyMatrix : matrixPoint f e RP y = p := by
      change e.hom.app RP (y ≫ f.hom.hom) = p
      rw [hy, hv]
    refine ⟨y, ?_, ?_⟩
    · apply matrixPoint_injective f e hf R
      apply Units.ext
      change (matrixPoint f e R (mapPoints zero y)).val =
        (matrixPoint f e R (1 : Points U.group.X R)).val
      rw [← hzero, hyMatrix, hp₀, hone]
    · apply matrixPoint_injective j e hj RL
      apply Units.ext
      change (matrixPoint j e RL (mapPoints punctured y ≫ U.inclusion.hom.hom)).val =
        (matrixPoint j e RL orbit).val
      rw [← matrixPoint_comp, ← hpunctured, hyMatrix, hp, horbit]

set_option backward.isDefEq.respectTransparency.types false in
/-- The pointwise test for centralization is the scheme-theoretic centralizer condition. -/
private theorem centralizesTorus_iff {G : AffineAlgebraicGroup k} (U T : ClosedSubgroup G.val)
    (R : TestAlgebra k) (x : Points U.group.X R) :
    CentralizesTorus U.inclusion T x ↔ Centralizes T.inclusion (x ≫ U.inclusion.hom.hom) := by
  let X := (testSpec k).obj (op R)
  constructor
  · intro h
    have : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
    have : IsAffine X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
    have hX : IsAffine (T.group.X ⊗ X).left := isAffineTensor
    obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hX
    let f : R ⟶ A.unop :=
      ((algSpec.fullyFaithful (R := CommRingCat.of k)).preimage (e.hom ≫ snd T.group.X X)).unop
    have hf : (testSpec k).map f.op = e.hom ≫ snd T.group.X X :=
      (algSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage _
    let a : Points T.group.X A.unop := e.hom ≫ fst T.group.X X
    have hc := h A.unop f a
    change Commute (((testSpec k).map f.op ≫ x) ≫ U.inclusion.hom.hom)
      (a ≫ T.inclusion.hom.hom) at hc
    rw [hf] at hc
    apply (cancel_epi e.hom).mp
    simpa only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc, a] using
      mul_inv_eq_iff_eq_mul.mpr hc.eq
  · intro h S f a
    change Commute (((testSpec k).map f.op ≫ x) ≫ U.inclusion.hom.hom)
      (a ≫ T.inclusion.hom.hom)
    have hc := congrArg (fun q ↦ lift a ((testSpec k).map f.op) ≫ q) h
    simp only [conjugateFamily, MonObj.comp_mul, GrpObj.comp_inv,
      lift_fst_assoc, lift_snd_assoc] at hc
    exact mul_inv_eq_iff_eq_mul.mp (by simpa only [Category.assoc] using hc)

open Specs.DiagonalizableGroups (IntegerCharacters integerGenerator groupAlgebra)
open private integerPointsIso pointsIso_spec from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups

set_option backward.isDefEq.respectTransparency.types false in
/-- Integral powers in split coordinates define a cocharacter of the torus. -/
private theorem realizesCocharacter {r : ℕ} {T : GroupScheme k}
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} r))
    (l : Index.{u} r → ℤ) : RealizesCocharacter t l := by
  let A := groupAlgebra k IntegerCharacters
  let g := DiagonalizableGroups.groupAlgebraPointsIso k IntegerCharacters
  let e := g ≪≫ integerPointsIso (k := k)
  let F := groupHomEquiv (specGroup A) T ((affineHopfSpec k).obj (op A)).property
  let alpha := e.hom ≫ cocharacterPoints t l
  refine ⟨F.symm alpha, ?_⟩
  intro R a
  have hf : (groupPointsFunctor k).map (F.symm alpha) = alpha := F.apply_symm_apply _
  change ((groupPointsFunctor k).map (F.symm alpha)).app R (multiplicativeParameter R a) = _
  rw [hf]
  have ha : e.hom.app R (multiplicativeParameter R a) = a := by
    let powers : IntegerCharacters.{u} →* Rˣ := (zpowersHom Rˣ a).comp MulEquiv.ulift.toMonoidHom
    let h := MonoidAlgebra.lift k R IntegerCharacters ((Units.coeHom (M := R)).comp powers)
    apply Units.ext
    change ((show IntegerCharacters →* Rˣ from g.hom.app R
      ((hopfSpecPointIso A).hom.app R (WithConv.toConv h))) integerGenerator).val = (a : R)
    rw [pointsIso_spec, MonoidAlgebra.lift_single, one_smul]
    change (a ^ (1 : ℤ) : Rˣ).val = (a : R)
    rw [zpow_one]
  change (cocharacterPoints t l).app R (e.hom.app R (multiplicativeParameter R a)) = _
  rw [ha]

set_option backward.isDefEq.respectTransparency.types false in
/-- The two intrinsic limit subgroups and the torus centralizer multiply
isomorphically onto the radical. The product of the limit subgroups gives a
section of the homogeneous right quotient by the centralizer. -/
theorem factorization : Factorization.{u} := by
  classical
  intro k _ G D p U T hsplit _ _ _ _ hn hT _ hu hmax
  obtain ⟨n, r, H, j, e, t, m, hj, htri, hd⟩ :=
    TorusAdaptedTriangularModel.existsTorusAdaptedTriangularModel G T hsplit hT
  obtain ⟨l, hsep⟩ := separatingCocharacter n r m
  let w (i : Index.{u} n) := cocharacterWeight l (m i)
  let U' := closedSubgroupAlgebraicGroup U
  let f : U.group ⟶ H.val := U.inclusion ≫ j
  let E := (groupPointsFunctor k).map f ≫ e.hom
  have hrad := radicalPoints_iff_unitriangular j e hsplit hj htri U hu hmax
  have hf : IsClosedImmersion f.hom.hom.left := by
    have := U.isClosedImmersion
    exact IsClosedImmersion.comp U.inclusion.hom.hom.left j.hom.hom.left
  have hEinj (R : TestAlgebra k) : Function.Injective (E.app R) :=
    matrixPoint_injective f e hf R
  have hE (R : TestAlgebra k) (x : Points U.group.X R) :
      IsUpperUnitriangular (matrixPoint f e R x).val := by
    change IsUpperUnitriangular (matrixPoint (U.inclusion ≫ j) e R x).val
    rw [matrixPoint_comp U.inclusion j]
    exact (hrad R _).mpr ⟨x, rfl⟩
  let E₀ (R : TestAlgebra k) : Points U.group.X R →* upperUnitriangular (Index.{u} n) R :=
    (matrixPointHom f e R).codRestrict _ (hE R)
  have hE₀inj (R : TestAlgebra k) : Function.Injective (E₀ R) := by
    intro x y h
    exact hEinj R (congrArg Subtype.val h)
  obtain ⟨N, hN⟩ := UnitriangularSupportSubgroups.closedSubgroupOfSupport U' n E hEinj hE
    (fun i j ↦ w i < w j) (fun _ _ _ ↦ lt_trans)
  obtain ⟨P, hP⟩ := UnitriangularSupportSubgroups.closedSubgroupOfSupport U' n E hEinj hE
    (fun i j ↦ w j < w i) (fun _ _ _ h h' ↦ lt_trans h' h)
  obtain ⟨Z, hZ⟩ := UnitriangularSupportSubgroups.closedSubgroupOfSupport U' n E hEinj hE
    (fun i j ↦ w i = w j) (fun _ _ _ ↦ Eq.trans)
  have hstay (R : TestAlgebra k) (x : Points U.group.X R)
      (a b z : upperUnitriangular (Index.{u} n) R)
      (ha : HasSupport (fun i j ↦ w i < w j) (a.val.val - 1))
      (hb : HasSupport (fun i j ↦ w j < w i) (b.val.val - 1))
      (hz : HasSupport (fun i j ↦ w i = w j) (z.val.val - 1))
      (he : a * b * z = E₀ R x) :
      a ∈ (E₀ R).range ∧ b ∈ (E₀ R).range ∧ z ∈ (E₀ R).range := by
    have hprod : (a * b * z).val ∈ Set.range (matrixPointHom j e R) := by
      refine ⟨x ≫ U.inclusion.hom.hom, ?_⟩
      change matrixPoint j e R (x ≫ U.inclusion.hom.hom) = (a * b * z).val
      rw [← matrixPoint_comp]
      exact congrArg Subtype.val he.symm
    obtain ⟨ha', hb', hz'⟩ :=
      TorusLimitFactorRestriction.factorRestriction j T e t m l hj hd R a b z ha hb hz hprod
    have liftFactor (g : upperUnitriangular (Index.{u} n) R)
        (hg : g.val ∈ Set.range (matrixPointHom j e R)) : g ∈ (E₀ R).range := by
      obtain ⟨y, hy⟩ := hg
      change matrixPoint j e R y = g.val at hy
      have hyU : IsUpperUnitriangular (matrixPoint j e R y).val := hy.symm ▸ g.property
      obtain ⟨v, hv⟩ := (hrad R y).mp hyU
      refine ⟨v, Subtype.ext ?_⟩
      change matrixPoint (U.inclusion ≫ j) e R v = g.val
      rw [matrixPoint_comp, hv]
      exact hy
    exact ⟨liftFactor a ha', liftFactor b hb', liftFactor z hz'⟩
  have hmul : IsIso (tripleProduct N P Z) :=
    multiplicationFromPointFactors U' N P Z n w E₀ hE₀inj
      (fun R x ↦ ⟨hN R x, hP R x, hZ R x⟩) hstay
  refine ⟨n, r, H, j, e, t, m, l, N, P, Z, hj, htri, hd, hsep, realizesCocharacter t l, ?_,
    hmul, splitQuotient N P Z hmul⟩
  dsimp only
  intro R x
  have hcentral := (torusCentralizerCriterion j U T e t m l hj hd hsep R x (hE R x)).trans
    (centralizesTorus_iff U T R x)
  refine ⟨hE R x, ?_, ?_, hcentral, hcentral.symm.trans (hZ R x)⟩
  · have hlimit : HasGroupIdentityLimit U T t l true x ↔
        HasIdentityLimit (fun i ↦ -w i) (E₀ R x).val := by
      change HasGroupIdentityLimit U T t l true x ↔
        HasIdentityLimit (fun i ↦ -cocharacterWeight l (m i)) (matrixPoint (U.inclusion ≫ j) e R x)
      simpa only [eq_self, ite_true, neg_one_mul] using
        groupIdentityLimit_iff_matrix j U T e t m l hj hn hd true R x
    have hsign : HasIdentityLimit (fun i ↦ -w i) (E₀ R x).val ↔
        HasSupport (fun i j ↦ w i < w j) ((E₀ R x).val.val - 1) := by
      simpa only [neg_lt_neg_iff] using identityLimitCriterion n (fun i ↦ -w i) (E₀ R x)
    exact hlimit.trans (hsign.trans (hN R x))
  · have hlimit : HasGroupIdentityLimit U T t l false x ↔
        HasIdentityLimit w (E₀ R x).val := by
      change HasGroupIdentityLimit U T t l false x ↔
        HasIdentityLimit (fun i ↦ cocharacterWeight l (m i)) (matrixPoint (U.inclusion ≫ j) e R x)
      simpa only [Bool.false_eq_true, ite_false, one_mul] using
        groupIdentityLimit_iff_matrix j U T e t m l hj hn hd false R x
    exact hlimit.trans ((identityLimitCriterion n w (E₀ R x)).trans (hP R x))

end
end LinearAlgebraicGroups.TorusLimitFactorization
