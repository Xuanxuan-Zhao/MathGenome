import Specs.LinearAlgebraicGroups.Classification.RankTwoRelations
import LinearAlgebraicGroups.Classification.RankOneRelations
import LinearAlgebraicGroups.Classification.Pinning
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum

open AlgebraicGeometry CategoryTheory WithConv
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Classification.RankTwoRelations

open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.RankTwoRelations
open Specs.Pinning (PinnedGroup)
open Specs.RootGroups (AdditiveLine Proportional)
open Specs.CharacterPairing (absoluteRoots)

noncomputable section

variable {k : Type u} [Field k] {A : AdditiveLine k} {P : PinnedGroup A}
  {τ : TypeOfRoots}

private theorem Frame.character_neg (F : Frame P τ) (r : RootIndex) :
    F.character (-r) = (F.character r)⁻¹ := by
  simp [Specs.RankTwoRelations.Frame.character, zpow_neg, mul_comm]

private theorem Frame.character_sum_powers (F : Frame P τ) (r s : RootIndex) (i j : ℕ) :
    F.character ((i : ℤ) * r.1 + (j : ℤ) * s.1, (i : ℤ) * r.2 + (j : ℤ) * s.2) =
      F.character r ^ i * F.character s ^ j := by
  simp only [Specs.RankTwoRelations.Frame.character, zpow_add]
  simp only [zpow_mul', zpow_natCast, mul_pow]
  ac_rfl

private theorem orthogonal_index (r : Index .orthogonal) :
    r.val = a ∨ r.val = b ∨ r.val = -a ∨ r.val = -b := by
  rcases r.property with h | h
  · rcases (show r.val = a ∨ r.val = b by simpa [positiveList] using h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases (show -r.val = a ∨ -r.val = b by simpa [positiveList] using h) with h | h
    · exact Or.inr (Or.inr (Or.inl (neg_eq_iff_eq_neg.mp h)))
    · exact Or.inr (Or.inr (Or.inr (neg_eq_iff_eq_neg.mp h)))

private theorem proportional_self {T : GroupScheme k} (χ : Specs.CharacterDescent.Character T) :
    Proportional χ χ := ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

private theorem proportional_inverse {T : GroupScheme k} (χ : Specs.CharacterDescent.Character T) :
    Proportional χ χ⁻¹ := by
  refine ⟨1, -1, one_ne_zero, by decide, ?_⟩
  simp

set_option maxHeartbeats 1000000 in
private theorem orthogonal_cone (F : Frame P .orthogonal)
    (r s : Index .orthogonal) (hind : ¬ Proportional (F.character r) (F.character s))
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    F.character r ^ i * F.character s ^ j ∉ absoluteRoots P.pair.T := by
  intro h
  obtain ⟨t, ht⟩ := (F.root_iff _).mp h
  have e := F.independent ((Frame.character_sum_powers F r s i j).trans ht)
  have e₁ := congrArg Prod.fst e
  have e₂ := congrArg Prod.snd e
  have hne : r.val ≠ s.val := by
    intro he
    apply hind
    rw [he]
    exact proportional_self _
  have hopp : r.val ≠ -s.val := by
    intro he
    apply hind
    rw [he, Frame.character_neg]
    simpa only [inv_inv] using proportional_inverse ((F.character s)⁻¹)
  rcases orthogonal_index r with hr | hr | hr | hr <;>
    rcases orthogonal_index s with hs | hs | hs | hs <;>
      simp only [hr, hs, neg_neg, ne_eq, not_true_eq_false] at hne hopp
  all_goals
    rcases orthogonal_index t with ht | ht | ht | ht <;>
      simp only [hr, hs, ht, a, b, Prod.fst_neg, Prod.snd_neg,
        neg_zero, mul_one, mul_zero, mul_neg, add_zero, zero_add] at e₁ e₂ <;>
      omega

/-- For the orthogonal root system, a strictly positive mixed power of two
independent signed roots cannot be a root. -/
theorem orthogonalCommutation_of_independent
    (independent : Specs.RankOneRelations.IndependentRootCommutation.{u}) :
    OrthogonalCommutation.{u} := by
  intro k _ A P F r s hind R x y
  exact independent P.pair.G P.pair.reductive P.pair.T
    P.pair.split P.pair.maximal (F.character r) (F.root r).property
    (F.character s) (F.root s).property hind (orthogonal_cone F r s hind)
    (P.roots (F.root r)).val (P.roots (F.root s)).val
    (P.roots (F.root r)).property (P.roots (F.root s)).property R x y

section SignedRelations

open Specs.AdjointRepresentation (GroupPoints)
open Specs.RootGroups (rootPoint)

private def signedList (τ : TypeOfRoots) : List RootIndex :=
  positiveList τ ++ (positiveList τ).map Neg.neg

private theorem mem_signedList (r : RootIndex) : r ∈ signedList τ ↔ IsIndex τ r := by
  simp only [signedList, List.mem_append, List.mem_map, IsIndex]
  constructor
  · rintro (h | ⟨s, hs, he⟩)
    · exact Or.inl h
    · exact Or.inr (by simpa [← he] using hs)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨-r, h, neg_neg _⟩

private def wordRoot (τ : TypeOfRoots) (w : List Bool) (r : RootIndex) : RootIndex :=
  w.foldr (reflection τ) r

private theorem wordAction_root (τ : TypeOfRoots) (w : List Bool) (r : RootIndex) (ε : ℤ) :
    (wordAction τ w r ε).1 = wordRoot τ w r := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change reflection τ i (wordAction τ w r ε).1 = reflection τ i (wordRoot τ w r)
    rw [ih]

private theorem reflection_involutive (τ : TypeOfRoots) (i : Bool) :
    Function.Involutive (reflection τ i) := by
  intro r
  cases τ <;> cases i <;> apply Prod.ext <;> simp [reflection]

private theorem reflection_mem (τ : TypeOfRoots) (i : Bool) (r : RootIndex)
    (hr : IsIndex τ r) : IsIndex τ (reflection τ i r) := by
  have check : ∀ s ∈ signedList τ, reflection τ i s ∈ signedList τ := by
    cases τ <;> cases i <;> decide
  exact (mem_signedList _).mp (check _ ((mem_signedList _).mpr hr))

private theorem wordRoot_mem (τ : TypeOfRoots) (w : List Bool) (r : RootIndex)
    (hr : IsIndex τ r) : IsIndex τ (wordRoot τ w r) := by
  induction w with
  | nil => exact hr
  | cons i w ih => exact reflection_mem τ i _ ih

private theorem wordRoot_injective (τ : TypeOfRoots) (w : List Bool) :
    Function.Injective (wordRoot τ w) := by
  induction w with
  | nil => exact fun _ _ h => h
  | cons i w ih => exact (reflection_involutive τ i).injective.comp ih

/-- One word for each reachable chamber, including the identity. -/
private def chamberWords : List (List Bool) :=
  [[], [false], [true], [false,true], [true,false], [false,true,false],
   [true,false,true], [false,true,false,true], [true,false,true,false],
   [false,true,false,true,false], [true,false,true,false,true],
   [false,true,false,true,false,true]]

private theorem move_pair (τ : TypeOfRoots) (r s : RootIndex) (hr : IsIndex τ r)
    (hs : IsIndex τ s) (hne : r ≠ s) (hopp : r ≠ -s) :
    ∃ w : List Bool, wordRoot τ w r ∈ positiveList τ ∧ wordRoot τ w s ∈ positiveList τ := by
  have check : ∀ r ∈ signedList τ, ∀ s ∈ signedList τ, r ≠ s → r ≠ -s →
      ∃ w ∈ chamberWords, wordRoot τ w r ∈ positiveList τ ∧ wordRoot τ w s ∈ positiveList τ := by
    cases τ <;> decide
  obtain ⟨w, _, h⟩ := check r ((mem_signedList r).mpr hr)
    s ((mem_signedList s).mpr hs) hne hopp
  exact ⟨w, h⟩

private theorem word_conjugates (F : Frame P τ) (X : Coordinates (P := P))
    (h : SimpleActions F X) (R : TestAlgebra k) (w : List Bool) (r : RootIndex)
    (hr : IsIndex τ r) (ε : ℤ) (x : R) :
    let n := (w.map (representative F X R)).prod
    let q := wordAction τ w r ε
    n * point F X R r ((ε : R) * x) * n⁻¹ = point F X R q.1 ((q.2 : R) * x) := by
  induction w with
  | nil => simp [wordAction]
  | cons i w ih =>
    dsimp only [List.map_cons, List.prod_cons]
    let q := wordAction τ w r ε
    let n := (w.map (representative F X R)).prod
    let m := representative F X R i
    have hq : IsIndex τ q.1 := by
      rw [wordAction_root]
      exact wordRoot_mem τ w r hr
    change (m * n) * point F X R r ((ε : R) * x) * (m * n)⁻¹ =
      point F X R (reflection τ i q.1) ((↑(actionSign τ i q.1 * q.2) : R) * x)
    calc
      _ = m * (n * point F X R r ((ε : R) * x) * n⁻¹) * m⁻¹ := by group
      _ = m * point F X R q.1 ((q.2 : R) * x) * m⁻¹ := by rw [ih]
      _ = _ := by
        simpa only [Int.cast_mul, mul_assoc] using h i ⟨q.1, hq⟩ R ((q.2 : R) * x)

private theorem rootParameter_neg {A : AdditiveLine k} {G : GroupScheme k}
    (x : A.group ⟶ G) (R : TestAlgebra k) (a : R) :
    rootPoint x R (-a) = (rootPoint x R a)⁻¹ := by
  let _ := A.operations.hopf
  let e : WithConv (Polynomial k →ₐ[k] R) ≃* GroupPoints A.group R := Spec.mapMulEquiv
  let f : GroupPoints A.group R →* GroupPoints G R := (((groupPointsFunctor k).map x).app R).hom
  have hf (s : R) : f (e (toConv (Polynomial.aeval s))) = rootPoint x R s := rfl
  have h : toConv (Polynomial.aeval (-a)) * toConv (Polynomial.aeval a) =
      (1 : WithConv (Polynomial k →ₐ[k] R)) := by
    apply WithConv.ofConv_injective
    apply Polynomial.algHom_ext
    rw [AlgHom.convMul_def, AlgHom.convOne_def]
    change Algebra.TensorProduct.lmul' k
      ((Algebra.TensorProduct.map (Polynomial.aeval (-a)) (Polynomial.aeval a))
        (A.operations.delta Polynomial.X)) = algebraMap k R (A.operations.epsilon Polynomial.X)
    rw [A.comultiplication, A.counit]
    simp
  apply eq_inv_of_mul_eq_one_left
  rw [← hf, ← hf, ← map_mul, ← map_mul, h, map_one, map_one]


private theorem point_neg (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (r : RootIndex) (x : R) :
    point F X R r (-x) = (point F X R r x)⁻¹ := by
  unfold point
  split
  · exact rootParameter_neg _ _ _
  · simp

private theorem positive_commutator (F : Frame P τ) (X : Coordinates (P := P))
    (h : PositiveRelations F X) (r s : RootIndex) (hr : r ∈ positiveList τ)
    (hs : s ∈ positiveList τ) (hne : r ≠ s) (R : TestAlgebra k) (x y : R) :
    point F X R r x * point F X R s y * (point F X R r x)⁻¹ *
      (point F X R s y)⁻¹ = positiveCommutator F X R r s x y := by
  by_cases hlt : (positiveList τ).idxOf r < (positiveList τ).idxOf s
  · rw [← point_neg, h r s hr hs hlt, positiveCommutator, ite_eq_left hlt]
  · have hgt : (positiveList τ).idxOf s < (positiveList τ).idxOf r := by
      have hn : (positiveList τ).idxOf r ≠ (positiveList τ).idxOf s :=
        fun he => hne ((List.idxOf_inj hr).mp he)
      omega
    have he := h s r hs hr hgt R y x
    rw [point_neg] at he
    rw [positiveCommutator, ite_eq_right hlt, ← he]
    group

/-- The fixed signs of the two representatives and the positive table imply
all signed nonopposite relations by transporting the two roots together. -/
theorem signedRelations_of_positive (F : Frame P τ) (X : Coordinates (P := P))
    (ha : SimpleActions F X) (hc : PositiveRelations F X) :
    SignedRelations F X := by
  intro r s hi
  have hne : r.val ≠ s.val := by
    intro he
    apply hi
    rw [he]
    exact proportional_self _
  have hopp : r.val ≠ -s.val := by
    intro he
    apply hi
    rw [he, Frame.character_neg]
    simpa using proportional_inverse ((F.character s)⁻¹)
  obtain ⟨w, hw₁, hw₂⟩ := move_pair τ r s r.property s.property hne hopp
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa only [wordAction_root] using hw₁
  · simpa only [wordAction_root] using hw₂
  · intro R x y
    let n := (w.map (representative F X R)).prod
    let p := wordAction τ w r 1
    let q := wordAction τ w s 1
    have hr := word_conjugates F X ha R w r r.property 1 x
    have hs := word_conjugates F X ha R w s s.property 1 y
    have hr' : n * point F X R r x * n⁻¹ = point F X R p.1 ((p.2 : R) * x) := by
      simpa only [Int.cast_one, one_mul] using hr
    have hs' : n * point F X R s y * n⁻¹ = point F X R q.1 ((q.2 : R) * y) := by
      simpa only [Int.cast_one, one_mul] using hs
    have e : p.1 ≠ q.1 := fun h => hne (wordRoot_injective τ w (by
      simpa only [p, q, wordAction_root] using h))
    dsimp only
    rw [← positive_commutator F X hc _ _ (by simpa only [p, wordAction_root] using hw₁)
      (by simpa only [q, wordAction_root] using hw₂) e, ← hr', ← hs']
    change n * _ * n⁻¹ = _
    group

end SignedRelations

section RadicalCalculations

variable {K : Type*} [CommRing K]

private def lowerTwo (A : K) (v : K × K) : K × K :=
  (v.1, A * v.1 + v.2)

private def upperTwoAtMinusOne (D : K) (v : K × K) : K × K :=
  (v.1 - D * v.2, v.2)

/-- The Weyl word on a two-root string fixes the coefficients when the second
axis is defined as the image of the first under the representative. -/
theorem twoRootStringCoefficients (A D : K)
    (word : lowerTwo A (upperTwoAtMinusOne D (lowerTwo A (1, 0))) = (0, 1)) :
    A = 1 ∧ D = 1 := by
  have diagonal := congrArg Prod.fst word
  have transport := congrArg Prod.snd word
  simp only [lowerTwo, upperTwoAtMinusOne, mul_one, add_zero] at diagonal transport
  have h : D * A = 1 := by linear_combination -diagonal
  rw [h] at transport
  have ha : A = 1 := by simpa using transport
  exact ⟨ha, by simpa [ha] using h⟩

private def shortThree (B C : K) (v : K × K × K) : K × K × K :=
  (v.1, -v.1 + v.2.1, B * v.1 + C * v.2.1 + v.2.2)

private def shortThreeRepresentative (s : K) (v : K × K × K) : K × K × K :=
  (v.2.2, s * v.2.1, v.1)

/-- The (B_2) Weyl word on the last axis fixes the quadratic coefficient,
the middle sign, and the coefficient of the short-root step from that axis.
Here the representative is its own inverse (its middle sign squares to one). -/
theorem b2StringCoefficients (B C s : K)
    (word : shortThree B C (shortThreeRepresentative s (shortThree B C
      (shortThreeRepresentative s (shortThree B C (0, 0, 1))))) = (1, 0, 0)) :
    B = 1 ∧ C = -2 ∧ s = -1 := by
  have corner := congrArg Prod.fst word
  have middle := congrArg (fun v : K × K × K => v.2.1) word
  have last := congrArg (fun v : K × K × K => v.2.2) word
  simp only [shortThree, shortThreeRepresentative, neg_zero, add_zero, zero_add,
    mul_zero, mul_one, mul_neg] at corner middle last
  have hs : s = -1 := by
    rw [corner] at middle
    linear_combination -middle
  rw [corner, hs] at last
  exact ⟨corner, by linear_combination last, hs⟩

private abbrev QuotientCoordinates (K : Type*) := K × K × K × K

private def shortFour (B C D E F t : K) (v : QuotientCoordinates K) : QuotientCoordinates K :=
  (v.1, v.2.1 - t * v.1, v.2.2.1 + B * t ^ 2 * v.1 + C * t * v.2.1,
    v.2.2.2 + D * t ^ 3 * v.1 + E * t ^ 2 * v.2.1 + F * t * v.2.2.1)

private def shortFourRepresentative (v : QuotientCoordinates K) : QuotientCoordinates K :=
  (-v.2.2.2, -v.2.2.1, v.2.1, v.1)

private def shortFourRepresentativeInverse (v : QuotientCoordinates K) : QuotientCoordinates K :=
  (v.2.2.2, v.2.2.1, -v.2.1, -v.1)

private theorem mixedFourCoefficients (B C D E F : K)
    (additive :
      shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
        (Polynomial.C F) Polynomial.X
        (shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
          (Polynomial.C F) 1 (1, 0, 0, 0)) =
      shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
        (Polynomial.C F) (Polynomial.X + 1) (1, 0, 0, 0)) :
    E * (-1) = 3 * D ∧ F * B = 3 * D := by
  let last : QuotientCoordinates (Polynomial K) → Polynomial K := fun v => v.2.2.2
  have h := congrArg last additive
  let X : Polynomial K := Polynomial.X
  have hn :
      Polynomial.C D + Polynomial.C (F * B) * X + Polynomial.C (E * (-1)) * X ^ 2 +
        Polynomial.C D * X ^ 3 =
      Polynomial.C D + Polynomial.C (3 * D) * X + Polynomial.C (3 * D) * X ^ 2 +
        Polynomial.C D * X ^ 3 := by
    calc
      _ = Polynomial.C D * (X + 1) ^ 3 := by
        convert h using 1 <;>
          simp only [X, last, shortFour, mul_zero, mul_one, zero_sub, add_zero, zero_add,
            one_pow, map_mul, map_neg, map_one] <;> ring
      _ = _ := by simp only [map_mul, map_ofNat]; ring
  constructor
  · have h₂ := congrArg (fun p : Polynomial K => p.coeff 2) hn
    simp only [X, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow] at h₂
    norm_num at h₂ ⊢
    exact h₂
  · have h₁ := congrArg (fun p : Polynomial K => p.coeff 1) hn
    simp only [X, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow] at h₁
    norm_num at h₁
    exact h₁

/-- The last column of the (G_2) Weyl word, followed by the two mixed
coefficients in the additive-parameter identity, determines the linear action
on the quotient by the highest root. -/
theorem g2StringCoefficients (B C D E F : K)
    (word : shortFour B C D E F 1 (shortFourRepresentative (shortFour B C D E F 1
      (shortFourRepresentativeInverse (shortFour B C D E F 1 (0, 0, 0, 1))))) =
        (-1, 0, 0, 0))
    (additive :
      shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
        (Polynomial.C F) Polynomial.X
        (shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
          (Polynomial.C F) 1 (1, 0, 0, 0)) =
      shortFour (Polynomial.C B) (Polynomial.C C) (Polynomial.C D) (Polynomial.C E)
        (Polynomial.C F) (Polynomial.X + 1) (1, 0, 0, 0)) :
    B = 1 ∧ C = -2 ∧ D = 1 ∧ E = -3 ∧ F = 3 := by
  obtain ⟨mixLeft, mixRight⟩ := mixedFourCoefficients B C D E F additive
  have corner := congrArg Prod.fst word
  have second := congrArg (fun v : QuotientCoordinates K => v.2.1) word
  have third := congrArg (fun v : QuotientCoordinates K => v.2.2.1) word
  simp only [shortFour, shortFourRepresentative, shortFourRepresentativeInverse, one_pow,
    mul_one, one_mul, add_zero, zero_add, mul_zero, sub_zero, zero_sub, neg_zero, mul_neg]
    at corner second third
  have hd : D = 1 := by linear_combination -corner
  have hb : B = 1 := by linear_combination -second + hd
  rw [hb, hd] at third mixRight
  rw [hd] at mixLeft
  refine ⟨hb, ?_, hd, ?_, ?_⟩
  · linear_combination -third
  · linear_combination -mixLeft
  · linear_combination mixRight

/-- Preserving the commutator of the two indicated axes in the (G_2) radical
forces the coefficient in the (c,d) commutator. -/
theorem g2MiddleCommutator (Kcd : K) (preserves : (1 : K) * 3 + Kcd * (-1) * 1 = 0) :
    Kcd = 3 := by
  linear_combination -preserves

/-- The coordinates of the type (G_2) parabolic radical, with the final
coordinate in its central root group. -/
private abbrev Radical (K : Type*) := K × K × K × K × K

private def shortRootAction (P Q : K) : Radical K → Radical K
  | (b, c, d, e, z) =>
    (b, c - b, d + b - 2 * c, e + b - 3 * c + 3 * d, z + P * b ^ 2 + Q * c ^ 2 - 3 * b * c)

private def shortRepresentative : Radical K → Radical K
  | (b, c, d, e, z) => (-e, -d, c, b, z + e * b + 3 * d * c)

private def shortRepresentativeInverse : Radical K → Radical K
  | (b, c, d, e, z) => (e, d, -c, -b, z + e * b + 3 * d * c)

private def shortWeylWord (P Q : K) : Radical K → Radical K :=
  shortRootAction P Q ∘ shortRepresentative ∘ shortRootAction P Q ∘
    shortRepresentativeInverse ∘ shortRootAction P Q

/-- The (G_2) central correction follows from the Weyl word on two axes.
The determinant of the coefficient system is one over the integers. -/
theorem g2CentralCoefficients (P Q : K)
    (firstAxis : shortWeylWord P Q (1, 0, 0, 0, 0) = shortRepresentative (1, 0, 0, 0, 0))
    (secondAxis : shortWeylWord P Q (0, 1, 0, 0, 0) = shortRepresentative (0, 1, 0, 0, 0)) :
    P = 1 ∧ Q = 3 := by
  let center : Radical K → K := fun x => x.2.2.2.2
  have h₁ := congrArg center firstAxis
  have h₂ := congrArg center secondAxis
  simp only [center, shortWeylWord, Function.comp_apply, shortRootAction, shortRepresentative,
    shortRepresentativeInverse] at h₁ h₂
  constructor
  · linear_combination 5 * h₁ - h₂
  · linear_combination 2 * h₂ - 9 * h₁

end RadicalCalculations


private def coneWeight (r s : RootIndex) (i j : ℕ) : RootIndex :=
  ((i : ℤ) * r.1 + (j : ℤ) * s.1, (i : ℤ) * r.2 + (j : ℤ) * s.2)

private theorem positive_root_bounds {r : RootIndex} (hr : r ∈ positiveList τ) :
    0 ≤ r.1 ∧ r.1 ≤ 3 ∧ 0 ≤ r.2 ∧ r.2 ≤ 3 ∧ (1 ≤ r.1 ∨ 1 ≤ r.2) := by
  have test : ∀ r ∈ positiveList τ,
      0 ≤ r.1 ∧ r.1 ≤ 3 ∧ 0 ≤ r.2 ∧ r.2 ≤ 3 ∧ (1 ≤ r.1 ∨ 1 ≤ r.2) := by
    cases τ <;> decide
  exact test r hr

set_option maxHeartbeats 3000000 in
/-- A mixed weight in the positive system occurs at one of the indicated
bidegrees. The integer values in the table play no role in this test. -/
private theorem positiveConeTable (τ : TypeOfRoots) (r s t : RootIndex)
    (hr : r ∈ positiveList τ) (hs : s ∈ positiveList τ) (ht : IsIndex τ t)
    (hrs : (positiveList τ).idxOf r < (positiveList τ).idxOf s) (i j : ℕ)
    (hi : 0 < i) (hj : 0 < j) (h : coneWeight r s i j = t) :
    ∃ q ∈ correctionTable τ r s, q.root = t ∧ q.leftDegree = i ∧ q.rightDegree = j := by
  obtain ⟨hr₁, _, hr₂, _, hrne⟩ := positive_root_bounds hr
  obtain ⟨hs₁, _, hs₂, _, hsne⟩ := positive_root_bounds hs
  have h₁ : (i : ℤ) * r.1 + (j : ℤ) * s.1 = t.1 := congrArg Prod.fst h
  have h₂ : (i : ℤ) * r.2 + (j : ℤ) * s.2 = t.2 := congrArg Prod.snd h
  have hi' : (1 : ℤ) ≤ i := by omega
  have hj' : (1 : ℤ) ≤ j := by omega
  have hpos : t ∈ positiveList τ := by
    rcases ht with ht | ht
    · exact ht
    obtain ⟨ht₁, _, ht₂, _, _⟩ := positive_root_bounds ht
    simp only [Prod.fst_neg, Prod.snd_neg] at ht₁ ht₂
    rcases hrne with hrne | hrne
    · have hh := mul_le_mul_of_nonneg_left hrne (show (0 : ℤ) ≤ i by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ j by omega) hs₁
      omega
    · have hh := mul_le_mul_of_nonneg_left hrne (show (0 : ℤ) ≤ i by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ j by omega) hs₂
      omega
  obtain ⟨_, ht₁, _, ht₂, _⟩ := positive_root_bounds hpos
  have hi₃ : i ≤ 3 := by
    rcases hrne with hrne | hrne
    · have hh := mul_le_mul_of_nonneg_left hrne (show (0 : ℤ) ≤ i by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ j by omega) hs₁
      omega
    · have hh := mul_le_mul_of_nonneg_left hrne (show (0 : ℤ) ≤ i by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ j by omega) hs₂
      omega
  have hj₃ : j ≤ 3 := by
    rcases hsne with hsne | hsne
    · have hh := mul_le_mul_of_nonneg_left hsne (show (0 : ℤ) ≤ j by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ i by omega) hr₁
      omega
    · have hh := mul_le_mul_of_nonneg_left hsne (show (0 : ℤ) ≤ j by omega)
      have hh' := mul_nonneg (show (0 : ℤ) ≤ i by omega) hr₂
      omega
  have check : ∀ r ∈ positiveList τ, ∀ s ∈ positiveList τ,
      (positiveList τ).idxOf r < (positiveList τ).idxOf s →
      ∀ i ∈ ([1, 2, 3] : List ℕ), ∀ j ∈ ([1, 2, 3] : List ℕ),
      ∀ t ∈ positiveList τ, coneWeight r s i j = t →
      ∃ q ∈ correctionTable τ r s, q.root = t ∧ q.leftDegree = i ∧ q.rightDegree = j := by
    cases τ <;> decide
  have him : i ∈ ([1, 2, 3] : List ℕ) := by simp; omega
  have hjm : j ∈ ([1, 2, 3] : List ℕ) := by simp; omega
  exact check r hr s hs hrs i him j hjm t hpos h


section GroupCalculations

variable {K H : Type*} [CommRing K] [Group H]

private def orderedWord (p : RootIndex → K → H) (l : List RootIndex)
    (v : RootIndex → K) : H := (l.map fun r => p r (v r)).prod

private def SeparatesCoordinates (p : RootIndex → K → H) (τ : TypeOfRoots) : Prop :=
  ∀ v w : RootIndex → K, orderedWord p (positiveList τ) v = orderedWord p (positiveList τ) w →
    ∀ r ∈ positiveList τ, v r = w r

private def parameters (x1 x2 x3 x4 x5 x6 : K) (r : RootIndex) : K :=
  if r = a then x1 else if r = b then x2 else if r = c then x3
  else if r = d then x4 else if r = e then x5 else x6

private theorem parameters_a (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 a = x1 := rfl
private theorem parameters_b (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 b = x2 := rfl
private theorem parameters_c (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 c = x3 := rfl
private theorem parameters_d (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 d = x4 := rfl
private theorem parameters_e (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 e = x5 := rfl
private theorem parameters_f (x1 x2 x3 x4 x5 x6 : K) : parameters x1 x2 x3 x4 x5 x6 f = x6 := rfl

private theorem commute_conjugation {p q : H} (h : Commute p q) : MulAut.conj p q = q := by
  rw [MulAut.conj_apply, h.eq, mul_inv_cancel_right]

private theorem conjugation_composition (x y z : H) :
    MulAut.conj x (MulAut.conj y z) = MulAut.conj (x * y) z := by
  simp only [MulAut.conj_apply]
  group

/-- Evaluate a linked Weyl word on a point whose image commutes with its
positive root factor. This compares two positive conjugation formulas. -/
private theorem conjugation_of_weyl_word (p q v n : H) (word : n = p * q * p)
    (opposite : MulAut.conj n p = q)
    (fixed : Commute p (MulAut.conj n v)) :
    MulAut.conj p v = MulAut.conj n (MulAut.conj p⁻¹ v) := by
  have hn : p⁻¹ * n = q * p := by rw [word]; group
  have hq : q⁻¹ * n = n * p⁻¹ := by
    rw [← opposite, MulAut.conj_apply]
    group
  have h : MulAut.conj q (MulAut.conj p v) = MulAut.conj n v := by
    rw [conjugation_composition, ← hn, ← conjugation_composition]
    exact commute_conjugation fixed.inv_left
  calc
    MulAut.conj p v = MulAut.conj q⁻¹ (MulAut.conj q (MulAut.conj p v)) := by
      rw [conjugation_composition, inv_mul_cancel]
      simp only [MulAut.conj_apply, one_mul, inv_one, mul_one]
    _ = _ := by rw [h, conjugation_composition, hq, ← conjugation_composition]

/-- Reversing an ordered positive conjugation is an identity in the ambient group. -/
private theorem reverse_conjugation {p q t : H} (h : MulAut.conj p⁻¹ q = q * t) :
    MulAut.conj q p = p * MulAut.conj q t := by
  rw [MulAut.conj_apply, inv_inv] at h
  have h' : q * p = p * (q * t) := by rw [← h]; group
  rw [MulAut.conj_apply, h', MulAut.conj_apply, mul_assoc]

set_option maxHeartbeats 2000000 in
private theorem a2Coefficients (p : RootIndex → K → H)
    (zero : ∀ r, p r 0 = 1) (neg : ∀ r x, p r (-x) = (p r x)⁻¹)
    (separates : SeparatesCoordinates p .a2) (Nₐ Nᵦ : H)
    (wordₐ : Nₐ = p a 1 * p (-a) (-1) * p a 1)
    (wordᵦ : Nᵦ = p b 1 * p (-b) (-1) * p b 1)
    (swapₐ : MulAut.conj Nₐ (p a 1) = p (-a) (-1))
    (swapᵦ : MulAut.conj Nᵦ (p b 1) = p (-b) (-1))
    (ac : ∀ x y, Commute (p a x) (p c y)) (bc : ∀ x y, Commute (p b x) (p c y))
    (nb nc na nd : K)
    (a_on_b : ∀ y, MulAut.conj Nₐ (p b y) = p c (nb * y))
    (a_on_c : ∀ y, MulAut.conj Nₐ (p c y) = p b (nc * y))
    (b_on_a : ∀ x, MulAut.conj Nᵦ (p a x) = p c (na * x))
    (b_on_c : ∀ y, MulAut.conj Nᵦ (p c y) = p a (nd * y))
    (normalized : nb = 1) (m : K)
    (ab : ∀ x y, MulAut.conj (p a x) (p b y) = p b y * p c (m * x * y)) :
    m = 1 ∧ na = -1 := by
  have testₐ := conjugation_of_weyl_word (p a 1) (p (-a) (-1)) (p b 1) Nₐ wordₐ swapₐ
    (by rw [a_on_b, normalized, one_mul]; exact ac 1 1)
  simp only [← neg, ab, map_mul, a_on_b, a_on_c, normalized, one_mul, mul_one] at testₐ
  have hₐ : p b 1 * p c m = p b (nc * (m * -1)) * p c 1 := testₐ.trans (bc _ _).eq.symm
  have eₐ : orderedWord p (positiveList .a2) (parameters 0 1 m 0 0 0) =
      orderedWord p (positiveList .a2) (parameters 0 (nc * (m * -1)) 1 0 0 0) := by
    simpa only [orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      parameters_a, parameters_b, parameters_c, zero, one_mul, mul_one] using hₐ
  have hm : m = 1 := separates _ _ eₐ c (by decide)
  have ba (x y : K) : MulAut.conj (p b y) (p a x) = p a x * p c (- (x * y)) := by
    have he := reverse_conjugation (p := p a x) (q := p b y) (t := p c (m * (-x) * y))
      (by rw [← neg]; exact ab (-x) y)
    simpa only [commute_conjugation (bc y _), hm, one_mul, neg_mul] using he
  have testᵦ := conjugation_of_weyl_word (p b 1) (p (-b) (-1)) (p a 1) Nᵦ wordᵦ swapᵦ
    (by rw [b_on_a]; exact bc 1 _)
  simp only [← neg, ba, map_mul, b_on_a, b_on_c, mul_one, one_mul, neg_neg] at testᵦ
  have hᵦ : p a 1 * p c (-1) = p a nd * p c na := testᵦ.trans (ac _ _).eq.symm
  have eᵦ : orderedWord p (positiveList .a2) (parameters 1 0 (-1) 0 0 0) =
      orderedWord p (positiveList .a2) (parameters nd 0 na 0 0 0) := by
    simpa only [orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      parameters_a, parameters_b, parameters_c, zero, one_mul, mul_one] using hᵦ
  exact ⟨hm, (separates _ _ eᵦ c (by decide)).symm⟩

private theorem reverse_three {x y z : H} (hxy : Commute x y) (hxz : Commute x z)
    (hyz : Commute y z) : z * (y * x) = x * (y * z) := by
  rw [hxy.symm.eq, ← mul_assoc, hxz.symm.eq, mul_assoc, hyz.symm.eq]

set_option maxHeartbeats 3000000 in
private theorem b2Coefficients (p : RootIndex → K → H)
    (zero : ∀ r, p r 0 = 1) (add : ∀ r x y, p r (x + y) = p r x * p r y)
    (neg : ∀ r x, p r (-x) = (p r x)⁻¹)
    (separates : SeparatesCoordinates p .b2) (Nₐ Nᵦ : H)
    (wordₐ : Nₐ = p a 1 * p (-a) (-1) * p a 1)
    (wordᵦ : Nᵦ = p b 1 * p (-b) (-1) * p b 1)
    (swapₐ : MulAut.conj Nₐ (p a 1) = p (-a) (-1))
    (swapᵦ : MulAut.conj Nᵦ (p b 1) = p (-b) (-1))
    (ad : ∀ x y, Commute (p a x) (p d y)) (bd : ∀ x y, Commute (p b x) (p d y))
    (bc : ∀ x y, Commute (p b x) (p c y)) (cd : ∀ x y, Commute (p c x) (p d y))
    (s : K)
    (a_on_b : ∀ y, MulAut.conj Nₐ (p b y) = p d y)
    (a_on_c : ∀ y, MulAut.conj Nₐ (p c y) = p c (s * y))
    (a_on_d : ∀ y, MulAut.conj Nₐ (p d y) = p b y)
    (b_on_a : ∀ x, MulAut.conj Nᵦ (p a x) = p c x)
    (b_on_c : ∀ y, MulAut.conj Nᵦ (p c y) = p a (-y))
    (b_on_d : ∀ y, MulAut.conj Nᵦ (p d y) = p d y)
    (m n t : K)
    (ab : ∀ x y, MulAut.conj (p a x) (p b y) = p b y * (p c (m * x * y) * p d (n * x ^ 2 * y)))
    (ac : ∀ x y, MulAut.conj (p a x) (p c y) = p c y * p d (t * x * y)) :
    m = -1 ∧ n = 1 ∧ t = -2 ∧ s = -1 := by
  have ba (x y : K) : MulAut.conj (p b y) (p a x) =
      p a x * (p c (m * (-x) * y) * p d (n * x ^ 2 * y)) := by
    have he := reverse_conjugation (p := p a x) (q := p b y)
      (t := p c (m * (-x) * y) * p d (n * (-x) ^ 2 * y)) (by rw [← neg]; exact ab (-x) y)
    simpa only [map_mul, commute_conjugation (bc y _), commute_conjugation (bd y _),
      neg_sq] using he
  have ca (x y : K) : p c y * p a x = p a x * (p c y * p d (t * (-x) * y)) := by
    rw [← ac (-x) y, neg, MulAut.conj_apply]
    group
  have testᵦ := conjugation_of_weyl_word (p b 1) (p (-b) (-1)) (p a 1) Nᵦ wordᵦ swapᵦ
    (by rw [b_on_a]; exact bc 1 1)
  simp only [← neg, ba, map_mul, b_on_a, b_on_c, b_on_d, mul_one, one_pow, neg_sq,
    neg_neg, mul_neg, neg_mul, one_mul] at testᵦ
  have hᵦ : p a 1 * (p c (-m) * p d n) = p a (-m) * (p c 1 * p d (t * m - n)) := by
    calc
      _ = p c 1 * (p a (-m) * p d (-n)) := testᵦ
      _ = _ := by
        rw [← mul_assoc, ca (-m) 1, neg_neg, mul_one]
        simp only [mul_assoc, ← add, sub_eq_add_neg]
  have eᵦ : orderedWord p (positiveList .b2) (parameters 1 0 (-m) n 0 0) =
      orderedWord p (positiveList .b2) (parameters (-m) 0 1 (t * m - n) 0 0) := by
    simpa only [orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      parameters_a, parameters_b, parameters_c, parameters_d, zero, one_mul, mul_one] using hᵦ
  have hm' : (1 : K) = -m := separates _ _ eᵦ a (by decide)
  have hm : m = -1 := by linear_combination hm'
  have ht : n = t * m - n := separates _ _ eᵦ d (by decide)
  have testₐ := conjugation_of_weyl_word (p a 1) (p (-a) (-1)) (p b 1) Nₐ wordₐ swapₐ
    (by rw [a_on_b]; exact ad 1 1)
  simp only [← neg, ab, map_mul, a_on_b, a_on_c, a_on_d, mul_one, one_pow, neg_sq,
    neg_neg, mul_neg, neg_mul, one_mul, hm] at testₐ
  have hₐ : p b 1 * (p c (-1) * p d n) = p b n * (p c s * p d 1) :=
    testₐ.trans (reverse_three (bc _ _) (bd _ _) (cd _ _))
  have eₐ : orderedWord p (positiveList .b2) (parameters 0 1 (-1) n 0 0) =
      orderedWord p (positiveList .b2) (parameters 0 n s 1 0 0) := by
    simpa only [orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      parameters_a, parameters_b, parameters_c, parameters_d, zero, one_mul, mul_one] using hₐ
  have hn : n = 1 := separates _ _ eₐ d (by decide)
  have hs : s = -1 := (separates _ _ eₐ c (by decide)).symm
  rw [hm, hn] at ht
  refine ⟨hm, hn, ?_, hs⟩
  linear_combination ht

private theorem swapped {x y z : H} (h : MulAut.conj x⁻¹ y = y * z) :
    y * x = x * (y * z) := by
  rw [← h, MulAut.conj_apply]
  group

private theorem conjugation_at_weyl_image (p q v n : H) (word : n = p * q * p)
    :
    MulAut.conj p v = MulAut.conj q⁻¹ (MulAut.conj p⁻¹ (MulAut.conj n v)) := by
  have h : q⁻¹ * (p⁻¹ * n) = p := by rw [word]; group
  rw [conjugation_composition, conjugation_composition, mul_assoc, h]

private theorem map_conjugation (φ : H ≃* H) (x y : H) :
    φ (MulAut.conj x y) = MulAut.conj (φ x) (φ y) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private def radicalWord (p : RootIndex → K → H) (v : Radical K) : H :=
  p b v.1 * (p c v.2.1 * (p d v.2.2.1 * (p e v.2.2.2.1 * p f v.2.2.2.2)))

private theorem radicalSeparation (p : RootIndex → K → H) (zero : ∀ r, p r 0 = 1)
    (h : SeparatesCoordinates p .g2) : Function.Injective (radicalWord p) := by
  rintro ⟨b₁, c₁, d₁, e₁, f₁⟩ ⟨b₂, c₂, d₂, e₂, f₂⟩ hv
  have hv' : orderedWord p (positiveList .g2) (parameters 0 b₁ c₁ d₁ e₁ f₁) =
      orderedWord p (positiveList .g2) (parameters 0 b₂ c₂ d₂ e₂ f₂) := by
    simpa only [radicalWord, orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      parameters_a, parameters_b, parameters_c, parameters_d, parameters_e, parameters_f,
      zero, one_mul, mul_one] using hv
  exact Prod.ext (h _ _ hv' b (by decide)) (Prod.ext (h _ _ hv' c (by decide))
    (Prod.ext (h _ _ hv' d (by decide)) (Prod.ext (h _ _ hv' e (by decide)) (h _ _ hv' f (by decide)))))

private theorem radicalWord_mul (p : RootIndex → K → H)
    (add : ∀ r x y, p r (x + y) = p r x * p r y) (j z : K)
    (bc : ∀ x y, Commute (p b x) (p c y)) (bd : ∀ x y, Commute (p b x) (p d y))
    (ce : ∀ x y, Commute (p c x) (p e y)) (de : ∀ x y, Commute (p d x) (p e y))
    (center : ∀ r ∈ positiveList .g2, ∀ x y, Commute (p f x) (p r y))
    (eb : ∀ x y, p e y * p b x = p b x * (p e y * p f (-(j * x * y))))
    (dc : ∀ x y, p d y * p c x = p c x * (p d y * p f (-(z * x * y))))
    (v w : Radical K) :
    radicalWord p v * radicalWord p w =
    radicalWord p (v.1 + w.1, v.2.1 + w.2.1, v.2.2.1 + w.2.2.1,
      v.2.2.2.1 + w.2.2.2.1,
      -(j * w.1 * v.2.2.2.1) + (-(z * w.2.1 * v.2.2.1) + (v.2.2.2.2 + w.2.2.2.2))) := by
  rcases v with ⟨b₁, c₁, d₁, e₁, f₁⟩
  rcases w with ⟨b₂, c₂, d₂, e₂, f₂⟩
  dsimp only [radicalWord]
  have move (r : RootIndex) (hr : r ∈ positiveList .g2) {i u : K} {g : H} :
      p f i * (p r u * g) = p r u * (p f i * g) := by
    rw [← mul_assoc, (center r hr i u).eq, mul_assoc]
  have moveB {r : RootIndex} {u : K} {g : H}
      (h : Commute (p b b₂) (p r u)) :
      p r u * (p b b₂ * g) = p b b₂ * (p r u * g) := by
    rw [← mul_assoc, h.symm.eq, mul_assoc]
  have moveC {r : RootIndex} {u : K} {g : H}
      (h : Commute (p c c₂) (p r u)) :
      p r u * (p c c₂ * g) = p c c₂ * (p r u * g) := by
    rw [← mul_assoc, h.symm.eq, mul_assoc]
  have combine {r : RootIndex} {i u : K} {g : H} :
      p r i * (p r u * g) = p r (i + u) * g := by rw [← mul_assoc, add]
  simp only [mul_assoc]
  rw [move b (by decide), ← mul_assoc (p e e₁) (p b b₂), eb, mul_assoc, mul_assoc (p e e₁),
    moveB (bd _ _), moveB (bc _ _), combine]
  rw [move c (by decide), move c (by decide), moveC (ce _ _), ← mul_assoc (p d d₁) (p c c₂), dc,
    mul_assoc, mul_assoc (p d d₁), combine]
  rw [move d (by decide), move d (by decide), ← mul_assoc (p e e₁) (p d d₂),
    (de _ _).symm.eq]
  simp only [mul_assoc]
  rw [move d (by decide), combine]
  rw [move e (by decide), move e (by decide), move e (by decide), move e (by decide), combine]
  simp only [← add]
  congr 5 <;> ring

private theorem neg_one_square : (-1 : K) ^ (2 : ℕ) = 1 := by ring

private theorem neg_one_cube : (-1 : K) ^ (3 : ℕ) = -1 := by ring

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4500000 in
private theorem g2Coefficients (p : RootIndex → K → H)
    (zero : ∀ r, p r 0 = 1) (add : ∀ r x y, p r (x + y) = p r x * p r y)
    (neg : ∀ r x, p r (-x) = (p r x)⁻¹)
    (separates : SeparatesCoordinates p .g2) (Nₐ Nᵦ : H)
    (wordₐ : Nₐ = p a 1 * p (-a) (-1) * p a 1)
    (wordᵦ : Nᵦ = p b 1 * p (-b) (-1) * p b 1)
    (swapₐ : MulAut.conj Nₐ (p a 1) = p (-a) (-1))
    (swapᵦ : MulAut.conj Nᵦ (p b 1) = p (-b) (-1))
    (ae : ∀ x y, Commute (p a x) (p e y))
    (bc : ∀ x y, Commute (p b x) (p c y)) (bd : ∀ x y, Commute (p b x) (p d y))
    (ce : ∀ x y, Commute (p c x) (p e y)) (de : ∀ x y, Commute (p d x) (p e y))
    (center : ∀ r ∈ positiveList .g2, ∀ x y, Commute (p f x) (p r y))
    (a_on_b : ∀ y, MulAut.conj Nₐ (p b y) = p e y)
    (a_on_c : ∀ y, MulAut.conj Nₐ (p c y) = p d y)
    (a_on_d : ∀ y, MulAut.conj Nₐ (p d y) = p c (-y))
    (a_on_e : ∀ y, MulAut.conj Nₐ (p e y) = p b (-y))
    (a_on_f : ∀ y, MulAut.conj Nₐ (p f y) = p f y)
    (b_on_a : ∀ x, MulAut.conj Nᵦ (p a x) = p c x)
    (b_on_c : ∀ y, MulAut.conj Nᵦ (p c y) = p a (-y))
    (b_on_d : ∀ y, MulAut.conj Nᵦ (p d y) = p d y)
    (b_on_e : ∀ y, MulAut.conj Nᵦ (p e y) = p f y)
    (b_on_f : ∀ y, MulAut.conj Nᵦ (p f y) = p e (-y))
    (m n v w t l g h j z : K)
    (ab : ∀ x y, MulAut.conj (p a x) (p b y) = p b y * (p c (m * x * y) *
      (p d (n * x ^ 2 * y) * (p e (v * x ^ 3 * y) * p f (w * x ^ 3 * y ^ 2)))))
    (ac : ∀ x y, MulAut.conj (p a x) (p c y) = p c y * (p d (t * x * y) *
      (p e (l * x ^ 2 * y) * p f (g * x * y ^ 2))))
    (ad : ∀ x y, MulAut.conj (p a x) (p d y) = p d y * p e (h * x * y))
    (be : ∀ x y, MulAut.conj (p b x) (p e y) = p e y * p f (j * x * y))
    (cd : ∀ x y, MulAut.conj (p c x) (p d y) = p d y * p f (z * x * y)) :
    m = -1 ∧ n = 1 ∧ v = 1 ∧ w = 1 ∧ t = -2 ∧ l = -3 ∧ g = 3 ∧ h = 3 ∧ j = 1 ∧ z = 3 := by
  have inject := radicalSeparation p zero separates
  have eb (x y : K) : p e y * p b x = p b x * (p e y * p f (-(j * x * y))) := by
    apply swapped
    rw [← neg, be, mul_neg, neg_mul]
  have dc (x y : K) : p d y * p c x = p c x * (p d y * p f (-(z * x * y))) := by
    apply swapped
    rw [← neg, cd, mul_neg, neg_mul]
  have combine (q q' : Radical K) := radicalWord_mul p add j z bc bd ce de center eb dc q q'
  have testⱼ := conjugation_of_weyl_word (p b 1) (p (-b) (-1)) (p e 1) Nᵦ wordᵦ swapᵦ
    (by rw [b_on_e]; exact (center b (by decide) 1 1).symm)
  simp only [← neg, be, map_mul, b_on_e, b_on_f, mul_one, mul_neg, neg_neg] at testⱼ
  rw [(center e (by decide) 1 j).eq] at testⱼ
  have ej := inject (a₁ := (0, 0, 0, 1, j)) (a₂ := (0, 0, 0, j, 1)) (by
    simpa only [radicalWord, zero, one_mul] using testⱼ)
  have hj : j = 1 := congrArg (fun q : Radical K => q.2.2.2.2) ej
  have hzh : z = h := by
    have eh := congrArg (MulAut.conj Nᵦ) (ad 1 1)
    simp only [map_conjugation, map_mul, b_on_a, b_on_d, b_on_e, mul_one] at eh
    have ht : p d 1 * p f z = p d 1 * p f h :=
      (by simpa only [mul_one] using (cd 1 1).symm :
        p d 1 * p f z = MulAut.conj (p c 1) (p d 1)).trans eh
    have ep := inject (a₁ := (0, 0, 1, 0, z)) (a₂ := (0, 0, 1, 0, h)) (by
      simpa only [radicalWord, zero, one_mul] using ht)
    exact congrArg (fun q : Radical K => q.2.2.2.2) ep
  have testₐ := conjugation_of_weyl_word (p a 1) (p (-a) (-1)) (p b 1) Nₐ wordₐ swapₐ
    (by rw [a_on_b]; exact ae 1 1)
  have hₐ : radicalWord p (1, m, n, v, w) =
      p e 1 * (p d (-m) * (p c (-n) * (p b v * p f (-w)))) := by
    simpa only [← neg, ab, map_mul, a_on_b, a_on_c, a_on_d, a_on_e, a_on_f, mul_one,
      one_pow, neg_sq, neg_one_cube, mul_neg, neg_neg, radicalWord]
      using testₐ
  have ha' : radicalWord p (1, m, n, v, w) =
      radicalWord p (v, -n, -m, 1, -(j * v * 1) + (-(z * (-n) * (-m)) + -w)) := by
    calc
      _ = radicalWord p (0, 0, 0, 1, 0) *
          (radicalWord p (0, 0, -m, 0, 0) *
            (radicalWord p (0, -n, 0, 0, 0) * radicalWord p (v, 0, 0, 0, -w))) := by
        simpa only [radicalWord, zero, one_mul, mul_one] using hₐ
      _ = _ := by simp only [combine, add_zero, zero_add, mul_zero, zero_mul, neg_zero]
  have haeq := inject ha'
  have hv : v = 1 := (congrArg Prod.fst haeq).symm
  have hn' : m = -n := congrArg (fun q : Radical K => q.2.1) haeq
  have hw' : w = -(j * v * 1) + (-(z * (-n) * (-m)) + -w) :=
    congrArg (fun q : Radical K => q.2.2.2.2) haeq
  have ba (x y : K) : MulAut.conj (p b y) (p a x) = p a x * (p c (m * (-x) * y) *
      (p d (n * x ^ 2 * y) * (p e (v * (-x) ^ 3 * y) * p f ((- (w + j * v)) * x ^ 3 * y ^ 2)))) := by
    have he := reverse_conjugation (p := p a x) (q := p b y)
      (t := p c (m * (-x) * y) * (p d (n * (-x) ^ 2 * y) *
        (p e (v * (-x) ^ 3 * y) * p f (w * (-x) ^ 3 * y ^ 2)))) (by rw [← neg]; exact ab (-x) y)
    simp only [map_mul, commute_conjugation (bc y _), commute_conjugation (bd y _),
      commute_conjugation (center b (by decide) _ y).symm, neg_sq, be, mul_assoc, ← add] at he
    have hc : j * (y * (v * ((-x) ^ 3 * y))) + w * ((-x) ^ 3 * y ^ 2) =
        -(w + j * v) * x ^ 3 * y ^ 2 := by ring
    rw [hc] at he
    simpa only [mul_assoc] using he
  have testᵦ := conjugation_of_weyl_word (p b 1) (p (-b) (-1)) (p a 1) Nᵦ wordᵦ swapᵦ
    (by rw [b_on_a]; exact bc 1 1)
  have hb' : p a 1 * radicalWord p (0, -m, n, -v, -(w + j * v)) =
      p c 1 * (p a (-m) * (p d (-n) * (p f v * p e (w + j * v)))) := by
    simpa only [← neg, ba, map_mul, b_on_a, b_on_c, b_on_d, b_on_e, b_on_f, mul_one,
      one_pow, neg_one_square, neg_one_cube, neg_neg, neg_mul, mul_neg,
      radicalWord, zero, one_mul] using testᵦ
  have ca : p c 1 * p a (-m) = p a (-m) * (p c 1 *
      (p d (t * m) * (p e (l * m ^ 2) * p f (g * m)))) := by
    apply swapped
    rw [← neg, neg_neg, ac, mul_one, mul_one, one_pow, mul_one]
  have hb : p a 1 * radicalWord p (0, -m, n, -v, -(w + j * v)) =
      p a (-m) * radicalWord p (0, 1, t * m - n, l * m ^ 2 + (w + j * v), g * m + v) := by
    have hw₁ : p c 1 * (p a (-m) * (p d (-n) * (p f v * p e (w + j * v)))) =
        p a (-m) * (radicalWord p (0, 1, t * m, l * m ^ 2, g * m) *
          radicalWord p (0, 0, -n, w + j * v, v)) := by
      rw [← mul_assoc (p c 1), ca, (center e (by decide) v _).eq]
      simp only [mul_assoc, radicalWord, zero, one_mul]
    rw [hb', hw₁, combine]
    simp only [add_zero, zero_add, mul_zero, zero_mul, neg_zero, sub_eq_add_neg]
  have eᵦ : orderedWord p (positiveList .g2) (parameters 1 0 (-m) n (-v) (-(w + j * v))) =
      orderedWord p (positiveList .g2) (parameters (-m) 0 1 (t * m - n)
        (l * m ^ 2 + (w + j * v)) (g * m + v)) := by
    simpa only [radicalWord, orderedWord, positiveList, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, parameters_a, parameters_b, parameters_c, parameters_d, parameters_e,
      parameters_f, zero, one_mul, mul_one] using hb
  have hm' : (1 : K) = -m := separates _ _ eᵦ a (by decide)
  have hm : m = -1 := by linear_combination hm'
  have hn : n = 1 := by rw [hm] at hn'; linear_combination hn'
  have ht : n = t * m - n := separates _ _ eᵦ d (by decide)
  have hl : -v = l * m ^ 2 + (w + j * v) := separates _ _ eᵦ e (by decide)
  have hg : -(w + j * v) = g * m + v := separates _ _ eᵦ f (by decide)
  rw [hm, hn, hv, hj, hzh] at hw'
  rw [hm, hn] at ht
  rw [hm, hv, hj] at hl hg
  have testC := conjugation_at_weyl_image (p a 1) (p (-a) (-1)) (p c 1) Nₐ wordₐ
  have hmove (q : H) : MulAut.conj (p (-a) (-1))⁻¹ q =
      MulAut.conj Nₐ (MulAut.conj (p a (-1)) (MulAut.conj Nₐ⁻¹ q)) := by
    rw [conjugation_composition, conjugation_composition, neg a (1 : K), ← swapₐ]
    simp only [MulAut.conj_apply]
    group
  rw [hmove, a_on_c, ← neg a (1 : K), ad, map_mul, mul_one, mul_neg] at testC
  have ht₁ : MulAut.conj Nₐ⁻¹ (p d 1) = p c 1 := by
    rw [← a_on_c, conjugation_composition, inv_mul_cancel]
    simp [MulAut.conj_apply]
  have ht₂ : MulAut.conj Nₐ⁻¹ (p e (-h)) = p b (-h) := by
    rw [← a_on_b, conjugation_composition, inv_mul_cancel]
    simp [MulAut.conj_apply]
  simp only [ht₁, ht₂, ac, ab, map_mul, a_on_b, a_on_c, a_on_d, a_on_e, a_on_f,
    mul_one, neg_sq, one_pow, mul_neg, neg_neg, neg_mul, hm, hn, hv, one_mul] at testC
  have rearrange (x1 x2 x3 x4 : K) : p d x1 * (p c x2 * (p b x3 * p f x4)) =
      radicalWord p (x3, x2, x1, 0, -(z * x2 * x1) + x4) := by
    have ht : p d x1 * (p c x2 * (p b x3 * p f x4)) = radicalWord p (0, 0, x1, 0, 0) *
        (radicalWord p (0, x2, 0, 0, 0) * radicalWord p (x3, 0, 0, 0, x4)) := by
      simp only [radicalWord, zero, one_mul, mul_one]
    rw [ht, combine, combine]
    simp only [add_zero, zero_add, mul_zero, zero_mul, neg_zero]
  have rearrange' (x1 x2 x3 x4 x5 : K) :
      p e x1 * (p d x2 * (p c x3 * (p b x4 * p f x5))) =
      radicalWord p (x4, x3, x2, x1, -(j * x4 * x1) + (-(z * x3 * x2) + x5)) := by
    have ht : p e x1 * (p d x2 * (p c x3 * (p b x4 * p f x5))) =
        radicalWord p (0, 0, 0, x1, 0) * radicalWord p (x4, x3, x2, 0, -(z * x3 * x2) + x5) := by
      rw [rearrange]
      simp only [radicalWord, zero, one_mul, mul_one]
    rw [ht, combine]
    simp only [add_zero, zero_add, mul_zero, zero_mul, neg_zero]
  have hel : l = -h := by
    have hwords : radicalWord p (0, 1, t, l, g) =
        (p d 1 * (p c t * (p b (-l) * p f (-g)))) *
        (p e (-h) * (p d (-h) * (p c h * (p b (-h) * p f (-(w * h ^ 2)))))) := by
      simpa only [radicalWord, zero, one_mul, neg_one_cube,
        mul_neg, neg_neg, neg_mul, mul_one, neg_sq, one_pow] using testC
    rw [rearrange, rearrange', combine] at hwords
    simpa only [zero_add] using congrArg (fun q : Radical K => q.2.2.2.1) (inject hwords)
  have hw : w = 1 := by linear_combination hw' + hl + hel
  rw [hw] at hw' hl hg
  refine ⟨hm, hn, hv, hw, ?_, ?_, ?_, ?_, hj, ?_⟩
  · linear_combination ht
  · linear_combination -hl
  · linear_combination hg
  · linear_combination -hw'
  · linear_combination hzh - hw'

end GroupCalculations

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open CategoryTheory.MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue)
open Specs.Pinning (RootCoordinate)
open Specs.RootGroups (CorootReflection HasScalarAction IsRootSubgroup rootPoint rankOneWord)
open LinearAlgebraicGroups.CocharacterDynamics


section RootLabels

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing characterValue)
open Specs.RootGroups (CorootReflection HasScalarAction rootPoint rankOneWord)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

private theorem Frame.character_a (F : Frame P τ) : F.character a = F.first.val.val := by
  simp [Specs.RankTwoRelations.Frame.character, a]

private theorem Frame.character_b (F : Frame P τ) : F.character b = F.second.val.val := by
  simp [Specs.RankTwoRelations.Frame.character, b]

private theorem Frame.mem_roots (F : Frame P τ) {s : RootIndex} (hs : IsIndex τ s) :
    F.character s ∈ absoluteRoots P.pair.T := (F.root ⟨s, hs⟩).property

private theorem Frame.root_a (F : Frame P τ) (ha : IsIndex τ a) :
    F.root ⟨a, ha⟩ = F.first.val := Subtype.ext (Frame.character_a F)

private theorem Frame.root_b (F : Frame P τ) (hb : IsIndex τ b) :
    F.root ⟨b, hb⟩ = F.second.val := Subtype.ext (Frame.character_b F)

private theorem Frame.pairing_character (F : Frame P τ) (r : RootIndex)
    (t : Cocharacter P.pair.T.group) :
    pairing P.pair.T.group (F.character r) t =
      r.1 * pairing P.pair.T.group F.first.val.val t +
        r.2 * pairing P.pair.T.group F.second.val.val t := by
  let T := P.pair.T.group
  obtain ⟨h, hp⟩ := RootData.CharacterPairing.perfectCharacterPairing T P.pair.split
  letI := h
  obtain ⟨_, _, _, _, pl, _, he⟩ := hp
  rw [← he (F.character r) t, ← he F.first.val.val t, ← he F.second.val.val t]
  change pl (r.1 • Additive.ofMul F.first.val.val + r.2 • Additive.ofMul F.second.val.val)
      (Additive.ofMul t) = _
  simp only [map_add, LinearMap.add_apply, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_id]
  rfl

private theorem positiveList_coefficients {r : RootIndex} (hr : r ∈ positiveList τ) :
    0 ≤ r.1 ∧ 0 ≤ r.2 ∧ (r.1 ≠ 0 ∨ r.2 ≠ 0) := by
  have h : ∀ r ∈ positiveList τ, 0 ≤ r.1 ∧ 0 ≤ r.2 ∧ (r.1 ≠ 0 ∨ r.2 ≠ 0) := by
    cases τ <;> decide
  exact h r hr

private theorem Frame.positive_iff_of_positive_simple (F : Frame P τ)
    (t : Cocharacter P.pair.T.group)
    (ha : 0 < pairing P.pair.T.group F.first.val.val t)
    (hb : 0 < pairing P.pair.T.group F.second.val.val t) (r : Index τ) :
    F.root r ∈ positiveRoots P.pair.T t ↔ r.val ∈ positiveList τ := by
  have hpos (s : RootIndex) (hs : s ∈ positiveList τ) :
      0 < pairing P.pair.T.group (F.character s) t := by
    rw [Frame.pairing_character]
    obtain ⟨h₁, h₂, hne⟩ := positiveList_coefficients hs
    rcases hne with hne | hne
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne h₁ (Ne.symm hne)) ha)
        (mul_nonneg h₂ hb.le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg h₁ ha.le)
        (mul_pos (lt_of_le_of_ne h₂ (Ne.symm hne)) hb)
  refine ⟨?_, hpos r.val⟩
  intro hr
  change 0 < pairing P.pair.T.group (F.character r) t at hr
  rcases r.property with hp | hn
  · exact hp
  · have hneg := hpos (-r.val) hn
    rw [Frame.pairing_character] at hneg hr
    simp only [Prod.fst_neg, Prod.snd_neg, neg_mul, ← neg_add] at hneg
    omega

private def Frame.rootEquiv (F : Frame P τ) : Index τ ≃ Root P.pair.T :=
  Equiv.ofBijective F.root ⟨fun _ _ h => Subtype.ext (F.independent (congrArg Subtype.val h)), by
    intro r
    obtain ⟨s, hs⟩ := (F.root_iff r.val).mp r.property
    exact ⟨s, Subtype.ext hs.symm⟩⟩

private theorem Frame.subgroupRoots_iff (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u}) :
    ∀ r : Index τ, F.root r ∈ subgroupRoots P.pair.T P.pair.B ↔ r.val ∈ positiveList τ := by
  obtain ⟨t, _, _, _, ht⟩ := (borels P.pair.G P.pair.reductive P.pair.T P.pair.split
    P.pair.maximal).1 P.pair.B P.pair.borel P.pair.containsTorus
  rw [ht]
  exact Frame.positive_iff_of_positive_simple F t
    (show F.first.val ∈ positiveRoots P.pair.T t from ht ▸ F.first.property.1)
    (show F.second.val ∈ positiveRoots P.pair.T t from ht ▸ F.second.property.1)

private theorem point_eq_rootPoint (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (s : Index τ) (z : R) :
    point F X R s z = rootPoint (rootMap X (F.root s)) R z := by
  unfold point
  rw [dif_pos (Frame.mem_roots F s.property)]
  rfl

open private rootPoint_add rootPoint_zero pointMap representative_eq_word
  from LinearAlgebraicGroups.Classification.RankOneRelations
open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_injective from LinearAlgebraicGroups.RootData.OrderedRootProducts

private theorem point_add (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (s : RootIndex) (x y : R) :
    point F X R s (x + y) = point F X R s x * point F X R s y := by
  unfold point
  split
  · exact rootPoint_add _ _ _ _
  · simp

private theorem point_zero (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (s : RootIndex) : point F X R s 0 = 1 := by
  unfold point
  split
  · exact rootPoint_zero _ _
  · rfl

private theorem point_injective (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (s : Index τ) : Function.Injective (point F X R s) := by
  intro x y h
  simp only [point_eq_rootPoint F X R s] at h
  let V := (P.roots (F.root s)).val
  letI := V.isClosedImmersion
  haveI : Mono V.inclusion.hom.hom := Over.mono_of_mono_left _
  apply rootPoint_injective (X.coordinate (F.root s)).val R
  change (rootPoint (X.coordinate (F.root s)).val.hom R x) =
    (rootPoint (X.coordinate (F.root s)).val.hom R y)
  apply (cancel_mono V.inclusion.hom.hom).mp
  let xV := (X.coordinate (F.root s)).val.hom
  change rootPoint (xV ≫ V.inclusion) R x = rootPoint (xV ≫ V.inclusion) R y at h
  exact (rootPoint_comp xV V.inclusion R x).symm.trans
    (h.trans (rootPoint_comp xV V.inclusion R y))

private theorem point_scalar (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (t : GroupPoints P.pair.T.group R) (s : Index τ) (x : R) :
    let g := pointMap R P.pair.T.inclusion t
    g * point F X R s x * g⁻¹ = point F X R s (characterValue (F.character s) R t * x) := by
  simp only [point_eq_rootPoint]
  exact (X.coordinate (F.root s)).property R t x

end RootLabels

section TorusTransport

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Character)
open Specs.Pinning (RootCoordinate)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.RootGroups (CorootReflection HasScalarAction IsRootSubgroup rootPoint)
open private innerMap innerIso comp_innerMap transportSubgroup
  from LinearAlgebraicGroups.Reductive.BorelProper
open private conjugation_maps_roots pointConj from LinearAlgebraicGroups.RootData.AbstractPairing
open private normalizes_of_point_conjugation tangent_weight_of_scalarAction rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups
open private rootPoint_surjective subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag
open private pointMap from LinearAlgebraicGroups.Classification.RankOneRelations

set_option backward.isDefEq.respectTransparency false in
private theorem transportCoordinate (P : PinnedGroup A) (r s : Root P.pair.T)
    (x : RootCoordinate A P.pair.T (P.roots r).val r.val)
    (g : 𝟙_ (SchemeOver k) ⟶ P.pair.G.val.X) (w : P.pair.T.group ≅ P.pair.T.group)
    (hg : (w.hom ≫ P.pair.T.inclusion).hom.hom =
      (toUnit P.pair.T.group.X ≫ g) * P.pair.T.inclusion.hom.hom *
        (toUnit P.pair.T.group.X ≫ g)⁻¹)
    (hw : w.inv ≫ r.val = s.val) :
    ∃ y : RootCoordinate A P.pair.T (P.roots s).val s.val,
      ∀ (R : TestAlgebra k) (v : R),
        let n : GroupPoints P.pair.G.val R := toUnit _ ≫ g
        n * rootPoint (x.val.hom ≫ (P.roots r).val.inclusion) R v * n⁻¹ =
          rootPoint (y.val.hom ≫ (P.roots s).val.inclusion) R v := by
  let T := P.pair.T
  let G := P.pair.G.val
  let U := (P.roots r).val
  let V := (P.roots s).val
  let j := innerIso g
  let U' := transportSubgroup U j
  have hx : HasScalarAction T s.val (x.val.hom ≫ U'.inclusion) := by
    intro R t v
    let t₀ : GroupPoints T.group R := t ≫ w.inv.hom.hom
    have htorus : pointMap R j.hom (pointMap R T.inclusion t₀) = pointMap R T.inclusion t := by
      have h₁ : (t₀ ≫ T.inclusion.hom.hom) ≫ (innerMap g).hom.hom =
          t₀ ≫ (w.hom ≫ T.inclusion).hom.hom := by
        rw [comp_innerMap, hg, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
          ← Category.assoc t₀ (toUnit T.group.X), comp_toUnit]
      have h₂ : t₀ ≫ (w.hom ≫ T.inclusion).hom.hom = t ≫ T.inclusion.hom.hom := by
        change t ≫ (w.inv ≫ w.hom ≫ T.inclusion).hom.hom = _
        rw [Iso.inv_hom_id_assoc]
      exact h₁.trans h₂
    have hχ : Specs.CharacterPairing.characterValue r.val R t₀ =
        Specs.CharacterPairing.characterValue s.val R t := by
      rw [← hw]
      unfold Specs.CharacterPairing.characterValue t₀
      simp only [Category.assoc]
      rfl
    have hroot (z : R) : pointMap R j.hom (rootPoint (x.val.hom ≫ U.inclusion) R z) =
        rootPoint (x.val.hom ≫ U'.inclusion) R z := by
      simp only [rootPoint, transportSubgroup, Category.assoc]
      rfl
    let z : GroupPoints G R := t₀ ≫ T.inclusion.hom.hom
    have h := congrArg (pointMap R j.hom) (x.property R t₀ v)
    change pointMap R j.hom (z * rootPoint (x.val.hom ≫ U.inclusion) R v * z⁻¹) =
        pointMap R j.hom (rootPoint (x.val.hom ≫ U.inclusion) R
          (characterValue r.val R t₀ * v)) at h
    have hz : pointMap R j.hom z = pointMap R T.inclusion t := htorus
    change pointMap R T.inclusion t * rootPoint (x.val.hom ≫ U'.inclusion) R v *
      (pointMap R T.inclusion t)⁻¹ = _
    simpa only [map_mul, map_inv, hz, hroot, hχ] using h
  have hU' : IsRootSubgroup T U' s.val := by
    refine ⟨(P.roots r).property.1, (P.roots r).property.2.1, ?_,
      tangent_weight_of_scalarAction T U' s.val A x.val hx⟩
    apply normalizes_of_point_conjugation
    intro R t p
    obtain ⟨z, rfl⟩ := rootPoint_surjective x.val R p
    refine ⟨rootPoint x.val.hom R (Specs.CharacterPairing.characterValue s.val R t * z), ?_⟩
    simpa only [rootPoint_comp] using (hx R t z).symm
  obtain ⟨W, _, _, _, _, unique⟩ := ((RootData.RootGroups.rootSubgroups P.pair.G
    P.pair.reductive T P.pair.split P.pair.maximal).2 s.val s.property).2.2
  have h₁ := unique U' hU'
  have h₂ := unique V (P.roots s).property
  let iso := subgroupIso (same_subgroup_trans ⟨h₁.2, h₁.1⟩ h₂)
  have himage : (x.val ≪≫ iso.val).hom ≫ V.inclusion = x.val.hom ≫ U'.inclusion := by
    simp only [Iso.trans_hom, Category.assoc, iso.property]
  refine ⟨⟨x.val ≪≫ iso.val, himage.symm ▸ hx⟩, ?_⟩
  intro R v
  rw [himage]
  let jx := x.val.hom ≫ U.inclusion
  have he : rootPoint (x.val.hom ≫ U'.inclusion) R v =
      rootPoint jx R v ≫ (innerMap g).hom.hom := by
    change rootPoint (x.val.hom ≫ U.inclusion ≫ innerMap g) R v = _
    rw [← Category.assoc]
    exact rootPoint_comp jx (innerMap g) R v
  exact (comp_innerMap g (rootPoint jx R v)).symm.trans he.symm

private theorem reflection_preserves_roots {T : ClosedSubgroup P.pair.G.val}
    {α : Character T.group} {x y : A.group ⟶ P.pair.G.val}
    (w : CorootReflection T α x y) (r : Root T) :
    (w.conjugation.inv ≫ r.val) ∈ absoluteRoots T :=
  conjugation_maps_roots w.conjugation w.representative w.conjugates r.property

end TorusTransport

section LinkedCoordinates

open Specs.AbstractPairing (Root)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open Specs.Pinning (RootCoordinate)
open Specs.RootGroups (CorootReflection HasScalarAction IsRootSubgroup rankOneWord rootPoint)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)
open private rescale rescale_point coordinate_change coordinate_ext from LinearAlgebraicGroups.Classification.Pinning
open private rankOneRepresentative rankOneRepresentative_point
  from LinearAlgebraicGroups.RootData.RootGroups
open private torusPointHom torusPointHom_apply word_eq_torus_mul
  from LinearAlgebraicGroups.Classification.RankOneRelations
open private subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private same_subgroup_trans from LinearAlgebraicGroups.RootData.RankOneFlag

private theorem rescaleLinkedPair {B : AdditiveLine k} {G : GroupScheme k}
    {T U V : ClosedSubgroup G} (hT : Specs.GeometricRadicals.IsSplitTorus T.group)
    {α : Specs.CharacterDescent.Character T.group}
    (xp : RootCoordinate B T U α) (xn : RootCoordinate B T V α⁻¹)
    (r : CorootReflection T α (xp.val.hom ≫ U.inclusion) (xn.val.hom ≫ V.inclusion))
    (s : kˣ) :
    Nonempty (CorootReflection T α
      ((rescale (A := A) xp s).val.hom ≫ U.inclusion)
      ((rescale (A := A) xn s⁻¹).val.hom ≫ V.inclusion)) := by
  let x := (rescale (A := A) xp s).val.hom ≫ U.inclusion
  let y := (rescale (A := A) xn s⁻¹).val.hom ≫ V.inclusion
  have hr (R : TestAlgebra k) (b : Rˣ) :
      rankOneWord x y R b = rankOneWord (xp.val.hom ≫ U.inclusion)
        (xn.val.hom ≫ V.inclusion) R (Units.map (algebraMap k R).toMonoidHom s * b) := by
    have hu : algebraMap k R (↑s⁻¹ : k) * -(↑b⁻¹ : R) =
        -(↑(Units.map (algebraMap k R).toMonoidHom s * b)⁻¹ : R) := by
      rw [mul_inv_rev, Units.val_mul, Units.coe_map_inv]
      change algebraMap k R (↑s⁻¹ : k) * -(↑b⁻¹ : R) =
        -(↑b⁻¹ * algebraMap k R (↑s⁻¹ : k))
      rw [mul_neg, mul_comm]
    simp only [x, y, rankOneWord, rescale_point, hu]
    rfl
  apply RootData.RootGroups.corootReflection_of_word T hT α x y
    (rescale (A := A) xp s).property (rescale (A := A) xn s⁻¹).property
    r.coroot (rankOneRepresentative x y) (rankOneRepresentative_point x y) _ r.root_pairing
  intro R b
  let sR : Rˣ := Units.map (algebraMap k R).toMonoidHom s
  rw [hr R b, hr R 1, mul_one, word_eq_torus_mul r R (sR * b),
    word_eq_torus_mul r R sR, map_mul, ← torusPointHom_apply]
  rw [((Commute.all sR b).map (torusPointHom T r.coroot R)).eq]
  group

/-- Any specified coordinate on an actual root subgroup extends to the
linked opposite coordinate, using the rank-one transvection normalization. -/
theorem linkedOppositeCoordinate (P : PinnedGroup A) (α β : Root P.pair.T)
    (hβ : β.val = α.val⁻¹) (x : RootCoordinate A P.pair.T (P.roots α).val α.val) :
    ∃ y : RootCoordinate A P.pair.T (P.roots β).val β.val,
      Nonempty (CorootReflection P.pair.T α.val
        (x.val.hom ≫ (P.roots α).val.inclusion) (y.val.hom ≫ (P.roots β).val.inclusion)) := by
  obtain ⟨C, cochar, _, _, D, E, _, Q, F, L, B, p, n, hp, hn, hxp, hxn, ⟨r⟩⟩ :=
    RootData.RootGroups.rankOneRootGroups P.pair.G P.pair.reductive P.pair.T
      P.pair.split P.pair.maximal α.val α.property
  let U := subgroupOfSubgroup C.subgroup D.contracting
  let V := subgroupOfSubgroup C.subgroup E.contracting
  have rootIso (χ : Root P.pair.T) (S : ClosedSubgroup P.pair.G.val)
      (hS : IsRootSubgroup P.pair.T S χ.val) :
      Specs.RankOneFlag.SameSubgroup S (P.roots χ).val := by
    obtain ⟨W, _, _, _, _, uniq⟩ := ((RootData.RootGroups.rootSubgroups P.pair.G
      P.pair.reductive P.pair.T P.pair.split P.pair.maximal).2 χ.val χ.property).2.2
    have h₁ := uniq S hS
    have h₂ := uniq (P.roots χ).val (P.roots χ).property
    exact same_subgroup_trans ⟨h₁.2, h₁.1⟩ h₂
  let eu := subgroupIso (rootIso α U hp)
  let ev := subgroupIso (rootIso β V (hβ.symm ▸ hn))
  let xp := p.root ≪≫ eu.val
  let xn := n.root ≪≫ ev.val
  have eqp : xp.hom ≫ (P.roots α).val.inclusion =
      p.root.hom ≫ D.contracting.inclusion ≫ C.subgroup.inclusion := by
    simp only [xp, Iso.trans_hom, Category.assoc, eu.property, U, subgroupOfSubgroup]
  have eqn : xn.hom ≫ (P.roots β).val.inclusion =
      n.root.hom ≫ E.contracting.inclusion ≫ C.subgroup.inclusion := by
    simp only [xn, Iso.trans_hom, Category.assoc, ev.property, V, subgroupOfSubgroup]
  let xp' : RootCoordinate B P.pair.T (P.roots α).val α.val := ⟨xp, eqp.symm ▸ hxp⟩
  let xn' : RootCoordinate B P.pair.T (P.roots β).val α.val⁻¹ := ⟨xn, eqn.symm ▸ hxn⟩
  have r' : CorootReflection P.pair.T α.val
      (xp'.val.hom ≫ (P.roots α).val.inclusion) (xn'.val.hom ≫ (P.roots β).val.inclusion) := by
    change CorootReflection _ _ (xp.hom ≫ _) (xn.hom ≫ _)
    rw [eqp, eqn]
    exact r
  obtain ⟨s, hs⟩ := coordinate_change (rescale (A := A) xp' 1) x
  have he : x = rescale xp' s := by
    apply coordinate_ext
    intro R t
    simp only [hs, rescale_point, Units.val_one, map_one, one_mul]
  rw [he]
  let y : RootCoordinate A P.pair.T (P.roots β).val α.val⁻¹ := rescale xn' s⁻¹
  let xneg : A.group ⟶ P.pair.G.val := y.val.hom ≫ (P.roots β).val.inclusion
  have hy : HasScalarAction P.pair.T β.val xneg :=
    Eq.mp (congrArg (fun χ => HasScalarAction P.pair.T χ xneg) hβ.symm) y.property
  let y' : RootCoordinate A P.pair.T (P.roots β).val β.val := ⟨y.val, hy⟩
  exact ⟨y', rescaleLinkedPair P.pair.split xp' xn' r' s⟩

end LinkedCoordinates

local instance (τ : TypeOfRoots) (r : RootIndex) : Decidable (IsIndex τ r) := by
  unfold IsIndex
  infer_instance

private def firstStringLength : TypeOfRoots → ℤ
  | .orthogonal => 0
  | .a2 => 1
  | .b2 => 2
  | .g2 => 3

private def secondStringLength : TypeOfRoots → ℤ
  | .orthogonal => 0
  | _ => 1

private theorem firstString_indices (τ : TypeOfRoots) (i : ℤ) :
    IsIndex τ (i, 1) ↔ 0 ≤ i ∧ i ≤ firstStringLength τ := by
  cases τ <;> simp [IsIndex, positiveList, a, b, c, d, e, f, firstStringLength,
    Prod.mk.injEq, Prod.fst_neg, Prod.snd_neg] <;> omega

private theorem secondString_indices (τ : TypeOfRoots) (i : ℤ) :
    IsIndex τ (1, i) ↔ 0 ≤ i ∧ i ≤ secondStringLength τ := by
  cases τ <;> simp [IsIndex, positiveList, a, b, c, d, e, f, secondStringLength,
    Prod.mk.injEq, Prod.fst_neg, Prod.snd_neg] <;> omega

private theorem firstStringLength_nonnegative (τ : TypeOfRoots) : 0 ≤ firstStringLength τ := by
  cases τ <;> decide

private theorem secondStringLength_nonnegative (τ : TypeOfRoots) : 0 ≤ secondStringLength τ := by
  cases τ <;> decide

private theorem index_a (τ : TypeOfRoots) : IsIndex τ a := by cases τ <;> decide

private theorem index_b (τ : TypeOfRoots) : IsIndex τ b := by cases τ <;> decide

section RootReflections

open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (pairing)
open Specs.RootGroups (CorootReflection)

private theorem Frame.character_shift_first (F : Frame P τ) (s : RootIndex) (n : ℤ) :
    F.character (s.1 + n, s.2) = F.character s * F.character a ^ n := by
  rw [Frame.character_a]
  simp only [Specs.RankTwoRelations.Frame.character, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

private theorem Frame.character_shift_second (F : Frame P τ) (s : RootIndex) (n : ℤ) :
    F.character (s.1, s.2 + n) = F.character s * F.character b ^ n := by
  rw [Frame.character_b]
  simp only [Specs.RankTwoRelations.Frame.character, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

private theorem Frame.root_iff_index (F : Frame P τ) (r : RootIndex) :
    F.character r ∈ absoluteRoots P.pair.T ↔ IsIndex τ r := by
  refine ⟨?_, Frame.mem_roots F⟩
  intro hr
  obtain ⟨s, hs⟩ := (F.root_iff _).mp hr
  exact (F.independent hs).symm ▸ s.property

private theorem Frame.firstCorootPairings (F : Frame P τ) {x y : A.group ⟶ P.pair.G.val}
    (w : CorootReflection P.pair.T (F.character a) x y) :
    pairing P.pair.T.group F.first.val.val w.coroot = 2 ∧
      pairing P.pair.T.group F.second.val.val w.coroot = -firstStringLength τ := by
  have ha : pairing P.pair.T.group F.first.val.val w.coroot = 2 :=
    (Frame.character_a F) ▸ w.root_pairing
  let n := pairing P.pair.T.group F.second.val.val w.coroot
  have h (s : Index τ) : IsIndex τ (s.val.1 - (2 * s.val.1 + n * s.val.2), s.val.2) := by
    have hroot := reflection_preserves_roots w (F.root s)
    change (w.conjugation.inv ≫ F.character s) ∈ _ at hroot
    rw [w.reflection, ← Frame.character_shift_first, Frame.pairing_character, ha] at hroot
    apply (Frame.root_iff_index F _).mp
    convert hroot using 2 <;> dsimp [n] <;> ring
  have h0 := h ⟨b, index_b τ⟩
  have he := h ⟨(firstStringLength τ, 1), (firstString_indices τ _).mpr
    ⟨firstStringLength_nonnegative τ, le_rfl⟩⟩
  change IsIndex τ (0 - (2 * 0 + n * 1), 1) at h0
  change IsIndex τ (firstStringLength τ - (2 * firstStringLength τ + n * 1), 1) at he
  rw [firstString_indices] at h0 he
  refine ⟨ha, ?_⟩
  change n = -firstStringLength τ
  omega

private theorem Frame.secondCorootPairings (F : Frame P τ) {x y : A.group ⟶ P.pair.G.val}
    (w : CorootReflection P.pair.T (F.character b) x y) :
    pairing P.pair.T.group F.first.val.val w.coroot = -secondStringLength τ ∧
      pairing P.pair.T.group F.second.val.val w.coroot = 2 := by
  have hb : pairing P.pair.T.group F.second.val.val w.coroot = 2 :=
    (Frame.character_b F) ▸ w.root_pairing
  let n := pairing P.pair.T.group F.first.val.val w.coroot
  have h (s : Index τ) : IsIndex τ (s.val.1, s.val.2 - (n * s.val.1 + 2 * s.val.2)) := by
    have hroot := reflection_preserves_roots w (F.root s)
    change (w.conjugation.inv ≫ F.character s) ∈ _ at hroot
    rw [w.reflection, ← Frame.character_shift_second, Frame.pairing_character, hb] at hroot
    apply (Frame.root_iff_index F _).mp
    convert hroot using 2 <;> dsimp [n] <;> ring
  have h0 := h ⟨a, index_a τ⟩
  have he := h ⟨(1, secondStringLength τ), (secondString_indices τ _).mpr
    ⟨secondStringLength_nonnegative τ, le_rfl⟩⟩
  change IsIndex τ (1, 0 - (n * 1 + 2 * 0)) at h0
  change IsIndex τ (1, secondStringLength τ - (n * 1 + 2 * secondStringLength τ)) at he
  rw [secondString_indices] at h0 he
  refine ⟨?_, hb⟩
  change n = -secondStringLength τ
  omega

private def simpleIndex (i : Bool) : RootIndex := if i then b else a

private def corootPairing (τ : TypeOfRoots) (i : Bool) (s : RootIndex) : ℤ :=
  if i then -secondStringLength τ * s.1 + 2 * s.2
  else 2 * s.1 - firstStringLength τ * s.2

private theorem Frame.corootPairing_eq (F : Frame P τ) (i : Bool)
    {x y : A.group ⟶ P.pair.G.val}
    (w : CorootReflection P.pair.T (F.character (simpleIndex i)) x y) (s : RootIndex) :
    pairing P.pair.T.group (F.character s) w.coroot = corootPairing τ i s := by
  rw [Frame.pairing_character]
  cases i
  · obtain ⟨ha, hb⟩ := Frame.firstCorootPairings F w
    rw [ha, hb]
    simp only [corootPairing, Bool.false_eq_true, if_false]
    ring
  · obtain ⟨ha, hb⟩ := Frame.secondCorootPairings F w
    rw [ha, hb]
    simp only [corootPairing, if_true]
    ring

private theorem Frame.reflection_character (F : Frame P τ) (i : Bool)
    {x y : A.group ⟶ P.pair.G.val}
    (w : CorootReflection P.pair.T (F.character (simpleIndex i)) x y) (s : RootIndex) :
    w.conjugation.inv ≫ F.character s = F.character (reflection τ i s) := by
  rw [w.reflection, Frame.corootPairing_eq F i w]
  cases i
  · rw [show simpleIndex false = a from rfl, ← Frame.character_shift_first]
    congr 1
    cases τ <;> ext <;> simp [corootPairing, reflection, firstStringLength] <;> ring
  · rw [show simpleIndex true = b from rfl, ← Frame.character_shift_second]
    congr 1
    cases τ <;> ext <;> simp [corootPairing, reflection, secondStringLength] <;> ring

end RootReflections

section RootCoordinateChoices

open private subgroupIso from LinearAlgebraicGroups.RootData.OrderedRootProducts
open Specs.AbstractPairing (Root)
open Specs.Pinning (RootCoordinate IsSimple)
open Specs.RootGroups (rootPoint CorootReflection)
open Specs.BorelsAndChambers (subgroupRoots)
open private rescale from LinearAlgebraicGroups.Classification.Pinning

private def negativeRoot (P : PinnedGroup A) (α : Root P.pair.T) : Root P.pair.T :=
  ⟨α.val⁻¹, (((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive P.pair.T
    P.pair.split P.pair.maximal).2 α.val α.property).2.1 α.val⁻¹).mpr (Or.inr rfl) |>.1⟩

private theorem negativeRoot_involutive (P : PinnedGroup A) : Function.Involutive (negativeRoot P) := by
  intro α
  exact Subtype.ext (inv_inv α.val)

private theorem IsIndex.neg {r : RootIndex} (h : IsIndex τ r) : IsIndex τ (-r) := by
  change _ ∨ _
  rw [neg_neg]
  exact h.symm

private theorem Frame.root_neg (F : Frame P τ) (r : Index τ) :
    F.root ⟨-r.val, IsIndex.neg r.property⟩ = negativeRoot P (F.root r) :=
  Subtype.ext (Frame.character_neg F r)

private theorem negative_not_pos (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u}) (α : Root P.pair.T) :
    negativeRoot P α ∈ subgroupRoots P.pair.T P.pair.B ↔ α ∉ subgroupRoots P.pair.T P.pair.B := by
  obtain ⟨r, rfl⟩ := (Frame.rootEquiv F).surjective α
  change negativeRoot P (F.root r) ∈ _ ↔ F.root r ∉ _
  rw [← Frame.root_neg, Frame.subgroupRoots_iff F borels, Frame.subgroupRoots_iff F borels]
  have no_opposites (s : RootIndex) (hs : s ∈ positiveList τ) : -s ∉ positiveList τ := by
    have h : ∀ s ∈ positiveList τ, -s ∉ positiveList τ := by cases τ <;> decide
    exact h s hs
  constructor
  · intro hn hp
    exact no_opposites r hp hn
  · intro hp
    exact r.property.resolve_left hp

private theorem coordinatesAt_exists (P : PinnedGroup A) (α : Root P.pair.T) :
    Nonempty (RootCoordinate A P.pair.T (P.roots α).val α.val) := by
  obtain ⟨U, _, _, _, ⟨B, e, he⟩, unique⟩ := ((RootData.RootGroups.rootSubgroups P.pair.G
    P.pair.reductive P.pair.T P.pair.split P.pair.maximal).2 α.val α.property).2.2
  let i := subgroupIso (unique _ (P.roots α).property)
  have h : (e ≪≫ i.val).hom ≫ (P.roots α).val.inclusion = e.hom ≫ U.inclusion := by
    simp only [Iso.trans_hom, Category.assoc, i.property]
  exact ⟨rescale (A := A) ⟨e ≪≫ i.val, h.symm ▸ he⟩ 1⟩

private def Coordinates.pinPositive (P : PinnedGroup A) (α : Root P.pair.T) :
    RootCoordinate A P.pair.T (P.roots α).val α.val := by
  classical
  exact if h : IsSimple P.pair α then P.pin ⟨α, h⟩ else (coordinatesAt_exists P α).some

private structure PositiveCoordinates (P : PinnedGroup A) where
  atRoot : ∀ α : Root P.pair.T, RootCoordinate A P.pair.T (P.roots α).val α.val
  pin : ∀ α : Specs.Pinning.SimpleRoot P.pair, atRoot α.val = P.pin α

private def initialPositiveCoordinates (P : PinnedGroup A) : PositiveCoordinates P :=
  ⟨Coordinates.pinPositive P, fun s => by simp [Coordinates.pinPositive, s.property]⟩

private def linkedNegative (α β : Root P.pair.T) (h : β.val = α.val⁻¹)
    (x : RootCoordinate A P.pair.T (P.roots α).val α.val) :
    RootCoordinate A P.pair.T (P.roots β).val β.val :=
  (linkedOppositeCoordinate P α β h x).choose

private def negativeCoordinate (Q : PositiveCoordinates P) (α β : Root P.pair.T)
    (h : β.val = α.val⁻¹) : RootCoordinate A P.pair.T (P.roots β).val β.val :=
  linkedNegative α β h (Q.atRoot α)

private def assembleCoordinates (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q : PositiveCoordinates P) : Coordinates (P := P) := by
  classical
  let x (α : Root P.pair.T) : RootCoordinate A P.pair.T (P.roots α).val α.val :=
    if α ∈ subgroupRoots P.pair.T P.pair.B then Q.atRoot α
    else negativeCoordinate Q (negativeRoot P α) α (inv_inv α.val).symm
  refine ⟨x, ?_, ?_⟩
  · intro α
    simpa only [x, if_pos α.property.1] using Q.pin α
  · intro α β ha hb
    have hnot : β ∉ subgroupRoots P.pair.T P.pair.B := by
      rw [show β = negativeRoot P α from Subtype.ext hb, negative_not_pos F borels]
      exact Classical.not_not.mpr ha
    simp only [x, if_pos ha, if_neg hnot]
    have hn : negativeRoot P β = α := Subtype.ext (by rw [show (negativeRoot P β).val = β.val⁻¹ from rfl,
      hb, inv_inv])
    have hlink (a₀ : Root P.pair.T) (e : a₀ = α) (h : β.val = a₀.val⁻¹) :
        Nonempty (CorootReflection P.pair.T α.val
          ((Q.atRoot α).val.hom ≫ (P.roots α).val.inclusion)
          ((negativeCoordinate Q a₀ β h).val.hom ≫ (P.roots β).val.inclusion)) := by
      subst a₀
      exact (linkedOppositeCoordinate P α β h (Q.atRoot α)).choose_spec
    exact hlink _ hn _

private theorem assemble_positive (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q : PositiveCoordinates P) (α : Root P.pair.T)
    (ha : α ∈ subgroupRoots P.pair.T P.pair.B) :
    (assembleCoordinates F borels Q).coordinate α = Q.atRoot α := by
  simp only [assembleCoordinates, if_pos ha]

private theorem assemble_negative (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q : PositiveCoordinates P) (α : Root P.pair.T)
    (ha : α ∉ subgroupRoots P.pair.T P.pair.B) :
    (assembleCoordinates F borels Q).coordinate α =
      negativeCoordinate Q (negativeRoot P α) α (inv_inv α.val).symm := by
  simp only [assembleCoordinates, if_neg ha]

private theorem assemble_positive_point (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q : PositiveCoordinates P) (r : Index τ) (hr : r.val ∈ positiveList τ)
    (R : TestAlgebra k) (x : R) :
    point F (assembleCoordinates F borels Q) R r x =
      rootPoint ((Q.atRoot (F.root r)).val.hom ≫ (P.roots (F.root r)).val.inclusion) R x := by
  rw [point_eq_rootPoint, rootMap,
    assemble_positive F borels Q _ ((Frame.subgroupRoots_iff F borels r).mpr hr)]

private theorem assembled_representative_eq (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q Q' : PositiveCoordinates P) (R : TestAlgebra k) (i : Bool) :
    representative F (assembleCoordinates F borels Q) R i =
      representative F (assembleCoordinates F borels Q') R i := by
  have simple (s : Specs.Pinning.SimpleRoot P.pair) (r : Index τ) (hr : F.root r = s.val) :
      (assembleCoordinates F borels Q).coordinate (F.root r) =
        (assembleCoordinates F borels Q').coordinate (F.root r) ∧
      (assembleCoordinates F borels Q).coordinate (F.root ⟨-r.val, IsIndex.neg r.property⟩) =
        (assembleCoordinates F borels Q').coordinate (F.root ⟨-r.val, IsIndex.neg r.property⟩) := by
    rw [Frame.root_neg, hr]
    have hneg : negativeRoot P s.val ∉ subgroupRoots P.pair.T P.pair.B :=
      fun h => (negative_not_pos F borels s.val).mp h s.property.1
    refine ⟨?_, ?_⟩
    · rw [assemble_positive F borels Q _ s.property.1, assemble_positive F borels Q' _ s.property.1,
        Q.pin, Q'.pin]
    · rw [assemble_negative F borels Q _ hneg, assemble_negative F borels Q' _ hneg]
      generalize_proofs h
      have he (α : Root P.pair.T) (p : α = s.val) (h : (negativeRoot P s.val).val = α.val⁻¹) :
          negativeCoordinate Q α (negativeRoot P s.val) h =
            negativeCoordinate Q' α (negativeRoot P s.val) h := by
        subst α
        unfold negativeCoordinate
        rw [Q.pin, Q'.pin]
      exact he _ (negativeRoot_involutive P s.val) _
  cases i
  · have h := simple F.first ⟨a, index_a τ⟩ (Frame.root_a F _)
    unfold representative
    change point F _ R a 1 * point F _ R (-a) (-1) * point F _ R a 1 =
      point F _ R a 1 * point F _ R (-a) (-1) * point F _ R a 1
    rw [point_eq_rootPoint F _ R ⟨a, index_a τ⟩, point_eq_rootPoint F _ R ⟨a, index_a τ⟩,
      point_eq_rootPoint F _ R ⟨-a, IsIndex.neg (index_a τ)⟩,
      point_eq_rootPoint F _ R ⟨-a, IsIndex.neg (index_a τ)⟩]
    simp only [rootMap, h.1, h.2]
  · have h := simple F.second ⟨b, index_b τ⟩ (Frame.root_b F _)
    unfold representative
    change point F _ R b 1 * point F _ R (-b) (-1) * point F _ R b 1 =
      point F _ R b 1 * point F _ R (-b) (-1) * point F _ R b 1
    rw [point_eq_rootPoint F _ R ⟨b, index_b τ⟩, point_eq_rootPoint F _ R ⟨b, index_b τ⟩,
      point_eq_rootPoint F _ R ⟨-b, IsIndex.neg (index_b τ)⟩,
      point_eq_rootPoint F _ R ⟨-b, IsIndex.neg (index_b τ)⟩]
    simp only [rootMap, h.1, h.2]

end RootCoordinateChoices

section RepresentativeActions

open private representative_eq_word
  from LinearAlgebraicGroups.Classification.RankOneRelations

private theorem simpleIndex_mem (τ : TypeOfRoots) (i : Bool) :
    IsIndex τ (simpleIndex i) := by
  cases i
  · exact index_a τ
  · exact index_b τ

private theorem Frame.simple_mem (F : Frame P τ) (i : Bool) :
    F.root ⟨simpleIndex i, simpleIndex_mem τ i⟩ ∈
      subgroupRoots P.pair.T P.pair.B := by
  cases i
  · change F.root ⟨a, index_a τ⟩ ∈ _
    rw [Frame.root_a]
    exact F.first.property.1
  · change F.root ⟨b, index_b τ⟩ ∈ _
    rw [Frame.root_b]
    exact F.second.property.1

private def chosenLink (F : Frame P τ) (X : Coordinates (P := P)) (r : Index τ)
    (hr : F.root r ∈ subgroupRoots P.pair.T P.pair.B) :
    CorootReflection P.pair.T (F.character r) (rootMap X (F.root r))
      (rootMap X (F.root ⟨-r.val, IsIndex.neg r.property⟩)) :=
  (X.linked (F.root r) _ hr (Frame.character_neg F r)).some

private def simpleLink (F : Frame P τ) (X : Coordinates (P := P)) (i : Bool) :=
  chosenLink F X ⟨simpleIndex i, simpleIndex_mem τ i⟩ (Frame.simple_mem F i)

private theorem representative_eq_link (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (i : Bool) :
    representative F X R i = toUnit _ ≫ (simpleLink F X i).representative := by
  rw [representative_eq_word]
  let r : Index τ := ⟨simpleIndex i, simpleIndex_mem τ i⟩
  let s : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  change point F X R r 1 * point F X R s (-1) * point F X R r 1 = _
  simp only [point_eq_rootPoint, rankOneWord, Units.val_one, inv_one]
  rfl

private abbrev includedTorusPoint {G : GroupScheme k} (T : ClosedSubgroup G)
    (R : TestAlgebra k) (t : GroupPoints T.group R) : GroupPoints G R :=
  t ≫ T.inclusion.hom.hom

private theorem linked_negative_scalar (F : Frame P τ) (X : Coordinates (P := P))
    (r : Index τ) :
    HasScalarAction P.pair.T (F.character r)⁻¹
      (rootMap X (F.root ⟨-r.val, IsIndex.neg r.property⟩)) := by
  let s : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  exact Eq.mp (congrArg (fun χ => HasScalarAction P.pair.T χ (rootMap X (F.root s)))
    (Frame.character_neg F r)) (X.coordinate (F.root s)).property

private theorem link_conjugates_torus {T : ClosedSubgroup P.pair.G.val}
    {α : Character T.group} {xp xn : A.group ⟶ P.pair.G.val} (L : CorootReflection T α xp xn)
    (R : TestAlgebra k) (t : GroupPoints T.group R) :
    let n : GroupPoints P.pair.G.val R := toUnit _ ≫ L.representative
    MulAut.conj n (t ≫ T.inclusion.hom.hom) =
      (t ≫ L.conjugation.hom.hom.hom ≫ T.inclusion.hom.hom) := by
  have h := congrArg (fun q => t ≫ q) L.conjugates
  have hunit : t ≫ (toUnit T.group.X ≫ L.representative) =
      toUnit _ ≫ L.representative := by rw [← Category.assoc, comp_toUnit]
  simp only [Grp.comp_hom_hom, MonObj.comp_mul, GrpObj.comp_inv, hunit] at h
  simpa only [MulAut.conj_apply, Category.assoc] using h.symm

private theorem representative_action_unit (F : Frame P τ) (X : Coordinates (P := P))
    (i : Bool) (r : Index τ) :
    ∃ s : kˣ, ∀ (R : TestAlgebra k) (x : R),
      MulAut.conj (representative F X R i) (point F X R r x) =
        point F X R (reflection τ i r) (algebraMap k R (s : k) * x) := by
  let r' : Index τ := ⟨reflection τ i r, reflection_mem τ i r r.property⟩
  let L := simpleLink F X i
  obtain ⟨y, hy⟩ := transportCoordinate P (F.root r) (F.root r') (X.coordinate (F.root r))
    L.representative L.conjugation L.conjugates (Frame.reflection_character F i L r)
  obtain ⟨s, hs, _⟩ := Classification.Pinning.coordinateChanges A P.pair.T (P.roots (F.root r')).val
    (F.root r').val (X.coordinate (F.root r')) y
  refine ⟨s, fun R x => ?_⟩
  rw [representative_eq_link, point_eq_rootPoint F X R r, point_eq_rootPoint F X R r', MulAut.conj_apply]
  exact (hy R x).trans (hs R x)

private theorem actsOn_own (F : Frame P τ) (X : Coordinates (P := P)) (i : Bool) :
    ActsOn F X i (simpleIndex i) (-simpleIndex i) (-1) := by
  intro R x
  let r : Index τ := ⟨simpleIndex i, simpleIndex_mem τ i⟩
  let r' : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  let L := simpleLink F X i
  have h := Classification.RankOneRelations.oppositeRootRelations P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal _ (F.root r).property _ _ L
    (X.coordinate (F.root r)).property
    (linked_negative_scalar F X r) R
  change representative F X R i * point F X R r x * (representative F X R i)⁻¹ =
    point F X R r' (((-1 : ℤ) : R) * x)
  rw [representative_eq_link, point_eq_rootPoint F X R r, point_eq_rootPoint F X R r']
  simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using h.2.2 x

private def squareSign (τ : TypeOfRoots) (i : Bool) (r : RootIndex) : ℤ :=
  if Even (corootPairing τ i r) then 1 else -1

private theorem square_action (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (i : Bool) (r : Index τ) (x : R) :
    MulAut.conj ((representative F X R i) ^ 2) (point F X R r x) =
      point F X R r ((squareSign τ i r : R) * x) := by
  let L := simpleLink F X i
  have opp := Classification.RankOneRelations.oppositeRootRelations P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal _ (F.root ⟨simpleIndex i, simpleIndex_mem τ i⟩).property
    _ _ L (X.coordinate _).property
    (linked_negative_scalar F X ⟨simpleIndex i, simpleIndex_mem τ i⟩) R
  have χ := (RootData.CharacterPairing.characterPairingComposition P.pair.T.group
    (F.character r) L.coroot).2 R (-1)
  rw [Frame.corootPairing_eq F i L] at χ
  rw [neg_one_zpow_eq_ite] at χ
  rw [representative_eq_link, opp.2.1, MulAut.conj_apply]
  have h := point_scalar F X R (cocharacterPoint L.coroot R (-1)) r x
  dsimp only at h
  rw [χ] at h
  rw [squareSign]
  split <;> rename_i he <;> simp only [he, if_true, if_false, Int.cast_one, Int.cast_neg] at h ⊢ <;> exact h

private theorem return_action (F : Frame P τ) (X : Coordinates (P := P))
    (i : Bool) (r : Index τ) (s : RootIndex) (ε : ℤ) (hε : ε * ε = 1)
    (h : ActsOn F X i r s ε) :
    ActsOn F X i s r (squareSign τ i r * ε) := by
  intro R x
  let n := representative F X R i
  change MulAut.conj n (point F X R s x) =
    point F X R r (((squareSign τ i r * ε : ℤ) : R) * x)
  have eq := h R ((ε : R) * x)
  change MulAut.conj n (point F X R r ((ε : R) * x)) =
    point F X R s ((ε : R) * ((ε : R) * x)) at eq
  rw [← mul_assoc, ← Int.cast_mul, hε, Int.cast_one, one_mul] at eq
  rw [← eq, conjugation_composition, ← pow_two, square_action, Int.cast_mul, mul_assoc]

end RepresentativeActions

section Normalization

open Specs.Pinning (IsSimple)

private theorem Frame.character_add (F : Frame P τ) (r s : RootIndex) :
    F.character (r + s) = F.character r * F.character s := by
  simp only [Specs.RankTwoRelations.Frame.character, Prod.fst_add, Prod.snd_add, zpow_add]
  simp only [mul_assoc, mul_left_comm, mul_comm]

private theorem Frame.not_simple (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u}) (s : Index τ)
    (hpos : s.val ∈ positiveList τ) (ha : s.val ≠ a) (hb : s.val ≠ b) :
    ¬ IsSimple P.pair (F.root s) := by
  have test : ∀ v ∈ positiveList τ, v ≠ a → v ≠ b →
      ∃ r ∈ positiveList τ, ∃ t ∈ positiveList τ, v = r + t := by
    cases τ <;> decide
  obtain ⟨r, hr, t, ht, he⟩ := test s hpos ha hb
  intro h
  let r₀ : Index τ := ⟨r, Or.inl hr⟩
  let t₀ : Index τ := ⟨t, Or.inl ht⟩
  apply h.2 (F.root r₀) ((Frame.subgroupRoots_iff F borels r₀).mpr hr)
    (F.root t₀) ((Frame.subgroupRoots_iff F borels t₀).mpr ht)
  change F.character s.val = F.character r * F.character t
  rw [he, Frame.character_add]

private theorem normalize_coordinate (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (Q : PositiveCoordinates P) (i : Bool) (r s : RootIndex)
    (hr : r ∈ positiveList τ) (hs : s ∈ positiveList τ) (hrs : reflection τ i r = s)
    (hne : r ≠ s) (ha : s ≠ a) (hb : s ≠ b) :
    ∃ Q' : PositiveCoordinates P,
      ActsOn F (assembleCoordinates F borels Q') i r s 1 ∧
      ∀ (j : Bool) (p q : RootIndex) (m : ℤ),
        p ∈ positiveList τ → q ∈ positiveList τ → p ≠ s → q ≠ s →
        ActsOn F (assembleCoordinates F borels Q) j p q m →
        ActsOn F (assembleCoordinates F borels Q') j p q m := by
  classical
  let r₀ : Index τ := ⟨r, Or.inl hr⟩
  let s₀ : Index τ := ⟨s, Or.inl hs⟩
  let X := assembleCoordinates F borels Q
  let L := simpleLink F X i
  obtain ⟨y, hy⟩ := transportCoordinate P (F.root r₀) (F.root s₀)
    (Q.atRoot (F.root r₀)) L.representative L.conjugation L.conjugates (by
      change L.conjugation.inv ≫ F.character r = F.character s
      rw [Frame.reflection_character F i L, hrs])
  let family := Function.update Q.atRoot (F.root s₀) y
  have avoid (g : Root P.pair.T) (hg : g ≠ F.root s₀) : family g = Q.atRoot g :=
    Function.update_of_ne hg _ _
  let Q' : PositiveCoordinates P := ⟨family, fun g => by
    rw [avoid, Q.pin]
    intro hg
    exact Frame.not_simple F borels s₀ hs ha hb (hg ▸ g.property)⟩
  have keep (z : RootIndex) (hz : z ∈ positiveList τ) (h : z ≠ s) (R : TestAlgebra k) (v : R) :
      point F (assembleCoordinates F borels Q') R z v =
        point F X R z v := by
    let z₀ : Index τ := ⟨z, Or.inl hz⟩
    rw [assemble_positive_point F borels Q' z₀ hz, assemble_positive_point F borels Q z₀ hz]
    have hn : F.root z₀ ≠ F.root s₀ := fun e => h (congrArg Subtype.val
      ((Frame.rootEquiv F).injective e))
    rw [show Q'.atRoot (F.root z₀) = Q.atRoot (F.root z₀) from avoid _ hn]
  refine ⟨Q', ?_, ?_⟩
  · intro R v
    change representative F (assembleCoordinates F borels Q') R i *
        point F (assembleCoordinates F borels Q') R r v *
        (representative F (assembleCoordinates F borels Q') R i)⁻¹ =
      point F (assembleCoordinates F borels Q') R s (((1 : ℤ) : R) * v)
    rw [assembled_representative_eq F borels Q' Q, keep _ hr hne,
      assemble_positive_point F borels Q r₀ hr, assemble_positive_point F borels Q' s₀ hs,
      Int.cast_one, one_mul, representative_eq_link]
    have hQ : Q'.atRoot (F.root s₀) = y := Function.update_self _ _ _
    rw [hQ]
    exact hy R v
  · intro j p q m hp hq hps hqs H R v
    change representative F (assembleCoordinates F borels Q') R j *
        point F (assembleCoordinates F borels Q') R p v *
        (representative F (assembleCoordinates F borels Q') R j)⁻¹ =
      point F (assembleCoordinates F borels Q') R q ((m : R) * v)
    rw [assembled_representative_eq F borels Q' Q, keep _ hp hps, keep _ hq hqs]
    exact H R v

private theorem exists_normalized (F : Frame P τ)
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u}) :
    ∃ X : Coordinates (P := P), WeylNormalization F X := by
  let Q := initialPositiveCoordinates P
  cases τ with
  | orthogonal => exact ⟨assembleCoordinates F borels Q, trivial⟩
  | a2 =>
    obtain ⟨Q', h, _⟩ := normalize_coordinate F borels Q false b c
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨assembleCoordinates F borels Q', h⟩
  | b2 =>
    obtain ⟨Q₁, h₁, _⟩ := normalize_coordinate F borels Q true a c
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨Q₂, h₂, keep⟩ := normalize_coordinate F borels Q₁ false b d
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨assembleCoordinates F borels Q₂, keep _ _ _ _ (by decide) (by decide)
      (by decide) (by decide) h₁, h₂⟩
  | g2 =>
    obtain ⟨Q₁, h₁, _⟩ := normalize_coordinate F borels Q true a c
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    obtain ⟨Q₂, h₂, keep₂⟩ := normalize_coordinate F borels Q₁ false c d
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h₁ := keep₂ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₁
    obtain ⟨Q₃, h₃, keep₃⟩ := normalize_coordinate F borels Q₂ false b e
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have h₁ := keep₃ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₁
    have h₂ := keep₃ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₂
    obtain ⟨Q₄, h₄, keep₄⟩ := normalize_coordinate F borels Q₃ true e f
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨assembleCoordinates F borels Q₄,
      keep₄ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₁,
      keep₄ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₂,
      keep₄ _ _ _ _ (by decide) (by decide) (by decide) (by decide) h₃, h₄⟩

end Normalization

section OppositeActions

open private rootPoint_contraction pointMap from LinearAlgebraicGroups.Classification.RankOneRelations
open private centralizes_onAlgebras centralizes_hasLimit
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private split_torus_sections_commute
  from LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection
open private opposite_point unitEquiv unitPointHom unitPointHom_apply
  from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups
open private hom_ext_on_affine_tests from LinearAlgebraicGroups.RootData.RootGroups

private theorem inverse_cocharacter {T : GroupScheme k} [IsCommMonObj T.X] (c : Cocharacter T) :
    oppositeCocharacter c = c⁻¹ := by
  apply Grp.hom_ext
  apply hom_ext_on_affine_tests
  intro R p
  let z := unitEquiv R p
  have hp : unitPoint R z = p := by
    rw [← unitPointHom_apply]
    exact (unitEquiv R).symm_apply_apply p
  rw [← hp]
  change cocharacterPoint (oppositeCocharacter c) R z =
    unitPoint R z ≫ (c⁻¹).hom.hom
  rw [opposite_point, Grp.Hom.hom_hom_inv, GrpObj.comp_inv]
  change unitPoint R z⁻¹ ≫ c.hom.hom = (unitPoint R z ≫ c.hom.hom)⁻¹
  rw [← unitPointHom_apply, ← unitPointHom_apply, map_inv, GrpObj.inv_comp]

private theorem reflection_neg (τ : TypeOfRoots) (i : Bool) (r : RootIndex) :
    reflection τ i (-r) = -(reflection τ i r) := by
  cases τ <;> cases i <;> apply Prod.ext <;> simp [reflection, mul_neg] <;> ring

private theorem actionSign_neg (τ : TypeOfRoots) (i : Bool) (r : Index τ) :
    actionSign τ i (-r.val) = actionSign τ i r := by
  have test : ∀ r ∈ signedList τ, actionSign τ i (-r) = actionSign τ i r := by
    cases τ <;> cases i <;> decide
  exact test r ((mem_signedList _).mpr r.property)

private theorem actionSign_square (τ : TypeOfRoots) (i : Bool) (r : Index τ) :
    actionSign τ i r * actionSign τ i r = 1 := by
  have test : ∀ r ∈ signedList τ, actionSign τ i r * actionSign τ i r = 1 := by
    cases τ <;> cases i <;> decide
  exact test r ((mem_signedList _).mpr r.property)

private theorem point_onTorus_hasLimit (P : PinnedGroup A) (c : Cocharacter P.pair.T.group)
    (R : TestAlgebra k) (t : GroupPoints P.pair.T.group R) :
    HasLimit (c ≫ P.pair.T.inclusion) (t ≫ P.pair.T.inclusion.hom.hom)
      (t ≫ P.pair.T.inclusion.hom.hom) := by
  apply centralizes_hasLimit
  apply (centralizes_onAlgebras _ _).mpr
  intro S g z
  have h := split_torus_sections_commute P.pair.split
    (mapPoints g t : GroupPoints P.pair.T.group S) (cocharacterPoint c S z)
  exact h.map (pointMap S P.pair.T.inclusion)

private theorem opposite_pairing {T : GroupScheme k} (hT : Specs.GeometricRadicals.IsSplitTorus T)
    (α : Character T) (c : Cocharacter T) : pairing T α⁻¹ (oppositeCocharacter c) = pairing T α c := by
  obtain ⟨comm, h⟩ := RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := comm
  obtain ⟨_, _, _, _, B, _, he⟩ := h
  rw [inverse_cocharacter, ← he, ← he]
  change B (-Additive.ofMul α) (-Additive.ofMul c) = B (Additive.ofMul α) (Additive.ofMul c)
  simp

private theorem gauss_uniqueness (F : Frame P τ) (X : Coordinates (P := P)) (r : Index τ)
    (hr : F.root r ∈ subgroupRoots P.pair.T P.pair.B) (R : TestAlgebra k)
    (t t' : GroupPoints P.pair.T.group R) (y y' x x' : R)
    (h : point F X R (-r.val) y * includedTorusPoint P.pair.T R t * point F X R r x =
      point F X R (-r.val) y' * includedTorusPoint P.pair.T R t' * point F X R r x') :
    y = y' := by
  let j := P.pair.T.inclusion
  let L := chosenLink F X r hr
  let c := L.coroot ≫ j
  let r' : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  have hx (v : R) : HasLimit c (point F X R r v) 1 := by
    rw [point_eq_rootPoint]
    exact rootPoint_contraction (X.coordinate (F.root r)).property L.coroot
      (by change 0 < pairing _ (F.character r) L.coroot; rw [L.root_pairing]; decide) R v
  have hy (v : R) : HasLimit (oppositeCocharacter c) (point F X R r' v) 1 := by
    rw [show oppositeCocharacter c = oppositeCocharacter L.coroot ≫ j by
      simp [c, oppositeCocharacter, Category.assoc], point_eq_rootPoint]
    apply rootPoint_contraction (X.coordinate (F.root r')).property
    change 0 < pairing P.pair.T.group (F.character (-r.val)) (oppositeCocharacter L.coroot)
    rw [Frame.character_neg, opposite_pairing P.pair.split, L.root_pairing]
    decide
  let left : GroupPoints P.pair.G.val R := includedTorusPoint P.pair.T R t * point F X R r x
  let right : GroupPoints P.pair.G.val R := includedTorusPoint P.pair.T R t' * point F X R r x'
  have he : (point F X R r' y')⁻¹ * point F X R r' y = right * left⁻¹ := by
    have h' : point F X R r' y * left = point F X R r' y' * right := by
      simpa only [left, right, mul_assoc] using h
    calc
      _ = (point F X R r' y')⁻¹ * (point F X R r' y * left) * left⁻¹ := by group
      _ = _ := by rw [h']; group
  have h1 : (point F X R r' y')⁻¹ * point F X R r' y = 1 := by
    apply oppositeLimit_intersection_onPoints P.pair.G.property.1 c
    · rw [he]
      exact ⟨_, ((point_onTorus_hasLimit P L.coroot R t').mul (hx x')).mul
        (((point_onTorus_hasLimit P L.coroot R t).mul (hx x)).inv)⟩
    · simpa only [inv_one, one_mul] using (hy y').inv.mul (hy y)
  exact point_injective F X R r' ((inv_mul_eq_one.mp h1).symm)

private theorem linked_gauss (F : Frame P τ) (X : Coordinates (P := P))
    (r : Index τ) (hr : F.root r ∈ subgroupRoots P.pair.T P.pair.B) (R : TestAlgebra k)
    (x y : R) (d : Rˣ) (hd : (d : R) = 1 + x * y) :
    point F X R r x * point F X R (-r.val) y =
      point F X R (-r.val) (y * (↑d⁻¹ : R)) *
        includedTorusPoint P.pair.T R (cocharacterPoint (chosenLink F X r hr).coroot R d) *
        point F X R r (x * (↑d⁻¹ : R)) := by
  let s : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  have hneg (z : R) : point F X R (-r.val) z = rootPoint (rootMap X (F.root s)) R z :=
    point_eq_rootPoint F X R s z
  simp only [point_eq_rootPoint F X R r, hneg]
  exact (Classification.RankOneRelations.oppositeRootRelations P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal _ (F.root r).property _ _ (chosenLink F X r hr)
    (X.coordinate (F.root r)).property
    (linked_negative_scalar F X r) R).1 x y d hd

private def principalUnit (x : k) : (DualNumber k)ˣ where
  val := 1 + algebraMap k (DualNumber k) x * DualNumber.eps
  inv := 1 - algebraMap k (DualNumber k) x * DualNumber.eps
  val_inv := by
    rw [show (1 + algebraMap k (DualNumber k) x * DualNumber.eps) *
         (1 - algebraMap k (DualNumber k) x * DualNumber.eps) =
       1 - (algebraMap k (DualNumber k) x) ^ 2 * DualNumber.eps ^ 2 by ring]
    simp
  inv_val := by
    rw [mul_comm]
    rw [show (1 + algebraMap k (DualNumber k) x * DualNumber.eps) *
         (1 - algebraMap k (DualNumber k) x * DualNumber.eps) =
       1 - (algebraMap k (DualNumber k) x) ^ 2 * DualNumber.eps ^ 2 by ring]
    simp

/-- Comparing the negative parameters in the two Gauss decompositions
over the dual numbers identifies the reciprocal scale. -/
private theorem actsOn_opposite_pair (F : Frame P τ) (X : Coordinates (P := P))
    (i : Bool) (r s : Index τ) (hr : F.root r ∈ subgroupRoots P.pair.T P.pair.B)
    (hs : F.root s ∈ subgroupRoots P.pair.T P.pair.B)
    (he : reflection τ i r = s.val) (m : ℤ) (hm : m * m = 1) (hp : ActsOn F X i r s m) :
    ActsOn F X i (-r.val) (-s.val) m := by
  let r' : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  obtain ⟨v, hv⟩ := representative_action_unit F X i r'
  have negacts (R : TestAlgebra k) (x : R) :
      MulAut.conj (representative F X R i) (point F X R (-r.val) x) =
        point F X R (-s.val) (algebraMap k R (v : k) * x) := by
    simpa only [r', reflection_neg, he] using hv R x
  let R := CommAlgCat.of k (DualNumber k)
  let eps : R := DualNumber.eps
  let u : R := algebraMap k R (m : k)
  let w : R := algebraMap k R (v : k)
  let D : Rˣ := principalUnit 1
  let E : Rˣ := principalUnit ((m : k) * (v : k))
  have hd : (D : R) = 1 + eps * 1 := by
    change 1 + algebraMap k R 1 * eps = _
    simp
  have he' : (E : R) = 1 + (u * eps) * w := by
    change 1 + algebraMap k R ((m : k) * (v : k)) * eps = _
    rw [map_mul]
    ring
  let n := representative F X R i
  have posacts (x : R) : MulAut.conj n (point F X R r x) = point F X R s (u * x) := by
    simpa only [u, map_intCast, MulAut.conj_apply, n] using hp R x
  let t := cocharacterPoint (chosenLink F X r hr).coroot R D
  let L := simpleLink F X i
  let tn : GroupPoints P.pair.T.group R := t ≫ L.conjugation.hom.hom.hom
  have htorus : MulAut.conj n (t ≫ P.pair.T.inclusion.hom.hom) =
      tn ≫ P.pair.T.inclusion.hom.hom := by
    dsimp only [n, tn]
    rw [representative_eq_link]
    exact link_conjugates_torus L R t
  have eq := congrArg (MulAut.conj n) (linked_gauss F X r hr R eps 1 D hd)
  change MulAut.conj n (point F X R r eps * point F X R (-r.val) 1) =
    MulAut.conj n (point F X R (-r.val) (1 * (↑D⁻¹ : R)) *
      includedTorusPoint P.pair.T R t * point F X R r (eps * (↑D⁻¹ : R))) at eq
  have negacts' (x : R) : MulAut.conj n (point F X R (-r.val) x) =
      point F X R (-s.val) (w * x) := negacts R x
  simp only [map_mul, one_mul, posacts, negacts', mul_one, htorus] at eq
  have eq' := linked_gauss F X s hs R (u * eps) w E he'
  have coeff := gauss_uniqueness F X s hs R tn _ _ _ _ _ (eq.symm.trans eq')
  change (algebraMap k (DualNumber k) (v : k)) *
      (1 - algebraMap k (DualNumber k) 1 * DualNumber.eps) =
      (algebraMap k (DualNumber k) (v : k)) *
        (1 - algebraMap k (DualNumber k) ((m : k) * (v : k)) * DualNumber.eps) at coeff
  have heq := congrArg (TrivSqZeroExt.snd : DualNumber k → k) coeff
  have hscalar (z : k) : algebraMap k (DualNumber k) z = TrivSqZeroExt.inl z := rfl
  have snd_mul (p q : DualNumber k) :
      (p * q).snd = p.fst * q.snd + p.snd * q.fst := rfl
  have snd_unit (z : k) : (1 - TrivSqZeroExt.inl z * (DualNumber.eps : DualNumber k)).snd = -z := by
    change 0 - (z * 1 + 0 * 0) = -z
    simp
  have hdiff : (v : k) * (-1) = (v : k) * (-((m : k) * (v : k))) := by
    simpa only [hscalar, snd_mul, snd_unit, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      zero_mul, add_zero] using heq
  have huv : (m : k) * (v : k) = 1 := by
    have h := mul_left_cancel₀ (Units.ne_zero v) hdiff
    linear_combination h
  have humm : (m : k) * (m : k) = 1 := by rw [← Int.cast_mul, hm, Int.cast_one]
  have hvm : (v : k) = (m : k) := by
    apply mul_left_cancel₀ (show (m : k) ≠ 0 by intro h; rw [h, zero_mul] at humm; exact zero_ne_one humm)
    rw [huv, humm]
  intro S x
  change _ = point F X S (-s.val) ((m : S) * x)
  simpa only [hvm, map_intCast, MulAut.conj_apply] using negacts S x

private def PositiveActions (F : Frame P τ) (X : Coordinates (P := P)) : Prop :=
  ∀ (i : Bool) (r : RootIndex), r ∈ positiveList τ →
    ActsOn F X i r (reflection τ i r) (actionSign τ i r)

private theorem simpleActions_of_positive (F : Frame P τ) (X : Coordinates (P := P))
    (borels : Specs.BorelsAndChambers.BorelsThroughT.{u})
    (h : PositiveActions F X) : SimpleActions F X := by
  intro i r
  rcases r.property with hpos | hneg
  · exact h i r hpos
  · let s : Index τ := ⟨-r.val, Or.inl hneg⟩
    let t : Index τ := ⟨reflection τ i s, reflection_mem τ i s s.property⟩
    have hsr : -s.val = r.val := neg_neg _
    have hs := h i s hneg
    have hrt : reflection τ i r = -t.val := by
      rw [← hsr, reflection_neg]
    have hsign : actionSign τ i r = actionSign τ i s := by
      rw [← hsr]
      exact actionSign_neg τ i s
    rw [hrt, hsign, ← hsr]
    by_cases he : s.val = simpleIndex i
    · have htest : reflection τ i (simpleIndex i) = -simpleIndex i ∧
          actionSign τ i (simpleIndex i) = -1 ∧ squareSign τ i (simpleIndex i) * (-1) = -1 := by
        cases τ <;> cases i <;> decide
      have hm : s = ⟨simpleIndex i, simpleIndex_mem τ i⟩ := Subtype.ext he
      change ActsOn F X i (-s.val) (-(reflection τ i s)) (actionSign τ i s)
      rw [hm, htest.1, htest.2.1, neg_neg, ← htest.2.2]
      exact return_action F X i ⟨simpleIndex i, simpleIndex_mem τ i⟩
        (-simpleIndex i) (-1) (by decide) (actsOn_own F X i)
    · have check : ∀ z ∈ positiveList τ, z ≠ simpleIndex i → reflection τ i z ∈ positiveList τ := by
        cases τ <;> cases i <;> decide
      exact actsOn_opposite_pair F X i s t ((Frame.subgroupRoots_iff F borels s).mpr hneg)
        ((Frame.subgroupRoots_iff F borels t).mpr (check s hneg he))
        rfl _ (actionSign_square τ i s) hs

end OppositeActions

section FixedRoots

open private rootPoint_comp from LinearAlgebraicGroups.RootData.RootGroups

private theorem independent_of_distinct (F : Frame P τ) (r s : Index τ)
    (hne : s.val ≠ r.val) (hopp : s.val ≠ -r.val) :
    ¬ Proportional (F.character r) (F.character s) := by
  intro h
  have hor := ((RootData.RootGroups.rootSubgroups P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal).2 (F.character r) (F.root r).property).2.1 (F.character s)
  rcases hor.mp ⟨(F.root s).property, h⟩ with h₁ | h₂
  · exact hne (F.independent h₁)
  · exact hopp (F.independent (h₂.trans (Frame.character_neg F r).symm))

private theorem point_commute_of_no_cone (F : Frame P τ) (X : Coordinates (P := P))
    (r s : Index τ) (hind : ¬ Proportional (F.character r) (F.character s))
    (h : ∀ (i j : ℕ), 0 < i → 0 < j → ¬ IsIndex τ (coneWeight r s i j))
    (R : TestAlgebra k) (x y : R) :
    Commute (point F X R r x) (point F X R s y) := by
  rw [point_eq_rootPoint F X R r, point_eq_rootPoint F X R s]
  have comm := Classification.RankOneRelations.independentRootCommutation P.pair.G P.pair.reductive
    P.pair.T P.pair.split P.pair.maximal _ (F.root r).property _ (F.root s).property hind
    (fun i j hi hj => by
      change F.character r ^ i * F.character s ^ j ∉ absoluteRoots P.pair.T
      rw [← Frame.character_sum_powers, ← show
        coneWeight r s i j = ((i : ℤ) * r.val.1 + (j : ℤ) * s.val.1,
          (i : ℤ) * r.val.2 + (j : ℤ) * s.val.2) from rfl, Frame.root_iff_index]
      exact h i j hi hj)
    (P.roots (F.root r)).val (P.roots (F.root s)).val
    (P.roots (F.root r)).property (P.roots (F.root s)).property R
    (rootPoint (X.coordinate (F.root r)).val.hom R x)
    (rootPoint (X.coordinate (F.root s)).val.hom R y)
  simpa only [rootMap, rootPoint_comp] using comm

private theorem point_commute_self (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (r : RootIndex) (x y : R) :
    Commute (point F X R r x) (point F X R r y) := by
  show point F X R r x * point F X R r y = point F X R r y * point F X R r x
  rw [← point_add, ← point_add, add_comm]

private theorem fixes_of_cones (F : Frame P τ) (X : Coordinates (P := P))
    (i : Bool) (s : Index τ)
    (hne : s.val ≠ simpleIndex i) (hopp : s.val ≠ -simpleIndex i)
    (hp : ∀ (u v : ℕ), 0 < u → 0 < v → ¬ IsIndex τ (coneWeight (simpleIndex i) s u v))
    (hn : ∀ (u v : ℕ), 0 < u → 0 < v → ¬ IsIndex τ (coneWeight (-simpleIndex i) s u v)) :
    ActsOn F X i s s 1 := by
  intro R x
  let r : Index τ := ⟨simpleIndex i, simpleIndex_mem τ i⟩
  let r' : Index τ := ⟨-r.val, IsIndex.neg r.property⟩
  have commp := point_commute_of_no_cone F X r s (independent_of_distinct F r s hne hopp) hp R 1 x
  have commn := point_commute_of_no_cone F X r' s (independent_of_distinct F r' s hopp (by
    simpa only [r', neg_neg] using hne)) hn R (-1) x
  change MulAut.conj (point F X R r 1 * point F X R r' (-1) * point F X R r 1)
      (point F X R s x) = point F X R s (((1 : ℤ) : R) * x)
  rw [Int.cast_one, one_mul]
  exact commute_conjugation ((commp.mul_left commn).mul_left commp)

private def fixedPairs : TypeOfRoots → List (Bool × RootIndex)
  | .orthogonal => [(false, b), (true, a)]
  | .a2 => []
  | .b2 => [(true, d)]
  | .g2 => [(false, f), (true, d)]

private theorem fixed_no_cone (τ : TypeOfRoots) (i : Bool) (r : RootIndex)
    (hr : (i, r) ∈ fixedPairs τ) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ¬ IsIndex τ (coneWeight (simpleIndex i) r u v) ∧
      ¬ IsIndex τ (coneWeight (-simpleIndex i) r u v) := by
  cases τ <;> cases i <;> simp [fixedPairs] at hr
  all_goals
    subst r
    constructor <;> intro h <;>
      simp [IsIndex, coneWeight, simpleIndex, positiveList, a, b, c, d, e, f,
        Prod.mk.injEq, mul_neg] at h <;> omega

private theorem actsOn_fixed (F : Frame P τ) (X : Coordinates (P := P))
    (i : Bool) (r : RootIndex) (h : (i, r) ∈ fixedPairs τ) : ActsOn F X i r r 1 := by
  have check : ∀ q ∈ fixedPairs τ, IsIndex τ q.2 ∧ q.2 ≠ simpleIndex q.1 ∧ q.2 ≠ -simpleIndex q.1 := by
    cases τ <;> decide
  obtain ⟨hr, hne, hopp⟩ := check (i, r) h
  exact fixes_of_cones F X i ⟨r, hr⟩ hne hopp
    (fun u v hu hv => (fixed_no_cone τ i r h u v hu hv).1)
    (fun u v hu hv => (fixed_no_cone τ i r h u v hu hv).2)

end FixedRoots

section RootCone

open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.GeometricRadicals (IsSplitTorus)
open private Bivariate substitute coeff_substitute fin_cases_one
  from LinearAlgebraicGroups.Classification.RankOneRelations

/-- Every nonzero coefficient in an equivariant bivariate root coordinate
which vanishes on the two axes lies in the strict positive root cone.
The torus equivariance is tested with a Laurent indeterminate, so this
argument applies even over a finite field. -/
theorem coefficient_in_root_cone {T : GroupScheme k} (hT : IsSplitTorus T)
    (α β target : Character T) (p : Bivariate k)
    (axis₀ : substitute (k := k) (Fin.cases (0 : k) (fun _ : Fin 1 => 1)) p = 0)
    (axis₁ : substitute (k := k) (Fin.cases (1 : k) (fun _ : Fin 1 => 0)) p = 0)
    (weight : ∀ c : Cocharacter T,
      substitute (Fin.cases (LaurentPolynomial.T (pairing T α c))
        (fun _ : Fin 1 => LaurentPolynomial.T (pairing T β c))) p =
      MvPolynomial.C (LaurentPolynomial.T (pairing T target c)) *
        substitute (fun _ : Fin 2 => (1 : LaurentPolynomial k)) p)
    (d : Fin 2 →₀ ℕ) (hd : p.coeff d ≠ 0) :
    0 < d 0 ∧ 0 < d 1 ∧ α ^ d 0 * β ^ d 1 = target := by
  have firstAxis : 0 < d 0 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k => q.coeff d) axis₀
    rw [coeff_substitute] at e
    apply hd
    simpa [show d 0 = 0 by omega, fin_cases_one] using e
  have secondAxis : 0 < d 1 := by
    by_contra! h
    have e := congrArg (fun q : Bivariate k => q.coeff d) axis₁
    rw [coeff_substitute] at e
    apply hd
    simpa [show d 1 = 0 by omega, fin_cases_one] using e
  refine ⟨firstAxis, secondAxis, ?_⟩
  obtain ⟨comm, h⟩ := RootData.CharacterPairing.perfectCharacterPairing T hT
  letI := comm
  obtain ⟨_, _, _, _, P, perfect, evaluate⟩ := h
  suffices (Additive.ofMul (α ^ d 0 * β ^ d 1) : Additive (Character T)) =
      Additive.ofMul target by exact congrArg Additive.toMul this
  apply perfect.bijective_left.injective
  ext c
  change P (d 0 • (Additive.ofMul α : Additive (Character T)) +
    d 1 • (Additive.ofMul β : Additive (Character T))) c = P (Additive.ofMul target) c
  simp only [map_add, LinearMap.add_apply, map_nsmul]
  change d 0 • P (Additive.ofMul α) (Additive.ofMul (Additive.toMul c)) +
    d 1 • P (Additive.ofMul β) (Additive.ofMul (Additive.toMul c)) =
      P (Additive.ofMul target) (Additive.ofMul (Additive.toMul c))
  rw [evaluate, evaluate, evaluate, nsmul_eq_mul, nsmul_eq_mul]
  let c₀ := Additive.toMul c
  have e := congrArg (fun q : Bivariate (LaurentPolynomial k) => q.coeff d) (weight c₀)
  simp only [coeff_substitute, MvPolynomial.coeff_C_mul, Fin.cases_zero, fin_cases_one,
    one_pow, mul_one, LaurentPolynomial.T_pow, ← LaurentPolynomial.T_add] at e
  rw [mul_comm (LaurentPolynomial.T _) (algebraMap k (LaurentPolynomial k) _)] at e
  have hn : algebraMap k (LaurentPolynomial k) (p.coeff d) ≠ 0 := by
    intro he
    apply hd
    exact (algebraMap k (LaurentPolynomial k)).injective (he.trans (map_zero _).symm)
  have hc := mul_left_cancel₀ hn e
  by_contra hne
  have hcoef := congrArg
    (fun q : LaurentPolynomial k => q.coeff (pairing T target c₀)) hc
  change (d 0 : ℤ) * pairing T α c₀ + (d 1 : ℤ) * pairing T β c₀ ≠
    pairing T target c₀ at hne
  simp [hne] at hcoef

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (positiveRoots)
open Specs.CharacterPairing (characterValue)
open Specs.OrderedRootProducts (Enumerates Parametrizes)
open LinearAlgebraicGroups.CocharacterDynamics
open private RootCoordinates RootCoordinates.mk RootCoordinates.action
  coordinatesType mapCoordinates zeroCoordinates
  evalCoordinates evalCoordinates_zero evalCoordinates_natural evalCoordinates_scalar
  evalCoordinates_injective evalCoordinates_range rootPoint_contraction
  rootCommutator rootCommutator_natural rootCommutator_conjugates
  bivariateEvaluation bivariateEvaluation_X_zero bivariateEvaluation_X_one
  rootPoint_zero substitute_X laurentParameter_zpow
  from LinearAlgebraicGroups.Classification.RankOneRelations

private def factorCoordinates (X : Coordinates (P := P)) : RootCoordinates P.roots :=
  RootCoordinates.mk (fun _ => A) (fun α => (X.coordinate α).val)
    (fun α => (X.coordinate α).property)

/-- A list of root coordinates whose nonzero coefficients have their
prescribed root weight and vanish on the axes. -/
private def CoordinatesInCone {T : ClosedSubgroup P.pair.G.val} (α β : Character T.group) :
    (l : List (Root T)) → coordinatesType (Bivariate k) l → Prop
  | [], _ => True
  | target :: l, q =>
    (∀ d : Fin 2 →₀ ℕ, q.1.coeff d ≠ 0 → 0 < d 0 ∧ 0 < d 1 ∧ α ^ d 0 * β ^ d 1 = target.val) ∧
      CoordinatesInCone α β l q.2

set_option maxHeartbeats 1800000 in
private theorem coordinates_in_cone {T : ClosedSubgroup P.pair.G.val}
    (hT : IsSplitTorus T.group) (α β : Character T.group)
    (l : List (Root T)) (q : coordinatesType (Bivariate k) l)
    (hz₀ : mapCoordinates (fun _ => substitute (Fin.cases (0 : k) (fun _ : Fin 1 => 1))) l q =
      zeroCoordinates (Bivariate k) l)
    (hz₁ : mapCoordinates (fun _ => substitute (Fin.cases (1 : k) (fun _ : Fin 1 => 0))) l q =
      zeroCoordinates (Bivariate k) l)
    (hw : ∀ c : Cocharacter T.group,
      mapCoordinates (fun _ => substitute (Fin.cases (LaurentPolynomial.T (pairing T.group α c))
        (fun _ : Fin 1 => LaurentPolynomial.T (pairing T.group β c)))) l q =
      mapCoordinates (fun target p => MvPolynomial.C (LaurentPolynomial.T (pairing T.group target.val c)) *
        substitute (fun _ : Fin 2 => (1 : LaurentPolynomial k)) p) l q) :
    CoordinatesInCone α β l q := by
  induction l with
  | nil => exact True.intro
  | cons target l ih =>
    constructor
    · exact coefficient_in_root_cone hT α β target.val q.1 (congrArg Prod.fst hz₀)
        (congrArg Prod.fst hz₁) (fun c => congrArg Prod.fst (hw c))
    · exact ih q.2 (congrArg Prod.snd hz₀) (congrArg Prod.snd hz₁)
        (fun c => congrArg Prod.snd (hw c))

/-- Ordered coordinate polynomials for the commutator in a chamber containing
both roots. The same polynomials work on every test algebra. -/
theorem commutatorCoordinatePolynomials
    (X : Coordinates (P := P)) (α β : Root P.pair.T)
    (c : Cocharacter P.pair.T.group) (hα : 0 < pairing P.pair.T.group α.val c)
    (hβ : 0 < pairing P.pair.T.group β.val c)
    (l : List (Root P.pair.T)) (hl : Enumerates l (positiveRoots P.pair.T c)) :
    ∃ q : coordinatesType (Bivariate k) l,
      CoordinatesInCone α.val β.val l q ∧
      ∀ (R : TestAlgebra k) (u v : R),
        rootCommutator (factorCoordinates X) α β R u v =
          evalCoordinates (factorCoordinates X) R l
            (mapCoordinates (fun _ => bivariateEvaluation u v) l q) := by
  let T := P.pair.T
  let C := factorCoordinates X
  have hc := (RootData.OrderedRootProducts.contractingProduct
    P.pair.G P.pair.reductive T P.pair.split P.pair.maximal).2.2 c
  obtain ⟨⟨D⟩, prod⟩ := hc
  have hprod := prod D P.roots l hl
  let R₀ := CommAlgCat.of k (Bivariate k)
  let u₀ : R₀ := MvPolynomial.X 0
  let v₀ : R₀ := MvPolynomial.X 1
  obtain ⟨p, hp⟩ := (D.contracting_points R₀ _).mp
    (rootPoint_contraction (RootCoordinates.action C α) c hα R₀ u₀)
  obtain ⟨p', hp'⟩ := (D.contracting_points R₀ _).mp
    (rootPoint_contraction (RootCoordinates.action C β) c hβ R₀ v₀)
  obtain ⟨q, hq⟩ := evalCoordinates_range C hprod R₀ (p * p' * p⁻¹ * p'⁻¹)
  have universal : evalCoordinates C R₀ l q = rootCommutator C α β R₀ u₀ v₀ := by
    simpa only [map_mul, map_inv, hp, hp', rootCommutator] using hq
  have specialize {R : TestAlgebra k} (f : R₀ ⟶ R) :
      evalCoordinates C R l (mapCoordinates (fun _ => f.hom) l q) =
        rootCommutator C α β R (f.hom u₀) (f.hom v₀) := by
    rw [← evalCoordinates_natural, universal, rootCommutator_natural]
  have axis (s : Fin 2 → k) (hs : s 0 = 0 ∨ s 1 = 0) :
      mapCoordinates (fun _ => substitute (k := k) s) l q = zeroCoordinates (Bivariate k) l := by
    apply evalCoordinates_injective C hprod R₀
    rw [evalCoordinates_zero]
    have e := specialize (CommAlgCat.ofHom (substitute (k := k) s))
    change evalCoordinates C R₀ l (mapCoordinates (fun _ => substitute s) l q) =
      rootCommutator C α β R₀ (substitute s u₀) (substitute s v₀) at e
    rw [e]
    simp only [u₀, v₀, substitute_X]
    rcases hs with h | h <;> simp [h, rootCommutator, rootPoint_zero]
  refine ⟨q, ?_, ?_⟩
  · apply coordinates_in_cone P.pair.split _ _ l q
      (axis _ (Or.inl rfl)) (axis _ (Or.inr rfl))
    intro cochar
    let S := LaurentPolynomial k
    let R := CommAlgCat.of k (Bivariate S)
    let param : Rˣ := Units.map (MvPolynomial.C : S →+* Bivariate S).toMonoidHom
      (laurentParameter (CommAlgCat.of k k))
    let t := cocharacterPoint cochar R param
    let scale : Fin 2 → S := Fin.cases (LaurentPolynomial.T (pairing T.group α.val cochar))
      (fun _ : Fin 1 => LaurentPolynomial.T (pairing T.group β.val cochar))
    let id₀ : R₀ ⟶ R := CommAlgCat.ofHom (substitute (fun _ => (1 : S)))
    let scaled : R₀ ⟶ R := CommAlgCat.ofHom (substitute scale)
    have χ (target : Root T) : characterValue target.val R t =
        MvPolynomial.C (LaurentPolynomial.T (pairing T.group target.val cochar)) := by
      rw [(RootData.CharacterPairing.characterPairingComposition T.group target.val cochar).2 R param]
      change (↑(Units.map (MvPolynomial.C : S →+* Bivariate S).toMonoidHom
        (laurentParameter (CommAlgCat.of k k)) ^ _) : Bivariate S) = _
      rw [← map_zpow, Units.coe_map, laurentParameter_zpow]
      rfl
    have h₀ : scaled.hom u₀ = characterValue α.val R t * id₀.hom u₀ := by
      change substitute scale (MvPolynomial.X 0) = _ * substitute (fun _ => (1 : S)) _
      rw [substitute_X, substitute_X, χ]
      simp only [scale, Fin.cases_zero, map_one, one_mul]
      rfl
    have h₁ : scaled.hom v₀ = characterValue β.val R t * id₀.hom v₀ := by
      change substitute scale (MvPolynomial.X 1) = _ * substitute (fun _ => (1 : S)) _
      rw [substitute_X, substitute_X, χ]
      simp only [scale, fin_cases_one, map_one, one_mul]
      rfl
    have hscale (ls : List (Root T)) (z : coordinatesType R₀ ls) :
        mapCoordinates (fun target a => characterValue target.val R t * a) ls
            (mapCoordinates (fun _ => id₀.hom) ls z) =
          mapCoordinates (fun target p => MvPolynomial.C
            (LaurentPolynomial.T (pairing T.group target.val cochar)) * id₀.hom p) ls z := by
      induction ls with
      | nil => rfl
      | cons target ls ih =>
        exact Prod.ext (by simpa only [mapCoordinates, χ]) (ih z.2)
    apply evalCoordinates_injective C hprod R
    change evalCoordinates C R l (mapCoordinates (fun _ => scaled.hom) l q) =
      evalCoordinates C R l
        (mapCoordinates (fun target p => MvPolynomial.C
          (LaurentPolynomial.T (pairing T.group target.val cochar)) * id₀.hom p) l q)
    rw [← hscale l q, ← evalCoordinates_scalar C R l t, specialize, specialize,
      h₀, h₁, rootCommutator_conjugates]
  · intro R u v
    let f : R₀ ⟶ R := CommAlgCat.ofHom (bivariateEvaluation u v)
    change rootCommutator C α β R u v = evalCoordinates C R l (mapCoordinates (fun _ => f.hom) l q)
    rw [specialize f, show f.hom u₀ = u from bivariateEvaluation_X_zero u v,
      show f.hom v₀ = v from bivariateEvaluation_X_one u v]

end RootCone

section OrderedCoordinates

open Specs.AbstractPairing (Root)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.BorelsAndChambers (positiveRoots subgroupRoots)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing)
open Specs.OrderedRootProducts (Enumerates Parametrizes)
open Specs.RootGroups (rootPoint)
open private coordinatesType mapCoordinates evalCoordinates evalCoordinates_injective rootCommutator
  Bivariate bivariateEvaluation bivariateEvaluation_X_zero bivariateEvaluation_X_one
  from LinearAlgebraicGroups.Classification.RankOneRelations

private def listCoordinates {I R : Type u} (v : I → R) :
    (l : List I) → coordinatesType R l
  | [] => PUnit.unit
  | r :: l => (v r, listCoordinates v l)

private theorem listCoordinates_eq_iff {I R : Type u} (l : List I) (v w : I → R) :
    listCoordinates v l = listCoordinates w l ↔ ∀ r ∈ l, v r = w r := by
  induction l with
  | nil => simp only [listCoordinates, List.not_mem_nil, false_implies, implies_true]
  | cons r l ih =>
    constructor
    · intro h y hy
      rcases List.mem_cons.mp hy with rfl | hyl
      · exact congrArg Prod.fst h
      · exact (ih.mp (congrArg Prod.snd h)) y hyl
    · intro h
      exact Prod.ext (h r (by simp)) (ih.mpr fun y hy => h y (List.mem_cons_of_mem _ hy))

private theorem exists_listCoordinates {I R : Type u} [Nonempty R]
    (l : List I) (h : l.Nodup) (v : coordinatesType R l) : ∃ w : I → R, listCoordinates w l = v := by
  classical
  induction l with
  | nil => exact ⟨fun _ => Classical.choice inferInstance, Subsingleton.elim _ _⟩
  | cons r l ih =>
    obtain ⟨q, hq⟩ := ih (List.nodup_cons.mp h).2 v.2
    let x : I → R := Function.update q r v.1
    refine ⟨x, ?_⟩
    change (x r, listCoordinates x l) = (v.1, v.2)
    refine Prod.ext (Function.update_self r v.1 q) ?_
    rw [← hq]
    apply (listCoordinates_eq_iff l x q).mpr
    intro s hs
    have hne : s ≠ r := fun e => (List.nodup_cons.mp h).1 (e ▸ hs)
    exact Function.update_of_ne hne _ _

private theorem mapped_listCoordinates {I R S : Type u} (f : I → R → S)
    (l : List I) (v : I → R) :
    mapCoordinates f l (listCoordinates v l) = listCoordinates (fun r => f r (v r)) l := by
  induction l with
  | nil => rfl
  | cons r l ih => exact Prod.ext rfl ih

private theorem weight_of_listCoordinates {T : ClosedSubgroup P.pair.G.val}
    {r s : Specs.CharacterDescent.Character T.group} (l : List (Root T))
    (v : Root T → Bivariate k) (h : CoordinatesInCone r s l (listCoordinates v l)) :
    ∀ t ∈ l, ∀ q : Fin 2 →₀ ℕ, (v t).coeff q ≠ 0 →
      0 < q 0 ∧ 0 < q 1 ∧ r ^ q 0 * s ^ q 1 = t.val := by
  induction l with
  | nil => simp
  | cons t l ih =>
    intro z hz q hq
    rcases List.mem_cons.mp hz with rfl | hzl
    · exact h.1 q hq
    · exact ih h.2 z hzl q hq

private def positiveIndices (τ : TypeOfRoots) : List (Index τ) :=
  (positiveList τ).attach.map fun r => ⟨r.1, Or.inl r.2⟩

private def positiveRootList (F : Frame P τ) : List (Root P.pair.T) :=
  (positiveIndices τ).map F.root

private theorem positiveIndices_map (τ : TypeOfRoots) :
    (positiveIndices τ).map Subtype.val = positiveList τ := by
  simp [positiveIndices, List.map_map, Function.comp_def, List.attach_map_subtype_val]

private theorem mem_positiveIndices {τ : TypeOfRoots} (r : Index τ) :
    r ∈ positiveIndices τ ↔ r.1 ∈ positiveList τ := by
  simp only [positiveIndices, List.mem_map, List.mem_attach, true_and, Subtype.mk.injEq]
  exact ⟨fun ⟨x, hx⟩ => hx ▸ x.2, fun hr => ⟨⟨r, hr⟩, rfl⟩⟩

private theorem positiveRootList_enumerates (F : Frame P τ) (t : Cocharacter P.pair.T.group)
    (ha : 0 < pairing P.pair.T.group F.first.val.val t)
    (hb : 0 < pairing P.pair.T.group F.second.val.val t) :
    Enumerates (positiveRootList F) (positiveRoots P.pair.T t) := by
  have hp : (positiveList τ).Nodup := by cases τ <;> decide
  have hi : (positiveIndices τ).Nodup := List.Nodup.of_map Subtype.val ((positiveIndices_map τ).symm ▸ hp)
  refine ⟨hi.map ((Frame.rootEquiv F)).injective, ?_⟩
  intro r
  obtain ⟨x, rfl⟩ := (Frame.rootEquiv F).surjective r
  change F.root x ∈ (positiveIndices τ).map F.root ↔ F.root x ∈ positiveRoots _ _
  have hpositive := Frame.positive_iff_of_positive_simple F t ha hb x
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h
    have hyx : y = x := (Frame.rootEquiv F).injective hxy
    exact hpositive.mpr ((mem_positiveIndices x).mp (hyx ▸ hy))
  · intro h
    exact List.mem_map.mpr ⟨x, (mem_positiveIndices x).mpr (hpositive.mp h), rfl⟩

private theorem evalCoordinates_orderedWord (F : Frame P τ) (X : Coordinates (P := P))
    (R : TestAlgebra k) (l : List (Index τ)) (v : RootIndex → R) :
    evalCoordinates (factorCoordinates X) R (l.map F.root)
      (listCoordinates (fun r => v ((Frame.rootEquiv F).symm r).val) (l.map F.root)) =
      orderedWord (point F X R) (l.map Subtype.val) v := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    change rootPoint (rootMap X (F.root r)) R (v ((Frame.rootEquiv F).symm (F.root r)).val) *
        evalCoordinates (factorCoordinates X) R (l.map F.root)
          (listCoordinates (fun t => v ((Frame.rootEquiv F).symm t).val) (l.map F.root)) =
      point F X R r (v r) * orderedWord (point F X R) (l.map Subtype.val) v
    rw [show (Frame.rootEquiv F).symm (F.root r) = r from (Frame.rootEquiv F).symm_apply_apply r,
      point_eq_rootPoint, ih]

private theorem orderedWord_separates (F : Frame P τ) (X : Coordinates (P := P))
    (t : Cocharacter P.pair.T.group)
    (ha : 0 < pairing P.pair.T.group F.first.val.val t)
    (hb : 0 < pairing P.pair.T.group F.second.val.val t) (R : TestAlgebra k) :
    SeparatesCoordinates (point F X R) τ := by
  have hc := (RootData.OrderedRootProducts.contractingProduct
    P.pair.G P.pair.reductive P.pair.T P.pair.split P.pair.maximal).2.2 t
  obtain ⟨⟨D⟩, mul⟩ := hc
  have hm := mul D P.roots (positiveRootList F) (positiveRootList_enumerates F t ha hb)
  intro v w hv r hr
  have heq : evalCoordinates (factorCoordinates X) R (positiveRootList F)
        (listCoordinates (fun t => v ((Frame.rootEquiv F).symm t).val) (positiveRootList F)) =
      evalCoordinates (factorCoordinates X) R (positiveRootList F)
        (listCoordinates (fun t => w ((Frame.rootEquiv F).symm t).val) (positiveRootList F)) := by
    unfold positiveRootList
    rw [evalCoordinates_orderedWord, evalCoordinates_orderedWord, positiveIndices_map, hv]
  have he := evalCoordinates_injective (factorCoordinates X) hm R heq
  have h := (listCoordinates_eq_iff _ _ _).mp he (F.root ⟨r, Or.inl hr⟩) (by
    change _ ∈ (positiveIndices τ).map F.root
    exact List.mem_map_of_mem (mem_positiveIndices ⟨r, Or.inl hr⟩ |>.mpr hr))
  simpa only [show (Frame.rootEquiv F).symm (F.root ⟨r, Or.inl hr⟩) = ⟨r, Or.inl hr⟩ from
    (Frame.rootEquiv F).symm_apply_apply _] using h

private def bidegree (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

private theorem bidegree_ext (q : Fin 2 →₀ ℕ) : q = bidegree (q 0) (q 1) := by
  ext r
  fin_cases r <;> simp [bidegree, Finsupp.single_apply]

private theorem bivar_eval_monomial (c : k) (i j : ℕ) (R : TestAlgebra k) (x y : R) :
    bivariateEvaluation x y (MvPolynomial.monomial (bidegree i j) c) =
      algebraMap k R c * x ^ i * y ^ j := by
  rw [bidegree, MvPolynomial.monomial_add_single, MvPolynomial.monomial_eq,
    Finsupp.prod_single_index (by simp)]
  simp only [map_mul, map_pow, bivariateEvaluation_X_zero, bivariateEvaluation_X_one]
  exact congrArg (fun z : R => z * x ^ i * y ^ j) ((bivariateEvaluation x y).commutes c)

private theorem correctionTable_root_injective (τ : TypeOfRoots) (r s : RootIndex)
    (hr : r ∈ positiveList τ) (hs : s ∈ positiveList τ) :
    ((correctionTable τ r s).map Correction.root).Nodup := by
  have test : ∀ r ∈ positiveList τ, ∀ s ∈ positiveList τ,
      ((correctionTable τ r s).map Correction.root).Nodup := by
    cases τ <;> decide
  exact test r hr s hs

private def expansionParameters (τ : TypeOfRoots) (r s : RootIndex) (coeff : RootIndex → k)
    (R : TestAlgebra k) (x y : R) (t : RootIndex) : R :=
  match (correctionTable τ r s).find? (fun q => q.root == t) with
  | none => 0
  | some q => algebraMap k R (coeff t) * x ^ q.leftDegree * y ^ q.rightDegree

private def HasPositiveExpansion (F : Frame P τ) (X : Coordinates (P := P)) : Prop :=
  ∀ r s : RootIndex, r ∈ positiveList τ → s ∈ positiveList τ →
    (positiveList τ).idxOf r < (positiveList τ).idxOf s →
    ∃ coeff : RootIndex → k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R r x) (point F X R s y) = point F X R s y *
        orderedWord (point F X R) (positiveList τ) (expansionParameters τ r s coeff R x y)

set_option maxHeartbeats 3200000 in
private theorem hasPositiveExpansion (F : Frame P τ) (X : Coordinates (P := P))
    (t : Cocharacter P.pair.T.group)
    (ha : 0 < pairing P.pair.T.group F.first.val.val t)
    (hb : 0 < pairing P.pair.T.group F.second.val.val t) : HasPositiveExpansion F X := by
  classical
  intro r s hr hs ho
  let r₀ : Index τ := ⟨r, Or.inl hr⟩
  let s₀ : Index τ := ⟨s, Or.inl hs⟩
  let l := positiveRootList F
  have henum := positiveRootList_enumerates F t ha hb
  obtain ⟨q, hq, hword⟩ := commutatorCoordinatePolynomials X (F.root s₀) (F.root r₀) t
     ((Frame.positive_iff_of_positive_simple F t ha hb s₀).mpr hs)
     ((Frame.positive_iff_of_positive_simple F t ha hb r₀).mpr hr) l henum
  obtain ⟨v, rfl⟩ := exists_listCoordinates l henum.1 q
  let coeff (u : RootIndex) : k := if hu : IsIndex τ u then
    bivariateEvaluation (k := k) (-1 : k) 1 (v (F.root ⟨u, hu⟩)) else 0
  refine ⟨coeff, ?_⟩
  intro R x y
  have hvalues (l₀ : Root P.pair.T) (hl₀ : l₀ ∈ l) :
      bivariateEvaluation (-y) x (v l₀) =
        expansionParameters τ r s coeff R x y ((Frame.rootEquiv F).symm l₀).val := by
    let u := (Frame.rootEquiv F).symm l₀
    have hu : F.root u = l₀ := (Frame.rootEquiv F).apply_symm_apply l₀
    have hcoeff (q : Fin 2 →₀ ℕ) (hq₀ : (v l₀).coeff q ≠ 0) :=
      weight_of_listCoordinates l v hq l₀ hl₀ q hq₀
    have hterm (q : Fin 2 →₀ ℕ) (h : (v l₀).coeff q ≠ 0) :
        ∃ w ∈ correctionTable τ r s, w.root = u.val ∧ w.leftDegree = q 1 ∧ w.rightDegree = q 0 := by
      obtain ⟨h₀, h₁, hw⟩ := hcoeff q h
      have hidx : coneWeight r s (q 1) (q 0) = u.val := by
        apply F.independent
        change F.character (coneWeight r s (q 1) (q 0)) = F.character u.val
        rw [coneWeight, Frame.character_sum_powers]
        exact (mul_comm _ _).trans (hw.trans (congrArg Subtype.val hu.symm))
      exact positiveConeTable τ r s u hr hs u.property ho
        (q 1) (q 0) h₁ h₀ hidx
    have unique := correctionTable_root_injective τ r s hr hs
    unfold expansionParameters
    change _ = match (correctionTable τ r s).find? (fun q => q.root == u.val) with
      | none => 0
      | some q => algebraMap k R (coeff u.val) * x ^ q.leftDegree * y ^ q.rightDegree
    split
    · rename_i heq
      suffices v l₀ = 0 by rw [this, map_zero]
      apply MvPolynomial.ext
      intro n
      rw [MvPolynomial.coeff_zero]
      by_contra hn
      obtain ⟨w, hw, hw₀, _, _⟩ := hterm n hn
      have hw₁ := List.find?_eq_none.mp heq w hw
      simp [hw₀] at hw₁
    · rename_i w hfind
      have hwmem := List.mem_of_find?_eq_some hfind
      have hwroot : w.root = u.val := by simpa only [beq_iff_eq] using List.find?_some hfind
      let n := bidegree w.rightDegree w.leftDegree
      have hsupp (m : Fin 2 →₀ ℕ) (hm : (v l₀).coeff m ≠ 0) : m = n := by
        obtain ⟨w', hw', he, hi, hj⟩ := hterm m hm
        have hww' : w' = w := List.inj_on_of_nodup_map unique hw' hwmem (he.trans hwroot.symm)
        rw [hww'] at hi hj
        rw [bidegree_ext m, ← hi, ← hj]
      have hv : v l₀ = MvPolynomial.monomial n ((v l₀).coeff n) :=
        MvPolynomial.eq_monomial_of_support_subset_singleton fun m hm =>
          hsupp m (MvPolynomial.mem_support_iff.mp hm)
      have hcf : coeff u.val = bivariateEvaluation (-1 : k) 1 (v l₀) := by
        dsimp only [coeff]
        rw [dif_pos u.property, hu]
      let b₀ := (v l₀).coeff n
      have hbase : bivariateEvaluation (-1 : k) 1 (v l₀) =
          b₀ * (-1 : k) ^ w.rightDegree := by
        rw [hv]
        change bivariateEvaluation (k := k) (-1 : k) 1
            (MvPolynomial.monomial (bidegree w.rightDegree w.leftDegree) b₀) = _
        have e := bivar_eval_monomial b₀ w.rightDegree w.leftDegree (CommAlgCat.of k k) (-1) 1
        change bivariateEvaluation (-1 : k) 1
            (MvPolynomial.monomial (bidegree w.rightDegree w.leftDegree) b₀) =
          b₀ * (-1 : k) ^ w.rightDegree * (1 : k) ^ w.leftDegree at e
        simpa only [one_pow, mul_one] using e
      rw [hcf, hbase, hv]
      change bivariateEvaluation (-y) x
          (MvPolynomial.monomial (bidegree w.rightDegree w.leftDegree) b₀) = _
      rw [bivar_eval_monomial, map_mul, map_pow, map_neg, map_one, ← neg_one_mul y, mul_pow]
      ring
  have hspecial := hword R (-y) x
  rw [mapped_listCoordinates] at hspecial
  have hel : listCoordinates (fun (_ : Root P.pair.T) => _) l =
      listCoordinates (fun t => expansionParameters τ r s coeff R x y ((Frame.rootEquiv F).symm t).val) l :=
    (listCoordinates_eq_iff _ _ _).mpr hvalues
  rw [hel] at hspecial
  unfold l positiveRootList at hspecial
  rw [evalCoordinates_orderedWord, positiveIndices_map] at hspecial
  unfold rootCommutator at hspecial
  change rootPoint (rootMap X (F.root s₀)) R (-y) * rootPoint (rootMap X (F.root r₀)) R x *
      (rootPoint (rootMap X (F.root s₀)) R (-y))⁻¹ * (rootPoint (rootMap X (F.root r₀)) R x)⁻¹ =
      _ at hspecial
  simp only [← point_eq_rootPoint F X R s₀, ← point_eq_rootPoint F X R r₀, point_neg, inv_inv] at hspecial
  change (point F X R s y)⁻¹ * point F X R r x * point F X R s y *
    (point F X R r x)⁻¹ = _ at hspecial
  rw [← hspecial, MulAut.conj_apply]
  group

end OrderedCoordinates

section AssembleRelations

private def RelationAt (F : Frame P τ) (X : Coordinates (P := P)) (r s : RootIndex) : Prop :=
  ∀ (R : TestAlgebra k) (x y : R),
    point F X R r x * point F X R s y * point F X R r (-x) =
      point F X R s y * positiveCorrection F X R r s x y

private theorem relation_from_conjugation (F : Frame P τ) (X : Coordinates (P := P))
    (r s : RootIndex) (h : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R r x) (point F X R s y) =
        point F X R s y * positiveCorrection F X R r s x y) :
    RelationAt F X r s := by
  intro R x y
  rw [point_neg]
  exact h R x y

private theorem commute_of_empty_table (F : Frame P τ) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) (r s : RootIndex)
    (hr : r ∈ positiveList τ) (hs : s ∈ positiveList τ)
    (hlt : (positiveList τ).idxOf r < (positiveList τ).idxOf s)
    (hempty : correctionTable τ r s = []) :
    ∀ (R : TestAlgebra k) (x y : R), Commute (point F X R r x) (point F X R s y) := by
  obtain ⟨xs, hx⟩ := expands r s hr hs hlt
  intro R x y
  have h := hx R x y
  simp only [expansionParameters, hempty, List.find?_nil, orderedWord, point_zero, List.map_const',
    List.prod_replicate, one_pow, mul_one, MulAut.conj_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h

private theorem relation_of_empty_table (F : Frame P τ) (X : Coordinates (P := P))
    (r s : RootIndex) (hempty : correctionTable τ r s = [])
    (comm : ∀ (R : TestAlgebra k) (x y : R), Commute (point F X R r x) (point F X R s y)) :
    RelationAt F X r s := by
  apply relation_from_conjugation
  intro R x y
  simp only [positiveCorrection, correctionFactors, hempty, List.map_nil, List.prod_nil, mul_one]
  exact commute_conjugation (comm R x y)

private def nontrivialPairs : TypeOfRoots → List (RootIndex × RootIndex)
  | .orthogonal => []
  | .a2 => [(a,b)]
  | .b2 => [(a,b), (a,c)]
  | .g2 => [(a,b), (a,c), (a,d), (b,e), (c,d)]

private theorem positive_from_nontrivial (F : Frame P τ) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X)
    (h : ∀ q ∈ nontrivialPairs τ, RelationAt F X q.1 q.2) : PositiveRelations F X := by
  have check : ∀ r ∈ positiveList τ, ∀ s ∈ positiveList τ,
      (positiveList τ).idxOf r < (positiveList τ).idxOf s →
      (r,s) ∈ nontrivialPairs τ ∨ correctionTable τ r s = [] := by
    cases τ <;> decide
  intro r s hr hs hlt
  rcases check r hr s hs hlt with hm | he
  · exact h (r,s) hm
  · exact relation_of_empty_table F X r s he (commute_of_empty_table F X expands r s hr hs hlt he)

private theorem prescribed_action (F : Frame P τ) (X : Coordinates (P := P))
    {i : Bool} {r s : RootIndex} {m : ℤ} (h : ActsOn F X i r s m)
    (hr : reflection τ i r = s) (hm : actionSign τ i r = m) :
    ActsOn F X i r (reflection τ i r) (actionSign τ i r) := by
  rw [hr, hm]
  exact h

private theorem cast_action (F : Frame P τ) (X : Coordinates (P := P))
    {i : Bool} {r s : RootIndex} {ε : ℤ} (h : ActsOn F X i r s ε)
    (R : TestAlgebra k) (x : R) :
    MulAut.conj (representative F X R i) (point F X R r x) = point F X R s ((ε : R) * x) :=
  h R x

private theorem acts_a (F : Frame P τ) (X : Coordinates (P := P)) :
    ActsOn F X false a (-a) (-1) := actsOn_own F X false

private theorem acts_b (F : Frame P τ) (X : Coordinates (P := P)) :
    ActsOn F X true b (-b) (-1) := actsOn_own F X true

private theorem a2_ab_expansion (F : Frame P .a2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ m : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
        point F X R b y * point F X R c (algebraMap k R m * x * y) := by
  obtain ⟨v, hv⟩ := expands a b (by decide) (by decide) (by decide)
  refine ⟨v c, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R b y *
    (point F X R a 0 * (point F X R b 0 * (point F X R c (algebraMap k R (v c) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) * 1))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem a2_ab_relation (F : Frame P .a2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
      point F X R b y * point F X R c (1 * x * y)) : RelationAt F X a b := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .a2 a b = [⟨c, 1, 1, 1⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem b2_ab_expansion (F : Frame P .b2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ m n : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
        point F X R b y * (point F X R c (algebraMap k R m * x * y) * point F X R d (algebraMap k R n * x ^ 2 * y)) := by
  obtain ⟨v, hv⟩ := expands a b (by decide) (by decide) (by decide)
  refine ⟨v c, v d, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R b y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c (algebraMap k R (v c) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R d (algebraMap k R (v d) * x ^ (2 : ℕ) * y ^ (1 : ℕ)) * 1)))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem b2_ab_relation (F : Frame P .b2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
      point F X R b y * (point F X R c ((-1) * x * y) * point F X R d (1 * x ^ 2 * y))) : RelationAt F X a b := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .b2 a b = [⟨c, 1, 1, -1⟩, ⟨d, 2, 1, 1⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem b2_ac_expansion (F : Frame P .b2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ t : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R c y) =
        point F X R c y * point F X R d (algebraMap k R t * x * y) := by
  obtain ⟨v, hv⟩ := expands a c (by decide) (by decide) (by decide)
  refine ⟨v d, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R c y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c 0 *
        (point F X R d (algebraMap k R (v d) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) * 1)))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem b2_ac_relation (F : Frame P .b2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R c y) =
      point F X R c y * point F X R d ((-2 : R) * x * y)) : RelationAt F X a c := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .b2 a c = [⟨d, 1, 1, -2⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem g2_ab_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ m n v w : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
        point F X R b y *
            (point F X R c (algebraMap k R m * x * y) *
            (point F X R d (algebraMap k R n * x ^ 2 * y) *
            (point F X R e (algebraMap k R v * x ^ 3 * y) *
            point F X R f (algebraMap k R w * x ^ 3 * y ^ 2)))) := by
  obtain ⟨v, hv⟩ := expands a b (by decide) (by decide) (by decide)
  refine ⟨v c, v d, v e, v f, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R b y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c (algebraMap k R (v c) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R d (algebraMap k R (v d) * x ^ (2 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R e (algebraMap k R (v e) * x ^ (3 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R f (algebraMap k R (v f) * x ^ (3 : ℕ) * y ^ (2 : ℕ)) * 1)))))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem g2_ab_relation (F : Frame P .g2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R b y) =
      point F X R b y *
          (point F X R c ((-1) * x * y) *
          (point F X R d (1 * x ^ 2 * y) *
          (point F X R e (1 * x ^ 3 * y) *
          point F X R f (1 * x ^ 3 * y ^ 2))))) : RelationAt F X a b := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .g2 a b = [⟨c, 1, 1, -1⟩, ⟨d, 2, 1, 1⟩, ⟨e, 3, 1, 1⟩, ⟨f, 3, 2, 1⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem g2_ac_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ t l g : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R c y) =
        point F X R c y *
            (point F X R d (algebraMap k R t * x * y) *
            (point F X R e (algebraMap k R l * x ^ 2 * y) *
            point F X R f (algebraMap k R g * x * y ^ 2))) := by
  obtain ⟨v, hv⟩ := expands a c (by decide) (by decide) (by decide)
  refine ⟨v d, v e, v f, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R c y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c 0 *
        (point F X R d (algebraMap k R (v d) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R e (algebraMap k R (v e) * x ^ (2 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R f (algebraMap k R (v f) * x ^ (1 : ℕ) * y ^ (2 : ℕ)) * 1)))))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem g2_ac_relation (F : Frame P .g2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R c y) =
      point F X R c y *
          (point F X R d ((-2 : R) * x * y) *
          (point F X R e ((-3 : R) * x ^ 2 * y) *
          point F X R f ((3 : R) * x * y ^ 2)))) : RelationAt F X a c := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .g2 a c = [⟨d, 1, 1, -2⟩, ⟨e, 2, 1, -3⟩, ⟨f, 1, 2, 3⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem g2_ad_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ h : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R d y) =
        point F X R d y * point F X R e (algebraMap k R h * x * y) := by
  obtain ⟨v, hv⟩ := expands a d (by decide) (by decide) (by decide)
  refine ⟨v e, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R d y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c 0 *
        (point F X R d 0 *
        (point F X R e (algebraMap k R (v e) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) *
        (point F X R f 0 * 1)))))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem g2_ad_relation (F : Frame P .g2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R a x) (point F X R d y) =
      point F X R d y * point F X R e ((3 : R) * x * y)) : RelationAt F X a d := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .g2 a d = [⟨e, 1, 1, 3⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem g2_be_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ j : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R b x) (point F X R e y) =
        point F X R e y * point F X R f (algebraMap k R j * x * y) := by
  obtain ⟨v, hv⟩ := expands b e (by decide) (by decide) (by decide)
  refine ⟨v f, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R e y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c 0 *
        (point F X R d 0 *
        (point F X R e 0 *
        (point F X R f (algebraMap k R (v f) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) * 1)))))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem g2_be_relation (F : Frame P .g2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R b x) (point F X R e y) =
      point F X R e y * point F X R f (1 * x * y)) : RelationAt F X b e := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .g2 b e = [⟨f, 1, 1, 1⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem g2_cd_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) :
    ∃ z : k, ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R c x) (point F X R d y) =
        point F X R d y * point F X R f (algebraMap k R z * x * y) := by
  obtain ⟨v, hv⟩ := expands c d (by decide) (by decide) (by decide)
  refine ⟨v f, fun R x y => ?_⟩
  have h := hv R x y
  change _ = point F X R d y *
    (point F X R a 0 *
        (point F X R b 0 *
        (point F X R c 0 *
        (point F X R d 0 *
        (point F X R e 0 *
        (point F X R f (algebraMap k R (v f) * x ^ (1 : ℕ) * y ^ (1 : ℕ)) * 1)))))) at h
  simpa only [point_zero, pow_one, mul_one, one_mul] using h

private theorem g2_cd_relation (F : Frame P .g2) (X : Coordinates (P := P))
    (H : ∀ (R : TestAlgebra k) (x y : R),
      MulAut.conj (point F X R c x) (point F X R d y) =
      point F X R d y * point F X R f ((3 : R) * x * y)) : RelationAt F X c d := by
  apply relation_from_conjugation
  intro R x y
  simpa only [positiveCorrection, correctionFactors,
    show correctionTable .g2 c d = [⟨f, 1, 1, 3⟩] from rfl,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Int.cast_neg, Int.cast_one,
    Int.cast_ofNat, pow_one, mul_one, one_mul] using H R x y

private theorem orthogonal_from_expansion (F : Frame P .orthogonal) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) : PositiveActions F X ∧ PositiveRelations F X := by
  constructor
  · intro i r hr
    simp only [positiveList, List.mem_cons, List.mem_nil_iff, or_false] at hr
    cases i <;> rcases hr with rfl | rfl
    · exact prescribed_action F X (acts_a F X) (by decide) (by decide)
    · exact prescribed_action F X (actsOn_fixed F X false b (by decide)) (by decide) (by decide)
    · exact prescribed_action F X (actsOn_fixed F X true a (by decide)) (by decide) (by decide)
    · exact prescribed_action F X (acts_b F X) (by decide) (by decide)
  · exact positive_from_nontrivial F X expands (by simp [nontrivialPairs])

set_option maxHeartbeats 6500000 in
private theorem a2_from_expansion (F : Frame P .a2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) (norm : WeylNormalization F X)
    (separates : ∀ R : TestAlgebra k, SeparatesCoordinates (point F X R) .a2) :
    PositiveActions F X ∧ PositiveRelations F X := by
  let K := CommAlgCat.of k k
  have scalar (v : k) : algebraMap k K v = v := rfl
  have ac := commute_of_empty_table F X expands a c (by decide) (by decide) (by decide) rfl
  have bc := commute_of_empty_table F X expands b c (by decide) (by decide) (by decide) rfl
  have abW : ActsOn F X false b c 1 := norm
  have acW := return_action F X false ⟨b, index_b .a2⟩ c 1 (by decide) abW
  rw [show squareSign .a2 false b * 1 = -1 by decide] at acW
  obtain ⟨s, hs⟩ := representative_action_unit F X true ⟨a, index_a .a2⟩
  obtain ⟨t, ht⟩ := representative_action_unit F X true ⟨c, by decide⟩
  have hac : reflection .a2 true a = c := by decide
  have hca : reflection .a2 true c = a := by decide
  obtain ⟨m, hm⟩ := a2_ab_expansion F X expands
  have sa := cast_action F X (acts_a F X) K 1
  have sb := cast_action F X (acts_b F X) K 1
  have h : m = 1 ∧ (s : k) = -1 := a2Coefficients (point F X K) (point_zero F X K) (point_neg F X K)
    (separates K) (representative F X K false) (representative F X K true)
    rfl rfl (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sa)
    (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sb)
    (ac K) (bc K) (1 : k) (-1 : k) (s : k) (t : k)
    (by simpa only [Int.cast_one] using cast_action F X abW K)
    (by simpa only [Int.cast_neg, Int.cast_one] using cast_action F X acW K)
    (by simpa only [scalar, hac] using hs K)
    (by simpa only [scalar, hca] using ht K)
    rfl m (by simpa only [scalar] using hm K)
  obtain ⟨hm', hs'⟩ := h
  have baW : ActsOn F X true a c (-1) := by
    intro R x
    simpa only [hac, hs', map_neg, map_one, Int.cast_neg, Int.cast_one, MulAut.conj_apply] using hs R x
  have bcW := return_action F X true ⟨a, index_a .a2⟩ c (-1) (by decide) baW
  rw [show squareSign .a2 true a * (-1) = 1 by decide] at bcW
  constructor
  · intro i r hr
    simp only [positiveList, List.mem_cons, List.mem_nil_iff, or_false] at hr
    cases i <;> rcases hr with rfl | rfl | rfl
    · exact prescribed_action F X (acts_a F X) (by decide) (by decide)
    · exact prescribed_action F X (abW) (by decide) (by decide)
    · exact prescribed_action F X (acW) (by decide) (by decide)
    · exact prescribed_action F X (baW) (by decide) (by decide)
    · exact prescribed_action F X (acts_b F X) (by decide) (by decide)
    · exact prescribed_action F X (bcW) (by decide) (by decide)
  · apply positive_from_nontrivial F X expands
    rintro q hq
    simp only [nontrivialPairs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    subst q
    apply a2_ab_relation
    intro R x y
    simpa only [hm', map_one] using hm R x y

set_option maxHeartbeats 6500000 in
private theorem b2_from_expansion (F : Frame P .b2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) (norm : WeylNormalization F X)
    (separates : ∀ R : TestAlgebra k, SeparatesCoordinates (point F X R) .b2) :
    PositiveActions F X ∧ PositiveRelations F X := by
  let K := CommAlgCat.of k k
  have scalar (v : k) : algebraMap k K v = v := rfl
  have ad := commute_of_empty_table F X expands a d (by decide) (by decide) (by decide) rfl
  have bd := commute_of_empty_table F X expands b d (by decide) (by decide) (by decide) rfl
  have bc := commute_of_empty_table F X expands b c (by decide) (by decide) (by decide) rfl
  have cd := commute_of_empty_table F X expands c d (by decide) (by decide) (by decide) rfl
  obtain ⟨baW, abW⟩ := norm
  have adW : ActsOn F X false d b 1 := return_action F X false ⟨b, index_b .b2⟩ d 1 (by decide) abW
  have bcW : ActsOn F X true c a (-1) := return_action F X true ⟨a, index_a .b2⟩ c 1 (by decide) baW
  have bdW := actsOn_fixed F X true d (by decide)
  obtain ⟨s, hs⟩ := representative_action_unit F X false ⟨c, by decide⟩
  have hcc : reflection .b2 false c = c := by decide
  obtain ⟨m, n, ab⟩ := b2_ab_expansion F X expands
  obtain ⟨t, ac⟩ := b2_ac_expansion F X expands
  have sa := cast_action F X (acts_a F X) K 1
  have sb := cast_action F X (acts_b F X) K 1
  obtain ⟨hm, hn, ht, hscale⟩ := b2Coefficients (point F X K) (point_zero F X K) (point_add F X K)
    (point_neg F X K) (separates K) (representative F X K false) (representative F X K true)
    rfl rfl (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sa)
    (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sb)
    (ad K) (bd K) (bc K) (cd K) (s : k)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X abW K)
    (by simpa only [scalar, hcc] using hs K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X adW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X baW K)
    (by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using cast_action F X bcW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X bdW K)
    m n t (by simpa only [scalar] using ab K) (by simpa only [scalar] using ac K)
  have acW : ActsOn F X false c c (-1) := by
    intro R x
    simpa only [hcc, hscale, map_neg, map_one, Int.cast_neg, Int.cast_one, MulAut.conj_apply] using hs R x
  constructor
  · intro i r hr
    simp only [positiveList, List.mem_cons, List.mem_nil_iff, or_false] at hr
    cases i <;> rcases hr with rfl | rfl | rfl | rfl
    · exact prescribed_action F X (acts_a F X) (by decide) (by decide)
    · exact prescribed_action F X (abW) (by decide) (by decide)
    · exact prescribed_action F X (acW) (by decide) (by decide)
    · exact prescribed_action F X (adW) (by decide) (by decide)
    · exact prescribed_action F X (baW) (by decide) (by decide)
    · exact prescribed_action F X (acts_b F X) (by decide) (by decide)
    · exact prescribed_action F X (bcW) (by decide) (by decide)
    · exact prescribed_action F X (bdW) (by decide) (by decide)
  · apply positive_from_nontrivial F X expands
    intro q hq
    simp only [nontrivialPairs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl
    · apply b2_ab_relation
      intro R x y
      simpa only [hm, hn, map_neg, map_one] using ab R x y
    · apply b2_ac_relation
      intro R x y
      simpa only [ht, map_neg, map_ofNat] using ac R x y

set_option maxHeartbeats 6500000 in
private theorem g2_from_expansion (F : Frame P .g2) (X : Coordinates (P := P))
    (expands : HasPositiveExpansion F X) (norm : WeylNormalization F X)
    (separates : ∀ R : TestAlgebra k, SeparatesCoordinates (point F X R) .g2) :
    PositiveActions F X ∧ PositiveRelations F X := by
  let K := CommAlgCat.of k k
  have scalar (v : k) : algebraMap k K v = v := rfl
  have ae := commute_of_empty_table F X expands a e (by decide) (by decide) (by decide) rfl
  have bc := commute_of_empty_table F X expands b c (by decide) (by decide) (by decide) rfl
  have bd := commute_of_empty_table F X expands b d (by decide) (by decide) (by decide) rfl
  have ce := commute_of_empty_table F X expands c e (by decide) (by decide) (by decide) rfl
  have de := commute_of_empty_table F X expands d e (by decide) (by decide) (by decide) rfl
  have central (r : RootIndex) (hr : r ∈ positiveList .g2) (x y : K) :
      Commute (point F X K f x) (point F X K r y) := by
    have test : ∀ v ∈ positiveList .g2, v = f ∨
        ((positiveList .g2).idxOf v < (positiveList .g2).idxOf f ∧ correctionTable .g2 v f = []) := by decide
    rcases test r hr with rfl | ⟨hl, he⟩
    · exact point_commute_self F X K f x y
    · exact (commute_of_empty_table F X expands r f hr (by decide) hl he K y x).symm
  obtain ⟨baW, acW, abW, beW⟩ := norm
  have adW : ActsOn F X false d c (-1) := return_action F X false ⟨c, by decide⟩ d 1 (by decide) acW
  have aeW : ActsOn F X false e b (-1) := return_action F X false ⟨b, index_b .g2⟩ e 1 (by decide) abW
  have bcW : ActsOn F X true c a (-1) := return_action F X true ⟨a, index_a .g2⟩ c 1 (by decide) baW
  have bfW : ActsOn F X true f e (-1) := return_action F X true ⟨e, by decide⟩ f 1 (by decide) beW
  have afW := actsOn_fixed F X false f (by decide)
  have bdW := actsOn_fixed F X true d (by decide)
  obtain ⟨m, n, v, w, ab⟩ := g2_ab_expansion F X expands
  obtain ⟨t, l, g, ac⟩ := g2_ac_expansion F X expands
  obtain ⟨h, ad⟩ := g2_ad_expansion F X expands
  obtain ⟨j, be⟩ := g2_be_expansion F X expands
  obtain ⟨z, cd⟩ := g2_cd_expansion F X expands
  have sa := cast_action F X (acts_a F X) K 1
  have sb := cast_action F X (acts_b F X) K 1
  obtain ⟨hm, hn, hv, hw, ht, hl, hg, hh, hj, hz⟩ := g2Coefficients (point F X K)
    (point_zero F X K) (point_add F X K) (point_neg F X K) (separates K)
    (representative F X K false) (representative F X K true)
    rfl rfl (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sa)
    (by simpa only [Int.cast_neg, Int.cast_one, mul_one] using sb)
    (ae K) (bc K) (bd K) (ce K) (de K) central
    (by simpa only [Int.cast_one, one_mul] using cast_action F X abW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X acW K)
    (by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using cast_action F X adW K)
    (by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using cast_action F X aeW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X afW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X baW K)
    (by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using cast_action F X bcW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X bdW K)
    (by simpa only [Int.cast_one, one_mul] using cast_action F X beW K)
    (by simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using cast_action F X bfW K)
    m n v w t l g h j z
    (by simpa only [scalar] using ab K) (by simpa only [scalar] using ac K)
    (by simpa only [scalar] using ad K) (by simpa only [scalar] using be K)
    (by simpa only [scalar] using cd K)
  constructor
  · intro i r hr
    simp only [positiveList, List.mem_cons, List.mem_nil_iff, or_false] at hr
    cases i <;> rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact prescribed_action F X (acts_a F X) (by decide) (by decide)
    · exact prescribed_action F X (abW) (by decide) (by decide)
    · exact prescribed_action F X (acW) (by decide) (by decide)
    · exact prescribed_action F X (adW) (by decide) (by decide)
    · exact prescribed_action F X (aeW) (by decide) (by decide)
    · exact prescribed_action F X (afW) (by decide) (by decide)
    · exact prescribed_action F X (baW) (by decide) (by decide)
    · exact prescribed_action F X (acts_b F X) (by decide) (by decide)
    · exact prescribed_action F X (bcW) (by decide) (by decide)
    · exact prescribed_action F X (bdW) (by decide) (by decide)
    · exact prescribed_action F X (beW) (by decide) (by decide)
    · exact prescribed_action F X (bfW) (by decide) (by decide)
  · apply positive_from_nontrivial F X expands
    intro q hq
    simp only [nontrivialPairs, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply g2_ab_relation
      intro R x y
      simpa only [hm, hn, hv, hw, map_neg, map_one] using ab R x y
    · apply g2_ac_relation
      intro R x y
      simpa only [ht, hl, hg, map_neg, map_ofNat] using ac R x y
    · apply g2_ad_relation
      intro R x y
      simpa only [hh, map_ofNat] using ad R x y
    · apply g2_be_relation
      intro R x y
      simpa only [hj, map_one] using be R x y
    · apply g2_cd_relation
      intro R x y
      simpa only [hz, map_ofNat] using cd R x y

end AssembleRelations

/-- The prescribed normalization forces the relations in any linked coordinates. -/
theorem normalizedRelations : DeterminedRelations.{u} := by
  intro k _ A P τ F X hX
  let borels : Specs.BorelsAndChambers.BorelsThroughT.{u} := RootData.BorelsAndChambers.borelsThroughT
  obtain ⟨t, _, _, _, ht⟩ := (borels P.pair.G P.pair.reductive P.pair.T P.pair.split
    P.pair.maximal).1 P.pair.B P.pair.borel P.pair.containsTorus
  have ha : 0 < pairing P.pair.T.group F.first.val.val t :=
    show F.first.val ∈ positiveRoots P.pair.T t from ht ▸ F.first.property.1
  have hb : 0 < pairing P.pair.T.group F.second.val.val t :=
    show F.second.val ∈ positiveRoots P.pair.T t from ht ▸ F.second.property.1
  have expands := hasPositiveExpansion F X t ha hb
  have separates := orderedWord_separates F X t ha hb
  have hpos : PositiveActions F X ∧ PositiveRelations F X := by
    cases τ
    · exact orthogonal_from_expansion F X expands
    · exact a2_from_expansion F X expands hX separates
    · exact b2_from_expansion F X expands hX separates
    · exact g2_from_expansion F X expands hX separates
  have hacts := simpleActions_of_positive F X borels hpos.1
  exact ⟨hacts, hpos.2, signedRelations_of_positive F X hacts hpos.2⟩

/-- The nonopposite commutations and the simple representative actions
in the rank-two coordinates transported from the pins. -/
theorem rankTwoRelations : Statement.{u} := by
  intro k _ A P τ F
  obtain ⟨X, hX⟩ := exists_normalized F RootData.BorelsAndChambers.borelsThroughT
  exact ⟨X, hX, normalizedRelations P τ F X hX⟩

/-- Roots in different orthogonal factors commute with either sign. -/
theorem orthogonalCommutation : OrthogonalCommutation.{u} :=
  orthogonalCommutation_of_independent Classification.RankOneRelations.independentRootCommutation

end
end LinearAlgebraicGroups.Classification.RankTwoRelations
