import Specs.LinearAlgebraicGroups.Classification.IntegralRootRelations
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Lie.OfAssociative
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RankTwoRootSystems
import Mathlib.RingTheory.Flat.Domain
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.RootSystem.Chain
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Polynomial.Derivative
import LinearAlgebraicGroups.RootData.OrderedRootProducts
import LinearAlgebraicGroups.Classification.Pinning
import LinearAlgebraicGroups.Classification.RationalRealization
import Batteries.Tactic.OpenPrivate
import LinearAlgebraicGroups.RootData.EuclideanComparison
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyBasis
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreTriangularConstruction
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.RingTheory.Spectrum.Prime.RingHom

open AlgebraicGeometry CategoryTheory Opposite
open scoped Matrix TensorProduct BigOperators

universe u v w

namespace LinearAlgebraicGroups.Classification.IntegralRootRelations

open Specs.IntegralRootRelations
open CocharacterDynamics (cocharacterPoint unitPoint unitCoordinates)
open Specs.Pinning (BasedRootDatum)
open Specs.OrderedRootProducts (Enumerates)
open Specs.RootGroups (rootPoint)
open Specs.RationalRealization (RationalField Realization diagonalTorus)
open Specs.RootGroups (AdditiveLine)
open Specs.AdjointRepresentation (GroupPoints)

noncomputable section

set_option linter.style.haveILetI false

theorem oppositeRootMatrix : OppositeRootMatrix.{u} := by
  intro R _ x y s hs
  have huv : (↑s⁻¹ : R) * (s : R) = 1 := Units.inv_mul s
  have h22 : (↑s⁻¹ : R) * (1 + x * y) = 1 := by rw [← hs, huv]
  apply Subtype.ext
  change (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; y, 1] =
    (!![1, 0; y * (↑s⁻¹ : R), 1] : Matrix (Fin 2) (Fin 2) R) *
      !![(s : R), 0; 0, (↑s⁻¹ : R)] * !![1, x * (↑s⁻¹ : R); 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, huv]
  · exact hs.symm
  · linear_combination -x * huv
  · linear_combination -h22

/-- Transport the matrix factorization along the action attached to a
normalized pair of root coordinates and its marked coroot. -/
theorem oppositeRootRelations_of_rankOneActions
    {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
    (Q : Realization D A) (z : RootCoordinates Q)
    (h : ∀ (i j : D.I), D.datum.root j = -D.datum.root i →
      ∀ R : TestAlgebra (RationalField.{u}),
        ∃ f : Matrix.SpecialLinearGroup (Fin 2) R →* GroupPoints Q.pinned.pair.G.val R,
          (∀ x, f (upper x) = root Q z i R x) ∧
          (∀ y, f (lower y) = root Q z j R y) ∧
          ∀ s, f (diagonal s) = torus Q (D.datum.coroot i) R s) :
    OppositeRootRelations Q z := by
  intro i j hij R x y s hs
  obtain ⟨f, hu, hl, hd⟩ := h i j hij R
  simpa only [map_mul, hu, hl, hd] using congrArg f (oppositeRootMatrix x y s hs)

/-- In the short-long G₂ string the sum of the two central brackets is twice
an integral multiple of the first one. This version works in any ℚ-Lie algebra. -/
theorem g₂_central_bracket {L : Type v} [LieRing L] [LieAlgebra ℚ L]
    (a v₀ v₁ v₂ v₃ : L) (h₁ : ⁅a, v₀⁆ = v₁) (h₃ : ⁅a, v₂⁆ = (3 : ℚ) • v₃)
    (h₀₂ : ⁅v₀, v₂⁆ = 0) :
    ⁅v₀, v₃⁆ + ⁅v₁, v₂⁆ = (2 : ℚ) • (-⁅v₀, v₃⁆) := by
  have h : ⁅v₁, v₂⁆ + (3 : ℚ) • ⁅v₀, v₃⁆ = 0 := by
    rw [← h₁, ← lie_smul, ← h₃, ← leibniz_lie, h₀₂, lie_zero]
  rw [eq_neg_of_add_eq_zero_left h]
  module

/-- Dividing an iterated Chevalley bracket by the factorial leaves
the signed binomial coefficient given by the backward root-string length. -/
theorem rootString_dividedBracket {L : Type v} [LieRing L] [LieAlgebra ℚ L]
    (a : L) (e : ℕ → L) (p q : ℕ)
    (h : ∀ j < q, ⁅a, e j⁆ = ((p + j + 1 : ℕ) : ℚ) • e (j + 1) ∨
                  ⁅a, e j⁆ = -(((p + j + 1 : ℕ) : ℚ) • e (j + 1)))
    (j : ℕ) (hj : j ≤ q) :
    let b := ((j.factorial : ℚ)⁻¹) • ((LieAlgebra.ad ℚ L a ^ j) (e 0))
    b = ((p + j).choose j : ℚ) • e j ∨ b = -(((p + j).choose j : ℚ) • e j) := by
  have hs (n : ℕ) (hn : n ≤ q) :
      (LieAlgebra.ad ℚ L a ^ n) (e 0) = ((p + 1).ascFactorial n : ℚ) • e n ∨
      (LieAlgebra.ad ℚ L a ^ n) (e 0) = -(((p + 1).ascFactorial n : ℚ) • e n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hfac : ((p + 1).ascFactorial (n + 1) : ℚ) =
          ((p + 1).ascFactorial n : ℚ) * ((p + n + 1 : ℕ) : ℚ) := by
        rw [Nat.ascFactorial_succ, Nat.cast_mul, Nat.add_right_comm, mul_comm]
      rw [pow_succ', Module.End.mul_apply]
      rcases ih (by omega) with ih | ih <;>
        rcases h n (by omega) with hx | hx <;>
        simp [ih, hx, lie_smul, hfac, smul_smul]
  have hfac : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have he : (j.factorial : ℚ)⁻¹ * ((p + 1).ascFactorial j : ℚ) = ((p + j).choose j : ℚ) := by
    rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
      inv_mul_cancel₀ hfac, one_mul]
  rcases hs j hj with hh | hh <;> simp [hh, smul_smul, he]

/-- The integer total-degree truncations reduce to the same coefficients
at every lower degree. -/
theorem integerTruncations {σ : Type v} [Finite σ] (f : MvPowerSeries σ ℤ) :
    ∀ (m n : ℕ) (d : σ →₀ ℕ), m ≤ n → d.degree ≤ m →
      (f.truncTotal (m + 1)).coeff d = (f.truncTotal (n + 1)).coeff d := by
  intro m n d hmn hdm
  rw [MvPowerSeries.coeff_truncTotal _ (by omega : d.degree < m + 1),
    MvPowerSeries.coeff_truncTotal _ (by omega : d.degree < n + 1)]

/-- The denominator of the rank-one identity is a unit on the formal
neighborhood of the origin, already over the integers. -/
theorem rankOneDenominator : RankOneDenominator.{u} := by
  intro σ x y hx
  have h : (1 + x * y).constantCoeff = 1 := by
    rw [map_add, map_one, map_mul, hx, zero_mul, add_zero]
  exact ⟨h, MvPowerSeries.isUnit_iff_constantCoeff.mpr (by rw [h]; exact isUnit_one)⟩

namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)

export Specs.IntegralRootRelations.RankTwo
  (Lattice step rootString backwardLength bracketPairs bracketMagnitude squaredLength)

theorem backwardLength_eq (R : Finset Lattice) (a b : Lattice) (p q : ℕ)
    (hp : p ≤ 3)
    (h : ∀ i : ℤ, step a b i ∈ R ↔ -(p : ℤ) ≤ i ∧ i ≤ q) :
    backwardLength R a b = p := by
  unfold backwardLength
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hi' := (h (-(i : ℤ))).mp (Finset.mem_filter.mp hi).2
    change i ≤ p
    omega
  · apply Finset.le_sup (f := id)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), (h (-(p : ℤ))).mpr (by omega)⟩

/-- For the shorter-first orientation, every bracket between string lines
is central among the lines, and each root's sum of bracket magnitudes is even. -/
def bracketChecks (kind : RankTwoKind) : Prop :=
  let R := rankTwoCoefficients kind
  ∀ a ∈ R, ∀ b ∈ R,
    a.1 * b.2 - a.2 * b.1 ≠ 0 →
    (kind = .A₁A₁ ∨ squaredLength kind a ≤ squaredLength kind b) →
    let pairs := bracketPairs R a b
    (∀ ij ∈ pairs, ∀ k ∈ rootString R a b,
      step (step (step a b ij.1) (step a b ij.2) 1) (step a b k) 1 ∉ R) ∧
    (∀ ij ∈ pairs, (∑ pq ∈ pairs.filter (fun pq => pq.1 + pq.2 = ij.1 + ij.2),
      bracketMagnitude R a b pq) % 2 = 0)

set_option maxRecDepth 25000 in
set_option maxHeartbeats 5000000 in
theorem centralBrackets_even (kind : RankTwoKind) : bracketChecks kind := by
  cases kind <;> unfold bracketChecks <;> decide

end RankTwo

section Jets

variable {σ : Type u} {K : Type v} [CommRing K]

/-- The total-degree truncation ideal. The quotient retains coefficients
strictly below degree n. -/
def degreeIdeal (n : ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | ∀ d : σ →₀ ℕ, d.degree < n → f.coeff d = 0}
  zero_mem' := by intro d _; simp
  add_mem' := by
    intro f g hf hg d hd
    rw [map_add, hf d hd, hg d hd, zero_add]
  smul_mem' := by
    classical
    intro f g hg d hd
    change (f * g).coeff d = 0
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have he := congrArg (fun x : σ →₀ ℕ => x.degree) (Finset.mem_antidiagonal.mp hij)
    rw [map_add] at he
    rw [hg ij.2 (by omega), mul_zero]

/-- Two power series have the same jet exactly when their retained
coefficients agree. -/
theorem jet_eq_iff (n : ℕ) (f g : MvPowerSeries σ K) :
    Ideal.Quotient.mk (degreeIdeal n) f = Ideal.Quotient.mk (degreeIdeal n) g ↔
      ∀ d : σ →₀ ℕ, d.degree < n → f.coeff d = g.coeff d := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change (∀ d : σ →₀ ℕ, d.degree < n → (f - g).coeff d = 0) ↔ _
  simp only [map_sub, sub_eq_zero]

/-- Computing a jet by polynomial truncation gives the same ring element. -/
theorem jet_eq_truncTotal [Finite σ] (n : ℕ) (f : MvPowerSeries σ K) :
    Ideal.Quotient.mk (degreeIdeal n) (f.truncTotal n).toMvPowerSeries =
      Ideal.Quotient.mk (degreeIdeal n) f := by
  apply (jet_eq_iff _ _ _).mpr
  intro d hd
  rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd]

/-- A compatible family of finite integer coefficient truncations
determines a unique formal series. -/
theorem series_of_integerTruncations [Finite σ] (p : ℕ → MvPolynomial σ ℤ)
    (hdeg : ∀ m (d : σ →₀ ℕ), m < d.degree → (p m).coeff d = 0)
    (h : ∀ m n (d : σ →₀ ℕ), m ≤ n → d.degree ≤ m → (p m).coeff d = (p n).coeff d) :
    ∃! f : MvPowerSeries σ ℤ, ∀ m, f.truncTotal (m + 1) = p m := by
  let f : MvPowerSeries σ ℤ := fun d => (p d.degree).coeff d
  refine ⟨f, ?_, ?_⟩
  · intro m
    ext d
    by_cases hd : d.degree ≤ m
    · rw [MvPowerSeries.coeff_truncTotal _ (by omega : d.degree < m + 1)]
      exact h d.degree m d hd le_rfl
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega : m + 1 ≤ d.degree),
        hdeg m d (by omega)]
  · intro g hg
    ext d
    have he := congrArg (fun f : MvPolynomial σ ℤ => f.coeff d) (hg d.degree)
    rw [MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_self _)] at he
    exact he

theorem degreeIdeal_antitone : Antitone (degreeIdeal (σ := σ) (K := K)) :=
  fun _ _ h _ hf d hd => hf d (hd.trans_le h)

theorem mul_mem_degreeIdeal {p q : ℕ} {x y : MvPowerSeries σ K}
    (hx : x ∈ degreeIdeal p) (hy : y ∈ degreeIdeal q) : x * y ∈ degreeIdeal (p + q) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he := congrArg (Finsupp.degree (R := ℕ)) (Finset.mem_antidiagonal.mp hij)
  rw [map_add] at he
  by_cases hi : ij.1.degree < p
  · rw [hx _ hi, zero_mul]
  · rw [hy _ (by omega), mul_zero]

theorem mem_degreeIdeal_one {x : MvPowerSeries σ K} :
    x ∈ degreeIdeal 1 ↔ x.constantCoeff = 0 := by
  constructor
  · intro h
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h 0 (by simp)
  · intro hx d hd
    have h : d = 0 := (Finsupp.degree_eq_zero_iff d).mp
      (Nat.eq_zero_of_le_zero (Nat.lt_succ_iff.mp hd))
    rw [h, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hx]

/-- Units which reduce to one modulo the specified parameter ideal. -/
def congruentUnits {S : Type*} [CommRing S] (I : Ideal S) : Subgroup Sˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).ker

theorem mem_congruentUnits {S : Type*} [CommRing S] {I : Ideal S} {s : Sˣ} :
    s ∈ congruentUnits I ↔ (s : S) - 1 ∈ I := by
  change Units.map (Ideal.Quotient.mk I).toMonoidHom s = 1 ↔ _
  rw [← Units.val_inj]
  change Ideal.Quotient.mk I (s : S) = 1 ↔ _
  rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.mk_eq_mk_iff_sub_mem]

theorem congruentUnits_mono {S : Type*} [CommRing S] :
    Monotone (congruentUnits (S := S)) :=
  fun _ _ h _ hs => mem_congruentUnits.mpr (h (mem_congruentUnits.mp hs))

theorem div_sub_mem_degreeIdeal {d e : ℕ} {x y : MvPowerSeries σ K}
    (hx : x ∈ degreeIdeal d) (hy : y ∈ degreeIdeal e)
    (s : (MvPowerSeries σ K)ˣ) (hs : (s : MvPowerSeries σ K) = 1 + x * y) :
    x * (↑s⁻¹ : MvPowerSeries σ K) - x ∈ degreeIdeal (d + (d + e)) ∧
      y * (↑s⁻¹ : MvPowerSeries σ K) - y ∈ degreeIdeal (e + (d + e)) := by
  have hdiff : (↑s⁻¹ : MvPowerSeries σ K) - 1 =
      -(↑s⁻¹ : MvPowerSeries σ K) * (x * y) := by
    have he : (↑s⁻¹ : MvPowerSeries σ K) * (1 + x * y) = 1 := by
      rw [← hs, Units.inv_mul]
    linear_combination he
  have h : (↑s⁻¹ : MvPowerSeries σ K) - 1 ∈ degreeIdeal (d + e) := by
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ (mul_mem_degreeIdeal hx hy)
  rw [← mul_sub_one, ← mul_sub_one]
  exact ⟨mul_mem_degreeIdeal hx h, mul_mem_degreeIdeal hy h⟩

variable {k : Type u} [Field k]

abbrev PowerSeriesAlgebra (k : Type u) [Field k] (σ : Type u) : TestAlgebra k :=
  CommAlgCat.of k (MvPowerSeries σ k)

abbrev JetAlgebra (k : Type u) [Field k] (σ : Type u) (m : ℕ) : TestAlgebra k :=
  CommAlgCat.of k (MvPowerSeries σ k ⧸ degreeIdeal (σ := σ) (K := k) (m + 1))

/-- Change of test algebra to the mth total-degree jet. -/
def toJet (k : Type u) [Field k] (σ : Type u) (m : ℕ) :
    PowerSeriesAlgebra k σ ⟶ JetAlgebra k σ m :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ k (degreeIdeal (σ := σ) (K := k) (m + 1)))

/-- Points of an affine scheme on a formal series algebra are determined
by their points on the total-degree quotient algebras. -/
theorem affinePoints_eq_of_jets {X : SchemeOver k} (hX : IsAffine X.left)
    {x y : Points X (PowerSeriesAlgebra k σ)}
    (h : ∀ m, mapPoints (toJet k σ m) x = mapPoints (toJet k σ m) y) : x = y := by
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := F.preimage (x ≫ e.inv)
  let b := F.preimage (y ≫ e.inv)
  have hm (m : ℕ) : a.unop ≫ toJet k σ m = b.unop ≫ toJet k σ m := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    change (testSpec k).map ((toJet k σ m).op ≫ a) =
      (testSpec k).map ((toJet k σ m).op ≫ b)
    rw [Functor.map_comp, Functor.map_comp]
    simp only [a, b, Functor.FullyFaithful.map_preimage, ← Category.assoc]
    exact congrArg (· ≫ e.inv) (h m)
  have hab : a.unop = b.unop := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro c
    apply MvPowerSeries.ext
    intro d
    have he := DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom (hm d.degree)) c
    change Ideal.Quotient.mk (degreeIdeal (d.degree + 1)) (a.unop.hom c) =
      Ideal.Quotient.mk (degreeIdeal (d.degree + 1)) (b.unop.hom c) at he
    exact (jet_eq_iff _ _ _).mp he d (Nat.lt_succ_self _)
  have hab' : a = b := Quiver.Hom.unop_inj hab
  have hp := congrArg ((testSpec k).map) hab'
  simp only [a, b, Functor.FullyFaithful.map_preimage] at hp
  exact (cancel_mono e.inv).mp hp

private theorem point_jet_reduction {X : SchemeOver k} {m n : ℕ} (hmn : m ≤ n)
    {x y : Points X (PowerSeriesAlgebra k σ)}
    (h : mapPoints (toJet k σ n) x = mapPoints (toJet k σ n) y) :
    mapPoints (toJet k σ m) x = mapPoints (toJet k σ m) y := by
  have hle : degreeIdeal (K := k) (σ := σ) (n + 1) ≤ degreeIdeal (m + 1) :=
    fun _ h d hd => h d (lt_of_lt_of_le hd (Nat.succ_le_succ hmn))
  let r : JetAlgebra k σ n ⟶ JetAlgebra k σ m :=
    CommAlgCat.ofHom (Ideal.Quotient.factorₐ k hle)
  have hr : toJet k σ n ≫ r = toJet k σ m := CommAlgCat.hom_ext rfl
  change (testSpec k).map (toJet k σ m).op ≫ x = (testSpec k).map (toJet k σ m).op ≫ y
  rw [← hr, op_comp, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg ((testSpec k).map r.op ≫ ·) h

/-- Integral approximations at every order give actual integer formal
coordinates when the rational chart distinguishes the retained coefficients. -/
theorem integerSeries_of_jetApproximation {ι : Type v} {X : SchemeOver k}
    (hX : IsAffine X.left) (g : Points X (PowerSeriesAlgebra k σ))
    (chart : (ι → {f : MvPowerSeries σ ℤ // f.constantCoeff = 0}) →
      Points X (PowerSeriesAlgebra k σ))
    (hChart : ∀ (m : ℕ) (p q : ι → {f : MvPowerSeries σ ℤ // f.constantCoeff = 0}),
      mapPoints (toJet k σ m) (chart p) = mapPoints (toJet k σ m) (chart q) ↔
        ∀ (i : ι) (d : σ →₀ ℕ), d.degree ≤ m → (p i).val.coeff d = (q i).val.coeff d)
    (hApprox : ∀ m, ∃ p, mapPoints (toJet k σ m) (chart p) = mapPoints (toJet k σ m) g) :
    ∃ p, chart p = g := by
  choose a ha using hApprox
  let f (i : ι) : MvPowerSeries σ ℤ := fun d => (a d.degree i).val.coeff d
  have hf (i : ι) : (f i).constantCoeff = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    change (a (Finsupp.degree (0 : σ →₀ ℕ)) i).val.coeff 0 = 0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (a _ i).property
  let p (i : ι) : {f : MvPowerSeries σ ℤ // f.constantCoeff = 0} := ⟨f i, hf i⟩
  refine ⟨p, affinePoints_eq_of_jets hX ?_⟩
  intro m
  rw [← ha m]
  apply (hChart m p (a m)).mpr
  intro i d hd
  change (a d.degree i).val.coeff d = (a m i).val.coeff d
  apply (hChart d.degree (a d.degree) (a m)).mp _ i d le_rfl
  rw [ha d.degree, point_jet_reduction hd (ha m)]

end Jets

section CellEvaluation

set_option backward.isDefEq.respectTransparency false

open Specs.DiagonalizableGroups (IntegerCharacters)

open Specs.RootGroups (rootPoint)

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
variable (Q : Realization D A) (z : RootCoordinates Q)
variable {R S : TestAlgebra (RationalField.{u})}

/-- Evaluating a root coordinate commutes with change of test algebra. -/
theorem map_root (f : R ⟶ S) (i : D.I) (x : R) :
    mapPoints f (root Q z i R x) = root Q z i S (f.hom x) := by
  unfold mapPoints root rootPoint
  rw [← Category.assoc, ← Functor.map_comp, ← op_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact (Polynomial.aeval_algHom f.hom x).symm

private theorem map_unitPoint {k : Type u} [Field k] {R S : TestAlgebra k}
    (f : R ⟶ S) (t : Rˣ) :
    mapPoints f (unitPoint R t) = unitPoint S (Units.map f.hom.toRingHom t) := by
  let p : CommAlgCat.of k (MonoidAlgebra k IntegerCharacters) ⟶ R :=
    CommAlgCat.ofHom (unitCoordinates R t)
  let q : CommAlgCat.of k (MonoidAlgebra k IntegerCharacters) ⟶ S :=
    CommAlgCat.ofHom (unitCoordinates S (Units.map f.hom.toRingHom t))
  have he : p ≫ f = q := by
    apply CommAlgCat.hom_ext
    change f.hom.comp (unitCoordinates R t) = unitCoordinates S (Units.map f.hom.toRingHom t)
    apply MonoidAlgebra.algHom_ext
    · intro m
      simp only [AlgHom.comp_apply, unitCoordinates, MonoidAlgebra.lift_single, one_smul,
        MonoidHom.comp_apply, zpowersHom, Units.coeHom_apply]
      exact congrArg (fun s : Sˣ => (s : S)) (map_zpow (Units.map f.hom.toRingHom) t _)
    · ext
  change (testSpec k).map f.op ≫ (testSpec k).map p.op = (testSpec k).map q.op
  rw [← Functor.map_comp, ← op_comp, he]

/-- Evaluating a marked cocharacter commutes with change of test algebra. -/
theorem map_torus (f : R ⟶ S) (v : D.Y) (t : Rˣ) :
    mapPoints f (torus Q v R t) = torus Q v S (Units.map f.hom.toRingHom t) := by
  let c : Specs.CharacterDescent.Cocharacter Q.pinned.pair.T.group :=
    Additive.toMul (Q.datumIso.val.coweightEquiv.symm v)
  let i := c.hom.hom ≫ Q.pinned.pair.T.inclusion.hom.hom
  change (testSpec _).map f.op ≫ (unitPoint R t ≫ c.hom.hom) ≫
    Q.pinned.pair.T.inclusion.hom.hom =
      (unitPoint S (Units.map f.hom.toRingHom t) ≫ c.hom.hom) ≫ Q.pinned.pair.T.inclusion.hom.hom
  simpa only [mapPoints, i, Category.assoc] using congrArg (· ≫ i) (map_unitPoint f t)

/-- The ordered cell product commutes with scalar evaluation, including
the multiplication of all of its separate torus coordinates. -/
theorem map_cellPoint {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y) (negative positive : List D.I)
    (f : R ⟶ S) (x : D.I → R) (t : Fin r → Rˣ) :
    mapPoints f (cellPoint Q z b negative positive R x t) =
      cellPoint Q z b negative positive S (fun i => f.hom (x i))
        (fun i => Units.map f.hom.toRingHom (t i)) := by
  let F := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map f).hom
  change F (cellPoint Q z b negative positive R x t) = _
  have hroot (i : D.I) : F (root Q z i R (x i)) = root Q z i S (f.hom (x i)) :=
    map_root Q z f i (x i)
  have htorus (i : Fin r) :
      F (torus Q (b i) R (t i)) = torus Q (b i) S (Units.map f.hom.toRingHom (t i)) :=
    map_torus Q f (b i) (t i)
  simp only [cellPoint, map_mul, map_list_prod, List.map_map, Function.comp_def, hroot, htorus]

set_option maxHeartbeats 1500000 in
private theorem jet_mapInt_eq_iff {σ : Type u} (m : ℕ) (p q : MvPowerSeries σ ℤ) :
    (toJet RationalField σ m).hom (MvPowerSeries.map (Int.castRingHom RationalField) p) =
      (toJet RationalField σ m).hom (MvPowerSeries.map (Int.castRingHom RationalField) q) ↔
        ∀ d : σ →₀ ℕ, d.degree ≤ m → p.coeff d = q.coeff d := by
  let I := degreeIdeal (K := RationalField.{u}) (σ := σ) (m + 1)
  let f := MvPowerSeries.map (σ := σ) (Int.castRingHom (RationalField.{u}))
  change Ideal.Quotient.mk I (f p) = Ideal.Quotient.mk I (f q) ↔ _
  dsimp only [I, f]
  rw [jet_eq_iff]
  simp only [MvPowerSeries.coeff_map, Int.coe_castRingHom, Nat.lt_succ_iff]
  constructor
  · intro h d hd
    have he := congrArg ULift.down (h d hd)
    change ((p.coeff d : ℤ) : ℚ) = ((q.coeff d : ℤ) : ℚ) at he
    exact_mod_cast he
  · intro h d hd
    rw [h d hd]

private theorem onePlusSeries_val {σ K : Type u} [CommRing K] (f : MvPowerSeries σ K)
    (hf : f.constantCoeff = 0) : (onePlusSeries f hf : MvPowerSeries σ K) = 1 + f :=
  IsUnit.unit_spec _

set_option maxHeartbeats 1500000 in
private theorem jet_integralCellPoint_iff {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I) (m : ℕ)
    (p q : D.I ⊕ Fin r → CenteredSeries (CellVariables D r))
    (hinj :
      let T := JetAlgebra RationalField (CellVariables D r) m
      Function.Injective (fun a : (D.I → T) × (Fin r → Tˣ) =>
        cellPoint Q z b negative positive T a.1 a.2)) :
    mapPoints (toJet RationalField (CellVariables D r) m) (integralCellPoint Q z b negative positive p) =
      mapPoints (toJet RationalField (CellVariables D r) m) (integralCellPoint Q z b negative positive q) ↔
        ∀ i (d : CellVariables D r →₀ ℕ), d.degree ≤ m → (p i).val.coeff d = (q i).val.coeff d := by
  let f := toJet RationalField (CellVariables D r) m
  let F := MvPowerSeries.map (σ := CellVariables D r) (Int.castRingHom (RationalField.{u}))
  let R₀ := CellAlgebra D r
  let T₀ := JetAlgebra RationalField (CellVariables D r) m
  let t (s : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)) (i : Fin r) : R₀ˣ :=
    onePlusSeries (F (s (.inr i)).val) (by simp [F, (s (.inr i)).property])
  let args (s : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)) :
      (D.I → T₀) × (Fin r → T₀ˣ) :=
    (fun i => f.hom (F (s (.inl i)).val), fun i => Units.map f.hom.toRingHom (t s i))
  have he (s : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)) :
      mapPoints f (integralCellPoint Q z b negative positive s) =
        cellPoint Q z b negative positive T₀ (args s).1 (args s).2 :=
    map_cellPoint Q z b negative positive f _ _
  change mapPoints f _ = mapPoints f _ ↔ _
  rw [he p, he q]
  have ht (i : Fin r) : (args p).2 i = (args q).2 i ↔
      f.hom (F (p (.inr i)).val) = f.hom (F (q (.inr i)).val) := by
    rw [← Units.val_inj]
    change f.hom (↑(t p i) : R₀) = f.hom (↑(t q i) : R₀) ↔ _
    simp only [t, onePlusSeries_val, map_add, map_one, add_right_inj]
  constructor
  · intro h i d hd
    have eq := hinj h
    cases i with
    | inl i => exact (jet_mapInt_eq_iff m _ _).mp (congrFun (congrArg Prod.fst eq) i) _ hd
    | inr i =>
      exact (jet_mapInt_eq_iff m _ _).mp ((ht i).mp (congrFun (congrArg Prod.snd eq) i)) _ hd
  · intro h
    have eq : args p = args q := Prod.ext
      (funext fun i => (jet_mapInt_eq_iff m _ _).mpr (h (.inl i)))
      (funext fun i => (ht i).mpr ((jet_mapInt_eq_iff m _ _).mpr (h (.inr i))))
    exact congrArg (fun a : (D.I → T₀) × (Fin r → T₀ˣ) =>
      cellPoint Q z b negative positive T₀ a.1 a.2) eq

set_option maxHeartbeats 1500000 in
/-- An injective marked cell and integral collection at each total degree
give the formal product in the original rational realization. -/
theorem formalBigCellProduct_of_jetCollection
    (hinj : ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ D.Y) (negative positive : List D.I),
      Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} →
      Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} →
      ∀ m : ℕ,
        let T := JetAlgebra RationalField (CellVariables D r) m
        Function.Injective (fun a : (D.I → T) × (Fin r → Tˣ) =>
          cellPoint Q z b negative positive T a.1 a.2))
    (hcollect : ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ D.Y) (negative positive : List D.I),
      Specs.OrderedRootProducts.Enumerates negative {i | ¬ D.base.IsPos i} →
      Specs.OrderedRootProducts.Enumerates positive {i | D.base.IsPos i} →
      ∀ m : ℕ, ∃ p : D.I ⊕ Fin r → CenteredSeries (CellVariables D r),
        let f := toJet RationalField (CellVariables D r) m
        mapPoints f (integralCellPoint Q z b negative positive p) =
          mapPoints f (genericCellPoint Q z b negative positive false *
            genericCellPoint Q z b negative positive true)) :
    FormalBigCellProduct Q z := by
  intro r b negative positive hneg hpos
  let g := genericCellPoint Q z b negative positive false * genericCellPoint Q z b negative positive true
  have hChart := fun m p q =>
    jet_integralCellPoint_iff Q z b negative positive m p q (hinj r b negative positive hneg hpos m)
  obtain ⟨p, hp⟩ := integerSeries_of_jetApproximation Q.pinned.pair.G.property.1 g
    (integralCellPoint Q z b negative positive) hChart (hcollect r b negative positive hneg hpos)
  let _ : Finite D.I := D.finiteRoots
  exact ⟨p, hp.symm, fun m i => (p i).val.truncTotal (m + 1),
    fun _ _ => rfl, fun m n i d => integerTruncations (p i).val m n d⟩

end CellEvaluation

section OrderedProducts

variable {ι : Type v} {G : Type w} [Group G]

private theorem list_prod_mul_of_cross_commute (l : List ι) (hl : l.Nodup) (f g : ι → G)
    (h : ∀ i ∈ l, ∀ j ∈ l, i ≠ j → Commute (g i) (f j)) :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    have hc : Commute (g a) (l.map f).prod :=
      Commute.list_prod_right _ _ (by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        exact h a (by simp) j (by simp [hj]) (fun he => ha (he ▸ hj)))
    simp only [List.map_cons, List.prod_cons,
      ih hl (fun i hi j hj hij => h i (by simp [hi]) j (by simp [hj]) hij)]
    calc
      (f a * g a) * ((l.map f).prod * (l.map g).prod) =
          f a * (g a * (l.map f).prod) * (l.map g).prod := by simp [mul_assoc]
      _ = _ := by rw [hc.eq]; simp [mul_assoc]

private theorem ordered_single [DecidableEq ι] (l : List ι) (hl : l.Nodup)
    (i : ι) (hi : i ∈ l) (a : G) :
    (l.map (fun j => if j = i then a else 1)).prod = a := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    obtain ⟨hj, hl⟩ := List.nodup_cons.mp hl
    by_cases hji : j = i
    · subst j
      simp [List.prod_eq_one (l := l.map (fun j => if j = i then a else 1)) (by
        intro x hx
        obtain ⟨j, hj', rfl⟩ := List.mem_map.mp hx
        simp [show j ≠ i by rintro rfl; exact hj hj'])]
    · simp [hji, ih hl (by simpa [Ne.symm hji] using hi)]

private theorem ordered_image_of_mem_iSup {G' : Type*} [Group G']
    (φ : G →* G') (l : List ι) (hl : l.Nodup) (hAll : ∀ i, i ∈ l)
    (P : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, Commute (φ x) (φ y))
    {x : G} (hx : x ∈ ⨆ i, P i) :
    ∃ f : ι → G, (∀ i, f i ∈ P i) ∧ φ x = (l.map fun i => φ (f i)).prod := by
  classical
  let S : Subgroup G' :=
    { carrier := {a | ∃ f : ι → G, (∀ i, f i ∈ P i) ∧
          a = (l.map fun i => φ (f i)).prod}
      one_mem' := ⟨fun _ => 1, fun _ => (P _).one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
        refine ⟨fun i => f i * g i, fun i => (P i).mul_mem (hf i) (hg i), ?_⟩
        simp_rw [map_mul]
        exact (list_prod_mul_of_cross_commute l hl _ _
          (fun i _ j _ hij => hc i j hij _ (hg i) _ (hf j))).symm
      inv_mem' := by
        rintro _ ⟨f, hf, rfl⟩
        refine ⟨fun i => (f i)⁻¹, fun i => (P i).inv_mem (hf i), ?_⟩
        apply inv_eq_of_mul_eq_one_right
        rw [← list_prod_mul_of_cross_commute l hl
          (fun i => φ (f i)) (fun i => φ ((f i)⁻¹))
          (fun i _ j _ hij => hc i j hij _ ((P i).inv_mem (hf i)) _ (hf j))]
        simp }
  have hle : (⨆ i, P i) ≤ S.comap φ := by
    apply iSup_le
    intro i a ha
    suffices φ a ∈ S from this
    refine ⟨fun j => if j = i then a else 1, fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst j; simpa
      · simp [hj]
    · simp_rw [apply_ite φ, map_one]
      exact (ordered_single l hl i (hAll i) (φ a)).symm
  exact hle hx

private theorem commute_in_quotient (N : Subgroup G) [N.Normal] {x y : G}
    (h : x * y * x⁻¹ * y⁻¹ ∈ N) :
    Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  have he := (QuotientGroup.eq_one_iff _).mpr h
  change QuotientGroup.mk' N (x * y * x⁻¹ * y⁻¹) = 1 at he
  simp only [map_mul, map_inv] at he
  let a := QuotientGroup.mk' N x
  let b := QuotientGroup.mk' N y
  change a * b * a⁻¹ * b⁻¹ = 1 at he
  change a * b = b * a
  calc
    a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = b * a := by rw [he, one_mul]

/-- In a group filtered by subgroups generated by the successively deeper
coordinate groups, collect a single ordered tuple to any specified depth.
Crossings involving a correction in degree d leave a correction in degree d+1. -/
theorem orderedProduct_mod_filtration (l : List ι) (hl : l.Nodup) (hAll : ∀ i, i ∈ l)
    (P : ℕ → ι → Subgroup G) (H : ℕ → Subgroup G)
    (hH : ∀ n, H n = ⨆ i, P n i) (hNormal : ∀ n, (H n).Normal)
    (hLower : ∀ n i, P (n + 1) i ≤ P 1 i)
    (hCross : ∀ n i j, i ≠ j →
      ∀ x ∈ P (n + 1) i, ∀ y ∈ P 1 j, x * y * x⁻¹ * y⁻¹ ∈ H (n + 2))
    {g : G} (hg : g ∈ H 1) (m : ℕ) :
    ∃ f : ι → G, (∀ i, f i ∈ P 1 i) ∧ (l.map f).prod⁻¹ * g ∈ H (m + 1) := by
  induction m with
  | zero => exact ⟨fun _ => 1, fun _ => (P _ _).one_mem, by simpa⟩
  | succ m ih =>
    obtain ⟨f, hf, he⟩ := ih
    let _ : (H (m + 2)).Normal := hNormal (m + 2)
    let φ := QuotientGroup.mk' (H (m + 2))
    rw [hH] at he
    have hc : ∀ i j, i ≠ j → ∀ x ∈ P (m + 1) i, ∀ y ∈ P 1 j, Commute (φ x) (φ y) :=
      fun i j hij x hx y hy => commute_in_quotient _ (hCross m i j hij x hx y hy)
    obtain ⟨a, ha, hea⟩ := ordered_image_of_mem_iSup φ l hl hAll (P (m + 1))
      (fun i j hij x hx y hy => hc i j hij x hx y (hLower m j hy)) he
    refine ⟨fun i => f i * a i, fun i => (P 1 i).mul_mem (hf i) (hLower m i (ha i)), ?_⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change φ (_⁻¹ * g) = 1
    have hprod : φ (l.map fun i => f i * a i).prod =
        φ (l.map f).prod * φ (l.map a).prod := by
      simp only [map_list_prod, List.map_map]
      exact list_prod_mul_of_cross_commute l hl _ _
        (fun i _ j _ hij => hc i j hij _ (ha i) _ (hf j))
    have hea' : φ ((l.map f).prod⁻¹ * g) = φ (l.map a).prod := by
      simpa only [map_list_prod, List.map_map, Function.comp_def] using hea
    rw [map_mul, map_inv, hprod, ← hea', map_mul, map_inv]
    group

/-- Collect a finite jet from the coordinate exchange identities. The exchange
hypothesis can be checked in a quotient where all deeper coordinates vanish. -/
theorem orderedProduct_of_truncated_coordinates (l : List ι) (hl : l.Nodup) (hAll : ∀ i, i ∈ l)
    (P : ℕ → ι → Subgroup G) (hLower : ∀ i, Antitone (fun n => P n i))
    (m : ℕ) (hEnd : ∀ i, P (m + 1) i = ⊥)
    (hExchange :
      let H : Subgroup G := ⨆ i, P 1 i
      ∀ n (N : Subgroup H) [N.Normal], (∀ i, (P (n + 2) i).subgroupOf H ≤ N) →
        ∀ (i j : ι) (x y : H), x.val ∈ P (n + 1) i → y.val ∈ P 1 j →
          Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y))
    {g : G} (hg : g ∈ ⨆ i, P 1 i) :
    ∃ f : ι → G, (∀ i, f i ∈ P 1 i) ∧ (l.map f).prod = g := by
  let H : Subgroup G := ⨆ i, P 1 i
  let S (n : ℕ) (i : ι) := (P n i).subgroupOf H
  let K (n : ℕ) := ⨆ i, S n i
  have hK1 : K 1 = ⊤ := by
    apply top_unique
    intro x _
    refine Subgroup.iSup_induction' (P 1)
      (C := fun y hy => (⟨y, hy⟩ : H) ∈ K 1) ?_ ?_ ?_ x.property
    · intro i y hy
      exact Subgroup.mem_iSup_of_mem i (show (⟨y, _⟩ : H) ∈ S 1 i from hy)
    · exact (K 1).one_mem
    · intro a b ha hb ha' hb'
      exact (K 1).mul_mem ha' hb'
  have hKmono : Antitone K := fun a b hab =>
    iSup_mono fun i => Subgroup.comap_mono (hLower i hab)
  have hKend : ∀ n, m + 1 ≤ n → K n = ⊥ := by
    intro n hn
    apply bot_unique
    calc
      K n ≤ K (m + 1) := hKmono hn
      _ = ⊥ := by simp only [K, S, hEnd, Subgroup.bot_subgroupOf, iSup_bot]
  have hstep (n : ℕ) (hN : (K (n + 2)).Normal) : (K (n + 1)).Normal := by
    letI := hN
    let φ := QuotientGroup.mk' (K (n + 2))
    have hc {x y : H} (hx : x ∈ K (n + 1)) : Commute (φ x) (φ y) := by
      refine Subgroup.iSup_induction (S (n + 1)) (C := fun a => Commute (φ a) (φ y))
        hx ?_ (by rw [map_one]; exact Commute.one_left _) ?_
      · intro i a ha
        have hy : y ∈ K 1 := by rw [hK1]; trivial
        refine Subgroup.iSup_induction (S 1) (C := fun b => Commute (φ a) (φ b))
          hy ?_ (by rw [map_one]; exact Commute.one_right _) ?_
        · intro j b hb
          exact hExchange n (K (n + 2)) (fun i => le_iSup (S (n + 2)) i) i j a b ha hb
        · intro b c hb hc
          simpa only [map_mul] using hb.mul_right hc
      · intro a b ha hb
        simpa only [map_mul] using ha.mul_left hb
    constructor
    intro x hx y
    have he : φ (y * x * y⁻¹ * x⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [(hc hx (y := y)).symm.eq]
      group
    have hmem := hKmono (Nat.le_succ (n + 1)) ((QuotientGroup.eq_one_iff _).mp he)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (K (n + 1)).mul_mem hmem hx
  have hNormal : ∀ n, (K n).Normal := by
    intro n
    cases n with
    | zero =>
      have hK0 : K 0 = ⊤ := top_unique (hK1 ▸ hKmono (Nat.zero_le 1))
      rw [hK0]
      infer_instance
    | succ n =>
      by_cases hn : n ≤ m
      · refine Nat.decreasingInduction' (P := fun n => (K (n + 1)).Normal)
          (fun t _ _ ht => hstep t ht) hn ?_
        rw [hKend _ le_rfl]
        infer_instance
      · rw [hKend _ (by omega)]
        infer_instance
  have hex (n : ℕ) (i j : ι) (_ : i ≠ j) (x : H) (hx : x ∈ S (n + 1) i)
      (y : H) (hy : y ∈ S 1 j) : x * y * x⁻¹ * y⁻¹ ∈ K (n + 2) := by
    letI := hNormal (n + 2)
    apply (QuotientGroup.eq_one_iff _).mp
    let φ := QuotientGroup.mk' (K (n + 2))
    change φ (_ * _ * _ * _) = 1
    have hc := hExchange n (K (n + 2)) (fun i => le_iSup (S (n + 2)) i) i j x y hx hy
    change Commute (φ x) (φ y) at hc
    simp only [map_mul, map_inv]
    rw [hc.eq]
    group
  have hg' : (⟨g, hg⟩ : H) ∈ K 1 := by rw [hK1]; trivial
  obtain ⟨f, hf, he⟩ := orderedProduct_mod_filtration l hl hAll S K (fun _ => rfl)
    hNormal (fun n i => Subgroup.comap_mono (hLower i (by omega))) hex hg' m
  rw [hKend _ le_rfl, Subgroup.mem_bot, inv_mul_eq_one] at he
  refine ⟨fun i => (f i).val, hf, ?_⟩
  simpa only [map_list_prod, List.map_map, Function.comp_def, Subgroup.coe_subtype]
    using congrArg H.subtype he

end OrderedProducts


/-- If the simple root vectors and their opposites are rational, the
nonzero bracket constants force all the root vectors to be rational. -/
theorem rootVectors_mem_range_of_simple
    (D : BasedRootDatum.{u})
    {L : Type v} [LieRing L] [LieAlgebra ℚ L]
    {M : Type w} [LieRing M] [LieAlgebra ℚ M]
    (f : L →ₗ⁅ℚ⁆ M) (e : D.I → M)
    (hsimple : ∀ i ∈ D.base.support,
      e i ∈ f.toLinearMap.range ∧ e (D.datum.reflectionPerm i i) ∈ f.toLinearMap.range)
    (hbracket : ∀ i j k : D.I, D.datum.root k = D.datum.root i + D.datum.root j →
      ∃ n : ℤ, n ≠ 0 ∧ ⁅e i, e j⁆ = n • e k) :
    ∀ i, e i ∈ f.toLinearMap.range := by
  let opp (i : D.I) := D.datum.reflectionPerm i i
  have hopp (i : D.I) : D.datum.root (opp i) = -D.datum.root i := by
    change D.datum.root (D.datum.reflectionPerm i i) = _
    rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self]
  have hopopp (i : D.I) : opp (opp i) = i := by
    apply D.datum.root.injective
    rw [hopp, hopp, neg_neg]
  have hs (i j k : D.I) (h : D.datum.root k = D.datum.root i + D.datum.root j)
      (hi : e i ∈ f.toLinearMap.range) (hj : e j ∈ f.toLinearMap.range) :
      e k ∈ f.toLinearMap.range := by
    rcases hi with ⟨x, hx⟩
    rcases hj with ⟨y, hy⟩
    obtain ⟨n, hn, hnbr⟩ := hbracket i j k h
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    change f x = e i at hx
    change f y = e j at hy
    refine ⟨(n : ℚ)⁻¹ • ⁅x, y⁆, ?_⟩
    change f ((n : ℚ)⁻¹ • ⁅x, y⁆) = _
    rw [map_smul, f.map_lie, hx, hy, hnbr, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
      inv_mul_cancel₀ hnq, one_smul]
  letI : Finite D.I := D.finiteRoots
  have hpos (i : D.I) (hi : D.base.IsPos i) :
      e i ∈ f.toLinearMap.range ∧ e (opp i) ∈ f.toLinearMap.range := by
    refine hi.induction_on_add hsimple ?_
    intro a b k h ha hb
    have hab : D.datum.root (opp k) = D.datum.root (opp a) + D.datum.root (opp b) := by
      rw [hopp, hopp, hopp, h, neg_add]
    exact ⟨hs a b k h ha.1 (hsimple b hb).1, hs _ _ _ hab ha.2 (hsimple b hb).2⟩
  intro i
  by_cases hi : D.base.IsPos i
  · exact (hpos i hi).1
  · have h := (hpos (opp i) ((RootPairing.Base.IsPos.neg_iff_not D.base i).mpr hi)).2
    rwa [hopopp] at h

/-- The exponential of a nilpotent commutator operator is conjugation by the
nilpotent exponential. Left and right multiplication commute as operators. -/
theorem nilpotent_exp_conjugation {A : Type v} [Ring A] [Algebra ℚ A]
    {a : A} (ha : IsNilpotent a) (b : A) :
    (IsNilpotent.exp (LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a)) b =
      IsNilpotent.exp a * b * IsNilpotent.exp (-a) := by
  let L := Algebra.lmul ℚ A
  let R : A →ₗ[ℚ] Module.End ℚ A := (LinearMap.mul ℚ A).flip
  have hl : IsNilpotent (LinearMap.mulLeft ℚ a) := ha.map L
  obtain ⟨n, hn⟩ := ha.neg
  have hr : R (-a) ^ n = 0 := by
    change LinearMap.mulRight ℚ (-a) ^ n = 0
    rw [LinearMap.pow_mulRight, hn]
    exact LinearMap.mulRight_zero_eq_zero ℚ A
  have he : IsNilpotent.exp (R (-a)) = R (IsNilpotent.exp (-a)) := by
    rw [IsNilpotent.exp_eq_sum hr, IsNilpotent.exp_eq_sum hn, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    exact LinearMap.pow_mulRight ℚ A (-a) i
  have hc : Commute (LinearMap.mulLeft ℚ a) (R (-a)) :=
    LinearMap.commute_mulLeft_right a (-a)
  have hf : LinearMap.mulLeft ℚ a - R a = LinearMap.mulLeft ℚ a + R (-a) := by
    ext t
    change a * t - t * a = a * t + t * -a
    rw [mul_neg, sub_eq_add_neg]
  change (IsNilpotent.exp (LinearMap.mulLeft ℚ a - R a)) b = _
  rw [hf, IsNilpotent.exp_add_of_commute hc hl ⟨n, hr⟩, he]
  have hl' : IsNilpotent.exp (LinearMap.mulLeft ℚ a) = LinearMap.mulLeft ℚ (IsNilpotent.exp a) :=
    (IsNilpotent.map_exp ha L).symm
  rw [hl']
  exact (mul_assoc _ _ _).symm

/-- When the bracket of two nilpotent elements is central in their
subalgebra, the group commutator of their exponentials is its exponential. -/
theorem nilpotent_exp_commutator_of_central {A : Type v} [Ring A] [Algebra ℚ A]
    (a b : A) (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hc : IsNilpotent (a * b - b * a)) (hca : Commute a (a * b - b * a))
    (hcb : Commute (a * b - b * a) b) :
    IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) * IsNilpotent.exp (-b) =
      IsNilpotent.exp (a * b - b * a) := by
  let T := LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a
  have hT : IsNilpotent T := by
    have hL := ha.map (Algebra.lmul ℚ A)
    obtain ⟨n, hn⟩ := ha
    refine (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hL ⟨n, ?_⟩
    rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]
  have hT2 : (T ^ 2) • b = 0 := by
    rw [pow_two]
    change a * (a * b - b * a) - (a * b - b * a) * a = 0
    exact sub_eq_zero.mpr hca.eq
  have hconj := nilpotent_exp_conjugation ha b
  change (IsNilpotent.exp T) • b = _ at hconj
  rw [IsNilpotent.exp_smul_eq_sum hT2 hT] at hconj
  have hconj' : IsNilpotent.exp a * b * IsNilpotent.exp (-a) = b + (a * b - b * a) := by
    change _ = b + T • b
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero, pow_one, one_smul] using hconj.symm
  let x := IsNilpotent.exp a
  let y := IsNilpotent.exp (-a)
  have hxy : x * y = 1 := ha.exp_mul_exp_neg_self
  have hyx : y * x = 1 := ha.exp_neg_mul_exp_self
  let F : A →+* A :=
    { toFun := fun z => x * z * y
      map_zero' := by simp
      map_one' := by rw [mul_one, hxy]
      map_add' := fun r s => by rw [mul_add, add_mul]
      map_mul' := fun r s => by
        calc
          x * (r * s) * y = x * r * (y * x) * s * y := by rw [hyx, mul_one, mul_assoc x r s]
          _ = _ := by noncomm_ring }
  have h := IsNilpotent.map_exp hb F
  change x * IsNilpotent.exp b * y =
    IsNilpotent.exp (x * b * y) at h
  change x * b * y = _ at hconj'
  rw [hconj', add_comm b, IsNilpotent.exp_add_of_commute hcb hc hb] at h
  change (x * IsNilpotent.exp b * y) * IsNilpotent.exp (-b) = _
  rw [h, mul_assoc, hb.exp_mul_exp_neg_self, mul_one]

section CentralExponential

open Polynomial

variable {A : Type v} [Ring A] [Algebra ℚ A]

private theorem derivative_pow_of_commute {p : Polynomial A} (hc : Commute p p.derivative) (n : ℕ) :
    (p ^ (n + 1)).derivative = (n + 1) • (p.derivative * p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ (n := n+1), derivative_mul, ih, smul_mul_assoc, mul_assoc, ← pow_succ,
      (hc.pow_left (n + 1)).eq, ← succ_nsmul]

private theorem derivative_exp_of_commute {p : Polynomial A} (hp : IsNilpotent p)
    (hc : Commute p p.derivative) :
    (IsNilpotent.exp p).derivative = p.derivative * IsNilpotent.exp p := by
  obtain ⟨N, hN⟩ := hp
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ N) hN),
    map_sum, Finset.sum_range_succ', Finset.mul_sum, Finset.sum_range_succ]
  have hscal (c : ℚ) (q : Polynomial A) : (c • q).derivative = c • q.derivative :=
    ((Polynomial.derivative : Polynomial A →ₗ[A] Polynomial A).restrictScalars ℚ).map_smul c q
  rw [hN, smul_zero, mul_zero, add_zero]
  simp only [hscal, pow_zero, derivative_one, smul_zero, zero_add, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  rw [derivative_pow_of_commute hc, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have h : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ h, mul_one]

private theorem polynomial_nilpotent_mul_X_pow (a : A) (ha : IsNilpotent a) (n : ℕ) :
    IsNilpotent (C a * (X : Polynomial A) ^ n) := by
  obtain ⟨N, hN⟩ := ha
  refine ⟨N, ?_⟩
  have h : Commute (C a : Polynomial A) ((X : Polynomial A) ^ n) :=
    (commute_X (C a)).symm.pow_right n
  rw [h.mul_pow, ← map_pow, hN, map_zero, zero_mul]

private theorem polynomial_derivative_exp_X (a : A) (ha : IsNilpotent a) :
    (IsNilpotent.exp (C a * X)).derivative = C a * IsNilpotent.exp (C a * X) := by
  have hn : IsNilpotent (C a * X) := by
    simpa only [pow_one] using polynomial_nilpotent_mul_X_pow a ha 1
  rw [derivative_exp_of_commute hn, derivative_C_mul_X]
  rw [derivative_C_mul_X]
  exact (Commute.refl (C a)).mul_left (commute_X _)

private theorem polynomial_derivative_exp_X_sq (a : A) (ha : IsNilpotent a) :
    (IsNilpotent.exp (C a * X ^ 2)).derivative = C (a * 2) * X * IsNilpotent.exp (C a * X ^ 2) := by
  rw [derivative_exp_of_commute (polynomial_nilpotent_mul_X_pow a ha 2), derivative_C_mul_X_sq]
  rw [derivative_C_mul_X_sq]
  have hc : Commute a (a * 2) := (Commute.refl a).mul_right (Nat.cast_commute 2 a).symm
  exact ((hc.map C).mul_right (commute_X _).symm).mul_left
    (((commute_X _).pow_left 2).mul_right ((commute_X X).pow_left 2))

private theorem exp_mul_of_central_bracket {a : A} (ha : IsNilpotent a) (b : A)
    (h : Commute a (a * b - b * a)) :
    IsNilpotent.exp a * b = (b + (a * b - b * a)) * IsNilpotent.exp a := by
  let T := LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a
  have hT : IsNilpotent T := by
    have hL := ha.map (Algebra.lmul ℚ A)
    obtain ⟨n, hn⟩ := ha
    refine (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hL ⟨n, ?_⟩
    rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]
  have hT2 : (T ^ 2) • b = 0 := by
    rw [pow_two]
    change a * (a * b - b * a) - (a * b - b * a) * a = 0
    exact sub_eq_zero.mpr h.eq
  have hconj := nilpotent_exp_conjugation ha b
  change (IsNilpotent.exp T) • b = _ at hconj
  rw [IsNilpotent.exp_smul_eq_sum hT2 hT] at hconj
  have he : IsNilpotent.exp a * b * IsNilpotent.exp (-a) = b + (a * b - b * a) := by
    change _ = b + T • b
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_zero, pow_one] using hconj.symm
  have hf := congrArg (· * IsNilpotent.exp a) he
  simpa only [mul_assoc, ha.exp_neg_mul_exp_self, mul_one] using hf

private theorem polynomial_ode_eq_exp (a : A) (p : Polynomial A)
    (h : p.derivative = C a * p) (h₀ : p.coeff 0 = 1) :
    IsNilpotent a ∧ p = IsNilpotent.exp (C a * X) := by
  have hrec (n : ℕ) : ((n + 1 : ℕ) : ℚ) • p.coeff (n + 1) = a * p.coeff n := by
    have he := congrArg (fun q : Polynomial A => q.coeff n) h
    rw [coeff_derivative, coeff_C_mul] at he
    rw [Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul, (Nat.cast_commute (n+1) (p.coeff (n+1))).eq, Nat.cast_succ]
    exact he
  have hp (n : ℕ) : a ^ n = (n.factorial : ℚ) • p.coeff n := by
    induction n with
    | zero => simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, one_smul, h₀]
    | succ n ih =>
      rw [pow_succ', ih, mul_smul_comm, ← hrec, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_comm]
  have ha : IsNilpotent a := by
    refine ⟨p.natDegree + 1, ?_⟩
    rw [hp, coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), smul_zero]
  refine ⟨ha, ?_⟩
  let q := IsNilpotent.exp (C a * X)
  have hq : q.derivative = C a * q := polynomial_derivative_exp_X a ha
  have hq₀ : q.coeff 0 = 1 := by
    let e := eval₂RingHom' (RingHom.id A) 0 (fun a => Commute.zero_right _)
    have hn : IsNilpotent (C a * X) := by simpa only [pow_one] using polynomial_nilpotent_mul_X_pow a ha 1
    have hh := IsNilpotent.map_exp hn e
    change eval₂ (RingHom.id A) 0 q = IsNilpotent.exp (e (C a * X)) at hh
    rw [eval₂_at_zero, RingHom.id_apply, map_mul] at hh
    change _ = IsNilpotent.exp (e (C a) * eval₂ (RingHom.id A) 0 X) at hh
    rwa [eval₂_X, mul_zero, IsNilpotent.exp_zero] at hh
  ext n
  induction n with
  | zero => exact h₀.trans hq₀.symm
  | succ n ih =>
    have he := congrArg (fun v : Polynomial A => v.coeff n) hq
    rw [coeff_derivative, coeff_C_mul, ← ih, ← hrec] at he
    have hs (x : A) : ((n + 1 : ℕ) : ℚ) • x = x * ((n : A) + 1) := by
      rw [Nat.cast_smul_eq_nsmul ℚ, nsmul_eq_mul, (Nat.cast_commute (n+1) x).eq, Nat.cast_succ]
    rw [hs] at he
    have hu : IsUnit ((n : A) + 1) := by
      rw [← Nat.cast_succ]
      simpa only [map_natCast] using ((show IsUnit (((n + 1 : ℕ) : ℚ)) from (by positivity : 0 < ((n+1 : ℕ) : ℚ)).ne'.isUnit).map (algebraMap ℚ A))
    exact (hu.mul_left_inj.mp he).symm

/-- The class-two exponential formula in a rational associative algebra.
The existence of the polynomial flow also proves nilpotence of the sum. -/
theorem nilpotent_exp_add_of_central_bracket (a b : A) (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hc : IsNilpotent (a * b - b * a))
    (hca : Commute a (a * b - b * a)) (hcb : Commute b (a * b - b * a)) :
    IsNilpotent (a + b) ∧ IsNilpotent.exp (a + b) =
      IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp ((- (1/2 : ℚ)) • (a * b - b * a)) := by
  let c := a * b - b * a
  let d := (- (1/2 : ℚ)) • c
  have hd : IsNilpotent d := by
    obtain ⟨n, hn⟩ := hc
    exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩
  have hd₂ : d * (2 : A) = -c := by
    change ((- (1/2 : ℚ)) • c) * (2 : A) = -c
    rw [smul_mul_assoc]
    have h : c * (2 : A) = (2 : ℚ) • c := by
      rw [Algebra.smul_def, map_ofNat]
      noncomm_ring
    rw [h, smul_smul, show (- (1/2 : ℚ)) * 2 = -1 by norm_num, neg_one_smul]
  let p := C a * (X : Polynomial A)
  let q := C b * (X : Polynomial A)
  let r := C d * (X : Polynomial A) ^ 2
  let E := IsNilpotent.exp p
  let F := IsNilpotent.exp q
  let G := IsNilpotent.exp r
  let B := C c * (X : Polynomial A)
  have hp : IsNilpotent p := by simpa only [p, pow_one] using polynomial_nilpotent_mul_X_pow a ha 1
  have hq : IsNilpotent q := by simpa only [q, pow_one] using polynomial_nilpotent_mul_X_pow b hb 1
  have hr : IsNilpotent r := polynomial_nilpotent_mul_X_pow d hd 2
  have hE : E.derivative = C a * E := polynomial_derivative_exp_X a ha
  have hF : F.derivative = C b * F := polynomial_derivative_exp_X b hb
  have hG : G.derivative = -B * G := by
    change (IsNilpotent.exp (C d * X ^ 2)).derivative = _
    rw [polynomial_derivative_exp_X_sq d hd, hd₂, map_neg, neg_mul]
  have hpc : Commute p B := ((hca.map C).mul_right (commute_X (C a)).symm).mul_left
    ((commute_X (C c)).mul_right (Commute.refl X))
  have hqc : Commute q B := ((hcb.map C).mul_right (commute_X (C b)).symm).mul_left
    ((commute_X (C c)).mul_right (Commute.refl X))
  have hB : p * C b - C b * p = B := by
    unfold p B c
    rw [mul_assoc, (commute_X (C b)).eq, ← mul_assoc, ← mul_assoc, ← sub_mul, ← map_mul, ← map_mul, ← map_sub]
  have hx : E * C b = (C b + B) * E :=
    exp_mul_of_central_bracket hp (C b) (hB.symm ▸ hpc) |>.trans (by rw [hB])
  have commExp {u v : Polynomial A} (hu : IsNilpotent u) (hc : Commute u v) :
      Commute (IsNilpotent.exp u) v := by
    obtain ⟨m, hm⟩ := hu
    rw [IsNilpotent.exp_eq_sum hm]
    apply Commute.sum_left
    intro n hn
    exact (hc.pow_left n).smul_left _
  have hEF : Commute (E * F) B := (commExp hp hpc).mul_left (commExp hq hqc)
  let S := E * F * G
  have hS : S.derivative = C (a + b) * S := by
    change (E * F * G).derivative = _
    rw [derivative_mul, derivative_mul, hE, hF, hG, ← mul_assoc E (C b) F, hx,
      ← mul_assoc (E * F) (-B) G, mul_neg, hEF.eq, map_add]
    unfold S
    noncomm_ring
  let evalAt (t : A) (ht : ∀ a : A, Commute a t) := eval₂RingHom' (RingHom.id A) t ht
  let e := evalAt 0 (fun _ => Commute.zero_right _)
  have hS₀ : S.coeff 0 = 1 := by
    have hev (n : ℕ) (a : A) : e (C a * X ^ (n + 1)) = 0 := by
      rw [map_mul, map_pow]
      change _ * eval₂ (RingHom.id A) (0 : A) X ^ (n + 1) = _
      rw [eval₂_X, zero_pow (Nat.succ_ne_zero n), mul_zero]
    have hp₀ : e p = 0 := by simpa only [p, Nat.zero_add, pow_one] using hev 0 a
    have hq₀ : e q = 0 := by simpa only [q, Nat.zero_add, pow_one] using hev 0 b
    have hr₀ : e r = 0 := hev 1 d
    have he : e S = 1 := by
      dsimp only [S, E, F, G]
      rw [map_mul, map_mul, IsNilpotent.map_exp hp e, IsNilpotent.map_exp hq e,
        IsNilpotent.map_exp hr e, hp₀, hq₀, hr₀, IsNilpotent.exp_zero, one_mul, one_mul]
    change eval₂ (RingHom.id A) 0 S = _ at he
    rwa [eval₂_at_zero, RingHom.id_apply] at he
  obtain ⟨hs, he⟩ := polynomial_ode_eq_exp (a + b) S hS hS₀
  let e₁ := evalAt 1 (fun _ => Commute.one_right _)
  have hh := congrArg e₁ he
  have hs' : IsNilpotent (C (a+b) * (X : Polynomial A)) := by
    simpa only [pow_one] using polynomial_nilpotent_mul_X_pow _ hs 1
  have he₁ (a : A) (n : ℕ) : e₁ (C a * X ^ n) = a := by
    rw [map_mul, map_pow]
    change eval₂ (RingHom.id A) (1 : A) (C a) * eval₂ (RingHom.id A) (1 : A) X ^ n = _
    rw [eval₂_C, eval₂_X, RingHom.id_apply, one_pow, mul_one]
  have ha₁ : e₁ p = a := by simpa only [p, pow_one] using he₁ a 1
  have hb₁ : e₁ q = b := by simpa only [q, pow_one] using he₁ b 1
  have hab₁ : e₁ (C (a+b) * (X : Polynomial A)) = a+b := by
    simpa only [pow_one] using he₁ (a+b) 1
  dsimp only [S, E, F, G] at hh
  rw [map_mul, map_mul, IsNilpotent.map_exp hp e₁, IsNilpotent.map_exp hq e₁,
    IsNilpotent.map_exp hr e₁, IsNilpotent.map_exp hs' e₁, ha₁, hb₁, he₁ d 2, hab₁] at hh
  exact ⟨hs, hh.symm⟩

/-- Sum of associative commutators taken in the order of a finite list. -/
private def orderedBracketSum : List A → A
  | [] => 0
  | a :: l => a * l.sum - l.sum * a + orderedBracketSum l

private theorem bracket_sum_mem (Z : Submodule ℚ A) (a : A) (l : List A)
    (h : ∀ b ∈ l, a * b - b * a ∈ Z) : a * l.sum - l.sum * a ∈ Z := by
  induction l with
  | nil => simpa using Z.zero_mem
  | cons b l ih =>
    have hb := h b List.mem_cons_self
    have hl := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [List.sum_cons, mul_add, add_mul, add_sub_add_comm]
    exact Z.add_mem hb hl

private theorem orderedBracketSum_mem (Z : Submodule ℚ A) (l : List A)
    (h : ∀ a ∈ l, ∀ b ∈ l, a * b - b * a ∈ Z) : orderedBracketSum l ∈ Z := by
  induction l with
  | nil => exact Z.zero_mem
  | cons a l ih =>
    simp only [orderedBracketSum]
    exact Z.add_mem (bracket_sum_mem Z a l fun b hb => h a List.mem_cons_self b (List.mem_cons_of_mem _ hb))
      (ih fun p hp q hq => h p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq))

private theorem commute_list_sum (a : A) (l : List A) (h : ∀ b ∈ l, Commute a b) :
    Commute a l.sum := by
  induction l with
  | nil => exact Commute.zero_right _
  | cons b l ih =>
    exact (h b List.mem_cons_self).add_right (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- A list in a class-two associative algebra separates into exponentials in
its given order with a single correction from the sum of its commutators. -/
private theorem nilpotent_exp_list_sum_of_central_brackets (Z : Submodule ℚ A)
    (hZ : ∀ z ∈ Z, IsNilpotent z)
    (hZZ : ∀ a ∈ Z, ∀ b ∈ Z, Commute a b)
    (l : List A) (hn : ∀ a ∈ l, IsNilpotent a)
    (hc : ∀ a ∈ l, ∀ z ∈ Z, Commute a z)
    (hb : ∀ a ∈ l, ∀ b ∈ l, a * b - b * a ∈ Z) :
    IsNilpotent l.sum ∧ IsNilpotent.exp l.sum = (l.map IsNilpotent.exp).prod *
      IsNilpotent.exp ((-(1/2 : ℚ)) • orderedBracketSum l) := by
  induction l with
  | nil => simp [orderedBracketSum, IsNilpotent.exp_zero, IsNilpotent.zero]
  | cons a l ih =>
    have hmem (b : A) (hb : b ∈ l) : b ∈ a :: l := List.mem_cons_of_mem _ hb
    have hb' (b : A) (hm : b ∈ l) (d : A) (hd : d ∈ l) := hb b (hmem b hm) d (hmem d hd)
    obtain ⟨hl, he⟩ := ih (fun b hb => hn b (hmem _ hb)) (fun b hb => hc b (hmem _ hb)) hb'
    let x := a * l.sum - l.sum * a
    have hx : x ∈ Z := bracket_sum_mem Z a l fun b hb₁ => hb a List.mem_cons_self b (hmem b hb₁)
    have hcl : Commute l.sum x := (commute_list_sum x l fun b hb => (hc b (hmem b hb) x hx).symm).symm
    obtain ⟨hn', he'⟩ := nilpotent_exp_add_of_central_bracket a l.sum (hn a List.mem_cons_self) hl
      (hZ x hx) (hc a List.mem_cons_self x hx) hcl
    let c : ℚ := -(1/2 : ℚ)
    have hy : c • orderedBracketSum l ∈ Z := Z.smul_mem _ (orderedBracketSum_mem Z l hb')
    have hx' : c • x ∈ Z := Z.smul_mem _ hx
    refine ⟨hn', ?_⟩
    change IsNilpotent.exp (a + l.sum) =
      IsNilpotent.exp a * (l.map IsNilpotent.exp).prod * IsNilpotent.exp (c • (x + orderedBracketSum l))
    rw [he', he, smul_add, add_comm (c • x), IsNilpotent.exp_add_of_commute (hZZ _ hy _ hx') (hZ _ hy) (hZ _ hx')]
    simp only [x, c, mul_assoc]

/-- Changing the order changes the sum of commutators by twice an element of
any integer lattice containing the pairwise commutators. -/
private theorem orderedBracketSum_perm (Z : Submodule ℤ A) {l l' : List A} (h : l.Perm l')
    (hb : ∀ a ∈ l, ∀ b ∈ l, a * b - b * a ∈ Z) :
    ∃ z ∈ Z, orderedBracketSum l = orderedBracketSum l' + (2 : ℕ) • z := by
  induction h with
  | nil => exact ⟨0, Z.zero_mem, by simp [orderedBracketSum]⟩
  | cons a h ih =>
    obtain ⟨z, hz, he⟩ := ih fun x hx y hy => hb x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    refine ⟨z, hz, ?_⟩
    simp only [orderedBracketSum, h.sum_eq, he, add_assoc]
  | swap a b l =>
    have hz : b * a - a * b ∈ Z := hb _ List.mem_cons_self _ (List.mem_cons_of_mem _ List.mem_cons_self)
    refine ⟨b * a - a * b, hz, ?_⟩
    simp only [orderedBracketSum, List.sum_cons, two_nsmul]
    noncomm_ring
  | trans h h' ih ih' =>
    obtain ⟨z, hz, he⟩ := ih hb
    obtain ⟨z', hz', he'⟩ := ih' fun x hx y hy => hb x (h.mem_iff.mpr hx) y (h.mem_iff.mpr hy)
    exact ⟨z' + z, Z.add_mem hz' hz, by rw [he, he', smul_add, add_assoc]⟩


end CentralExponential

/-- The simple coroots form a basis when the full cocharacter lattice is
generated by its coroots. -/
def simpleCorootBasis (D : BasedRootDatum.{u})
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Module.Basis D.base.support ℤ D.Y :=
  Module.Basis.mk D.base.linearIndepOn_coroot (by
    have he : Set.range (fun i : D.base.support => D.datum.coroot i) =
        D.datum.coroot '' (D.base.support : Set D.I) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, i.property, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    change ⊤ ≤ Submodule.span ℤ (Set.range (fun i : D.base.support => D.datum.coroot i))
    rw [he, D.base.span_int_coroot_support, hcoroot])

@[simp]
theorem simpleCorootBasis_apply (D : BasedRootDatum.{u}) (hcoroot) (i : D.base.support) :
    simpleCorootBasis D hcoroot i = D.datum.coroot i :=
  Module.Basis.mk_apply _ _ _

/-- The dual basis in the full character lattice consists of fundamental
weights, as specified by the marked integral pairing. -/
def fundamentalWeightBasis (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Module.Basis D.base.support ℤ D.X :=
  (simpleCorootBasis D hcoroot).dualBasis.map D.datum.toPerfPair.symm

theorem fundamentalWeightBasis_pair (D : BasedRootDatum.{u}) [DecidableEq D.base.support] (hcoroot)
    (i j : D.base.support) :
    D.datum.toLinearMap (fundamentalWeightBasis D hcoroot i) (D.datum.coroot j) =
      if j = i then 1 else 0 := by
  let b := simpleCorootBasis D hcoroot
  change D.datum.toPerfPair (D.datum.toPerfPair.symm (b.dualBasis i)) (D.datum.coroot j) = _
  rw [LinearEquiv.apply_symm_apply, ← simpleCorootBasis_apply D hcoroot j]
  exact b.dualBasis_apply_self i j

/-- The dual basis consists of the marked fundamental weights. -/
theorem fundamentalWeights : FundamentalWeights.{u} := by
  intro D hcoroot
  classical
  refine ⟨fundamentalWeightBasis D hcoroot, fun i => ⟨?_, ?_⟩⟩
  · simpa using fundamentalWeightBasis_pair D hcoroot i i
  · intro j hj
    simpa [hj] using fundamentalWeightBasis_pair D hcoroot i j

/-- The simple coroot evaluations recover the character itself in this
lattice case. -/
theorem simpleCorootEvaluations_injective (D : BasedRootDatum.{u})
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Function.Injective (fun x : D.X => fun i : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot i)) := by
  intro x y h
  apply D.datum.toPerfPair.injective
  apply (simpleCorootBasis D hcoroot).ext
  intro i
  rw [simpleCorootBasis_apply]
  exact congrFun h i

/-- Every coroot is primitive in the coroot lattice. A character taking
value one on it is obtained by transporting a fundamental weight. -/
theorem coroot_has_character_value_one (D : BasedRootDatum.{u})
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) (i : D.I) :
    ∃ x : D.X, D.datum.toLinearMap x (D.datum.coroot i) = 1 := by
  classical
  letI := D.finiteRoots
  letI := D.reduced
  let p (i : D.I) := ∃ x : D.X, D.datum.coroot' i x = 1
  have hreflect (i j : D.I) (h : p i) : p (D.datum.reflectionPerm j i) := by
    rcases h with ⟨x, hx⟩
    refine ⟨D.datum.reflection j x, ?_⟩
    rw [D.datum.coroot'_reflectionPerm, LinearMap.comp_apply]
    change D.datum.coroot' i (D.datum.reflection j (D.datum.reflection j x)) = 1
    rwa [D.datum.reflection_same]
  change p i
  apply D.base.induction_reflect i (fun j => hreflect j j) ?_ (fun j k hj _ => hreflect j k hj)
  intro j hj
  refine ⟨fundamentalWeightBasis D hcoroot ⟨j, hj⟩, ?_⟩
  simpa using fundamentalWeightBasis_pair D hcoroot ⟨j, hj⟩ ⟨j, hj⟩

theorem rootString_endpoints (D : BasedRootDatum.{u}) {i j : D.I}
    (h : LinearIndependent ℤ ![D.datum.root i, D.datum.root j]) :
    letI : Finite D.I := D.finiteRoots
    IsRootString i j (D.datum.chainBotCoeff i j) (D.datum.chainTopCoeff i j) ∧
      D.datum.chainBotCoeff i j + D.datum.chainTopCoeff i j ≤ 3 := by
  letI : Finite D.I := D.finiteRoots
  letI := D.reduced
  exact ⟨fun _ => RootPairing.root_add_zsmul_mem_range_iff h,
    RootPairing.chainBotCoeff_add_chainTopCoeff_le_three⟩

namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)

private theorem signed_sum_dvd_two {ι : Type*} (s : Finset ι) (a : ι → ℕ) (b : ι → ℤ)
    (hs : ∀ i ∈ s, b i = (a i : ℤ) ∨ b i = -(a i : ℤ))
    (h : (∑ i ∈ s, a i) % 2 = 0) :
    ∃ n : ℤ, (∑ i ∈ s, b i) = 2 * n := by
  have hmod (i : ι) (hi : i ∈ s) : b i ≡ (a i : ℤ) [ZMOD 2] := by
    change b i % 2 = (a i : ℤ) % 2
    rcases hs i hi with h | h
    · rw [h]
    · rw [h]
      omega
  have he := Int.ModEq.sum hmod
  change (∑ i ∈ s, b i) % 2 = (∑ i ∈ s, (a i : ℤ)) % 2 at he
  have hsum : ((∑ i ∈ s, a i : ℕ) : ℤ) % 2 = 0 := by exact_mod_cast h
  rw [← Nat.cast_sum, hsum] at he
  exact ⟨(∑ i ∈ s, b i) / 2, by omega⟩

/-- Evenness holds for the signed correction in each bracket root, so
dividing that coefficient by two stays in the integers. -/
theorem centralBracketCoefficients_integral :
    Specs.IntegralRootRelations.RankTwo.CentralBracketCoefficientsIntegral := by
  intro kind a b ha hb hdet horder c hc
  intro ij hij
  have h := (centralBrackets_even kind a ha b hb hdet horder).2 ij hij
  refine signed_sum_dvd_two _ (bracketMagnitude (rankTwoCoefficients kind) a b) c ?_ h
  exact fun k hk => hc k (Finset.mem_filter.mp hk).1

end RankTwo

section DividedRootBrackets

variable {D : BasedRootDatum.{u}}

private theorem IsRootString.shift {i j k : D.I} {p q d : ℕ}
    (h : IsRootString i j p q) (hd : d ≤ q)
    (hk : D.datum.root k = D.datum.root j + (d : ℤ) • D.datum.root i) :
    IsRootString i k (p + d) (q - d) := by
  intro n
  rw [hk, add_assoc, ← add_zsmul, h]
  omega

private theorem IsRootString.backwardLength_unique {i j : D.I} {p p' q q' : ℕ}
    (h : IsRootString i j p q) (h' : IsRootString i j p' q') : p = p' := by
  have hl := (h' (-(p : ℤ))).mp ((h _).mpr (by omega))
  have hr := (h (-(p' : ℤ))).mp ((h' _).mpr (by omega))
  omega

private theorem factorial_choose_step (p n : ℕ) :
    (n.factorial : ℤ) * ((p + n).choose n : ℤ) * ((p : ℤ) + n + 1) =
      ((n + 1).factorial : ℤ) * ((p + (n + 1)).choose (n + 1) : ℤ) := by
  have h : n.factorial * (p + n).choose n * (p + n + 1) =
      (n + 1).factorial * (p + (n + 1)).choose (n + 1) := by
    calc
      _ = n.factorial * ((p + n + 1) * (p + n).choose n) := by ac_rfl
      _ = n.factorial * ((p + n + 1).choose (n + 1) * (n + 1)) := by
        rw [Nat.add_one_mul_choose_eq]
      _ = _ := by rw [Nat.factorial_succ, ← Nat.add_assoc]; ac_rfl
  exact_mod_cast h

/-- Iterating the Chevalley brackets on a root string gives the signed
binomial coefficients after division by the corresponding factorial. -/
theorem iteratedRootBracket_factorial_choose {V : Type v} [LieRing V]
    (e : D.I → V)
    (hbracket : ∀ i j k : D.I, D.datum.root i + D.datum.root j = D.datum.root k →
      ∃ (p q : ℕ) (c : ℤ), IsRootString i j p q ∧
        (c = (p : ℤ) + 1 ∨ c = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = c • e k)
    (i j : D.I) (p q : ℕ) (h : IsRootString i j p q) :
    ∃ s : ℕ → D.I, s 0 = j ∧
      ∀ d ≤ q, D.datum.root (s d) = D.datum.root j + (d : ℤ) • D.datum.root i ∧
        ∃ c : ℤ, (c = ((p + d).choose d : ℤ) ∨ c = -((p + d).choose d : ℤ)) ∧
          (fun x : V => ⁅e i, x⁆)^[d] (e j) = ((d.factorial : ℤ) * c) • e (s d) := by
  classical
  have hx (d : ℕ) (hd : d ≤ q) :
      ∃ k, D.datum.root k = D.datum.root j + (d : ℤ) • D.datum.root i :=
    (h (d : ℤ)).mpr (by omega)
  let s (d : ℕ) : D.I := if hd : d ≤ q then (hx d hd).choose else j
  have hs (d : ℕ) (hd : d ≤ q) : D.datum.root (s d) =
      D.datum.root j + (d : ℤ) • D.datum.root i := by
    dsimp only [s]
    rw [dite_eq_left hd]
    exact (hx d hd).choose_spec
  have hs₀ : s 0 = j := D.datum.root.injective (by simpa using hs 0 (Nat.zero_le q))
  refine ⟨s, hs₀, fun d hd => ⟨hs d hd, ?_⟩⟩
  induction d with
  | zero => refine ⟨1, Or.inl (by simp), ?_⟩; simp [hs₀]
  | succ d ih =>
    have hd' : d ≤ q := Nat.le_of_succ_le hd
    obtain ⟨a, ha, he⟩ := ih hd'
    have hstep : D.datum.root i + D.datum.root (s d) = D.datum.root (s (d + 1)) := by
      rw [hs d hd', hs (d+1) hd, Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
      abel
    obtain ⟨p', q', b, hstr, hb, hh⟩ := hbracket i (s d) (s (d + 1)) hstep
    have hp' := IsRootString.backwardLength_unique hstr (IsRootString.shift h hd' (hs d hd'))
    rw [hp', Nat.cast_add] at hb
    rw [Function.iterate_succ_apply', he, lie_zsmul, hh, smul_smul]
    let N : ℤ := ((p + d + 1).choose (d + 1) : ℤ)
    have hf := factorial_choose_step p d
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · refine ⟨N, Or.inl rfl, ?_⟩
      rw [ha, hb, hf]
      rfl
    · refine ⟨-N, Or.inr rfl, ?_⟩
      rw [ha, hb, mul_neg, hf, mul_neg]
      rfl
    · refine ⟨-N, Or.inr rfl, ?_⟩
      rw [ha, hb, mul_neg, neg_mul, hf, mul_neg]
      rfl
    · refine ⟨N, Or.inl rfl, ?_⟩
      simp only [ha, hb, mul_neg, neg_mul, neg_neg, hf]
      rfl

/-- Past the upper endpoint of an independent string the iterated bracket
vanishes, because the next sum is nonzero and lies outside the roots. -/
theorem iteratedRootBracket_zero_after_string {V : Type v} [LieRing V]
    (e : D.I → V)
    (hbracket : ∀ i j k : D.I, D.datum.root i + D.datum.root j = D.datum.root k →
      ∃ (p q : ℕ) (c : ℤ), IsRootString i j p q ∧
        (c = (p : ℤ) + 1 ∨ c = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = c • e k)
    (hzero : ∀ i j : D.I, D.datum.root i + D.datum.root j ≠ 0 →
      D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0)
    (i j : D.I) (hi : LinearIndependent ℤ ![D.datum.root i, D.datum.root j])
    (p q : ℕ) (h : IsRootString i j p q) (d : ℕ) (hd : q < d) :
    (fun x : V => ⁅e i, x⁆)^[d] (e j) = 0 := by
  obtain ⟨s, _, hs⟩ := iteratedRootBracket_factorial_choose e hbracket i j p q h
  obtain ⟨hr, c, _, he⟩ := hs q le_rfl
  have hsum : D.datum.root i + D.datum.root (s q) =
      ((q : ℤ) + 1) • D.datum.root i + D.datum.root j := by
    rw [hr, add_zsmul, one_zsmul]
    abel
  have hne : D.datum.root i + D.datum.root (s q) ≠ 0 := by
    rw [hsum]
    intro hz
    have hz' : ((q : ℤ) + 1) • D.datum.root i + (1 : ℤ) • D.datum.root j = 0 := by
      rwa [one_zsmul]
    exact one_ne_zero (hi.eq_zero_of_pair hz').2
  have hnmem : D.datum.root i + D.datum.root (s q) ∉ Set.range D.datum.root := by
    rw [hsum, add_comm, h]
    omega
  have hk : (fun x : V => ⁅e i, x⁆)^[q + 1] (e j) = 0 := by
    rw [Function.iterate_succ_apply', he, lie_zsmul, hzero i (s q) hne hnmem, smul_zero]
  obtain ⟨r, heq⟩ := Nat.exists_eq_add_of_le (show q + 1 ≤ d by omega)
  rw [heq, add_comm (q + 1) r, Function.iterate_add_apply, hk]
  exact Function.iterate_fixed (lie_zero (e i)) r

end DividedRootBrackets

section ConjugatedRootString

variable {D : BasedRootDatum.{u}} {V : Type v} [LieRing V]
  {R : Type v} [CommRing R] [Algebra ℚ R]
  {M : Type w} [Ring M] [Algebra ℚ M] [Algebra R M] [IsScalarTower ℚ R M]

/-- Conjugation of a root vector in an associative representation has the
integer coefficients of the divided brackets of its root string. -/
theorem conjugateRootString_eq_sum
    (e : D.I → V) (f : V →+ M) (hf : ∀ a b, f ⁅a,b⁆ = f a * f b - f b * f a)
    (hbr : ∀ i j k : D.I, D.datum.root i + D.datum.root j = D.datum.root k →
      ∃ (p q : ℕ) (c : ℤ), IsRootString i j p q ∧
        (c = (p : ℤ) + 1 ∨ c = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = c • e k)
    (hzero : ∀ i j : D.I, D.datum.root i + D.datum.root j ≠ 0 →
      D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0)
    (i j : D.I) (hi : LinearIndependent ℤ ![D.datum.root i, D.datum.root j])
    (p q : ℕ) (hstr : IsRootString i j p q) :
    ∃ (s : ℕ → D.I) (c : ℕ → ℤ), s 0 = j ∧ c 0 = 1 ∧
      (∀ d ≤ q, D.datum.root (s d) = D.datum.root j + (d : ℤ) • D.datum.root i ∧
        (c d = ((p+d).choose d : ℤ) ∨ c d = -((p+d).choose d : ℤ))) ∧
      ∀ x y : R, IsNilpotent (x • f (e i)) →
        IsNilpotent.exp (x • f (e i)) * (y • f (e j)) * IsNilpotent.exp (-(x • f (e i))) =
          ∑ d ∈ Finset.range (q+1), ((c d : R) * x ^ d * y) • f (e (s d)) := by
  classical
  obtain ⟨s, hs₀, hs⟩ := iteratedRootBracket_factorial_choose e hbr i j p q hstr
  have hc (d : ℕ) (hd : d ≤ q) : ∃ c : ℤ,
      (c = ((p+d).choose d : ℤ) ∨ c = -((p+d).choose d : ℤ)) ∧
      (fun a : V => ⁅e i,a⁆)^[d] (e j) = (d.factorial * c : ℤ) • e (s d) := (hs d hd).2
  let c (d : ℕ) : ℤ := if d = 0 then 1 else if h : d ≤ q then (hc d h).choose else 0
  have hconst (d : ℕ) (hd : d ≤ q) :
      (c d = ((p+d).choose d : ℤ) ∨ c d = -((p+d).choose d : ℤ)) ∧
        (fun a : V => ⁅e i,a⁆)^[d] (e j) = (d.factorial * c d : ℤ) • e (s d) := by
    by_cases h : d = 0
    · subst d
      simp [c, hs₀]
    · simpa [c, h, hd] using (hc d hd).choose_spec
  refine ⟨s, c, hs₀, by simp [c], fun d hd => ⟨(hs d hd).1, (hconst d hd).1⟩, ?_⟩
  intro x y ha
  let a := x • f (e i)
  let b := y • f (e j)
  let T := LinearMap.mulLeft ℚ a - LinearMap.mulRight ℚ a
  have hT : IsNilpotent T := by
    have hL := ha.map (Algebra.lmul ℚ M)
    obtain ⟨n, hn⟩ := ha
    refine (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hL ⟨n, ?_⟩
    rw [LinearMap.pow_mulRight, hn, LinearMap.mulRight_zero_eq_zero]
  have hpow (n : ℕ) : (T ^ n) • b = (x ^ n * y) • f ((fun a : V => ⁅e i,a⁆)^[n] (e j)) := by
    induction n with
    | zero => simp [b]
    | succ n ih =>
      have h := (Function.iterate_succ_apply' (fun a : V => ⁅e i,a⁆) n (e j))
      rw [pow_succ', mul_smul, ih, h, hf]
      change (x • f (e i)) * ((x ^ n * y) • f ((fun a : V => ⁅e i,a⁆)^[n] (e j))) -
        ((x ^ n * y) • f ((fun a : V => ⁅e i,a⁆)^[n] (e j))) * (x • f (e i)) = _
      rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
        mul_comm (x ^ n * y) x, ← smul_sub, ← mul_assoc, ← pow_succ']
  have hcut : (T ^ (q+1)) • b = 0 := by
    rw [hpow, iteratedRootBracket_zero_after_string e hbr hzero i j hi p q hstr _ (Nat.lt_succ_self _),
      map_zero, smul_zero]
  have hconj := (nilpotent_exp_conjugation ha b).symm
  change IsNilpotent.exp a * b * IsNilpotent.exp (-a) = (IsNilpotent.exp T) • b at hconj
  rw [hconj, IsNilpotent.exp_smul_eq_sum hcut hT]
  apply Finset.sum_congr rfl
  intro d hd
  have hd' : d ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  rw [hpow, (hconst d hd').2, map_zsmul, ← Int.cast_smul_eq_zsmul R, smul_smul,
    ← IsScalarTower.algebraMap_smul R, smul_smul]
  congr 1
  have hFac : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [Int.cast_mul, Int.cast_natCast]
  have hcanc : algebraMap ℚ R ((d.factorial : ℚ)⁻¹) * (d.factorial : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R) d.factorial, ← map_mul, inv_mul_cancel₀ hFac, map_one]
  calc
    _ = (algebraMap ℚ R ((d.factorial : ℚ)⁻¹) * (d.factorial : R)) * ((c d : R) * x ^ d * y) := by ring
    _ = _ := by rw [hcanc, one_mul]

end ConjugatedRootString


namespace RankTwo

open LieAlgebrasAndRepresentations
  (RootAxioms IsRootSystem RankTwoModel RankTwoKind rankTwoCoefficients rankTwoRootSet
    rootReflection component_rootSystem rank_two_classification)


variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Restricting a reduced root system to the plane of two independent roots
gives one of the four rank-two systems, with the induced metric. -/
theorem rootPlane_model (R : Set E) (hR : RootAxioms R)
    (a b : E) (ha : a ∈ R) (hb : b ∈ R) (hab : LinearIndependent ℝ ![a,b]) :
    let P := Submodule.span ℝ ({a,b} : Set E)
    ∃ k : RankTwoKind, RankTwoModel {x : P | (x : E) ∈ R} k := by
  let P := Submodule.span ℝ ({a,b} : Set E)
  let S := R ∩ (P : Set E)
  have hS : RootAxioms S :=
    { finite := hR.finite.subset (fun _ hx => hx.1)
      nonzero := fun x hx => hR.nonzero x hx.1
      reflection_mem := fun x hx y hy =>
        ⟨hR.reflection_mem x hx.1 y hy.1, P.sub_mem hy.2 (P.smul_mem _ hx.2)⟩
      integral := fun x hx y hy => hR.integral x hx.1 y hy.1
      reduced := fun x hx y hy h => hR.reduced x hx.1 y hy.1 h }
  have he : Submodule.span ℝ S = P := by
    apply le_antisymm (Submodule.span_le.mpr fun _ h => h.2)
    apply Submodule.span_le.mpr
    intro x hx
    rcases (show x = a ∨ x = b from by simpa using hx) with rfl | rfl
    · exact Submodule.subset_span ⟨ha, Submodule.subset_span (by simp)⟩
    · exact Submodule.subset_span ⟨hb, Submodule.subset_span (by simp)⟩
  have hP : IsRootSystem {x : P | (x : E) ∈ R} := by
    have H := component_rootSystem S hS
    rw [he] at H
    have hs : {x : P | (x : E) ∈ S} = {x : P | (x : E) ∈ R} := by
      ext x
      exact ⟨And.left, fun h => ⟨h, x.property⟩⟩
    rwa [hs] at H
  have hdim : Module.finrank ℝ P = 2 := by
    have hset : Set.range ![a,b] = ({a,b} : Set E) := by
      simp [Matrix.range_cons, Matrix.range_empty, Set.pair_comm]
    change Module.finrank ℝ (Submodule.span ℝ ({a,b} : Set E)) = 2
    rw [← hset, finrank_span_eq_card hab, Fintype.card_fin]
  exact (rank_two_classification _ hP hdim).exists

private def rootPlaneCoords (a b : E) (x : Lattice) : E :=
  x.1 • a + x.2 • b

private theorem rootPlaneCoords_injective {a b : E} (hab : LinearIndependent ℝ ![a,b]) :
    Function.Injective (rootPlaneCoords a b) := by
  intro x y h
  have he : (x.1 : ℝ) • a + (x.2 : ℝ) • b = (y.1 : ℝ) • a + (y.2 : ℝ) • b := by
    simpa only [rootPlaneCoords, Int.cast_smul_eq_zsmul] using h
  exact Prod.ext (Int.cast_injective (α := ℝ) (hab.eq_of_pair he).1)
    (Int.cast_injective (α := ℝ) (hab.eq_of_pair he).2)

omit [InnerProductSpace ℝ E] in
private theorem rootPlaneCoords_step (a b : E) (x y : Lattice) (i : ℤ) :
    rootPlaneCoords a b (step x y i) = rootPlaneCoords a b y + i • rootPlaneCoords a b x := by
  simp only [step, rootPlaneCoords, add_smul, mul_smul, smul_add]
  abel

/-- In the exact coefficient model, the lattice string test reads membership
of the original root string in the Euclidean system. -/
theorem rootString_mem_rankTwoCoefficients {R : Set E} {a b : E} {kind : RankTwoKind}
    (hab : LinearIndependent ℝ ![a,b]) (hR : R = rankTwoRootSet kind a b)
    (x y : Lattice) (i : ℤ) :
    step x y i ∈ rankTwoCoefficients kind ↔
      rootPlaneCoords a b y + i • rootPlaneCoords a b x ∈ R := by
  rw [← rootPlaneCoords_step, hR]
  change step x y i ∈ (rankTwoCoefficients kind : Set Lattice) ↔
    rootPlaneCoords a b (step x y i) ∈ rootPlaneCoords a b '' (rankTwoCoefficients kind : Set Lattice)
  exact ((rootPlaneCoords_injective hab).mem_set_image).symm

end RankTwo

namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients rankTwoRootSet)
open RootData (realRoot realRootSpan euclideanComparison)
open private latticeEmbedding_injective from LinearAlgebraicGroups.RootData.EuclideanComparison

private theorem independentRoots_int {D : BasedRootDatum.{u}} {i j : D.I}
    (h : IndependentRoots i j) : LinearIndependent ℤ ![D.datum.root i, D.datum.root j] := by
  letI := D.reduced
  have hdiff : i ≠ j := by
    rintro rfl
    have he : (1 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) + (0 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) =
        (0 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) + (1 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) := by simp
    exact one_ne_zero (h.eq_of_pair he).1
  have hneg : D.datum.root i ≠ -D.datum.root j := by
    intro he
    have hm : (1 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) + (1 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root j) =
        (0 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root i) + (0 : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] D.datum.root j) := by
      simp [he, TensorProduct.tmul_neg]
    exact one_ne_zero (h.eq_of_pair hm).1
  exact RootPairing.IsReduced.linearIndependent D.datum hdiff hneg

private theorem determinant_ne_zero {X : Type u} [AddCommGroup X]
    (f : Lattice →+ X) (a b : Lattice) (h : LinearIndependent ℤ ![f a, f b]) :
    a.1 * b.2 - a.2 * b.1 ≠ 0 := by
  intro hdet
  have hcomb (x y : ℤ) (h0 : x • a + y • b = 0) : x = 0 ∧ y = 0 := by
    have hp := congrArg f h0
    simp only [map_add, map_zsmul, map_zero] at hp
    apply h.eq_of_pair
    simpa only [zero_zsmul, add_zero] using hp
  have h₁ : b.2 • a + (-a.2) • b = 0 := by
    ext <;> change (_ : ℤ) = 0
    · change b.2 * a.1 + (-a.2) * b.1 = 0
      rw [neg_mul, mul_comm b.2 a.1, ← sub_eq_add_neg]
      exact hdet
    · change b.2 * a.2 + (-a.2) * b.2 = 0
      ring
  obtain ⟨hb, ha⟩ := hcomb _ _ h₁
  have h₂ : b.1 • a + (-a.1) • b = 0 := by
    ext <;> change (_ : ℤ) = 0
    · change b.1 * a.1 + (-a.1) * b.1 = 0
      ring
    · change b.1 * a.2 + (-a.1) * b.2 = 0
      simp [hb, neg_eq_zero.mp ha]
  have he : a = 0 := Prod.ext (neg_eq_zero.mp (hcomb _ _ h₂).2) (neg_eq_zero.mp ha)
  have hz : f a ≠ 0 := h.ne_zero 0
  exact hz (he.symm ▸ map_zero f)

/-- The plane of two independent labelled roots admits an exact integral
rank-two coefficient model inside the original character lattice. -/
private theorem latticeModel_of_independentRoots (D : BasedRootDatum.{u}) {i j : D.I}
    (h : IndependentRoots i j) :
    ∃ (k : RankTwoKind) (f : Lattice →+ D.X) (a b : Lattice),
      Function.Injective f ∧ a ∈ rankTwoCoefficients k ∧ b ∈ rankTwoCoefficients k ∧
      a.1 * b.2 - a.2 * b.1 ≠ 0 ∧
      f a = D.datum.root i ∧ f b = D.datum.root j ∧
      ∀ p, p ∈ rankTwoCoefficients k ↔ f p ∈ Set.range D.datum.root := by
  classical
  letI : Finite D.I := D.finiteRoots
  letI := D.freeX
  letI := D.freeY
  letI := D.finiteX
  letI := D.finiteY
  letI := D.reduced
  let P := D.datum
  let V := realRootSpan P
  let R := Set.range (realRoot P)
  obtain ⟨_, _, _, _, _, M, _, _, _, hR, _⟩ := euclideanComparison P D.base
  letI : NormedAddCommGroup V := M.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore M.toCore
  have hZ := independentRoots_int h
  have hli : LinearIndependent ℝ ![realRoot P i, realRoot P j] := by
    apply LinearIndependent.of_comp (realRootSpan P).subtype
    convert Module.Flat.linearIndependent_one_tmul (S := ℝ) hZ using 1
    funext q
    fin_cases q <;> rfl
  let W := Submodule.span ℝ ({realRoot P i, realRoot P j} : Set V)
  obtain ⟨k, x, hx, y, hy, hxy, _, _, he⟩ :=
    rootPlane_model R hR.toRootAxioms (realRoot P i) (realRoot P j)
      (Set.mem_range_self i) (Set.mem_range_self j) hli
  obtain ⟨i₀, hi₀⟩ : (x : V) ∈ R := hx
  obtain ⟨j₀, hj₀⟩ : (y : V) ∈ R := hy
  let f : Lattice →+ D.X :=
    { toFun := fun z => z.1 • P.root i₀ + z.2 • P.root j₀
      map_zero' := by simp
      map_add' := by intro a b; simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel }
  let T := TensorProduct.mk ℤ ℝ D.X 1
  have hf (p : Lattice) : T (f p) = ((rootPlaneCoords x y p : W) : V).val := by
    change T (p.1 • P.root i₀ + p.2 • P.root j₀) = _
    rw [map_add, map_zsmul, map_zsmul]
    change p.1 • (realRoot P i₀).val + p.2 • (realRoot P j₀).val = _
    rw [hi₀, hj₀]
    rfl
  have hf_inj : Function.Injective f := fun r s hh => rootPlaneCoords_injective hxy
    (Subtype.ext (Subtype.ext ((hf r).symm.trans ((congrArg T hh).trans (hf s)))))
  have hmem (p : Lattice) : p ∈ rankTwoCoefficients k ↔ f p ∈ Set.range P.root := by
    have h : p ∈ rankTwoCoefficients k ↔ rootPlaneCoords x y p ∈ {x : W | (x : V) ∈ R} := by
      rw [he]
      exact (rootPlaneCoords_injective hxy).mem_set_image.symm
    rw [h]
    constructor
    · rintro ⟨r, hr⟩
      refine ⟨r, latticeEmbedding_injective ?_⟩
      exact (congrArg Subtype.val hr).trans (hf p).symm
    · rintro ⟨r, hr⟩
      exact ⟨r, Subtype.ext ((congrArg T hr).trans (hf p))⟩
  let r : W := ⟨realRoot P i, Submodule.subset_span (by simp)⟩
  let s : W := ⟨realRoot P j, Submodule.subset_span (by simp)⟩
  have hmr : r ∈ rankTwoRootSet k x y := he ▸ (show r ∈ {x : W | (x : V) ∈ R} from ⟨i, rfl⟩)
  have hms : s ∈ rankTwoRootSet k x y := he ▸ (show s ∈ {x : W | (x : V) ∈ R} from ⟨j, rfl⟩)
  obtain ⟨a, ha, ha'⟩ := hmr
  obtain ⟨b, hb, hb'⟩ := hms
  have hfa : f a = P.root i := latticeEmbedding_injective
    ((hf a).trans (congrArg (fun t : W => (t : V).val) ha'))
  have hfb : f b = P.root j := latticeEmbedding_injective
    ((hf b).trans (congrArg (fun t : W => (t : V).val) hb'))
  exact ⟨k, f, a, b, hf_inj, ha, hb, determinant_ne_zero f a b (by simpa only [hfa, hfb] using hZ),
    hfa, hfb, hmem⟩

end RankTwo

namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)

private def det (a b : Lattice) : ℤ := a.1 * b.2 - a.2 * b.1

private def relativeCoordinates (a b x : Lattice) : Lattice :=
  (det x b / det a b, det a x / det a b)

private theorem relativeCoordinates_combination (a b : Lattice) (h : det a b ≠ 0) (x y : ℤ) :
    relativeCoordinates a b (x • a + y • b) = (x,y) := by
  have h₁ : det (x • a + y • b) b = x * det a b := by
    change (x * a.1 + y * b.1) * b.2 - (x * a.2 + y * b.2) * b.1 = _
    unfold det
    ring
  have h₂ : det a (x • a + y • b) = y * det a b := by
    change a.1 * (x * a.2 + y * b.2) - a.2 * (x * a.1 + y * b.1) = _
    unfold det
    ring
  simp only [relativeCoordinates, h₁, h₂, Int.mul_ediv_cancel _ h]

/-- Compute those rank-two model roots which lie in the strictly positive
integral cone on the ordered pair. -/
private def positiveConeCoefficients (R : Finset Lattice) (a b : Lattice) : Finset Lattice :=
  ((R.filter fun r => let t := relativeCoordinates a b r; r = t.1 • a + t.2 • b).image
    (relativeCoordinates a b)).filter (fun t => 0 < t.1 ∧ 0 < t.2)

private theorem mem_positiveConeCoefficients {R : Finset Lattice} {a b : Lattice} (h : det a b ≠ 0)
    (x y : ℤ) : (x,y) ∈ positiveConeCoefficients R a b ↔
      x • a + y • b ∈ R ∧ 0 < x ∧ 0 < y := by
  classical
  simp only [positiveConeCoefficients, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨t, ⟨ht, he⟩, ht'⟩, hx, hy⟩
    rw [ht'] at he
    exact ⟨he ▸ ht, hx, hy⟩
  · rintro ⟨hR, hx, hy⟩
    refine ⟨⟨x • a + y • b, ⟨hR, ?_⟩, relativeCoordinates_combination a b h x y⟩, hx, hy⟩
    rw [relativeCoordinates_combination a b h x y]

private def coneShape (C : Finset Lattice) : Prop :=
  C = ∅ ∨ C = {(1,1)} ∨ C = {(1,1), (2,1)} ∨
    C = {(1,1), (2,1), (1,2)} ∨ C = {(1,1), (2,1), (3,1), (3,2)}

set_option maxRecDepth 25000 in
set_option maxHeartbeats 5000000 in
/-- In the shorter-first orientation the only cone roots beyond the string
can have second coordinate two. The two cones containing such a root are
the nonabelian string cases of G₂. -/
private theorem positiveCone_shape (k : RankTwoKind) :
    ∀ a ∈ rankTwoCoefficients k, ∀ b ∈ rankTwoCoefficients k,
      det a b ≠ 0 → (k = .A₁A₁ ∨ squaredLength k a ≤ squaredLength k b) →
      coneShape (positiveConeCoefficients (rankTwoCoefficients k) a b) := by
  unfold coneShape
  cases k <;> decide

end RankTwo

private theorem subsingleton_lattices_of_emptyRoots (D : BasedRootDatum.{u}) [IsEmpty D.I]
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    Subsingleton D.X ∧ Subsingleton D.Y := by
  have hrange : Set.range D.datum.coroot = ∅ := by
    ext y
    exact ⟨fun ⟨i, _⟩ => isEmptyElim i, False.elim⟩
  have h : (⊥ : Submodule ℤ D.Y) = ⊤ := by
    simpa only [hrange, Submodule.span_empty] using hcoroot
  have hzero (y : D.Y) : y = 0 := (Submodule.mem_bot ℤ).mp (by rw [h]; exact Submodule.mem_top)
  have hy : Subsingleton D.Y := ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  refine ⟨⟨fun x y => D.datum.toPerfPair.injective (LinearMap.ext fun a => ?_)⟩, hy⟩
  have ha : a = 0 := hy.elim a 0
  rw [ha, map_zero, map_zero]

private theorem subsingleton_points_of_emptyCharacters (D : BasedRootDatum.{u}) [Subsingleton D.X]
    (R : TestAlgebra (RationalField.{u})) :
    Subsingleton (GroupPoints (diagonalTorus (RationalField.{u}) D).val R) := by
  let e := (DiagonalizableGroups.groupAlgebraPointsIso RationalField
    (Multiplicative D.X)).app R
  refine ⟨fun a b => ?_⟩
  have h (f g : Multiplicative D.X →* Rˣ) : f = g := by
    apply MonoidHom.ext
    intro x
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx, map_one, map_one]
  exact (ConcreteCategory.bijective_of_isIso e.hom).1 (h _ _)

/-- The rootless case of the integral relation theorem, where the coroot
hypothesis forces both lattices and the rational group to be trivial. -/
theorem integralRootRelations_of_emptyRoots
    (realize : Specs.RationalRealization.Statement.{u}) (D : BasedRootDatum.{u})
    (hI : IsEmpty D.I) (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    ∃ (A : AdditiveLine (RationalField.{u})) (Q : Realization D A) (z : RootCoordinates Q),
      IsChevalley Q z ∧ OppositeRootRelations Q z ∧
        IndependentRootRelations Q z ∧ FormalBigCellProduct Q z := by
  letI := hI
  obtain ⟨hX, _⟩ := subsingleton_lattices_of_emptyRoots D hcoroot
  letI := hX
  obtain ⟨A, Q, hQ, _⟩ := realize D
  obtain ⟨e⟩ := hQ hI
  have hpoints (R : TestAlgebra (RationalField.{u})) :
      Subsingleton (GroupPoints Q.pinned.pair.G.val R) := by
    letI := subsingleton_points_of_emptyCharacters D R
    let i := ((groupPointsFunctor _).mapIso e).app R
    exact (ConcreteCategory.bijective_of_isIso i.hom).1.subsingleton
  let z : RootCoordinates Q := fun i => isEmptyElim i
  refine ⟨A, Q, z, ?_, fun i => isEmptyElim i, fun i => isEmptyElim i, ?_⟩
  · refine ⟨fun i => (hI.false i.val).elim, ?_⟩
    let L := identityLieStructure Q.pinned.pair.G
    refine ⟨L, ?_⟩
    letI := L.lieRing
    letI := L.lieAlgebra
    haveI : Subsingleton (Lie (RationalField.{u}) Q.pinned.pair.G.val) :=
      ⟨fun a b => Subtype.ext ((hpoints _).elim a.toMul.val b.toMul.val)⟩
    exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, Module.Basis.empty _,
      fun i => isEmptyElim i, fun i => isEmptyElim i.val, fun i => isEmptyElim i,
      fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i,
      fun i => isEmptyElim i, fun i => isEmptyElim i, fun a => isEmptyElim a⟩
  · intro r b n p hn hp
    letI : Finite D.I := D.finiteRoots
    letI := hpoints (CellAlgebra D r)
    let f : D.I ⊕ Fin r → CenteredSeries (CellVariables D r) := fun _ => ⟨0, map_zero _⟩
    exact ⟨f, Subsingleton.elim _ _, fun m i => (f i).val.truncTotal (m + 1),
      fun _ _ => rfl, fun m n i d => integerTruncations (f i).val m n d⟩

section RankOneWord

variable {R : Type u} [CommRing R] {G : Type v} [Group G]

/-- The Gauss formula for a linked pair, when the second parameter is a unit.
The word is the Weyl word of the two root coordinates. -/
theorem oppositeRoot_of_linkedWord_of_isUnit
    (X Y : Multiplicative R →* G) (H : Rˣ →* G)
    (hX : ∀ (s : Rˣ) (a : R), H s * X (.ofAdd a) * (H s)⁻¹ = X (.ofAdd ((s : R)^2 * a)))
    (hY : ∀ (s : Rˣ) (a : R), H s * Y (.ofAdd a) * (H s)⁻¹ = Y (.ofAdd ((↑s⁻¹ : R)^2 * a)))
    (hW :
      let w := fun s : Rˣ => X (.ofAdd (s : R)) * Y (.ofAdd (-(↑s⁻¹ : R))) * X (.ofAdd (s : R))
      ∀ s, w s * (w 1)⁻¹ = H s)
    (x : R) (y c : Rˣ) (hc : (c : R) = 1 + x * (y : R)) :
    X (.ofAdd x) * Y (.ofAdd (y : R)) =
      Y (.ofAdd ((y : R) * (↑c⁻¹ : R))) * H c * X (.ofAdd (x * (↑c⁻¹ : R))) := by
  let X' (a : R) := X (.ofAdd a)
  let Y' (a : R) := Y (.ofAdd a)
  let w (s : Rˣ) := X' (s : R) * Y' (-(↑s⁻¹ : R)) * X' (s : R)
  let n := w 1
  have hXa (a b : R) : X' (a + b) = X' a * X' b := X.map_mul (.ofAdd a) (.ofAdd b)
  have hX0 : X' 0 = 1 := X.map_one
  have hw (s : Rˣ) : w s = H s * n := by
    have hs : w s * n⁻¹ = H s := hW s
    rw [← hs, inv_mul_cancel_right]
  have hconj (s : Rˣ) (a : G) (b : G) :
      H s * (a * b) * (H s)⁻¹ = (H s * a * (H s)⁻¹) * (H s * b * (H s)⁻¹) := by group
  have hn (s : Rˣ) : H s * n * (H s)⁻¹ = H s * H s * n := by
    dsimp only [n, w]
    rw [hconj, hconj]
    rw [show ∀ r, H s * X' r * (H s)⁻¹ = X' ((s : R)^2 * r) from hX s]
    rw [show ∀ r, H s * Y' r * (H s)⁻¹ = Y' ((↑s⁻¹ : R)^2 * r) from hY s]
    simp only [inv_one, Units.val_one, mul_one, mul_neg]
    change w (s ^ 2) = H s * H s * n
    rw [hw, map_pow, pow_two]
  have hn' (s : Rˣ) : n * H s = H s⁻¹ * n := by
    rw [map_inv]
    calc
      n * H s = (H s * H s)⁻¹ * (H s * H s * n) * H s := by group
      _ = (H s * H s)⁻¹ * (H s * n * (H s)⁻¹) * H s := by rw [hn]
      _ = _ := by group
  have hwH (r s : Rˣ) : w r * H s = w (r * s⁻¹) := by
    rw [hw r, hw (r * s⁻¹), map_mul, mul_assoc, hn', mul_assoc]
  have hmove (s : Rˣ) (a : R) : X' a * H s = H s * X' ((↑s⁻¹ : R)^2 * a) := by
    have he := hX s⁻¹ a
    change H s⁻¹ * X' a * (H s⁻¹)⁻¹ = X' ((↑s⁻¹ : R)^2 * a) at he
    rw [map_inv, inv_inv] at he
    rw [← he]
    group
  let r : Rˣ := -(c * y⁻¹)
  let t : Rˣ := -y⁻¹
  have hrt : r * c⁻¹ = t := by
    dsimp [r, t]
    rw [neg_mul, mul_comm c, mul_assoc, mul_inv_cancel, mul_one]
  have hr : (r : R) = -((c : R) * (↑y⁻¹ : R)) := by simp [r]
  have ht : (t : R) = -(↑y⁻¹ : R) := by simp [t]
  have hri : -(↑r⁻¹ : R) = (y : R) * (↑c⁻¹ : R)  := by simp [r]
  have hti : -(↑t⁻¹ : R) = (y : R) := by simp [t]
  have hcy : (c : R) * (↑y⁻¹ : R) + -(↑y⁻¹ : R) = x := by
    rw [hc, add_mul, one_mul, mul_assoc, Units.mul_inv, mul_one]
    ring
  have hlhs : X' x * Y' (y : R) =
      X' ((c : R) * (↑y⁻¹ : R)) * w t * X' (↑y⁻¹ : R) := by
    dsimp only [w]
    rw [ht, hti]
    calc
      X' x * Y' (y : R) =
          (X' ((c : R) * (↑y⁻¹ : R)) * X' (-(↑y⁻¹ : R))) * Y' (y : R) *
            (X' (-(↑y⁻¹ : R)) * X' (↑y⁻¹ : R)) := by
        rw [← hXa, ← hXa, neg_add_cancel, hX0, mul_one, hcy]
      _ = _ := by group
  have hyr : Y' ((y : R) * (↑c⁻¹ : R)) =
      X' ((c : R) * (↑y⁻¹ : R)) * w r * X' ((c : R) * (↑y⁻¹ : R)) := by
    dsimp only [w]
    rw [hr, hri]
    symm
    calc
      _ = X' ((c : R) * (↑y⁻¹ : R) + -((c : R) * (↑y⁻¹ : R))) *
          Y' ((y : R) * (↑c⁻¹ : R)) *
          X' (-((c : R) * (↑y⁻¹ : R)) + (c : R) * (↑y⁻¹ : R)) := by
        rw [hXa, hXa]
        group
      _ = _ := by rw [add_neg_cancel, neg_add_cancel, hX0, one_mul, mul_one]
  have harg :
      (↑c⁻¹ : R)^2 * ((c : R) * (↑y⁻¹ : R)) + x * (↑c⁻¹ : R) = (↑y⁻¹ : R) := by
    have hy' : (↑y⁻¹ : R) + x = (↑y⁻¹ : R) * (c : R) := by
      rw [hc, mul_add, mul_one]
      rw [mul_left_comm, Units.inv_mul, mul_one]
    calc
      _ = (↑c⁻¹ : R) * (↑y⁻¹ : R) + x * (↑c⁻¹ : R) := by
        rw [pow_two, mul_assoc, ← mul_assoc (↑c⁻¹ : R) (c : R), Units.inv_mul, one_mul]
      _ = (↑c⁻¹ : R) * ((↑y⁻¹ : R) + x) := by ring
      _ = (↑y⁻¹ : R) := by rw [hy', mul_left_comm, Units.inv_mul, mul_one]
  change X' x * Y' (y : R) = Y' ((y : R) * (↑c⁻¹ : R)) * H c * X' (x * (↑c⁻¹ : R))
  rw [hlhs, hyr]
  symm
  calc
    _ = X' ((c : R) * (↑y⁻¹ : R)) * (w r * H c) *
        (X' ((↑c⁻¹ : R)^2 * ((c : R) * (↑y⁻¹ : R))) * X' (x * (↑c⁻¹ : R))) := by
      calc
        _ = X' ((c : R) * (↑y⁻¹ : R)) * w r * (X' ((c : R) * (↑y⁻¹ : R)) * H c) *
            X' (x * (↑c⁻¹ : R)) := by group
        _ = _ := by rw [hmove]; group
    _ = _ := by rw [hwH, hrt, ← hXa, harg]

end RankOneWord

section RankOneExtension

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

private theorem mapPoints_injective_of_affine {k : Type u} [Field k] {X : SchemeOver k}
    (hX : IsAffine X.left) {R S : TestAlgebra k} (f : R ⟶ S)
    (hf : Function.Injective f.hom) : Function.Injective (mapPoints (X := X) f) := by
  intro x y hxy
  obtain ⟨B, ⟨e⟩⟩ := AlgebraicGeometry.essImage_algSpec.mpr hX
  let F := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := F.preimage (x ≫ e.inv)
  let b := F.preimage (y ≫ e.inv)
  have hm : a.unop ≫ f = b.unop ≫ f := by
    apply Quiver.Hom.op_inj
    apply F.map_injective
    change (testSpec k).map (f.op ≫ a) = (testSpec k).map (f.op ≫ b)
    rw [Functor.map_comp, Functor.map_comp]
    simpa only [a, b, Functor.FullyFaithful.map_preimage, ← Category.assoc] using
      congrArg (· ≫ e.inv) hxy
  have hab : a.unop = b.unop := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro c
    exact hf (DFunLike.congr_fun (congrArg CommAlgCat.Hom.hom hm) c)
  have hp := congrArg ((testSpec k).map) (Quiver.Hom.unop_inj hab)
  simp only [a, b, Functor.FullyFaithful.map_preimage] at hp
  exact (cancel_mono e.inv).mp hp

section

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q) (i j : D.I)
variable {R S : TestAlgebra (RationalField.{u})}

private def oppositeLeft (R : TestAlgebra (RationalField.{u})) (x y : R) :
    GroupPoints Q.pinned.pair.G.val R :=
  root Q z i R x * root Q z j R y

private def oppositeRight (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ) :
    GroupPoints Q.pinned.pair.G.val R :=
  root Q z j R (y * (↑s⁻¹ : R)) * torus Q (D.datum.coroot i) R s *
    root Q z i R (x * (↑s⁻¹ : R))

private theorem map_oppositeLeft (f : R ⟶ S) (x y : R) :
    mapPoints f (oppositeLeft Q z i j R x y) =
      oppositeLeft Q z i j S (f.hom x) (f.hom y) := by
  let φ := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map f).hom
  change φ (oppositeLeft Q z i j R x y) = _
  rw [oppositeLeft, oppositeLeft, map_mul]
  rw [show φ (root Q z i R x) = _ from map_root Q z f i x,
    show φ (root Q z j R y) = _ from map_root Q z f j y]

private theorem map_oppositeRight (f : R ⟶ S) (x y : R) (s : Rˣ) :
    mapPoints f (oppositeRight Q z i j R x y s) =
      oppositeRight Q z i j S (f.hom x) (f.hom y) (Units.map f.hom.toMonoidHom s) := by
  let φ := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map f).hom
  change φ (oppositeRight Q z i j R x y s) = _
  rw [oppositeRight, oppositeRight, map_mul, map_mul]
  rw [show φ (root Q z j R (y * (↑s⁻¹ : R))) = _ from map_root Q z f j _,
    show φ (root Q z i R (x * (↑s⁻¹ : R))) = _ from map_root Q z f i _,
    show φ (torus Q (D.datum.coroot i) R s) = _ from map_torus Q f _ _,
    map_mul, map_mul]
  rfl

/-- The opposite-root identity on the locus where the second input is a
unit extends to all algebras on which the denominator is a unit. -/
theorem oppositeRoot_of_invertibleSecond
    (h : ∀ (R : TestAlgebra (RationalField.{u})) (x : R) (y s : Rˣ),
      (s : R) = 1 + x * (y : R) →
      oppositeLeft Q z i j R x (y : R) = oppositeRight Q z i j R x (y : R) s)
    (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ) (hs : (s : R) = 1 + x * y) :
    oppositeLeft Q z i j R x y = oppositeRight Q z i j R x y s := by
  let k := RationalField.{u}
  let B := MvPolynomial (Fin 2) k
  let X : B := MvPolynomial.X 0
  let Y : B := MvPolynomial.X 1
  let c : B := 1 + X * Y
  have hc : c ≠ 0 := by
    intro hh
    have he := congrArg (MvPolynomial.eval (fun _ : Fin 2 => (0 : k))) hh
    simp [c, X, Y] at he
  let T := Localization.Away c
  letI : IsDomain T := Localization.Away.isDomain hc
  letI : Algebra k T := ((algebraMap B T).comp (algebraMap k B)).toAlgebra
  letI : @IsScalarTower k B T Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let TK := FractionRing T
  letI : Algebra k TK := ((algebraMap T TK).comp (algebraMap k T)).toAlgebra
  letI : @IsScalarTower k T TK Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let M := CommAlgCat.of k T
  let F := CommAlgCat.of k TK
  let inc : M ⟶ F := CommAlgCat.ofHom (IsScalarTower.toAlgHom k T TK)
  let a : M := algebraMap B T X
  let b : M := algebraMap B T Y
  let t : Mˣ := (IsLocalization.Away.algebraMap_isUnit (S := T) c).unit
  have ht : (t : M) = 1 + a * b := by
    rw [IsUnit.unit_spec]
    simp only [a, b, c, map_add, map_mul, map_one]
  have hinc : Function.Injective inc.hom := IsFractionRing.injective T TK
  have hb : inc.hom b ≠ 0 := by
    have hb : (algebraMap B T Y : T) ≠ 0 := by
      simpa only [Y, map_zero] using
        (IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hc)).ne
          (MvPolynomial.X_ne_zero (R := k) (1 : Fin 2))
    simpa only [b, map_zero] using hinc.ne hb
  have hM : oppositeLeft Q z i j M a b = oppositeRight Q z i j M a b t := by
    apply mapPoints_injective_of_affine Q.pinned.pair.G.property.1 inc hinc
    rw [map_oppositeLeft, map_oppositeRight]
    exact h F (inc.hom a) (Units.mk0 (inc.hom b) hb) (Units.map inc.hom.toMonoidHom t) (by
      change inc.hom (t : M) = _
      rw [ht, map_add, map_mul, map_one]
      rfl)
  let g : B →ₐ[k] R := MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then x else y)
  have hX : g X = x := by
    dsimp only [g, X]
    rw [MvPolynomial.aeval_X, ite_eq_left rfl]
  have hY : g Y = y := by
    dsimp only [g, Y]
    rw [MvPolynomial.aeval_X, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  have hg : g c = (s : R) := by
    dsimp only [c]
    rw [map_add, map_mul, map_one, hX, hY, hs]
  have hu : IsUnit (g c) := by rw [hg]; exact s.isUnit
  let g' : T →ₐ[k] R := IsLocalization.Away.liftAlgHom c hu
  let E : M ⟶ R := CommAlgCat.ofHom g'
  have hE (n : B) : E.hom (algebraMap B T n) = g n := IsLocalization.Away.lift_eq c hu n
  have ha : E.hom a = x := (hE X).trans hX
  have hy : E.hom b = y := (hE Y).trans hY
  have hst : Units.map E.hom.toMonoidHom t = s := by
    apply Units.ext
    change E.hom (↑t : M) = (s : R)
    rw [ht, map_add, map_mul, map_one, ha, hy, hs]
  have H := congrArg (mapPoints E) hM
  rwa [map_oppositeLeft, map_oppositeRight, ha, hy, hst] at H

end

end RankOneExtension

section ReciprocalScaling

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z w : RootCoordinates Q)

/-- Rescaling a linked pair by reciprocal units preserves the marked
opposite-root identity. -/
theorem oppositeRoot_of_reciprocal_rescaling (i j : D.I) (c : RationalField.{u}ˣ)
    (h : ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      oppositeLeft Q z i j R x y = oppositeRight Q z i j R x y s)
    (hp : ∀ (R : TestAlgebra (RationalField.{u})) (a : R),
      root Q w i R a = root Q z i R (algebraMap (RationalField.{u}) R (c : RationalField.{u}) * a))
    (hn : ∀ (R : TestAlgebra (RationalField.{u})) (a : R),
      root Q w j R a = root Q z j R (algebraMap (RationalField.{u}) R (↑c⁻¹ : RationalField.{u}) * a)) :
    ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      oppositeLeft Q w i j R x y = oppositeRight Q w i j R x y s := by
  intro R x y s hs
  let a := algebraMap (RationalField.{u}) R (c : RationalField.{u})
  let b := algebraMap (RationalField.{u}) R (↑c⁻¹ : RationalField.{u})
  have hab : a * b = 1 := by
    change algebraMap (RationalField.{u}) R _ * algebraMap (RationalField.{u}) R _ = _
    rw [← map_mul, Units.mul_inv, map_one]
  have ht : (s : R) = 1 + (a * x) * (b * y) := by rw [mul_mul_mul_comm, hab, one_mul, hs]
  have he := h R (a * x) (b * y) s ht
  simpa only [oppositeLeft, oppositeRight, hp, hn, mul_assoc, a, b] using he

end ReciprocalScaling

section MarkedPointEvaluation

open scoped CategoryTheory.MonObj

open Specs.CharacterDescent (Character Cocharacter)
open Specs.CharacterPairing (characterValue pairing)
open CocharacterDynamics (cocharacterPoint unitPoint)
open RootData.RootGroups (additivePoints)
open private rootPoint_eq rootPoint_zero additivePoints_add characterUnit characterUnitOnPoints
  characterUnit_cocharacter characterValue_eq_unit from LinearAlgebraicGroups.RootData.RootGroups
open private unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

private abbrev pointMap {k : Type u} [Field k] {G H : GroupScheme k} (f : G ⟶ H)
    (R : TestAlgebra k) : GroupPoints G R →* GroupPoints H R :=
  (((groupPointsFunctor k).map f).app R).hom

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private def rootHom (i : D.I) (R : TestAlgebra (RationalField.{u})) :
    Multiplicative R →* GroupPoints Q.pinned.pair.G.val R where
  toFun a := root Q z i R a.toAdd
  map_one' := rootPoint_zero _ _
  map_mul' a b := by
    let f := (z i).val.hom ≫ (Q.pinned.roots (rootIndex Q i)).val.inclusion
    change rootPoint f R (a.toAdd + b.toAdd) = rootPoint f R a.toAdd * rootPoint f R b.toAdd
    simp only [rootPoint_eq, additivePoints_add]
    exact (pointMap f R).map_mul _ _

private abbrev markedCocharacter (v : D.Y) : Cocharacter Q.pinned.pair.T.group :=
  Additive.toMul (Q.datumIso.val.coweightEquiv.symm v)

private abbrev markedCharacter (x : D.X) : Character Q.pinned.pair.T.group :=
  Additive.toMul (Q.datumIso.val.weightEquiv x)

private theorem markedCharacter_root (i : D.I) :
    markedCharacter Q (D.datum.root i) = (rootIndex Q i).val := by
  letI := Q.attached.comm
  change Additive.toMul _ = _
  rw [RootPairing.Equiv.weightEquiv_apply, RootPairing.Hom.root_weightMap_apply]
  change Additive.toMul (Q.attached.datum.rootDatum.root (rootIndex Q i)) = _
  exact congrArg Additive.toMul (Q.attached.datum.root_eq (rootIndex Q i))

private theorem markedPairing (x : D.X) (v : D.Y) :
    pairing Q.pinned.pair.T.group (markedCharacter Q x) (markedCocharacter Q v) =
      D.datum.toLinearMap x v := by
  letI := Q.attached.comm
  rw [← Q.attached.datum.pairing_eq]
  change Q.attached.toBased.datum.toLinearMap (Q.datumIso.val.weightEquiv x)
    (Q.datumIso.val.coweightEquiv.symm v) = _
  rw [Q.datumIso.val.toLinearMap_weightEquiv, LinearEquiv.apply_symm_apply]

private def torusHom (v : D.Y) (R : TestAlgebra (RationalField.{u})) :
    Rˣ →* GroupPoints Q.pinned.pair.G.val R :=
  (pointMap (markedCocharacter Q v ≫ Q.pinned.pair.T.inclusion) R).comp (unitPointHom R)

private theorem torusHom_apply (v : D.Y) (R : TestAlgebra (RationalField.{u})) (s : Rˣ) :
    torusHom Q v R s = torus Q v R s := by
  change unitPointHom R s ≫ _ = _
  rw [unitPointHom_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem torus_conjugates_root (v : D.Y) (i : D.I) (R : TestAlgebra (RationalField.{u}))
    (s : Rˣ) (a : R) :
    torus Q v R s * root Q z i R a * (torus Q v R s)⁻¹ =
      root Q z i R ((↑(s ^ (D.datum.toLinearMap (D.datum.root i) v)) : R) * a) := by
  have h := (z i).property R (cocharacterPoint (markedCocharacter Q v) R s) a
  change torus Q v R s * root Q z i R a * (torus Q v R s)⁻¹ =
    root Q z i R (characterValue (rootIndex Q i).val R
      (cocharacterPoint (markedCocharacter Q v) R s) * a) at h
  rw [← markedCharacter_root Q i,
    (RootData.CharacterPairing.characterPairingComposition _ _ _).2,
    markedPairing] at h
  exact h

private def torusProduct {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (R : TestAlgebra (RationalField.{u})) (t : Fin r → Rˣ) :
    GroupPoints Q.pinned.pair.T.group R :=
  ((List.finRange r).map (fun i => cocharacterPoint (markedCocharacter Q (b i)) R (t i))).prod

private theorem torusProduct_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (R : TestAlgebra (RationalField.{u})) : Function.Injective (torusProduct Q b R) := by
  classical
  letI := Q.attached.comm
  intro t s he
  funext j
  obtain ⟨x, hx⟩ := D.datum.toPerfPair.surjective (b.coord j)
  let χ := markedCharacter Q x
  let f := characterUnitOnPoints χ R
  have hf (a : Fin r → Rˣ) : f (torusProduct Q b R a) = a j := by
    have hpair (i : Fin r) : pairing Q.pinned.pair.T.group χ (markedCocharacter Q (b i)) =
        if i = j then 1 else 0 := by
      rw [markedPairing]
      have hi := congrArg (fun l : D.Y →ₗ[ℤ] ℤ => l (b i)) hx
      simpa [Finsupp.single_apply, eq_comm] using hi
    have hcalc (i : Fin r) : f (cocharacterPoint (markedCocharacter Q (b i)) R (a i)) =
        if i = j then a i else 1 := by
      change characterUnit χ R _ = _
      rw [characterUnit_cocharacter, hpair]
      split_ifs <;> simp
    simp only [torusProduct, map_list_prod, List.map_map, Function.comp_def, hcalc]
    rw [← List.prod_toFinset _ (List.nodup_finRange r)]
    rw [show (List.finRange r).toFinset = Finset.univ from
      Finset.eq_univ_of_forall fun i => List.mem_toFinset.mpr (List.mem_finRange i)]
    simp
  exact (hf t).symm.trans ((congrArg f he).trans (hf s))

private def cocharacterEvaluation (R : TestAlgebra (RationalField.{u})) (s : Rˣ) :
    Multiplicative D.Y →* GroupPoints Q.pinned.pair.T.group R := by
  letI := Q.attached.comm
  exact {
    toFun w := cocharacterPoint (markedCocharacter Q w.toAdd) R s
    map_one' := by
      change unitPoint R s ≫ (markedCocharacter Q 0).hom.hom = _
      have h0 : markedCocharacter Q 0 = 1 :=
        congrArg Additive.toMul Q.datumIso.val.coweightEquiv.symm.map_zero
      rw [h0]
      exact MonObj.comp_one _
    map_mul' x y := by
      have he : markedCocharacter Q (x.toAdd + y.toAdd) =
          markedCocharacter Q x.toAdd * markedCocharacter Q y.toAdd :=
        congrArg Additive.toMul (Q.datumIso.val.coweightEquiv.symm.map_add _ _)
      change unitPoint R s ≫ (markedCocharacter Q (x.toAdd + y.toAdd)).hom.hom = _
      rw [he]
      exact MonObj.comp_mul _ _ _ }

private theorem torus_eq_product {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (v : D.Y) (R : TestAlgebra (RationalField.{u})) (s : Rˣ) :
    torus Q v R s =
      ((List.finRange r).map (fun i => torus Q (b i) R (s ^ b.repr v i))).prod := by
  classical
  let e := cocharacterEvaluation Q R s
  let f : GroupPoints Q.pinned.pair.T.group R →* GroupPoints Q.pinned.pair.G.val R :=
    pointMap Q.pinned.pair.T.inclusion R
  have hb (i : Fin r) : e (Multiplicative.ofAdd (b.repr v i • b i)) =
      cocharacterPoint (markedCocharacter Q (b i)) R (s ^ b.repr v i) := by
    change e ((Multiplicative.ofAdd (b i)) ^ b.repr v i) = _
    let t := (pointMap (markedCocharacter Q (b i)) R).comp (unitPointHom R)
    have ht (s : Rˣ) : t s = cocharacterPoint (markedCocharacter Q (b i)) R s := by
      change unitPointHom R s ≫ _ = _
      rw [unitPointHom_apply]
      rfl
    rw [map_zpow, ← ht, map_zpow, ht]
    rfl
  have hv : e (Multiplicative.ofAdd v) =
      torusProduct Q b R (fun i => s ^ b.repr v i) := by
    let l := List.finRange r
    let f (i : Fin r) := (b.repr v i) • b i
    have hl : l.toFinset = Finset.univ :=
      Finset.eq_univ_of_forall fun i => List.mem_toFinset.mpr (List.mem_finRange i)
    have hv : (l.map f).sum = v := by
      rw [← List.sum_toFinset _ (List.nodup_finRange r), hl]
      exact b.sum_repr v
    have hprod (l' : List (Fin r)) : (l'.map (fun i => Multiplicative.ofAdd (f i))).prod =
        Multiplicative.ofAdd (l'.map f).sum := by
      induction l' with
      | nil => rfl
      | cons i l' ih => simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]; rfl
    have hp : (l.map (fun i => Multiplicative.ofAdd (f i))).prod = Multiplicative.ofAdd v := by
      rw [hprod, hv]
    rw [← hp, map_list_prod, List.map_map]
    simp only [torusProduct, Function.comp_def, f, hb, l]
  change f (e (Multiplicative.ofAdd v)) = _
  rw [hv, torusProduct, map_list_prod, List.map_map]
  rfl

end MarkedPointEvaluation

section LinkedWords

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

/-- The linked rank-one word and marked torus action give the Gauss
factorization for the indicated opposite pair. -/
private theorem oppositeRoot_of_linkedWords (i j : D.I)
    (hij : D.datum.root j = -D.datum.root i)
    (hword : ∀ (R : TestAlgebra (RationalField.{u})),
      let w (s : Rˣ) :=
        root Q z i R (s : R) * root Q z j R (-(↑s⁻¹ : R)) * root Q z i R (s : R)
      ∀ s, w s * (w 1)⁻¹ = torus Q (D.datum.coroot i) R s) :
    ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      oppositeLeft Q z i j R x y = oppositeRight Q z i j R x y s := by
  intro R x y s hs
  apply oppositeRoot_of_invertibleSecond Q z i j ?_ R x y s hs
  intro S a t u hu
  let X := rootHom Q z i S
  let Y := rootHom Q z j S
  let T := torusHom Q (D.datum.coroot i) S
  have ht (s : Sˣ) : T s = torus Q (D.datum.coroot i) S s := torusHom_apply Q _ _ s
  have hp : D.datum.toLinearMap (D.datum.root i) (D.datum.coroot i) = 2 :=
    D.datum.pairing_same i
  have hn : D.datum.toLinearMap (D.datum.root j) (D.datum.coroot i) = -2 := by
    rw [hij, map_neg, LinearMap.neg_apply, hp]
  have hx (s : Sˣ) (b : S) :
      T s * X (.ofAdd b) * (T s)⁻¹ = X (.ofAdd ((s : S)^2 * b)) := by
    change T s * root Q z i S b * (T s)⁻¹ = _
    rw [ht]
    have h := torus_conjugates_root Q z (D.datum.coroot i) i S s b
    rw [hp, zpow_ofNat] at h
    exact h
  have hy (s : Sˣ) (b : S) :
      T s * Y (.ofAdd b) * (T s)⁻¹ = Y (.ofAdd ((↑s⁻¹ : S)^2 * b)) := by
    change T s * root Q z j S b * (T s)⁻¹ = _
    rw [ht]
    have h := torus_conjugates_root Q z (D.datum.coroot i) j S s b
    have hs : s ^ (-(2 : ℤ)) = s⁻¹ ^ (2 : ℕ) := by rw [zpow_neg, zpow_ofNat, inv_pow]
    rw [hn, hs] at h
    exact h
  have hw :
      let w := fun s : Sˣ => X (.ofAdd (s : S)) * Y (.ofAdd (-(↑s⁻¹ : S))) * X (.ofAdd (s : S))
      ∀ s, w s * (w 1)⁻¹ = T s := by
    dsimp only
    intro s
    rw [ht]
    exact hword S s
  have h := oppositeRoot_of_linkedWord_of_isUnit X Y T hx hy hw a t u hu
  rw [ht] at h
  exact h

/-- The linked rank-one words and the marked torus action give the Gauss
factorization on all rational test algebras. -/
theorem oppositeRootRelations_of_linkedWords
    (hword : ∀ (i j : D.I), D.datum.root j = -D.datum.root i →
      ∀ (R : TestAlgebra (RationalField.{u})),
        let w (s : Rˣ) :=
          root Q z i R (s : R) * root Q z j R (-(↑s⁻¹ : R)) * root Q z i R (s : R)
        ∀ s, w s * (w 1)⁻¹ = torus Q (D.datum.coroot i) R s) :
    OppositeRootRelations Q z := by
  intro i j hij
  exact oppositeRoot_of_linkedWords Q z i j hij (hword i j hij)

end LinkedWords

section RankOneTangents

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (TwoVariables liftS liftT liftST)

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private theorem liftST_injective (k : Type u) [Field k] :
    Function.Injective (liftST k) := by
  intro x y h
  exact TrivSqZeroExt.ext (congrArg (fun z : TwoVariables k => z.fst.fst) h)
    (congrArg (fun z : TwoVariables k => z.snd.snd) h)

private theorem liftST_eps_eq_mul (k : Type u) [Field k] :
    liftST k DualNumber.eps = liftS k DualNumber.eps * liftT k DualNumber.eps := by
  have hS : liftS k DualNumber.eps = (⟨DualNumber.eps, 0⟩ : TwoVariables k) := rfl
  have hT : liftT k DualNumber.eps = (⟨0, 1⟩ : TwoVariables k) := by
    apply TrivSqZeroExt.ext
    · exact map_zero (algebraMap k (DualNumber k))
    · exact map_one (algebraMap k (DualNumber k))
  rw [hS, hT]
  apply TrivSqZeroExt.ext
  · change (0 : DualNumber k) = DualNumber.eps * 0
    rw [mul_zero]
  · change (DualNumber.eps : DualNumber k) = DualNumber.eps * 1 + 0 * 0
    rw [mul_one, zero_mul, add_zero]

private theorem dualUnit_val :
    (dualUnit.{u} : DualNumber (RationalField.{u})) = 1 + DualNumber.eps :=
  IsUnit.unit_spec _

/-- Differentiating the rank-one factorization gives the bracket of the
linked root vectors, on the original marked coroot. -/
theorem oppositeRootBracket_of_factorization (i j : D.I) (hij : D.datum.root j = -D.datum.root i)
    (hop : ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
      oppositeLeft Q z i j R x y = oppositeRight Q z i j R x y s)
    (L : IdentityLieStructure Q.pinned.pair.G.val)
    (e f h : Lie (RationalField.{u}) Q.pinned.pair.G.val) :
    IsRootTangent Q z i e → IsRootTangent Q z j f →
    h.toMul.val = torus Q (D.datum.coroot i) (CommAlgCat.of _ (DualNumber (RationalField.{u}))) dualUnit.{u} →
    letI := L.lieRing
    ⁅e, f⁆ = h := by
  intro he hf hh
  let k := RationalField.{u}
  let R₀ := CommAlgCat.of k (DualNumber k)
  let R := CommAlgCat.of k (TwoVariables k)
  let S : R₀ ⟶ R := CommAlgCat.ofHom (liftS k)
  let T : R₀ ⟶ R := CommAlgCat.ofHom (liftT k)
  let ST : R₀ ⟶ R := CommAlgCat.ofHom (liftST k)
  let x : R := S.hom DualNumber.eps
  let y : R := T.hom DualNumber.eps
  let t : Rˣ := Units.map ST.hom.toMonoidHom dualUnit.{u}
  have hx : x * x = 0 := by
    change S.hom DualNumber.eps * S.hom DualNumber.eps = _
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hy : y * y = 0 := by
    change T.hom DualNumber.eps * T.hom DualNumber.eps = _
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have ht : (t : R) = 1 + x * y := by
    change ST.hom (dualUnit.{u} : DualNumber k) = _
    rw [dualUnit_val, map_add, map_one]
    exact congrArg (fun z : R => 1 + z) (liftST_eps_eq_mul k)
  have htinv : (↑t⁻¹ : R) = 1 - x * y := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [ht]
    linear_combination -(y*y) * hx
  have hxt : x * (↑t⁻¹ : R) = x := by
    rw [htinv, mul_sub, mul_one, ← mul_assoc x x y, hx, zero_mul, sub_zero]
  have hyt : y * (↑t⁻¹ : R) = y := by
    rw [htinv, mul_sub, mul_one, mul_left_comm y x y, hy, mul_zero, sub_zero]
  let a := root Q z i R x
  let b := root Q z j R y
  let c := torus Q (D.datum.coroot i) R t
  have hxy : a * b = b * c * a := by
    have hp := hop R x y t ht
    rw [oppositeLeft, oppositeRight, hxt, hyt] at hp
    exact hp
  have hbc : Commute b c := by
    have hpair : D.datum.toLinearMap (D.datum.root j) (D.datum.coroot i) = -(2 : ℤ) := by
      rw [hij, map_neg, LinearMap.neg_apply, D.datum.root_coroot_eq_pairing, D.datum.pairing_same]
    have hc := torus_conjugates_root Q z (D.datum.coroot i) j R t y
    have hfix : (↑(t ^ (-(2 : ℤ))) : R) * y = y := by
      have hp : t ^ (-(2 : ℤ)) = t⁻¹ ^ (2 : ℕ) := by rw [zpow_neg, zpow_ofNat, inv_pow]
      rw [hp, Units.val_pow_eq_pow_val, pow_two, mul_assoc,
        mul_comm (↑t⁻¹ : R) y, hyt, mul_comm (↑t⁻¹ : R) y, hyt]
    rw [hpair, hfix] at hc
    change c * b * c⁻¹ = b at hc
    exact (mul_inv_eq_iff_eq_mul.mp hc).symm
  have hac : a * b * a⁻¹ * b⁻¹ = c := by
    calc
      _ = b * c * b⁻¹ := by rw [hxy]; group
      _ = c := by rw [hbc.eq, mul_inv_cancel_right]
  letI : Group (Points Q.pinned.pair.G.val.X R) :=
    inferInstanceAs (Group (GroupPoints Q.pinned.pair.G.val R))
  have hcomm := L.commutator_law e f
  change mapPoints ST ((L.lieRing.toBracket.bracket e f).toMul.val) = _ at hcomm
  unfold InfinitesimalCommutator.commutator at hcomm
  change mapPoints ST _ =
    (mapPoints S e.toMul.val : GroupPoints Q.pinned.pair.G.val R) *
      (mapPoints T f.toMul.val : GroupPoints Q.pinned.pair.G.val R) *
      (mapPoints S e.toMul.val : GroupPoints Q.pinned.pair.G.val R)⁻¹ *
      (mapPoints T f.toMul.val : GroupPoints Q.pinned.pair.G.val R)⁻¹ at hcomm
  change e.toMul.val = root Q z i R₀ DualNumber.eps at he
  change f.toMul.val = root Q z j R₀ DualNumber.eps at hf
  rw [he, hf, map_root, map_root] at hcomm
  have htor : mapPoints ST h.toMul.val = c := by
    rw [hh, map_torus]
    rfl
  apply Subtype.ext
  apply mapPoints_injective_of_affine Q.pinned.pair.G.property.1 ST (liftST_injective k)
  exact hcomm.trans (hac.trans htor.symm)

end RankOneTangents

section CartanTangents

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (TwoVariables liftS liftT liftST)

private theorem unit_zpow_of_square_zero {R : Type u} [CommRing R]
    (x : R) (hx : x * x = 0) (s : Rˣ) (hs : (s : R) = 1 + x) (n : ℤ) :
    (↑(s ^ n) : R) = 1 + (n : R) * x := by
  let f : Multiplicative ℤ →* Rˣ :=
    { toFun := fun a => Units.mkOfMulEqOne (1 + (a.toAdd : R) * x) (1 - (a.toAdd : R) * x) (by
        linear_combination -((a.toAdd : R) ^ 2) * hx)
      map_one' := by
        apply Units.ext
        change 1 + ((0 : ℤ) : R) * x = (1 : R)
        rw [Int.cast_zero, zero_mul, add_zero]
      map_mul' := fun a b => by
        apply Units.ext
        change 1 + ((a.toAdd + b.toAdd : ℤ) : R) * x =
          (1 + (a.toAdd : R) * x) * (1 + (b.toAdd : R) * x)
        rw [Int.cast_add]
        linear_combination -((a.toAdd : R) * (b.toAdd : R)) * hx }
  have he : f (Multiplicative.ofAdd (1 : ℤ)) = s := by
    apply Units.ext
    change 1 + ((1 : ℤ) : R) * x = (s : R)
    rw [hs, Int.cast_one, one_mul]
  rw [← he, ← map_zpow]
  change 1 + (((Multiplicative.ofAdd (1 : ℤ) ^ n).toAdd : ℤ) : R) * x = _
  have h : ((Multiplicative.ofAdd (1 : ℤ) ^ n).toAdd : ℤ) = n := by
    change n • (1 : ℤ) = n
    exact zsmul_one n
  rw [h]

private theorem scaled_epsilon {k : Type u} [Field k] (r : k) :
    dualNumberScale r DualNumber.eps = algebraMap k (DualNumber k) r * DualNumber.eps := by
  apply TrivSqZeroExt.ext
  · rw [dualNumberScale, TrivSqZeroExt.fst_map]
    change (0 : k) = r * 0
    rw [mul_zero]
  · rw [dualNumberScale, TrivSqZeroExt.snd_map, DualNumber.snd_eps,
      LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    change r * 1 = r * 1 + 0 * 0
    rw [zero_mul, add_zero]

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

/-- The bracket of a marked cocharacter tangent with a root tangent is
given by the original character–cocharacter pairing. -/
theorem cocharacterTangent_bracket_root (i : D.I) (v : D.Y)
    (L : IdentityLieStructure Q.pinned.pair.G.val)
    (h e : Lie (RationalField.{u}) Q.pinned.pair.G.val) :
    IsRootTangent Q z i e →
    h.toMul.val = torus Q v (CommAlgCat.of _ (DualNumber (RationalField.{u}))) dualUnit.{u} →
    L.lieRing.toBracket.bracket h e =
      L.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul
        (D.datum.toLinearMap (D.datum.root i) v : RationalField.{u}) e := by
  intro he hh
  letI := L.lieRing
  let k := RationalField.{u}
  let R₀ := CommAlgCat.of k (DualNumber k)
  let R := CommAlgCat.of k (TwoVariables k)
  let S : R₀ ⟶ R := CommAlgCat.ofHom (liftS k)
  let T : R₀ ⟶ R := CommAlgCat.ofHom (liftT k)
  let ST : R₀ ⟶ R := CommAlgCat.ofHom (liftST k)
  let x : R := S.hom DualNumber.eps
  let y : R := T.hom DualNumber.eps
  let t : Rˣ := Units.map S.hom.toMonoidHom dualUnit.{u}
  let n := D.datum.toLinearMap (D.datum.root i) v
  let en := L.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul
    (n : RationalField.{u}) e
  change L.lieRing.toBracket.bracket h e = en
  have hx : x * x = 0 := by
    change S.hom DualNumber.eps * S.hom DualNumber.eps = _
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have ht : (t : R) = 1 + x := by
    change S.hom (dualUnit.{u} : DualNumber k) = _
    rw [dualUnit_val, map_add, map_one]
  let a := torus Q v R t
  let b := root Q z i R y
  have hbr : a * b * a⁻¹ * b⁻¹ = root Q z i R ((n : R) * x * y) := by
    have ha := torus_conjugates_root Q z v i R t y
    change a * b * a⁻¹ = root Q z i R ((↑(t ^ n) : R) * y) at ha
    rw [ha, unit_zpow_of_square_zero x hx t ht n, add_mul, one_mul, add_comm y]
    have hr := (rootHom Q z i R).map_mul (.ofAdd ((n : R) * x * y)) (.ofAdd y)
    change root Q z i R ((n : R) * x * y + y) = root Q z i R ((n : R) * x * y) * b at hr
    rw [hr, mul_inv_cancel_right]
  have hscaled :
      en.toMul.val = root Q z i R₀ (algebraMap k R₀ (n : k) * DualNumber.eps) := by
    have hsc := congrFun (congrFun L.scalar_law (n : k)) e
    change en = scalePointKernel Q.pinned.pair.G.val (n : k) e at hsc
    have hp := congrArg (fun f : Lie k Q.pinned.pair.G.val => f.toMul.val) hsc
    let sc : R₀ ⟶ R₀ := CommAlgCat.ofHom (dualNumberScale (n : k))
    change en.toMul.val = mapPoints sc e.toMul.val at hp
    rw [hp, he, map_root]
    exact congrArg (root Q z i R₀) (scaled_epsilon (n : k))
  have hst : ST.hom (algebraMap k R₀ (n : k) * DualNumber.eps) = (n : R) * x * y := by
    rw [map_mul, AlgHom.commutes, map_intCast]
    rw [show ST.hom DualNumber.eps = x * y from liftST_eps_eq_mul k, mul_assoc]
  letI : Group (Points Q.pinned.pair.G.val.X R) :=
    inferInstanceAs (Group (GroupPoints Q.pinned.pair.G.val R))
  have hcomm := L.commutator_law h e
  change mapPoints ST (⁅h, e⁆).toMul.val = _ at hcomm
  unfold InfinitesimalCommutator.commutator at hcomm
  change mapPoints ST _ =
    mapPoints S h.toMul.val * mapPoints T e.toMul.val *
      (mapPoints S h.toMul.val)⁻¹ * (mapPoints T e.toMul.val)⁻¹ at hcomm
  rw [hh, he, map_torus, map_root] at hcomm
  have htarget : mapPoints ST en.toMul.val = root Q z i R ((n : R) * x * y) := by
    rw [hscaled, map_root, hst]
  apply Subtype.ext
  apply mapPoints_injective_of_affine Q.pinned.pair.G.property.1 ST (liftST_injective k)
  exact hcomm.trans (hbr.trans htarget.symm)

end CartanTangents

section LinkedCoordinates

open scoped CategoryTheory.MonObj

open Specs.Pinning (RootCoordinate)
open Specs.RootGroups (HasScalarAction IsRootSubgroup rankOneWord)
open Specs.GeometricBorelConjugacy (subgroupOfSubgroup)
open RootData.RootGroups (rootSubgroups)
open private subgroupOf_mutual_iso from LinearAlgebraicGroups.Reductive.GeometricBorelConjugacy
open private rescale rescale_point from LinearAlgebraicGroups.Classification.Pinning

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A)

private theorem markedCharacter_neg (x : D.X) :
    markedCharacter Q (-x) = (markedCharacter Q x)⁻¹ :=
  congrArg Additive.toMul (Q.datumIso.val.weightEquiv.map_neg x)

private theorem markedCocharacter_coroot (i : D.I) :
    letI := Q.attached.comm
    markedCocharacter Q (D.datum.coroot i) =
      Additive.toMul (Q.attached.datum.rootDatum.coroot (rootIndex Q i)) := by
  letI := Q.attached.comm
  let e := Q.datumIso.val
  have h : e.coweightEquiv (Q.attached.toBased.datum.coroot (e.indexEquiv i)) = D.datum.coroot i := by
    change e.toHom.coweightMap (Q.attached.toBased.datum.coroot (e.toHom.indexEquiv i)) = _
    exact (RootPairing.Hom.coroot_coweightMap_apply D.datum Q.attached.toBased.datum
      (e.toHom.indexEquiv i) e.toHom).trans
        (congrArg D.datum.coroot (e.toHom.indexEquiv.symm_apply_apply i))
  exact congrArg (@Additive.toMul (Specs.CharacterDescent.Cocharacter Q.pinned.pair.T.group))
    ((congrArg e.coweightEquiv.symm h).symm.trans (e.coweightEquiv.symm_apply_apply _))

private theorem coordinate_on_pinnedRoot {B : AdditiveLine (RationalField.{u})} (i : D.I)
    (U : ClosedSubgroup Q.pinned.pair.G.val)
    (x : RootCoordinate B Q.pinned.pair.T U (rootIndex Q i).val)
    (hx : IsRootSubgroup Q.pinned.pair.T U (rootIndex Q i).val) :
    ∃ y : RootCoordinate B Q.pinned.pair.T (Q.pinned.roots (rootIndex Q i)).val (rootIndex Q i).val,
      y.val.hom ≫ (Q.pinned.roots (rootIndex Q i)).val.inclusion = x.val.hom ≫ U.inclusion := by
  let P := Q.pinned.pair
  let α := rootIndex Q i
  let V := Q.pinned.roots α
  obtain ⟨W, _, _, _, _, hunique⟩ :=
    (rootSubgroups P.G P.reductive P.T P.split P.maximal).2 α.val α.property |>.2.2
  obtain ⟨e, he⟩ := subgroupOf_mutual_iso (hunique U hx).2 (hunique U hx).1
  obtain ⟨f, hf⟩ := subgroupOf_mutual_iso (hunique V.val V.property).1 (hunique V.val V.property).2
  have hcomp : (x.val ≪≫ e ≪≫ f).hom ≫ V.val.inclusion = x.val.hom ≫ U.inclusion := by
    change (x.val.hom ≫ e.hom ≫ f.hom) ≫ V.val.inclusion = _
    simp only [Category.assoc, hf, he]
  exact ⟨⟨x.val ≪≫ e ≪≫ f, by rw [hcomp]; exact x.property⟩, hcomp⟩

/-- The coroot attached to an actual root of the rational model gives
coordinates of its two root subgroups satisfying the Gauss identity. -/
theorem exists_linkedRootCoordinates (z : RootCoordinates Q) (i j : D.I)
    (hij : D.datum.root j = -D.datum.root i) :
    ∃ w : RootCoordinates Q,
      ∀ (R : TestAlgebra (RationalField.{u})) (x y : R) (s : Rˣ), (s : R) = 1 + x * y →
        oppositeLeft Q w i j R x y = oppositeRight Q w i j R x y s := by
  classical
  letI := Q.attached.comm
  let α := rootIndex Q i
  let β := rootIndex Q j
  have hβ : β.val = α.val⁻¹ := by
    change (rootIndex Q j).val = (rootIndex Q i).val⁻¹
    rw [← markedCharacter_root Q j, ← markedCharacter_root Q i, hij, markedCharacter_neg]
  obtain ⟨C, cochar, _, _, P, N, _, _, _, _, B, p, n, hp, hn, hs, ht, r, hr⟩ :=
    Q.attached.datum.attached α
  let U := subgroupOfSubgroup C.subgroup P.contracting
  let V := subgroupOfSubgroup C.subgroup N.contracting
  let x : RootCoordinate B Q.pinned.pair.T U α.val :=
    ⟨p.root, by
      change HasScalarAction Q.pinned.pair.T α.val (p.root.hom ≫ P.contracting.inclusion ≫ C.subgroup.inclusion)
      exact hs⟩
  let y : RootCoordinate B Q.pinned.pair.T V β.val :=
    ⟨n.root, by
      rw [hβ]
      change HasScalarAction Q.pinned.pair.T α.val⁻¹
        (n.root.hom ≫ N.contracting.inclusion ≫ C.subgroup.inclusion)
      exact ht⟩
  have hn' : IsRootSubgroup Q.pinned.pair.T V β.val := hβ.symm ▸ hn
  obtain ⟨a, ha⟩ := coordinate_on_pinnedRoot Q i U x hp
  obtain ⟨b, hb⟩ := coordinate_on_pinnedRoot Q j V y hn'
  let a' := rescale (A := A) a 1
  let b' := rescale (A := A) b 1
  have hne : i ≠ j := by
    intro he
    have h := congrArg (fun v => D.datum.toLinearMap v (D.datum.coroot i)) (he.symm ▸ hij)
    rw [map_neg, LinearMap.neg_apply] at h
    change D.datum.pairing i i = -D.datum.pairing i i at h
    rw [D.datum.pairing_same] at h
    omega
  let w := Function.update (Function.update z i a') j b'
  refine ⟨w, oppositeRoot_of_linkedWords Q w i j hij ?_⟩
  have hw₁ : w i = a' := by
    dsimp only [w]
    exact (Function.update_of_ne hne b' (Function.update z i a')).trans
      (Function.update_self i a' z)
  have hw₂ : w j = b' := by
    dsimp only [w]
    exact Function.update_self j b' (Function.update z i a')
  intro R
  have h₁ (t : R) :
      root Q w i R t = rootPoint (p.root.hom ≫ P.contracting.inclusion ≫ C.subgroup.inclusion) R t := by
    unfold root
    rw [hw₁, rescale_point, Units.val_one, map_one, one_mul, ha]
    rfl
  have h₂ (t : R) :
      root Q w j R t = rootPoint (n.root.hom ≫ N.contracting.inclusion ≫ C.subgroup.inclusion) R t := by
    unfold root
    rw [hw₂, rescale_point, Units.val_one, map_one, one_mul, hb]
    rfl
  have hc : r.coroot = markedCocharacter Q (D.datum.coroot i) :=
    hr.trans (markedCocharacter_coroot Q i).symm
  dsimp only
  intro s
  simp only [h₁, h₂]
  have h := (r.coroot_word R s).symm
  rw [hc] at h
  exact h

end LinkedCoordinates

section OppositeNormalization

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z w : RootCoordinates Q)

private theorem rootTangent_exists_nonzero (i : D.I) :
    ∃ e : Lie (RationalField.{u}) Q.pinned.pair.G.val, IsRootTangent Q z i e ∧ e ≠ 0 := by
  obtain ⟨f, h, _⟩ := Pinning.coordinateVectors A Q.pinned.pair (rootIndex Q i)
    (Q.pinned.roots (rootIndex Q i)).val (Q.pinned.roots (rootIndex Q i)).property
  exact ⟨(f (z i)).val, h (z i), (f (z i)).property.2⟩

private theorem rootTangent_scaling (i : D.I) (c : RationalField.{u}ˣ)
    (h : ∀ (R : TestAlgebra (RationalField.{u})) (x : R),
      root Q z i R x = root Q w i R (algebraMap (RationalField.{u}) R (c : RationalField.{u}) * x))
    (L : IdentityLieStructure Q.pinned.pair.G.val)
    (e f : Lie (RationalField.{u}) Q.pinned.pair.G.val)
    (he : IsRootTangent Q z i e) (hf : IsRootTangent Q w i f) :
    e = L.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul (c : RationalField.{u}) f := by
  let k := RationalField.{u}
  let R := CommAlgCat.of k (DualNumber k)
  let s := CommAlgCat.ofHom (dualNumberScale (c : k))
  have hsc := congrFun (congrFun L.scalar_law (c : k)) f
  rw [hsc]
  apply Subtype.ext
  change e.toMul.val = mapPoints s f.toMul.val
  rw [he, hf, map_root, h]
  exact congrArg (root Q w i R) (scaled_epsilon (c : k)).symm

private theorem eq_one_of_scaled_bracket {k : Type u} {V : Type u}
    [Field k] [LieRing V] [LieAlgebra k V] (x y h : V) (a b n : k)
    (hx : x ≠ 0) (hn : n ≠ 0) (hw : ⁅h, x⁆ = n • x)
    (hb : ⁅x, y⁆ = h) (he : ⁅a • x, b • y⁆ = h) :
    a * b = 1 := by
  have hh : h ≠ 0 := by
    intro hzero
    rw [hzero, zero_lie, eq_comm, smul_eq_zero] at hw
    exact hw.elim hn hx
  rw [smul_lie, lie_smul, ← mul_smul, hb] at he
  have hdiff : (a * b - 1) • h = 0 := by
    rw [sub_smul, he, one_smul, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hdiff).resolve_right hh)

/-- Opposite vectors with the Chevalley bracket have reciprocal
rescalings relative to the attached rank-one coordinates. -/
theorem oppositeRootRelations_of_Chevalley (hz : IsChevalley Q z) :
    OppositeRootRelations Q z := by
  intro i j hij R x y s hs
  classical
  obtain ⟨L, e, h, _, hpoints, _, _, hop, _⟩ := hz.2
  obtain ⟨w, hw⟩ := exists_linkedRootCoordinates Q z i j hij
  obtain ⟨a, ha, _⟩ := Pinning.coordinateChanges A Q.pinned.pair.T
    (Q.pinned.roots (rootIndex Q i)).val (rootIndex Q i).val (w i) (z i)
  obtain ⟨b, hb, _⟩ := Pinning.coordinateChanges A Q.pinned.pair.T
    (Q.pinned.roots (rootIndex Q j)).val (rootIndex Q j).val (w j) (z j)
  obtain ⟨f, hf, hnf⟩ := rootTangent_exists_nonzero Q w i
  obtain ⟨g, hg, _⟩ := rootTangent_exists_nonzero Q w j
  have hlinked := oppositeRootBracket_of_factorization Q w i j hij hw L f g (h i)
    hf hg (hpoints i).2
  have ha' := rootTangent_scaling Q z w i a ha L (e i) f (hpoints i).1 hf
  have hb' := rootTangent_scaling Q z w j b hb L (e j) g (hpoints j).1 hg
  have he := hop i j hij
  rw [ha', hb'] at he
  have hwt := cocharacterTangent_bracket_root Q w i (D.datum.coroot i) L (h i) f hf (hpoints i).2
  let n : RationalField.{u} := D.datum.toLinearMap (D.datum.root i) (D.datum.coroot i)
  have hn : n ≠ 0 := by
    change (D.datum.pairing i i : RationalField.{u}) ≠ 0
    rw [D.datum.pairing_same]
    intro hzero
    have hq : (2 : ℚ) = 0 := congrArg ULift.down hzero
    exact (by decide : (2 : ℚ) ≠ 0) hq
  have hnf' : f ≠ L.lieRing.toAddCommGroup.toAddGroup.toAddMonoid.toZero.zero := by
    rw [L.group_law]
    exact hnf
  have hab := @eq_one_of_scaled_bracket (RationalField.{u}) _ _ L.lieRing L.lieAlgebra
    f g (h i) (a : RationalField.{u}) (b : RationalField.{u}) n hnf' hn hwt hlinked he
  have hb_inv : b = a⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr (Units.ext (by simpa only [Units.val_mul, Units.val_one, mul_comm] using hab))
  rw [hb_inv] at hb
  exact oppositeRoot_of_reciprocal_rescaling Q w z i j a hw ha hb R x y s hs

end OppositeNormalization

section PolynomialRootActions

open Polynomial

set_option backward.isDefEq.respectTransparency false

private theorem aeval_dualNumber_fst {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (p : Polynomial k) (x y : R) :
    TrivSqZeroExt.fst (Polynomial.aeval (A := DualNumber R) ⟨x, y⟩ p) = Polynomial.aeval x p := by
  let f := (TrivSqZeroExt.fstHom k R R).comp (Polynomial.aeval (A := DualNumber R) ⟨x, y⟩)
  have hf : f = Polynomial.aeval x := by
    apply Polynomial.algHom_ext
    change (TrivSqZeroExt.fstHom k R R) (Polynomial.aeval (A := DualNumber R) ⟨x, y⟩ X) = _
    rw [Polynomial.aeval_X, Polynomial.aeval_X]
    rfl
  change f p = _
  rw [hf]

private theorem aeval_dualNumber_snd {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (p : Polynomial k) (x y : R) :
    TrivSqZeroExt.snd (Polynomial.aeval (A := DualNumber R) ⟨x, y⟩ p) = Polynomial.aeval x p.derivative * y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, TrivSqZeroExt.snd_add, hp, hq, Polynomial.derivative_add, map_add, add_mul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_pow,
      Polynomial.derivative_monomial, Polynomial.aeval_monomial]
    rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
      smul_zero, add_zero]
    change (algebraMap k R c) • (n • ((x ^ n.pred) • y)) =
      algebraMap k R (c * n) * x ^ (n - 1) * y
    simp only [smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast, Nat.pred_eq_sub_one]
    ring

/-- A natural additive family of matrices in characteristic zero has a
nilpotent linear coefficient. Its values on all test algebras are the
finite exponential series of that coefficient. -/
theorem polynomialRootAction_eq_exp_sum
    {k : Type u} [Field k] [CharZero k] {J : Type u} [Fintype J] [DecidableEq J]
    (F : ∀ (R : TestAlgebra k), R → Matrix J J R)
    (hzero : ∀ (R : TestAlgebra k), F R 0 = 1)
    (hadd : ∀ (R : TestAlgebra k) (x y : R), F R (x + y) = F R x * F R y)
    (hmap : ∀ (R S : TestAlgebra k) (f : R →ₐ[k] S) (x : R),
      F S (f x) = f.toRingHom.mapMatrix (F R x)) :
    let E := CommAlgCat.of k (DualNumber k)
    let T : Matrix J J k := fun i j => (F E DualNumber.eps i j).snd
    ∃ m : ℕ, T ^ m = 0 ∧
      ∀ (R : TestAlgebra k) (x : R),
        F R x = ∑ d ∈ Finset.range m,
          (algebraMap k R ((d.factorial : k)⁻¹) * x ^ d) •
            (algebraMap k R).mapMatrix (T ^ d) := by
  classical
  let R₀ := CommAlgCat.of k (Polynomial k)
  let E := CommAlgCat.of k (DualNumber k)
  let P : Matrix J J (Polynomial k) := F R₀ Polynomial.X
  let T : Matrix J J k := fun i j => (F E DualNumber.eps i j).snd
  let Cn (d : ℕ) : Matrix J J k := fun i j => (P i j).coeff d
  change ∃ m : ℕ, T ^ m = 0 ∧
    ∀ (R : TestAlgebra k) (x : R), F R x = ∑ d ∈ Finset.range m,
      (algebraMap k R ((d.factorial : k)⁻¹) * x ^ d) • (algebraMap k R).mapMatrix (T ^ d)
  have heval (R : TestAlgebra k) (x : R) (i j : J) :
      F R x i j = Polynomial.aeval x (P i j) := by
    have h := congrArg (fun M : Matrix J J R => M i j)
      (hmap R₀ R (Polynomial.aeval x) Polynomial.X)
    rw [Polynomial.aeval_X] at h
    exact h
  have hC₀ : Cn 0 = 1 := by
    ext i j
    change (P i j).coeff 0 = _
    rw [Polynomial.coeff_zero_eq_aeval_zero, ← heval (CommAlgCat.of k k) 0, hzero]
  have hC₁ : Cn 1 = T := by
    ext i j
    change (P i j).coeff 1 = (F E DualNumber.eps i j).snd
    rw [heval E DualNumber.eps]
    change _ = TrivSqZeroExt.snd (Polynomial.aeval (A := DualNumber k) ⟨0, 1⟩ (P i j))
    rw [aeval_dualNumber_snd, mul_one, ← Polynomial.coeff_zero_eq_aeval_zero, Polynomial.coeff_derivative]
    simp
  have hdiff (i j : J) : (P i j).derivative = ∑ a, P i a * Polynomial.C (T a j) := by
    let R := CommAlgCat.of k (DualNumber (Polynomial k))
    let a : R := ⟨Polynomial.X, 0⟩
    let b : R := ⟨0, 1⟩
    have hfstₐ (i j : J) : (F R a i j).fst = P i j := by
      rw [heval]
      dsimp only [a]
      rw [aeval_dualNumber_fst, Polynomial.aeval_X_left]
      rfl
    have hsndₐ (i j : J) : (F R a i j).snd = 0 := by
      rw [heval]
      dsimp only [a]
      rw [aeval_dualNumber_snd, mul_zero]
    have hsndᵦ (i j : J) : (F R b i j).snd = Polynomial.C (T i j) := by
      rw [heval]
      dsimp only [b]
      rw [aeval_dualNumber_snd, mul_one]
      rw [show (Polynomial.aeval (0 : Polynomial k)) =
          (Polynomial.CAlgHom : k →ₐ[k] Polynomial k).comp (Polynomial.aeval (0 : k)) from by
        apply Polynomial.algHom_ext
        simp]
      rw [AlgHom.comp_apply, ← Polynomial.coeff_zero_eq_aeval_zero, Polynomial.coeff_derivative]
      simp
      exact congrArg (fun M : Matrix J J k => M i j) hC₁
    have hab (i j : J) : (F R (a + b) i j).snd = (P i j).derivative := by
      have h : a + b = (⟨Polynomial.X, 1⟩ : R) := by
        apply TrivSqZeroExt.ext
        · exact add_zero _
        · exact zero_add _
      rw [h, heval, aeval_dualNumber_snd, mul_one, Polynomial.aeval_X_left]
      rfl
    have h := congrArg (fun M : Matrix J J R => (M i j).snd) (hadd R a b)
    rw [hab, Matrix.mul_apply] at h
    rw [h]
    change (TrivSqZeroExt.sndHom (R := Polynomial k) (M := Polynomial k)) _ = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    change TrivSqZeroExt.snd (F R a i d * F R b d j) = _
    rw [TrivSqZeroExt.snd_mul]
    rw [hfstₐ, hsndₐ, hsndᵦ, smul_zero, add_zero, smul_eq_mul]
  have hrec (d : ℕ) : ((d + 1 : ℕ) : k) • Cn (d + 1) = Cn d * T := by
    ext i j
    have h := congrArg (fun p : Polynomial k => p.coeff d) (hdiff i j)
    simpa only [Polynomial.coeff_derivative, finsetSum_coeff, Polynomial.coeff_mul_C,
      Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Cn, Nat.cast_add, Nat.cast_one,
      mul_comm ((d : k) + 1)] using h
  have hpows (d : ℕ) : T ^ d = (d.factorial : k) • Cn d := by
    induction d with
    | zero => rw [pow_zero, Nat.factorial_zero, Nat.cast_one, one_smul, hC₀]
    | succ d ih =>
      rw [pow_succ, ih, smul_mul_assoc, ← hrec, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_comm]
  have hcoeff (d : ℕ) : Cn d = (d.factorial : k)⁻¹ • T ^ d := by
    rw [hpows, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]
  let m := (Finset.univ.sup (fun ij : J × J => (P ij.1 ij.2).natDegree)) + 1
  have hm (i j : J) : (P i j).natDegree < m :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun ij : J × J => (P ij.1 ij.2).natDegree)
      (Finset.mem_univ (i,j)))
  refine ⟨m, ?_, ?_⟩
  · rw [hpows]
    ext i j
    change (m.factorial : k) * (P i j).coeff m = 0
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hm i j), mul_zero]
  · intro R x
    ext i j
    rw [heval, Polynomial.aeval_eq_sum_range' (hm i j)]
    simp only [Matrix.sum_apply, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro d _
    rw [Algebra.smul_def]
    change algebraMap k R (Cn d i j) * x ^ d = _
    rw [hcoeff]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul]
    ring

end PolynomialRootActions

section RootMatrixExp

open _root_.LinearAlgebraicGroups.Specs (Lie)
open InfinitesimalCommutator (matrixDifferential)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)
  {H : GroupScheme (RationalField.{u})}
  (f : Q.pinned.pair.G.val ⟶ H)
  {J : Type u} [Fintype J] [DecidableEq J]
  (l : (groupPointsFunctor (RationalField.{u})).obj H ≅
    Specs.StandardGroups.generalLinearPoints (RationalField.{u}) J)

/-- The matrix of an actual marked root coordinate is the finite
exponential of its differential in any rational linear representation. -/
theorem rootMatrix_eq_exp_sum (i : D.I)
    (e : Lie (RationalField.{u}) Q.pinned.pair.G.val) (he : IsRootTangent Q z i e) :
    let T := matrixDifferential f l e
    ∃ m : ℕ, T ^ m = 0 ∧
      ∀ (R : TestAlgebra (RationalField.{u})) (x : R),
        ((l.hom.app R).hom ((((groupPointsFunctor (RationalField.{u})).map f).app R).hom
          (root Q z i R x))).val =
          ∑ d ∈ Finset.range m, (algebraMap (RationalField.{u}) R ((d.factorial : RationalField.{u})⁻¹) *
            x ^ d) • (algebraMap (RationalField.{u}) R).mapMatrix (T ^ d) := by
  let k := RationalField.{u}
  letI : CharZero k := ⟨fun m n h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩
  let γ := (groupPointsFunctor k).map f ≫ l.hom
  let F (R : TestAlgebra k) (a : R) : Matrix J J R := ((γ.app R).hom (root Q z i R a)).val
  have hzero (R : TestAlgebra k) : F R 0 = 1 := by
    have h : root Q z i R 0 = 1 := (rootHom Q z i R).map_one
    change ((γ.app R).hom (root Q z i R 0)).val = _
    rw [h, map_one]
    rfl
  have hadd (R : TestAlgebra k) (a b : R) : F R (a + b) = F R a * F R b := by
    have h := (rootHom Q z i R).map_mul (.ofAdd a) (.ofAdd b)
    change root Q z i R (a + b) = root Q z i R a * root Q z i R b at h
    change ((γ.app R).hom (root Q z i R (a + b))).val = _
    rw [h, map_mul]
    rfl
  have hmap (R S : TestAlgebra k) (a : R →ₐ[k] S) (x : R) :
      F S (a x) = a.toRingHom.mapMatrix (F R x) := by
    let b : R ⟶ S := CommAlgCat.ofHom a
    have h := congrArg (fun g => ((g : _ ⟶ _) (root Q z i R x)).val) (γ.naturality b)
    change ((γ.app S).hom (mapPoints b (root Q z i R x))).val =
      a.toRingHom.mapMatrix (F R x) at h
    rw [map_root] at h
    exact h
  have h := polynomialRootAction_eq_exp_sum F hzero hadd hmap
  have ht : (fun i' j' => (F (CommAlgCat.of k (DualNumber k)) DualNumber.eps i' j').snd) =
      matrixDifferential f l e := by
    unfold matrixDifferential
    change (fun i' j' => (F (CommAlgCat.of k (DualNumber k)) DualNumber.eps i' j').snd) =
      (fun i' j' => (((γ.app (CommAlgCat.of k (DualNumber k))).hom e.toMul.val).val i' j').snd)
    rw [he]
  dsimp only at h ⊢
  rw [← ht]
  exact h

end RootMatrixExp

section CommutingRoots

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear from LinearAlgebraicGroups.Affine.LieBracket

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

/-- Root coordinates with commuting tangent vectors commute on every
rational test algebra. -/
theorem rootPoints_commute_of_lieBracket_eq_zero
    (L : IdentityLieStructure Q.pinned.pair.G.val) (i j : D.I)
    (e g : Lie (RationalField.{u}) Q.pinned.pair.G.val)
    (hi : IsRootTangent Q z i e) (hj : IsRootTangent Q z j g)
    (hbr : L.lieRing.toBracket.bracket e g = 0)
    (R : TestAlgebra (RationalField.{u})) (x y : R) :
    Commute (root Q z i R x) (root Q z j R y) := by
  classical
  let k := RationalField.{u}
  obtain ⟨_, H, ⟨l⟩, f, hf⟩ := faithfulLinearization k Q.pinned.pair.G
  letI := Q.pinned.pair.G.property.1
  letI := H.property.1
  let X := matrixDifferential f l e
  let Y := matrixDifferential f l g
  have hd := (identityLieBracketMatrix k Q.pinned.pair.G.val H.val _ f l hf).2 L e g
  rw [hbr] at hd
  change matrixDifferential f l 0 = X * Y - Y * X at hd
  have h0 : matrixDifferential f l 0 = 0 := (matrixDifferentialLinear f l).map_zero
  rw [h0] at hd
  have hXY : Commute X Y := sub_eq_zero.mp hd.symm
  obtain ⟨m, _, hm⟩ := rootMatrix_eq_exp_sum Q z f l i e hi
  obtain ⟨n, _, hn⟩ := rootMatrix_eq_exp_sum Q z f l j g hj
  let γ := (groupPointsFunctor k).map f ≫ l.hom
  let φ := (γ.app R).hom
  have hinj : Function.Injective φ := by
    intro a b hab
    change (l.hom.app R).hom (a ≫ f.hom.hom) = (l.hom.app R).hom (b ≫ f.hom.hom) at hab
    have h := (l.app R).groupIsoToMulEquiv.injective hab
    letI := hf
    letI : Mono f.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono f.hom.hom).mp h
  apply hinj
  change φ (_ * _) = φ (_ * _)
  rw [map_mul, map_mul]
  apply Units.ext
  change Commute (φ (root Q z i R x)).val (φ (root Q z j R y)).val
  have hmi := hm R x
  have hnj := hn R y
  change (φ (root Q z i R x)).val = _ at hmi
  change (φ (root Q z j R y)).val = _ at hnj
  rw [hmi, hnj]
  apply Commute.sum_left
  intro p _
  apply Commute.sum_right
  intro q _
  exact (((hXY.pow_pow p q).map ((algebraMap k R).mapMatrix)).smul_left _).smul_right _

/-- For a nonzero sum outside the roots, the corresponding Chevalley
coordinates have trivial commutator. -/
theorem rootPoints_commute_of_no_root_sum (hz : IsChevalley Q z) (i j : D.I)
    (hne : D.datum.root i + D.datum.root j ≠ 0)
    (hnot : D.datum.root i + D.datum.root j ∉ Set.range D.datum.root)
    (R : TestAlgebra (RationalField.{u})) (x y : R) :
    Commute (root Q z i R x) (root Q z j R y) := by
  obtain ⟨L, e, _, _, he, _, _, _, _, hz₀, _⟩ := hz.2
  have h : L.lieRing.toBracket.bracket (e i) (e j) = 0 := hz₀ i j hne hnot
  exact rootPoints_commute_of_lieBracket_eq_zero Q z L i j (e i) (e j) (he i).1 (he j).1 h R x y

end CommutingRoots

section CentralRootCommutators

open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear from LinearAlgebraicGroups.Affine.LieBracket

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

local instance : CharZero (RationalField.{u}) :=
  ⟨fun _ _ h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private theorem rootMatrix_eq_nilpotentExp
    {H : GroupScheme (RationalField.{u})} (f : Q.pinned.pair.G.val ⟶ H)
    {J : Type u} [Fintype J] [DecidableEq J]
    (l : (groupPointsFunctor (RationalField.{u})).obj H ≅
      Specs.StandardGroups.generalLinearPoints (RationalField.{u}) J)
    (i : D.I) (e : Lie (RationalField.{u}) Q.pinned.pair.G.val) (he : IsRootTangent Q z i e)
    (R : TestAlgebra (RationalField.{u})) (x : R) :
    letI := Specs.RationalRealization.matrixAlgebra R
    let T := x • (algebraMap (RationalField.{u}) R).mapMatrix (matrixDifferential f l e)
    IsNilpotent T ∧
      (((groupPointsFunctor (RationalField.{u})).map f ≫ l.hom).app R (root Q z i R x)).val =
        IsNilpotent.exp T := by
  let k := RationalField.{u}
  letI := Specs.RationalRealization.matrixAlgebra R
  let T := matrixDifferential f l e
  let F := (algebraMap k R).mapMatrix (m := J)
  obtain ⟨m, hm, hex⟩ := rootMatrix_eq_exp_sum Q z f l i e he
  have hn : (x • F T) ^ m = 0 := by
    rw [smul_pow, ← map_pow, hm, map_zero, smul_zero]
  refine ⟨⟨m, hn⟩, ?_⟩
  rw [IsNilpotent.exp_eq_sum hn]
  change _ = ∑ d ∈ Finset.range m, ((d.factorial : ℚ)⁻¹) • (x • F T) ^ d
  erw [hex R x]
  apply Finset.sum_congr rfl
  intro d hd
  rw [smul_pow, ← map_pow]
  rw [show ((d.factorial : ℚ)⁻¹) • (x ^ d • F (T ^ d)) =
      (algebraMap ℚ R ((d.factorial : ℚ)⁻¹) * x ^ d) • F (T ^ d) by
    rw [← IsScalarTower.algebraMap_smul R, smul_smul]]
  rfl

end CentralRootCommutators

section MarkedTorusCoordinates

open scoped CategoryTheory.MonObj
open Specs.CharacterDescent (Character StandardLattice)
open Specs.CharacterPairing (characterValue pairing)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap)
open private splitPresentation charactersOfIso algebraPoint characterValue_monomial
  from LinearAlgebraicGroups.RootData.CharacterPairing
open private torus_point_from_coordinates characterUnit characterUnitOnPoints characterEvaluation
  characterUnit_cocharacter characterValue_eq_unit from LinearAlgebraicGroups.RootData.RootGroups

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem splitTorus_points_ext {k : Type u} [Field k] {T : GroupScheme k}
    (hT : IsSplitTorus T) (R : TestAlgebra k) (a b : GroupPoints T R)
    (h : ∀ χ : Character T, characterUnit χ R a = characterUnit χ R b) : a = b := by
  obtain ⟨r, ⟨i⟩⟩ := splitPresentation hT
  obtain ⟨χ, _, hχ, _, _⟩ := LinearAlgebraicGroups.CharacterDescent.splitCompositionPairing (k := k) r
  obtain ⟨f, hf⟩ := torus_point_from_coordinates r i R a
  obtain ⟨g, hg⟩ := torus_point_from_coordinates r i R b
  have heval (q : MonoidAlgebra k (StandardLattice.{u} r) →ₐ[k] R) (m : StandardLattice.{u} r) :
      characterValue ((charactersOfIso i) (χ m)) R (algebraPoint R q ≫ i.hom.hom.hom) =
        q (MonoidAlgebra.single m 1) := by
    have he : (algebraPoint R q ≫ i.hom.hom.hom) ≫ ((charactersOfIso i) (χ m)).hom.hom =
        algebraPoint R q ≫ (χ m).hom.hom := by
      change (algebraPoint R q ≫ i.hom.hom.hom) ≫ i.inv.hom.hom ≫ (χ m).hom.hom = _
      have hi : i.hom.hom.hom ≫ i.inv.hom.hom = 𝟙 _ := (Grp.forget _).congr_map i.hom_inv_id
      simp only [Category.assoc, ← Category.assoc (f := i.hom.hom.hom), hi, Category.id_comp]
    unfold characterValue
    dsimp only
    rw [he]
    change characterValue (χ m) R (algebraPoint R q) = _
    rw [hχ, characterValue_monomial]
  have hfg : f = g := by
    apply MonoidAlgebra.algHom_ext
    · intro m
      rw [← heval, ← heval, hf, hg, characterValue_eq_unit, characterValue_eq_unit, h]
    · ext
  rw [← hf, ← hg, hfg]

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})} (Q : Realization D A)

private theorem torusProduct_surjective {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (R : TestAlgebra (RationalField.{u})) : Function.Surjective (torusProduct Q b R) := by
  classical
  letI := Q.attached.comm
  let b' : Module.Basis (Fin r) ℤ D.X := b.dualBasis.map D.datum.toPerfPair.symm
  have hpair (i j : Fin r) : pairing Q.pinned.pair.T.group (markedCharacter Q (b' j))
      (markedCocharacter Q (b i)) = if i = j then 1 else 0 := by
    rw [markedPairing]
    change D.datum.toPerfPair (D.datum.toPerfPair.symm (b.dualBasis j)) (b i) = _
    rw [LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply, b.repr_self]
    simp [Finsupp.single_apply, eq_comm]
  intro t
  let s (i : Fin r) := characterUnit (markedCharacter Q (b' i)) R t
  refine ⟨s, splitTorus_points_ext Q.pinned.pair.split R _ _ (fun χ => ?_)⟩
  let ev (p : GroupPoints Q.pinned.pair.T.group R) : D.X →ₗ[ℤ] Additive Rˣ :=
    (characterEvaluation R p).toAdditive.toIntLinearMap.comp Q.datumIso.val.weightEquiv.toLinearMap
  have hev : ev (torusProduct Q b R s) = ev t := by
    apply b'.ext
    intro j
    change characterUnitOnPoints (markedCharacter Q (b' j)) R (torusProduct Q b R s) = s j
    let f := characterUnitOnPoints (markedCharacter Q (b' j)) R
    change f (torusProduct Q b R s) = s j
    have hcalc (i : Fin r) : f (cocharacterPoint (markedCocharacter Q (b i)) R (s i)) =
        if i = j then s i else 1 := by
      change characterUnit (markedCharacter Q (b' j)) R _ = _
      rw [characterUnit_cocharacter, hpair]
      split_ifs <;> simp
    simp only [torusProduct, map_list_prod, List.map_map, Function.comp_def, hcalc]
    rw [← List.prod_toFinset _ (List.nodup_finRange r)]
    rw [show (List.finRange r).toFinset = Finset.univ from
      Finset.eq_univ_of_forall fun i => List.mem_toFinset.mpr (List.mem_finRange i)]
    simp
  obtain ⟨x, hx⟩ := Q.datumIso.val.weightEquiv.surjective (Additive.ofMul χ)
  have hχ : markedCharacter Q x = χ := congrArg Additive.toMul hx
  rw [← hχ]
  exact congrArg (fun f : D.X →ₗ[ℤ] Additive Rˣ => (f x).toMul) hev

end MarkedTorusCoordinates

section IntegralCollection

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

section RootParameters

variable {D : BasedRootDatum.{u}}

private theorem independentRoots_of_ne_of_ne_neg {i j : D.I} (hij : i ≠ j)
    (hneg : D.datum.root j ≠ -D.datum.root i) : IndependentRoots i j := by
  letI := D.reduced
  have h := RootPairing.IsReduced.linearIndependent D.datum hij
    (fun e => hneg (by rw [e, neg_neg]))
  letI := D.freeX
  have hr := Module.Flat.linearIndependent_one_tmul (S := ℚ) h
  have hv : (fun k : Fin 2 => (1 : ℚ) ⊗ₜ[ℤ] ![D.datum.root i, D.datum.root j] k) =
      ![(1 : ℚ) ⊗ₜ[ℤ] D.datum.root i, (1 : ℚ) ⊗ₜ[ℤ] D.datum.root j] := by
    funext k
    fin_cases k <;> rfl
  rw [hv] at hr
  exact hr

private theorem coneRoot_index_injective {i j : D.I} (h : IndependentRoots i j) :
    Function.Injective (ConeRoot.index (i := i) (j := j)) := by
  intro a b he
  have hc := a.root_eq.symm.trans ((congrArg D.datum.root he).trans b.root_eq)
  have hm := congrArg (fun x : D.X => (1 : ℚ) ⊗ₜ[ℤ] x) hc
  change TensorProduct.mk ℤ ℚ D.X 1 _ = TensorProduct.mk ℤ ℚ D.X 1 _ at hm
  simp only [map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ] at hm
  have hd := LinearIndependent.eq_of_pair h hm
  have hl : a.leftDegree = b.leftDegree := Subtype.ext (Nat.cast_injective (R := ℚ) hd.1)
  have hr : a.rightDegree = b.rightDegree := Subtype.ext (Nat.cast_injective (R := ℚ) hd.2)
  cases a; cases b; cases hl; cases hr; cases he
  rfl

private theorem rootCone_enumeration {i j : D.I} (h : IndependentRoots i j) :
    ∃ l : List (ConeRoot i j), Enumerates l Set.univ := by
  classical
  letI : Finite D.I := D.finiteRoots
  letI := Finite.of_injective _ (coneRoot_index_injective h)
  letI := Fintype.ofFinite (ConeRoot i j)
  exact ⟨(Finset.univ : Finset (ConeRoot i j)).toList, Finset.nodup_toList _, by simp⟩

private theorem degreeIdeal_mul_monomial {σ : Type u} {d e : ℕ} {x y : MvPowerSeries σ ℤ}
    (hx : x ∈ degreeIdeal d) (hy : y ∈ degreeIdeal e) (p q : ℕ+) (c : ℤ) :
    (c : MvPowerSeries σ ℤ) * x ^ (p : ℕ) * y ^ (q : ℕ) ∈ degreeIdeal (d + e) := by
  obtain ⟨p', hp⟩ := Nat.exists_eq_succ_of_ne_zero (show (p : ℕ) ≠ 0 from (PNat.pos p).ne')
  obtain ⟨q', hq⟩ := Nat.exists_eq_succ_of_ne_zero (show (q : ℕ) ≠ 0 from (PNat.pos q).ne')
  rw [hp, hq, pow_succ, pow_succ]
  exact mul_mem_degreeIdeal (by simpa only [mul_assoc] using
    (Ideal.mul_mem_left (degreeIdeal d) ((c : MvPowerSeries σ ℤ) * x ^ p') hx))
    (Ideal.mul_mem_left (degreeIdeal e) (y ^ q') hy)

private def intJet (σ : Type u) (m : ℕ) :
    MvPowerSeries σ ℤ →+* JetAlgebra RationalField σ m :=
  (toJet RationalField σ m).hom.toRingHom.comp
    (MvPowerSeries.map (Int.castRingHom RationalField))

private theorem intJet_eq_zero {σ : Type u} (m : ℕ) {f : MvPowerSeries σ ℤ}
    (hf : f ∈ degreeIdeal (m + 1)) : intJet σ m f = 0 := by
  change Ideal.Quotient.mk (degreeIdeal (m + 1))
    (MvPowerSeries.map (Int.castRingHom RationalField) f) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  intro d hd
  rw [MvPowerSeries.coeff_map, hf d hd, map_zero]

private theorem intJet_unit_eq_one {σ : Type u} (m : ℕ) {s : (MvPowerSeries σ ℤ)ˣ}
    (hs : s ∈ congruentUnits (degreeIdeal (m + 1))) :
    Units.map (intJet σ m).toMonoidHom s = 1 := by
  apply Units.ext
  change intJet σ m (s : MvPowerSeries σ ℤ) = 1
  have h := intJet_eq_zero m (mem_congruentUnits.mp hs)
  rwa [map_sub, map_one, sub_eq_zero] at h

private def cellOrder {r : ℕ} (negative positive : List D.I) : List (D.I ⊕ Fin r) :=
  negative.map Sum.inl ++ ((List.finRange r).map Sum.inr ++ positive.map Sum.inl)

private theorem cellOrder_nodup {r : ℕ} {negative positive : List D.I}
    (hneg : Enumerates negative {i | ¬ D.base.IsPos i})
    (hpos : Enumerates positive {i | D.base.IsPos i}) :
    (cellOrder (r := r) negative positive).Nodup := by
  unfold cellOrder
  rw [List.nodup_append', List.nodup_append']
  refine ⟨hneg.1.map Sum.inl_injective,
    ⟨(List.nodup_finRange r).map Sum.inr_injective, hpos.1.map Sum.inl_injective, ?_⟩, ?_⟩
  · simp [List.disjoint_left]
  · intro a ha hb
    rcases List.mem_map.mp ha with ⟨i, hi, rfl⟩
    rcases List.mem_append.mp hb with hb | hb
    · simp at hb
    · obtain ⟨j, hj, eq⟩ := List.mem_map.mp hb
      have hj_eq : j = i := Sum.inl_injective eq
      subst j
      exact (hneg.2 i |>.mp hi) (hpos.2 i |>.mp hj)

private theorem cellOrder_mem {r : ℕ} {negative positive : List D.I}
    (hneg : Enumerates negative {i | ¬ D.base.IsPos i})
    (hpos : Enumerates positive {i | D.base.IsPos i}) (a : D.I ⊕ Fin r) :
    a ∈ cellOrder negative positive := by
  cases a with
  | inr i => simp [cellOrder, List.mem_finRange]
  | inl i =>
    by_cases h : D.base.IsPos i
    · simp [cellOrder, (hpos.2 i).mpr h]
    · simp [cellOrder, (hneg.2 i).mpr h]

end RootParameters

section JetCollection

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)
variable {σ : Type u} (m : ℕ)

private abbrev IntSeries (σ : Type u) := MvPowerSeries σ ℤ
private def onePlusIntSeries (f : IntSeries σ) (hf : f.constantCoeff = 0) : (IntSeries σ)ˣ :=
  (MvPowerSeries.isUnit_iff_constantCoeff.mpr (show IsUnit (1 + f).constantCoeff by
    rw [map_add, map_one, hf, add_zero]
    exact isUnit_one)).unit

private theorem onePlusIntSeries_val (f : IntSeries σ) (hf : f.constantCoeff = 0) :
    (onePlusIntSeries f hf : IntSeries σ) = 1 + f :=
  IsUnit.unit_spec _

private abbrev RationalJet (σ : Type u) (m : ℕ) := JetAlgebra RationalField σ m
private abbrev JetPoints (σ : Type u) (m : ℕ) := GroupPoints Q.pinned.pair.G.val (RationalJet σ m)

private def jetRootHom (i : D.I) : Multiplicative (IntSeries σ) →* JetPoints Q σ m :=
  (rootHom Q z i (RationalJet σ m)).comp (intJet σ m).toAddMonoidHom.toMultiplicative

private def jetTorusHom (v : D.Y) : (IntSeries σ)ˣ →* JetPoints Q σ m :=
  (torusHom Q v (RationalJet σ m)).comp (Units.map (intJet σ m).toMonoidHom)

private abbrev jetRoot (i : D.I) (f : IntSeries σ) :=
  jetRootHom Q z m i (Multiplicative.ofAdd f)

private theorem jetRoot_apply (i : D.I) (x : IntSeries σ) :
    jetRoot Q z m i x = root Q z i (RationalJet σ m) (intJet σ m x) := rfl

private abbrev jetTorus (v : D.Y) (s : (IntSeries σ)ˣ) :=
  jetTorusHom Q m v s

private theorem jetTorus_apply (v : D.Y) (s : (IntSeries σ)ˣ) :
    jetTorus Q m v s = torus Q v (RationalJet σ m) (Units.map (intJet σ m).toMonoidHom s) :=
  torusHom_apply Q v _ _

private theorem jetRoot_add (i : D.I) (x y : IntSeries σ) :
    jetRoot Q z m i (x + y) = jetRoot Q z m i x * jetRoot Q z m i y :=
  (jetRootHom Q z m i).map_mul _ _

private def jetCoordinateGroup {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (d : ℕ) : D.I ⊕ Fin r → Subgroup (JetPoints Q σ m)
  | .inl i => ((degreeIdeal (σ := σ) (K := ℤ) d).toAddSubgroup.toSubgroup).map (jetRootHom Q z m i)
  | .inr i => (congruentUnits (degreeIdeal d)).map (jetTorusHom Q m (b i))

private theorem jetRoot_mem {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y) {d : ℕ}
    (i : D.I) {x : IntSeries σ} (hx : x ∈ degreeIdeal d) :
    jetRoot Q z m i x ∈ jetCoordinateGroup Q z m b d (.inl i) :=
  ⟨Multiplicative.ofAdd x, hx, rfl⟩

private theorem jetTorus_mem {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y) {d : ℕ}
    (i : Fin r) {s : (IntSeries σ)ˣ} (hs : s ∈ congruentUnits (degreeIdeal d)) :
    jetTorus Q m (b i) s ∈ jetCoordinateGroup Q z m b d (.inr i) :=
  Subgroup.mem_map_of_mem _ hs

private theorem jetCoordinateGroup_antitone {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (a : D.I ⊕ Fin r) : Antitone (fun d => jetCoordinateGroup (σ := σ) Q z m b d a) := by
  intro d e h
  cases a with
  | inl i =>
    apply Subgroup.map_mono
    exact fun f hf => degreeIdeal_antitone h hf
  | inr i =>
    apply Subgroup.map_mono
    exact congruentUnits_mono (degreeIdeal_antitone h)

private theorem jetCoordinateGroup_eq_bot {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (a : D.I ⊕ Fin r) : jetCoordinateGroup (σ := σ) Q z m b (m + 1) a = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  cases a with
  | inl i =>
    obtain ⟨x, hx, rfl⟩ := hg
    change jetRoot Q z m i x.toAdd = 1
    have he : intJet σ m x.toAdd = 0 := intJet_eq_zero m hx
    change rootHom Q z i _ (Multiplicative.ofAdd (intJet σ m x.toAdd)) = 1
    rw [he]
    exact map_one _
  | inr i =>
    obtain ⟨s, hs, rfl⟩ := hg
    change torusHom Q (b i) _ (Units.map (intJet σ m).toMonoidHom s) = 1
    rw [intJet_unit_eq_one m hs, map_one]

private theorem commute_mod_of_commutator {G : Type u} [Group G] (H : Subgroup G)
    (N : Subgroup H) [N.Normal] (x y : H)
    (h : (x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹ ∈ N.map H.subtype) :
    Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  let φ := QuotientGroup.mk' N
  have hN : x * y * x⁻¹ * y⁻¹ ∈ N :=
    (Subgroup.mem_map_iff_mem H.subtype_injective).mp h
  have h1 := (QuotientGroup.eq_one_iff (N := N) _).mpr hN
  change φ (_ * _ * _ * _) = 1 at h1
  simp only [map_mul, map_inv] at h1
  change φ x * φ y = φ y * φ x
  calc
    φ x * φ y = (φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹) * (φ y * φ x) := by group
    _ = _ := by rw [h1, one_mul]

private theorem conjugate_mem_subgroupImage {G : Type u} [Group G] (H : Subgroup G)
    (N : Subgroup H) [nN : N.Normal] {a : G} (ha : a ∈ N.map H.subtype) (y : H) :
    (y : G) * a * (y : G)⁻¹ ∈ N.map H.subtype := by
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  exact Subgroup.mem_map_of_mem H.subtype (nN.conj_mem a' ha' y)

private theorem jetTorus_mem_of_deep {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (N : Subgroup (JetPoints Q σ m)) {d : ℕ}
    (hN : ∀ i : Fin r, jetCoordinateGroup Q z m b d (.inr i) ≤ N)
    (v : D.Y) {s : (IntSeries σ)ˣ} (hs : s ∈ congruentUnits (degreeIdeal d)) :
    jetTorus Q m v s ∈ N := by
  rw [jetTorus_apply, torus_eq_product Q b]
  let f := Units.map (intJet σ m).toMonoidHom
  have hterm (i : Fin r) : torus Q (b i) (RationalJet σ m) (f s ^ b.repr v i) ∈ N := by
    rw [← map_zpow f, ← jetTorus_apply Q m]
    exact hN i (jetTorus_mem Q z m b i ((congruentUnits _).zpow_mem hs _))
  apply N.list_prod_mem
  rintro _ hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact hterm i

private theorem jetRoot_commutator_mem {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (hop : OppositeRootRelations Q z) (hind : IndependentRootRelations Q z)
    {d e : ℕ} (hde : 0 < d + e) (N : Subgroup (JetPoints Q σ m))
    (hN : ∀ a, jetCoordinateGroup Q z m b (d + e) a ≤ N)
    (i j : D.I) {x y : IntSeries σ} (hx : x ∈ degreeIdeal d) (hy : y ∈ degreeIdeal e)
    (hconj : ∀ a ∈ N, jetRoot Q z m j y * a * (jetRoot Q z m j y)⁻¹ ∈ N) :
    jetRoot Q z m i x * jetRoot Q z m j y *
      (jetRoot Q z m i x)⁻¹ * (jetRoot Q z m j y)⁻¹ ∈ N := by
  by_cases hij : i = j
  · subst j
    have hc : Commute (jetRoot Q z m i x) (jetRoot Q z m i y) :=
      (Commute.all (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)).map (jetRootHom Q z m i)
    rw [hc.eq]
    simp [mul_assoc]
  by_cases hneg : D.datum.root j = -D.datum.root i
  · let F := intJet σ m
    have hxy := mul_mem_degreeIdeal hx hy
    have hc : (x * y).constantCoeff = 0 :=
      mem_degreeIdeal_one.mp (degreeIdeal_antitone hde hxy)
    let s := onePlusIntSeries (x * y) hc
    have hs : (s : IntSeries σ) = 1 + x * y := onePlusIntSeries_val _ _
    have hsN : s ∈ congruentUnits (degreeIdeal (d + e)) := by
      rw [mem_congruentUnits, hs, add_sub_cancel_left]
      exact hxy
    have hFs : (↑(Units.map F.toMonoidHom s) : RationalJet σ m) = 1 + F x * F y := by
      change F (s : IntSeries σ) = _
      rw [hs, map_add, map_one, map_mul]
    have hdiv (a : IntSeries σ) :
        F (a * (↑s⁻¹ : IntSeries σ)) = F a * (↑(Units.map F.toMonoidHom s)⁻¹ : RationalJet σ m) := by
      rw [map_mul]
      rfl
    have heq := hop i j hneg (RationalJet σ m) (F x) (F y) (Units.map F.toMonoidHom s) hFs
    have hgauss : jetRoot Q z m i x * jetRoot Q z m j y =
        jetRoot Q z m j (y * (↑s⁻¹ : IntSeries σ)) * jetTorus Q m (D.datum.coroot i) s *
          jetRoot Q z m i (x * (↑s⁻¹ : IntSeries σ)) := by
      simp only [jetTorus_apply, jetRoot_apply, ← show F = intJet σ m from rfl, hdiv]
      exact heq
    let dx := x * (↑s⁻¹ : IntSeries σ) - x
    let dy := y * (↑s⁻¹ : IntSeries σ) - y
    have hdx := degreeIdeal_antitone (Nat.le_add_left (d + e) d)
      (div_sub_mem_degreeIdeal hx hy s hs).1
    have hdy := degreeIdeal_antitone (Nat.le_add_left (d + e) e)
      (div_sub_mem_degreeIdeal hx hy s hs).2
    have hx' : x * (↑s⁻¹ : IntSeries σ) = dx + x := (sub_add_cancel _ _).symm
    have hy' : y * (↑s⁻¹ : IntSeries σ) = y + dy := by rw [add_comm, sub_add_cancel]
    rw [hx', hy', jetRoot_add, jetRoot_add] at hgauss
    rw [hgauss]
    have hprod : jetRoot Q z m j dy * jetTorus Q m (D.datum.coroot i) s *
        jetRoot Q z m i dx ∈ N :=
      N.mul_mem (N.mul_mem (hN (.inl j) (jetRoot_mem Q z m b j hdy))
        (jetTorus_mem_of_deep Q z m b N (fun k => hN (.inr k)) (D.datum.coroot i) hsN))
        (hN (.inl i) (jetRoot_mem Q z m b i hdx))
    convert hconj _ hprod using 1
    group
  · have hi := independentRoots_of_ne_of_ne_neg hij hneg
    obtain ⟨l, hl⟩ := rootCone_enumeration hi
    obtain ⟨c, hc⟩ := hind i j hi l hl
    let F := intJet σ m
    have he := hc (RationalJet σ m) (F x) (F y)
    have hprod : jetRoot Q z m i x * jetRoot Q z m j y *
        (jetRoot Q z m i x)⁻¹ * (jetRoot Q z m j y)⁻¹ =
        (l.map (fun a => jetRoot Q z m a.index
          ((c a : IntSeries σ) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod := by
      simpa only [jetRoot_apply, map_mul, map_intCast, map_pow] using he
    rw [hprod]
    apply N.list_prod_mem
    rintro _ ha
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    exact hN (.inl a.index) (jetRoot_mem Q z m b _ <|
      degreeIdeal_mul_monomial hx hy a.leftDegree a.rightDegree (c a))


private theorem jetTorus_root_commutator_mem {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    {d e : ℕ} (N : Subgroup (JetPoints Q σ m))
    (hN : ∀ i, jetCoordinateGroup Q z m b (d + e) (.inl i) ≤ N)
    (v : D.Y) (j : D.I) {s : (IntSeries σ)ˣ} {y : IntSeries σ}
    (hs : s ∈ congruentUnits (degreeIdeal d)) (hy : y ∈ degreeIdeal e) :
    jetTorus Q m v s * jetRoot Q z m j y *
      (jetTorus Q m v s)⁻¹ * (jetRoot Q z m j y)⁻¹ ∈ N := by
  let F := intJet σ m
  let k := D.datum.toLinearMap (D.datum.root j) v
  have hconj : jetTorus Q m v s * jetRoot Q z m j y * (jetTorus Q m v s)⁻¹ =
      jetRoot Q z m j ((↑(s ^ k) : IntSeries σ) * y) := by
    simp only [jetTorus_apply, jetRoot_apply, map_mul]
    have h := torus_conjugates_root Q z v j (RationalJet σ m) (Units.map F.toMonoidHom s) (F y)
    rw [← map_zpow (Units.map F.toMonoidHom)] at h
    exact h
  rw [hconj]
  have heq : jetRoot Q z m j ((↑(s ^ k) : IntSeries σ) * y) * (jetRoot Q z m j y)⁻¹ =
      jetRoot Q z m j (((↑(s ^ k) : IntSeries σ) - 1) * y) := by
    rw [sub_mul, one_mul, sub_eq_add_neg, jetRoot_add]
    rw [← map_inv (jetRootHom Q z m j)]
    rfl
  rw [heq]
  exact hN j (jetRoot_mem Q z m b j (mul_mem_degreeIdeal
    (mem_congruentUnits.mp ((congruentUnits _).zpow_mem hs k)) hy))

open scoped CategoryTheory.MonObj in
private theorem jetTorus_commute (v w : D.Y) (s t : (IntSeries σ)ˣ) :
    Commute (jetTorus Q m v s) (jetTorus Q m w t) := by
  letI := Q.attached.comm
  let R := RationalJet σ m
  letI : IsMulCommutative (GroupPoints Q.pinned.pair.T.group R) :=
    (isCommMonObj_iff_isMulCommutative _).mp Q.attached.comm _
  let f := pointMap Q.pinned.pair.T.inclusion R
  have hc (a b : GroupPoints Q.pinned.pair.T.group R) : Commute a b := by
    exact mul_comm' a b
  rw [jetTorus_apply, jetTorus_apply]
  exact (hc (cocharacterPoint (markedCocharacter Q v) R (Units.map (intJet σ m).toMonoidHom s))
    (cocharacterPoint (markedCocharacter Q w) R (Units.map (intJet σ m).toMonoidHom t))).map f

private theorem jetCoordinateGroup_exchange {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (hop : OppositeRootRelations Q z) (hin : IndependentRootRelations Q z)
    (d : ℕ) :
    let P := jetCoordinateGroup (σ := σ) Q z m b
    let H : Subgroup (JetPoints Q σ m) := ⨆ a, P 1 a
    ∀ (N : Subgroup H) [N.Normal], (∀ a, (P (d + 2) a).subgroupOf H ≤ N) →
      ∀ (a a' : D.I ⊕ Fin r) (x y : H), x.val ∈ P (d + 1) a → y.val ∈ P 1 a' →
        Commute (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  let P := jetCoordinateGroup (σ := σ) Q z m b
  let H : Subgroup (JetPoints Q σ m) := ⨆ a, P 1 a
  change ∀ (N : Subgroup H) [N.Normal], _
  intro N nN hN a a' x y hx hy
  let M := N.map H.subtype
  have hM (a : D.I ⊕ Fin r) : P (d + 2) a ≤ M := by
    have hsub : P (d + 2) a ≤ H :=
      (jetCoordinateGroup_antitone Q z m b a (by omega : 1 ≤ d + 2)).trans (le_iSup _ a)
    rw [← Subgroup.map_subgroupOf_eq_of_le hsub]
    exact Subgroup.map_mono (hN a)
  cases a with
  | inl i =>
    obtain ⟨s, hs, hxs⟩ := hx
    cases a' with
    | inl j =>
      obtain ⟨t, ht, hyt⟩ := hy
      apply commute_mod_of_commutator H N
      change _ * _ * _⁻¹ * _⁻¹ ∈ M
      rw [← hxs, ← hyt]
      have h := jetRoot_commutator_mem Q z m b hop hin (d := d + 1) (e := 1) (by omega)
        M hM i j (x := s.toAdd) (y := t.toAdd) hs ht
      apply h
      intro a ha
      change (jetRootHom Q z m j) t * a * ((jetRootHom Q z m j) t)⁻¹ ∈ M
      rw [hyt]
      exact conjugate_mem_subgroupImage H N ha y
    | inr j =>
      obtain ⟨t, ht, hyt⟩ := hy
      apply Commute.symm
      apply commute_mod_of_commutator H N
      change _ * _ * _⁻¹ * _⁻¹ ∈ M
      rw [← hxs, ← hyt]
      apply jetTorus_root_commutator_mem Q z m b M _ (b j) i ht (y := s.toAdd) hs
      intro k
      simpa only [Nat.add_comm 1] using hM (.inl k)
  | inr i =>
    obtain ⟨s, hs, hxs⟩ := hx
    apply commute_mod_of_commutator H N
    change _ * _ * _⁻¹ * _⁻¹ ∈ M
    cases a' with
    | inl j =>
      obtain ⟨t, ht, hyt⟩ := hy
      rw [← hxs, ← hyt]
      exact jetTorus_root_commutator_mem Q z m b (d := d + 1) (e := 1)
        M (fun k => hM (.inl k)) (b i) j hs (y := t.toAdd) ht
    | inr j =>
      obtain ⟨t, ht, hyt⟩ := hy
      rw [← hxs, ← hyt, (jetTorus_commute Q m (b i) (b j) s t).eq]
      simp [mul_assoc]

end JetCollection

section IntegralCellJets

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)
variable {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y) (negative positive : List D.I) (m : ℕ)

private def integralJetFactor (a : D.I ⊕ Fin r) (p : CenteredSeries (CellVariables D r)) :
    JetPoints Q (CellVariables D r) m :=
  match a with
  | .inl i => jetRoot Q z m i p.val
  | .inr i => jetTorus Q m (b i) (onePlusIntSeries p.val p.property)

private theorem integralJetFactor_mem (a : D.I ⊕ Fin r) (p : CenteredSeries (CellVariables D r)) :
    integralJetFactor Q z b m a p ∈ jetCoordinateGroup Q z m b 1 a := by
  cases a with
  | inl i => exact jetRoot_mem Q z m b i (mem_degreeIdeal_one.mpr p.property)
  | inr i =>
    apply jetTorus_mem Q z m b i
    rw [mem_congruentUnits, onePlusIntSeries_val, add_sub_cancel_left]
    exact mem_degreeIdeal_one.mpr p.property

private theorem exists_integralJetFactor (a : D.I ⊕ Fin r)
    (g : JetPoints Q (CellVariables D r) m) (hg : g ∈ jetCoordinateGroup Q z m b 1 a) :
    ∃ p : CenteredSeries (CellVariables D r), integralJetFactor Q z b m a p = g := by
  cases a with
  | inl i =>
    obtain ⟨x, hx, rfl⟩ := hg
    exact ⟨⟨x.toAdd, mem_degreeIdeal_one.mp hx⟩, rfl⟩
  | inr i =>
    obtain ⟨s, hs, rfl⟩ := hg
    let p : CenteredSeries (CellVariables D r) :=
      ⟨(s : IntSeries (CellVariables D r)) - 1, mem_degreeIdeal_one.mp (mem_congruentUnits.mp hs)⟩
    refine ⟨p, congrArg (jetTorus Q m (b i)) ?_⟩
    apply Units.ext
    rw [onePlusIntSeries_val]
    change 1 + ((s : IntSeries (CellVariables D r)) - 1) = _
    ring

private theorem integralCellPoint_jet
    (p : D.I ⊕ Fin r → CenteredSeries (CellVariables D r)) :
    mapPoints (toJet RationalField (CellVariables D r) m)
      (integralCellPoint Q z b negative positive p) =
      ((cellOrder negative positive).map (fun i => integralJetFactor Q z b m i (p i))).prod := by
  let σ := CellVariables D r
  let F := MvPowerSeries.map (σ := σ) (Int.castRingHom (RationalField.{u}))
  let f := toJet RationalField σ m
  let t (i : Fin r) := onePlusSeries (F (p (.inr i)).val)
    (by
      dsimp only [F]
      rw [MvPowerSeries.constantCoeff_map, (p (.inr i)).property, map_zero])
  have ht (i : Fin r) : Units.map f.hom.toRingHom (t i) =
      Units.map (intJet σ m).toMonoidHom (onePlusIntSeries (p (.inr i)).val (p (.inr i)).property) := by
    apply Units.ext
    change f.hom (↑(t i)) =
      f.hom (F ((onePlusIntSeries (p (.inr i)).val (p (.inr i)).property : (IntSeries σ)ˣ) :
        IntSeries σ))
    simp only [t, onePlusSeries_val, onePlusIntSeries_val, map_add, map_one]
  change mapPoints f (cellPoint Q z b negative positive (CellAlgebra D r)
    (fun i => F (p (.inl i)).val) t) = _
  rw [map_cellPoint Q z, cellPoint]
  simp only [cellOrder, List.map_append, List.map_map, List.prod_append, Function.comp_def,
    integralJetFactor, jetRoot_apply, jetTorus_apply, ht, mul_assoc]
  rfl

private theorem genericCellPoint_eq_integralCellPoint (side : Bool) :
    genericCellPoint Q z b negative positive side =
      integralCellPoint Q z b negative positive
        (fun i => ⟨MvPowerSeries.X (side, i), MvPowerSeries.constantCoeff_X _⟩) := by
  unfold genericCellPoint integralCellPoint
  congr 1 <;> funext i
  · exact (MvPowerSeries.map_X _ _).symm
  · apply Units.ext
    simp only [onePlusSeries_val, MvPowerSeries.map_X]

private theorem collectIntegralCellJet
    (hneg : Enumerates negative {i | ¬ D.base.IsPos i})
    (hpos : Enumerates positive {i | D.base.IsPos i})
    (hop : OppositeRootRelations Q z) (hin : IndependentRootRelations Q z) :
    ∃ p : D.I ⊕ Fin r → CenteredSeries (CellVariables D r),
      let f := toJet RationalField (CellVariables D r) m
      mapPoints f (integralCellPoint Q z b negative positive p) =
        mapPoints f (genericCellPoint Q z b negative positive false *
          genericCellPoint Q z b negative positive true) := by
  let σ := CellVariables D r
  let f := toJet RationalField σ m
  let P := jetCoordinateGroup (σ := σ) Q z m b
  let H : Subgroup (JetPoints Q σ m) := ⨆ a, P 1 a
  let l := cellOrder (D := D) (r := r) negative positive
  let φ := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map f).hom
  let g := genericCellPoint Q z b negative positive false * genericCellPoint Q z b negative positive true
  have hmem (side : Bool) : φ (genericCellPoint Q z b negative positive side) ∈ H := by
    show mapPoints f _ ∈ H
    rw [genericCellPoint_eq_integralCellPoint Q z b, integralCellPoint_jet]
    apply H.list_prod_mem
    rintro _ ha
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ha
    exact Subgroup.mem_iSup_of_mem a (integralJetFactor_mem Q z b m a _)
  have hg : φ g ∈ H := by
    exact (map_mul φ _ _) ▸ H.mul_mem (hmem false) (hmem true)
  obtain ⟨q, hq, he⟩ := orderedProduct_of_truncated_coordinates l
    (cellOrder_nodup hneg hpos) (cellOrder_mem hneg hpos)
    P (jetCoordinateGroup_antitone Q z m b) m (jetCoordinateGroup_eq_bot Q z m b)
    (jetCoordinateGroup_exchange Q z m b hop hin) hg
  choose p hp using fun a => exists_integralJetFactor Q z b m a (q a) (hq a)
  refine ⟨p, ?_⟩
  change mapPoints f _ = φ g
  rw [integralCellPoint_jet]
  simp only [hp]
  exact he

end IntegralCellJets

section CellChart

open scoped CategoryTheory.MonObj

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Specs.OrderedRootProducts (product rootProduct rootCellMap)
open Specs.BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open Specs.AbstractPairing (Root)
open Specs.CharacterPairing (pairing)
open CocharacterDynamics (oppositeCocharacter)
open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes
open private rootPoint_injective from LinearAlgebraicGroups.RootData.OrderedRootProducts
open private opposite_point unitEquiv unitPointHom unitPointHom_apply from LinearAlgebraicGroups.Reductive.CocharacterLimitSubgroups

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

set_option backward.isDefEq.respectTransparency false in
private theorem opposite_markedCocharacter (v : D.Y) :
    oppositeCocharacter (markedCocharacter Q v) = markedCocharacter Q (-v) := by
  letI := Q.attached.comm
  apply Grp.hom_ext
  apply hom_ext_of_points (by
    change IsAffine (Spec (CommRingCat.of
      (MonoidAlgebra (RationalField.{u}) Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance)
  intro R p
  obtain ⟨s, hs⟩ := (unitEquiv R).symm.surjective p
  change unitPointHom R s = p at hs
  rw [unitPointHom_apply] at hs
  rw [← hs]
  change cocharacterPoint (oppositeCocharacter (markedCocharacter Q v)) R s =
    cocharacterPoint (markedCocharacter Q (-v)) R s
  rw [opposite_point]
  let f := (pointMap (markedCocharacter Q v) R).comp (unitPointHom R)
  have hl (s : Rˣ) : f s = cocharacterPoint (markedCocharacter Q v) R s := by
    change unitPointHom R s ≫ _ = _
    rw [unitPointHom_apply]
    rfl
  rw [← hl, map_inv, hl]
  have hneg : markedCocharacter Q (-v) = (markedCocharacter Q v)⁻¹ :=
    congrArg Additive.toMul (Q.datumIso.val.coweightEquiv.symm.map_neg v)
  rw [hneg]
  exact (GrpObj.comp_inv (unitPoint R s) (markedCocharacter Q v).hom.hom).symm

set_option backward.isDefEq.respectTransparency false in
private theorem marked_regular_cocharacter :
    ∃ v : D.Y, IsRegular Q.pinned.pair.T (markedCocharacter Q v) ∧
      ∀ i : D.I, 0 < D.datum.toLinearMap (D.datum.root i) v ↔ D.base.IsPos i := by
  letI : Finite D.I := D.finiteRoots
  let P := Q.pinned.pair
  obtain ⟨c, _, hregular, _, hroots⟩ :=
    (RootData.BorelsAndChambers.borelsThroughT P.G P.reductive P.T P.split P.maximal).1
      P.B P.borel P.containsTorus
  let v := Q.datumIso.val.coweightEquiv (Additive.ofMul c)
  have hv : markedCocharacter Q v = c := by
    change Additive.toMul (Q.datumIso.val.coweightEquiv.symm (Q.datumIso.val.coweightEquiv _)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨v, hv ▸ hregular, ?_⟩
  have hsimple (i : D.I) (hi : i ∈ D.base.support) :
      0 < D.datum.toLinearMap (D.datum.root i) v := by
    have hs := (Q.simpleRoot ⟨i, hi⟩).property.1
    change rootIndex Q i ∈ subgroupRoots P.T P.B at hs
    rw [hroots] at hs
    change 0 < pairing P.T.group (rootIndex Q i).val c at hs
    rwa [← hv, ← markedCharacter_root Q i, markedPairing] at hs
  have hpos (i : D.I) (hi : D.base.IsPos i) :
      0 < D.datum.toLinearMap (D.datum.root i) v := by
    refine hi.induction_on_add hsimple ?_
    intro a b d he ha hb
    rw [he, map_add, LinearMap.add_apply]
    exact add_pos ha (hsimple b hb)
  intro i
  refine ⟨fun hi => ?_, hpos i⟩
  by_contra h
  have hj := hpos (D.datum.reflectionPerm i i) ((RootPairing.Base.IsPos.neg_iff_not D.base i).mpr h)
  rw [D.datum.root_reflectionPerm, D.datum.reflection_apply_self, map_neg, LinearMap.neg_apply] at hj
  omega

private def orderedRootPoint (R : TestAlgebra (RationalField.{u})) (a : D.I → R) :
    (l : List D.I) → Points
      (product (fun α => (Q.pinned.roots α).val.group.X) (l.map (rootIndex Q))) R
  | [] => toUnit _
  | i :: l => lift (rootPoint (z i).val.hom R (a i)) (orderedRootPoint R a l)

private theorem orderedRootPoint_eval (R : TestAlgebra (RationalField.{u})) (a : D.I → R)
    (l : List D.I) :
    orderedRootPoint Q z R a l ≫ rootProduct Q.pinned.roots (l.map (rootIndex Q)) =
      (l.map (fun i => root Q z i R (a i))).prod := by
  induction l with
  | nil => exact MonObj.comp_one _
  | cons i l ih =>
    change _ ≫ rootProduct Q.pinned.roots (rootIndex Q i :: l.map (rootIndex Q)) = _
    rw [orderedRootPoint, rootProduct, MonObj.comp_mul]
    simp only [← Category.assoc, lift_fst, lift_snd, ih, List.map_cons, List.prod_cons]
    rfl

private theorem orderedRootPoint_eq (R : TestAlgebra (RationalField.{u})) (a b : D.I → R)
    (l : List D.I) (h : orderedRootPoint Q z R a l = orderedRootPoint Q z R b l) :
    ∀ i ∈ l, a i = b i := by
  induction l with
  | nil => simp
  | cons j l ih =>
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · have hh := congrArg (fun p => p ≫ fst _ _) h
      simp only [orderedRootPoint, lift_fst] at hh
      exact rootPoint_injective (z i).val R hh
    · have hh := congrArg (fun p => p ≫ snd _ _) h
      simp only [orderedRootPoint, lift_snd] at hh
      exact ih hh i hi

set_option backward.isDefEq.respectTransparency false in
private theorem markedCell_isOpenImmersion (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) :
    IsOpenImmersion (rootCellMap Q.pinned.pair.T Q.pinned.roots
      (negative.map (rootIndex Q)) (positive.map (rootIndex Q))).left := by
  classical
  obtain ⟨v, hreg, hsign⟩ := marked_regular_cocharacter Q
  let P := Q.pinned.pair
  let c := markedCocharacter Q v
  let e := Q.datumIso.val.indexEquiv
  have hpos (i : D.I) : e i ∈ positiveRoots P.T c ↔ D.base.IsPos i := by
    change 0 < pairing P.T.group (rootIndex Q i).val c ↔ _
    rw [← markedCharacter_root Q i, markedPairing]
    exact hsign i
  have hneg (i : D.I) : e i ∈ positiveRoots P.T (oppositeCocharacter c) ↔ ¬ D.base.IsPos i := by
    change 0 < pairing P.T.group (rootIndex Q i).val (oppositeCocharacter (markedCocharacter Q v)) ↔ _
    rw [opposite_markedCocharacter, ← markedCharacter_root Q i, markedPairing, LinearMap.map_neg]
    have he : D.datum.toLinearMap (D.datum.root i) v ≠ 0 := by
      have h := hreg (e i)
      change pairing P.T.group (rootIndex Q i).val c ≠ 0 at h
      rwa [← markedCharacter_root Q i, markedPairing] at h
    rw [← hsign]
    omega
  have hn' : Enumerates (negative.map e) (positiveRoots P.T (oppositeCocharacter c)) := by
    refine ⟨hn.1.map e.injective, ?_⟩
    intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    simpa only [List.mem_map, e.injective.eq_iff, exists_eq_right, hneg, Set.mem_ofPred_eq] using hn.2 i
  have hp' : Enumerates (positive.map e) (positiveRoots P.T c) := by
    refine ⟨hp.1.map e.injective, ?_⟩
    intro α
    obtain ⟨i, rfl⟩ := e.surjective α
    simpa only [List.mem_map, e.injective.eq_iff, exists_eq_right, hpos, Set.mem_ofPred_eq] using hp.2 i
  let f := rootCellMap P.T Q.pinned.roots (negative.map e) (positive.map e)
  exact RootData.OrderedRootProducts.regularRootCell P.G P.reductive P.T P.split P.maximal c hreg
      Q.pinned.roots _ _ hn' hp'

set_option backward.isDefEq.respectTransparency false in
private theorem cellPoint_injective {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i}) (R : TestAlgebra (RationalField.{u})) :
    Function.Injective (fun a : (D.I → R) × (Fin r → Rˣ) =>
      cellPoint Q z b negative positive R a.1 a.2) := by
  let P := Q.pinned.pair
  let e := Q.datumIso.val.indexEquiv
  let f := rootCellMap P.T Q.pinned.roots (negative.map e) (positive.map e)
  haveI : IsOpenImmersion f.left := markedCell_isOpenImmersion Q negative positive hn hp
  haveI : Mono f := Over.mono_of_mono_left f
  let p (a : (D.I → R) × (Fin r → Rˣ)) :=
    lift (orderedRootPoint Q z R a.1 negative)
      (lift (torusProduct Q b R a.2) (orderedRootPoint Q z R a.1 positive))
  have hf (a : (D.I → R) × (Fin r → Rˣ)) :
      p a ≫ f = cellPoint Q z b negative positive R a.1 a.2 := by
    have he : torusProduct Q b R a.2 ≫ P.T.inclusion.hom.hom =
        ((List.finRange r).map (fun i => torus Q (b i) R (a.2 i))).prod := by
      let g := pointMap P.T.inclusion R
      change g _ = _
      simp only [torusProduct, map_list_prod, List.map_map]
      rfl
    simp only [p, f, rootCellMap, MonObj.comp_mul, ← Category.assoc, e, P,
      lift_fst, lift_snd, orderedRootPoint_eval, he, cellPoint, mul_assoc]
  intro a a' h
  have hab : p a = p a' := (cancel_mono f).mp ((hf a).trans (h.trans (hf a').symm))
  have hh := congrArg (fun x => x ≫ snd _ _) hab
  simp only [p, lift_snd] at hh
  have ht := congrArg (fun x => x ≫ fst _ _) hh
  have hleft := congrArg (fun x => x ≫ fst _ _) hab
  have hright := congrArg (fun x => x ≫ snd _ _) hh
  simp only [lift_fst] at ht
  simp only [p, lift_fst] at hleft
  simp only [lift_snd] at hright
  refine Prod.ext ?_ (torusProduct_injective Q b R ht)
  funext i
  by_cases hi : D.base.IsPos i
  · exact orderedRootPoint_eq Q z R a.1 a'.1 positive hright i ((hp.2 i).mpr hi)
  · exact orderedRootPoint_eq Q z R a.1 a'.1 negative hleft i ((hn.2 i).mpr hi)

/-- Integral collection on all finite jets gives integral formal multiplication
in the marked big cell. -/
theorem formalBigCellProduct_of_rootRelations
    (hop : OppositeRootRelations Q z) (hin : IndependentRootRelations Q z) :
    FormalBigCellProduct Q z :=
  formalBigCellProduct_of_jetCollection Q z
    (fun r b n p hn hp m => cellPoint_injective Q z b n p hn hp (JetAlgebra RationalField (CellVariables D r) m))
    (fun _r b n p hn hp m => collectIntegralCellJet Q z b n p m hn hp hop hin)

open private rootPoint_surjective from LinearAlgebraicGroups.RootData.OrderedRootProducts

private theorem orderedRootPoint_ext (R : TestAlgebra (RationalField.{u})) (a b : D.I → R)
    (l : List D.I) (h : ∀ i ∈ l, a i = b i) :
    orderedRootPoint Q z R a l = orderedRootPoint Q z R b l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    dsimp only [orderedRootPoint]
    rw [h j List.mem_cons_self, ih (fun i hi => h i (List.mem_cons_of_mem _ hi))]

private theorem orderedRootPoint_surjective (R : TestAlgebra (RationalField.{u})) (l : List D.I)
    (hl : l.Nodup) : Function.Surjective (fun a : D.I → R => orderedRootPoint Q z R a l) := by
  classical
  induction l with
  | nil => exact fun p => ⟨0, toUnit_unique _ _⟩
  | cons j l ih =>
    intro p
    obtain ⟨a, ha⟩ := rootPoint_surjective (z j).val R (p ≫ fst _ _)
    obtain ⟨b, hb⟩ := ih hl.of_cons (p ≫ snd _ _)
    refine ⟨Function.update b j a, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [orderedRootPoint, lift_fst, Function.update_self] using ha
    · simp only [orderedRootPoint, lift_snd]
      rw [← hb]
      apply orderedRootPoint_ext
      intro i hi
      have hne : i ≠ j := fun he => (List.nodup_cons.mp hl).1 (by rwa [← he])
      exact Function.update_of_ne hne a b

private theorem cellPoint_identity {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I) (R : TestAlgebra (RationalField.{u})) :
    cellPoint Q z b negative positive R 0 1 = 1 := by
  have hr (i : D.I) : root Q z i R 0 = 1 := (rootHom Q z i R).map_one
  have ht (i : Fin r) : torus Q (b i) R 1 = 1 := by
    rw [←torusHom_apply, map_one]
  simp [cellPoint, hr, ht]

private theorem dualReduction_surjective {k : Type u} [Field k] :
    Function.Surjective (((testSpec k).map (dualReduction k).op).left) := by
  let f := (TrivSqZeroExt.fstHom k k k).toRingHom
  have hmap : Function.Surjective f := fun a => ⟨⟨a, 0⟩, rfl⟩
  change Function.Surjective (PrimeSpectrum.comap f)
  rw [← Set.range_eq_univ, range_comap_of_surjective _ f hmap,
    PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  change IsNilpotent x
  have h0 : x.fst = 0 := hx
  refine ⟨2, TrivSqZeroExt.ext ?_ ?_⟩ <;>
    simp [pow_two, TrivSqZeroExt.fst_mul, DualNumber.snd_mul, h0]

set_option backward.isDefEq.respectTransparency false in
private theorem cellPoint_covers_tangents {r : ℕ} (b : Module.Basis (Fin r) ℤ D.Y)
    (negative positive : List D.I)
    (hn : Enumerates negative {i | ¬ D.base.IsPos i})
    (hp : Enumerates positive {i | D.base.IsPos i})
    (p : Lie (RationalField.{u}) Q.pinned.pair.G.val) :
    let R := CommAlgCat.of (RationalField.{u}) (DualNumber (RationalField.{u}))
    ∃ (a : D.I → R) (s : Fin r → Rˣ), p.toMul.val = cellPoint Q z b negative positive R a s := by
  intro R
  classical
  let k := RationalField.{u}
  let P := Q.pinned.pair
  let f := rootCellMap P.T Q.pinned.roots (negative.map (rootIndex Q)) (positive.map (rootIndex Q))
  haveI : IsOpenImmersion f.left := markedCell_isOpenImmersion Q negative positive hn hp
  let q (S : TestAlgebra k) (a : D.I → S) (s : Fin r → Sˣ) :=
    lift (orderedRootPoint Q z S a negative)
      (lift (torusProduct Q b S s) (orderedRootPoint Q z S a positive))
  have hq (S : TestAlgebra k) (a : D.I → S) (s : Fin r → Sˣ) :
      q S a s ≫ f = cellPoint Q z b negative positive S a s := by
    have ht : torusProduct Q b S s ≫ P.T.inclusion.hom.hom =
        ((List.finRange r).map (fun j => torus Q (b j) S (s j))).prod := by
      let g := pointMap P.T.inclusion S
      change g _ = _
      simp only [torusProduct, map_list_prod, List.map_map]
      rfl
    simp only [q, f, rootCellMap, MonObj.comp_mul, ← Category.assoc, P,
      lift_fst, lift_snd, orderedRootPoint_eval, ht, cellPoint, mul_assoc]
  let S := CommAlgCat.of k k
  have hbase : q S 0 1 ≫ f = 1 := (hq S _ _).trans (cellPoint_identity Q z b _ _ S)
  have hsub : Set.range p.toMul.val.left ⊆ Set.range f.left := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := (dualReduction_surjective (k := k)) j
    have h₁ := congrArg Over.Hom.left p.toMul.property
    have e := congrArg Over.Hom.left hbase
    have h := h₁.trans e.symm
    refine ⟨(q S 0 1).left i, ?_⟩
    exact (congrArg (fun a : _ ⟶ P.G.val.X.left => a i) h).symm
  let g : ((testSpec k).obj (op R)) ⟶ _ :=
    Over.homMk (IsOpenImmersion.lift f.left p.toMul.val.left hsub) (by
      rw [← Over.w f, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w p.toMul.val]
      rfl)
  have hg : g ≫ f = p.toMul.val := Over.OverMorphism.ext (IsOpenImmersion.lift_fac ..)
  obtain ⟨an, han⟩ := orderedRootPoint_surjective Q z R negative hn.1 (g ≫ fst _ _)
  obtain ⟨ap, hap⟩ := orderedRootPoint_surjective Q z R positive hp.1 (g ≫ snd _ _ ≫ snd _ _)
  obtain ⟨s, hs⟩ := torusProduct_surjective Q b R (g ≫ snd _ _ ≫ fst _ _)
  let a (i : D.I) := if D.base.IsPos i then ap i else an i
  have ha : q R a s = g := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [q, lift_fst]
      calc
        _ = orderedRootPoint Q z R an negative := orderedRootPoint_ext Q z R a an negative
          (fun i hi => if_neg ((hn.2 i).mp hi))
        _ = _ := han
    · simp only [q, lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        exact hs
      · rw [lift_snd, Category.assoc]
        calc
          _ = orderedRootPoint Q z R ap positive := orderedRootPoint_ext Q z R a ap positive
            (fun i hi => if_pos ((hp.2 i).mp hi))
          _ = _ := hap
  exact ⟨a, s, hg.symm.trans ((congrArg (· ≫ f) ha).symm.trans (hq R a s))⟩

end CellChart

end IntegralCollection

section NormalizedSerreRoots

open Specs.RationalRealization (CartanIdentification ComplexCartan SerreStructure SerreBaseChange
  rationalWeightSpace generator)
open LieAlgebrasAndRepresentations
  (IsMaximalToral IsSemisimple rootSet rootSpace killingCoroot mem_rootSpace
    finrank_rootSpace_eq_one chevalley_basis rootForm_self_ne_zero killingCoroot_pairing)
open private cartan_toral cartan_centralizer self_centralizing_maximal from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.MaximalTori

private abbrev oppositeIndex (D : BasedRootDatum.{u}) (i : D.I) : D.I :=
  D.datum.reflectionPerm i i

private theorem root_oppositeIndex (D : BasedRootDatum.{u}) (i : D.I) :
    D.datum.root (oppositeIndex D i) = -D.datum.root i := by
  rw [oppositeIndex, D.datum.root_reflectionPerm, D.datum.reflection_apply_self]

private abbrev datumCartan (D : BasedRootDatum.{u}) := RootData.integralCartan D.datum D.base

private def cartanCharacter (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) : D.X →+ Module.Dual ℂ C.cartan where
  toFun x := C.cartanBasis.constr ℂ (fun i => (D.datum.toLinearMap x (D.datum.coroot i) : ℂ))
  map_zero' := by
    apply C.cartanBasis.ext
    intro i
    rw [Module.Basis.constr_basis]
    simp
  map_add' x y := by
    apply C.cartanBasis.ext
    intro i
    simp only [Module.Basis.constr_basis, LinearMap.add_apply, map_add, Int.cast_add]

private theorem cartanCharacter_apply (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) (x : D.X) (i : D.base.support) :
    cartanCharacter D C x (C.cartanBasis i) = D.datum.toLinearMap x (D.datum.coroot i) :=
  C.cartanBasis.constr_basis ℂ _ i

private theorem cartanCharacter_injective (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D)
    (h : Function.Injective (fun x : D.X => fun i : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot i))) :
    Function.Injective (cartanCharacter D C) := by
  intro x y he
  apply h
  funext i
  apply Int.cast_injective (α := ℂ)
  rw [← cartanCharacter_apply D C x i, he, cartanCharacter_apply]

private theorem rootSet_cartanCharacter (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) (x : D.X)
    (hi : Function.Injective (cartanCharacter D C)) :
    cartanCharacter D C x ∈ rootSet C.cartan ↔ x ∈ Set.range D.datum.root := by
  change _ ∈ _root_.Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value C.cartan ↔ _
  rw [← C.roots_eq]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, hi hj⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

private theorem cartanCharacter_simple (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) (i : D.base.support) :
    (C.simpleIndex i).val = cartanCharacter D C (D.datum.root i) := C.simple_eq i

private theorem complexWeight_of_rootSpace (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) (j : D.I) {x : LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)}
    (hx : x ∈ rootSpace C.cartan (cartanCharacter D C (D.datum.root j))) (i : D.base.support) :
    ⁅generator ℂ (datumCartan D) (.H i), x⁆ = (D.datum.pairing j i : ℂ) • x := by
  have h := (mem_rootSpace C.cartan _ _).mp hx (C.cartanBasis i)
  rw [C.cartanBasis_eq, cartanCharacter_apply] at h
  exact h

private theorem scalar_multiple_of_rootSpace (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (C : CartanIdentification D) (hss : IsSemisimple ℂ (LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)))
    (hH : IsMaximalToral C.cartan) (α : rootSet C.cartan)
    {x y : LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)} (hx : x ∈ rootSpace C.cartan α.val)
    (hy : y ∈ rootSpace C.cartan α.val) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ c : ℂˣ, y = (c : ℂ) • x := by
  letI := C.finite
  have hspan : ℂ ∙ x = rootSpace C.cartan α.val := by
    apply Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx))
    rw [finrank_rootSpace_eq_one hss C.cartan hH α.val α.property,
      finrank_span_singleton hx0]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan.symm ▸ hy)
  have hc0 : c ≠ 0 := by rintro rfl; simp_all
  exact ⟨Units.mk0 c hc0, hc.symm⟩

private def rootScaling (D : BasedRootDatum.{u}) (c : D.base.support → ℂˣ) :
    D.datum.rootSpan ℤ →ₗ[ℤ] Additive ℂˣ := D.base.toWeightBasisInt.constr ℤ (Additive.ofMul ∘ c)

private theorem rootScaling_apply_simple (D : BasedRootDatum.{u}) (c : D.base.support → ℂˣ)
    (i : D.base.support) :
    (rootScaling D c (D.datum.rootSpanMem ℤ i)).toMul = c i := by
  rw [show D.datum.rootSpanMem ℤ i = D.base.toWeightBasisInt i from
    Subtype.ext (D.base.coe_toWeightBasisInt_apply i).symm, rootScaling, Module.Basis.constr_basis]
  rfl

private theorem rootScaling_mul (D : BasedRootDatum.{u}) (c : D.base.support → ℂˣ)
    (i j k : D.I) (h : D.datum.root i + D.datum.root j = D.datum.root k) :
    (rootScaling D c (D.datum.rootSpanMem ℤ i)).toMul *
      (rootScaling D c (D.datum.rootSpanMem ℤ j)).toMul =
    (rootScaling D c (D.datum.rootSpanMem ℤ k)).toMul := by
  change (rootScaling D c (D.datum.rootSpanMem ℤ i) +
    rootScaling D c (D.datum.rootSpanMem ℤ j)).toMul = _
  rw [← map_add]
  exact congrArg (fun r => (rootScaling D c r).toMul) (Subtype.ext h)

private theorem rootScaling_opp (D : BasedRootDatum.{u}) (c : D.base.support → ℂˣ) (i : D.I) :
    (rootScaling D c (D.datum.rootSpanMem ℤ i)).toMul *
      (rootScaling D c (D.datum.rootSpanMem ℤ (oppositeIndex D i))).toMul = 1 := by
  change (rootScaling D c (D.datum.rootSpanMem ℤ i) +
    rootScaling D c (D.datum.rootSpanMem ℤ (oppositeIndex D i))).toMul = _
  rw [← map_add, show D.datum.rootSpanMem ℤ i + D.datum.rootSpanMem ℤ (oppositeIndex D i) = 0 from
    Subtype.ext (by change D.datum.root i + D.datum.root (oppositeIndex D i) = 0;
                    rw [root_oppositeIndex, add_neg_cancel]), map_zero]
  rfl

private theorem normalizedComplexSerreRoots (D : BasedRootDatum.{u})
    [DecidableEq D.base.support] (C : CartanIdentification D)
    (hsep : Function.Injective (fun x : D.X => fun i : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot i)))
    (hss : IsSemisimple ℂ (LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D))) :
    ∃ (e : D.I → LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D))
      (b : Module.Basis (D.base.support ⊕ D.I) ℂ (LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D))),
      (∀ j, e j ≠ 0 ∧ ∀ i : D.base.support,
        ⁅generator ℂ (datumCartan D) (.H i), e j⁆ = (D.datum.pairing j i : ℂ) • e j) ∧
      (∀ i : D.base.support, e i = generator ℂ (datumCartan D) (.E i) ∧
        e (oppositeIndex D i) = generator ℂ (datumCartan D) (.F i)) ∧
      (∀ i, b (.inl i) = generator ℂ (datumCartan D) (.H i)) ∧
      (∀ i, b (.inr i) = e i) ∧
      (∀ i, ⁅⁅e i, e (oppositeIndex D i)⁆, e i⁆ = (2 : ℂ) • e i) ∧
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = (n : ℂ) • e k ∧
          ⁅e (oppositeIndex D i), e (oppositeIndex D j)⁆ = (-n : ℤ) • e (oppositeIndex D k)) ∧
      (∀ i j, D.datum.root i + D.datum.root j ≠ 0 →
        D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0) := by
  classical
  letI := C.finite
  letI := C.isCartan
  letI : LieAlgebra.HasTrivialRadical ℂ (LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)) := ⟨hss⟩
  have ht := cartan_toral C.cartan
  have hH : IsMaximalToral C.cartan :=
    self_centralizing_maximal C.cartan ht (cartan_centralizer C.cartan ht)
  let a := cartanCharacter D C
  have ha : Function.Injective a := cartanCharacter_injective D C hsep
  have hr (y : D.X) : a y ∈ rootSet C.cartan ↔ y ∈ Set.range D.datum.root :=
    rootSet_cartanCharacter D C y ha
  have hreg (α : Module.Dual ℂ C.cartan) (hα : α ∈ rootSet C.cartan) : C.direction α ≠ 0 :=
    C.regular α hα
  obtain ⟨negRoot, X, N, _, B, hX, hOpp, _, _, _, hbr, hz, hBc, hBr, _, _, _⟩ :=
    chevalley_basis hss C.cartan hH C.direction hreg
  let r (i : D.I) : rootSet C.cartan := ⟨a (D.datum.root i), (hr _).mpr ⟨i, rfl⟩⟩
  have hrOpp (i : D.I) : (r (oppositeIndex D i)).val = -(r i).val := by
    change a (D.datum.root (oppositeIndex D i)) = -a (D.datum.root i)
    rw [root_oppositeIndex, map_neg]
  let opp (α : rootSet C.cartan) : rootSet C.cartan := ⟨-α.val, negRoot α⟩
  have hopp (i : D.I) : opp (r i) = r (oppositeIndex D i) := Subtype.ext (hrOpp i).symm
  have hn (i : D.I) : ⁅X (r i), X (r (oppositeIndex D i))⁆ =
      (killingCoroot C.cartan (r i).val : LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)) := by
    simpa only [← hopp] using hOpp (r i)
  have hsimple (i : D.base.support) := C.normalized (C.simpleIndex i)
  simp only [Equiv.symm_apply_apply, cartanCharacter_simple] at hsimple
  have hsimple' (i : D.base.support) :
      ∃ c : ℂˣ, generator ℂ (datumCartan D) (.E i) = (c : ℂ) • X (r i) := by
    have h := hsimple i
    exact scalar_multiple_of_rootSpace D C hss hH (r i) (hX _).1 h.1 (hX _).2 h.2.2.1
  choose c hc using hsimple'
  let s (i : D.I) : ℂˣ := (rootScaling D c (D.datum.rootSpanMem ℤ i)).toMul
  let e (i : D.I) := (s i : ℂ) • X (r i)
  have hs (i : D.I) : e i ∈ rootSpace C.cartan (r i).val := Submodule.smul_mem _ _ (hX _).1
  have he0 (i : D.I) : e i ≠ 0 := smul_ne_zero (Units.ne_zero _) (hX _).2
  have hpos (i : D.base.support) : e i = generator ℂ (datumCartan D) (.E i) := by
    dsimp only [e, s]
    rw [rootScaling_apply_simple, ← hc]
  have hnorm (i : D.I) : ⁅e i, e (oppositeIndex D i)⁆ =
      (killingCoroot C.cartan (r i).val : LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)) := by
    change ⁅(s i : ℂ) • X (r i), (s (oppositeIndex D i) : ℂ) • X (r (oppositeIndex D i))⁆ = _
    have h : (s i : ℂ) * (s (oppositeIndex D i) : ℂ) = 1 :=
      congrArg Units.val (rootScaling_opp D c i)
    rw [smul_lie, lie_smul, smul_smul, h, one_smul, hn]
  have hlength (i : D.I) : (r i).val (killingCoroot C.cartan (r i).val) = 2 := by
    rw [killingCoroot_pairing hss C.cartan hH, mul_div_cancel_right₀ _
      (rootForm_self_ne_zero hss C.cartan hH (r i).val (r i).property)]
  have h2 (i : D.I) : ⁅⁅e i, e (oppositeIndex D i)⁆, e i⁆ = (2 : ℂ) • e i := by
    rw [hnorm, (mem_rootSpace C.cartan _ _).mp (hs i), hlength]
  have hneg (i : D.base.support) : e (oppositeIndex D i) = generator ℂ (datumCartan D) (.F i) := by
    have h := hsimple i
    have hf : generator ℂ (datumCartan D) (.F i) ∈ rootSpace C.cartan (r (oppositeIndex D i)).val := by
      rw [hrOpp]
      exact h.2.1
    obtain ⟨d, hd⟩ := scalar_multiple_of_rootSpace D C hss hH (r (oppositeIndex D i))
      (hs _) hf (he0 _) h.2.2.2.1
    have hb : ⁅e i, generator ℂ (datumCartan D) (.F i)⁆ = ⁅e i, e (oppositeIndex D i)⁆ := by
      rw [hnorm, hpos]
      have hb := h.2.2.2.2
      change _ = (killingCoroot C.cartan (C.simpleIndex i).val :
        LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)) at hb
      rw [cartanCharacter_simple] at hb
      exact hb
    rw [hd, lie_smul] at hb
    have hz : ⁅e i, e (oppositeIndex D i)⁆ ≠ 0 := by
      intro he
      have h₀ := h2 i
      rw [he, zero_lie] at h₀
      exact smul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) (he0 i) h₀.symm
    have hdone := smul_left_injective ℂ hz (hb.trans (one_smul ℂ _).symm)
    rw [hd, hdone, one_smul]
  let rEquiv : D.I ≃ rootSet C.cartan := Equiv.ofBijective r ⟨fun i j h =>
    D.datum.root.injective (ha (congrArg Subtype.val h)), fun α => by
      have hα := α.property
      change α.val ∈ _root_.Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSet_value C.cartan at hα
      rw [← C.roots_eq] at hα
      obtain ⟨i, hi⟩ := hα
      exact ⟨i, Subtype.ext hi⟩⟩
  let b := (B.reindex (Equiv.sumCongr C.simpleIndex rEquiv).symm).unitsSMul (Sum.elim (fun _ => 1) s)
  have hbC (i : D.base.support) : b (.inl i) = generator ℂ (datumCartan D) (.H i) := by
    simp only [b, Module.Basis.unitsSMul_apply, Sum.elim_inl, one_smul, Module.Basis.reindex_apply,
      Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inl, hBc, cartanCharacter_simple]
    rw [← hnorm i, hpos, hneg]
    change ⁅LieAlgebrasAndRepresentations.Serre.e (datumCartan D) i,
      LieAlgebrasAndRepresentations.Serre.f (datumCartan D) i⁆ =
        LieAlgebrasAndRepresentations.Serre.h (datumCartan D) i
    simp [LieAlgebrasAndRepresentations.Serre.ef]
  have hbR (i : D.I) : b (.inr i) = e i := by
    simp only [b, Module.Basis.unitsSMul_apply, Sum.elim_inr, Module.Basis.reindex_apply,
      Equiv.symm_symm, Equiv.sumCongr_apply, Sum.map_inr, hBr]
    rfl
  refine ⟨e, b, fun i => ⟨he0 i, complexWeight_of_rootSpace D C i (hs i)⟩,
    fun i => ⟨hpos i, hneg i⟩, hbC, hbR, h2, ?_, ?_⟩
  · intro i j k hij
    have hab : (r i).val + (r j).val = (r k).val := by
      change a (D.datum.root i) + a (D.datum.root j) = a (D.datum.root k)
      rw [← map_add, hij]
    have hm : (r i).val + (r j).val ∈ rootSet C.cartan := hab.symm ▸ (r k).property
    obtain ⟨Hbr, Hneg, p, q, hpq, hN⟩ := hbr (r i) (r j) hm
    refine ⟨p, q, N (r i) (r j) hm, ?_, hN, ?_, ?_⟩
    · intro n
      have h := hpq n
      change (r j).val + n • (r i).val ∈ rootSet C.cartan ↔ _ at h
      rw [show (r j).val + n • (r i).val = a (D.datum.root j + n • D.datum.root i) by
        simp [r, map_add, map_zsmul], hr] at h
      exact h
    · have H : (⟨(r i).val + (r j).val, hm⟩ : rootSet C.cartan) = r k := Subtype.ext hab
      rw [H] at Hbr
      have hs' : (s i : ℂ) * (s j : ℂ) = (s k : ℂ) :=
        congrArg Units.val (rootScaling_mul D c i j k hij)
      change ⁅(s i : ℂ) • X (r i), (s j : ℂ) • X (r j)⁆ = _
      rw [smul_lie, lie_smul, smul_smul, hs', Hbr, smul_smul]
      change _ = _ • ((s k : ℂ) • X (r k))
      rw [smul_smul, mul_comm (s k : ℂ)]
    · have hmo : (opp (r i)).val + (opp (r j)).val ∈ rootSet C.cartan := by
        change -(r i).val + -(r j).val ∈ rootSet C.cartan
        simpa only [← neg_add] using negRoot ⟨_, hm⟩
      have ho := (hbr (opp (r i)) (opp (r j)) hmo).1
      change N (opp (r i)) (opp (r j)) hmo = -N (r i) (r j) hm at Hneg
      rw [Hneg] at ho
      have hk : (⟨_, hmo⟩ : rootSet C.cartan) = r (oppositeIndex D k) :=
        Subtype.ext (by change -(r i).val + -(r j).val = _; rw [← neg_add, hab, hrOpp])
      rw [hk, hopp i, hopp j] at ho
      have hij' : D.datum.root (oppositeIndex D i) + D.datum.root (oppositeIndex D j) =
          D.datum.root (oppositeIndex D k) := by
        simp only [root_oppositeIndex, ← neg_add, hij]
      have hs' : (s (oppositeIndex D i) : ℂ) * (s (oppositeIndex D j) : ℂ) =
          (s (oppositeIndex D k) : ℂ) := congrArg Units.val (rootScaling_mul D c _ _ _ hij')
      rw [← Int.cast_smul_eq_zsmul ℂ]
      change ⁅(s (oppositeIndex D i) : ℂ) • X _, (s (oppositeIndex D j) : ℂ) • X _⁆ =
        ((-N (r i) (r j) hm : ℤ) : ℂ) • ((s (oppositeIndex D k) : ℂ) • X _)
      rw [smul_lie, lie_smul, smul_smul, hs', ho, smul_smul, smul_smul, mul_comm]
  · intro i j hne hnot
    have hab : (r i).val + (r j).val = a (D.datum.root i + D.datum.root j) := (map_add _ _ _).symm
    have hne' : (r i).val + (r j).val ≠ 0 := by rw [hab, ← map_zero a]; exact fun h => hne (ha h)
    have hnot' : (r i).val + (r j).val ∉ rootSet C.cartan := by rw [hab, hr]; exact hnot
    change ⁅(s i : ℂ) • X (r i), (s j : ℂ) • X (r j)⁆ = _
    rw [smul_lie, lie_smul, hz _ _ hne' hnot', smul_zero, smul_zero]

private abbrev RationalSerre (D : BasedRootDatum.{u}) [DecidableEq D.base.support] :=
  Matrix.ToLieAlgebra ℚ (datumCartan D)

private abbrev ComplexSerre (D : BasedRootDatum.{u}) [DecidableEq D.base.support] :=
  LieAlgebrasAndRepresentations.Serre.Algebra (datumCartan D)

local instance (D : BasedRootDatum.{u}) [DecidableEq D.base.support] :
    LieAlgebra ℚ (ComplexSerre D) :=
  inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ ℂ (ComplexSerre D)))

local instance (D : BasedRootDatum.{u}) [DecidableEq D.base.support] :
    IsScalarTower ℚ ℂ (ComplexSerre D) := IsScalarTower.restrictScalars ℚ ℂ (ComplexSerre D)

private def serreComplexification (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (E : (ℂ ⊗[ℚ] RationalSerre D) ≃ₗ⁅ℂ⁆ ComplexSerre D) :
    RationalSerre D →ₗ⁅ℚ⁆ ComplexSerre D :=
  { ((E.toLinearEquiv.toLinearMap : (ℂ ⊗[ℚ] RationalSerre D) →ₗ[ℂ] ComplexSerre D).restrictScalars ℚ).comp
      (TensorProduct.mk ℚ ℂ (RationalSerre D) 1) with
    map_lie' := by
      intro x y
      change E (1 ⊗ₜ[ℚ] ⁅x,y⁆) = ⁅E (1 ⊗ₜ[ℚ] x), E (1 ⊗ₜ[ℚ] y)⁆
      rw [← E.map_lie, LieAlgebra.ExtendScalars.bracket_tmul, one_mul] }

private theorem serreComplexification_injective (D : BasedRootDatum.{u}) [DecidableEq D.base.support]
    (E : (ℂ ⊗[ℚ] RationalSerre D) ≃ₗ⁅ℂ⁆ ComplexSerre D) :
    Function.Injective (serreComplexification D E) := by
  have hi : Function.Injective (TensorProduct.mk ℚ ℂ (RationalSerre D) 1) := by
    intro x y he
    apply eq_of_sub_eq_zero
    by_contra! hne
    have h : LinearIndependent ℚ (fun _ : Unit => x - y) :=
      linearIndependent_unique_iff.mpr hne
    have h' := (Module.Flat.linearIndependent_one_tmul (S := ℂ) h).ne_zero ()
    apply h'
    change (TensorProduct.mk ℚ ℂ (RationalSerre D) 1) (x - y) = 0
    rw [map_sub, he, sub_self]
  exact E.injective.comp hi

/-- The complex Chevalley vectors normalized at the Serre generators descend
along the rational presentation, including the integer string constants. -/
private theorem normalizedRationalSerreRoots (D : BasedRootDatum.{u})
    [DecidableEq D.base.support] (hC : ComplexCartan.{u}) (hS : SerreStructure.{u})
    (hE : SerreBaseChange.{u})
    (hsep : Function.Injective (fun x : D.X => fun i : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot i))) :
    ∃ (e : D.I → RationalSerre D) (b : Module.Basis (D.base.support ⊕ D.I) ℚ (RationalSerre D)),
      (∀ j, e j ≠ 0 ∧ e j ∈ rationalWeightSpace (datumCartan D) (fun i => D.datum.pairing j i)) ∧
      (∀ i : D.base.support, e i = generator ℚ (datumCartan D) (.E i) ∧
        e (oppositeIndex D i) = generator ℚ (datumCartan D) (.F i)) ∧
      (∀ i, b (.inl i) = generator ℚ (datumCartan D) (.H i)) ∧
      (∀ i, b (.inr i) = e i) ∧
      (∀ i, ⁅⁅e i, e (oppositeIndex D i)⁆, e i⁆ = (2 : ℕ) • e i) ∧
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k ∧
          ⁅e (oppositeIndex D i), e (oppositeIndex D j)⁆ = (-n) • e (oppositeIndex D k)) ∧
      (∀ i j, D.datum.root i + D.datum.root j ≠ 0 →
        D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0) := by
  let A := datumCartan D
  obtain ⟨C⟩ := hC D
  obtain ⟨_, _, hfin, hdim, hss, _, _, _, _⟩ := hS D
  obtain ⟨E, hgen⟩ := hE A
  obtain ⟨x, B, hx, hs, hBc, hBr, h2, hbr, hz⟩ := normalizedComplexSerreRoots D C hsep hss
  let f := serreComplexification D E
  have hf : Function.Injective f := serreComplexification_injective D E
  have hmap (s : CartanMatrix.Generators D.base.support) :
      f (generator ℚ (datumCartan D) s) = generator ℂ (datumCartan D) s := hgen s
  have hx' (i : D.I) : x i ∈ f.toLinearMap.range := by
    apply rootVectors_mem_range_of_simple D f x ?_ ?_ i
    · intro j hj
      exact ⟨⟨generator ℚ A (.E ⟨j, hj⟩), (hmap _).trans (hs ⟨j, hj⟩).1.symm⟩,
        ⟨generator ℚ A (.F ⟨j, hj⟩), (hmap _).trans (hs ⟨j, hj⟩).2.symm⟩⟩
    · intro i j k he
      obtain ⟨p, _, n, _, hn, hb, _⟩ := hbr i j k he.symm
      refine ⟨n, ?_, ?_⟩
      · rcases hn with rfl | rfl <;> omega
      · simpa only [Int.cast_smul_eq_zsmul ℂ] using hb
  choose e he using hx'
  have he' (i : D.I) : f (e i) = x i := he i
  have hcartan (i : D.base.support) : f (generator ℚ A (.H i)) = B (.inl i) :=
    (hmap _).trans (hBc i).symm
  let v : D.base.support ⊕ D.I → RationalSerre D := Sum.elim (fun i => generator ℚ A (.H i)) e
  have hv (i : D.base.support ⊕ D.I) : f (v i) = B i := by
    cases i with
    | inl i => exact hcartan i
    | inr i => exact (he' i).trans (hBr i).symm
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite D.I
  letI : Module.Finite ℚ (RationalSerre D) := hfin
  have hli : LinearIndependent ℚ v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have h := congrArg f hc
    simp only [map_sum, map_smul, map_zero, hv] at h
    change (∑ i, (algebraMap ℚ ℂ (c i)) • B i) = 0 at h
    exact (algebraMap ℚ ℂ).injective (by
      simpa only [map_zero] using Fintype.linearIndependent_iff.mp B.linearIndependent _ h i)
  have hcard : Fintype.card (D.base.support ⊕ D.I) = Module.finrank ℚ (RationalSerre D) := by
    rw [hdim, Fintype.card_sum, Fintype.card_coe, Nat.card_eq_fintype_card]
  let b := basisOfLinearIndependentOfCardEqFinrank' v hli hcard
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  refine ⟨e, b, ?_, ?_, fun i => congrFun hb (.inl i), fun i => congrFun hb (.inr i), ?_, ?_, ?_⟩
  · intro i
    refine ⟨fun h => (hx i).1 ((he' i).symm.trans ((congrArg f h).trans (map_zero f))), ?_⟩
    intro j
    apply hf
    simp only [f.map_lie, hmap, he', map_smul]
    change _ = ((D.datum.pairing i j : ℚ) : ℂ) • x i
    rw [Rat.cast_intCast]
    exact (hx i).2 j
  · intro i
    exact ⟨hf ((he' i).trans ((hs i).1.trans (hmap _).symm)),
      hf ((he' _).trans ((hs i).2.trans (hmap _).symm))⟩
  · intro i
    apply hf
    simpa only [f.map_lie, he', map_nsmul, two_smul, two_nsmul, map_add] using h2 i
  · intro i j k heq
    obtain ⟨p, q, n, hp, hn, hpos, hneg⟩ := hbr i j k heq
    refine ⟨p, q, n, hp, hn, hf ?_, hf ?_⟩
    · simpa only [f.map_lie, he', map_zsmul, Int.cast_smul_eq_zsmul ℂ] using hpos
    · simpa only [f.map_lie, he', map_zsmul] using hneg
  · intro i j h₀ h₁
    apply hf
    simpa only [f.map_lie, he', map_zero] using hz i j h₀ h₁

end NormalizedSerreRoots

section CartanWeights

variable {D : BasedRootDatum.{u}} {K : Type v} [Field K] [CharZero K]
  {L : Type w} [LieRing L] [LieAlgebra K L]

private def HasCartanWeight (h : D.base.support → L) (χ : D.X) (x : L) : Prop :=
  ∀ j, ⁅h j, x⁆ = (D.datum.toLinearMap χ (D.datum.coroot j) : K) • x

private theorem HasCartanWeight.smul {h : D.base.support → L} {χ : D.X} {x : L}
    (hx : HasCartanWeight (K := K) h χ x) (a : K) : HasCartanWeight (K := K) h χ (a • x) := by
  intro j
  rw [lie_smul, hx j, smul_comm]

private theorem HasCartanWeight.lie {h : D.base.support → L} {χ ψ : D.X} {x y : L}
    (hx : HasCartanWeight (K := K) h χ x) (hy : HasCartanWeight (K := K) h ψ y) :
    HasCartanWeight (K := K) h (χ + ψ) ⁅x,y⁆ := by
  intro j
  rw [leibniz_lie, hx j, hy j, smul_lie, lie_smul, map_add, LinearMap.add_apply, Int.cast_add, add_smul]

private theorem HasCartanWeight.ad_pow {h : D.base.support → L} {χ ψ : D.X} {x y : L}
    (hx : HasCartanWeight (K := K) h χ x) (hy : HasCartanWeight (K := K) h ψ y) (n : ℕ) :
    HasCartanWeight (K := K) h (ψ + n • χ) ((LieAlgebra.ad K L x ^ n) y) := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
    rw [pow_succ']
    change HasCartanWeight (K := K) h _ ⁅x, ((LieAlgebra.ad K L x ^ n) y)⁆
    rw [show ψ + (n + 1) • χ = χ + (ψ + n • χ) by rw [succ_nsmul]; abel]
    exact hx.lie ih

private theorem cartanWeight_coord_eq_zero {ι : Type*} (b : Module.Basis ι K L)
    (h : D.base.support → L) (wt : ι → D.X)
    (hb : ∀ i, HasCartanWeight (K := K) h (wt i) (b i))
    (hsep : Function.Injective (fun x : D.X => fun j : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot j)))
    {χ : D.X} {x : L} (hx : HasCartanWeight (K := K) h χ x) {i : ι} (hi : wt i ≠ χ) :
    b.repr x i = 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : D.base.support,
      D.datum.toLinearMap (wt i) (D.datum.coroot j) ≠ D.datum.toLinearMap χ (D.datum.coroot j) := by
    by_contra! h
    exact hi (hsep (funext h))
  have hc : (b.coord i).comp (LieAlgebra.ad K L (h j)) =
      (D.datum.toLinearMap (wt i) (D.datum.coroot j) : K) • b.coord i := by
    apply b.ext
    intro q
    change b.coord i ⁅h j, b q⁆ = _
    rw [hb q j, map_smul, LinearMap.smul_apply, Module.Basis.coord_apply, b.repr_self]
    by_cases hh : i = q
    · subst q; rfl
    · simp [Finsupp.single_apply, hh, Ne.symm hh]
  have he := LinearMap.congr_fun hc x
  change b.coord i ⁅h j, x⁆ = (D.datum.toLinearMap (wt i) (D.datum.coroot j) : K) • b.coord i x at he
  rw [hx j, map_smul, Module.Basis.coord_apply] at he
  by_contra hne
  exact hj (Int.cast_injective (α := K) (mul_right_cancel₀ hne he).symm)

private theorem eq_zero_of_cartanWeight_not_labelled (b : Module.Basis (D.base.support ⊕ D.I) K L)
    (h : D.base.support → L)
    (hb : ∀ i, HasCartanWeight (K := K) h (i.elim (fun _ => 0) D.datum.root) (b i))
    (hsep : Function.Injective (fun x : D.X => fun j : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot j)))
    {χ : D.X} {x : L} (hx : HasCartanWeight (K := K) h χ x) (h0 : χ ≠ 0)
    (hχ : χ ∉ Set.range D.datum.root) : x = 0 := by
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  exact cartanWeight_coord_eq_zero b h _ hb hsep hx (by
    cases i with
    | inl j => exact h0.symm
    | inr j => exact fun he => hχ ⟨j, he⟩)

private theorem eq_smul_of_cartanWeight_root (b : Module.Basis (D.base.support ⊕ D.I) K L)
    (h : D.base.support → L)
    (hb : ∀ i, HasCartanWeight (K := K) h (i.elim (fun _ => 0) D.datum.root) (b i))
    (hsep : Function.Injective (fun x : D.X => fun j : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot j)))
    {j : D.I} {x : L} (hx : HasCartanWeight (K := K) h (D.datum.root j) x) :
    x = b.repr x (.inr j) • b (.inr j) := by
  classical
  apply b.repr.injective
  ext i
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply]
  split_ifs with hi
  · subst i; simp
  · rw [smul_zero]
    exact cartanWeight_coord_eq_zero b h _ hb hsep hx (by
      cases i with
      | inl i => exact (D.datum.ne_zero j).symm
      | inr i => exact fun he => hi (congrArg Sum.inr (D.datum.root.injective he).symm))

end CartanWeights

section SerreLift

open Specs.RationalRealization (generator)

variable {ι : Type u} {K : Type v} [Field K] {M : Type w} [LieRing M] [LieAlgebra K M]

private theorem exists_serreHom [DecidableEq ι] (C : Matrix ι ι ℤ) (H E F : ι → M)
    (hHH : ∀ i j, ⁅H i, H j⁆ = 0)
    (hEF : ∀ i j, ⁅E i, F j⁆ = if i = j then H i else 0)
    (hHE : ∀ i j, ⁅H i, E j⁆ = C i j • E j)
    (hHF : ∀ i j, ⁅H i, F j⁆ = -(C i j • F j))
    (hE : ∀ i j, i ≠ j → ((LieAlgebra.ad K M (E i)) ^ ((-C i j).toNat + 1)) (E j) = 0)
    (hF : ∀ i j, i ≠ j → ((LieAlgebra.ad K M (F i)) ^ ((-C i j).toNat + 1)) (F j) = 0) :
    ∃ f : Matrix.ToLieAlgebra K C →ₗ⁅K⁆ M,
      (∀ i, f (generator K C (.H i)) = H i) ∧
      (∀ i, f (generator K C (.E i)) = E i) ∧
      ∀ i, f (generator K C (.F i)) = F i := by
  let X : CartanMatrix.Generators ι → M
    | .H i => H i
    | .E i => E i
    | .F i => F i
  let f := FreeLieAlgebra.lift K X
  have h (i) : f (FreeLieAlgebra.of K (.H i)) = H i := FreeLieAlgebra.lift_of_apply _ _
  have e (i) : f (FreeLieAlgebra.of K (.E i)) = E i := FreeLieAlgebra.lift_of_apply _ _
  have g (i) : f (FreeLieAlgebra.of K (.F i)) = F i := FreeLieAlgebra.lift_of_apply _ _
  have had (x y : FreeLieAlgebra K (CartanMatrix.Generators ι)) (n : ℕ) :
      f ((LieAlgebra.ad K _ x ^ n) y) = (LieAlgebra.ad K _ (f x) ^ n) (f y) := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, f.map_lie, ih]
  have hker : CartanMatrix.Relations.toIdeal K C ≤ f.ker := by
    apply LieSubmodule.lieSpan_le.mpr
    intro x hx
    change f x = 0
    simp only [CartanMatrix.Relations.toSet, Set.mem_union] at hx
    rcases hx with (((((hx | hx) | hx) | hx) | hx) | hx) <;> rcases hx with ⟨⟨i,j⟩, rfl⟩
    · simpa only [CartanMatrix.Relations.HH, Function.uncurry_apply_pair, Function.comp_apply,
        f.map_lie, h] using hHH i j
    · by_cases hh : i = j
      · subst j
        simp [CartanMatrix.Relations.EF, f.map_lie, e, g, h, hEF]
      · simp [CartanMatrix.Relations.EF, hh, f.map_lie, e, g, hEF]
    · simp [CartanMatrix.Relations.HE, f.map_lie, h, e, hHE]
    · simp [CartanMatrix.Relations.HF, f.map_lie, h, g, hHF]
    · simp only [CartanMatrix.Relations.adE, Function.uncurry_apply_pair, Function.comp_apply,
        had, f.map_lie, e]
      by_cases hh : i = j
      · subst j; simp only [lie_self, map_zero]
      · simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using hE i j hh
    · simp only [CartanMatrix.Relations.adF, Function.uncurry_apply_pair, Function.comp_apply,
        had, f.map_lie, g]
      by_cases hh : i = j
      · subst j; simp only [lie_self, map_zero]
      · simpa only [pow_succ, Module.End.mul_apply, LieAlgebra.ad_apply] using hF i j hh
  let I := CartanMatrix.Relations.toIdeal K C
  let φ : Matrix.ToLieAlgebra K C →ₗ⁅K⁆ M :=
    { I.toSubmodule.liftQ f.toLinearMap hker with
      map_lie' := by
        intro x y
        induction x using Submodule.Quotient.induction_on with | _ x =>
        induction y using Submodule.Quotient.induction_on with | _ y =>
        exact f.map_lie x y }
  exact ⟨φ, h, e, g⟩

end SerreLift
section SerreTraces

variable {D : BasedRootDatum.{u}} {K : Type v} [Field K] [CharZero K]
  {L : Type w} [LieRing L] [LieAlgebra K L]

private theorem simple_string_past_top (D : BasedRootDatum.{u})
    (i j : D.base.support) (hij : i ≠ j) :
    let n := (-(datumCartan D i j)).toNat + 1
    D.datum.root j + n • D.datum.root i ≠ 0 ∧
      D.datum.root j + n • D.datum.root i ∉ Set.range D.datum.root := by
  letI : Finite D.I := D.finiteRoots
  letI := D.reduced
  intro n
  have hab := D.base.linearIndependent_pair_of_ne hij
  refine ⟨?_, ?_⟩
  · intro h
    have e : (n : ℤ) • D.datum.root i + (1 : ℤ) • D.datum.root j =
        (0 : ℤ) • D.datum.root i + (0 : ℤ) • D.datum.root j := by
      simp only [natCast_zsmul, one_zsmul, zero_zsmul, add_zero, add_comm _ (D.datum.root j)]
      exact h
    exact one_ne_zero (hab.eq_of_pair e).2
  · have htop : D.datum.chainTopCoeff i j = (-(datumCartan D i j)).toNat := by
      have h := D.base.chainTopCoeff_eq_of_ne hij
      have hpair : D.datum.pairingIn ℤ j i = datumCartan D i j := by
        simpa only [RootData.integralCartan, Algebra.algebraMap_self_apply] using
          D.datum.algebraMap_pairingIn ℤ (j : D.I) (i : D.I)
      rw [hpair] at h
      simpa only [Int.toNat_natCast] using congrArg Int.toNat h
    rw [D.datum.root_add_nsmul_mem_range_iff_le_chainTopCoeff hab, htop]
    exact Nat.not_succ_le_self _

private theorem serreRelations_of_cartanBasis [DecidableEq D.base.support]
    (b : Module.Basis (D.base.support ⊕ D.I) K L) (h : D.base.support → L) (E F : D.base.support → L)
    (hb : ∀ i, HasCartanWeight (K := K) h (i.elim (fun _ => 0) D.datum.root) (b i))
    (hsep : Function.Injective (fun x : D.X => fun j : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot j)))
    (hH : ∀ i, b (.inl i) = h i) (hE : ∀ i : D.base.support, b (.inr i) = E i)
    (hF : ∀ i : D.base.support, HasCartanWeight (K := K) h (-D.datum.root i) (F i))
    (hEF : ∀ i, ⁅E i, F i⁆ = h i) :
    (∀ i j, ⁅h i, h j⁆ = 0) ∧
    (∀ i j, ⁅E i, F j⁆ = if i = j then h i else 0) ∧
    (∀ i j, ⁅h i, E j⁆ = datumCartan D i j • E j) ∧
    (∀ i j, ⁅h i, F j⁆ = -(datumCartan D i j • F j)) ∧
    (∀ i j, i ≠ j → ((LieAlgebra.ad K L (E i)) ^ ((-datumCartan D i j).toNat + 1)) (E j) = 0) ∧
    (∀ i j, i ≠ j → ((LieAlgebra.ad K L (F i)) ^ ((-datumCartan D i j).toNat + 1)) (F j) = 0) := by
  have hwE (i : D.base.support) : HasCartanWeight (K := K) h (D.datum.root i) (E i) := by
    rw [← hE i]
    exact hb (.inr i)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [← hH j]
    simpa only [Sum.elim_inl, map_zero, LinearMap.zero_apply, Int.cast_zero, zero_smul] using hb (.inl j) i
  · intro i j
    by_cases hij : i = j
    · subst j; simpa using hEF i
    · rw [if_neg hij]
      apply eq_zero_of_cartanWeight_not_labelled b h hb hsep ((hwE i).lie (hF j))
      · rw [← sub_eq_add_neg, sub_ne_zero]
        exact fun he => hij (Subtype.ext (D.datum.root.injective he))
      · rw [← sub_eq_add_neg]
        exact D.base.sub_notMem_range_root i.property j.property
  · intro i j
    have he := hwE j i
    change _ = (datumCartan D i j : K) • _ at he
    simpa only [Int.cast_smul_eq_zsmul K] using he
  · intro i j
    have he := hF j i
    rw [map_neg, LinearMap.neg_apply] at he
    change ⁅h i, F j⁆ = ((-(datumCartan D i j) : ℤ) : K) • F j at he
    simpa only [Int.cast_smul_eq_zsmul K, neg_smul] using he
  · intro i j hij
    let n := (-(datumCartan D i j)).toNat + 1
    have hw := (hwE i).ad_pow (hwE j) n
    obtain ⟨hn₀, hn₁⟩ := simple_string_past_top D i j hij
    exact eq_zero_of_cartanWeight_not_labelled b h hb hsep hw hn₀ hn₁
  · intro i j hij
    let n := (-(datumCartan D i j)).toNat + 1
    have hw := (hF i).ad_pow (hF j) n
    obtain ⟨hn₀, hn₁⟩ := simple_string_past_top D i j hij
    apply eq_zero_of_cartanWeight_not_labelled b h hb hsep hw
    · rwa [smul_neg, ← neg_add, neg_ne_zero]
    · rwa [smul_neg, ← neg_add, D.datum.neg_mem_range_root_iff]

end SerreTraces

section MarkedChevalleyVectors

open Specs.RationalRealization (ComplexCartan SerreStructure SerreBaseChange
  RationalSerreDecomposition generator rationalWeightSpace)

variable {D : BasedRootDatum.{u}} {K : Type v} [Field K] [CharZero K]
  {L : Type w} [LieRing L] [LieAlgebra K L]

private theorem normalizeRootVectors [DecidableEq D.base.support]
    (hC : ComplexCartan.{u}) (hS : SerreStructure.{u}) (hE : SerreBaseChange.{u})
    (hdec : RationalSerreDecomposition.{u})
    (b : Module.Basis (D.base.support ⊕ D.I) K L) (h : D.I → L)
    (hb : ∀ i, HasCartanWeight (K := K) (fun j : D.base.support => h j)
      (i.elim (fun _ => 0) D.datum.root) (b i))
    (hsep : Function.Injective (fun x : D.X => fun j : D.base.support =>
      D.datum.toLinearMap x (D.datum.coroot j)))
    (hH : ∀ i : D.base.support, b (.inl i) = h i)
    (hbracket : ∀ i, ∃ c : Kˣ, ⁅b (.inr i), b (.inr (oppositeIndex D i))⁆ = (c : K) • h i)
    (hdiag : ∀ i, ⁅h i, b (.inr i)⁆ = (2 : K) • b (.inr i)) :
    ∃ c : D.I → Kˣ, (∀ i : D.base.support, c i = 1) ∧
      let e (i : D.I) := (c i : K) • b (.inr i)
      (∀ i j, D.datum.root j = -D.datum.root i → ⁅e i, e j⁆ = h i) ∧
      (∀ i j k, D.datum.root i + D.datum.root j = D.datum.root k →
        ∃ (p q : ℕ) (n : ℤ), IsRootString i j p q ∧
          (n = (p : ℤ) + 1 ∨ n = -((p : ℤ) + 1)) ∧ ⁅e i, e j⁆ = n • e k ∧
          ⁅e (oppositeIndex D i), e (oppositeIndex D j)⁆ = (-n) • e (oppositeIndex D k)) ∧
      (∀ i j, D.datum.root i + D.datum.root j ≠ 0 →
        D.datum.root i + D.datum.root j ∉ Set.range D.datum.root → ⁅e i, e j⁆ = 0) := by
  classical
  choose d hd using hbracket
  let H (i : D.base.support) : L := h i
  let E (i : D.base.support) : L := b (.inr i)
  let F (i : D.base.support) : L := (↑(d i)⁻¹ : K) • b (.inr (oppositeIndex D i))
  have hF (i : D.base.support) : HasCartanWeight (K := K) H (-D.datum.root i) (F i) := by
    have hh : HasCartanWeight (K := K) H (D.datum.root (oppositeIndex D i))
        (b (.inr (oppositeIndex D i))) := hb (.inr (oppositeIndex D i))
    rw [root_oppositeIndex] at hh
    exact hh.smul _
  have hEF (i : D.base.support) : ⁅E i, F i⁆ = H i := by
    change ⁅b (.inr i), (↑(d i)⁻¹ : K) • b (.inr (oppositeIndex D i))⁆ = h i
    rw [lie_smul, hd, smul_smul, Units.inv_mul, one_smul]
  obtain ⟨hHH, hEF', hHE, hHF, hEP, hFP⟩ := serreRelations_of_cartanBasis b H E F hb hsep hH
    (fun _ => rfl) hF hEF
  letI : LieAlgebra ℚ L := inferInstanceAs (LieAlgebra ℚ (RestrictScalars ℚ K L))
  letI : IsScalarTower ℚ K L := IsScalarTower.restrictScalars ℚ K L
  have had (x y : L) (n : ℕ) : ((LieAlgebra.ad ℚ L x) ^ n) y = ((LieAlgebra.ad K L x) ^ n) y := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [pow_succ', Module.End.mul_apply, LieAlgebra.ad_apply, ih]
  obtain ⟨f, hfH, hfE, _⟩ := exists_serreHom (K := ℚ) (datumCartan D) H E F hHH hEF' hHE hHF
    (fun i j hij => (had _ _ _).trans (hEP i j hij))
    (fun i j hij => (had _ _ _).trans (hFP i j hij))
  obtain ⟨e, _, hw, heS, _, _, h2, hbr, hz⟩ := normalizedRationalSerreRoots D hC hS hE hsep
  have hfHE (i : D.base.support) : f (e i) = E i := (congrArg f (heS i).1).trans (hfE i)
  have hw' (i : D.I) : HasCartanWeight (K := K) H (D.datum.root i) (f (e i)) := by
    intro j
    have he := (hw i).2 j
    change ⁅generator ℚ (datumCartan D) (.H j), e i⁆ = (D.datum.pairing i j : ℚ) • e i at he
    rw [Int.cast_smul_eq_zsmul ℚ] at he
    have hf := congrArg f he
    rw [f.map_lie, map_zsmul, hfH, ← Int.cast_smul_eq_zsmul K] at hf
    exact hf
  have hfnz (i : D.I) : f (e i) ≠ 0 := by
    intro hz
    let z := ⁅e i, e (oppositeIndex D i)⁆
    have hz' : f z = 0 := by simp [z, f.map_lie, hz]
    have hz₀ : z ≠ 0 := by
      intro he
      have h := h2 i
      change ⁅z, e i⁆ = _ at h
      rw [he, zero_lie, ← Nat.cast_smul_eq_nsmul ℚ] at h
      exact smul_ne_zero (by norm_num : ((2 : ℕ) : ℚ) ≠ 0) (hw i).1 h.symm
    have hzero : z ∈ rationalWeightSpace (datumCartan D) 0 := by
      intro j
      have hi := (hw i).2 j
      have hj := (hw (oppositeIndex D i)).2 j
      change ⁅generator ℚ (datumCartan D) (.H j), e i⁆ =
        ((D.datum.toLinearMap (D.datum.root i) (D.datum.coroot j) : ℤ) : ℚ) • e i at hi
      change ⁅generator ℚ (datumCartan D) (.H j), e (oppositeIndex D i)⁆ =
        ((D.datum.toLinearMap (D.datum.root (oppositeIndex D i)) (D.datum.coroot j) : ℤ) : ℚ) • _ at hj
      rw [root_oppositeIndex, map_neg, LinearMap.neg_apply, Int.cast_neg] at hj
      simp only [Pi.zero_apply, zero_smul]
      change ⁅generator ℚ (datumCartan D) (.H j), ⁅e i, e (oppositeIndex D i)⁆⁆ = 0
      rw [leibniz_lie, hi, hj, smul_lie, lie_smul, neg_smul, add_neg_cancel]
    have hh := (hdec D).2.2
    change rationalWeightSpace (datumCartan D) 0 =
      Submodule.span ℚ (Set.range fun j => generator ℚ (datumCartan D) (.H j)) at hh
    rw [hh] at hzero
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hzero
    have hi : LinearIndependent K H := by
      have h := b.linearIndependent.comp Sum.inl Sum.inl_injective
      simpa only [Function.comp_def, hH] using h
    have hsum : (∑ j, a j • H j) = 0 := by
      simpa only [map_sum, map_smul, hfH, hz'] using congrArg f ha
    have ha0 := Fintype.linearIndependent_iff.mp (hi.restrict_scalars' ℚ) a hsum
    exact hz₀ (by simpa only [ha0, zero_smul, Finset.sum_const_zero] using ha.symm)
  let a (i : D.I) : K := b.repr (f (e i)) (.inr i)
  have hscale (i : D.I) : f (e i) = a i • b (.inr i) :=
    eq_smul_of_cartanWeight_root b H hb hsep (hw' i)
  have ha₀ (i : D.I) : a i ≠ 0 := fun h => hfnz i (by rw [hscale, h, zero_smul])
  have hsimple (i : D.base.support) : a i = 1 := by
    dsimp only [a]
    rw [hfHE]
    simp [E]
  let c (i : D.I) := Units.mk0 (a i) (ha₀ i)
  refine ⟨c, fun i => Units.ext (hsimple i), ?_, ?_, ?_⟩
  · intro i j hij
    have he : j = oppositeIndex D i := D.datum.root.injective (hij.trans (root_oppositeIndex D i).symm)
    subst j
    change ⁅a i • b (.inr i), a (oppositeIndex D i) • b (.inr (oppositeIndex D i))⁆ = h i
    have hsrc := congrArg f (h2 i)
    simp only [f.map_lie, map_nsmul, hscale] at hsrc
    have hb₀ : ⁅a i • b (.inr i), a (oppositeIndex D i) • b (.inr (oppositeIndex D i))⁆ =
        (a i * a (oppositeIndex D i) * d i) • h i := by
      rw [smul_lie, lie_smul, smul_smul, hd, smul_smul]
    rw [hb₀, smul_lie, lie_smul, hdiag, smul_comm (a i) (2 : K),
      ← Nat.cast_smul_eq_nsmul K] at hsrc
    have hh : (2 : K) • a i • b (.inr i) ≠ 0 :=
      smul_ne_zero (by norm_num) (smul_ne_zero (ha₀ i) (b.ne_zero _))
    have hconst : a i * a (oppositeIndex D i) * d i = 1 := by
      apply smul_left_injective K hh
      change _ • ((2 : K) • a i • b (.inr i)) = (1 : K) • ((2 : K) • a i • b (.inr i))
      rwa [one_smul]
    rw [hb₀, hconst, one_smul]
  · intro i j k heq
    obtain ⟨p, q, n, hp, hn, hpos, hneg⟩ := hbr i j k heq
    refine ⟨p, q, n, hp, hn, ?_, ?_⟩
    · simpa only [c, Units.val_mk0, f.map_lie, map_zsmul, hscale] using congrArg f hpos
    · simpa only [c, Units.val_mk0, f.map_lie, map_zsmul, hscale] using congrArg f hneg
  · intro i j h₀ h₁
    simpa only [c, Units.val_mk0, f.map_lie, map_zero, hscale] using congrArg f (hz i j h₀ h₁)

end MarkedChevalleyVectors


section MarkedLieBasis

open scoped CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (TwoVariables liftS liftT liftST)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private abbrev dualAlgebra := CommAlgCat.of (RationalField.{u}) (DualNumber (RationalField.{u}))

private def markedCocharacterTangent (v : D.Y) : Lie (RationalField.{u}) Q.pinned.pair.G.val := by
  refine ⟨torus Q v dualAlgebra dualUnit.{u}, ?_⟩
  let k := RationalField.{u}
  let R := dualAlgebra.{u}
  let S := CommAlgCat.of k k
  let f : R ⟶ S := dualReduction k
  let t : Rˣ := dualUnit.{u}
  have hunit : Units.map f.hom.toMonoidHom t = 1 := by
    apply Units.ext
    change (dualUnit.{u} : DualNumber RationalField).fst = 1
    simp [dualUnit_val]
  change mapPoints f (torus Q v R t) = (1 : GroupPoints Q.pinned.pair.G.val S)
  calc
    _ = torus Q v S (Units.map f.hom.toMonoidHom t) := map_torus Q f v t
    _ = torus Q v S 1 := congrArg (torus Q v S) hunit
    _ = 1 := (torusHom_apply Q v S 1).symm.trans ((torusHom Q v S).map_one)

private def markedCocharacterTangentLinear :
    let L := identityLieStructure Q.pinned.pair.G
    letI := L.lieRing
    D.Y →ₗ[ℤ] Lie (RationalField.{u}) Q.pinned.pair.G.val := by
  let L := identityLieStructure Q.pinned.pair.G
  letI := L.lieRing
  let f := (pointMap Q.pinned.pair.T.inclusion dualAlgebra).comp
    (cocharacterEvaluation Q dualAlgebra dualUnit.{u})
  refine AddMonoidHom.toIntLinearMap
    { toFun := markedCocharacterTangent Q
      map_zero' := Subtype.ext (map_one f)
      map_add' := fun x y => Subtype.ext (map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) }

private def dualUnitWith (a : RationalField.{u}) : (DualNumber (RationalField.{u}))ˣ :=
  Units.map (dualNumberScale a).toMonoidHom dualUnit.{u}

private theorem dualUnitWith_coe (a : RationalField.{u}) :
    (dualUnitWith a : DualNumber (RationalField.{u})) = ⟨1, a⟩ := by
  change dualNumberScale a (dualUnit.{u} : DualNumber RationalField) = _
  rw [dualUnit_val, map_add, map_one, scaled_epsilon]
  apply TrivSqZeroExt.ext
  · change 1 + a * 0 = 1
    simp
  · change 0 + (a * 1 + 0 * 0) = a
    simp

private theorem units_eq_dualUnitWith (s : (DualNumber (RationalField.{u}))ˣ)
    (hs : (s : DualNumber RationalField).fst = 1) : s = dualUnitWith (s : DualNumber RationalField).snd := by
  apply Units.ext
  rw [dualUnitWith_coe]
  exact TrivSqZeroExt.ext hs rfl

private theorem list_sum_tangent_point (L : IdentityLieStructure Q.pinned.pair.G.val) :
    letI := L.lieRing
    ∀ l : List (Lie (RationalField.{u}) Q.pinned.pair.G.val),
      l.sum.toMul.val = (l.map (fun v => v.toMul.val)).prod := by
  letI := L.lieRing
  have hzero : (0 : Lie (RationalField.{u}) Q.pinned.pair.G.val).toMul.val = 1 := rfl
  have hadd (x y : Lie (RationalField.{u}) Q.pinned.pair.G.val) :
      (x + y).toMul.val = x.toMul.val * y.toMul.val := rfl
  intro l
  induction l with
  | nil => exact hzero
  | cons i l ih => simp only [List.sum_cons, List.map_cons, List.prod_cons, hadd, ih]

private theorem torus_lieBracket (L : IdentityLieStructure Q.pinned.pair.G.val) (v w : D.Y) :
    L.lieRing.toBracket.bracket (markedCocharacterTangent Q v) (markedCocharacterTangent Q w) = 0 := by
  letI := Q.attached.comm
  let k := RationalField.{u}
  let G := Q.pinned.pair.G
  let R := CommAlgCat.of k (TwoVariables k)
  let S : dualAlgebra ⟶ R := CommAlgCat.ofHom (liftS k)
  let T : dualAlgebra ⟶ R := CommAlgCat.ofHom (liftT k)
  let ST : dualAlgebra ⟶ R := CommAlgCat.ofHom (liftST k)
  letI : IsMulCommutative (GroupPoints Q.pinned.pair.T.group R) :=
    (isCommMonObj_iff_isMulCommutative _).mp Q.attached.comm _
  let a := cocharacterPoint (markedCocharacter Q v) R (Units.map S.hom.toMonoidHom dualUnit.{u})
  let b := cocharacterPoint (markedCocharacter Q w) R (Units.map T.hom.toMonoidHom dualUnit.{u})
  have h : Commute a b := mul_comm' a b
  have hcomm := L.commutator_law (markedCocharacterTangent Q v) (markedCocharacterTangent Q w)
  unfold InfinitesimalCommutator.commutator at hcomm
  change mapPoints ST (_ : Lie k G.val).toMul.val =
    mapPoints S (torus Q v dualAlgebra dualUnit.{u}) * mapPoints T (torus Q w dualAlgebra dualUnit.{u}) *
      (mapPoints S (torus Q v dualAlgebra dualUnit.{u}))⁻¹ *
      (mapPoints T (torus Q w dualAlgebra dualUnit.{u}))⁻¹ at hcomm
  rw [map_torus, map_torus] at hcomm
  let x := torus Q v R (Units.map S.hom.toRingHom dualUnit.{u})
  let y := torus Q w R (Units.map T.hom.toRingHom dualUnit.{u})
  have hh : Commute x y := h.map (pointMap Q.pinned.pair.T.inclusion R)
  change mapPoints ST (_ : Lie (RationalField.{u}) G.val).toMul.val = x * y * x⁻¹ * y⁻¹ at hcomm
  have he : x * y * x⁻¹ * y⁻¹ = 1 := by rw [hh.eq]; group
  rw [he] at hcomm

  apply Subtype.ext
  apply mapPoints_injective_of_affine G.property.1 ST (liftST_injective k)
  exact hcomm.trans (map_one (((groupPointsFunctor k).obj G.val).map ST).hom).symm

private theorem markedLieBasis (hcor : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    let L := identityLieStructure Q.pinned.pair.G
    letI := L.lieRing
    letI := L.lieAlgebra
    ∃ (e : D.I → Lie (RationalField.{u}) Q.pinned.pair.G.val)
      (B : Module.Basis (D.base.support ⊕ D.I) (RationalField.{u})
        (Lie (RationalField.{u}) Q.pinned.pair.G.val)),
      (∀ i, IsRootTangent Q z i (e i)) ∧
      (∀ i : D.base.support, B (.inl i) = markedCocharacterTangent Q (D.datum.coroot i)) ∧
      ∀ i, B (.inr i) = e i := by
  classical
  let L := identityLieStructure Q.pinned.pair.G
  letI := L.lieRing
  letI := L.lieAlgebra
  letI : Finite D.I := D.finiteRoots
  letI : Fintype D.I := Fintype.ofFinite D.I
  let R := dualAlgebra.{u}
  let S := CommAlgCat.of (RationalField.{u}) (RationalField.{u})
  obtain ⟨e, he⟩ := Classical.skolem.mp (fun i => rootTangent_exists_nonzero Q z i)
  let r := Fintype.card D.base.support
  let equiv : D.base.support ≃ Fin r := Fintype.equivFin _
  let b := (simpleCorootBasis D hcor).reindex equiv
  let n := (Finset.univ.filter (fun i : D.I => ¬ D.base.IsPos i)).toList
  let p := (Finset.univ.filter (fun i : D.I => D.base.IsPos i)).toList
  have hn : Enumerates n {i | ¬ D.base.IsPos i} := by
    exact ⟨Finset.nodup_toList _, fun i => by simp [n]⟩
  have hp : Enumerates p {i | D.base.IsPos i} := by
    exact ⟨Finset.nodup_toList _, fun i => by simp [p]⟩
  let Index := D.I ⊕ Fin r
  let E : Index → Lie (RationalField.{u}) Q.pinned.pair.G.val := Sum.elim e (fun j => markedCocharacterTangent Q (b j))
  let b₀ := Pi.basisFun (RationalField.{u}) Index
  let f := b₀.constr (RationalField.{u}) E
  have hf (a : Index → (RationalField.{u})) : (f a).toMul.val =
      cellPoint Q z b n p R (fun i => TrivSqZeroExt.inr (a (.inl i))) (fun j => dualUnitWith (a (.inr j))) := by
    let l := cellOrder (D := D) (r := r) n p
    have hnodup : l.Nodup := cellOrder_nodup hn hp
    have hmem : ∀ i, i ∈ l := cellOrder_mem hn hp
    have hl : l.toFinset = Finset.univ := Finset.eq_univ_of_forall fun i => List.mem_toFinset.mpr (hmem i)
    have hs : f a = (l.map (fun i => a i • E i)).sum := by
      change b₀.constr (RationalField.{u}) E a = _
      rw [Module.Basis.constr_apply_fintype, ← hl, List.sum_toFinset _ hnodup]
      simp only [b₀, Pi.basisFun_equivFun, LinearEquiv.refl_apply]
    have hscaled (i : Index) : (a i • E i).toMul.val = i.elim
        (fun j => root Q z j R (TrivSqZeroExt.inr (a (.inl j))))
        (fun j => torus Q (b j) R (dualUnitWith (a (.inr j)))) := by
      let g : R ⟶ R := CommAlgCat.ofHom (dualNumberScale (a i))
      change mapPoints g (E i).toMul.val = _
      cases i with
      | inl j =>
        change mapPoints g (e j).toMul.val = _
        rw [(he j).1, map_root]
        change root Q z j R (dualNumberScale (a (.inl j)) DualNumber.eps) =
          root Q z j R (TrivSqZeroExt.inr (a (.inl j)))
        congr 1
        apply TrivSqZeroExt.ext
        · rw [dualNumberScale, TrivSqZeroExt.fst_map]
          rfl
        · rw [dualNumberScale, TrivSqZeroExt.snd_map]
          change a (.inl j) * 1 = _
          exact mul_one _
      | inr j =>
        change mapPoints g (torus Q (b j) R dualUnit.{u}) = _
        rw [map_torus]
        rfl
    rw [hs, list_sum_tangent_point Q L]
    simp only [List.map_map, Function.comp_def, hscaled, l, cellOrder, List.map_append,
      List.prod_append, Sum.elim_inl, Sum.elim_inr, cellPoint, mul_assoc]
  have hinj : Function.Injective f := by
    intro a a' heq
    have h := congrArg (fun e : Lie (RationalField.{u}) Q.pinned.pair.G.val => e.toMul.val) heq
    rw [hf, hf] at h
    have hh : ((fun i : D.I => (TrivSqZeroExt.inr (a (.inl i)) : R)), fun j : Fin r => dualUnitWith (a (.inr j))) =
        ((fun i : D.I => (TrivSqZeroExt.inr (a' (.inl i)) : R)), fun j : Fin r => dualUnitWith (a' (.inr j))) :=
      cellPoint_injective Q z b n p hn hp R h
    funext i
    cases i with
    | inl i => exact congrArg TrivSqZeroExt.snd (congrFun (congrArg Prod.fst hh) i)
    | inr i =>
      have heq := congrFun (congrArg Prod.snd hh) i
      have hu := congrArg Units.val heq
      rw [dualUnitWith_coe, dualUnitWith_coe] at hu
      exact congrArg TrivSqZeroExt.snd hu
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨a, s, hs⟩ := cellPoint_covers_tangents Q z b n p hn hp y
    have h := y.toMul.property
    change mapPoints (dualReduction (RationalField.{u})) y.toMul.val = 1 at h
    rw [hs, map_cellPoint, ← cellPoint_identity Q z b n p S] at h
    have hc : ((fun i => (dualReduction (RationalField.{u})).hom (a i)),
        (fun j => Units.map (dualReduction (RationalField.{u})).hom.toMonoidHom (s j))) =
        ((0 : D.I → S), (1 : Fin r → Sˣ)) := cellPoint_injective Q z b n p hn hp S h
    let v : Index → (RationalField.{u}) := Sum.elim (fun i => (a i).snd) (fun j => (s j : DualNumber (RationalField.{u})).snd)
    refine ⟨v, Subtype.ext ?_⟩
    change (f v).toMul.val = y.toMul.val
    rw [hf, hs]
    have ha (i : D.I) : (TrivSqZeroExt.inr (v (.inl i)) : DualNumber (RationalField.{u})) = a i :=
      TrivSqZeroExt.ext ((congrFun (congrArg Prod.fst hc) i).symm) rfl
    have ht (j : Fin r) : dualUnitWith (v (.inr j)) = s j :=
      (units_eq_dualUnitWith (s j) (congrArg Units.val (congrFun (congrArg Prod.snd hc) j))).symm
    rw [funext ha, funext ht]
  let B' := b₀.map (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)
  have hB (i : Index) : B' i = E i := (b₀.constr_basis (RationalField.{u}) E i)
  let re : (D.base.support ⊕ D.I) ≃ Index :=
    (Equiv.sumCongr equiv (Equiv.refl D.I)).trans (Equiv.sumComm _ _)
  let B := B'.reindex re.symm
  refine ⟨e, B, fun i => (he i).1, ?_, ?_⟩
  · intro i
    rw [show B = B'.reindex re.symm from rfl, Module.Basis.reindex_apply, Equiv.symm_symm]
    change B' (.inr (equiv i)) = _
    rw [hB]
    simp only [E, Sum.elim_inr, b, Module.Basis.reindex_apply, Equiv.symm_apply_apply, simpleCorootBasis_apply]
  · intro i
    rw [show B = B'.reindex re.symm from rfl, Module.Basis.reindex_apply, Equiv.symm_symm]
    change B' (.inl i) = _
    exact hB (.inl i)

end MarkedLieBasis

section ChevalleyCoordinates

open Specs.Pinning (RootCoordinate RootVector)
open Specs.RationalRealization (ComplexCartan SerreStructure SerreBaseChange RationalSerreDecomposition)
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open private rescale rescale_point coordinate_ext from LinearAlgebraicGroups.Classification.Pinning

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})} (Q : Realization D A)

private theorem exists_pinnedRootCoordinates :
    ∃ z : RootCoordinates Q, ∀ i : D.base.support, z i.val = Q.pinned.pin (Q.simpleRoot i) := by
  classical
  have h (i : D.I) : Nonempty (RootCoordinate A Q.pinned.pair.T
      (Q.pinned.roots (rootIndex Q i)).val (rootIndex Q i).val) := by
    obtain ⟨f, _, _⟩ := Pinning.coordinateVectors A Q.pinned.pair (rootIndex Q i)
      (Q.pinned.roots (rootIndex Q i)).val (Q.pinned.roots (rootIndex Q i)).property
    obtain ⟨x, hx, hx'⟩ := (rootIndex Q i).property.2
    exact ⟨f.symm ⟨x, hx, hx'⟩⟩
  let z : RootCoordinates Q := fun i => if hi : i ∈ D.base.support then
    Q.pinned.pin (Q.simpleRoot ⟨i, hi⟩) else Classical.choice (h i)
  exact ⟨z, fun i => by simp only [z, dif_pos i.property]⟩

/-- The marked rational model admits a Chevalley normalization extending its
specified simple root coordinates. -/
theorem exists_chevalleyCoordinates (hC : ComplexCartan.{u}) (hS : SerreStructure.{u})
    (hE : SerreBaseChange.{u}) (hdec : RationalSerreDecomposition.{u})
    (hcoroot : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤) :
    ∃ z : RootCoordinates Q, IsChevalley Q z := by
  classical
  let L := identityLieStructure Q.pinned.pair.G
  letI := L.lieRing
  letI := L.lieAlgebra
  letI : CharZero (RationalField.{u}) := ⟨fun a b h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩
  obtain ⟨z, hz⟩ := exists_pinnedRootCoordinates Q
  obtain ⟨t, B, ht, hH, hB⟩ := markedLieBasis Q z hcoroot
  let h (i : D.I) : Lie (RationalField.{u}) Q.pinned.pair.G.val := markedCocharacterTangent Q (D.datum.coroot i)
  have hweight (a : D.base.support ⊕ D.I) :
      HasCartanWeight (K := (RationalField.{u})) (fun i : D.base.support => h i)
        (a.elim (fun _ => 0) D.datum.root) (B a) := by
    intro j
    cases a with
    | inl i =>
      simpa only [hH, Sum.elim_inl, map_zero, LinearMap.zero_apply, Int.cast_zero, zero_smul] using
        torus_lieBracket Q L (D.datum.coroot j) (D.datum.coroot i)
    | inr i =>
      rw [hB]
      have hh := cocharacterTangent_bracket_root Q z i (D.datum.coroot j) L (h j) (t i) (ht i) rfl
      rw [L.scalar_law] at hh
      exact hh
  have hdiag (i : D.I) : ⁅h i, B (.inr i)⁆ = (2 : (RationalField.{u})) • B (.inr i) := by
    rw [hB]
    have hh := cocharacterTangent_bracket_root Q z i (D.datum.coroot i) L (h i) (t i) (ht i) rfl
    rw [L.scalar_law] at hh
    change ⁅h i, t i⁆ = (D.datum.pairing i i : (RationalField.{u})) • t i at hh
    rwa [D.datum.pairing_same, Int.cast_ofNat] at hh
  have hbr (i : D.I) : ∃ c : (RationalField.{u})ˣ, ⁅B (.inr i), B (.inr (oppositeIndex D i))⁆ = (c : (RationalField.{u})) • h i := by
    let j := oppositeIndex D i
    have hij : D.datum.root j = -D.datum.root i := root_oppositeIndex D i
    obtain ⟨w, hw⟩ := exists_linkedRootCoordinates Q z i j hij
    obtain ⟨a, ha, _⟩ := Pinning.coordinateChanges A Q.pinned.pair.T
      (Q.pinned.roots (rootIndex Q i)).val (rootIndex Q i).val (w i) (z i)
    obtain ⟨b, hb, _⟩ := Pinning.coordinateChanges A Q.pinned.pair.T
      (Q.pinned.roots (rootIndex Q j)).val (rootIndex Q j).val (w j) (z j)
    obtain ⟨x, hx, _⟩ := rootTangent_exists_nonzero Q w i
    obtain ⟨y, hy, _⟩ := rootTangent_exists_nonzero Q w j
    have he : ⁅x, y⁆ = h i := oppositeRootBracket_of_factorization Q w i j hij hw L x y (h i) hx hy rfl
    have h₁ : t i = (a : (RationalField.{u})) • x := rootTangent_scaling Q z w i a ha L (t i) x (ht i) hx
    have h₂ : t j = (b : (RationalField.{u})) • y := rootTangent_scaling Q z w j b hb L (t j) y (ht j) hy
    refine ⟨a * b, ?_⟩
    change ⁅B (.inr i), B (.inr j)⁆ = _
    rw [hB, hB, h₁, h₂, smul_lie, lie_smul, smul_smul, he, Units.val_mul]
  obtain ⟨c, hc, hop, hadd, hzero⟩ := normalizeRootVectors hC hS hE hdec B h hweight
    (simpleCorootEvaluations_injective D hcoroot) hH hbr hdiag
  let w : RootCoordinates Q := fun i => rescale (z i) (c i)
  let e (i : D.I) := (c i : (RationalField.{u})) • B (.inr i)
  have hR (i : D.I) : IsRootTangent Q w i (e i) := by
    obtain ⟨x, hx, _⟩ := rootTangent_exists_nonzero Q w i
    have hs : ∀ (R : TestAlgebra (RationalField.{u})) (a : R),
        root Q w i R a = root Q z i R (algebraMap (RationalField.{u}) R (c i : (RationalField.{u})) * a) := rescale_point (z i) (c i)
    have he : x = (c i : (RationalField.{u})) • t i := rootTangent_scaling Q w z i (c i) hs L x (t i) hx (ht i)
    have heq : e i = x := by
      dsimp only [e]
      rw [hB, he]
    rw [heq]
    exact hx
  let B' := B.unitsSMul (Sum.elim (fun _ => 1) c)
  have hLeft (i : D.base.support) : B' (.inl i) = h i := by
    simp [B', Module.Basis.unitsSMul_apply, hH, h]
  have hRight (i : D.I) : B' (.inr i) = e i := by
    simp only [B', Module.Basis.unitsSMul_apply, Sum.elim_inr, Units.smul_def, e]
  have hCartan (i j : D.I) : ⁅h i, h j⁆ = 0 :=
    torus_lieBracket Q L (D.datum.coroot i) (D.datum.coroot j)
  have hCartanRoot (i j : D.I) : ⁅h i, e j⁆ = D.datum.pairing j i • e j := by
    rw [← Int.cast_smul_eq_zsmul (RationalField.{u})]
    exact cocharacterTangent_bracket_root Q w j (D.datum.coroot i) L (h i) (e j) (hR j) rfl
  refine ⟨w, ?_, L, e, h, B', fun i => ⟨hR i, rfl⟩, hLeft, hRight, hop, hadd, hzero,
    hCartan, hCartanRoot, ?_⟩
  · intro i
    rw [← hz i]
    change rescale (z i) (c i) = z i
    rw [hc i]
    apply coordinate_ext
    intro R a
    rw [rescale_point, Units.val_one, map_one, one_mul]
  · let S := Submodule.span ℤ (Set.range B')
    have hgen (a : D.base.support ⊕ D.I) : B' a ∈ S :=
      Submodule.subset_span (Set.mem_range_self a)
    have hLeftMem (i : D.base.support) : h i ∈ S := hLeft i ▸ hgen (.inl i)
    have hRightMem (i : D.I) : e i ∈ S := hRight i ▸ hgen (.inr i)
    have hMem (i : D.I) : h i ∈ S := by
      let f := markedCocharacterTangentLinear Q
      let b := simpleCorootBasis D hcoroot
      have he := congrArg f (b.sum_repr (D.datum.coroot i))
      rw [map_sum] at he
      change (∑ j, f (b.repr (D.datum.coroot i) j • b j)) = h i at he
      rw [← he]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul, simpleCorootBasis_apply]
      exact S.smul_mem _ (hLeftMem j)
    have hBracket (a b : D.base.support ⊕ D.I) : ⁅B' a, B' b⁆ ∈ S := by
      cases a with
      | inl i =>
        cases b with
        | inl j => rw [hLeft, hLeft, hCartan]; exact S.zero_mem
        | inr j => rw [hLeft, hRight, hCartanRoot]; exact S.smul_mem _ (hRightMem j)
      | inr i =>
        cases b with
        | inl j =>
          rw [hRight, hLeft, ← lie_skew, hCartanRoot]
          exact S.neg_mem (S.smul_mem _ (hRightMem i))
        | inr j =>
          rw [hRight, hRight]
          by_cases hs : D.datum.root i + D.datum.root j = 0
          · rw [hop i j (eq_neg_of_add_eq_zero_right hs)]
            exact hMem i
          · by_cases hroot : D.datum.root i + D.datum.root j ∈ Set.range D.datum.root
            · obtain ⟨k, hk⟩ := hroot
              obtain ⟨_, _, n, _, _, hlie, _⟩ := hadd i j k hk.symm
              rw [hlie]
              exact S.smul_mem n (hRightMem k)
            · rw [hzero i j hs hroot]
              exact S.zero_mem
    intro a b c
    let Z := (Algebra.linearMap ℤ (RationalField.{u})).range
    have hcoord : S ≤ Z.comap ((B'.coord c).restrictScalars ℤ) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change ∃ n : ℤ, (n : RationalField.{u}) = B'.repr (B' i) c
      rw [B'.repr_self_apply]
      split
      · exact ⟨1, Int.cast_one⟩
      · exact ⟨0, Int.cast_zero⟩
    obtain ⟨n, hn⟩ := hcoord (hBracket a b)
    exact ⟨n, hn.symm⟩

end ChevalleyCoordinates




section ReversedRootPair

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private def swapConeRoots (i j : D.I) : ConeRoot i j ≃ ConeRoot j i where
  toFun a := ⟨a.rightDegree, a.leftDegree, a.index, a.root_eq.trans (add_comm _ _)⟩
  invFun a := ⟨a.rightDegree, a.leftDegree, a.index, a.root_eq.trans (add_comm _ _)⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro a; cases a; rfl

/-- Swapping a root pair inverts its commutator. Reversing the enumeration
and negating the integer coefficients gives the relation in the new order. -/
private theorem independentRootRelation_swap (i j : D.I)
    (h : ∀ l : List (ConeRoot j i), Enumerates l Set.univ →
      ∃ c : ConeRoot j i → ℤ, ∀ (R : TestAlgebra (RationalField.{u})) (y x : R),
        root Q z j R y * root Q z i R x * (root Q z j R y)⁻¹ * (root Q z i R x)⁻¹ =
          (l.map (fun a => root Q z a.index R
            ((c a : R) * y ^ (a.leftDegree : ℕ) * x ^ (a.rightDegree : ℕ)))).prod)
    (l : List (ConeRoot i j)) (hl : Enumerates l Set.univ) :
    ∃ c : ConeRoot i j → ℤ, ∀ (R : TestAlgebra (RationalField.{u})) (x y : R),
      root Q z i R x * root Q z j R y * (root Q z i R x)⁻¹ * (root Q z j R y)⁻¹ =
        (l.map (fun a => root Q z a.index R
          ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod := by
  let e := swapConeRoots i j
  let l' := (l.map e).reverse
  have hl' : Enumerates l' Set.univ := by
    refine ⟨List.nodup_reverse.mpr (hl.1.map e.injective), ?_⟩
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    simp [l', hl.2 b]
  obtain ⟨c, hc⟩ := h l' hl'
  refine ⟨fun b => -c (e b), fun R x y => ?_⟩
  have he := congrArg (Inv.inv : GroupPoints Q.pinned.pair.G.val R → _) (hc R y x)
  dsimp only [l'] at he
  rw [List.map_reverse, List.prod_inv_reverse, List.map_reverse, List.reverse_reverse,
    List.map_map, List.map_map] at he
  simp only [mul_inv_rev, inv_inv, ← mul_assoc] at he
  rw [he]
  simp only [Function.comp_def]
  apply congrArg List.prod
  apply List.map_congr_left
  intro b _
  have hroot (s : R) : (root Q z b.index R s)⁻¹ = root Q z b.index R (-s) :=
    ((rootHom Q z b.index R).map_inv (Multiplicative.ofAdd s)).symm
  change (root Q z b.index R ((c (e b) : R) * y ^ (b.rightDegree : ℕ) * x ^ (b.leftDegree : ℕ)))⁻¹ = _
  rw [hroot, Int.cast_neg]
  congr 1
  ring

end ReversedRootPair


namespace RankTwo

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)

private theorem coneShape_second {C : Finset Lattice} (h : coneShape C)
    {r s : ℤ} (hm : (r,s) ∈ C) : s = 1 ∨ s = 2 := by
  rcases h with h | h | h | h | h <;>
    simp only [h, Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hm
  all_goals grind

private theorem coneShape_degreeTwo_unique {C : Finset Lattice} (h : coneShape C)
    {r s : ℤ} (hr : (r,2) ∈ C) (hs : (s,2) ∈ C) : r = s := by
  rcases h with h | h | h | h | h <;>
    simp only [h, Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hr hs
  all_goals grind

private theorem step_eq_zsmul (a b : Lattice) (n : ℤ) :
    step a b n = b + n • a := rfl

private theorem map_step {X : Type u} [AddCommGroup X] (f : Lattice →+ X) (a b : Lattice) (n : ℤ) :
    f (step a b n) = f b + n • f a := by
  rw [step_eq_zsmul, map_add, map_zsmul]

private theorem string_sum_eq (a b : Lattice) (d e : ℕ) :
    step (step a b d) (step a b e) 1 = ((d+e : ℕ) : ℤ) • a + (2 : ℤ) • b := by
  apply Prod.ext
  · change (b.1 + (e : ℤ) * a.1) + 1 * (b.1 + (d : ℤ) * a.1) = (↑(d+e) : ℤ) * a.1 + 2 * b.1
    push_cast
    ring
  · change (b.2 + (e : ℤ) * a.2) + 1 * (b.2 + (d : ℤ) * a.2) = (↑(d+e) : ℤ) * a.2 + 2 * b.2
    push_cast
    ring

private theorem rootString_eq_range {R : Finset Lattice} {a b : Lattice} {p q : ℕ}
    (hq : q ≤ 3) (hstr : ∀ n : ℤ, step a b n ∈ R ↔ -(p : ℤ) ≤ n ∧ n ≤ q) :
    rootString R a b = Finset.range (q+1) := by
  ext d
  simp only [rootString, Finset.mem_filter, Finset.mem_range, hstr]
  omega

private theorem sum_bracket_pairs {M : Type v} [AddCommGroup M] {R : Finset Lattice}
    {a b : Lattice} {q : ℕ} (hr : rootString R a b = Finset.range (q+1))
    (g : ℕ × ℕ → M) (hg : ∀ i j : ℕ, i < j → j ≤ q →
      step (step a b i) (step a b j) 1 ∉ R → g (i,j) = 0) :
    ∑ ij ∈ bracketPairs R a b, g ij = ∑ j ∈ Finset.range (q+1), ∑ i ∈ Finset.range j, g (i,j) := by
  classical
  let P := ((Finset.range (q+1)) ×ˢ (Finset.range (q+1))).filter (fun ij => ij.1 < ij.2)
  have he (ij : ℕ × ℕ) : ij ∈ P ↔ ij.2 ∈ Finset.range (q+1) ∧ ij.1 ∈ Finset.range ij.2 := by
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [← Finset.sum_finset_product_right P _ _ he]
  refine Finset.sum_subset ?_ ?_
  · intro ij hij
    simp only [bracketPairs, hr, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij
    exact (he ij).mpr ⟨Finset.mem_range.mpr hij.1.2, Finset.mem_range.mpr hij.2.1⟩
  · intro ij hij hnot
    have hmem := (he ij).mp hij
    have hi := Finset.mem_range.mp hmem.2
    have hj := Finset.mem_range.mp hmem.1
    refine hg ij.1 ij.2 hi (by omega) (fun hh => hnot ?_)
    exact Finset.mem_filter.mpr ⟨hr.symm ▸ Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), hmem.1⟩, hi, hh⟩

end RankTwo


section StringOrder

variable {D : BasedRootDatum.{u}} {i j : D.I}

private theorem rootDegrees_eq (h : IndependentRoots i j) {r s r' s' : ℕ}
    (he : r • D.datum.root i + s • D.datum.root j =
      r' • D.datum.root i + s' • D.datum.root j) : r = r' ∧ s = s' := by
  have ht := LinearIndependent.eq_of_pair (RankTwo.independentRoots_int h)
    (s := (r : ℤ)) (t := (s : ℤ)) (s' := (r' : ℤ)) (t' := (s' : ℤ))
    (by simpa only [natCast_zsmul] using he)
  exact ⟨Int.ofNat.inj ht.1, Int.ofNat.inj ht.2⟩

private theorem rootCombination_ne_zero (h : IndependentRoots i j) (r s : ℕ) (hs : 0 < s) :
    r • D.datum.root i + s • D.datum.root j ≠ 0 := by
  intro hz
  have he : r • D.datum.root i + s • D.datum.root j = 0 • D.datum.root i + 0 • D.datum.root j := by
    simpa only [zero_smul, add_zero] using hz
  exact (Nat.ne_of_gt hs) (rootDegrees_eq h he).2

private def isStringConeRoot (a : ConeRoot i j) : Bool :=
  decide ((a.rightDegree : ℕ) = 1)

private theorem stringConeRoot_index (p q : ℕ) (hstr : IsRootString i j p q)
    (s : ℕ → D.I) (hs : ∀ d ≤ q, D.datum.root (s d) = D.datum.root j + (d : ℤ) • D.datum.root i)
    (a : ConeRoot i j) (ha : (a.rightDegree : ℕ) = 1) :
    (a.leftDegree : ℕ) ≤ q ∧ s (a.leftDegree : ℕ) = a.index := by
  have he : D.datum.root a.index = D.datum.root j + ((a.leftDegree : ℕ) : ℤ) • D.datum.root i := by
    rw [a.root_eq, ha, one_smul, natCast_zsmul, add_comm]
  have hq := (hstr ((a.leftDegree : ℕ) : ℤ)).mp ⟨a.index, he⟩
  have h : (a.leftDegree : ℕ) ≤ q := by exact_mod_cast hq.2
  exact ⟨h, D.datum.root.injective ((hs _ h).trans he.symm)⟩

private theorem stringConeRoot_degrees (h : IndependentRoots i j) {p q : ℕ}
    (hstr : IsRootString i j p q)
    (s : ℕ → D.I) (hs : ∀ d ≤ q, D.datum.root (s d) = D.datum.root j + (d : ℤ) • D.datum.root i)
    (l : List (ConeRoot i j)) (hl : Enumerates l Set.univ) :
    (((l.filter isStringConeRoot).map fun a : ConeRoot i j => (a.leftDegree : ℕ)) ++ [0]).Perm (List.range (q+1)) := by
  classical
  have hinj : ∀ a ∈ l.filter isStringConeRoot, ∀ b ∈ l.filter isStringConeRoot,
      (a.leftDegree : ℕ) = (b.leftDegree : ℕ) → a = b := by
    intro a ha b hb he
    have ha₁ : (a.rightDegree : ℕ) = 1 := by simpa [isStringConeRoot] using (List.mem_filter.mp ha).2
    have hb₁ : (b.rightDegree : ℕ) = 1 := by simpa [isStringConeRoot] using (List.mem_filter.mp hb).2
    apply coneRoot_index_injective h
    exact ((stringConeRoot_index p q hstr s hs a ha₁).2.symm.trans
      ((congrArg s he).trans (stringConeRoot_index p q hstr s hs b hb₁).2))
  have hzero : 0 ∉ (l.filter isStringConeRoot).map (fun a : ConeRoot i j => (a.leftDegree : ℕ)) := by
    rintro hh
    obtain ⟨a, _, he⟩ := List.mem_map.mp hh
    exact a.leftDegree.pos.ne' he
  have hn : (((l.filter isStringConeRoot).map fun a : ConeRoot i j => (a.leftDegree : ℕ)) ++ [0]).Nodup := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · apply List.Nodup.map_on _ (hl.1.filter _)
      exact hinj
    · intro n hn m hm he
      have h : m = 0 := List.mem_singleton.mp hm
      exact hzero ((he.trans h) ▸ hn)
  apply (List.perm_ext_iff_of_nodup hn List.nodup_range).mpr
  intro n
  simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_filter,
    isStringConeRoot, decide_eq_true_eq, List.mem_range]
  constructor
  · intro hm
    rcases hm with ⟨a, ⟨_, ha⟩, he⟩ | he
    · rw [← he]
      exact Nat.lt_succ_iff.mpr (stringConeRoot_index p q hstr s hs a ha).1
    · omega
  · intro hn
    by_cases he : n = 0
    · exact Or.inr he
    · have hnp : 0 < n := Nat.pos_of_ne_zero he
      let a : ConeRoot i j := ⟨⟨n, hnp⟩, 1, s n, by rw [hs _ (by omega), natCast_zsmul]; simp [add_comm]⟩
      exact Or.inl ⟨a, ⟨(hl.2 a).mpr (Set.mem_univ a), rfl⟩, rfl⟩

private theorem list_product_filter_single {ι G : Type*} [Monoid G] [DecidableEq ι]
    (l : List ι) (hn : l.Nodup) (P : ι → Bool) (f : ι → G) {a : ι}
    (ha : P a = false) (h₁ : ∀ i ∈ l, P i = false → i ≠ a → f i = 1)
    (hc : ∀ i ∈ l, P i = true → Commute (f a) (f i)) :
    (l.map f).prod = ((l.filter P).map f).prod * (if a ∈ l then f a else 1) := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hTail (i : ι) (hi : i ∈ l) : i ∈ b :: l := List.mem_cons_of_mem _ hi
    have hh := ih (List.nodup_cons.mp hn).2
      (fun i hi => h₁ i (hTail i hi)) (fun i hi => hc i (hTail i hi))
    have hb : b ∈ b :: l := List.mem_cons_self
    have hprod (hs : ∀ i ∈ l, P i = true → Commute (f a) (f i)) :
        Commute (f a) ((l.filter P).map f).prod := by
      apply Commute.list_prod_right
      intro j hj
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
      exact hs i (List.mem_filter.mp hi).1 (List.mem_filter.mp hi).2
    cases hP : P b with
    | true =>
      have hab : a ≠ b := fun e => by subst b; rw [ha] at hP; contradiction
      simp only [List.map_cons, List.prod_cons, List.filter_cons_of_pos hP, List.mem_cons,
        hab, false_or, hh, mul_assoc]
    | false =>
      simp only [List.map_cons, List.prod_cons, List.filter_cons, hP, Bool.false_eq_true, ite_false,
        hh, List.mem_cons]
      by_cases hEq : a = b
      · subst b
        have hnot : a ∉ l := (List.nodup_cons.mp hn).1
        rw [if_pos (Or.inl rfl), if_neg hnot, mul_one, (hprod fun i hi => hc i (hTail i hi)).eq]
      · simp [h₁ b hb hP (Ne.symm hEq), hEq]

end StringOrder


section StringCollection

variable {M : Type v} [Ring M] [Algebra ℚ M]

private theorem exp_conjugate_eq {a b : M} (ha : IsNilpotent a) (hb : IsNilpotent b) :
    IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) =
      IsNilpotent.exp (IsNilpotent.exp a * b * IsNilpotent.exp (-a)) := by
  let x := IsNilpotent.exp a
  let y := IsNilpotent.exp (-a)
  have hxy : x * y = 1 := ha.exp_mul_exp_neg_self
  have hyx : y * x = 1 := ha.exp_neg_mul_exp_self
  let F : M →+* M :=
    { toFun := fun z => x * z * y
      map_zero' := by simp
      map_one' := by rw [mul_one, hxy]
      map_add' := fun r s => by rw [mul_add, add_mul]
      map_mul' := fun r s => by
        calc
          x * (r * s) * y = x * r * (y * x) * s * y := by rw [hyx, mul_one, mul_assoc x r s]
          _ = _ := by noncomm_ring }
  exact IsNilpotent.map_exp hb F

private theorem orderedBracketSum_append_single (l : List M) (v : M) :
    orderedBracketSum (l ++ [v]) = orderedBracketSum l + (l.sum * v - v * l.sum) := by
  induction l with
  | nil => simp [orderedBracketSum]
  | cons a l ih =>
    simp only [List.cons_append, orderedBracketSum, List.sum_cons, List.sum_append,
      List.sum_nil, add_zero, ih]
    noncomm_ring

private theorem orderedBracketSum_range (v : ℕ → M) (n : ℕ) :
    orderedBracketSum ((List.range n).map v) =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range j, (v i * v j - v j * v i) := by
  induction n with
  | zero => simp [orderedBracketSum]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, orderedBracketSum_append_single,
      ih, Finset.sum_range_succ]
    have h : ((List.range n).map v).sum = ∑ i ∈ Finset.range n, v i := by
      rw [← List.sum_toFinset _ List.nodup_range]
      simp only [List.toFinset_range]
    rw [h, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

private theorem two_nsmul_exp_correction (c : ℤ) (v : M) :
    (-(1/2 : ℚ)) • ((2 : ℕ) • (c • v)) = (-c) • v := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, Int.cast_neg]
  norm_num

/-- Collect a conjugated string in any order. All nonzero commutators
lie in a single central line, and its canonical correction is even. -/
private theorem collect_exp_string (a b v : M) (ha : IsNilpotent a) (hb : IsNilpotent b)
    (hv : IsNilpotent v)
    (l l₀ : List M) (hperm : (l ++ [b]).Perm l₀)
    (hn : ∀ x ∈ l₀, IsNilpotent x) (hc : ∀ x ∈ l₀, Commute x v)
    (hbr : ∀ x ∈ l₀, ∀ y ∈ l₀, ∃ n : ℤ, x * y - y * x = n • v)
    (hconj : IsNilpotent.exp a * b * IsNilpotent.exp (-a) = l₀.sum)
    (d : ℤ) (hd : orderedBracketSum l₀ = (2 : ℕ) • (d • v)) :
    ∃ c : ℤ, IsNilpotent.exp a * IsNilpotent.exp b * IsNilpotent.exp (-a) *
      IsNilpotent.exp (-b) = (l.map IsNilpotent.exp).prod * IsNilpotent.exp (c • v) := by
  let Z : Submodule ℚ M := ℚ ∙ v
  let W : Submodule ℤ M := ℤ ∙ v
  have hnZ (z : M) (hz : z ∈ Z) : IsNilpotent z := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact hv.smul _
  have hcZ (x : M) (hx : Commute x v) (z : M) (hz : z ∈ Z) : Commute x z := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact hx.smul_right r
  have hZZ (z : M) (hz : z ∈ Z) (w : M) (hw : w ∈ Z) : Commute z w := by
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact hcZ _ ((Commute.refl v).smul_left r) w hw
  have hbZ (x : M) (hx : x ∈ l ++ [b]) (y : M) (hy : y ∈ l ++ [b]) : x * y - y * x ∈ Z := by
    obtain ⟨n, h⟩ := hbr x (hperm.mem_iff.mp hx) y (hperm.mem_iff.mp hy)
    rw [h, ← Int.cast_smul_eq_zsmul ℚ]
    exact Z.smul_mem _ (Submodule.mem_span_singleton_self _)
  have hbW (x : M) (hx : x ∈ l ++ [b]) (y : M) (hy : y ∈ l ++ [b]) : x * y - y * x ∈ W := by
    obtain ⟨n, h⟩ := hbr x (hperm.mem_iff.mp hx) y (hperm.mem_iff.mp hy)
    rw [h]
    exact W.smul_mem _ (Submodule.mem_span_singleton_self _)
  obtain ⟨w, hw, heq⟩ := orderedBracketSum_perm W hperm hbW
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hsum : orderedBracketSum (l ++ [b]) = (2 : ℕ) • ((d+n) • v) := by
    rw [heq, hd, add_zsmul, smul_add]
  have hbmem : b ∈ l ++ [b] := List.mem_append_right _ List.mem_cons_self
  have hbc : Commute b ((-(d+n)) • v) := by
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact (hc b (hperm.mem_iff.mp hbmem)).smul_right _
  have hv' : IsNilpotent ((-(d+n)) • v) := by
    rw [← Int.cast_smul_eq_zsmul ℚ]
    exact hv.smul _
  have hs := (nilpotent_exp_list_sum_of_central_brackets Z hnZ hZZ (l ++ [b])
    (fun x hx => hn x (hperm.mem_iff.mp hx)) (fun x hx => hcZ x (hc x (hperm.mem_iff.mp hx))) hbZ).2
  rw [hperm.sum_eq, hsum, two_nsmul_exp_correction, ← hconj, ← exp_conjugate_eq ha hb,
    List.map_append, List.map_singleton, List.prod_append, List.prod_singleton] at hs
  refine ⟨-(d+n), ?_⟩
  let p := (l.map IsNilpotent.exp).prod
  let z := IsNilpotent.exp ((-(d+n)) • v)
  have hz : IsNilpotent.exp b * z = z * IsNilpotent.exp b := by
    change _ * IsNilpotent.exp ((-(d+n)) • v) = _
    rw [← IsNilpotent.exp_add_of_commute hbc hb hv', add_comm, IsNilpotent.exp_add_of_commute hbc.symm hv' hb]
  calc
    _ = (p * IsNilpotent.exp b * z) * IsNilpotent.exp (-b) := congrArg (· * IsNilpotent.exp (-b)) hs
    _ = p * (IsNilpotent.exp b * z) * IsNilpotent.exp (-b) := by rw [mul_assoc p]
    _ = (p * z) * (IsNilpotent.exp b * IsNilpotent.exp (-b)) := by rw [hz]; simp only [mul_assoc]
    _ = _ := by rw [hb.exp_mul_exp_neg_self, mul_one]

end StringCollection


section CollectRootPairs

open LieAlgebrasAndRepresentations (RankTwoKind rankTwoCoefficients)
open _root_.LinearAlgebraicGroups.Specs.IntegralRootRelations.RankTwo
  (Lattice step rootString bracketPairs bracketMagnitude backwardLength squaredLength)
open _root_.LinearAlgebraicGroups.Specs (Lie IdentityLieStructure)
open InfinitesimalCommutator (matrixDifferential)
open private matrixDifferentialLinear from LinearAlgebraicGroups.Affine.LieBracket

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

local instance : CharZero (RationalField.{u}) :=
  ⟨fun _ _ h => Nat.cast_injective (R := ℚ) (congrArg ULift.down h)⟩

variable {D : BasedRootDatum.{u}} {A : AdditiveLine (RationalField.{u})}
  (Q : Realization D A) (z : RootCoordinates Q)

private theorem map_rootProduct {R S : TestAlgebra (RationalField.{u})}
    (g : R ⟶ S) {i j : D.I} (l : List (ConeRoot i j)) (c : ConeRoot i j → ℤ) (x y : R) :
    mapPoints g ((l.map (fun a => root Q z a.index R
      ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod) =
      (l.map (fun a => root Q z a.index S
        ((c a : S) * g.hom x ^ (a.leftDegree : ℕ) * g.hom y ^ (a.rightDegree : ℕ)))).prod := by
  let F := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map g).hom
  change F _ = _
  have hroot (a : ConeRoot i j) : F (root Q z a.index R
      ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ))) =
      root Q z a.index S
        ((c a : S) * g.hom x ^ (a.leftDegree : ℕ) * g.hom y ^ (a.rightDegree : ℕ)) := by
    have h := map_root Q z g a.index ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ))
    rw [map_mul, map_mul, map_pow, map_pow, map_intCast] at h
    exact h
  simp only [map_list_prod, List.map_map, Function.comp_def, hroot]

private theorem genericRootCommutator {i j : D.I} (l : List (ConeRoot i j))
    (c : ConeRoot i j → ℤ)
    (h : let R := CommAlgCat.of RationalField.{u} (MvPolynomial (Fin 2) RationalField.{u})
         let x : R := MvPolynomial.X 0
         let y : R := MvPolynomial.X 1
         root Q z i R x * root Q z j R y * (root Q z i R x)⁻¹ * (root Q z j R y)⁻¹ =
          (l.map (fun a => root Q z a.index R
            ((c a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod) :
    ∀ (S : TestAlgebra (RationalField.{u})) (x y : S),
      root Q z i S x * root Q z j S y * (root Q z i S x)⁻¹ * (root Q z j S y)⁻¹ =
        (l.map (fun a => root Q z a.index S
          ((c a : S) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod := by
  intro S x y
  let R := CommAlgCat.of RationalField.{u} (MvPolynomial (Fin 2) RationalField.{u})
  let g : R ⟶ S := CommAlgCat.ofHom (MvPolynomial.aeval (fun n : Fin 2 => if n = 0 then x else y))
  let X : R := MvPolynomial.X 0
  let Y : R := MvPolynomial.X 1
  have hX : g.hom X = x := by change MvPolynomial.aeval _ (MvPolynomial.X 0) = _; simp
  have hY : g.hom Y = y := by change MvPolynomial.aeval _ (MvPolynomial.X 1) = _; simp
  let F := (((groupPointsFunctor _).obj Q.pinned.pair.G.val).map g).hom
  have hroot (a : D.I) (t : R) : F (root Q z a R t) = root Q z a S (g.hom t) :=
    map_root Q z g a t
  have hprod : F ((l.map (fun a => root Q z a.index R
      ((c a : R) * X ^ (a.leftDegree : ℕ) * Y ^ (a.rightDegree : ℕ)))).prod) =
      (l.map (fun a => root Q z a.index S
        ((c a : S) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))).prod := by
    have hh := map_rootProduct Q z g l c X Y
    change F _ = _ at hh
    rwa [hX, hY] at hh
  change root Q z i R X * root Q z j R Y * (root Q z i R X)⁻¹ * (root Q z j R Y)⁻¹ = _ at h
  have hh := congrArg F h
  change F (_ * _ * _ * _) = _ at hh
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hh
  rwa [hroot i X, hroot j Y, hX, hY, hprod] at hh

private theorem coneRoot_of_degree {i j : D.I} {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (h : r • D.datum.root i + s • D.datum.root j ∈ Set.range D.datum.root) :
    ∃ C : ConeRoot i j, (C.leftDegree : ℕ) = r ∧ (C.rightDegree : ℕ) = s := by
  obtain ⟨k, hk⟩ := h
  exact ⟨⟨⟨r, hr⟩, ⟨s, hs⟩, k, hk⟩, rfl, rfl⟩

private theorem signed_of_natAbs_eq {z : ℤ} {n : ℕ} (h : z.natAbs = n) :
    z = (n : ℤ) ∨ z = -(n : ℤ) := by
  apply Int.natAbs_eq_natAbs_iff.mp
  simpa using h

/-- Integrality for an independent pair in the shorter-first orientation in
its rank-two lattice model. The string factors remain in the requested order. -/
private theorem rootCommutatorAt_of_ordered_model (hz : IsChevalley Q z)
    (i j : D.I) (hi : IndependentRoots i j) (k : RankTwoKind)
    (F : Lattice →+ D.X) (a b : Lattice)
    (ha : a ∈ rankTwoCoefficients k) (hb : b ∈ rankTwoCoefficients k)
    (hdet : RankTwo.det a b ≠ 0)
    (hfa : F a = D.datum.root i) (hfb : F b = D.datum.root j)
    (hmem : ∀ t, t ∈ rankTwoCoefficients k ↔ F t ∈ Set.range D.datum.root)
    (horder : k = .A₁A₁ ∨ squaredLength k a ≤ squaredLength k b)
    (l : List (ConeRoot i j)) (hl : Enumerates l Set.univ)
    (R : TestAlgebra (RationalField.{u})) (x y : R) :
    ∃ c : ConeRoot i j → ℤ,
      root Q z i R x * root Q z j R y * (root Q z i R x)⁻¹ * (root Q z j R y)⁻¹ =
        (l.map (fun C => root Q z C.index R
          ((c C : R) * x ^ (C.leftDegree : ℕ) * y ^ (C.rightDegree : ℕ)))).prod := by
  classical
  letI : Finite D.I := D.finiteRoots
  obtain ⟨L, e, _, _, ht, _, _, _, hLie, hLie₀, _⟩ := hz.2
  letI := L.lieRing
  obtain ⟨dim, H, ⟨iso⟩, rep, hrep⟩ := faithfulLinearization RationalField.{u} Q.pinned.pair.G
  letI := Q.pinned.pair.G.property.1
  letI := H.property.1
  let J := ULift.{u} (Fin dim)
  letI := Specs.RationalRealization.matrixAlgebra R
  let T := rankTwoCoefficients k
  let P := bracketPairs T a b
  let Aφ := (algebraMap RationalField.{u} R).mapMatrix (m := J)
  let d : Lie RationalField.{u} Q.pinned.pair.G.val →+ Matrix J J R :=
    Aφ.toAddMonoidHom.comp (matrixDifferentialLinear rep iso).toAddMonoidHom
  have hd (v w : Lie RationalField.{u} Q.pinned.pair.G.val) : d ⁅v,w⁆ = d v * d w - d w * d v := by
    have h := (identityLieBracketMatrix RationalField.{u} Q.pinned.pair.G.val H.val _
      rep iso hrep).2 L v w
    change Aφ (matrixDifferential rep iso (L.lieRing.toBracket.bracket v w)) = _
    rw [h, map_sub, map_mul, map_mul]
    rfl
  let φ : GroupPoints Q.pinned.pair.G.val R →* Matrix J J R :=
    (Units.coeHom (Matrix J J R)).comp ((((groupPointsFunctor RationalField.{u}).map rep ≫ iso.hom).app R).hom)
  have hφ : Function.Injective φ := by
    intro p q hpq
    have he := Units.ext hpq
    change (iso.hom.app R).hom (p ≫ rep.hom.hom) = (iso.hom.app R).hom (q ≫ rep.hom.hom) at he
    letI := hrep
    letI : Mono rep.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono rep.hom.hom).mp ((iso.app R).groupIsoToMulEquiv.injective he)
  have hroot (i : D.I) (t : R) : IsNilpotent (t • d (e i)) ∧
      φ (root Q z i R t) = IsNilpotent.exp (t • d (e i)) := by
    obtain ⟨hn, he⟩ := rootMatrix_eq_nilpotentExp Q z rep iso i (e i) (ht i).1 R t
    change IsNilpotent (t • d (e i)) at hn
    change φ (root Q z i R t) = IsNilpotent.exp (t • d (e i)) at he
    exact ⟨hn, he⟩
  have hInv (i : D.I) (t : R) : φ ((root Q z i R t)⁻¹) =
      IsNilpotent.exp (-(t • d (e i))) := by
    have h := (rootHom Q z i R).map_inv (Multiplicative.ofAdd t)
    change root Q z i R (-t) = (root Q z i R t)⁻¹ at h
    rw [← h, (hroot i (-t)).2]
    exact congrArg IsNilpotent.exp (neg_smul t (d (e i)))
  obtain ⟨hstr, hlim⟩ := rootString_endpoints D (RankTwo.independentRoots_int hi)
  let p := D.datum.chainBotCoeff i j
  let q := D.datum.chainTopCoeff i j
  change IsRootString i j p q at hstr
  change p + q ≤ 3 at hlim
  have hm (r s : ℕ) : (r : ℤ) • a + (s : ℤ) • b ∈ T ↔
      r • D.datum.root i + s • D.datum.root j ∈ Set.range D.datum.root := by
    rw [hmem, map_add, map_zsmul, map_zsmul, hfa, hfb, natCast_zsmul, natCast_zsmul]
  have hs' (n : ℤ) : step a b n ∈ T ↔ -(p : ℤ) ≤ n ∧ n ≤ q := by
    rw [hmem, RankTwo.map_step, hfa, hfb, hstr]
  have hlen : backwardLength T a b = p := RankTwo.backwardLength_eq _ _ _ _ _ (by omega) hs'
  have hrange : rootString T a b = Finset.range (q+1) :=
    RankTwo.rootString_eq_range (by omega) hs'
  have hshape := RankTwo.positiveCone_shape k a ha b hb hdet horder
  have hcmem {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
      (h : r • D.datum.root i + s • D.datum.root j ∈ Set.range D.datum.root) :
      ((r : ℤ), (s : ℤ)) ∈ RankTwo.positiveConeCoefficients T a b :=
    (RankTwo.mem_positiveConeCoefficients hdet _ _).mpr ⟨(hm r s).mpr h, by omega, by omega⟩
  have hdegree {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
      (h : r • D.datum.root i + s • D.datum.root j ∈ Set.range D.datum.root) :
      s = 1 ∨ s = 2 := by
    rcases RankTwo.coneShape_second hshape (hcmem hr hs h) with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hcone (C : ConeRoot i j) : (C.rightDegree : ℕ) = 1 ∨ (C.rightDegree : ℕ) = 2 :=
    hdegree C.leftDegree.pos C.rightDegree.pos ⟨C.index, C.root_eq⟩
  have hcentralUnique (C C' : ConeRoot i j) (hC : (C.rightDegree : ℕ) = 2)
      (hC' : (C'.rightDegree : ℕ) = 2) : C = C' := by
    have h₁ := hcmem C.leftDegree.pos C.rightDegree.pos ⟨C.index, C.root_eq⟩
    have h₂ := hcmem C'.leftDegree.pos C'.rightDegree.pos ⟨C'.index, C'.root_eq⟩
    rw [hC] at h₁
    rw [hC'] at h₂
    have he := RankTwo.coneShape_degreeTwo_unique hshape h₁ h₂
    apply coneRoot_index_injective hi
    apply D.datum.root.injective
    rw [C.root_eq, C'.root_eq, hC, hC', Int.ofNat.inj he]
  let hasCenter := ∃ C : ConeRoot i j, (C.rightDegree : ℕ) = 2
  let r : ℕ := if h : hasCenter then h.choose.leftDegree else 0
  let C₀ : Matrix J J R := if h : hasCenter then d (e h.choose.index) else 0
  let v := (x ^ r * y ^ 2) • C₀
  have hchoose (C : ConeRoot i j) (hC : (C.rightDegree : ℕ) = 2) :
      r = (C.leftDegree : ℕ) ∧ C₀ = d (e C.index) := by
    have h : hasCenter := ⟨C, hC⟩
    have he := hcentralUnique h.choose C h.choose_spec hC
    simp [r, C₀, h, he]
  have hv : IsNilpotent v := by
    by_cases h : hasCenter
    · obtain ⟨hr, hc⟩ := hchoose h.choose h.choose_spec
      simpa only [v, hc] using (hroot h.choose.index (x ^ r * y ^ 2)).1
    · simpa only [v, C₀, dif_neg h, smul_zero] using (IsNilpotent.zero : IsNilpotent (0 : Matrix J J R))
  letI : LieRing (Matrix J J R) := LieRing.ofAssociativeRing
  let eM (a : D.I) := d (e a)
  have hLieM (i j k : D.I) (h : D.datum.root i + D.datum.root j = D.datum.root k) :
      ∃ (p q : ℕ) (t : ℤ), IsRootString i j p q ∧
        (t = (p : ℤ) + 1 ∨ t = -((p : ℤ) + 1)) ∧ ⁅eM i, eM j⁆ = t • eM k := by
    obtain ⟨p, q, t, hs, ht, hb, _⟩ := hLie i j k h
    refine ⟨p, q, t, hs, ht, ?_⟩
    change d (e i) * d (e j) - d (e j) * d (e i) = t • d (e k)
    rw [← hd, hb, map_zsmul]
  have hLieM₀ (i j : D.I) (hn : D.datum.root i + D.datum.root j ≠ 0)
      (hh : D.datum.root i + D.datum.root j ∉ Set.range D.datum.root) :
      ⁅eM i, eM j⁆ = 0 := by
    change d (e i) * d (e j) - d (e j) * d (e i) = 0
    rw [← hd, hLie₀ i j hn hh, map_zero]
  obtain ⟨s, c, hs₀, hc₀, hsc, hconj⟩ := conjugateRootString_eq_sum (R := R)
    eM (AddMonoidHom.id (Matrix J J R)) (fun _ _ => rfl) hLieM hLieM₀ i j
    (RankTwo.independentRoots_int hi) p q hstr
  simp only [AddMonoidHom.id_apply, eM] at hconj
  let U (n : ℕ) := ((c n : R) * x ^ n * y) • d (e (s n))
  have hU₀ : U 0 = y • d (e j) := by simp [U, hs₀, hc₀]
  have hs (n : ℕ) (hn : n ≤ q) :
      D.datum.root (s n) = n • D.datum.root i + 1 • D.datum.root j := by
    rw [(hsc n hn).1, natCast_zsmul, one_smul, add_comm]
  have hsum (n m : ℕ) (hn : n ≤ q) (hm : m ≤ q) :
      D.datum.root (s n) + D.datum.root (s m) =
        (n+m) • D.datum.root i + 2 • D.datum.root j := by
    simp only [hs n hn, hs m hm, add_nsmul, two_nsmul, one_nsmul]
    abel
  have hbracket (r s : R) (u w : Lie RationalField.{u} Q.pinned.pair.G.val) :
      (r • d u) * (s • d w) - (s • d w) * (r • d u) = (r*s) • d ⁅u,w⁆ := by
    rw [hd, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      smul_smul, smul_smul, mul_comm s r, smul_sub]
  have hvcomm (n : ℕ) (hn : n ≤ q) : Commute (U n) v := by
    by_cases h : hasCenter
    · let C := h.choose
      have hC := h.choose_spec
      have hw : D.datum.root (s n) + D.datum.root C.index =
          (n + (C.leftDegree : ℕ)) • D.datum.root i + 3 • D.datum.root j := by
        rw [hs _ hn, C.root_eq, hC, add_nsmul, show (3 : ℕ) = 1 + 2 by decide, add_nsmul]
        abel
      have hpos : 0 < n + (C.leftDegree : ℕ) := by have h := C.leftDegree.pos; omega
      have hnot : D.datum.root (s n) + D.datum.root C.index ∉ Set.range D.datum.root := by
        rw [hw]
        intro hh
        rcases hdegree hpos (by decide : 0 < (3 : ℕ)) hh with h | h <;> omega
      have hne : D.datum.root (s n) + D.datum.root C.index ≠ 0 :=
        hw.symm ▸ rootCombination_ne_zero hi _ 3 (by decide)
      have hzero := hLie₀ (s n) C.index hne hnot
      have hcomm : Commute (d (e (s n))) (d (e C.index)) :=
        sub_eq_zero.mp ((hd _ _).symm.trans (by rw [hzero, map_zero]))
      change Commute (U n) ((x ^ r * y ^ 2) • C₀)
      rw [(hchoose C hC).2]
      exact (hcomm.smul_left _).smul_right _
    · simpa [v, C₀, h] using Commute.zero_right (U n)
  have hbb (n m : ℕ) (hn : n < m) (hm' : m ≤ q) (hNot : step (step a b n) (step a b m) 1 ∉ T) :
      U n * U m - U m * U n = 0 := by
    have hne : D.datum.root (s n) + D.datum.root (s m) ≠ 0 := by
      rw [hsum n m (by omega) hm']
      exact rootCombination_ne_zero hi _ 2 (by decide)
    have hnot : D.datum.root (s n) + D.datum.root (s m) ∉ Set.range D.datum.root := by
      rw [hsum n m (by omega) hm', ← hm]
      exact fun ht => hNot (RankTwo.string_sum_eq a b n m ▸ ht)
    dsimp only [U]
    rw [hbracket, hLie₀ _ _ hne hnot, map_zero, smul_zero]
  have hpair (ij : ℕ × ℕ) (hij : ij ∈ P) :
      ∃ t : ℤ, t.natAbs = bracketMagnitude T a b ij ∧
        U ij.1 * U ij.2 - U ij.2 * U ij.1 = t • v := by
    have hij' := Finset.mem_filter.mp hij
    have hn := hij'.2.1
    have hq := (Finset.mem_product.mp hij'.1).2
    rw [hrange, Finset.mem_range] at hq
    have hm' : ij.2 ≤ q := by omega
    have hn' : ij.1 ≤ q := by omega
    have hmroot : (ij.1+ij.2) • D.datum.root i + 2 • D.datum.root j ∈ Set.range D.datum.root :=
      (hm _ 2).mp (RankTwo.string_sum_eq a b _ _ ▸ hij'.2.2)
    obtain ⟨C, hleft, hright⟩ := coneRoot_of_degree (by omega : 0 < ij.1 + ij.2)
      (by decide : 0 < (2 : ℕ)) hmroot
    have hk : D.datum.root (s ij.1) + D.datum.root (s ij.2) = D.datum.root C.index := by
      rw [hsum _ _ hn' hm', C.root_eq, hleft, hright]
    have hne : s ij.1 ≠ s ij.2 := by
      intro he
      have hroot := congrArg D.datum.root he
      rw [hs _ hn', hs _ hm'] at hroot
      exact (Nat.ne_of_lt hn) (rootDegrees_eq hi hroot).1
    have hneg : D.datum.root (s ij.2) ≠ -D.datum.root (s ij.1) := by
      intro he
      rw [he, add_neg_cancel] at hk
      exact D.datum.ne_zero C.index hk.symm
    obtain ⟨p', q', t, hstring, ht, hbr, _⟩ := hLie (s ij.1) (s ij.2) C.index hk
    obtain ⟨hstr₀, hbnd⟩ := rootString_endpoints D
      (RankTwo.independentRoots_int (independentRoots_of_ne_of_ne_neg hne hneg))
    have hpp : p' ≤ 3 := by
      rw [IsRootString.backwardLength_unique hstring hstr₀]
      omega
    have hback := RankTwo.backwardLength_eq T (step a b ij.1) (step a b ij.2) p' q' hpp
      (fun n => by
        rw [hmem, RankTwo.map_step]
        simp only [RankTwo.map_step, hfa, hfb]
        rw [← (hsc _ hn').1, ← (hsc _ hm').1, hstring])
    have hsignI : (c ij.1).natAbs = (p + ij.1).choose ij.1 := by
      rcases (hsc _ hn').2 with h | h <;> simp [h]
    have hsignJ : (c ij.2).natAbs = (p + ij.2).choose ij.2 := by
      rcases (hsc _ hm').2 with h | h <;> simp [h]
    have htAbs : t.natAbs = 1 + p' := by
      have hInt : ((p' : ℤ) + 1) = ((p'+1 : ℕ) : ℤ) := by push_cast; rfl
      rcases ht with h | h
      · rw [h, hInt, Int.natAbs_natCast, Nat.add_comm]
      · rw [h, hInt, Int.natAbs_neg, Int.natAbs_natCast, Nat.add_comm]
    refine ⟨c ij.1 * c ij.2 * t, ?_, ?_⟩
    · simp only [Int.natAbs_mul, hsignI, hsignJ, htAbs, bracketMagnitude, hlen, hback]
    · have hc := hchoose C hright
      dsimp only [U, v]
      rw [hbracket, hbr, map_zsmul, hc.2, hc.1, hleft, ← Int.cast_smul_eq_zsmul R,
        smul_smul, ← Int.cast_smul_eq_zsmul R, smul_smul]
      congr 1
      push_cast
      rw [pow_add, pow_two]
      ring
  let g (ij : ℕ × ℕ) := if h : ij ∈ P then (hpair ij h).choose else 0
  have hg (ij : ℕ × ℕ) (hij : ij ∈ P) :
      U ij.1 * U ij.2 - U ij.2 * U ij.1 = g ij • v := by
    simpa only [g, dif_pos hij] using (hpair ij hij).choose_spec.2
  have heventh : ∃ b : ℤ, (∑ ij ∈ P, g ij) = 2 * b := by
    by_cases hP : P.Nonempty
    · obtain ⟨ij, hij⟩ := hP
      have hgAbs (t : ℕ × ℕ) (ht : t ∈ P) : (g t).natAbs = bracketMagnitude T a b t := by
        rw [show g t = (hpair t ht).choose from dite_eq_left ht]
        exact (hpair t ht).choose_spec.1
      have hE := RankTwo.centralBracketCoefficients_integral k a b ha hb hdet horder g
        (fun t ht => signed_of_natAbs_eq (hgAbs t ht)) ij hij
      have hfilter : P.filter (fun t => t.1+t.2 = ij.1+ij.2) = P := by
        apply Finset.filter_true_of_mem
        intro t ht
        have h' (w : ℕ × ℕ) (hw : w ∈ P) :
            ((↑(w.1+w.2) : ℤ), (2 : ℤ)) ∈ RankTwo.positiveConeCoefficients T a b := by
          have hww := (Finset.mem_filter.mp hw).2
          have hRoot : _ ∈ T := RankTwo.string_sum_eq a b _ _ ▸ hww.2
          exact (RankTwo.mem_positiveConeCoefficients hdet _ _).mpr ⟨hRoot, by omega, by decide⟩
        exact Int.ofNat.inj (RankTwo.coneShape_degreeTwo_unique hshape (h' t ht) (h' ij hij))
      rwa [hfilter] at hE
    · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp hP]⟩
  have hbrV (n m : ℕ) (hn : n ≤ q) (hm : m ≤ q) :
      ∃ c : ℤ, U n * U m - U m * U n = c • v := by
    suffices h : ∀ n m : ℕ, n < m → m ≤ q → ∃ c : ℤ, U n * U m - U m * U n = c • v by
      rcases lt_trichotomy n m with ht | rfl | ht
      · exact h n m ht hm
      · exact ⟨0, by simp⟩
      · obtain ⟨c, hc⟩ := h m n ht hn
        exact ⟨-c, by rw [neg_zsmul, ← hc, neg_sub]⟩
    intro n m hn hm
    by_cases h : (n,m) ∈ P
    · exact ⟨_, hg _ h⟩
    · refine ⟨0, ?_⟩
      rw [zero_zsmul]
      apply hbb n m hn hm
      intro ht
      apply h
      exact Finset.mem_filter.mpr ⟨hrange.symm ▸ Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hn, ht⟩
  let l₁ := l.filter isStringConeRoot
  let lM := l₁.map (fun C : ConeRoot i j => U C.leftDegree)
  let l₀ := (List.range (q+1)).map U
  have hperm : (lM ++ [y • d (e j)]).Perm l₀ := by
    simpa only [lM, l₀, l₁, List.map_append, List.map_map, List.map_singleton, hU₀, Function.comp_def]
      using (stringConeRoot_degrees hi hstr s (fun d hd => (hsc d hd).1) l hl).map U
  have hcSum : IsNilpotent.exp (x • d (e i)) * (y • d (e j)) *
      IsNilpotent.exp (-(x • d (e i))) = l₀.sum := by
    rw [hconj x y (hroot i x).1]
    change _ = ((List.range (q+1)).map U).sum
    rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  have hmem₀ (a : Matrix J J R) (ha : a ∈ l₀) : ∃ n ≤ q, U n = a := by
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp ha
    exact ⟨n, by simpa using List.mem_range.mp hn, rfl⟩
  have hUordered : orderedBracketSum l₀ = (∑ ij ∈ P, g ij) • v := by
    change orderedBracketSum ((List.range (q+1)).map U) = _
    rw [orderedBracketSum_range, ← RankTwo.sum_bracket_pairs hrange
      (fun ij => U ij.1 * U ij.2 - U ij.2 * U ij.1) hbb, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro ij hij
    exact hg ij hij
  obtain ⟨b₀, hb₀⟩ := heventh
  have hcanon : orderedBracketSum l₀ = (2 : ℕ) • (b₀ • v) := by
    rw [hUordered, hb₀, mul_zsmul, two_zsmul, two_nsmul]
  obtain ⟨C, hC⟩ := collect_exp_string (x • d (e i)) (y • d (e j)) v
    (hroot i x).1 (hroot j y).1 hv lM l₀ hperm
    (fun m hm => by obtain ⟨n, hn, rfl⟩ := hmem₀ m hm; exact (hroot (s n) _).1)
    (fun m hm => by obtain ⟨n, hn, rfl⟩ := hmem₀ m hm; exact hvcomm n hn)
    (fun m hm n hn => by obtain ⟨a, ha, rfl⟩ := hmem₀ m hm; obtain ⟨b, hb, rfl⟩ := hmem₀ n hn
                         exact hbrV a b ha hb) hcSum b₀ hcanon
  let coeff (a : ConeRoot i j) : ℤ :=
    if (a.rightDegree : ℕ) = 1 then c a.leftDegree else C
  refine ⟨coeff, ?_⟩
  apply hφ
  rw [map_mul, map_mul, map_mul, (hroot _ _).2, (hroot _ _).2, hInv, hInv, hC, map_list_prod]
  conv_rhs => rw [List.map_map]
  let f (a : ConeRoot i j) := φ (root Q z a.index R
      ((coeff a : R) * x ^ (a.leftDegree : ℕ) * y ^ (a.rightDegree : ℕ)))
  change (lM.map IsNilpotent.exp).prod * IsNilpotent.exp (C • v) = (l.map f).prod
  have hStr (a : ConeRoot i j) (ha : isStringConeRoot a = true) :
      f a = IsNilpotent.exp (U a.leftDegree) := by
    have ha' : (a.rightDegree : ℕ) = 1 := by simpa [isStringConeRoot] using ha
    have hs := stringConeRoot_index p q hstr s (fun d hd => (hsc d hd).1) a ha'
    dsimp only [f, coeff, U]
    rw [if_pos ha', ha', pow_one, hs.2, (hroot _ _).2]
  have hString : ((l₁.map f).prod) = (lM.map IsNilpotent.exp).prod := by
    dsimp only [lM]
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro a ha
    exact hStr a (List.mem_filter.mp ha).2
  rw [← hString]
  by_cases h : hasCenter
  · let a := h.choose
    have ha : (a.rightDegree : ℕ) = 2 := h.choose_spec
    have ha' : isStringConeRoot a = false := by
      change decide ((a.rightDegree : ℕ) = 1) = false
      rw [ha] <;> decide
    have hexp : f a = IsNilpotent.exp (C • v) := by
      obtain ⟨hr, hc⟩ := hchoose a ha
      dsimp only [f, coeff, v]
      rw [ha, if_neg (by decide : (2 : ℕ) ≠ 1), (hroot _ _).2, hr, hc, ← Int.cast_smul_eq_zsmul R,
        smul_smul, mul_assoc]
    have hf (b : ConeRoot i j) (_ : b ∈ l) (hb : isStringConeRoot b = false) (hn : b ≠ a) : f b = 1 := by
      exfalso
      apply hn
      rcases hcone b with ht | ht
      · simp [isStringConeRoot, ht] at hb
      · exact hcentralUnique b a ht ha
    have hcomm (b : ConeRoot i j) (_ : b ∈ l) (hb : isStringConeRoot b = true) : Commute (f a) (f b) := by
      have hb' : (b.rightDegree : ℕ) = 1 := by simpa [isStringConeRoot] using hb
      have hn := (stringConeRoot_index p q hstr s (fun d hd => (hsc d hd).1) b hb').1
      rw [hexp, hStr b hb]
      have hc : Commute (C • v) (U b.leftDegree) := by
        rw [← Int.cast_smul_eq_zsmul ℚ]
        exact (hvcomm _ hn).symm.smul_left _
      have hn₁ : IsNilpotent (C • v) := by rw [← Int.cast_smul_eq_zsmul ℚ]; exact hv.smul _
      have hn₂ : IsNilpotent (U b.leftDegree) := (hroot _ _).1
      change _ * _ = _ * _
      rw [← IsNilpotent.exp_add_of_commute hc hn₁ hn₂, add_comm, IsNilpotent.exp_add_of_commute hc.symm hn₂ hn₁]
    rw [list_product_filter_single l hl.1 isStringConeRoot f ha' hf hcomm,
      if_pos ((hl.2 a).mpr (Set.mem_univ a)), hexp]
  · have h₁ (a : ConeRoot i j) : isStringConeRoot a = true := by
      rcases hcone a with ha | ha
      · simp [isStringConeRoot, ha]
      · exact (h ⟨a, ha⟩).elim
    simp [l₁, List.filter_eq_self.mpr (fun a _ => h₁ a), v, C₀, h, IsNilpotent.exp_zero]

private theorem independentRootRelation_of_ordered_model (hz : IsChevalley Q z)
    (i j : D.I) (hi : IndependentRoots i j) (k : RankTwoKind)
    (F : Lattice →+ D.X) (a b : Lattice)
    (ha : a ∈ rankTwoCoefficients k) (hb : b ∈ rankTwoCoefficients k)
    (hdet : RankTwo.det a b ≠ 0)
    (hfa : F a = D.datum.root i) (hfb : F b = D.datum.root j)
    (hmem : ∀ t, t ∈ rankTwoCoefficients k ↔ F t ∈ Set.range D.datum.root)
    (horder : k = .A₁A₁ ∨ squaredLength k a ≤ squaredLength k b)
    (l : List (ConeRoot i j)) (hl : Enumerates l Set.univ) :
    ∃ c : ConeRoot i j → ℤ, ∀ (R : TestAlgebra (RationalField.{u})) (x y : R),
      root Q z i R x * root Q z j R y * (root Q z i R x)⁻¹ * (root Q z j R y)⁻¹ =
        (l.map (fun C => root Q z C.index R
          ((c C : R) * x ^ (C.leftDegree : ℕ) * y ^ (C.rightDegree : ℕ)))).prod := by
  let R := CommAlgCat.of RationalField.{u} (MvPolynomial (Fin 2) RationalField.{u})
  obtain ⟨c, hc⟩ := rootCommutatorAt_of_ordered_model Q z hz i j hi k F a b ha hb hdet hfa hfb hmem horder
    l hl R (MvPolynomial.X 0) (MvPolynomial.X 1)
  exact ⟨c, genericRootCommutator Q z l c hc⟩

/-- Chevalley coordinates give all commutator coefficients, for every
enumeration of each independent cone. -/
theorem independentRootRelations_of_Chevalley (hz : IsChevalley Q z) : IndependentRootRelations Q z := by
  intro i j hi l hl
  obtain ⟨k, F, a, b, _, ha, hb, hdet, hfa, hfb, hm⟩ := RankTwo.latticeModel_of_independentRoots D hi
  by_cases h : squaredLength k a ≤ squaredLength k b
  · exact independentRootRelation_of_ordered_model Q z hz i j hi k F a b ha hb hdet hfa hfb hm (Or.inr h) l hl
  · have hj : IndependentRoots j i := by
      let w := ![(1 : ℚ) ⊗ₜ[ℤ] D.datum.root i, (1 : ℚ) ⊗ₜ[ℤ] D.datum.root j]
      let σ := Equiv.swap (0 : Fin 2) 1
      have he : w ∘ σ = ![(1 : ℚ) ⊗ₜ[ℤ] D.datum.root j, (1 : ℚ) ⊗ₜ[ℤ] D.datum.root i] := by
        funext t
        fin_cases t <;> rfl
      exact (linearIndependent_equiv' σ he).mpr hi
    exact independentRootRelation_swap Q z i j
      (independentRootRelation_of_ordered_model Q z hz j i hj k F b a hb ha
        (by unfold RankTwo.det at *; intro ht; apply hdet; linarith) hfb hfa hm (Or.inr (le_of_not_ge h))) l hl

end CollectRootPairs


/-- The integral relations use the marked torus, Borel and simple root
coordinates of the given rational realization. -/
theorem integralRootRelationsForRealization : RelationsInRealization.{u} := by
  intro D _ hcoroot A Q
  obtain ⟨z, hz⟩ := exists_chevalleyCoordinates Q
    _root_.LinearAlgebraicGroups.RationalRealization.complexCartan
    _root_.LinearAlgebraicGroups.RationalRealization.serreStructure
    _root_.LinearAlgebraicGroups.RationalRealization.serreBaseChange
    _root_.LinearAlgebraicGroups.RationalRealization.rationalSerreDecomposition hcoroot
  have hop := oppositeRootRelations_of_Chevalley Q z hz
  have hin := independentRootRelations_of_Chevalley Q z hz
  exact ⟨z, hz, hop, hin, formalBigCellProduct_of_rootRelations Q z hop hin⟩

/-- Each semisimple datum on its coroot lattice admits a rational model
with the integral root relations and formal cell multiplication. -/
theorem integralRootRelations : Specs.IntegralRootRelations.Statement.{u} := by
  intro D hsemisimple hcoroot
  obtain ⟨A, Q, _⟩ := _root_.LinearAlgebraicGroups.RationalRealization.existsRationalRealization D
  exact ⟨A, Q, integralRootRelationsForRealization D hsemisimple hcoroot A Q⟩

end

end LinearAlgebraicGroups.Classification.IntegralRootRelations
