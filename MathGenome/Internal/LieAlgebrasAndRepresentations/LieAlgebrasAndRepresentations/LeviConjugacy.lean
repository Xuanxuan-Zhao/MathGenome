import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.LeviConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleIdealDecomposition
import Mathlib.LinearAlgebra.Projection
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Nilradical
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FirstWhitehead
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.NilpotentBCH

noncomputable section
universe u v w
namespace LieAlgebrasAndRepresentations.LeviConjugacy

attribute [local instance 100] LieRing.ofAssociativeRing

variable (k : Type u) (L : Type v) [Field k] [CharZero k]
    [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]

/-- Elements of the nilradical have nilpotent adjoint action on the entire
ambient algebra, not only on the nilradical. -/
theorem nilpotent_ad (z : L) (hz : z ∈ nilradical k L) :
    IsNilpotent (LieAlgebra.ad k L z) :=
  ((mem_nilradical_iff k L z).mp hz).2

/-- The algebraic exponential of the ambient adjoint derivation. -/
def innerExponential (z : L) (hz : z ∈ nilradical k L) : L ≃ₗ⁅k⁆ L :=
  letI : Module ℚ L := Module.restrictScalars ℚ k L
  (LieDerivation.ad k L z).exp (by simpa using nilpotent_ad k L z hz)

@[simp] theorem innerExponential_toLinearMap (z : L) (hz : z ∈ nilradical k L) :
    (innerExponential k L z hz).toLinearMap =
      Specs.LieAlgebrasAndRepresentations.LeviConjugacy.adjointExponential k L z := by
  let : Module ℚ L := Module.restrictScalars ℚ k L
  change IsNilpotent.exp ((LieDerivation.ad k L z).toLinearMap) = _
  rw [LieDerivation.coe_ad_apply_eq_ad_apply]
  unfold IsNilpotent.exp
    Specs.LieAlgebrasAndRepresentations.LeviConjugacy.adjointExponential
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Rat.cast_smul_eq_qsmul k]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- Explicit finite sum in the original coefficient field. -/
theorem finiteExponential :
    Specs.LieAlgebrasAndRepresentations.LeviConjugacy.finiteExponentialType.{u,v} := by
  intro k L _ _ _ _ _ z hz
  have hn := nilpotent_ad k L z hz
  obtain ⟨N, hN⟩ := hn
  refine ⟨nilpotent_ad k L z hz, N, innerExponential k L z hz, hN, ?_, ?_⟩
  · exact innerExponential_toLinearMap k L z hz
  · let : Module ℚ L := Module.restrictScalars ℚ k L
    change IsNilpotent.exp ((LieDerivation.ad k L z).toLinearMap) = _
    rw [LieDerivation.coe_ad_apply_eq_ad_apply]
    rw [IsNilpotent.exp_eq_sum hN]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Rat.cast_smul_eq_qsmul k]
    simp only [Rat.cast_inv, Rat.cast_natCast]

/-- Two homomorphisms out of a semisimple algebra which agree modulo the
radical already agree modulo the nilradical. This is the initial reduction
before the successive lower-central corrections in Malcev's argument. -/
theorem difference_mem_nilradical
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (a b : H →ₗ⁅k⁆ L)
    (hr : ∀ x, a x - b x ∈ radical k L) (x : H) :
    a x - b x ∈ nilradical k L := by
  let d : H →ₗ[k] L := a.toLinearMap - b.toLinearMap
  change x ∈ (nilradical k L).toSubmodule.comap d
  have hx : x ∈ (⁅(⊤ : LieIdeal k H), ⊤⁆ : LieIdeal k H) := by
    rw [semisimple_perfect k H hH]
    trivial
  change x ∈ (⁅(⊤ : LieIdeal k H), ⊤⁆ : LieIdeal k H).toSubmodule at hx
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
  apply (Submodule.span_le.mpr ?_) hx
  rintro _ ⟨y, _, z, _, rfl⟩
  change a ⁅y,z⁆ - b ⁅y,z⁆ ∈ nilradical k L
  rw [a.map_lie, b.map_lie]
  have h₁ : ⁅a y, a z - b z⁆ ∈ nilradical k L := by
    simpa using derivation_radical_mem_nilradical k L
      (LieDerivation.ad k L (a y)) _ (hr z)
  have h₂ : ⁅a y - b y, b z⁆ ∈ nilradical k L := by
    rw [← lie_skew (a y - b y)]
    apply (nilradical k L).neg_mem
    simpa using derivation_radical_mem_nilradical k L
      (LieDerivation.ad k L (b z)) _ (hr y)
  have heq : ⁅a y, a z⁆ - ⁅b y, b z⁆ =
      ⁅a y, a z - b z⁆ + ⁅a y - b y, b z⁆ := by
    rw [lie_sub, sub_lie]
    abel
  rw [heq]
  exact (nilradical k L).add_mem h₁ h₂

/-- The canonical quotient isomorphism of any complement to the radical. -/
def quotientEquiv (S : LieSubalgebra k L)
    (hS : IsCompl S.toSubmodule (radical k L).toSubmodule) :
    S ≃ₗ⁅k⁆ (L ⧸ radical k L) :=
  { ((radical k L).toSubmodule.quotientEquivOfIsCompl S.toSubmodule hS.symm).symm with
    map_lie' := by intro x y; rfl }

omit [CharZero k] [FiniteDimensional k L] in
@[simp] theorem quotientEquiv_apply (S : LieSubalgebra k L)
    (hS : IsCompl S.toSubmodule (radical k L).toSubmodule) (x : S) :
    quotientEquiv k L S hS x = LieSubmodule.Quotient.mk (x : L) := rfl

/-- The graph of one Levi factor over another has its discrepancy in the
nilradical. No algebraic closure or choice of eigenvalues is used. -/
theorem leviFactorsEquiv :
    Specs.LieAlgebrasAndRepresentations.LeviConjugacy.leviFactorsEquivType.{u,v} := by
  intro k L _ _ _ _ _ S T hS hT
  let qS := quotientEquiv k L S hS.2
  let qT := quotientEquiv k L T hT.2
  let e : S ≃ₗ⁅k⁆ T := qS.trans qT.symm
  refine ⟨e, ?_⟩
  have hr (x : S) : (e x : L) - (x : L) ∈ radical k L := by
    have he : (LieSubmodule.Quotient.mk (e x : L) : L ⧸ radical k L) =
        LieSubmodule.Quotient.mk (x : L) := by
      change qT (e x) = qS x
      exact qT.apply_symm_apply (qS x)
    apply (LieSubmodule.Quotient.mk_eq_zero (radical k L)).mp
    change (radical k L).toSubmodule.mkQ ((e x : L) - (x : L)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr he
  exact difference_mem_nilradical k L S hS.1 (T.incl.comp e.toLieHom) S.incl hr

/-- Whitehead's lemma applied to the actual adjoint action on an abelian
ideal. This is the correction step when no further quotient is needed. -/
theorem difference_inner_of_abelian_ideal
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (a b : H →ₗ⁅k⁆ L)
    (I : LieIdeal k L) (hI : ∀ x ∈ I, ∀ y ∈ I, ⁅x,y⁆ = (0 : L))
    (hd : ∀ x, a x - b x ∈ I) :
    ∃ v : L, v ∈ I ∧ ∀ x, a x - b x = ⁅b x,v⁆ := by
  let := LieRingModule.compLieHom I b
  let := LieModule.compLieHom I b
  let d : H →ₗ[k] I := (a.toLinearMap - b.toLinearMap).codRestrict I.toSubmodule hd
  have hc : ∀ x y, d ⁅x,y⁆ = ⁅x,d y⁆ - ⁅y,d x⁆ := by
    intro x y
    apply Subtype.ext
    change a ⁅x,y⁆ - b ⁅x,y⁆ =
      ⁅b x,a y - b y⁆ - ⁅b y,a x - b x⁆
    apply sub_eq_zero.mp
    calc
      _ = ⁅a x - b x,a y - b y⁆ := by
        simp only [a.map_lie, b.map_lie, sub_lie, lie_sub]
        rw [← lie_skew (b y) (a x), ← lie_skew (b y) (b x)]
        abel
      _ = 0 := hI _ (hd x) _ (hd y)
  obtain ⟨v,hv⟩ := FirstWhitehead.cocycle_inner k H I hH d hc
  exact ⟨v, v.property, fun x => congrArg Subtype.val (hv x)⟩

/-- In a quotient where the discrepancy ideal becomes abelian, the
Whitehead correction can be lifted to that ideal in the original algebra. -/
theorem difference_inner_mod_ideal
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (a b : H →ₗ⁅k⁆ L)
    (I J : LieIdeal k L) (hII : ⁅I,I⁆ ≤ J)
    (hd : ∀ x, a x - b x ∈ I) :
    ∃ v : L, v ∈ I ∧ ∀ x, a x - b x - ⁅b x,v⁆ ∈ J := by
  let q : L →ₗ⁅k⁆ L ⧸ J :=
    { J.toSubmodule.mkQ with map_lie' := by intros; rfl }
  have hq : Function.Surjective q := Quot.mk_surjective
  have hbar : ∀ x ∈ I.map q, ∀ y ∈ I.map q, ⁅x,y⁆ = (0 : L ⧸ J) := by
    intro x hx y hy
    obtain ⟨x,hx⟩ := LieIdeal.mem_map_of_surjective hq hx
    obtain ⟨y,hy⟩ := LieIdeal.mem_map_of_surjective hq hy
    rw [← hx, ← hy, ← q.map_lie]
    exact (LieSubmodule.Quotient.mk_eq_zero J).mpr
      (hII (LieSubmodule.lie_mem_lie x.property y.property))
  have hdq (x : H) : (q.comp a) x - (q.comp b) x ∈ I.map q := by
    change q (a x) - q (b x) ∈ I.map q
    rw [← map_sub]
    exact LieIdeal.mem_map (hd x)
  obtain ⟨v,hvI,hv⟩ := difference_inner_of_abelian_ideal k (L ⧸ J) H hH
    (q.comp a) (q.comp b) (I.map q) hbar hdq
  obtain ⟨v,hvv⟩ := LieIdeal.mem_map_of_surjective hq hvI
  refine ⟨v,v.property,fun x => ?_⟩
  apply (LieSubmodule.Quotient.mk_eq_zero J).mp
  change q (a x - b x - ⁅b x,v.val⁆) = 0
  rw [map_sub, map_sub, q.map_lie, hvv]
  exact sub_eq_zero.mpr (hv x)

/-- Modulo an ideal containing the self-commutator of I, conjugation by
an element of I has just its constant and linear terms. The exponential is
still the genuine automorphism of the whole ambient algebra. -/
theorem innerExponential_first_order_mod
    (I J : LieIdeal k L) (hII : ⁅I,I⁆ ≤ J)
    (v : L) (hv : v ∈ I) (hvn : v ∈ nilradical k L) (y : L) :
    innerExponential k L v hvn y - y - ⁅v,y⁆ ∈ J := by
  let : Module ℚ L := Module.restrictScalars ℚ k L
  let : Module ℚ (L ⧸ J) := Module.restrictScalars ℚ k (L ⧸ J)
  let q : L →ₗ⁅k⁆ L ⧸ J :=
    { J.toSubmodule.mkQ with map_lie' := by intros; rfl }
  have hq : Function.Surjective q := Quot.mk_surjective
  let D := LieAlgebra.ad k L v
  let Dq := LieAlgebra.ad k (L ⧸ J) (q v)
  have hcomm : Dq ∘ₗ q.toLinearMap = q.toLinearMap ∘ₗ D := by
    ext x
    exact (q.map_lie v x).symm
  have hq2 : Dq ^ 2 = 0 := by
    ext x
    obtain ⟨x,rfl⟩ := hq x
    change ⁅q v,⁅q v,q x⁆⁆ = 0
    rw [← q.map_lie, ← q.map_lie]
    exact (LieSubmodule.Quotient.mk_eq_zero J).mpr
      (hII (LieSubmodule.lie_mem_lie hv (lie_mem_left k L I v x hv)))
  have hEq : IsNilpotent.exp Dq = 1 + Dq := by
    rw [IsNilpotent.exp_eq_sum hq2]
    simp [Finset.sum_range_succ]
  have hE : (innerExponential k L v hvn).toLinearMap = IsNilpotent.exp D := by
    change IsNilpotent.exp (LieDerivation.ad k L v).toLinearMap = _
    rw [LieDerivation.coe_ad_apply_eq_ad_apply]
  have hc := Module.End.commute_exp_left_of_commute
    (nilpotent_ad k L v hvn) (show IsNilpotent Dq from ⟨2,hq2⟩) hcomm
  have he := LinearMap.congr_fun hc y
  rw [hEq, ← hE] at he
  have hy : q (innerExponential k L v hvn y) = q y + q ⁅v,y⁆ := by
    change q y + ⁅q v,q y⁆ = q (innerExponential k L v hvn y) at he
    rw [← q.map_lie] at he
    exact he.symm
  apply (LieSubmodule.Quotient.mk_eq_zero J).mp
  change q (innerExponential k L v hvn y - y - ⁅v,y⁆) = 0
  rw [map_sub, map_sub, hy]
  abel

/-- One Whitehead correction replaces discrepancy in I by discrepancy in
its commutator ideal (or any specified ideal containing that commutator). -/
theorem improve_discrepancy
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (a b : H →ₗ⁅k⁆ L)
    (I J : LieIdeal k L) (hIn : I ≤ nilradical k L) (hII : ⁅I,I⁆ ≤ J)
    (hd : ∀ x, a x - b x ∈ I) :
    ∃ v : L, ∃ hv : v ∈ nilradical k L, v ∈ I ∧
      ∀ x, innerExponential k L v hv (a x) - b x ∈ J := by
  obtain ⟨v,hvI,hv⟩ := difference_inner_mod_ideal k L H hH a b I J hII hd
  refine ⟨v,hIn hvI,hvI,fun x => ?_⟩
  have hfirst := innerExponential_first_order_mod k L I J hII v hvI (hIn hvI) (a x)
  have hbr : ⁅v,a x - b x⁆ ∈ J :=
    hII (LieSubmodule.lie_mem_lie hvI (hd x))
  have heq : innerExponential k L v (hIn hvI) (a x) - b x =
      (innerExponential k L v (hIn hvI) (a x) - a x - ⁅v,a x⁆) +
        (a x - b x - ⁅b x,v⁆) + ⁅v,a x - b x⁆ := by
    rw [lie_sub, ← lie_skew (b x) v]
    abel
  rw [heq]
  exact J.add_mem (J.add_mem hfirst (hv x)) hbr

/-- Apply the listed inner exponentials in order, from the head to the tail. -/
def exponentialProduct : List (nilradical k L) → L ≃ₗ⁅k⁆ L
  | [] => LieEquiv.refl
  | v :: vs => (innerExponential k L v.val v.property).trans (exponentialProduct vs)

@[simp] theorem exponentialProduct_nil (x : L) :
    exponentialProduct k L [] x = x := rfl

@[simp] theorem exponentialProduct_cons (v : nilradical k L)
    (vs : List (nilradical k L)) (x : L) :
    exponentialProduct k L (v :: vs) x =
      exponentialProduct k L vs (innerExponential k L v.val v.property x) := rfl

/-- Successive Whitehead corrections terminate along the derived series of
any discrepancy ideal contained in the nilradical. No choice of eigenvalues
or algebraically closed coefficient field is needed. -/
theorem rectify_discrepancy
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (n : ℕ) :
    ∀ (I : LieIdeal k L), I ≤ nilradical k L →
      LieAlgebra.derivedSeriesOfIdeal k L n I = ⊥ →
      ∀ a b : H →ₗ⁅k⁆ L, (∀ x, a x - b x ∈ I) →
      ∃ vs : List (nilradical k L), ∀ x, exponentialProduct k L vs (a x) = b x := by
  induction n with
  | zero =>
    intro I hIn hI a b hd
    refine ⟨[], fun x => ?_⟩
    have hx := hd x
    rw [LieAlgebra.derivedSeriesOfIdeal_zero] at hI
    rw [hI] at hx
    change a x - b x = 0 at hx
    exact sub_eq_zero.mp hx
  | succ n ih =>
    intro I hIn hI a b hd
    obtain ⟨v,hvn,hvI,hv⟩ := improve_discrepancy k L H hH a b I ⁅I,I⁆ hIn le_rfl hd
    have hJn : (⁅I,I⁆ : LieIdeal k L) ≤ nilradical k L :=
      le_trans (LieSubmodule.lie_le_left I I) hIn
    have hJ : LieAlgebra.derivedSeriesOfIdeal k L n ⁅I,I⁆ = ⊥ := by
      change LieAlgebra.derivedSeriesOfIdeal k L n
        (LieAlgebra.derivedSeriesOfIdeal k L 1 I) = ⊥
      rw [← LieAlgebra.derivedSeriesOfIdeal_add I n 1]
      exact hI
    let a' := (innerExponential k L v hvn).toLieHom.comp a
    obtain ⟨vs,hvs⟩ := ih ⁅I,I⁆ hJn hJ a' b hv
    exact ⟨⟨v,hvn⟩ :: vs, hvs⟩

/-- A nilpotent discrepancy ideal has a terminating derived series, so a
finite list of genuine inner exponential automorphisms removes the entire
discrepancy between the two homomorphisms. -/
theorem rectify_nilradical_discrepancy
    (H : Type w) [LieRing H] [LieAlgebra k H] [FiniteDimensional k H]
    (hH : IsSemisimple k H) (a b : H →ₗ⁅k⁆ L)
    (hd : ∀ x, a x - b x ∈ nilradical k L) :
    ∃ vs : List (nilradical k L), ∀ x, exponentialProduct k L vs (a x) = b x := by
  let := nilradical_nilpotent k L
  obtain ⟨n,hn⟩ := LieAlgebra.IsSolvable.solvable k (nilradical k L)
  apply rectify_discrepancy k L H hH n (nilradical k L) le_rfl ?_ a b hd
  exact (LieIdeal.derivedSeries_eq_bot_iff (nilradical k L) n).mp hn

/-- Finite-product conjugacy, prior to compressing the product by BCH. -/
theorem finiteProductConjugacy
    (S T : LieSubalgebra k L)
    (hS : Specs.LieAlgebrasAndRepresentations.LeviConjugacy.IsLeviFactor k L S)
    (hT : Specs.LieAlgebrasAndRepresentations.LeviConjugacy.IsLeviFactor k L T) :
    ∃ vs : List (nilradical k L), T.map (exponentialProduct k L vs).toLieHom = S := by
  obtain ⟨e,he⟩ := leviFactorsEquiv k L S T hS hT
  obtain ⟨vs,hvs⟩ := rectify_nilradical_discrepancy k L S hS.1
    (T.incl.comp e.toLieHom) S.incl he
  refine ⟨vs, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨t,ht,hty⟩ := (T.mem_map (exponentialProduct k L vs).toLieHom y).mp hy
    obtain ⟨x,hx⟩ := e.surjective ⟨t,ht⟩
    have hx' : (e x : L) = t := congrArg Subtype.val hx
    have hxy : (x : L) = y := by
      have hh := hvs x
      change exponentialProduct k L vs (e x : L) = (x : L) at hh
      rw [hx'] at hh
      exact hh.symm.trans hty
    exact hxy ▸ x.property
  · intro hy
    let x : S := ⟨y,hy⟩
    apply (T.mem_map (exponentialProduct k L vs).toLieHom y).mpr
    exact ⟨e x, (e x).property, hvs x⟩

namespace FiniteDegreeEvaluation
open LieAlgebrasAndRepresentations.CompletedPrimitives
open LieAlgebrasAndRepresentations.FormalExpLog

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (G : Submodule K A) (N : ℕ) (hG : G ^ (N + 1) = ⊥)
include hG

/-- A nilpotent homogeneous generator subspace makes every completed series
an ordinary polynomial. -/
theorem coeff_eq_zero (p : degreeSeries G) (n : ℕ) (hn : N + 1 ≤ n) :
    PowerSeries.coeff n p.val = 0 := by
  have h := p.property n
  have hGn : G ^ n = ⊥ := pow_eq_zero_of_le hn hG
  rw [hGn] at h
  exact h

theorem trunc_coe (p : degreeSeries G) :
    (PowerSeries.trunc (N + 1) p.val : PowerSeries A) = p.val := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with hn
  · rfl
  · exact (coeff_eq_zero G N hG p n (by omega)).symm

/-- Forget the degree marker in a finite homogeneous completion. -/
def toPolynomial : degreeSeries G →ₐ[K] Polynomial A where
  toFun p := PowerSeries.trunc (N + 1) p.val
  map_zero' := by simp
  map_one' := by simp
  map_add' p q := by simp
  map_mul' p q := by
    apply Polynomial.coe_injective
    rw [trunc_coe G N hG, Polynomial.coe_mul, trunc_coe G N hG,
      trunc_coe G N hG]
    rfl
  commutes' r := by
    apply Polynomial.coe_injective
    rw [trunc_coe G N hG]
    simp [PowerSeries.algebraMap_apply]

/-- Evaluation at one is meaningful here because nilpotence made the
homogeneous completion finite before the degree marker was removed. -/
def evaluate : degreeSeries G →ₐ[K] A :=
  (Polynomial.eval₂AlgHom (AlgHom.id K A) (1 : A)
    (fun _ => Commute.one_right _)).comp (toPolynomial G N hG)

/-- A positive series in the finite homogeneous completion is nilpotent. -/
theorem positive_power_eq_zero (p : degreeSeries G)
    (hp : PowerSeries.coeff 0 p.val = 0) : p ^ (N + 1) = 0 := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  by_cases hn : n < N + 1
  · exact (coeff_pow_eq_zero hp hn).trans (map_zero _).symm
  · exact (coeff_eq_zero G N hG (p ^ (N + 1)) n (by omega)).trans (map_zero _).symm

/-- Scalar-series evaluation is genuinely a finite polynomial in this
completion, so every algebra map preserves it. -/
theorem seriesEval_eq_sum (c : ℕ → K) (p : degreeSeries G)
    (hp : PowerSeries.coeff 0 p.val = 0) :
    seriesEval G c p = ∑ i ∈ Finset.range (N + 1), c i • p ^ i := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro n
  by_cases hn : n < N + 1
  · rw [seriesEval_coeff_cutoff G c p hp n (N + 1) hn]
    have hs : (∑ i ∈ Finset.range (N + 1), c i • p ^ i : degreeSeries G).val =
        ∑ i ∈ Finset.range (N + 1), c i • p.val ^ i := by
      change (degreeSeries G).val (∑ i ∈ Finset.range (N + 1), c i • p ^ i) = _
      rw [map_sum]
      rfl
    rw [hs, map_sum]
    simp only [PowerSeries.coeff_smul]
  · rw [coeff_eq_zero G N hG (seriesEval G c p) n (by omega)]
    exact (coeff_eq_zero G N hG (∑ i ∈ Finset.range (N + 1), c i • p ^ i) n
      (by omega)).symm

theorem evaluate_eq_sum (p : degreeSeries G) :
    evaluate G N hG p = ∑ i ∈ Finset.range (N + 1), PowerSeries.coeff i p.val := by
  change Polynomial.eval₂ (RingHom.id A) (1 : A)
    (PowerSeries.trunc (N + 1) p.val) = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp

variable [CharZero K]

/-- Finite evaluation preserves the algebraic exponential, with exactly the
usual factorial coefficients. -/
theorem evaluate_exponential (p : degreeSeries G)
    (hp : PowerSeries.coeff 0 p.val = 0) :
    letI : Module ℚ A := Module.restrictScalars ℚ K A
    evaluate G N hG (exponential G p) = IsNilpotent.exp (evaluate G N hG p) := by
  let : Module ℚ A := Module.restrictScalars ℚ K A
  have hnil : (evaluate G N hG p) ^ (N + 1) = 0 := by
    rw [← map_pow, positive_power_eq_zero G N hG p hp, map_zero]
  rw [exponential, seriesEval_eq_sum G N hG _ p hp,
    map_sum, IsNilpotent.exp_eq_sum hnil]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, map_pow, ← Rat.cast_smul_eq_qsmul K]
  simp [expCoefficients]

end FiniteDegreeEvaluation

/-- Engel's theorem upgrades pointwise nilpotence of nilradical adjoints to
nilpotence of their joint action on the ambient algebra. -/
theorem nilradical_action_nilpotent : LieModule.IsNilpotent (nilradical k L) L := by
  apply (LieModule.isNilpotent_iff_forall (R := k)).mpr
  intro v
  exact nilpotent_ad k L v.val v.property

/-- The associative powers of the subspace of nilradical adjoints eventually
vanish. This supplies the finite evaluation bound for the BCH identity. -/
theorem adjointRange_power_eq_bot :
    ∃ N : ℕ, ((LieModule.toEnd k (nilradical k L) L).toLinearMap.range) ^ (N + 1) = ⊥ := by
  let G := (LieModule.toEnd k (nilradical k L) L).toLinearMap.range
  let := nilradical_action_nilpotent k L
  obtain ⟨N,hN⟩ := LieModule.IsNilpotent.nilpotent k (nilradical k L) L
  have hm {n : ℕ} {f : Module.End k L} (hf : f ∈ G ^ n) :
      ∀ x, f x ∈ LieModule.lowerCentralSeries k (nilradical k L) L n := by
    induction hf using Submodule.pow_induction_on_left' with
    | algebraMap r => intro x; trivial
    | add f g i hf hg ihf ihg =>
      intro x
      exact (LieModule.lowerCentralSeries k (nilradical k L) L i).add_mem (ihf x) (ihg x)
    | mem_mul f hf i g hg ih =>
      obtain ⟨v,rfl⟩ := hf
      intro x
      change ⁅v,g x⁆ ∈ LieModule.lowerCentralSeries k (nilradical k L) L (i + 1)
      rw [LieModule.lowerCentralSeries_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top v) (ih x)
  refine ⟨N,eq_bot_iff.mpr ?_⟩
  intro f hf
  change f = 0
  ext x
  have hx := LieModule.antitone_lowerCentralSeries k (nilradical k L) L
    (Nat.le_succ N) (hm hf x)
  rw [hN] at hx
  exact hx

/-- The finite BCH identity in the actual ambient adjoint representation.
The truncation bound comes from its joint nilpotent action. -/
theorem innerExponential_mul (x y : nilradical k L) :
    ∃ z : nilradical k L,
      (innerExponential k L z.val z.property).toLinearMap =
        (innerExponential k L x.val x.property).toLinearMap *
          (innerExponential k L y.val y.property).toLinearMap := by
  classical
  let : Module ℚ L := Module.restrictScalars ℚ k L
  let G := (LieModule.toEnd k (nilradical k L) L).toLinearMap.range
  obtain ⟨M,hM⟩ := adjointRange_power_eq_bot k L
  let N := M + 1
  have hG : G ^ (N + 1) = ⊥ := pow_eq_zero_of_le (by omega) hM
  let f : FormalBCH.Two k →ₗ[k] Module.End k L :=
    (LieModule.toEnd k (nilradical k L) L).toLinearMap.comp (NilpotentBCH.inputMap x y)
  let F := TensorAlgebra.lift k f
  have hF : (CompletedPrimitives.generators k (FormalBCH.Two k)).map F.toLinearMap ≤ G := by
    rintro a ⟨b,⟨v,rfl⟩,rfl⟩
    change (TensorAlgebra.lift k f) (TensorAlgebra.ι k v) ∈ G
    rw [TensorAlgebra.lift_ι_apply]
    exact ⟨NilpotentBCH.inputMap x y v,rfl⟩
  let C := CompletedPrimitives.completionMap _ G F hF
  let T := (FiniteDegreeEvaluation.evaluate G N hG).comp C
  have Te (p : CompletedPrimitives.Completion k (FormalBCH.Two k))
      (hp : CompletedPrimitives.Positive k (FormalBCH.Two k) p) :
      T (FormalExpLog.exponential (CompletedPrimitives.generators k (FormalBCH.Two k)) p) =
        IsNilpotent.exp (T p) := by
    change FiniteDegreeEvaluation.evaluate G N hG (C _) = _
    rw [show C (FormalExpLog.exponential _ p) = FormalExpLog.exponential G (C p) from
      FormalExpLog.map_exponential _ G F hF p]
    apply FiniteDegreeEvaluation.evaluate_exponential G N hG (C p)
    change F (PowerSeries.coeff 0 p.val) = 0
    exact (congrArg F hp).trans (map_zero F)
  have Tsum (p : CompletedPrimitives.Completion k (FormalBCH.Two k)) :
      T p = F (FormalBCH.tensorTruncation (N + 1) p) := by
    change FiniteDegreeEvaluation.evaluate G N hG (C p) = _
    rw [FiniteDegreeEvaluation.evaluate_eq_sum]
    unfold FormalBCH.tensorTruncation
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact CompletedPrimitives.completionMap_coeff _ G F hF p i
  have Tletter (v : FormalBCH.Two k) :
      T (FormalBCH.letter k (FormalBCH.Two k) v) = f v := by
    rw [Tsum]
    simp [FormalBCH.tensorTruncation, FormalBCH.letter_coeff,
      show 1 < N + 1 by omega, F]
  have TX : T (FormalBCH.X k) = LieAlgebra.ad k L x.val := by
    rw [FormalBCH.X, Tletter]
    simp [f, NilpotentBCH.inputMap]
    rfl
  have TY : T (FormalBCH.Y k) = LieAlgebra.ad k L y.val := by
    rw [FormalBCH.Y, Tletter]
    simp [f, NilpotentBCH.inputMap]
    rfl
  let z : nilradical k L := NilpotentBCH.product (k := k) N x y
  have Tz : T (FormalBCH.universalBCH k) = LieAlgebra.ad k L z.val := by
    rw [Tsum, ← NilpotentBCH.truncated_tensor]
    change (TensorAlgebra.lift k f) ((NilpotentBCH.truncatedPolynomial k N).eval
      (TensorAlgebra.ι k)) = _
    rw [NilpotentBCH.Polynomial.eval_tensor_lift]
    have he := NilpotentBCH.Polynomial.eval_map
      (LieModule.toEnd k (nilradical k L) L) (NilpotentBCH.inputMap x y)
      (NilpotentBCH.truncatedPolynomial k N)
    exact he.symm
  have he := congrArg T (FormalBCH.exponential_bch k (FormalBCH.Two k)
    (FormalBCH.X k) (FormalBCH.Y k))
  rw [map_mul, Te _ (FormalBCH.bch_positive _ _ _ _),
    Te _ (by simp [CompletedPrimitives.Positive, FormalBCH.X, FormalBCH.letter_coeff]),
    Te _ (by simp [CompletedPrimitives.Positive, FormalBCH.Y, FormalBCH.letter_coeff]),
    TX, TY] at he
  change IsNilpotent.exp (T (FormalBCH.universalBCH k)) = _ at he
  rw [Tz] at he
  refine ⟨z, ?_⟩
  change IsNilpotent.exp (LieDerivation.ad k L z.val).toLinearMap =
    IsNilpotent.exp (LieDerivation.ad k L x.val).toLinearMap *
      IsNilpotent.exp (LieDerivation.ad k L y.val).toLinearMap
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply]
  exact he


/-- Every finite product of inner exponentials from the nilradical is a
single inner exponential from that same ideal. -/
theorem exponentialProduct_eq_innerExponential (vs : List (nilradical k L)) :
    ∃ z : nilradical k L,
      exponentialProduct k L vs = innerExponential k L z.val z.property := by
  induction vs with
  | nil =>
    refine ⟨0, ?_⟩
    apply LieEquiv.ext
    intro x
    let : Module ℚ L := Module.restrictScalars ℚ k L
    change x = IsNilpotent.exp (LieDerivation.ad k L (0 : L)).toLinearMap x
    simp
  | cons v vs ih =>
    obtain ⟨z,hz⟩ := ih
    obtain ⟨w,hw⟩ := innerExponential_mul k L z v
    refine ⟨w, ?_⟩
    apply LieEquiv.ext
    intro x
    have hx := LinearMap.congr_fun hw x
    change innerExponential k L w.val w.property x =
      innerExponential k L z.val z.property
        (innerExponential k L v.val v.property x) at hx
    simpa only [exponentialProduct_cons, hz] using hx.symm

/-- Malcev conjugacy of arbitrary Levi factors by a single finite ambient
inner exponential, with its generator in the actual nilradical. -/
theorem conjugacy :
    Specs.LieAlgebrasAndRepresentations.LeviConjugacy.conjugacyType.{u,v} := by
  intro k L _ _ _ _ _ S T hS hT
  obtain ⟨vs,hvs⟩ := finiteProductConjugacy k L S T hS hT
  obtain ⟨z,hz⟩ := exponentialProduct_eq_innerExponential k L vs
  refine ⟨z.val,z.property,nilpotent_ad k L z.val z.property,
    innerExponential k L z.val z.property,
    innerExponential_toLinearMap k L z.val z.property, ?_⟩
  rwa [hz] at hvs

end LieAlgebrasAndRepresentations.LeviConjugacy
