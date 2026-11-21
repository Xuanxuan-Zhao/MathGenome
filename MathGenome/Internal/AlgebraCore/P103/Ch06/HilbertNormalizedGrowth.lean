import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertNormalizedGrowth
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.P103.Ch06.LinearGradedNormalization
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertDegreewiseComparison
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertPolynomialGrowth
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

namespace P103.HilbertNormalizedGrowth

open P103.Graded P103.HilbertSerreLength
open P103.Specs.Ch06.LinearGradedNormalization

universe u v w

/-- A finitely supported Laurent series cannot have a positive reduced pole
at 1. This uses the concrete power-series identity, without asymptotics. -/
theorem exponent_zero_of_eventually_zero (h : ℤ → ℤ) (b : ℤ)
    (p : Polynomial ℤ) (e : ℕ) (hp : RationalPresentation h b p e)
    (hred : e = 0 ∨ p.eval 1 ≠ 0) (hz : ∃ J : ℤ, ∀ j ≥ J, h j = 0) : e = 0 := by
  rcases hred with he | hpone
  · exact he
  by_contra he
  obtain ⟨J, hJ⟩ := hz
  obtain ⟨r, hr⟩ := rationalPresentation_of_finite_support h b J hp.1 hJ
  have hs : shiftedSeries h b = (r : PowerSeries ℤ) := by
    simpa only [pow_zero, mul_one] using hr.2
  have hpoly : r * (1 - Polynomial.X) ^ e = p := by
    apply Polynomial.coe_injective (R := ℤ)
    simpa only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_X, ← hs] using hp.2
  apply hpone
  rw [← hpoly]
  simp [he]

section Scalars

variable (k : Type u) {C : Type v} [Field k] [CommRing C] [Algebra k C]

/-- The connected structural field maps onto the actual degree-zero ring. -/
def baseScalarMap (G : NonnegativeGrading C) (hzero : Connected k G) :
    k →+* Base G where
  toFun a := ⟨algebraMap k C a, (hzero _).mpr ⟨a, rfl⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ a b)
  map_mul' a b := Subtype.ext (map_mul _ a b)

theorem baseScalarMap_surjective (G : NonnegativeGrading C) (hzero : Connected k G) :
    Function.Surjective (baseScalarMap k G hzero) := by
  intro a
  obtain ⟨b, hb⟩ := (hzero a).mp a.2
  exact ⟨b, Subtype.ext hb⟩

theorem base_isArtinian (G : NonnegativeGrading C) (hzero : Connected k G) :
    IsArtinianRing (Base G) := by
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  let : Module.Finite k (Base G) := Module.Finite.of_surjective
    (Algebra.linearMap k (Base G)) (baseScalarMap_surjective k G hzero)
  exact IsArtinianRing.of_finite k (Base G)

end Scalars

/-- Compare lengths over the actual degree-zero ring with dimensions over
the specified structural field. No new field instance is put on A₀. -/
theorem finite_components : Specs.P103.HilbertNormalizedGrowth.finiteComponentsType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ _ G U hzero hstd
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  have hsurj : Function.Surjective (algebraMap k (Base G)) :=
    baseScalarMap_surjective k G hzero
  letI : Module.Finite k (Base G) :=
    Module.Finite.of_surjective (Algebra.linearMap k (Base G)) hsurj
  letI : IsScalarTower k (Base G) M :=
    IsScalarTower.of_algebraMap_smul fun a m => by
      change (algebraMap k C a) • m = a • m
      exact algebraMap_smul C a m
  letI : Algebra.FiniteType k C :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  letI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  have hfin (j : ℤ) : Module.Finite k (fieldComponent k G U hzero j) := by
    letI : Module (Base G) (fieldComponent k G U hzero j) := (component G U j).module
    letI : IsScalarTower k (Base G) (fieldComponent k G U hzero j) :=
      ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
    letI : Module.Finite (Base G) (fieldComponent k G U hzero j) :=
      component_finite_of_noetherian G U j
    exact Module.Finite.trans (Base G) (fieldComponent k G U hzero j)
  refine ⟨hfin, ?_⟩
  intro j
  letI : Module (Base G) (fieldComponent k G U hzero j) := (component G U j).module
  letI : IsScalarTower k (Base G) (fieldComponent k G U hzero j) :=
    ⟨fun a b m => Subtype.ext (smul_assoc a b (m : M))⟩
  haveI := hfin j
  have hlength := Module.length_eq_of_surjective
    (R := Base G) (M := fieldComponent k G U hzero j) hsurj
  rw [Module.length_eq_finrank] at hlength
  change ((Module.length (Base G) (fieldComponent k G U hzero j)).toNat : ℤ) =
    (Module.finrank k (fieldComponent k G U hzero j) : ℤ)
  rw [← hlength]
  simp

section FiniteSupport

variable {C : Type v} {M : Type w} [CommRing C] [AddCommGroup M] [Module C M]

/-- Degree projection is linear over the actual degree-zero ring. -/
noncomputable def componentProjection (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (j : ℤ) : M →ₗ[Base G] component G U j where
  toFun m := DirectSum.decompose U.piece m j
  map_add' x y := by
    apply Subtype.ext
    exact congrArg (fun z => (z j : M)) (DirectSum.decompose_add U.piece x y)
  map_smul' a m := by
    apply Subtype.ext
    change (DirectSum.decompose U.piece ((a : C) • m) j : M) =
      (a : C) • (DirectSum.decompose U.piece m j : M)
    have h := decompose_homogeneous_smul G U 0 j a m
    rw [sub_zero] at h
    exact h

/-- Bounded support together with finite homogeneous pieces implies ordinary
finite generation over the degree-zero ring. -/
theorem finite_base_of_bounded_support (G : NonnegativeGrading C) (U : ModuleGrading G M)
    [IsNoetherianRing (Base G)] [∀ j, Module.Finite (Base G) (component G U j)]
    (b J : ℤ) (hb : ∀ j < b, U.piece j = ⊥) (hJ : ∀ j ≥ J, U.piece j = ⊥) :
    Module.Finite (Base G) M := by
  classical
  let D := ↥(Finset.Ico b J)
  letI : Fintype D := Finset.fintypeCoeSort _
  let f : M →ₗ[Base G] (∀ j : D, component G U j) :=
    LinearMap.pi fun j => componentProjection G U j
  haveI (j : D) : IsNoetherian (Base G) (component G U j) :=
    isNoetherian_of_isNoetherianRing_of_finite (Base G) (component G U j)
  haveI : Module.Finite (Base G) (∀ j : D, component G U j) := Module.Finite.pi
  haveI : IsNoetherian (Base G) (∀ j : D, component G U j) :=
    isNoetherian_of_isNoetherianRing_of_finite (Base G) (∀ j : D, component G U j)
  apply Module.Finite.of_injective f
  intro x y hxy
  apply (DirectSum.decomposeAddEquiv U.piece).injective
  ext j
  by_cases hj : j ∈ Finset.Ico b J
  · exact congrArg Subtype.val (congrFun hxy ⟨j, hj⟩)
  · have hbot : U.piece j = ⊥ := by
      by_cases hjb : j < b
      · exact hb j hjb
      · exact hJ j (by simp only [Finset.mem_Ico] at hj; omega)
    have hz (m : M) : (DirectSum.decompose U.piece m j : M) = 0 := by
      have hm := (DirectSum.decompose U.piece m j).2
      simpa only [hbot, AddSubgroup.mem_bot] using hm
    exact (hz x).trans (hz y).symm

theorem piece_eq_bot_of_hilbertFunction_eq_zero (G : NonnegativeGrading C)
    (U : ModuleGrading G M) [IsArtinianRing (Base G)] [Module.Finite C M]
    (hstd : Specs.P103.Graded.standardValue G) (j : ℤ)
    (hj : hilbertFunction G U j = 0) : U.piece j = ⊥ := by
  have hfin := finite_length G U hstd j
  have hne : Module.length (Base G) (component G U j) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr hfin
  have hlen : Module.length (Base G) (component G U j) = 0 := by
    unfold hilbertFunction at hj
    have hz : (Module.length (Base G) (component G U j)).toNat = 0 := by
      exact_mod_cast hj
    exact (ENat.toNat_eq_zero.mp hz).resolve_right hne
  haveI : Subsingleton (component G U j) := Module.length_eq_zero_iff.mp hlen
  apply le_antisymm _ bot_le
  intro m hm
  change m = 0
  exact congrArg Subtype.val (Subsingleton.elim (⟨m, hm⟩ : component G U j) 0)

end FiniteSupport

/-- A faithful algebra acting on a finite module over a Noetherian base is
itself finite over that base. The injection is the actual representation. -/
theorem finite_algebra_of_faithful_finite_module
    (R : Type u) (C : Type v) (M : Type w) [CommRing R] [CommRing C]
    [Algebra R C] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module C M]
    [IsScalarTower R C M] [FaithfulSMul C M] [Module.Finite R M] :
    Module.Finite R C := by
  apply Module.Finite.of_injective (Algebra.lsmul R R M).toLinearMap
  intro x y hxy
  exact eq_of_smul_eq_smul (fun m : M => DFunLike.congr_fun hxy m)

/-- Zero-dimensional normalization makes the module finite over the field;
its grading then has finite support. -/
theorem dimension_zero : Specs.P103.HilbertNormalizedGrowth.dimensionZeroType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ G U hzero hstd hdim b p e hp hred
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  letI : Module k M := Module.compHom M (algebraMap k C)
  letI : IsScalarTower k C M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower k (Base G) M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite k C :=
    P103.Ch06.LinearGradedNormalization.dimension_zero k C G hzero hstd hdim
  haveI : Module.Finite k M := Module.Finite.trans C M
  haveI : Module.Finite (Base G) M := Module.Finite.of_restrictScalars_finite k (Base G) M
  obtain ⟨J, hJ⟩ := bounded_above_of_finite_base G U
  exact exponent_zero_of_eventually_zero _ b p e hp hred
    ⟨J, fun j hj => hilbertFunction_eq_zero_of_piece_eq_bot G U j (hJ j hj)⟩

/-- The reverse boundary implication uses faithfulness, and rules out hiding
a positive-dimensional algebra inside an eventually vanishing module. -/
theorem dimension_zero_of_exponent_zero
    (k : Type u) {C : Type v} {M : Type w}
    [Field k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [FaithfulSMul C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (hstd : Specs.P103.Graded.standardValue G)
    (b : ℤ) (p : Polynomial ℤ)
    (hp : RationalPresentation (hilbertFunction G U) b p 0) : ringKrullDim C = 0 := by
  letI : Algebra k (Base G) := (baseScalarMap k G hzero).toAlgebra
  haveI : Module.Finite k (Base G) := Module.Finite.of_surjective
    (Algebra.linearMap k (Base G)) (baseScalarMap_surjective k G hzero)
  haveI : IsArtinianRing (Base G) := base_isArtinian k G hzero
  haveI : Algebra.FiniteType k C :=
    P103.Ch06.LinearGradedNormalization.finiteType_of_standard G hzero hstd
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing k C
  haveI (j : ℤ) : Module.Finite (Base G) (component G U j) :=
    component_finite_of_noetherian G U j
  obtain ⟨q, _, hq, _⟩ := coefficients _ b p 0 hp
  obtain ⟨_, J, hJ⟩ := hq rfl
  obtain ⟨B, hB⟩ := P103.Graded.bounded_below G U
  haveI : Module.Finite (Base G) M := finite_base_of_bounded_support G U B J hB
    (fun j hj => piece_eq_bot_of_hilbertFunction_eq_zero G U hstd j (hJ j hj))
  letI : IsScalarTower (Base G) C M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite (Base G) C := finite_algebra_of_faithful_finite_module (Base G) C M
  letI hTower : IsScalarTower k (Base G) C :=
    IsScalarTower.of_algebraMap_smul fun a c => by
      change algebraMap k C a * c = a • c
      exact Algebra.smul_def a c |>.symm
  haveI : Module.Finite k C := by
    exact @Module.Finite.trans k (Base G) C _ _ _ _ _ _ hTower inferInstance inferInstance
  haveI : IsArtinianRing C := IsArtinianRing.of_finite k C
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

theorem exponent_zero : Specs.P103.HilbertNormalizedGrowth.exponentZeroType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ _ _ G U hzero hstd b p e hp hred
  constructor
  · intro he
    subst e
    exact dimension_zero_of_exponent_zero k G U hzero hstd b p hp
  · intro hd
    exact dimension_zero k G U hzero hstd hd b p e hp hred

/-- The ordinary homogeneous polynomial piece has a monomial basis.
This counts the actual vector space, including zero variables and degree zero. -/
theorem polynomial_piece_finrank (k : Type u) [Field k] (d n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) =
      Nat.multichoose d n := by
  classical
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  change Module.finrank k (MvPolynomial.restrictSupport k
    {m : Fin d →₀ ℕ | Finsupp.degree m = n}) = _
  let S := {m : Fin d →₀ ℕ | Finsupp.degree m = n}
  let e : Sym (Fin d) n ≃ S := Sym.equivNatSum (Fin d) n
  letI : Fintype S := Fintype.ofEquiv (Sym (Fin d) n) e
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport k S),
    ← Fintype.card_congr e, Sym.card_sym_eq_multichoose, Fintype.card_fin]

theorem polynomial_piece_finrank_choose (k : Type u) [Field k] (d n : ℕ) (hd : 0 < d) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin d) k n) =
      (n + d - 1).choose (d - 1) := by
  rw [polynomial_piece_finrank, Nat.multichoose_eq]
  have hle : n ≤ d + n - 1 := by omega
  rw [← Nat.choose_symm hle]
  congr 1 <;> omega

theorem polynomial_piece_finite (k : Type u) [Field k] (d n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin d) k n) :=
  Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (Fin d) k n)

/-- Taking all components of ordinary finite generators works over any
chosen scalar ring. In particular the normalization subring need not have
the same finite generating set as the original algebra. -/
theorem homogeneous_generators_over (R : Type u) {C : Type v} {M : Type w}
    [Semiring R] [CommRing C] [AddCommGroup M] [Module C M] [Module R M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) [Module.Finite R M] :
    ∃ s : Finset M, Submodule.span R (s : Set M) = ⊤ ∧
      ∀ m ∈ s, ∃ j : ℤ, m ∈ U.piece j := by
  classical
  obtain ⟨F, hF⟩ := Module.Finite.fg_top (R := R) (M := M)
  let I := Σ (x : F), (DirectSum.decompose U.piece x.1).support
  let x (i : I) : M := (DirectSum.decompose U.piece i.1.1 i.2.1 : M)
  refine ⟨Finset.univ.image x, ?_, ?_⟩
  · rw [← top_le_iff, ← hF]
    apply Submodule.span_le.mpr
    intro m hm
    rw [← DirectSum.sum_support_decompose U.piece m]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨⟨⟨m, hm⟩, j, hj⟩, Finset.mem_univ _, rfl⟩
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact ⟨i.2.1, (DirectSum.decompose U.piece i.1.1 i.2.1).2⟩

/-- Normalization supplies homogeneous generators over the polynomial ring,
with ordinary finite generation and faithfulness after restriction proved. -/
theorem normalization_generators
    (k : Type u) {C : Type v} {M : Type w}
    [Field k] [Infinite k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [FaithfulSMul C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (hstd : Specs.P103.Graded.standardValue G) :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) k →ₐ[k] C),
      Function.Injective g ∧ g.Finite ∧ IsGraded G g ∧
      ringKrullDim C = (d : WithBot ℕ∞) ∧
      (letI : Module (MvPolynomial (Fin d) k) M := Module.compHom M g.toRingHom
       FaithfulSMul (MvPolynomial (Fin d) k) M ∧
       ∃ s : Finset M, Submodule.span (MvPolynomial (Fin d) k) (s : Set M) = ⊤ ∧
         ∀ m ∈ s, ∃ j : ℤ, m ∈ U.piece j) := by
  obtain ⟨d, g, hinj, hfin, hgraded, _, hdim⟩ :=
    P103.Ch06.LinearGradedNormalization.normalization_map k C G hzero hstd
  refine ⟨d, g, hinj, hfin, hgraded, hdim, ?_⟩
  letI : Algebra (MvPolynomial (Fin d) k) C := g.toRingHom.toAlgebra
  letI : Module (MvPolynomial (Fin d) k) M := Module.compHom M g.toRingHom
  letI : IsScalarTower (MvPolynomial (Fin d) k) C M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite (MvPolynomial (Fin d) k) C := hfin
  haveI : Module.Finite (MvPolynomial (Fin d) k) M := Module.Finite.trans C M
  refine ⟨⟨fun {x y} hxy => hinj (eq_of_smul_eq_smul (fun m : M => hxy m))⟩, ?_⟩
  exact homogeneous_generators_over (MvPolynomial (Fin d) k) G U

/-- The two degreewise estimates force the reduced pole order to equal the
number of normalization variables. The zero-dimensional case uses finite
support instead, so the conclusion includes exponent zero. -/
theorem normalized_growth :
    Specs.P103.HilbertNormalizedGrowth.normalizedGrowthType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ _ _ G U hzero hstd b p e hp hred
  obtain ⟨d, hdim, hbounds⟩ :=
    P103.HilbertDegreewiseComparison.comparison k G U hzero hstd
  by_cases hd : d = 0
  · have hdimzero : ringKrullDim C = 0 := by simpa only [hd, Nat.cast_zero] using hdim
    have he := dimension_zero k G U hzero hstd hdimzero b p e hp hred
    simpa only [he, Nat.cast_zero] using hdimzero
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    obtain ⟨r, hr, a, J, hJ, ha, hbound⟩ := hbounds hdpos
    have he : e = d := P103.HilbertPolynomialGrowth.comparison
      (hilbertFunction G U) b p e
      (fun j => Int.natCast_nonneg _) hp hred d r hdpos hr a J hJ ha
      (fun j hj => (hbound j hj).1) (fun j hj => (hbound j hj).2)
    simpa only [he] using hdim

end P103.HilbertNormalizedGrowth
