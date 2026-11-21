import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertDegreewiseComparison
import MathGenome.Internal.AlgebraCore.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.P103.Ch06.LinearGradedNormalization
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

set_option linter.style.haveILetI false

namespace P103.HilbertDegreewiseComparison

open P103.Graded P103.HilbertSerreLength
open P103.Specs.Ch06.LinearGradedNormalization

universe u v w

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
theorem finite_components : Specs.P103.HilbertDegreewiseComparison.finiteComponentsType.{u,v,w} := by
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

section Degreewise

variable (k : Type u) {C : Type v} {M : Type w}
    [Field k] [CommRing C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G)
    {d : ℕ} (g : MvPolynomial (Fin d) k →ₐ[k] C) (hg : IsGraded G g)

include hg

omit [Module k M] [IsScalarTower k C M] in
/-- Projection onto a module degree extracts exactly the required homogeneous
part of a polynomial coefficient. The module generator may have negative degree. -/
theorem project_polynomial_smul (a j : ℤ) (haj : a ≤ j) (m : M)
    (hm : m ∈ U.piece a) (p : MvPolynomial (Fin d) k) :
    (DirectSum.decompose U.piece (g p • m) j : M) =
      g (MvPolynomial.homogeneousComponent (j - a).toNat p) • m := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
    have hp := MvPolynomial.isHomogeneous_monomial (σ := Fin d) c (rfl : e.degree = e.degree)
    have hmem : g (MvPolynomial.monomial e c) • m ∈ U.piece ((e.degree : ℤ) + a) :=
      SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) (hg _ _ hp) hm
    rw [MvPolynomial.homogeneousComponent_of_mem hp]
    by_cases he : (j - a).toNat = e.degree
    · have hj : (e.degree : ℤ) + a = j := by omega
      rw [ite_eq_left he, DirectSum.decompose_of_mem_same U.piece (hj ▸ hmem)]
    · have hj : (e.degree : ℤ) + a ≠ j := by omega
      rw [ite_eq_right he, map_zero, zero_smul, DirectSum.decompose_of_mem_ne U.piece hmem hj]
  | add p q hp hq =>
    simp only [map_add, add_smul, DirectSum.decompose_add]
    change (DirectSum.decompose U.piece (g p • m) j : M) +
      (DirectSum.decompose U.piece (g q • m) j : M) = _
    rw [hp, hq]

/-- Multiplication by a homogeneous generator, restricted to homogeneous pieces. -/
def homogeneousAction (a : ℤ) (m : M) (hm : m ∈ U.piece a)
    (n : ℕ) (t : ℤ) (ht : (n : ℤ) + a = t) :
    MvPolynomial.homogeneousSubmodule (Fin d) k n →ₗ[k] fieldComponent k G U hzero t where
  toFun p := ⟨g p • m, by
    change g p • m ∈ U.piece t
    rw [← ht]
    exact SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) (hg _ _ p.2) hm⟩
  map_add' p q := Subtype.ext (by simp [add_smul])
  map_smul' c p := Subtype.ext (by simp [smul_assoc])

variable {ι : Type*} [Fintype ι] (x : ι → M) (a : ι → ℤ)
    (hx : ∀ i, x i ∈ U.piece (a i))

/-- The map from shifted free pieces onto the j-th module piece. -/
noncomputable def shiftedFreeMap (j : ℤ) (haj : ∀ i, a i ≤ j) :
    (∀ i, MvPolynomial.homogeneousSubmodule (Fin d) k (j - a i).toNat) →ₗ[k]
      fieldComponent k G U hzero j :=
  ∑ i, (homogeneousAction k G U hzero g hg (a i) (x i) (hx i)
    (j - a i).toNat j (by have := haj i; omega)).comp (LinearMap.proj i)

/-- Generators give surjectivity in each degree after taking homogeneous coefficients. -/
theorem shiftedFreeMap_surjective
    (hgen : ∀ m : M, ∃ p : ι → MvPolynomial (Fin d) k, ∑ i, g (p i) • x i = m)
    (j : ℤ) (haj : ∀ i, a i ≤ j) :
    Function.Surjective (shiftedFreeMap k G U hzero g hg x a hx j haj) := by
  classical
  intro m
  obtain ⟨p, hp⟩ := hgen m
  refine ⟨fun i => ⟨MvPolynomial.homogeneousComponent (j - a i).toNat (p i),
    MvPolynomial.homogeneousComponent_mem _ _⟩, ?_⟩
  apply Subtype.ext
  simp only [shiftedFreeMap, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum]
  change (∑ i, g (MvPolynomial.homogeneousComponent (j - a i).toNat (p i)) • x i) = (m : M)
  simp_rw [← project_polynomial_smul k G U g hg (a _) j (haj _) _ (hx _)]
  have hsum := congrArg (fun z : M => (DirectSum.decompose U.piece z j : M)) hp
  rw [DirectSum.decompose_of_mem_same U.piece m.2] at hsum
  simpa only [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum] using hsum

/-- Multiplication on all the generators, restricted to polynomial degree n. -/
noncomputable def multiplicationMap (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin d) k n →ₗ[k]
      (∀ i, fieldComponent k G U hzero ((n : ℤ) + a i)) :=
  LinearMap.pi fun i => homogeneousAction k G U hzero g hg (a i) (x i) (hx i)
    n ((n : ℤ) + a i) rfl

/-- Faithfulness proves injectivity; no torsion-free hypothesis is needed. -/
theorem multiplicationMap_injective [FaithfulSMul C M] (hinj : Function.Injective g)
    (hgen : ∀ m : M, ∃ p : ι → MvPolynomial (Fin d) k, ∑ i, g (p i) • x i = m)
    (n : ℕ) : Function.Injective (multiplicationMap k G U hzero g hg x a hx n) := by
  intro p q hpq
  have heq : ∀ i, g (p : MvPolynomial (Fin d) k) • x i = g (q : MvPolynomial (Fin d) k) • x i :=
    fun i => congrArg Subtype.val (congrFun hpq i)
  apply Subtype.ext
  apply hinj
  apply eq_of_smul_eq_smul (α := M)
  intro m
  obtain ⟨c, rfl⟩ := hgen m
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_comm (g p) (g (c i)), smul_comm (g q) (g (c i)), heq i]

include hx

/-- Taking dimensions of the two concrete maps gives the binomial bounds. -/
theorem degreewise_finrank_bounds [FaithfulSMul C M] (hinj : Function.Injective g)
    (hgen : ∀ m : M, ∃ p : ι → MvPolynomial (Fin d) k, ∑ i, g (p i) • x i = m)
    (hfin : ∀ j, Module.Finite k (fieldComponent k G U hzero j))
    (hd : 0 < d) (j : ℤ) (hj : 0 ≤ j) (haj : ∀ i, a i ≤ j) :
    Module.finrank k (fieldComponent k G U hzero j) ≤
      ∑ i, ((j - a i).toNat + d - 1).choose (d - 1) ∧
    (j.toNat + d - 1).choose (d - 1) ≤
      ∑ i, Module.finrank k (fieldComponent k G U hzero (j + a i)) := by
  classical
  haveI (i : ι) := polynomial_piece_finite k d (j - a i).toNat
  haveI (t : ℤ) := hfin t
  have hu := LinearMap.finrank_le_finrank_of_surjective
    (shiftedFreeMap_surjective k G U hzero g hg x a hx hgen j haj)
  have hl := LinearMap.finrank_le_finrank_of_injective
    (multiplicationMap_injective k G U hzero g hg x a hx hinj hgen j.toNat)
  constructor
  · simpa only [Module.finrank_pi_fintype, polynomial_piece_finrank_choose k d _ hd] using hu
  · simp only [Module.finrank_pi_fintype, polynomial_piece_finrank_choose k d _ hd] at hl
    have hjcast : (j.toNat : ℤ) = j := by omega
    rw [hjcast] at hl
    exact hl

end Degreewise

/-- The complete comparison theorem, with canonical length coefficients. -/
theorem comparison : Specs.P103.HilbertDegreewiseComparison.comparisonType.{u,v,w} := by
  intro k C M _ _ _ _ _ _ _ _ _ _ G U hzero hstd
  classical
  letI : Module k M := Module.compHom M (algebraMap k C)
  letI : IsScalarTower k C M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨hfin, hlength⟩ := finite_components k G U hzero hstd
  obtain ⟨d, g, hinj, hfinite, hg, hdim, hrest⟩ := normalization_generators k G U hzero hstd
  refine ⟨d, hdim, ?_⟩
  intro hd
  letI : Module (MvPolynomial (Fin d) k) M := Module.compHom M g.toRingHom
  obtain ⟨_, s, hspan, hhom⟩ := hrest
  have hsne : s.Nonempty := by
    by_contra hs
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hs0, Finset.coe_empty, Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨m₀, hm₀⟩ := hsne
  letI : Nonempty s := ⟨⟨m₀, hm₀⟩⟩
  let r := Fintype.card s
  let e : Fin r ≃ s := (Fintype.equivFin s).symm
  let x : Fin r → M := fun i => (e i).val
  have hr : 0 < r := Fintype.card_pos
  have hrange : Set.range x = (s : Set M) := by
    ext m
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hm
      exact ⟨e.symm ⟨m, hm⟩, by simp [x]⟩
  choose a ha using fun i : Fin r => hhom (x i) (e i).property
  have hgen (m : M) : ∃ p : Fin r → MvPolynomial (Fin d) k,
      ∑ i, g (p i) • x i = m := by
    have hm : m ∈ Submodule.span (MvPolynomial (Fin d) k) (Set.range x) := by
      rw [hrange, hspan]
      trivial
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin d) k)).mp hm
    exact ⟨p, hp⟩
  let J : ℤ := max 0 (Finset.univ.sup' Finset.univ_nonempty a)
  have hJ0 : 0 ≤ J := le_max_left _ _
  have hJa (i : Fin r) : a i ≤ J :=
    (Finset.le_sup' a (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨r, hr, a, J, hJ0, hJa, ?_⟩
  intro j hj
  obtain ⟨hu, hl⟩ := degreewise_finrank_bounds k G U hzero g hg x a ha hinj hgen hfin hd j
    (hJ0.trans hj) (fun i => (hJa i).trans hj)
  constructor
  · simp only [hlength]
    exact_mod_cast hu
  · simp only [hlength]
    exact_mod_cast hl

end P103.HilbertDegreewiseComparison
