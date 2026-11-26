import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.OrderedValuationGroups
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound
import Mathlib.LinearAlgebra.Dimension.Finite

noncomputable section

namespace CommutativeAlgebraNotes.FiniteValuationDegreeBound

open CommutativeAlgebraNotes.OrderedValuationGroups
open Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound (inclusion)
open Additive (ofMul)
open IsLocalRing (ResidueField residue)
open scoped BigOperators

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  (V : ValuationSubring K) (W : ValuationSubring L)
  (h : W.comap (algebraMap K L) = V)

local notation "ιₐ" => algebraMap K L

include h in
private theorem mem_iff (x : K) : ιₐ x ∈ W ↔ x ∈ V := by
  rw [← h]
  rfl

include h in
private theorem valuation_le_iff (x y : K) :
    W.valuation (ιₐ x) ≤ W.valuation (ιₐ y) ↔ V.valuation x ≤ V.valuation y := by
  rw [W.valuation_le_iff, V.valuation_le_iff]
  constructor
  · intro he
    by_cases hy : y = 0
    · subst y
      obtain ⟨w, hw⟩ := he
      have hx : x = 0 := (ιₐ).injective (by simpa using hw.symm)
      exact ⟨0, by simp [hx]⟩
    · obtain ⟨w, hw⟩ := he
      have hd : ιₐ (x / y) = (w : L) := by
        rw [map_div₀, div_eq_iff ((map_ne_zero ιₐ).mpr hy)]
        exact hw.symm
      exact ⟨⟨x / y, (mem_iff V W h _).mp (hd ▸ w.property)⟩, div_mul_cancel₀ x hy⟩
  · rintro ⟨a, ha⟩
    exact ⟨inclusion V W h a, by
      change ιₐ (a : K) * ιₐ y = ιₐ x
      rw [← map_mul, ha]⟩

private abbrev fieldUnits : Additive Kˣ →+ Additive Lˣ :=
  MonoidHom.toAdditive (Units.map (algebraMap K L).toMonoidHom)

include h in
private theorem compare_values (a b : Additive Kˣ) :
    value W (fieldUnits a) ≤ value W (fieldUnits b) ↔ value V a ≤ value V b := by
  change Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom
      (Units.map (ιₐ).toMonoidHom (Additive.toMul b)) ≤
    Units.map W.valuation.toMonoidWithZeroHom.toMonoidHom
      (Units.map (ιₐ).toMonoidHom (Additive.toMul a)) ↔
    Units.map V.valuation.toMonoidWithZeroHom.toMonoidHom (Additive.toMul b) ≤
    Units.map V.valuation.toMonoidWithZeroHom.toMonoidHom (Additive.toMul a)
  rw [← Units.val_le_val, ← Units.val_le_val]
  exact valuation_le_iff V W h _ _

include h in
private theorem exists_value_map :
    ∃ g : ValueGroup V →+o ValueGroup W,
      StrictMono g ∧ ∀ a : Additive Kˣ, g (value V a) = value W (fieldUnits a) := by
  let f : Additive Kˣ →+ ValueGroup W := (value W).comp fieldUnits
  have hker : (value V).ker ≤ f.ker := by
    intro a ha
    rw [AddMonoidHom.mem_ker] at ha ⊢
    have hv : value V a = value V 0 := ha.trans (map_zero _).symm
    have hf : f a = f 0 := le_antisymm
      ((compare_values V W h a 0).mpr hv.le) ((compare_values V W h 0 a).mpr hv.ge)
    exact hf.trans (map_zero _)
  let g := (value V).liftOfSurjective (value_surjective V) ⟨f, hker⟩
  have hg (a : Additive Kˣ) : g (value V a) = f a :=
    (value V).liftOfRightInverse_comp_apply _ _ _ a
  have ho (x y : ValueGroup V) : g x ≤ g y ↔ x ≤ y := by
    obtain ⟨a, rfl⟩ := value_surjective V x
    obtain ⟨b, rfl⟩ := value_surjective V y
    rw [hg, hg]
    exact compare_values V W h _ _
  exact ⟨{ g with monotone' := fun x y hxy => (ho x y).mpr hxy },
    fun x y hxy => (lt_iff_not_ge).mpr (fun hyx => hxy.not_ge ((ho y x).mp hyx)), hg⟩

private theorem inclusion_isLocalHom : IsLocalHom (inclusion V W h) := by
  constructor
  intro a ha
  have hW : W.valuation (ιₐ (a : K)) = 1 :=
    (W.valuation_eq_one_iff (inclusion V W h a)).mp ha
  have he : W.valuation (ιₐ (a : K)) = W.valuation (ιₐ 1) := by simpa using hW
  apply (V.valuation_eq_one_iff a).mpr
  rw [← V.valuation.map_one]
  exact le_antisymm ((valuation_le_iff V W h _ _).mp he.le)
    ((valuation_le_iff V W h _ _).mp he.ge)

section LinearIndependence

variable [Algebra (ResidueField V) (ResidueField W)]
  (hr : (algebraMap (ResidueField V) (ResidueField W)).comp (residue V) =
    (residue W).comp (inclusion V W h))

include hr in
/-- A nontrivial coefficient block has the valuation of one of its coefficients. -/
private theorem block_value {J : Type*} [Fintype J] (y : J → W)
    (hy : LinearIndependent (ResidueField V) (fun j => residue W (y j)))
    (a : J → K) (ha : ∃ j, a j ≠ 0) :
    ∃ j, a j ≠ 0 ∧
      W.valuation (∑ k, ιₐ (a k) * (y k : L)) = W.valuation (ιₐ (a j)) := by
  classical
  -- In the multiplicative convention, a largest valuation is a least additive value.
  obtain ⟨j₁, hj₁⟩ := ha
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun k => V.valuation (a k))
    ⟨j₁, Finset.mem_univ _⟩
  have hjmax (k : J) : V.valuation (a k) ≤ V.valuation (a j) := hj k (Finset.mem_univ _)
  have hjne : a j ≠ 0 := by
    intro hz
    have he := hjmax j₁
    rw [hz, map_zero, le_zero_iff, map_eq_zero] at he
    exact hj₁ he
  let c (k : J) : V := ⟨a k / a j, by
    rw [← V.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (V.valuation.pos_iff.mpr hjne)).mpr (hjmax k)⟩
  have hc (k : J) : ιₐ (a k) = ιₐ (a j) * ιₐ (c k : K) := by
    rw [← map_mul]
    exact congrArg ιₐ ((mul_comm _ _).trans (div_mul_cancel₀ (a k) hjne)).symm
  have hcj : c j = 1 := Subtype.ext (div_self hjne)
  let d : W := ∑ k, inclusion V W h (c k) * y k
  have hdres : residue W d ≠ 0 := by
    intro hz
    have he : ∑ k, residue V (c k) • residue W (y k) = 0 := by
      have hcres (k : J) :
          algebraMap (ResidueField V) (ResidueField W) (residue V (c k)) =
            residue W (inclusion V W h (c k)) := DFunLike.congr_fun hr (c k)
      simpa only [d, map_sum, map_mul, Algebra.smul_def, hcres] using hz
    have hzero := (Fintype.linearIndependent_iff.mp hy) (fun k => residue V (c k)) he j
    simp [hcj] at hzero
  have hdval : W.valuation (d : L) = 1 := by
    apply (W.valuation_eq_one_iff d).mp
    exact (IsLocalRing.residue_ne_zero_iff_isUnit d).mp hdres
  refine ⟨j, hjne, ?_⟩
  have hsum : (∑ k, ιₐ (a k) * (y k : L)) = ιₐ (a j) * (d : L) := by
    change (∑ k, ιₐ (a k) * (y k : L)) =
      ιₐ (a j) * W.toSubring.subtype (∑ k, inclusion V W h (c k) * y k)
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      change ιₐ (a k) * (y k : L) = ιₐ (a j) * (ιₐ (c k : K) * (y k : L))
      rw [← mul_assoc, ← hc]
  rw [hsum, map_mul, hdval, mul_one]


variable (g : ValueGroup V →+o ValueGroup W)
  (hg : ∀ a : Additive Kˣ, g (value V a) = value W (fieldUnits a))

local notation "q" => QuotientAddGroup.mk' g.toAddMonoidHom.range

include hr hg in
private theorem products_independent_finite {I J : Type*} [Fintype I] [Fintype J]
    (x : I → Lˣ) (hx : Function.Injective (fun i => q (value W (ofMul (x i)))))
    (y : J → W) (hy : LinearIndependent (ResidueField V) (fun j => residue W (y j))) :
    LinearIndependent K (fun p : I × J => (x p.1 : L) * (y p.2 : L)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha p
  by_contra hp
  let t (i : I) := (x i : L) * ∑ j, ιₐ (a (i, j)) * (y j : L)
  have htValue (i : I) (hi : ∃ j, a (i, j) ≠ 0) :
      ∃ j, a (i, j) ≠ 0 ∧ W.valuation (t i) =
        W.valuation ((x i : L) * ιₐ (a (i, j))) := by
    obtain ⟨j, hj, hjval⟩ := block_value V W h hr y hy (fun j => a (i, j)) hi
    refine ⟨j, hj, ?_⟩
    simp only [t, map_mul, hjval]
  have hpval : W.valuation (t p.1) ≠ 0 := by
    obtain ⟨j, hj, hval⟩ := htValue p.1 ⟨p.2, hp⟩
    rw [hval, W.valuation.ne_zero_iff]
    exact mul_ne_zero (x p.1).ne_zero ((map_ne_zero ιₐ).mpr hj)
  have htCoset (i : I) (hi : t i ≠ 0) :
      q (value W (ofMul (Units.mk0 (t i) hi))) = q (value W (ofMul (x i))) := by
    have hi' : ∃ j, a (i, j) ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hi (by simp [t, hn])
    obtain ⟨j, hj, hval⟩ := htValue i hi'
    let aUnit := ofMul (Units.mk0 (a (i, j)) hj)
    have hEq : value W (ofMul (Units.mk0 (t i) hi)) =
        value W (ofMul (x i)) + g (value V aUnit) := by
      rw [hg, ← map_add]
      apply Units.ext
      exact hval
    have hqZero : q (g (value V aUnit)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨value V aUnit, rfl⟩
    rw [hEq, map_add, hqZero, add_zero]
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => W.valuation (t i))
    ⟨p.1, Finset.mem_univ _⟩
  have hipos : 0 < W.valuation (t i) :=
    (pos_iff_ne_zero.mpr hpval).trans_le (hmax p.1 (Finset.mem_univ _))
  have hiti : t i ≠ 0 := by
    intro hz
    simp [hz] at hipos
  -- Every nonzero block has the coset of its chosen representative.
  have hsumVal : W.valuation (∑ k, t k) = W.valuation (t i) := by
    apply W.valuation.map_sum_eq_of_lt hi
    intro k hk
    obtain ⟨hku, hki⟩ := Finset.mem_sdiff.mp hk
    apply lt_of_le_of_ne (hmax k hku)
    intro he
    have hkt : t k ≠ 0 := by
      intro hz
      rw [hz, map_zero] at he
      exact hipos.ne' he.symm
    have hv : value W (ofMul (Units.mk0 (t k) hkt)) =
        value W (ofMul (Units.mk0 (t i) hiti)) := Units.ext he
    have hki' : k = i := hx ((htCoset k hkt).symm.trans
      ((congrArg q hv).trans (htCoset i hiti)))
    exact hki (by simp [hki'])
  have hsum : (∑ k, t k) = 0 := by
    rw [← ha, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [t, Finset.mul_sum, Algebra.smul_def]
    exact Finset.sum_congr rfl fun j _ => by ac_rfl
  rw [hsum, map_zero] at hsumVal
  exact hipos.ne' hsumVal.symm

include hr hg in
private theorem products_independent {I J : Type*}
    (x : I → Lˣ) (hx : Function.Injective (fun i => q (value W (ofMul (x i)))))
    (y : J → W) (hy : LinearIndependent (ResidueField V) (fun j => residue W (y j))) :
    LinearIndependent K (fun p : I × J => (x p.1 : L) * (y p.2 : L)) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  -- Each finite subfamily is contained in a finite rectangle of indices.
  let s₁ := s.image Prod.fst
  let s₂ := s.image Prod.snd
  let embed (p : s) : s₁ × s₂ :=
    (⟨p.1.1, Finset.mem_image_of_mem Prod.fst p.2⟩,
     ⟨p.1.2, Finset.mem_image_of_mem Prod.snd p.2⟩)
  have hembed : Function.Injective embed := by
    intro a b he
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p : s₁ × s₂ => p.1.1) he)
      (congrArg (fun p : s₁ × s₂ => p.2.1) he)
  exact (products_independent_finite V W h hr g hg
    (fun i : s₁ => x i) (hx.comp Subtype.val_injective)
    (fun j : s₂ => y j) (hy.comp _ Subtype.val_injective)).comp embed hembed

end LinearIndependence

/-- The intrinsic ramification index and residue degree are finite, and their product
is bounded by the field degree. -/
theorem degree_bound :
    Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound.DegreeBound.{u, v} := by
  classical
  intro K L _ _ _ _ V W h
  obtain ⟨g, hgMono, hg⟩ := exists_value_map V W h
  let : IsLocalHom (inclusion V W h) := inclusion_isLocalHom V W h
  let r := ResidueField.map (inclusion V W h)
  let : Algebra (ResidueField V) (ResidueField W) := r.toAlgebra
  have hr : r.comp (residue V) = (residue W).comp (inclusion V W h) :=
    ResidueField.map_comp_residue _
  let H := g.toAddMonoidHom.range
  let Q := ValueGroup W ⧸ H
  let q : ValueGroup W →+ Q := QuotientAddGroup.mk' H
  have hxExists (i : Q) : ∃ a : Lˣ, q (value W (ofMul a)) = i :=
    (QuotientAddGroup.mk'_surjective H).comp (value_surjective W) i
  choose x hx using hxExists
  let J := Module.Free.ChooseBasisIndex (ResidueField V) (ResidueField W)
  let b : Module.Basis J (ResidueField V) (ResidueField W) := Module.Free.chooseBasis _ _
  have hyExists (j : J) : ∃ w : W, residue W w = b j := IsLocalRing.residue_surjective (b j)
  choose y hy using hyExists
  have hyIndependent : LinearIndependent (ResidueField V) (fun j => residue W (y j)) := by
    simpa only [hy] using b.linearIndependent
  have hxInjective : Function.Injective (fun i => q (value W (ofMul (x i)))) := by
    intro i j hij
    exact (hx i).symm.trans (hij.trans (hx j))
  have hIndependent : LinearIndependent K (fun p : Q × J => (x p.1 : L) * (y p.2 : L)) :=
    products_independent V W h hr g hg x hxInjective y hyIndependent
  let : Finite (Q × J) := Cardinal.mk_lt_aleph0_iff.mp
    (hIndependent.cardinalMk_le_finrank.trans_lt Cardinal.natCast_lt_aleph0)
  let : Nonempty J := b.index_nonempty
  let : Finite Q := Finite.prod_left J
  let : Finite J := Finite.prod_right Q
  refine ⟨g, r, hgMono, r.injective, hg, hr, ‹Finite Q›, Module.Finite.of_basis b, ?_⟩
  change Nat.card Q * Module.finrank (ResidueField V) (ResidueField W) ≤ Module.finrank K L
  let : Fintype (Q × J) := Fintype.ofFinite _
  rw [Module.finrank_eq_nat_card_basis b, ← Nat.card_prod, Nat.card_eq_fintype_card]
  exact hIndependent.fintype_card_le_finrank

end CommutativeAlgebraNotes.FiniteValuationDegreeBound
