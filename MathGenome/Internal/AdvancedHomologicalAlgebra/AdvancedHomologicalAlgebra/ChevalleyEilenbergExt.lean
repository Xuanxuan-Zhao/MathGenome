import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ChevalleyEilenbergGraded
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SymmetricKoszulExactness
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergExt
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions

/-! Work on HA-A07: the actual augmented CE complex, without rank or
characteristic restrictions. No unproved Ext implementation is imported. -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct DirectSum
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Every CE term is free over the enveloping algebra, in arbitrary rank. -/
theorem term_free [Module.Free k g] (n : ℕ) : Module.Free (U k g) (V k g n) := by
  infer_instance

/-- The CE augmentation is onto, including over the zero ring. -/
theorem augmentation_surjective : Function.Surjective (augmentation k g) := by
  intro r
  refine ⟨(1 : U k g) ⊗ₜ[k] (exteriorPower.zeroEquiv k g).symm r, ?_⟩
  simp [augmentation]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct DirectSum
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I k g)

/-- Polynomial total degree is the length of its corresponding ordered word. -/
theorem orderedWord_degree (l : Shared.Lie.PBW.OrderedWord I) :
    (Shared.Lie.PBW.Graded.orderedWordExponents l).degree = l.val.length := by
  change (Multiset.toFinsupp (l.val : Multiset I)).sum (fun _ n => n) = _
  exact Multiset.toFinsupp_sum_eq (l.val : Multiset I)

/-- Each monomial basis vector belongs to the specified homogeneous submodule. -/
theorem symmetric_basis_mem (m : I →₀ ℕ) :
    b.symmetricAlgebra m ∈ Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m.degree := by
  let l := Shared.Lie.PBW.Graded.orderedWordExponents.symm m
  have he : Shared.Lie.PBW.Graded.orderedSymmetricBasis b l = b.symmetricAlgebra m := by
    simp [Shared.Lie.PBW.Graded.orderedSymmetricBasis, l]
  rw [← he, Shared.Lie.PBW.Graded.orderedSymmetricBasis_apply]
  apply Submodule.subset_span
  refine ⟨l.val.map b, ?_, rfl⟩
  rw [List.length_map, ← orderedWord_degree l]
  simp [l]

/-- The basis-free homogeneous submodule is spanned by monomials of that degree. -/
theorem symmetricDegree_eq_basis_span (m : ℕ) :
    Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m =
      Submodule.span k (b.symmetricAlgebra '' {d | d.degree = m}) := by
  apply le_antisymm
  · intro p hp
    have hmap : Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g) p ∈
        LinearMap.range (DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m) := by
      rw [← Shared.Lie.PBW.Graded.canonicalMap_degree b m]
      exact ⟨p, hp, rfl⟩
    obtain ⟨q, hq⟩ := hmap
    induction q using Submodule.Quotient.induction_on with
    | _ a =>
      have hs := Shared.Lie.PBW.Graded.symbol_mem_degree_span b m a
      have hm : Submodule.span k (Shared.Lie.PBW.Graded.gradedWord b '' {l | l.val.length = m}) ≤
          Submodule.map (Shared.Lie.PBW.Graded.canonicalMap (k := k) (g := g)).toLinearMap
            (Submodule.span k (b.symmetricAlgebra '' {d | d.degree = m})) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨l, hl, rfl⟩
        refine ⟨Shared.Lie.PBW.Graded.orderedSymmetricBasis b l, ?_, ?_⟩
        · apply Submodule.subset_span
          refine ⟨Shared.Lie.PBW.Graded.orderedWordExponents l, ?_, ?_⟩
          · exact (orderedWord_degree l).trans hl
          · simp [Shared.Lie.PBW.Graded.orderedSymmetricBasis]
        · simp
      have hsp := hm hs
      change DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m
        (Shared.Lie.PBW.Graded.principal k g m a) = _ at hq
      change DirectSum.lof k ℕ (Shared.Lie.PBW.Graded.Piece k g) m
        (Shared.Lie.PBW.Graded.principal k g m a) ∈ _ at hsp
      rw [hq] at hsp
      obtain ⟨p', hp', he⟩ := hsp
      have he' : p' = p := Shared.Lie.PBW.Graded.canonicalMap_bijective.1 he
      exact he' ▸ hp'
  · apply Submodule.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change d.degree = m at hd
    change b.symmetricAlgebra d ∈ Shared.Lie.PBW.Graded.symmetricDegree (k := k) (g := g) m
    rw [← hd]
    exact symmetric_basis_mem b d

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I k g)

/-- Homogeneous tensors embed in the full symmetric Koszul term. -/
theorem koszulInclusion_injective (m n : ℕ) :
    Function.Injective (koszulInclusion k g m n) :=
  TensorFiltration.map_id_injective _ (Submodule.injective_subtype _)

/-- The homogeneous tensor term has precisely its indicated total weight. -/
theorem koszulInclusion_mem_weight (m n : ℕ) (q : KoszulPiece k g m n) :
    koszulInclusion k g m n q ∈ SymmetricKoszul.weightSpace b (m+n) n := by
  induction q using TensorProduct.inductionOn with
  | tmul p z =>
    have hp := (symmetricDegree_eq_basis_span b m).le p.property
    change p.val ⊗ₜ[k] z ∈ _
    suffices ∀ p : SymmetricAlgebra k g,
        p ∈ Submodule.span k (b.symmetricAlgebra '' {d | d.degree = m}) →
        p ⊗ₜ[k] z ∈ SymmetricKoszul.weightSpace b (m+n) n from this p.val hp
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨d, hd, rfl⟩ := hp
      exact Submodule.subset_span ⟨d, z, by change d.degree = m at hd; omega, rfl⟩
    | zero => simp
    | add p q hp hq ihp ihq =>
      simpa only [TensorProduct.add_tmul] using Submodule.add_mem _ ihp ihq
    | smul r p hp ih =>
      simpa only [← TensorProduct.smul_tmul'] using Submodule.smul_mem _ r ih
  | add p q hp hq => simpa only [map_add] using Submodule.add_mem _ hp hq

/-- Any chain supported in one weight is represented in the homogeneous tensor term. -/
theorem weight_mem_koszulInclusion_range (a n : ℕ) (han : n ≤ a)
    (z : SymmetricKoszul.Term k g n) (hz : z ∈ SymmetricKoszul.weightSpace b a n) :
    z ∈ LinearMap.range (koszulInclusion k g (a-n) n) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨d, w, hd, rfl⟩ := hz
    have he : d.degree = a-n := by omega
    refine ⟨⟨b.symmetricAlgebra d, ?_⟩ ⊗ₜ[k] w, rfl⟩
    simpa only [he] using symmetric_basis_mem b d
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul r x hx ih => exact Submodule.smul_mem _ r ih

/-- There is no Koszul chain of a weight below its exterior degree. -/
theorem weightSpace_below (a n : ℕ) (han : a < n) :
    SymmetricKoszul.weightSpace b a n = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro z ⟨d, w, hd, rfl⟩
  omega

/-- The two independently constructed Koszul boundaries agree on homogeneous terms. -/
theorem koszulDifferential_inclusion (m n : ℕ) (q : KoszulPiece k g m (n+1)) :
    koszulInclusion k g (m+1) n (koszulDifferential k g m n q) =
      SymmetricKoszul.symmetricDifferential b n (koszulInclusion k g m (n+1) q) := by
  have he : (koszulInclusion k g (m+1) n).comp (koszulDifferential k g m n) =
      ((SymmetricKoszul.symmetricDifferential b n).restrictScalars k).comp
        (koszulInclusion k g m (n+1)) := by
    apply TensorProduct.ext'
    intro p z
    have hz : z ∈ Submodule.span k (Set.range (wedge k g (n+1))) := by
      rw [exteriorPower.ιMulti_span]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      change koszulInclusion k g (m+1) n
        (koszulDifferential k g m n (p ⊗ₜ[k] wedge k g (n+1) x)) =
          SymmetricKoszul.symmetricDifferential b n (p.val ⊗ₜ[k] wedge k g (n+1) x)
      rw [koszulDifferential_formula, SymmetricKoszul.symmetricDifferential_formula]
      unfold koszulSum
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Int.cast_smul_eq_zsmul k, Int.cast_pow, Int.cast_neg, Int.cast_one]
      rfl
    | zero => simp
    | add z w hz hw ihz ihw => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) ihz ihw
    | smul r z hz ih => simpa only [TensorProduct.tmul_smul, map_smul] using congrArg (r • ·) ih
  exact DFunLike.congr_fun he q

/-- Both symmetric augmentations are evaluation at zero on the same tensor term. -/
theorem koszulAugmentation_eq : koszulAugmentation k g = SymmetricKoszul.augmentation k g := by
  apply TensorProduct.ext'
  intro p z
  simp [koszulAugmentation, SymmetricKoszul.augmentation, SymmetricKoszul.zeroTermEquiv, mul_comm]

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I k g)

include b

/-- In the lowest possible positive-degree weight, a Koszul cycle is zero. -/
theorem homogeneous_cycle_zero (n : ℕ) (q : KoszulPiece k g 0 (n+1))
    (hq : koszulDifferential k g 0 n q = 0) : q = 0 := by
  have hc : SymmetricKoszul.symmetricDifferential b n (koszulInclusion k g 0 (n+1) q) = 0 := by
    rw [← koszulDifferential_inclusion b, hq, map_zero]
  obtain ⟨y, hyw, hy⟩ := SymmetricKoszul.symmetric_weight_cycle_lift b (0+(n+1)) n
    (koszulInclusion k g 0 (n+1) q) (koszulInclusion_mem_weight b _ _ q) hc
  rw [weightSpace_below b _ _ (by omega), Submodule.mem_bot] at hyw
  apply koszulInclusion_injective 0 (n+1)
  simpa only [hyw, map_zero] using hy.symm

/-- A homogeneous cycle lifts in the same total weight. -/
theorem homogeneous_cycle_lift (m n : ℕ) (q : KoszulPiece k g (m+1) (n+1))
    (hq : koszulDifferential k g (m+1) n q = 0) :
    ∃ y : KoszulPiece k g m (n+2), koszulDifferential k g m (n+1) y = q := by
  have hc : SymmetricKoszul.symmetricDifferential b n (koszulInclusion k g (m+1) (n+1) q) = 0 := by
    rw [← koszulDifferential_inclusion b, hq, map_zero]
  obtain ⟨y, hyw, hy⟩ := SymmetricKoszul.symmetric_weight_cycle_lift b ((m+1)+(n+1)) n
    (koszulInclusion k g (m+1) (n+1) q) (koszulInclusion_mem_weight b _ _ q) hc
  have hr := weight_mem_koszulInclusion_range b ((m+1)+(n+1)) (n+2) (by omega) y hyw
  have hidx : (m+1+(n+1))-(n+2) = m := by omega
  rw [hidx] at hr
  obtain ⟨y', hy'⟩ := hr
  refine ⟨y', ?_⟩
  apply koszulInclusion_injective (m+1) (n+1)
  rw [koszulDifferential_inclusion b, hy', hy]

/-- The weight-zero augmented Koszul kernel is zero. -/
theorem homogeneous_augmented_zero (q : KoszulPiece k g 0 0)
    (hq : koszulAugmentation k g (koszulInclusion k g 0 0 q) = 0) : q = 0 := by
  rw [koszulAugmentation_eq] at hq
  obtain ⟨y, hyw, hy⟩ := SymmetricKoszul.symmetric_weight_augmented_lift b 0
    (koszulInclusion k g 0 0 q) (koszulInclusion_mem_weight b 0 0 q) hq
  rw [weightSpace_below b 0 1 (by omega), Submodule.mem_bot] at hyw
  apply koszulInclusion_injective 0 0
  simpa only [hyw, map_zero] using hy.symm

/-- Augmented degree-zero cycles also lift in the same total weight. -/
theorem homogeneous_augmented_lift (m : ℕ) (q : KoszulPiece k g (m+1) 0)
    (hq : koszulAugmentation k g (koszulInclusion k g (m+1) 0 q) = 0) :
    ∃ y : KoszulPiece k g m 1, koszulDifferential k g m 0 y = q := by
  rw [koszulAugmentation_eq] at hq
  obtain ⟨y, hyw, hy⟩ := SymmetricKoszul.symmetric_weight_augmented_lift b ((m+1)+0)
    (koszulInclusion k g (m+1) 0 q) (koszulInclusion_mem_weight b (m+1) 0 q) hq
  have hr := weight_mem_koszulInclusion_range b (m+1+0) 1 (by omega) y hyw
  have hidx : m+1+0-1 = m := by omega
  rw [hidx] at hr
  obtain ⟨y', hy'⟩ := hr
  refine ⟨y', ?_⟩
  apply koszulInclusion_injective (m+1) 0
  rw [koszulDifferential_inclusion b, hy', hy]

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I k g)
include b

/-- Removing a homogeneous boundary lowers the filtration of a positive-degree cycle. -/
theorem cycle_lower (m n : ℕ) (z : Step k g ((m : ℤ)+(n+1 : ℕ)) (n+1))
    (hz : boundary k g n z.val = 0) :
    ∃ y : V k g (n+2), z.val - boundary k g (n+1) y ∈
      weight k g ((m : ℤ)+(n+1 : ℕ)-1) (n+1) := by
  let q := (koszulComparison k g m (n+1)).symm
    (principal k g ((m : ℤ)+(n+1 : ℕ)) (n+1) z)
  have hmem : boundary k g n z.val ∈ weight k g ((m+1 : ℕ)+n) n := by
    rw [hz]
    exact Submodule.zero_mem _
  have hq : koszulDifferential k g m n q = 0 := by
    apply (koszulComparison k g (m+1) n).injective
    rw [map_zero]
    change koszulComparison k g (m+1) n (koszulDifferential k g m n
      ((koszulComparison k g m (n+1)).symm (principal k g _ _ z))) = 0
    rw [koszulDifferential_principal k g m n z hmem]
    apply (Submodule.Quotient.mk_eq_zero (lower k g ((m+1 : ℕ)+n) n)).mpr
    change boundary k g n z.val ∈ weight k g (((m+1 : ℕ)+n)-1) n
    rw [hz]
    exact Submodule.zero_mem _
  cases m with
  | zero =>
    have hq0 := homogeneous_cycle_zero b n q hq
    have hp : principal k g ((0 : ℕ)+(n+1 : ℕ)) (n+1) z = 0 := by
      exact (LinearEquiv.apply_symm_apply (koszulComparison k g 0 (n+1)) _).symm.trans
        ((congrArg (koszulComparison k g 0 (n+1)) hq0).trans (map_zero _))
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact (Submodule.Quotient.mk_eq_zero (lower k g ((0 : ℕ)+(n+1 : ℕ)) (n+1))).mp hp
  | succ m =>
    obtain ⟨p, hp⟩ := homogeneous_cycle_lift b m n q hq
    obtain ⟨y, hy⟩ := (Submodule.mkQ_surjective (lower k g ((m : ℤ)+(n+2 : ℕ)) (n+2)))
      (koszulComparison k g m (n+2) p)
    have hyb : boundary k g (n+1) y.val ∈ weight k g ((m+1 : ℕ)+(n+1 : ℕ)) (n+1) := by
      have he : ((m+1 : ℕ) : ℤ)+(n+1 : ℕ) = (m : ℤ)+(n+2 : ℕ) := by omega
      rw [he]
      exact boundary_preserves k g _ _ y.val y.property
    have hyq : (koszulComparison k g m (n+2)).symm
        (principal k g ((m : ℤ)+(n+2 : ℕ)) (n+2) y) = p := by
      exact (koszulComparison k g m (n+2)).symm_apply_eq.mpr hy
    have hs := koszulDifferential_principal k g m (n+1) y hyb
    rw [hyq, hp] at hs
    change koszulComparison k g (m+1) (n+1) q = _ at hs
    have heq : principal k g ((m+1 : ℕ)+(n+1 : ℕ)) (n+1) z =
        principal k g ((m+1 : ℕ)+(n+1 : ℕ)) (n+1) ⟨boundary k g (n+1) y.val, hyb⟩ :=
      (LinearEquiv.apply_symm_apply (koszulComparison k g (m+1) (n+1)) _).symm.trans hs
    refine ⟨y.val, ?_⟩
    have hr := (Submodule.Quotient.eq _).mp heq
    exact hr

/-- Finite filtration descent proves exactness in every positive chain degree. -/
theorem cycle_lift_weight (a n : ℕ) (z : V k g (n+1))
    (hzw : z ∈ weight k g a (n+1)) (hz : boundary k g n z = 0) :
    ∃ y, boundary k g (n+1) y = z := by
  induction a using Nat.strong_induction_on generalizing z with
  | h a ih =>
    by_cases ha : a < n+1
    · rw [weight_below k g a (n+1) (by exact_mod_cast ha), Submodule.mem_bot] at hzw
      exact ⟨0, by simp [hzw]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, a = m+(n+1) := ⟨a-(n+1), by omega⟩
      have hzw' : z ∈ weight k g ((m : ℤ)+(n+1 : ℕ)) (n+1) := by simpa [hm] using hzw
      obtain ⟨y, hy⟩ := cycle_lower b m n ⟨z, hzw'⟩ hz
      have ha0 : 0 < a := by omega
      have hrw : z - boundary k g (n+1) y ∈ weight k g (a-1 : ℕ) (n+1) := by
        have he : ((a-1 : ℕ) : ℤ) = (m : ℤ)+(n+1 : ℕ)-1 := by omega
        rw [he]
        exact hy
      have hrc : boundary k g n (z - boundary k g (n+1) y) = 0 := by
        rw [map_sub, hz]
        have hs := DFunLike.congr_fun (boundary_squared k g n) y
        change boundary k g n (boundary k g (n+1) y) = 0 at hs
        rw [hs, sub_self]
      obtain ⟨y', hy'⟩ := ih (a-1) (by omega) _ hrw hrc
      refine ⟨y'+y, ?_⟩
      rw [map_add, hy', sub_add_cancel]

/-- Exhaustivity reduces every CE cycle to the finite descent theorem. -/
theorem cycle_lift (n : ℕ) (z : V k g (n+1)) (hz : boundary k g n z = 0) :
    ∃ y, boundary k g (n+1) y = z := by
  obtain ⟨a, ha⟩ := weight_exhaustive k g (n+1) z
  exact cycle_lift_weight b (max a 0).toNat n z
    (weight_mono k g (n+1) (by omega) ha) hz

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Graded
open scoped TensorProduct
universe u v w
variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g] [Fact (Specs.Shared.Lie.filtrationType k g)]
variable {I : Type w} [LinearOrder I] (b : Module.Basis I k g)
include b

/-- The same filtration reduction at the augmented degree-zero term. -/
theorem augmented_lower (m : ℕ) (z : Step k g ((m : ℤ)+0) 0)
    (hz : augmentation k g z.val = 0) :
    ∃ y : V k g 1, z.val - boundary k g 0 y ∈ weight k g ((m : ℤ)+0-1) 0 := by
  let q := (koszulComparison k g m 0).symm (principal k g ((m : ℤ)+0) 0 z)
  have hq : koszulAugmentation k g (koszulInclusion k g m 0 q) = 0 := by
    have h := koszulAugmentation_principal k g m z
    change koszulAugmentation k g (koszulInclusion k g m 0 q) = _ at h
    simpa only [hz, ite_self] using h
  cases m with
  | zero =>
    have hq0 := homogeneous_augmented_zero b q hq
    have hp : principal k g ((0 : ℕ)+0) 0 z = 0 := by
      exact (LinearEquiv.apply_symm_apply (koszulComparison k g 0 0) _).symm.trans
        ((congrArg (koszulComparison k g 0 0) hq0).trans (map_zero _))
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero]
    exact (Submodule.Quotient.mk_eq_zero (lower k g ((0 : ℕ)+0) 0)).mp hp
  | succ m =>
    obtain ⟨p, hp⟩ := homogeneous_augmented_lift b m q hq
    obtain ⟨y, hy⟩ := (Submodule.mkQ_surjective (lower k g ((m : ℤ)+1) 1))
      (koszulComparison k g m 1 p)
    have hyb : boundary k g 0 y.val ∈ weight k g ((m+1 : ℕ)+0) 0 := by
      have he : ((m+1 : ℕ) : ℤ)+0 = (m : ℤ)+1 := by omega
      rw [he]
      exact boundary_preserves k g _ _ y.val y.property
    have hyq : (koszulComparison k g m 1).symm
        (principal k g ((m : ℤ)+1) 1 y) = p := by
      exact (koszulComparison k g m 1).symm_apply_eq.mpr hy
    have hs := koszulDifferential_principal k g m 0 y hyb
    change koszulComparison k g (m+1) 0 (koszulDifferential k g m 0
      ((koszulComparison k g m 1).symm (principal k g ((m : ℤ)+1) 1 y))) = _ at hs
    rw [hyq, hp] at hs
    change koszulComparison k g (m+1) 0 q = _ at hs
    have heq : principal k g ((m+1 : ℕ)+0) 0 z =
        principal k g ((m+1 : ℕ)+0) 0 ⟨boundary k g 0 y.val, hyb⟩ :=
      (LinearEquiv.apply_symm_apply (koszulComparison k g (m+1) 0) _).symm.trans hs
    refine ⟨y.val, ?_⟩
    exact (Submodule.Quotient.eq (lower k g ((m+1 : ℕ)+0) 0)).mp heq

/-- Augmented exactness follows by induction down to the zero filtration step. -/
theorem augmented_lift_weight (a : ℕ) (z : V k g 0)
    (hzw : z ∈ weight k g a 0) (hz : augmentation k g z = 0) :
    ∃ y, boundary k g 0 y = z := by
  induction a using Nat.strong_induction_on generalizing z with
  | h a ih =>
    obtain ⟨y, hy⟩ := augmented_lower b a ⟨z, by simpa only [add_zero] using hzw⟩ hz
    by_cases ha : a = 0
    · subst a
      rw [weight_below k g _ 0 (by norm_num), Submodule.mem_bot] at hy
      exact ⟨y, (sub_eq_zero.mp hy).symm⟩
    · have hrw : z - boundary k g 0 y ∈ weight k g (a-1 : ℕ) 0 := by
        have he : ((a-1 : ℕ) : ℤ) = (a : ℤ)+0-1 := by omega
        rw [he]
        exact hy
      have hrc : augmentation k g (z - boundary k g 0 y) = 0 := by
        rw [map_sub, hz, augmentation_boundary k g (boundary k g) (boundary_formula k g) y, sub_self]
      obtain ⟨y', hy'⟩ := ih (a-1) (by omega) _ hrw hrc
      exact ⟨y'+y, by rw [map_add, hy', sub_add_cancel]⟩

/-- Every degree-zero augmented cycle is a boundary. -/
theorem augmented_lift (z : V k g 0) (hz : augmentation k g z = 0) :
    ∃ y, boundary k g 0 y = z := by
  obtain ⟨a, ha⟩ := weight_exhaustive k g 0 z
  exact augmented_lift_weight b (max a 0).toNat z
    (weight_mono k g 0 (by omega) ha) hz

end AdvancedHomologicalAlgebra.CE.Graded

namespace AdvancedHomologicalAlgebra.CE.Ext
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

/-- Exactness of the original CE boundary, derived from the Koszul theorem. -/
theorem boundary_exact : AugmentedExact k g (boundary k g) := by
  classical
  letI : Fact (Specs.Shared.Lie.filtrationType k g) := ⟨Shared.Lie.filtration_properties k g⟩
  let I := Module.Free.ChooseBasisIndex k g
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b : Module.Basis I k g := Module.Free.chooseBasis k g
  refine ⟨augmentation_surjective k g, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact augmentation_boundary k g _ (boundary_formula k g) y
    · intro hz
      exact Graded.augmented_lift b z hz
  · intro n
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact DFunLike.congr_fun (boundary_squared k g n) y
    · intro hz
      exact Graded.cycle_lift b n z hz

/-- Every formula-checked CE boundary gives the exact free complex. -/
theorem free_resolution : Specs.AdvancedHomologicalAlgebra.CE.Ext.freeResolutionExpected.{u, v} := by
  intro k g _ _ _ _ D
  have hd := boundaryFormula_unique k g D.formula (boundary_formula k g)
  exact ⟨hd.symm ▸ boundary_exact k g, term_free k g⟩

end AdvancedHomologicalAlgebra.CE.Ext

namespace AdvancedHomologicalAlgebra.CE.Ext
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]
variable (d : BoundaryFamily k g) (hc : IsAugmentedComplex k g d)

/-- The given evaluation identifies the ordinary resolution Hom complex
with its exterior Chevalley–Eilenberg cochains. -/
def evaluationIso (C : CochainData k g M d) : homComplex (chain k g d hc) M ≅
    cochain k g M C.differential C.squared :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (C.evaluation n).toAddEquiv.toIntLinearEquiv.toModuleIso)
    (by
      intro i j hij
      change i + 1 = j at hij
      subst j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro F
      simp only [cochain, CochainComplex.of_d, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply]
      change C.differential i (C.evaluation i F) =
        C.evaluation (i + 1) (((homComplex (chain k g d hc) M).d i (i + 1)).hom F)
      rw [P103.Ch11.ExtTorDefinitions.hom_differential, C.compatible]
      simp only [chain, ChainComplex.of_d, ModuleCat.hom_ofHom, homCoboundary])

/-- The cohomology comparison is induced by inverse evaluation. -/
def evaluationCohomology (C : CochainData k g M d) (he : AugmentedExact k g d) (n : ℕ) :
    Homology (cochain k g M C.differential C.squared) n ≃+
      @ExtWith _ _ _ _ (trivialModule k g) (resolution k g d hc he) M _ _ n :=
  ((quotientHomology (ComplexShape.up ℕ) n).mapIso
    (evaluationIso k g M d hc C).symm).toLinearEquiv.toAddEquiv

end AdvancedHomologicalAlgebra.CE.Ext

namespace AdvancedHomologicalAlgebra.CE.Ext
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

theorem cohomology.{a, b, c} :
    Specs.AdvancedHomologicalAlgebra.CE.Ext.cohomologyExpected.{a, b, c} := by
  intro k g _ _ _ _ D he M _ _ _ _ C
  refine ⟨evaluationIso k g M D.differential D.augmented C, fun _ _ => rfl, ?_⟩
  intro n
  exact ⟨evaluationCohomology k g M D.differential D.augmented C he n, fun _ => rfl⟩

theorem naturality.{a, b, c} :
    Specs.AdvancedHomologicalAlgebra.CE.Ext.naturalityExpected.{a, b, c} := by
  intro k g _ _ _ d hc M _ _ _ _ N _ _ _ _ δM sM δN sN eM eN hM hN h
  let f := eM.inv ≫ homPostMap (chain k g d hc) h ≫ eN.hom
  refine ⟨f, ?_, ?_⟩
  · intro n z
    apply LinearMap.ext
    intro x
    change (eN.hom.f n).hom (h.comp ((eM.inv.f n).hom z)) x = h (z x)
    rw [hN]
    have hi := congrArg (fun a => (a.f n).hom) eM.inv_hom_id
    have hz := LinearMap.congr_fun hi z
    have hx := LinearMap.congr_fun hz x
    change ((eM.hom.f n).hom ((eM.inv.f n).hom z)) x = z x at hx
    rw [hM] at hx
    exact congrArg h hx
  · intro n
    have hf : f ≫ eN.inv = eM.inv ≫ homPostMap (chain k g d hc) h := by simp [f]
    have he := congrArg (fun a => ((quotientHomology (ComplexShape.up ℕ) n).map a).hom) hf
    simpa only [Functor.map_comp, ModuleCat.hom_comp, quotientHomology, ModuleCat.hom_ofHom] using he

end AdvancedHomologicalAlgebra.CE.Ext

namespace AdvancedHomologicalAlgebra.CE.Ext
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
universe r a m
variable {R : Type r} [Ring R] {A : Type a} [AddCommGroup A] [Module R A]
  (P Q : LeftResolution R A) (hP : P.IsProjective) (hQ : Q.IsProjective)
  (M : Type m) [AddCommGroup M] [Module R M]

/-- P103's coherent comparison identifies the computations using any two
ordinary projective resolutions, with no coefficient injectivity assumption. -/
def resolutionExtEquiv (n : ℕ) : ExtWith P M n ≃+ ExtWith Q M n :=
  let C := (P103.Ch11.ExtTorDefinitions.ext_coherent.{r,a,m} R M n).some
  ((C.comparison (A := ModuleCat.of R A) ⟨Q, hQ⟩ ⟨P, hP⟩).unop).toLinearEquiv.toAddEquiv

/-- The resolution comparison agrees with precomposition by every actual
augmented lift, so it is independent of the choice of such a lift. -/
theorem resolutionExtEquiv_apply (n : ℕ) (f : Q.complex ⟶ P.complex)
    (hf : ChainLift Q P LinearMap.id f) (x : ExtWith P M n) :
    resolutionExtEquiv P Q hP hQ M n x = homologyMap (homPreMap f M) n x := by
  let C := (P103.Ch11.ExtTorDefinitions.ext_coherent.{r,a,m} R M n).some
  change (C.comparison (A := ModuleCat.of R A) ⟨Q, hQ⟩ ⟨P, hP⟩).hom.unop.hom x = _
  rw [C.comparison_hom, C.map_eq ⟨Q, hQ⟩ ⟨P, hP⟩ (𝟙 (ModuleCat.of R A)) f hf]
  rfl

end AdvancedHomologicalAlgebra.CE.Ext

namespace AdvancedHomologicalAlgebra.CE.Ext
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

theorem resolution_comparison.{a, b, c} :
    Specs.AdvancedHomologicalAlgebra.CE.Ext.resolutionComparisonExpected.{a, b, c} := by
  intro k g _ _ _ _ d hd hc he M _ _ _ _ δ s e heval
  letI := trivialModule k g
  intro Q hQ n
  let P := resolution k g d hc he
  have hP : P.IsProjective := by
    intro i
    change Module.Projective (U k g) (V k g i)
    haveI := term_free k g i
    infer_instance
  let E := ((quotientHomology (ComplexShape.up ℕ) n).mapIso e.symm).toLinearEquiv.toAddEquiv
  refine ⟨E.trans (resolutionExtEquiv P Q hP hQ M n), ?_⟩
  intro f hf z
  change resolutionExtEquiv P Q hP hQ M n
    (homologyMap e.inv n (homologyClass _ n z)) = _
  rw [resolutionExtEquiv_apply P Q hP hQ M n f hf]
  rfl

end AdvancedHomologicalAlgebra.CE.Ext


namespace AdvancedHomologicalAlgebra.CE.Ext
open CategoryTheory
open P103.Specs.Ch10.Complexes P103.Specs.Ch11.ExtTorDefinitions

universe s t
section Quotients

variable {R : Type*} [Ring R]
  {K : CochainComplex (ModuleCat.{s} R) ℕ}
  {L : CochainComplex (ModuleCat.{t} R) ℕ}
  (f : ∀ n, K.X n →ₗ[R] L.X n)
  (comm : ∀ i j, (L.d i j).hom.comp (f i) = (f j).comp (K.d i j).hom)

/-- A cochain map on terms in independent universes restricts to cycles. -/
private def pointwiseCyclesMap (n : ℕ) : cycles K n →ₗ[R] cycles L n :=
  ((f n).comp (cycles K n).subtype).codRestrict (cycles L n) (by
    intro z
    change (L.d n ((ComplexShape.up ℕ).next n)).hom (f n z.val) = 0
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply]
    have hz : (K.d n ((ComplexShape.up ℕ).next n)).hom z.val = 0 := z.property
    rw [hz, map_zero])

/-- The pointwise map sends boundaries to boundaries, so it descends to the
quotients of the original cycle groups. -/
private def pointwiseHomologyMap (n : ℕ) : Homology K n →ₗ[R] Homology L n :=
  (cycleBoundaries K n).mapQ (cycleBoundaries L n) (pointwiseCyclesMap f comm n) (by
    intro z hz
    obtain ⟨x, hx⟩ := hz
    let p := (ComplexShape.up ℕ).prev n
    change (K.d p n).hom x = z.val at hx
    change ∃ y, (L.d p n).hom y = f n z.val
    refine ⟨f p x, ?_⟩
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply, hx])

end Quotients

private theorem pointwiseHomologyMap_induces
    {K : CochainComplex (ModuleCat.{s} ℤ) ℕ}
    {L : CochainComplex (ModuleCat.{t} ℤ) ℕ}
    (f : ∀ n, K.X n →ₗ[ℤ] L.X n)
    (comm : ∀ i j, (L.d i j).hom.comp (f i) = (f j).comp (K.d i j).hom) :
    InducesCohomologyMap f
      (fun n => (pointwiseHomologyMap (R := ℤ) f comm n).toAddMonoidHom.toIntLinearMap) :=
  ⟨comm, fun n z => ⟨pointwiseCyclesMap (R := ℤ) f comm n z, rfl, rfl⟩⟩

private theorem component_comm {K L : CochainComplex (ModuleCat.{s} ℤ) ℕ}
    (f : K ⟶ L) (i j : ℕ) (z : K.X i) :
    (L.d i j).hom ((f.f i).hom z) = (f.f j).hom ((K.d i j).hom z) :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.comm i j)) z

private theorem inverse_component_apply {K L : CochainComplex (ModuleCat.{s} ℤ) ℕ}
    (e : K ≅ L) (n : ℕ) (z : K.X n) :
    (e.inv.f n).hom ((e.hom.f n).hom z) = z :=
  LinearMap.congr_fun (congrArg (fun a => (a.f n).hom) e.hom_inv_id) z

open scoped TensorProduct

/-- Evaluation commutes with coefficient maps on the original cycle quotients,
including across distinct carrier universes. -/
theorem heterogeneous_naturality :
    Specs.AdvancedHomologicalAlgebra.CE.Ext.heterogeneousNaturalityExpected := by
  intro k g _ _ _ D M _ _ _ _ N _ _ _ _ CM CN
  dsimp only
  intro eM eN hM hN h
  let P := chain k g D.differential D.augmented
  let K := cochain k g M CM.differential CM.squared
  let L := cochain k g N CN.differential CN.squared
  let b : ∀ n, (homComplex P M).X n →ₗ[ℤ] (homComplex P N).X n :=
    fun _ => (P103.HomTensorExactness.post h).toIntLinearMap
  let a : ∀ n, K.X n →ₗ[ℤ] L.X n :=
    fun n => (eN.hom.f n).hom.comp ((b n).comp (eM.inv.f n).hom)
  have b_comm i j : ((homComplex P N).d i j).hom.comp (b i) =
      (b j).comp ((homComplex P M).d i j).hom := by
    by_cases hij : (ComplexShape.up ℕ).Rel i j
    · change i + 1 = j at hij
      subst j
      apply LinearMap.ext
      intro F
      rfl
    · rw [(homComplex P N).shape i j hij, (homComplex P M).shape i j hij]
      simp
  have a_comm i j : (L.d i j).hom.comp (a i) = (a j).comp (K.d i j).hom := by
    apply LinearMap.ext
    intro z
    change (L.d i j).hom ((eN.hom.f i).hom (b i ((eM.inv.f i).hom z))) =
      (eN.hom.f j).hom (b j ((eM.inv.f j).hom ((K.d i j).hom z)))
    rw [component_comm eN.hom i j, ← component_comm eM.inv i j]
    exact congrArg (eN.hom.f j).hom (LinearMap.congr_fun (b_comm i j) _)
  have ha : a = fun n => (P103.HomTensorExactness.post
      (P := W k g n) (h.restrictScalars k)).toIntLinearMap := by
    funext n
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro x
    change (eN.hom.f n).hom (h.comp ((eM.inv.f n).hom z)) x = h (z x)
    rw [hN, CN.evaluate_tmul]
    have hx := LinearMap.congr_fun (inverse_component_apply eM.symm n z) x
    change ((eM.hom.f n).hom ((eM.inv.f n).hom z)) x = z x at hx
    rw [hM, CM.evaluate_tmul] at hx
    exact congrArg h hx
  refine ⟨fun n => (pointwiseHomologyMap a a_comm n).toAddMonoidHom.toIntLinearMap,
    fun n => (pointwiseHomologyMap b b_comm n).toAddMonoidHom.toIntLinearMap, ?_,
    pointwiseHomologyMap_induces b b_comm, ?_⟩
  · rw [← ha]
    exact pointwiseHomologyMap_induces a a_comm
  · intro n
    apply (cycleBoundaries K n).quot_hom_ext
    intro z
    change homologyClass _ n (cyclesMap eN.inv n (pointwiseCyclesMap a a_comm n z)) =
      homologyClass _ n (pointwiseCyclesMap b b_comm n (cyclesMap eM.inv n z))
    congr 1
    apply Subtype.ext
    exact inverse_component_apply eN n (b n ((eM.inv.f n).hom z.val))

end AdvancedHomologicalAlgebra.CE.Ext
