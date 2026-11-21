import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.DimensionBounds
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.ExactSequence
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.Syzygies

/-! CM-12a: the maximal Cohen–Macaulay syzygy bound.
The depth lemma works equally for zero terms (whose depth is infinity).
-/
universe u
open CategoryTheory
namespace AdvCommAlg.CohenMacaulay
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- Once a syzygy is zero, extend the chain by zero free modules. The same
zero module is used as representative for each subsequent zero kernel. -/
theorem FiniteFreeSyzygy.zero_tail {M N : ModuleCat.{u} R}
    [Module.Finite R N] [Subsingleton N] {n : ℕ}
    (h : FiniteFreeSyzygy R M n N) (k : ℕ) : FiniteFreeSyzygy R M (n + k) N := by
  have hw : (𝟙 N) ≫ (𝟙 N) = 0 := by ext x; exact Subsingleton.elim _ _
  have hS : (ShortComplex.mk (𝟙 N) (𝟙 N) hw).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton N) }
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simpa only [Nat.add_assoc] using FiniteFreeSyzygy.succ ih (𝟙 N) (𝟙 N) hw hS

/-- Flat base change carries ring-regular lists to weakly regular lists on a
free module; Nakayama makes these proper when the module is nonzero. -/
lemma depth_self_le_depth_free (F : ModuleCat.{u} R)
    [Module.Finite R F] [Module.Free R F] : Depth.depth R R ≤ Depth.depth R F := by
  cases subsingleton_or_nontrivial F with
  | inl h =>
    let := h
    rw [Depth.depth_eq_top_of_subsingleton R F]
    exact le_top
  | inr h =>
    let := h
    rw [Depth.depth_eq_libraryDepth (ModuleCat.of R R), Depth.depth_eq_libraryDepth F,
      IsLocalRing.depth_eq_sSup_length_isRegular, IsLocalRing.depth_eq_sSup_length_isRegular]
    apply sSup_le
    rintro _ ⟨xs, hxs, hmem, rfl⟩
    apply le_sSup
    refine ⟨xs, ?_, hmem, rfl⟩
    apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
    exact ((TensorProduct.lid R F).isWeaklyRegular_congr xs).mp
      hxs.toIsWeaklyRegular.isWeaklyRegular_rTensor

lemma depth_self_eq_dimension (d : ℕ) (hCM : LocalCohenMacaulay R R)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) : Depth.depth R R = (d : ℕ∞) := by
  have h := (localCohenMacaulay_self_iff R).mp hCM
  rw [hd, ← Depth.depth_eq_libraryDepth (ModuleCat.of R R)] at h
  exact WithBot.coe_injective h

/-- The depth estimate for a finite chain, without extending the resolution. -/
theorem finiteFreeSyzygy_depth_lower_bound (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (d e n : ℕ)
    (hCM : LocalCohenMacaulay R R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (he : Depth.depth R M = (e : ℕ∞)) (h : FiniteFreeSyzygy R M n N) :
    ((min d (e + n) : ℕ) : ℕ∞) ≤ Depth.depth R N := by
  induction h with
  | zero =>
    rw [he, Nat.add_zero]
    exact_mod_cast min_le_right d e
  | @succ n N F K _ _ _ _ hprev i p w hS ih =>
    have hF : (d : ℕ∞) ≤ Depth.depth R F := by
      rw [← depth_self_eq_dimension d hCM hd]
      exact depth_self_le_depth_free F
    have hstep := Depth.depth_min_add_one_le_left _ hS
    change min (Depth.depth R F) (Depth.depth R N + 1) ≤ Depth.depth R K at hstep
    apply le_trans ?_ hstep
    apply le_min
    · have hl : ((min d (e + (n + 1)) : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
        exact_mod_cast min_le_left d (e + (n + 1))
      exact hl.trans hF
    · apply le_trans ?_ (add_le_add ih (le_refl (1 : ℕ∞)))
      have hn : min d (e + (n + 1)) ≤ min d (e + n) + 1 := by omega
      exact_mod_cast hn

/-- The bound for a finite chain of free surjections. In particular no infinite
resolution, projective dimension assumption, or nonzero kernel is required. -/
theorem finiteFreeSyzygy_bound (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] (d e : ℕ)
    (hCM : LocalCohenMacaulay R R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (he : Depth.depth R M = (e : ℕ∞)) (h : FiniteFreeSyzygy R M (d - e) N) :
    e ≤ d ∧ e + (d - e) = d ∧ MaximalCohenMacaulay R N := by
  have hle := (Depth.depth_le_supportDim M).trans
    (Module.supportDim_le_ringKrullDim R M)
  rw [he, hd] at hle
  have hed : e ≤ d := by exact_mod_cast hle
  have hsum : e + (d - e) = d := by omega
  refine ⟨hed, hsum, ?_⟩
  cases subsingleton_or_nontrivial N with
  | inl hz => exact Or.inl hz
  | inr hn =>
    let := hn
    apply (maximalCohenMacaulay_iff_sourceDepth R N).mpr
    rw [hd]
    have hlo := finiteFreeSyzygy_depth_lower_bound M N d e (d - e) hCM hd he h
    rw [hsum, min_self] at hlo
    have hhi := (Depth.depth_le_supportDim N).trans
      (Module.supportDim_le_ringKrullDim R N)
    rw [hd] at hhi
    exact le_antisymm hhi (WithBot.coe_le_coe.mpr hlo)

/-- At every stage, depth has increased by at least one until it reaches `d`.
No nonzero hypothesis is imposed on the intermediate kernels or free terms. -/
theorem syzygy_depth_lower_bound (T : FiniteFreeSyzygies R) (d e : ℕ)
    (hCM : LocalCohenMacaulay R R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (he : Depth.depth R (T.K 0) = (e : ℕ∞)) (n : ℕ) :
    ((min d (e + n) : ℕ) : ℕ∞) ≤ Depth.depth R (T.K n) := by
  induction n with
  | zero =>
    rw [he, Nat.add_zero]
    exact_mod_cast min_le_right d e
  | succ n ih =>
    have hF : (d : ℕ∞) ≤ Depth.depth R (T.F n) := by
      rw [← depth_self_eq_dimension d hCM hd]
      exact depth_self_le_depth_free (T.F n)
    have hstep := Depth.depth_min_add_one_le_left _ (T.shortExact n)
    change min (Depth.depth R (T.F n)) (Depth.depth R (T.K n) + 1) ≤
      Depth.depth R (T.K (n + 1)) at hstep
    apply le_trans ?_ hstep
    apply le_min
    · have hl : ((min d (e + (n + 1)) : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
        exact_mod_cast min_le_left d (e + (n + 1))
      exact hl.trans hF
    · apply le_trans ?_ (add_le_add ih (le_refl (1 : ℕ∞)))
      have hn : min d (e + (n + 1)) ≤ min d (e + n) + 1 := by omega
      exact_mod_cast hn

/-- Any syzygy at or beyond the dimension-minus-depth bound is MCM or zero. -/
theorem syzygy_maximalCohenMacaulay (T : FiniteFreeSyzygies R) (d e n : ℕ)
    (hCM : LocalCohenMacaulay R R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (he : Depth.depth R (T.K 0) = (e : ℕ∞)) (hn : d ≤ e + n) :
    MaximalCohenMacaulay R (T.K n) := by
  cases subsingleton_or_nontrivial (T.K n) with
  | inl h => exact Or.inl h
  | inr h =>
    let := h
    apply (maximalCohenMacaulay_iff_sourceDepth R (T.K n)).mpr
    rw [hd]
    have hlo := syzygy_depth_lower_bound T d e hCM hd he n
    rw [min_eq_left hn] at hlo
    have hhi := (Depth.depth_le_supportDim (T.K n)).trans
      (Module.supportDim_le_ringKrullDim R (T.K n))
    rw [hd] at hhi
    exact le_antisymm hhi (WithBot.coe_le_coe.mpr hlo)

/-- Source CM-12a, including the depth bound needed for ordinary subtraction.
The zeroth syzygy and zero syzygies are included. -/
theorem syzygy_bound (T : FiniteFreeSyzygies R) [Nontrivial (T.K 0)] (d e : ℕ)
    (hCM : LocalCohenMacaulay R R) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (he : Depth.depth R (T.K 0) = (e : ℕ∞)) :
    e ≤ d ∧ e + (d - e) = d ∧ MaximalCohenMacaulay R (T.K (d - e)) := by
  have hle := (Depth.depth_le_supportDim (T.K 0)).trans
    (Module.supportDim_le_ringKrullDim R (T.K 0))
  rw [he, hd] at hle
  have hed : e ≤ d := by exact_mod_cast hle
  have hsum : e + (d - e) = d := by omega
  exact ⟨hed, hsum, syzygy_maximalCohenMacaulay T d e (d - e) hCM hd he (by omega)⟩

end AdvCommAlg.CohenMacaulay
