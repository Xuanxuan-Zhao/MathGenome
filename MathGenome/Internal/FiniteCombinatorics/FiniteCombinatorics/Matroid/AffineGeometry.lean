import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.VectorRepresentation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.AffineGeometry
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.ParallelClasses

namespace FiniteCombinatorics.Matroid
open Set Submodule
universe u

def affineColumn (K : Type u) [Field K] (d : ℕ) (x : Fin d → K) :
    K × (Fin d → K) := (1, x)

def affineMatroid (K : Type u) [Field K] [Fintype K] (d : ℕ) :
    _root_.Matroid (Fin d → K) :=
  vectorMatroid K univ finite_univ (affineColumn K d)

instance (K : Type u) [Field K] [Fintype K] (d : ℕ) :
    (affineMatroid K d).Finite := by unfold affineMatroid; infer_instance

def affineLine {K : Type u} [Field K] {d : ℕ} (x a : Fin d → K) : Set (Fin d → K) :=
  range (fun t : K => x + t • a)

theorem affineGround : Expected.affineGround := by
  intro K _ _ d
  rfl

theorem affineFinite : Expected.affineFinite := by
  intro K _ _ d
  infer_instance

theorem affineIndep : Expected.affineIndep := by
  intro K _ _ d I
  exact and_iff_right (subset_univ I)

private theorem affineColumn_ne_zero {K : Type u} [Field K] {d : ℕ} (x : Fin d → K) :
    affineColumn K d x ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  exact one_ne_zero this

theorem affineSimple : Expected.affineSimple := by
  intro K _ _ d
  constructor
  · intro x
    apply (affineIndep K d {x}).mpr
    rw [linearIndepOn_singleton_iff]
    exact affineColumn_ne_zero x
  · intro x y hxy
    apply (affineIndep K d {x, y}).mpr
    apply (linearIndepOn_pair_iff _ hxy (affineColumn_ne_zero x)).mpr
    intro c hc
    have hc1 : c = 1 := by simpa [affineColumn] using congrArg Prod.fst hc
    have hxy' : x = y := by simpa [hc1, affineColumn] using congrArg Prod.snd hc
    exact hxy hxy'

theorem affineNoLoopsParallel : Expected.affineNoLoopsParallel := by
  intro K _ _ d
  constructor
  · intro x
    exact (_root_.Matroid.indep_singleton.mp ((affineSimple K d).1 x)).not_isLoop
  · intro x y hxy
    have hi := (affineSimple K d).2 x y hxy
    have hr : Expected.rank (Expected.affineMatroid K d) {x, y} = 2 := by
      simp [Expected.rank, hi.eRk_eq_encard, encard_pair hxy]
    simp [Expected.ParallelRelated, hxy, hr]

theorem affineSpan : Expected.affineSpan := by
  intro K _ d
  apply top_unique
  rintro ⟨c, x⟩ _
  have hx := subset_span (R := K) (mem_range_self x : Expected.affineColumn K d x ∈ _)
  have h0 := subset_span (R := K) (mem_range_self (0 : Fin d → K) :
    Expected.affineColumn K d 0 ∈ _)
  have hm := (span K (range (Expected.affineColumn K d))).add_mem
    ((span K _).smul_mem (c - 1) h0) hx
  convert hm using 1
  ext <;> simp [Expected.affineColumn]

theorem affineRank : Expected.affineRank := by
  intro K _ _ d
  rw [affineGround]
  unfold Expected.affineMatroid
  rw [vectorRank K univ finite_univ (Expected.affineColumn K d) univ (subset_refl _)]
  rw [image_univ, affineSpan]
  simp [Nat.add_comm]

theorem affinePointCount : Expected.affinePointCount := by
  intro K _ _ d
  rw [affineGround]
  simp [Nat.card_eq_fintype_card]

theorem affineLineInjective : Expected.affineLineInjective := by
  intro K _ d x a ha t s h
  exact smul_left_injective K ha (add_left_cancel h)

theorem affineLineCard : Expected.affineLineCard := by
  intro K _ _ d x a ha
  simpa [Expected.affineLine, Nat.card_eq_fintype_card] using
    ncard_range_of_injective (affineLineInjective K d x a ha)

theorem affineLineNormalized : Expected.affineLineNormalized := by
  intro K _ d x a
  ext v
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨rfl, mem_span_pair.mpr ⟨1, t, ?_⟩⟩
    ext <;> simp [Expected.affineColumn]
  · rintro ⟨h1, hv⟩
    obtain ⟨c, t, heq⟩ := mem_span_pair.mp hv
    have hc : c = 1 := by simpa [Expected.affineColumn, h1] using congrArg Prod.fst heq
    refine ⟨x + t • a, ⟨t, rfl⟩, ?_⟩
    rw [← heq, hc]
    ext <;> simp [Expected.affineColumn]

theorem affineDimensionZero : Expected.affineDimensionZero := by
  intro K _ _
  constructor
  · rw [affineGround]
    exact Set.eq_univ_iff_forall.mpr (fun x => by simp [Subsingleton.elim x 0]) |>.symm
  · simpa using affineRank K 0

end FiniteCombinatorics.Matroid
