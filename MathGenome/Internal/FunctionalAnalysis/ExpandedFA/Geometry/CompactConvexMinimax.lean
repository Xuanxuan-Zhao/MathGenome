import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CompactConvexMinimax
import Mathlib.Topology.Sion

/-! Convex–concave minimax, with all real extrema and universal saddle pairs.
We use Sion's theorem after checking convexity implies quasiconvexity, and
concavity implies quasiconcavity. No local convexity or norm is required.
-/
namespace ExpandedFA.Geometry
open Set
open Specs.ExpandedFA.Geometry.CompactConvexMinimax
universe u v

/-- An attained maximum is the finite real supremum of the image. -/
private lemma max_eq_sup {A : Type*} {s : Set A} {f : A → ℝ} {a : A}
    (ha : a ∈ s) (hm : IsMaxOn f s a) : sSup (f '' s) = f a :=
  hm.isLUB ha |>.csSup_eq (Set.Nonempty.image f ⟨a, ha⟩)

/-- An attained minimum is the finite real infimum of the image. -/
private lemma min_eq_inf {A : Type*} {s : Set A} {f : A → ℝ} {a : A}
    (ha : a ∈ s) (hm : IsMinOn f s a) : sInf (f '' s) = f a :=
  hm.isGLB ha |>.csInf_eq (Set.Nonempty.image f ⟨a, ha⟩)

/-- The compact convex minimax theorem in arbitrary Hausdorff real TVSs. -/
theorem compact_convex_minimax : compactConvexMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ _ _ _ _ _ _ K L F hK kK cK hL kL cL cv lsc cc usc
  have hmax (x : E) (hx : x ∈ K) := (usc x hx).exists_isMaxOn hL kL
  have hmin (y : G) (hy : y ∈ L) := (lsc y hy).exists_isMinOn hK kK
  have bmax (x : E) (hx : x ∈ K) : BddAbove (F x '' L) := by
    obtain ⟨y, _, hm⟩ := hmax x hx
    exact hm.bddAbove
  have bmin (y : G) (hy : y ∈ L) : BddBelow ((fun x => F x y) '' K) := by
    obtain ⟨x, _, hm⟩ := hmin y hy
    exact hm.bddBelow
  have le_max (x : E) (hx : x ∈ K) (y : G) (hy : y ∈ L) :
      F x y ≤ sectionSup L F x := le_csSup (bmax x hx) ⟨y, hy, rfl⟩
  have min_le (x : E) (hx : x ∈ K) (y : G) (hy : y ∈ L) :
      sectionInf K F y ≤ F x y := csInf_le (bmin y hy) ⟨x, hx, rfl⟩
  obtain ⟨a, ha, b, hb, hs⟩ := Sion.exists_isSaddlePointOn hK cK kK lsc
    (fun y hy => (cv y hy).quasiconvexOn) cL hL kL usc
    (fun x hx => (cc x hx).quasiconcaveOn)
  have sa : sectionSup L F a = F a b :=
    max_eq_sup hb (fun y hy => hs a ha y hy)
  have ib : sectionInf K F b = F a b :=
    min_eq_inf ha (fun x hx => hs x hx b hb)
  have amin : IsMinOn (sectionSup L F) K a := by
    intro x hx
    rw [sa]
    exact (hs x hx b hb).trans (le_max x hx b hb)
  have bmax' : IsMaxOn (sectionInf K F) L b := by
    intro y hy
    rw [ib]
    exact (min_le a ha y hy).trans (hs a ha y hy)
  have outerMin : sInf (sectionSup L F '' K) = F a b :=
    (min_eq_inf ha amin).trans sa
  have outerMax : sSup (sectionInf K F '' L) = F a b :=
    (max_eq_sup hb bmax').trans ib
  refine ⟨?_, ?_, amin.bddBelow, bmax'.bddAbove,
    outerMin.trans outerMax.symm, ⟨a, ha, amin, (min_eq_inf ha amin).symm⟩,
    ⟨b, hb, bmax', (max_eq_sup hb bmax').symm⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hm⟩ := hmax x hx
    exact ⟨hm.bddAbove, y, hy, hm, max_eq_sup hy hm⟩
  · intro y hy
    obtain ⟨x, hx, hm⟩ := hmin y hy
    exact ⟨hm.bddBelow, x, hx, hm, min_eq_inf hx hm⟩
  · intro x₀ hx₀ y₀ hy₀ hm₀ hn₀ x hx y hy
    have eq₀ : sectionSup L F x₀ = sectionInf K F y₀ := by
      calc sectionSup L F x₀ = sInf (sectionSup L F '' K) :=
              (min_eq_inf hx₀ hm₀).symm
        _ = sSup (sectionInf K F '' L) := outerMin.trans outerMax.symm
        _ = sectionInf K F y₀ := max_eq_sup hy₀ hn₀
    constructor
    · exact (le_max x₀ hx₀ y hy).trans (eq₀.le.trans (min_le x₀ hx₀ y₀ hy₀))
    · exact (le_max x₀ hx₀ y₀ hy₀).trans (eq₀.le.trans (min_le x hx y₀ hy₀))

/-- Source-domain formulation: the payoff can be defined only on K × L. -/
theorem restricted_compact_convex_minimax : restrictedMinimaxType.{u,v} := by
  intro E G _ _ _ _ _ _ _ _ _ _ _ _ K L F hK kK cK hL kL cL cv lsc cc usc
  apply compact_convex_minimax K L (extendPayoff F) hK kK cK hL kL cL
  · intro y hy
    exact cv ⟨y, hy⟩
  · intro y hy
    rw [← lowerSemicontinuous_restrict_iff]
    convert lsc ⟨y, hy⟩ using 1
    ext x
    simp [extendPayoff, x.property, hy]
  · intro x hx
    exact cc ⟨x, hx⟩
  · intro x hx
    rw [← upperSemicontinuousOn_iff_restrict]
    convert usc ⟨x, hx⟩ using 1
    ext y
    simp [extendPayoff, hx, y.property]

end ExpandedFA.Geometry
