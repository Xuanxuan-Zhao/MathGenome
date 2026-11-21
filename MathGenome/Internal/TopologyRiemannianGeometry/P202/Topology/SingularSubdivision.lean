import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SingularSubdivision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SimplicialApproximation
import Mathlib.Tactic.Abel

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SimplicialApproximation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory Opposite

namespace P202.SingularSubdivision
open P202Specs.SingularChains P202Specs.SingularSubdivision Convexity
universe u v w
variable (R : Type u) [CommRing R]

private theorem basis_ext {I N : Type*} [AddCommGroup N] [Module R N]
    {f g : (I →₀ R) →ₗ[R] N}
    (h : ∀ i, f (Finsupp.single i 1) = g (Finsupp.single i 1)) : f = g := by
  apply Finsupp.lhom_ext
  intro i r
  rw [← Finsupp.smul_single_one i r]
  simpa only [map_smul] using congrArg (r • ·) (h i)

@[simp] theorem affineBoundary_single {Y : Type v} (n : ℕ) (t : Fin (n+1) → Y) (r : R) :
    affineBoundary R Y n (Finsupp.single t r) =
      ∑ i : Fin (n+1), (-1 : R)^i.val • Finsupp.single (t ∘ i.succAbove) r := by
  simp [affineBoundary, LinearMap.sum_apply, LinearMap.smul_apply]

@[simp] theorem cone_single {Y : Type v} (b : Y) (n : ℕ) (t : Fin n → Y) (r : R) :
    cone R b n (Finsupp.single t r) = Finsupp.single (Fin.cons b t) r := by
  simp [cone]

theorem boundary_cone_zero {Y : Type v} (b : Y) (c : AffineChains R Y 0) :
    affineBoundary R Y 0 (cone R b 0 c) = c := by
  have h : (affineBoundary R Y 0).comp (cone R b 0) = LinearMap.id := by
    apply basis_ext R
    intro t
    change affineBoundary R Y 0 (cone R b 0 (Finsupp.single t 1)) = Finsupp.single t 1
    rw [cone_single, affineBoundary_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  exact LinearMap.congr_fun h c

theorem boundary_cone {Y : Type v} (b : Y) (n : ℕ) (c : AffineChains R Y (n+1)) :
    affineBoundary R Y (n+1) (cone R b (n+1) c) =
      c - cone R b n (affineBoundary R Y n c) := by
  have h : (affineBoundary R Y (n+1)).comp (cone R b (n+1)) =
      LinearMap.id - (cone R b n).comp (affineBoundary R Y n) := by
    apply basis_ext R
    intro t
    change affineBoundary R Y (n+1) (cone R b (n+1) (Finsupp.single t 1)) =
      Finsupp.single t 1 - cone R b n (affineBoundary R Y n (Finsupp.single t 1))
    rw [cone_single, affineBoundary_single, Fin.sum_univ_succ]
    rw [affineBoundary_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Fin.cons_comp_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      map_smul, cone_single, Fin.cons_comp_succ_succAbove,
      ← Finset.sum_neg_distrib, sub_eq_add_neg]
    rfl
  exact LinearMap.congr_fun h c

theorem affineBoundary_squared {Y : Type v} (n : ℕ) (c : AffineChains R Y (n+2)) :
    affineBoundary R Y n (affineBoundary R Y (n+1) c) = 0 := by
  induction n with
  | zero =>
    have h : (affineBoundary R Y 0).comp (affineBoundary R Y 1) = 0 := by
      apply basis_ext R
      intro t
      have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
      rw [ht, ← cone_single R (t 0) 1]
      rw [LinearMap.comp_apply, boundary_cone, map_sub, boundary_cone_zero]
      simp
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (affineBoundary R Y (n+1)).comp (affineBoundary R Y (n+2)) = 0 := by
      apply basis_ext R
      intro t
      have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
      rw [ht, ← cone_single R (t 0) (n+2)]
      rw [LinearMap.comp_apply, boundary_cone, map_sub, boundary_cone, ih]
      simp
    exact LinearMap.congr_fun h c

@[simp] theorem affineSubdivision_single {Y : Type v} [ConvexSpace ℝ Y]
    (n : ℕ) (t : Fin (n+1) → Y) :
    affineSubdivision R Y (n+1) (Finsupp.single t 1) =
      cone R ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).iConvexComb t) n
        (affineSubdivision R Y n (affineBoundary R Y n (Finsupp.single t 1))) := by
  simp [affineSubdivision, Finsupp.linearCombination_single]

theorem affineSubdivision_boundary {Y : Type v} [ConvexSpace ℝ Y]
    (n : ℕ) (c : AffineChains R Y (n+1)) :
    affineBoundary R Y n (affineSubdivision R Y (n+1) c) =
      affineSubdivision R Y n (affineBoundary R Y n c) := by
  induction n with
  | zero =>
    have h : (affineBoundary R Y 0).comp (affineSubdivision R Y 1) =
        (affineSubdivision R Y 0).comp (affineBoundary R Y 0) := by
      apply basis_ext R
      intro t
      simp only [LinearMap.comp_apply, affineSubdivision_single, boundary_cone_zero]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (affineBoundary R Y (n+1)).comp (affineSubdivision R Y (n+2)) =
        (affineSubdivision R Y (n+1)).comp (affineBoundary R Y (n+1)) := by
      apply basis_ext R
      intro t
      simp only [LinearMap.comp_apply, affineSubdivision_single, boundary_cone,
        ih, affineBoundary_squared, map_zero, sub_zero]
    exact LinearMap.congr_fun h c

@[simp] theorem affineHomotopy_single {Y : Type v} [ConvexSpace ℝ Y]
    (n : ℕ) (t : Fin (n+1) → Y) :
    affineHomotopy R Y (n+1) (Finsupp.single t 1) =
      cone R ((StdSimplex.barycenter : StdSimplex ℝ (Fin (n+1))).iConvexComb t) (n+1)
        (affineSubdivision R Y (n+1) (Finsupp.single t 1) - Finsupp.single t 1 -
          affineHomotopy R Y n (affineBoundary R Y n (Finsupp.single t 1))) := by
  simp [affineHomotopy, Finsupp.linearCombination_single]

theorem affineHomotopy_identity {Y : Type v} [ConvexSpace ℝ Y]
    (n : ℕ) (c : AffineChains R Y (n+1)) :
    affineBoundary R Y (n+1) (affineHomotopy R Y (n+1) c) +
      affineHomotopy R Y n (affineBoundary R Y n c) =
        affineSubdivision R Y (n+1) c - c := by
  induction n with
  | zero =>
    have h : (affineBoundary R Y 1).comp (affineHomotopy R Y 1) +
        (affineHomotopy R Y 0).comp (affineBoundary R Y 0) =
        affineSubdivision R Y 1 - LinearMap.id := by
      apply basis_ext R
      intro t
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, affineHomotopy_single, boundary_cone,
        map_sub, affineSubdivision_boundary]
      simp [affineHomotopy, affineSubdivision]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (affineBoundary R Y (n+2)).comp (affineHomotopy R Y (n+2)) +
        (affineHomotopy R Y (n+1)).comp (affineBoundary R Y (n+1)) =
        affineSubdivision R Y (n+2) - LinearMap.id := by
      apply basis_ext R
      intro t
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.id_apply, affineHomotopy_single, boundary_cone, map_sub,
        affineSubdivision_boundary]
      have hz := ih (affineBoundary R Y (n+1) (Finsupp.single t 1))
      rw [affineBoundary_squared, map_zero, add_zero] at hz
      rw [hz, map_sub]
      abel
    exact LinearMap.congr_fun h c

@[simp] theorem affinePush_single {Y : Type v} {Z : Type w} (f : Y → Z)
    (n : ℕ) (t : Fin n → Y) (r : R) :
    affinePush R f n (Finsupp.single t r) = Finsupp.single (f ∘ t) r := by
  simp [affinePush]

theorem affinePush_boundary {Y : Type v} {Z : Type w} (f : Y → Z)
    (n : ℕ) (c : AffineChains R Y (n+1)) :
    affinePush R f n (affineBoundary R Y n c) =
      affineBoundary R Z n (affinePush R f (n+1) c) := by
  have h : (affinePush R f n).comp (affineBoundary R Y n) =
      (affineBoundary R Z n).comp (affinePush R f (n+1)) := by
    apply basis_ext R
    intro t
    simp only [LinearMap.comp_apply, affineBoundary_single, affinePush_single,
      map_sum, map_smul, Function.comp_assoc]
  exact LinearMap.congr_fun h c

theorem affinePush_cone {Y : Type v} {Z : Type w} (f : Y → Z) (b : Y)
    (n : ℕ) (c : AffineChains R Y n) :
    affinePush R f (n+1) (cone R b n c) = cone R (f b) n (affinePush R f n c) := by
  have h : (affinePush R f (n+1)).comp (cone R b n) =
      (cone R (f b) n).comp (affinePush R f n) := by
    apply basis_ext R
    intro t
    simp only [LinearMap.comp_apply, affinePush_single, cone_single]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact LinearMap.congr_fun h c

theorem affineSubdivision_natural {Y : Type v} {Z : Type w}
    [ConvexSpace ℝ Y] [ConvexSpace ℝ Z] (f : ConvexSpace.AffineMap ℝ Y Z)
    (n : ℕ) (c : AffineChains R Y n) :
    affinePush R f n (affineSubdivision R Y n c) =
      affineSubdivision R Z n (affinePush R f n c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (affinePush R f (n+1)).comp (affineSubdivision R Y (n+1)) =
        (affineSubdivision R Z (n+1)).comp (affinePush R f (n+1)) := by
      apply basis_ext R
      intro t
      simp only [LinearMap.comp_apply, affinePush_single, affineSubdivision_single,
        affinePush_cone, ih, affinePush_boundary,
        f.isAffineMap.map_iConvexComb]
    exact LinearMap.congr_fun h c

theorem affineHomotopy_natural {Y : Type v} {Z : Type w}
    [ConvexSpace ℝ Y] [ConvexSpace ℝ Z] (f : ConvexSpace.AffineMap ℝ Y Z)
    (n : ℕ) (c : AffineChains R Y n) :
    affinePush R f (n+1) (affineHomotopy R Y n c) =
      affineHomotopy R Z n (affinePush R f n c) := by
  induction n with
  | zero => simp [affineHomotopy]
  | succ n ih =>
    have h : (affinePush R f (n+2)).comp (affineHomotopy R Y (n+1)) =
        (affineHomotopy R Z (n+1)).comp (affinePush R f (n+1)) := by
      apply basis_ext R
      intro t
      simp only [LinearMap.comp_apply, affinePush_single, affineHomotopy_single,
        affinePush_cone, map_sub, affineSubdivision_natural, ih,
        affinePush_boundary, f.isAffineMap.map_iConvexComb]
    exact LinearMap.congr_fun h c

theorem affineSubdivision_one {Y : Type v} [ConvexSpace ℝ Y]
    (c : AffineChains R Y 1) : affineSubdivision R Y 1 c = c := by
  have h : affineSubdivision R Y 1 = LinearMap.id := by
    apply basis_ext R
    intro t
    change affineSubdivision R Y 1 (Finsupp.single t 1) = Finsupp.single t 1
    rw [affineSubdivision_single]
    rw [StdSimplex.barycenter_fin_one, iConvexComb_single]
    change cone R (t 0) 0 (affineBoundary R Y 0 (Finsupp.single t 1)) = _
    rw [affineBoundary_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, cone_single]
    congr 1
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  exact LinearMap.congr_fun h c

theorem affineHomotopy_one {Y : Type v} [ConvexSpace ℝ Y]
    (c : AffineChains R Y 1) : affineHomotopy R Y 1 c = 0 := by
  have h : affineHomotopy R Y 1 = 0 := by
    apply basis_ext R
    intro t
    change affineHomotopy R Y 1 (Finsupp.single t 1) = 0
    rw [affineHomotopy_single, affineSubdivision_one]
    simp only [affineHomotopy, LinearMap.zero_apply, sub_self, map_zero]
  exact LinearMap.congr_fun h c

theorem affineSimplexMap_face {m n : ℕ} (t : Fin (n+2) → Delta m) (i : Fin (n+2)) :
    (affineSimplexMap t).comp (faceInclusion i) = affineSimplexMap (t ∘ i.succAbove) := by
  have h : (StdSimplex.affineMapMk t).comp (StdSimplex.affineMap (R := ℝ) i.succAbove) =
      StdSimplex.affineMapMk (t ∘ i.succAbove) := by
    ext j
    simp [StdSimplex.affineMap]
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : ConvexSpace.AffineMap ℝ (Delta n) (Delta m) => f x) h

theorem affineSimplexMap_comp {k m n : ℕ} (t : Fin (m+1) → Delta k)
    (q : Fin (n+1) → Delta m) :
    (affineSimplexMap t).comp (affineSimplexMap q) =
      affineSimplexMap (fun j => affineSimplexMap t (q j)) := by
  have h : (StdSimplex.affineMapMk t).comp (StdSimplex.affineMapMk q) =
      StdSimplex.affineMapMk (fun j => affineSimplexMap t (q j)) := by
    ext j
    simp [affineSimplexMap]
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : ConvexSpace.AffineMap ℝ (Delta n) (Delta k) => f x) h

@[simp] theorem affineSimplexMap_vertices (n : ℕ) :
    affineSimplexMap (StdSimplex.single : Fin (n+1) → Delta n) = ContinuousMap.id _ := by
  have h : StdSimplex.affineMapMk (StdSimplex.single : Fin (n+1) → Delta n) =
      ConvexSpace.AffineMap.id (R := ℝ) (Delta n) := by
    ext j
    simp
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : ConvexSpace.AffineMap ℝ (Delta n) (Delta n) => f x) h

@[simp] theorem evaluate_single {X : TopCat.{v}} {m : ℕ} (s : Simplex X m)
    (n : ℕ) (t : Fin (n+1) → Delta m) (r : R) :
    evaluate R s n (Finsupp.single t r) = Finsupp.single
      ((simplexEquiv X n).symm ((simplexEquiv X m s).comp (affineSimplexMap t))) r := by
  simp [evaluate]

@[simp] theorem evaluate_vertices {X : TopCat.{v}} {n : ℕ} (s : Simplex X n) :
    evaluate R s n (Finsupp.single StdSimplex.single 1) = Finsupp.single s 1 := by
  simp

theorem evaluate_boundary {X : TopCat.{v}} {m : ℕ} (s : Simplex X m)
    (n : ℕ) (c : AffineChains R (Delta m) (n+2)) :
    boundary R R X n (evaluate R s (n+1) c) =
      evaluate R s n (affineBoundary R (Delta m) (n+1) c) := by
  have h : (boundary R R X n).comp (evaluate R s (n+1)) =
      (evaluate R s n).comp (affineBoundary R (Delta m) (n+1)) := by
    apply basis_ext R
    intro t
    change boundary R R X n (evaluate R s (n+1) (Finsupp.single t 1)) =
      evaluate R s n (affineBoundary R (Delta m) (n+1) (Finsupp.single t 1))
    rw [evaluate_single, P202.SingularChains.boundary_single, affineBoundary_single, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, evaluate_single]
    have hi : face i ((simplexEquiv X (n+1)).symm
        ((simplexEquiv X m s).comp (affineSimplexMap t))) =
        (simplexEquiv X n).symm ((simplexEquiv X m s).comp
          (affineSimplexMap (t ∘ i.succAbove))) := by
      apply (simplexEquiv X n).injective
      simp only [P202.SingularChains.simplexEquiv_face, Equiv.apply_symm_apply]
      rw [ContinuousMap.comp_assoc, affineSimplexMap_face]
    rw [hi]
    have hsign : (-1 : R)^i.val = (((-1 : ℤ)^i.val : ℤ) : R) := by simp
    rw [hsign, Int.cast_smul_eq_zsmul]
  exact LinearMap.congr_fun h c

theorem evaluate_push {X : TopCat.{v}} {k m : ℕ} (s : Simplex X k)
    (t : Fin (m+1) → Delta k) (n : ℕ) (c : AffineChains R (Delta m) (n+1)) :
    evaluate R s n (affinePush R (StdSimplex.affineMapMk t) (n+1) c) =
      evaluate R ((simplexEquiv X m).symm
        ((simplexEquiv X k s).comp (affineSimplexMap t))) n c := by
  have h : (evaluate R s n).comp (affinePush R (StdSimplex.affineMapMk t) (n+1)) =
      evaluate R ((simplexEquiv X m).symm
        ((simplexEquiv X k s).comp (affineSimplexMap t))) n := by
    apply basis_ext R
    intro q
    simp only [LinearMap.comp_apply, affinePush_single, evaluate_single,
      Equiv.apply_symm_apply]
    rw [ContinuousMap.comp_assoc, affineSimplexMap_comp]
    rfl
  exact LinearMap.congr_fun h c

theorem subdivision_evaluate {X : TopCat.{v}} {m : ℕ} (s : Simplex X m)
    (n : ℕ) (c : AffineChains R (Delta m) (n+1)) :
    subdivision R X n (evaluate R s n c) =
      evaluate R s n (affineSubdivision R (Delta m) (n+1) c) := by
  have h : (subdivision R X n).comp (evaluate R s n) =
      (evaluate R s n).comp (affineSubdivision R (Delta m) (n+1)) := by
    apply basis_ext R
    intro t
    change subdivision R X n (evaluate R s n (Finsupp.single t 1)) = _
    rw [evaluate_single]
    simp only [subdivision, Finsupp.linearCombination_single, one_smul]
    rw [← evaluate_push R s t n, affineSubdivision_natural, affinePush_single]
    simp only [Function.comp_def, StdSimplex.affineMapMk_single]
    rfl
  exact LinearMap.congr_fun h c

theorem homotopy_evaluate {X : TopCat.{v}} {m : ℕ} (s : Simplex X m)
    (n : ℕ) (c : AffineChains R (Delta m) (n+1)) :
    homotopy R X n (evaluate R s n c) =
      evaluate R s (n+1) (affineHomotopy R (Delta m) (n+1) c) := by
  have h : (homotopy R X n).comp (evaluate R s n) =
      (evaluate R s (n+1)).comp (affineHomotopy R (Delta m) (n+1)) := by
    apply basis_ext R
    intro t
    change homotopy R X n (evaluate R s n (Finsupp.single t 1)) = _
    rw [evaluate_single]
    simp only [homotopy, Finsupp.linearCombination_single, one_smul]
    rw [← evaluate_push R s t (n+1), affineHomotopy_natural, affinePush_single]
    simp only [Function.comp_def, StdSimplex.affineMapMk_single]
    rfl
  exact LinearMap.congr_fun h c

@[simp] theorem subdivision_single (X : TopCat.{v}) (n : ℕ) (s : Simplex X n) :
    subdivision R X n (Finsupp.single s 1) = evaluate R s n
      (affineSubdivision R (Delta n) (n+1) (Finsupp.single StdSimplex.single 1)) := by
  simp [subdivision, Finsupp.linearCombination_single]

@[simp] theorem homotopy_single (X : TopCat.{v}) (n : ℕ) (s : Simplex X n) :
    homotopy R X n (Finsupp.single s 1) = evaluate R s (n+1)
      (affineHomotopy R (Delta n) (n+1) (Finsupp.single StdSimplex.single 1)) := by
  simp [homotopy, Finsupp.linearCombination_single]

theorem subdivision_zero (X : TopCat.{v}) (c : Chains R X 0) :
    subdivision R X 0 c = c := by
  have h : subdivision R X 0 = LinearMap.id := by
    apply basis_ext R
    intro s
    change subdivision R X 0 (Finsupp.single s 1) = Finsupp.single s 1
    rw [subdivision_single, affineSubdivision_one, evaluate_vertices]
  exact LinearMap.congr_fun h c

theorem homotopy_zero (X : TopCat.{v}) (c : Chains R X 0) :
    homotopy R X 0 c = 0 := by
  have h : homotopy R X 0 = 0 := by
    apply basis_ext R
    intro s
    change homotopy R X 0 (Finsupp.single s 1) = 0
    rw [homotopy_single, affineHomotopy_one, map_zero]
  exact LinearMap.congr_fun h c

theorem subdivision_boundary (X : TopCat.{v}) (n : ℕ) (c : Chains R X (n+1)) :
    boundary R R X n (subdivision R X (n+1) c) =
      subdivision R X n (boundary R R X n c) := by
  have h : (boundary R R X n).comp (subdivision R X (n+1)) =
      (subdivision R X n).comp (boundary R R X n) := by
    apply basis_ext R
    intro s
    change boundary R R X n (subdivision R X (n+1) (Finsupp.single s 1)) = _
    rw [subdivision_single, evaluate_boundary, affineSubdivision_boundary,
      ← subdivision_evaluate, ← evaluate_boundary, evaluate_vertices]
    rfl
  exact LinearMap.congr_fun h c

/-- A version of the differential with its concrete finite-chain type exposed. -/
private def chainBoundary (X : TopCat.{v}) (n : ℕ) :
    Chains R X (n+1) →ₗ[R] Chains R X n := boundary R R X n

theorem homotopy_identity (X : TopCat.{v}) (n : ℕ) (c : Chains R X (n+1)) :
    chainBoundary R X (n+1) (homotopy R X (n+1) c) +
      homotopy R X n (boundary R R X n c) = subdivision R X (n+1) c - c := by
  have h : (chainBoundary R X (n+1)).comp (homotopy R X (n+1)) +
      (homotopy R X n).comp (chainBoundary R X n) =
      subdivision R X (n+1) - LinearMap.id := by
    apply basis_ext R
    intro s
    change chainBoundary R X (n+1) (homotopy R X (n+1) (Finsupp.single s 1)) +
      homotopy R X n (boundary R R X n (Finsupp.single s 1)) = _
    rw [homotopy_single]
    have hd := evaluate_boundary R s (n+1)
      (affineHomotopy R (Delta (n+1)) (n+2) (Finsupp.single StdSimplex.single 1))
    change chainBoundary R X (n+1) _ = _ at hd
    rw [hd, ← evaluate_vertices R s, evaluate_boundary, homotopy_evaluate,
      ← map_add, affineHomotopy_identity, map_sub, evaluate_vertices]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, subdivision_single]
  exact LinearMap.congr_fun h c

theorem evaluate_natural {X Y : TopCat.{v}} (f : X ⟶ Y) {m : ℕ}
    (s : Simplex X m) (n : ℕ) (c : AffineChains R (Delta m) (n+1)) :
    ((chainMap R R f).f n).hom (evaluate R s n c) =
      evaluate R ((TopCat.toSSet.map f).app (op (SimplexCategory.mk m)) s) n c := by
  have h : (((chainMap R R f).f n).hom).comp (evaluate R s n) =
      evaluate R ((TopCat.toSSet.map f).app (op (SimplexCategory.mk m)) s) n := by
    apply basis_ext R
    intro t
    change ((chainMap R R f).f n).hom (evaluate R s n (Finsupp.single t 1)) = _
    rw [evaluate_single, P202.SingularChains.chainMap_single]
    change (Finsupp.single
      (((TopCat.toSSet.map f).app (op (SimplexCategory.mk n)))
        ((simplexEquiv X n).symm ((simplexEquiv X m s).comp (affineSimplexMap t)))) 1 :
        Chains R Y n) = evaluate R _ n (Finsupp.single t 1)
    rw [evaluate_single]
    congr 1
  exact LinearMap.congr_fun h c

theorem subdivision_natural {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ)
    (c : Chains R X n) :
    subdivision R Y n (((chainMap R R f).f n).hom c) =
      ((chainMap R R f).f n).hom (subdivision R X n c) := by
  have h : (subdivision R Y n).comp ((chainMap R R f).f n).hom =
      (((chainMap R R f).f n).hom).comp (subdivision R X n) := by
    apply basis_ext R
    intro s
    change subdivision R Y n (((chainMap R R f).f n).hom (Finsupp.single s 1)) = _
    rw [P202.SingularChains.chainMap_single, subdivision_single]
    change _ = ((chainMap R R f).f n).hom (subdivision R X n (Finsupp.single s 1))
    rw [subdivision_single, evaluate_natural]
  exact LinearMap.congr_fun h c

theorem homotopy_natural {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ)
    (c : Chains R X n) :
    homotopy R Y n (((chainMap R R f).f n).hom c) =
      ((chainMap R R f).f (n+1)).hom (homotopy R X n c) := by
  have h : (homotopy R Y n).comp ((chainMap R R f).f n).hom =
      (((chainMap R R f).f (n+1)).hom).comp (homotopy R X n) := by
    apply basis_ext R
    intro s
    change homotopy R Y n (((chainMap R R f).f n).hom (Finsupp.single s 1)) = _
    rw [P202.SingularChains.chainMap_single, homotopy_single]
    change _ = ((chainMap R R f).f (n+1)).hom (homotopy R X n (Finsupp.single s 1))
    rw [homotopy_single, evaluate_natural]
  exact LinearMap.congr_fun h c

theorem evaluate_carrier {X : TopCat.{v}} {m : ℕ} (s : Simplex X m)
    (n : ℕ) (c : AffineChains R (Delta m) (n+1))
    (q : Simplex X n) (hq : q ∈ (evaluate R s n c).support) :
    Set.range (simplexEquiv X n q) ⊆ Set.range (simplexEquiv X m s) := by
  classical
  change q ∈ (Finsupp.mapDomain _ c).support at hq
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hq)
  subst q
  rintro y ⟨x, rfl⟩
  exact ⟨affineSimplexMap t x, by simp⟩

private theorem linearCombination_carrier {I J : Type*} (F : I → J →₀ R)
    (c : I →₀ R) (j : J) (hj : j ∈ (Finsupp.linearCombination R F c).support) :
    ∃ i ∈ c.support, j ∈ (F i).support := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hj
  obtain ⟨i, hi, hji⟩ := Finsupp.mem_support_finsetSum j hj
  exact ⟨i, hi, Finsupp.support_smul hji⟩

theorem subdivision_carrier (X : TopCat.{v}) (n : ℕ) (c : Chains R X n)
    (q : Simplex X n) (hq : q ∈ (subdivision R X n c).support) :
    ∃ s ∈ c.support, Set.range (simplexEquiv X n q) ⊆ Set.range (simplexEquiv X n s) := by
  obtain ⟨s, hs, hqs⟩ := linearCombination_carrier R _ c q hq
  exact ⟨s, hs, evaluate_carrier R s n _ q hqs⟩

theorem homotopy_carrier (X : TopCat.{v}) (n : ℕ) (c : Chains R X n)
    (q : Simplex X (n+1)) (hq : q ∈ (homotopy R X n c).support) :
    ∃ s ∈ c.support, Set.range (simplexEquiv X (n+1) q) ⊆ Set.range (simplexEquiv X n s) := by
  obtain ⟨s, hs, hqs⟩ := linearCombination_carrier R _ c q hq
  exact ⟨s, hs, evaluate_carrier R s (n+1) _ q hqs⟩

theorem subdivision_support (X : TopCat.{v}) (n : ℕ) (c : Chains R X n) :
    support (subdivision R X n c) ⊆ support c := by
  intro y hy
  simp only [support, Set.mem_iUnion] at hy ⊢
  obtain ⟨q, hq, hy⟩ := hy
  obtain ⟨s, hs, hqs⟩ := subdivision_carrier R X n c q hq
  exact ⟨s, hs, hqs hy⟩

theorem homotopy_support (X : TopCat.{v}) (n : ℕ) (c : Chains R X n) :
    support (homotopy R X n c) ⊆ support c := by
  intro y hy
  simp only [support, Set.mem_iUnion] at hy ⊢
  obtain ⟨q, hq, hy⟩ := hy
  obtain ⟨s, hs, hqs⟩ := homotopy_carrier R X n c q hq
  exact ⟨s, hs, hqs hy⟩

theorem preserves_subspace (X : TopCat.{v}) (A : Set X) (n : ℕ) (c : Chains R X n)
    (hc : SupportedIn A c) :
    SupportedIn A (subdivision R X n c) ∧ SupportedIn A (homotopy R X n c) :=
  ⟨(subdivision_support R X n c).trans hc, (homotopy_support R X n c).trans hc⟩

theorem preserves_small (X : TopCat.{v}) {ι : Type w} (U : ι → Set X)
    (n : ℕ) (c : Chains R X n) (hc : IsSmall U c) :
    IsSmall U (subdivision R X n c) ∧ IsSmall U (homotopy R X n c) := by
  constructor
  · intro q hq
    obtain ⟨s, hs, hqs⟩ := subdivision_carrier R X n c q hq
    obtain ⟨i, hi⟩ := hc s hs
    exact ⟨i, hqs.trans hi⟩
  · intro q hq
    obtain ⟨s, hs, hqs⟩ := homotopy_carrier R X n c q hq
    obtain ⟨i, hi⟩ := hc s hs
    exact ⟨i, hqs.trans hi⟩

theorem augmentedSubdivision_boundary (X : TopCat.{v}) (n : ℕ) :
    augmentedSubdivision R X (n+1) ≫ (augmentedShifted R R X).d (n+1) n =
      (augmentedShifted R R X).d (n+1) n ≫ augmentedSubdivision R X n := by
  cases n with
  | zero =>
    have h : subdivision R X 0 = LinearMap.id := LinearMap.ext (subdivision_zero R X)
    simp [augmentedSubdivision, augmentedShifted, h]
    exact Category.id_comp _
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact subdivision_boundary R X n c

theorem augmentedHomotopy_identity (X : TopCat.{v}) (n : ℕ) :
    augmentedHomotopy R X (n+1) ≫ (augmentedShifted R R X).d (n+2) (n+1) +
      (augmentedShifted R R X).d (n+1) n ≫ augmentedHomotopy R X n =
        augmentedSubdivision R X (n+1) - 𝟙 _ := by
  cases n with
  | zero =>
    have hS : subdivision R X 0 = LinearMap.id := LinearMap.ext (subdivision_zero R X)
    have hK : homotopy R X 0 = 0 := LinearMap.ext (homotopy_zero R X)
    simp [augmentedHomotopy, augmentedSubdivision, hS, hK]
    exact (sub_self _).symm
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact homotopy_identity R X n c

theorem augmentedHomotopy_bottom (X : TopCat.{v}) :
    augmentedHomotopy R X 0 ≫ (augmentedShifted R R X).d 1 0 =
      augmentedSubdivision R X 0 - 𝟙 _ := by
  simp [augmentedHomotopy, augmentedSubdivision]

theorem augmentedSubdivision_natural {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ) :
    (augmentedShiftedMap R R f).f n ≫ augmentedSubdivision R Y n =
      augmentedSubdivision R X n ≫ (augmentedShiftedMap R R f).f n := by
  cases n with
  | zero => simp [augmentedSubdivision, augmentedShiftedMap]
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact subdivision_natural R f n c

theorem augmentedHomotopy_natural {X Y : TopCat.{v}} (f : X ⟶ Y) (n : ℕ) :
    (augmentedShiftedMap R R f).f n ≫ augmentedHomotopy R Y n =
      augmentedHomotopy R X n ≫ (augmentedShiftedMap R R f).f (n+1) := by
  cases n with
  | zero => simp [augmentedHomotopy]
  | succ n =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact homotopy_natural R f n c

end P202.SingularSubdivision

namespace P202.Topology
universe u v
open P202.SingularSubdivision P202Specs.SingularChains P202Specs.SingularSubdivision

/-- Conditional draft interface. The affine-chain construction proves the
conclusion independently of the geometric premises; all frozen premise types
are nevertheless retained in their required order for later owner closure. -/
theorem supportControlledSubdivision_conditional
    (_finiteMetricRealization :
      P202Specs.Topology.SimplicialApproximation.finiteMetricRealization.{u})
    (_finiteSourceSimplicialApproximation :
      P202Specs.Topology.SimplicialApproximation.finiteSourceSimplicialApproximation.{u,v})
    (_openStars : P202Specs.Topology.SimplicialApproximation.openStars.{u})
    (_shrinkingMeshAndStars :
      P202Specs.Topology.SimplicialApproximation.shrinkingMeshAndStars.{u})
    (_simplicialMapContinuous :
      P202Specs.Topology.SimplicialApproximation.simplicialMapContinuous.{u,v})
    (_starCriterion : P202Specs.Topology.SimplicialApproximation.starCriterion.{u,v})
    (_starHomotopy : P202Specs.Topology.SimplicialApproximation.starHomotopy.{u,v})
    (_starRefinement : P202Specs.Topology.SimplicialApproximation.starRefinement.{u,v})
    (_subdivisionFaceCompatibility :
      P202Specs.Topology.SimplicialApproximation.subdivisionFaceCompatibility.{u})
    (_subdivisionHomeomorphism :
      P202Specs.Topology.SimplicialApproximation.subdivisionHomeomorphism.{u}) :
    P202Specs.SingularSubdivision.supportControlledSubdivision.{u,v} := by
  intro R _
  refine ⟨subdivision_boundary R, subdivision_natural R, homotopy_natural R,
    ?_, homotopy_identity R, ?_, ?_, preserves_subspace R, ?_,
    augmentedSubdivision_boundary R, augmentedHomotopy_identity R,
    augmentedHomotopy_bottom R, augmentedSubdivision_natural R,
    augmentedHomotopy_natural R⟩
  · intro X c
    rw [homotopy_zero, map_zero, subdivision_zero, sub_self]
  · intro X n c
    exact ⟨subdivision_support R X n c, homotopy_support R X n c⟩
  · intro X c
    exact ⟨subdivision_zero R X c, homotopy_zero R X c,
      congrArg (augmentationLinear R R X) (subdivision_zero R X c)⟩
  · intro X ι U n c hc
    exact preserves_small R X U n c hc

end P202.Topology

universe v8_closure_1f0c6291133c722f_u0 v8_closure_1f0c6291133c722f_u1
theorem _root_.«P202».«Topology».«supportControlledSubdivision» : _root_.«P202Specs».«SingularSubdivision».«supportControlledSubdivision».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1} :=
  @_root_.«P202».«Topology».«supportControlledSubdivision_conditional».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1} (@_root_.«P202».«Topology».«finiteMetricRealization».{v8_closure_1f0c6291133c722f_u0}) (@_root_.«P202».«Topology».«finiteSourceSimplicialApproximation».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1}) (@_root_.«P202».«Topology».«openStars».{v8_closure_1f0c6291133c722f_u0}) (@_root_.«P202».«Topology».«shrinkingMeshAndStars».{v8_closure_1f0c6291133c722f_u0}) (@_root_.«P202».«Topology».«simplicialMapContinuous».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1}) (@_root_.«P202».«Topology».«starCriterion».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1}) (@_root_.«P202».«Topology».«starHomotopy».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1}) (@_root_.«P202».«Topology».«starRefinement».{v8_closure_1f0c6291133c722f_u0, v8_closure_1f0c6291133c722f_u1}) (@_root_.«P202».«Topology».«subdivisionFaceCompatibility».{v8_closure_1f0c6291133c722f_u0}) (@_root_.«P202».«Topology».«subdivisionHomeomorphism».{v8_closure_1f0c6291133c722f_u0})
