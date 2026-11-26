import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
import MathGenome.Internal.AlgebraCore.P103.Ch11.TorExactSequences

noncomputable section

open CategoryTheory
open scoped BigOperators
open CommutativeAlgebraNotes.Intersection.IsolatedTorSupport (Tor)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler
  (cutoffEuler_symm regularLocalDimension ringKrullDim_eq_regularLocalDimension
    tor_vanishes_above)
open CommutativeAlgebraNotes.Intersection.IsolatedIntersectionEuler.Specs (intersectionEuler)
open P103.Ch11.ExtTorDefinitions (resolutionFamily torMaps torMapLinear)
open P103.Specs.Ch10.Complexes (homologyMap)
open P103.Specs.Ch11.ExtTorDefinitions (tensorSecondMap)
open P103.Specs.Ch11.TorBalance (commRightFunctor)

namespace CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity

universe u v w

variable {R : Type u} [CommRing R]

private theorem tor_second_map_apply (N : ModuleCat.{w} R)
    {A B : ModuleCat.{v} R} (f : A ⟶ B) (i : ℕ) (x : Tor N A i) :
    torMapLinear R i (𝟙 ((commRightFunctor R).obj N)) f x =
      homologyMap (tensorSecondMap
        (resolutionFamily Rᵐᵒᵖ ((commRightFunctor R).obj N)).val.complex f.hom) i x := by
  let P := resolutionFamily Rᵐᵒᵖ ((commRightFunctor R).obj N)
  change (torMaps i).map P P (𝟙 _) f x =
    homologyMap (tensorSecondMap P.val.complex f.hom) i x
  rw [(torMaps i).formula P P (𝟙 _) f (𝟙 _)
    (P103.Ch10.Comparison.chainLift_id P.val)]
  simp only [P103.Ch11.TorExactSequences.tensorFirstMap_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The Tor sequence in the coefficient variable for the chapter's fixed resolution. -/
private theorem tor_long_exact_second (A M C : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (f : A ⟶ M) (g : M ⟶ C) (hf : Function.Injective f.hom)
    (he : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    let i (n : ℕ) : Tor N A n →ₗ[R] Tor N M n :=
      torMapLinear R n (𝟙 ((commRightFunctor R).obj N)) f
    let p (n : ℕ) : Tor N M n →ₗ[R] Tor N C n :=
      torMapLinear R n (𝟙 ((commRightFunctor R).obj N)) g
    ∃ δ : ∀ n, Tor N C (n + 1) →ₗ[R] Tor N A n,
      (∀ n, Function.Exact (i n) (p n)) ∧
      (∀ n, Function.Exact (p (n + 1)) (δ n)) ∧
      (∀ n, Function.Exact (δ n) (i n)) ∧ Function.Surjective (p 0) := by
  let B := (commRightFunctor R).obj N
  let P := resolutionFamily Rᵐᵒᵖ B
  obtain ⟨⟨δ, hδ⟩, hzero, hsurj⟩ :=
    P103.Ch11.TorExactSequences.second_sequence R B P.val P.property A M C f.hom g.hom hf he hg
  have hmap {X Y : ModuleCat.{v} R} (j : X ⟶ Y) (n : ℕ) :
      (⇑(torMapLinear R n (𝟙 B) j) : Tor N X n → Tor N Y n) =
        ⇑(homologyMap (tensorSecondMap P.val.complex j.hom) n) :=
    funext (tor_second_map_apply N j n)
  let δ' (n : ℕ) : Tor N C (n + 1) →ₗ[R] Tor N A n :=
    { toFun := fun x => δ n x
      map_add' := fun x y => (δ n).map_add x y
      map_smul' := P103.Ch11.TorExactSequences.connecting_linear.2
        R B P A M C f g hf he hg n (torMaps (n + 1)) (torMaps n) (δ n) (hδ n).1 }
  have hfun (n : ℕ) : (⇑(δ' n) : Tor N C (n + 1) → Tor N A n) = ⇑(δ n) := rfl
  refine ⟨δ', ?_, ?_, ?_, ?_⟩
  · intro n
    have h (k : ℕ) : Function.Exact
        (homologyMap (tensorSecondMap P.val.complex f.hom) k)
        (homologyMap (tensorSecondMap P.val.complex g.hom) k) :=
      match k with
      | 0 => hzero
      | k + 1 => (hδ k).2.1
    have hexact := h n
    rw [← hmap f n, ← hmap g n] at hexact
    exact hexact
  · intro n
    have hexact := (hδ n).2.2.1
    rw [← hmap g (n + 1), ← hfun n] at hexact
    exact hexact
  · intro n
    have hexact := (hδ n).2.2.2
    rw [← hfun n, ← hmap f n] at hexact
    exact hexact
  · rw [← hmap g 0] at hsurj
    exact hsurj

private abbrev lengthInt (R : Type*) [CommRing R] (X : Type*) [AddCommGroup X] [Module R X] : ℤ :=
  (Module.length R X).toNat

private theorem lengthInt_eq_ker_add_range {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Module R X] [Module R Y] (f : X →ₗ[R] Y) (hX : IsFiniteLength R X) :
    lengthInt R X = lengthInt R (LinearMap.ker f) + lengthInt R (LinearMap.range f) := by
  have h := Module.length_eq_add_of_exact (LinearMap.ker f.rangeRestrict).subtype
    f.rangeRestrict (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_subtype_ker_map f.rangeRestrict)
  rw [LinearMap.ker_rangeRestrict] at h
  have hk : IsFiniteLength R (LinearMap.ker f) :=
    hX.of_injective (Submodule.subtype_injective _)
  have hr : IsFiniteLength R (LinearMap.range f) := hX.of_surjective f.surjective_rangeRestrict
  unfold lengthInt
  rw [h, ENat.toNat_add (Module.length_ne_top_iff.mpr hk) (Module.length_ne_top_iff.mpr hr),
    Nat.cast_add]

private theorem lengthInt_eq_range_add_range {X Y Z : Type*}
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    {f : X →ₗ[R] Y} {g : Y →ₗ[R] Z} (h : Function.Exact f g) (hY : IsFiniteLength R Y) :
    lengthInt R Y = lengthInt R (LinearMap.range f) + lengthInt R (LinearMap.range g) := by
  rw [lengthInt_eq_ker_add_range g hY, ← LinearMap.exact_iff.mp h]

/-- Summing the three length identities in each degree leaves only the image
of the connecting map into the last degree. -/
private theorem sum_alternating_length (a b c x y z : ℕ → ℤ)
    (ha : ∀ n, a n = z n + x n) (hb : ∀ n, b n = x n + y n)
    (hc₀ : c 0 = y 0) (hc : ∀ n, c (n + 1) = y (n + 1) + z n)
    (d : ℕ) :
    (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (a n - b n + c n)) =
      (-1 : ℤ) ^ d * z d := by
  induction d with
  | zero =>
    simp [ha, hb, hc₀]
    ring
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, ha, hb, hc, pow_succ]
    ring

/-- The isolated-intersection Euler characteristic is additive in its second argument. -/
theorem intersectionEuler_add_right : Specs.addRight.{u,v,w} := by
  intro R _ _ A M C N _ _ _ _ f g hf he hg hA hM hC
  let I (n : ℕ) : Tor N A n →ₗ[R] Tor N M n :=
    torMapLinear R n (𝟙 ((commRightFunctor R).obj N)) (ModuleCat.ofHom f)
  let P (n : ℕ) : Tor N M n →ₗ[R] Tor N C n :=
    torMapLinear R n (𝟙 ((commRightFunctor R).obj N)) (ModuleCat.ofHom g)
  obtain ⟨δ, hIP, hPδ, hδI, hP₀⟩ :=
    tor_long_exact_second A M C N (ModuleCat.ofHom f) (ModuleCat.ofHom g) hf he hg
  change (∀ n, Function.Exact (I n) (P n)) at hIP
  change (∀ n, Function.Exact (P (n + 1)) (δ n)) at hPδ
  change (∀ n, Function.Exact (δ n) (I n)) at hδI
  change Function.Surjective (P 0) at hP₀
  let d := regularLocalDimension R
  let a (n : ℕ) := lengthInt R (Tor N A n)
  let b (n : ℕ) := lengthInt R (Tor N M n)
  let c (n : ℕ) := lengthInt R (Tor N C n)
  let x (n : ℕ) := lengthInt R (LinearMap.range (I n))
  let y (n : ℕ) := lengthInt R (LinearMap.range (P n))
  let z (n : ℕ) := lengthInt R (LinearMap.range (δ n))
  have hfiniteA := IsolatedTorSupport.tor_finite_length N A hA
  have hfiniteM := IsolatedTorSupport.tor_finite_length N M hM
  have hfiniteC := IsolatedTorSupport.tor_finite_length N C hC
  have ha (n : ℕ) : a n = z n + x n :=
    lengthInt_eq_range_add_range (hδI n) (hfiniteA n)
  have hb (n : ℕ) : b n = x n + y n :=
    lengthInt_eq_range_add_range (hIP n) (hfiniteM n)
  have hc (n : ℕ) : c (n + 1) = y (n + 1) + z n :=
    lengthInt_eq_range_add_range (hPδ n) (hfiniteC (n + 1))
  have hc₀ : c 0 = y 0 := by
    change lengthInt R (Tor N C 0) = lengthInt R (LinearMap.range (P 0))
    have h := congrArg (fun S : Submodule R (Tor N C 0) => Module.length R S)
      (LinearMap.range_eq_top.mpr hP₀)
    exact congrArg (fun l : ℕ∞ => (l.toNat : ℤ)) (h.trans Module.length_top).symm
  have hz : z d = 0 := by
    have : Subsingleton (Tor N C (d + 1)) := tor_vanishes_above N C d
      (ringKrullDim_eq_regularLocalDimension R) (d + 1) (Nat.lt_succ_self d)
    have : Subsingleton (LinearMap.range (δ d)) := (δ d).surjective_rangeRestrict.subsingleton
    change lengthInt R (LinearMap.range (δ d)) = 0
    simp only [lengthInt, Module.length_eq_zero, ENat.toNat_zero, Nat.cast_zero]
  have hsum := sum_alternating_length a b c x y z ha hb hc₀ hc d
  rw [hz, mul_zero] at hsum
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  change (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * b n) =
    (∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * a n) +
      ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * c n
  omega

/-- The isolated-intersection Euler characteristic is additive in its first argument. -/
theorem intersectionEuler_add_left : Specs.addLeft.{u,v,w} := by
  intro R _ _ A M C N _ _ _ _ f g hf he hg hA hM hC
  have hsymm (X : ModuleCat.{v} R) : intersectionEuler X N = intersectionEuler N X :=
    cutoffEuler_symm X N (regularLocalDimension R)
  rw [hsymm M, hsymm A, hsymm C]
  exact intersectionEuler_add_right A M C N f g hf he hg
    (by simpa only [Set.inter_comm] using hA)
    (by simpa only [Set.inter_comm] using hM)
    (by simpa only [Set.inter_comm] using hC)

end CommutativeAlgebraNotes.Intersection.IntersectionEulerAdditivity
