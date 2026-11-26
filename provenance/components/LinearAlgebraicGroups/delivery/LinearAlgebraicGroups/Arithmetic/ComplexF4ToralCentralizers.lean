import Specs.LinearAlgebraicGroups.Arithmetic.ComplexF4ToralCentralizers
import LinearAlgebraicGroups.Flag.BruhatCells
import LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import Mathlib.Analysis.Complex.Convex
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology Module
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Matrix

universe u v w

namespace LinearAlgebraicGroups.Arithmetic.ComplexF4ToralCentralizers

open LinearAlgebraicGroups.Specs
open Specs.AbsoluteDynkinTypes (HasDynkinType)
open Specs.Pinning (AttachedDatum SplitBorelPair)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.SimplyConnectedLattice (corootLattice)
open RootData (integralCartan)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- A full-rank F₄ coroot lattice equals the ambient cocharacter lattice. -/
theorem f4_coroot_span_eq_top
    {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : _root_.RootDatum I X Y) (B : P.Base)
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range P.coroot)) = finrank ℤ Y)
    (hF : HasDynkinType (integralCartan P B) .F4) :
    Submodule.span ℤ (Set.range P.coroot) = ⊤ := by
  classical
  obtain ⟨e, he⟩ := hF
  change B.support ≃ Fin 4 at e
  change ∀ i j, integralCartan P B i j = CartanMatrix.F₄ (e i) (e j) at he
  let a (j : Fin 4) := P.root (e.symm j).val
  let c (j : Fin 4) := P.coroot (e.symm j).val
  let f : Y →ₗ[ℤ] (Fin 4 → ℤ) := LinearMap.pi fun j => P.toLinearMap (a j)
  have hcartan (i j : Fin 4) : f (c i) j = CartanMatrix.F₄ i j := by
    change integralCartan P B (e.symm i) (e.symm j) = _
    simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
  have hsum (u : Fin 4 → ℤ) : f (∑ i, u i • c i) = u ᵥ* CartanMatrix.F₄ := by
    rw [map_sum, Matrix.vecMul_eq_sum]
    simp only [map_smul, show ∀ i, f (c i) = CartanMatrix.F₄ i from fun i => funext (hcartan i)]
  let C : Matrix (Fin 4) (Fin 4) ℤ := CartanMatrix.F₄
  have hC : IsUnit C.det := CartanMatrix.F₄_det ▸ isUnit_one
  have hf : Function.Surjective f := by
    intro z
    refine ⟨∑ i, (z ᵥ* C⁻¹) i • c i, ?_⟩
    rw [hsum]
    change (z ᵥ* C⁻¹) ᵥ* C = z
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hC, Matrix.vecMul_one]
  have hY : finrank ℤ Y = 4 := by
    have hset : Set.range c = P.coroot '' (B.support : Set I) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨_, (e.symm j).property, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨e ⟨j, hj⟩, congrArg (fun i : B.support => P.coroot i.val) (e.symm_apply_apply ⟨j,hj⟩)⟩
    rw [← hfull, ← B.span_int_coroot_support, ← hset]
    have hind : LinearIndependent ℤ c := B.linearIndepOn_coroot.comp e.symm e.symm.injective
    rw [finrank_span_eq_card hind, Fintype.card_fin]
  have hker : f.ker = ⊥ := by
    have hr : (⊤ : Submodule ℤ Y).map f = ⊤ := by
      rw [Submodule.map_top, LinearMap.range_eq_top]
      exact hf
    have hle : finrank ℤ (⊤ : Submodule ℤ Y) ≤ finrank ℤ ((⊤ : Submodule ℤ Y).map f) := by
      rw [hr, finrank_top, finrank_top, hY, finrank_fin_fun]
    simpa using Submodule.disjoint_ker_of_finrank_le f hle
  apply eq_top_iff.mpr
  intro y _
  let z := f y ᵥ* C⁻¹
  have hz : f (∑ i, z i • c i) = f y := by
    rw [hsum]
    change (f y ᵥ* C⁻¹) ᵥ* C = f y
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hC, Matrix.vecMul_one]
  rw [← (LinearMap.ker_eq_bot.mp hker) hz]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- In a full-rank root datum of type F₄ the roots generate the entire
character lattice. This is the character-lattice counterpart of the coroot
span calculation. -/
theorem f4_root_span_eq_top
    {I : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
    [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : _root_.RootDatum I X Y) (B : P.Base)
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range P.coroot)) = finrank ℤ Y)
    (hF : HasDynkinType (integralCartan P B) .F4) :
    Submodule.span ℤ (Set.range P.root) = ⊤ := by
  classical
  have hcoroot := f4_coroot_span_eq_top P B hfull hF
  obtain ⟨e, he⟩ := hF
  change B.support ≃ Fin 4 at e
  change ∀ i j, integralCartan P B i j = CartanMatrix.F₄ (e i) (e j) at he
  let a (j : Fin 4) := P.root (e.symm j).val
  let c (j : Fin 4) := P.coroot (e.symm j).val
  let f : X →ₗ[ℤ] (Fin 4 → ℤ) := LinearMap.pi fun i => P.toLinearMap.flip (c i)
  have hc (i j : Fin 4) : f (a j) i = CartanMatrix.F₄ i j := by
    change integralCartan P B (e.symm i) (e.symm j) = _
    simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
  have hsum (z : Fin 4 → ℤ) : f (∑ j, z j • a j) = CartanMatrix.F₄ *ᵥ z := by
    ext i
    rw [map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, Matrix.mulVec,
      dotProduct, mul_comm]
  have hC : IsUnit CartanMatrix.F₄.det := CartanMatrix.F₄_det ▸ isUnit_one
  apply eq_top_iff.mpr
  intro x _
  let z := CartanMatrix.F₄⁻¹ *ᵥ f x
  have hz : f (∑ j, z j • a j) = f x := by
    rw [hsum]
    change CartanMatrix.F₄ *ᵥ (CartanMatrix.F₄⁻¹ *ᵥ f x) = f x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hC, Matrix.one_mulVec]
  have hinj : Function.Injective f := by
    intro x y hxy
    apply P.toPerfPair.injective
    apply LinearMap.ext_on (s := P.coroot '' (B.support : Set I)) (by
      rw [B.span_int_coroot_support, hcoroot])
    rintro _ ⟨i, hi, rfl⟩
    have h := congrFun hxy (e ⟨i, hi⟩)
    change P.toLinearMap x (c (e ⟨i, hi⟩)) = P.toLinearMap y (c (e ⟨i, hi⟩)) at h
    change P.toLinearMap x (P.coroot i) = P.toLinearMap y (P.coroot i)
    simpa only [c, Equiv.symm_apply_apply] using h
  rw [← hinj hz]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-- The action on simple-root coordinates of reflection in simple root `i`.
The row of the Cartan matrix pairs the roots with coroot `i`. -/
def f4SimpleReflectionMatrix (i : Fin 4) : Matrix (Fin 4) (Fin 4) ℤ :=
  fun a j => (if a = j then 1 else 0) - (if a = i then CartanMatrix.F₄ i j else 0)

/-- The right action on binary characters of the root lattice. The binary
characters encode evaluation at order-dividing-two elements of the torus. -/
def f4SignAction (b : Fin 4 → ZMod 2) (M : Matrix (Fin 4) (Fin 4) ℤ) :
    Fin 4 → ZMod 2 := b ᵥ* M.map (Int.castRingHom (ZMod 2))

private theorem f4SignAction_one (b : Fin 4 → ZMod 2) : f4SignAction b 1 = b := by
  simp [f4SignAction]

private theorem f4SignAction_mul (b : Fin 4 → ZMod 2) (M N : Matrix (Fin 4) (Fin 4) ℤ) :
    f4SignAction b (M * N) = f4SignAction (f4SignAction b M) N := by
  unfold f4SignAction
  rw [Matrix.map_mul (f := Int.castRingHom (ZMod 2)), Matrix.vecMul_vecMul]

private def f4Color (c : Fin 16) : Fin 4 → ZMod 2 :=
  fun j => if c.val.testBit j.val then 1 else 0

private theorem f4Color_bijective : Function.Bijective f4Color := by decide +kernel

private def f4OrbitBase : Fin 16 → Fin 16 := ![0, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4]

/-- Words taking the orbit representative to the designated binary character. -/
private def f4Transversal : Fin 16 → List (Fin 4) :=
  ![[], [], [0, 1], [0], [], [2, 1, 2], [2, 1, 0, 2, 1], [2, 1, 0, 2],
    [2, 1, 0, 2, 1, 2, 3], [2, 1, 0, 3], [2, 3], [2, 1, 3], [2, 1, 0, 2, 1, 2],
    [2, 1, 0], [2], [2, 1]]

/-- A nontrivial transition is a conjugate of the indicated simple reflection.
The conjugating word is written in the same convention as the transversal. -/
private def f4TransitionReflection : Fin 16 → Fin 4 → Option (Fin 4 × List (Fin 4)) :=
  ![![some (0, []), some (1, []), some (2, []), some (3, [])],
    ![none, some (1, []), some (2, []), some (3, [])],
    ![some (1, []), none, some (2, [0, 1]), some (3, [])],
    ![none, none, some (2, []), some (3, [])],
    ![some (0, []), some (1, []), none, some (3, [])],
    ![none, some (1, []), none, some (3, [2, 1, 2])],
    ![some (1, []), none, none, some (3, [2, 1, 2])],
    ![none, none, none, some (3, [2, 1, 2])],
    ![some (1, []), some (0, []), some (3, [2, 1, 2]), none],
    ![none, some (0, []), some (3, [2, 1, 2]), none],
    ![some (0, []), none, some (3, []), none],
    ![none, none, some (3, [2, 1, 2]), none],
    ![some (1, []), some (0, []), none, none],
    ![none, some (0, []), none, none],
    ![some (0, []), none, none, none],
    ![none, none, none, none]]

private def f4WordMatrix (w : List (Fin 4)) : Matrix (Fin 4) (Fin 4) ℤ :=
  (w.map f4SimpleReflectionMatrix).prod

private def f4NextColor (c : Fin 16) (i : Fin 4) : Fin 16 :=
  ⟨∑ j : Fin 4, if f4SignAction (f4Color c) (f4SimpleReflectionMatrix i) j = 0
    then 0 else 2 ^ j.val, by
      have hle : (∑ j : Fin 4, if f4SignAction (f4Color c) (f4SimpleReflectionMatrix i) j = 0
        then 0 else 2 ^ j.val) ≤ ∑ j : Fin 4, 2 ^ j.val :=
        Finset.sum_le_sum fun j _ => by split <;> simp
      exact lt_of_le_of_lt hle (by decide)⟩

private theorem f4SimpleReflectionMatrix_sq (i : Fin 4) :
    f4SimpleReflectionMatrix i * f4SimpleReflectionMatrix i = 1 := by
  revert i
  decide +kernel

private theorem f4Transversal_base : ∀ c : Fin 16,
    f4OrbitBase (f4OrbitBase c) = f4OrbitBase c ∧ f4Transversal (f4OrbitBase c) = [] := by
  decide +kernel

private theorem f4Transversal_action : ∀ c : Fin 16,
    f4SignAction (f4Color (f4OrbitBase c)) (f4WordMatrix (f4Transversal c)) = f4Color c := by
  decide +kernel

private theorem f4NextColor_action : ∀ (c : Fin 16) (i : Fin 4),
    f4OrbitBase (f4NextColor c i) = f4OrbitBase c ∧
    f4Color (f4NextColor c i) = f4SignAction (f4Color c) (f4SimpleReflectionMatrix i) := by
  decide +kernel

private def f4TransitionValid (p : Option (Fin 4 × List (Fin 4)))
    (M : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin 4 → ZMod 2) : Prop :=
  match p with
  | none => M = 1
  | some (j, w) => M = f4WordMatrix (w ++ [j] ++ w.reverse) ∧
      f4SignAction b (f4WordMatrix w) j = 0

private instance (p : Option (Fin 4 × List (Fin 4)))
    (M : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin 4 → ZMod 2) :
    Decidable (f4TransitionValid p M b) := by
  cases p with
  | none => dsimp [f4TransitionValid]; infer_instance
  | some q => rcases q with ⟨i, w⟩; dsimp [f4TransitionValid]; infer_instance

private def f4TransitionAt (c : Fin 16) (i : Fin 4) : Prop :=
  let d := f4NextColor c i
  let M := f4WordMatrix (f4Transversal c ++ [i] ++ (f4Transversal d).reverse)
  f4TransitionValid (f4TransitionReflection c i) M (f4Color (f4OrbitBase c))

private instance (c : Fin 16) (i : Fin 4) : Decidable (f4TransitionAt c i) := by
  unfold f4TransitionAt
  dsimp only
  infer_instance

private theorem f4Transition_row0 : ∀ i, f4TransitionAt 0 i := by
  decide +kernel

private theorem f4Transition_row1 : ∀ i, f4TransitionAt 1 i := by
  decide +kernel

private theorem f4Transition_row2 : ∀ i, f4TransitionAt 2 i := by
  decide +kernel

private theorem f4Transition_row3 : ∀ i, f4TransitionAt 3 i := by
  decide +kernel

private theorem f4Transition_row4 : ∀ i, f4TransitionAt 4 i := by
  decide +kernel

private theorem f4Transition_row5 : ∀ i, f4TransitionAt 5 i := by
  decide +kernel

private theorem f4Transition_row6 : ∀ i, f4TransitionAt 6 i := by
  decide +kernel

private theorem f4Transition_row7 : ∀ i, f4TransitionAt 7 i := by
  decide +kernel

private theorem f4Transition_row8 : ∀ i, f4TransitionAt 8 i := by
  decide +kernel

private theorem f4Transition_row9 : ∀ i, f4TransitionAt 9 i := by
  decide +kernel

private theorem f4Transition_row10 : ∀ i, f4TransitionAt 10 i := by
  decide +kernel

private theorem f4Transition_row11 : ∀ i, f4TransitionAt 11 i := by
  decide +kernel

private theorem f4Transition_row12 : ∀ i, f4TransitionAt 12 i := by
  decide +kernel

private theorem f4Transition_row13 : ∀ i, f4TransitionAt 13 i := by
  decide +kernel

private theorem f4Transition_row14 : ∀ i, f4TransitionAt 14 i := by
  decide +kernel

private theorem f4Transition_row15 : ∀ i, f4TransitionAt 15 i := by
  decide +kernel

/-- Each row checks the products by a simple reflection at a given sign
character. The arbitrary word equality then follows by subgroup induction. -/
private theorem f4Transition_certificate (c : Fin 16) (i : Fin 4) :
    f4TransitionAt c i := by
  fin_cases c
  · exact f4Transition_row0 i
  · exact f4Transition_row1 i
  · exact f4Transition_row2 i
  · exact f4Transition_row3 i
  · exact f4Transition_row4 i
  · exact f4Transition_row5 i
  · exact f4Transition_row6 i
  · exact f4Transition_row7 i
  · exact f4Transition_row8 i
  · exact f4Transition_row9 i
  · exact f4Transition_row10 i
  · exact f4Transition_row11 i
  · exact f4Transition_row12 i
  · exact f4Transition_row13 i
  · exact f4Transition_row14 i
  · exact f4Transition_row15 i

private def reflectionWord {W : Type*} [Group W] (s : Fin 4 → W) (w : List (Fin 4)) : W :=
  (w.map s).prod

private theorem reflectionWord_append {W : Type*} [Group W] (s : Fin 4 → W)
    (a b : List (Fin 4)) : reflectionWord s (a ++ b) = reflectionWord s a * reflectionWord s b := by
  simp [reflectionWord]

private theorem reflectionWord_conj {W : Type*} [Group W] (s : Fin 4 → W)
    (h : ∀ i, (s i)⁻¹ = s i) (a b : List (Fin 4)) (i : Fin 4) :
    reflectionWord s (a ++ [i] ++ b.reverse) = reflectionWord s a * s i * (reflectionWord s b)⁻¹ := by
  rw [reflectionWord_append, reflectionWord_append]
  show (reflectionWord s a * (s i * 1)) * (b.reverse.map s).prod = _
  simp only [List.map_reverse, mul_one, reflectionWord, List.prod_inv_reverse, List.map_map,
    Function.comp_def, h]

/-- A torus sign character in type `F₄` has Weyl stabilizer generated by
the reflections in its roots of sign `+1`. A conjugate of a simple
reflection is recorded by its conjugating Weyl element and simple label. -/
theorem f4_sign_stabilizer_generated {W : Type*} [Group W]
    (s : Fin 4 → W) (M : W →* Matrix (Fin 4) (Fin 4) ℤ) (hM : Function.Injective M)
    (hs : ∀ i, M (s i) = f4SimpleReflectionMatrix i) (hgen : Subgroup.closure (Set.range s) = ⊤)
    (b : Fin 4 → ZMod 2) (w : W) (hw : f4SignAction b (M w) = b) :
    w ∈ Subgroup.closure {g | ∃ (t : W) (i : Fin 4),
      g = t * s i * t⁻¹ ∧ f4SignAction b (M t) i = 0} := by
  have hi (i : Fin 4) : (s i)⁻¹ = s i := by
    apply inv_eq_of_mul_eq_one_right
    apply hM
    rw [map_mul, hs, map_one]
    exact f4SimpleReflectionMatrix_sq i
  have hword (a : List (Fin 4)) : M (reflectionWord s a) = f4WordMatrix a := by
    simp only [reflectionWord, f4WordMatrix, map_list_prod, List.map_map, Function.comp_def, hs]
  let generators (d : Fin 4 → ZMod 2) : Set W := {g | ∃ (t : W) (i : Fin 4),
    g = t * s i * t⁻¹ ∧ f4SignAction d (M t) i = 0}
  let N (d : Fin 4 → ZMod 2) := Subgroup.closure (generators d)
  have hfix (d : Fin 4 → ZMod 2) (u : W) (hu : u ∈ N d) : f4SignAction d (M u) = d := by
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨t, i, rfl, ht⟩
      rw [map_mul, map_mul, f4SignAction_mul, f4SignAction_mul, hs]
      have hsimple : f4SignAction (f4SignAction d (M t)) (f4SimpleReflectionMatrix i) =
          f4SignAction d (M t) := by
        let e := f4SignAction d (M t)
        ext j
        change (∑ k, e k * ((f4SimpleReflectionMatrix i k j : ℤ) : ZMod 2)) = e j
        have hterm (k : Fin 4) : e k * ((f4SimpleReflectionMatrix i k j : ℤ) : ZMod 2) =
            if k = j then e k else 0 := by
          by_cases hki : k = i
          · subst k; simp [show e i = 0 from ht]
          · by_cases hkj : k = j
            · subst j; simp [f4SimpleReflectionMatrix, hki]
            · simp [f4SimpleReflectionMatrix, hki, hkj]
        simp [hterm]
      rw [hsimple, ← f4SignAction_mul, ← map_mul, mul_inv_cancel, map_one, f4SignAction_one]
    · rw [map_one, f4SignAction_one]
    · intro x y _ _ hx hy
      rw [map_mul, f4SignAction_mul, hx, hy]
    · intro x _ hx
      conv_lhs => rw [← hx]
      rw [← f4SignAction_mul, ← map_mul, mul_inv_cancel, map_one, f4SignAction_one]
  have hcoset (c : Fin 16) (i : Fin 4) :
      reflectionWord s (f4Transversal c) * s i * (reflectionWord s (f4Transversal (f4NextColor c i)))⁻¹ ∈
        N (f4Color (f4OrbitBase c)) := by
    rw [← reflectionWord_conj s hi]
    have h := f4Transition_certificate c i
    unfold f4TransitionAt at h
    dsimp only at h
    cases hcase : f4TransitionReflection c i with
    | none =>
      simp only [hcase, f4TransitionValid] at h
      have he : reflectionWord s (f4Transversal c ++ [i] ++
          (f4Transversal (f4NextColor c i)).reverse) = 1 := hM (by rw [hword, map_one]; exact h)
      rw [he]
      exact (N _).one_mem
    | some p =>
      obtain ⟨j, a⟩ := p
      simp only [hcase, f4TransitionValid] at h
      have he : reflectionWord s (f4Transversal c ++ [i] ++
          (f4Transversal (f4NextColor c i)).reverse) = reflectionWord s (a ++ [j] ++ a.reverse) :=
        hM (by rw [hword, hword]; exact h.1)
      rw [he, reflectionWord_conj s hi]
      exact Subgroup.subset_closure ⟨reflectionWord s a, j, rfl, by rw [hword]; exact h.2⟩
  have hbase (c : Fin 16) (x : W) (hx : f4SignAction (f4Color (f4OrbitBase c)) (M x) =
      f4Color (f4OrbitBase c)) : x ∈ N (f4Color (f4OrbitBase c)) := by
    let m := f4OrbitBase c
    let H := N (f4Color m)
    have hdecomp : ∃ d : Fin 16, f4OrbitBase d = m ∧ x * (reflectionWord s (f4Transversal d))⁻¹ ∈ H := by
      have hmem : x ∈ Subgroup.closure (Set.range s) := hgen ▸ Subgroup.mem_top x
      have hstep (y : W) (i : Fin 4)
          (hy : ∃ d : Fin 16, f4OrbitBase d = m ∧ y * (reflectionWord s (f4Transversal d))⁻¹ ∈ H) :
          ∃ d : Fin 16, f4OrbitBase d = m ∧ (y * s i) * (reflectionWord s (f4Transversal d))⁻¹ ∈ H := by
        obtain ⟨d, hd, hy⟩ := hy
        have hdi := hcoset d i
        rw [hd] at hdi
        refine ⟨f4NextColor d i, (f4NextColor_action d i).1.trans hd, ?_⟩
        have hp := H.mul_mem hy hdi
        simpa only [mul_assoc, inv_mul_cancel_left] using hp
      refine Subgroup.closure_induction_right (p := fun y _ => ∃ d : Fin 16,
        f4OrbitBase d = m ∧ y * (reflectionWord s (f4Transversal d))⁻¹ ∈ H) ?_ ?_ ?_ hmem
      · exact ⟨m, (f4Transversal_base c).1, by
          rw [(f4Transversal_base c).2]; simp [reflectionWord]⟩
      · intro y _ u hu hy
        obtain ⟨i, rfl⟩ := hu
        exact hstep y i hy
      · intro y _ u hu hy
        obtain ⟨i, rfl⟩ := hu
        rw [hi]
        exact hstep y i hy
    obtain ⟨d, hd, hxd⟩ := hdecomp
    have hfactor : x = (x * (reflectionWord s (f4Transversal d))⁻¹) *
      reflectionWord s (f4Transversal d) := by simp
    have hh := hfix _ _ hxd
    have hdcolor : f4SignAction (f4Color m) (M x) = f4Color d := by
      conv_lhs => rw [hfactor]
      rw [map_mul, f4SignAction_mul, hh, hword, ← hd, f4Transversal_action]
    have hdm : d = m := f4Color_bijective.injective (hdcolor.symm.trans hx)
    subst d
    rwa [(f4Transversal_base c).2, show reflectionWord s [] = 1 from rfl, inv_one, mul_one] at hxd
  obtain ⟨c, rfl⟩ := f4Color_bijective.surjective b
  let t := reflectionWord s (f4Transversal c)
  let d := f4Color (f4OrbitBase c)
  have htd : f4SignAction d (M t) = f4Color c := (hword _).symm ▸ f4Transversal_action c
  have hti : f4SignAction (f4Color c) (M t⁻¹) = d := by
    rw [← htd, ← f4SignAction_mul, ← map_mul, mul_inv_cancel, map_one, f4SignAction_one]
  have hwt : t * w * t⁻¹ ∈ N d := hbase c _ (by
    rw [map_mul, map_mul, f4SignAction_mul, f4SignAction_mul, htd, hw, hti])
  let conj : W →* W := (MulAut.conj t⁻¹).toMonoidHom
  have hle : N d ≤ (N (f4Color c)).comap conj := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, i, rfl, hai⟩
    change t⁻¹ * (a * s i * a⁻¹) * (t⁻¹)⁻¹ ∈ N (f4Color c)
    apply Subgroup.subset_closure
    refine ⟨t⁻¹ * a, i, by simp [mul_assoc], ?_⟩
    rwa [map_mul, f4SignAction_mul, hti]
  have hu := hle hwt
  change t⁻¹ * (t * w * t⁻¹) * (t⁻¹)⁻¹ ∈ N (f4Color c) at hu
  change w ∈ N (f4Color c)
  simpa [mul_assoc] using hu


private theorem conjugate_root_reflection
    {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : _root_.RootDatum I X Y) (w : P.weylGroup) (i : I) :
    RootPairing.weylGroup.ofIdx P (w.val.indexEquiv i) =
      w * RootPairing.weylGroup.ofIdx P i * w⁻¹ := by
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  have h := congrArg (fun f : Module.End ℤ X => f (w.val.weightEquiv.symm x))
    (w.val.weightEquiv_symm_conj_reflection i)
  change w.val.weightEquiv.symm
      (P.reflection (w.val.indexEquiv i) (w.val.weightEquiv (w.val.weightEquiv.symm x))) =
    P.reflection i (w.val.weightEquiv.symm x) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change (RootPairing.Equiv.weightHom P (RootPairing.Equiv.reflection P _)) x =
    (RootPairing.Equiv.weightHom P
      (w.val * RootPairing.Equiv.reflection P i * w.val⁻¹)) x
  simp only [map_mul, map_inv, LinearEquiv.mul_apply, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.reflection_weightEquiv]
  exact w.val.weightEquiv.symm.injective (by simpa using h)

private theorem simple_reflections_generate
    {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite I]
    (P : _root_.RootDatum I X Y) [P.IsReduced] (B : P.Base)
    (e : B.support ≃ Fin 4) :
    Subgroup.closure (Set.range fun j : Fin 4 => RootPairing.weylGroup.ofIdx P (e.symm j).val) =
      ⊤ := by
  classical
  let s := RootPairing.weylGroup.ofIdx P
  let H := Subgroup.closure (Set.range fun j : Fin 4 => s (e.symm j).val)
  have hsimple (i : I) (hi : i ∈ B.support) : s i ∈ H := by
    apply Subgroup.subset_closure
    exact ⟨e ⟨i, hi⟩, congrArg (fun a : B.support => s a.val) (e.symm_apply_apply _)⟩
  have hroots (i : I) : s i ∈ H := by
    refine B.induction_reflect i (p := fun i => s i ∈ H) ?_ hsimple ?_
    · intro a ha
      have h := conjugate_root_reflection P (s a) a
      change s (P.reflectionPerm a a) = _ at h
      rw [h]
      exact H.mul_mem (H.mul_mem ha ha) (H.inv_mem ha)
    · intro a j ha hj
      have h := conjugate_root_reflection P (s j) a
      change s (P.reflectionPerm j a) = _ at h
      rw [h]
      exact H.mul_mem (H.mul_mem (hsimple j hj) ha) (H.inv_mem (hsimple j hj))
  apply top_unique
  intro w _
  exact RootPairing.weylGroup.induction P (pred := fun w hw => (⟨w, hw⟩ : P.weylGroup) ∈ H)
    hroots H.one_mem (fun _ _ _ _ => H.mul_mem) w.property

/-- The stabilizer of an additive sign character is generated by the
reflections in roots on which the sign character vanishes. -/
private theorem weyl_stabilizer_mem_closure
    {I X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite I] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (P : _root_.RootDatum I X Y) [P.IsReduced] (B : P.Base)
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range P.coroot)) = finrank ℤ Y)
    (hF : HasDynkinType (integralCartan P B) .F4)
    (χ : X →+ ZMod 2) (w : P.weylGroup)
    (hw : ∀ x, χ (w.val.weightEquiv x) = χ x) :
    w ∈ Subgroup.closure (RootPairing.weylGroup.ofIdx P '' {i | χ (P.root i) = 0}) := by
  classical
  have hspan := f4_root_span_eq_top P B hfull hF
  obtain ⟨e, he⟩ := hF
  change B.support ≃ Fin 4 at e
  change ∀ i j, integralCartan P B i j = CartanMatrix.F₄ (e i) (e j) at he
  let a : Fin 4 → X := fun j => P.root (e.symm j).val
  have ha : Set.range a = P.root '' (B.support : Set I) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, (e.symm j).property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e ⟨j, hj⟩, congrArg (fun i : B.support => P.root i.val) (e.symm_apply_apply _)⟩
  let b : Module.Basis (Fin 4) ℤ X := Module.Basis.mk
    (B.linearIndepOn_root.comp e.symm e.symm.injective)
    (by change ⊤ ≤ Submodule.span ℤ (Set.range a); rw [ha, B.span_int_root_support, hspan])
  have hb (j : Fin 4) : b j = a j := Module.Basis.mk_apply _ _ _
  let ρ : P.weylGroup →* Module.End ℤ X :=
    { toFun := fun g => g.val.weightEquiv.toLinearMap
      map_one' := rfl
      map_mul' := fun x y => rfl }
  let M : P.weylGroup →* Matrix (Fin 4) (Fin 4) ℤ :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp ρ
  have hM : Function.Injective M := by
    intro x y h
    apply Subtype.ext
    apply RootPairing.Equiv.weightHom_injective P
    apply LinearEquiv.ext
    intro z
    exact LinearMap.congr_fun ((LinearMap.toMatrixAlgEquiv b).injective h) z
  let s := fun j : Fin 4 => RootPairing.weylGroup.ofIdx P (e.symm j).val
  have hs (i : Fin 4) : M (s i) = f4SimpleReflectionMatrix i := by
    ext k j
    change LinearMap.toMatrix b b (ρ (s i)) k j = _
    rw [LinearMap.toMatrix_apply, hb j]
    change b.repr ((RootPairing.Equiv.reflection P (e.symm i).val).weightEquiv (a j)) k = _
    rw [RootPairing.Equiv.reflection_weightEquiv, P.reflection_apply]
    have hcartan : P.coroot' (e.symm i).val (a j) = CartanMatrix.F₄ i j := by
      change integralCartan P B (e.symm i) (e.symm j) = _
      simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
    rw [hcartan]
    change b.repr (a j - CartanMatrix.F₄ i j • a i) k = _
    rw [← hb j, ← hb i]
    simp [f4SimpleReflectionMatrix, Finsupp.single_apply, eq_comm]
  let color (j : Fin 4) := χ (b j)
  have hcolor (g : P.weylGroup) (j : Fin 4) :
      f4SignAction color (M g) j = χ (g.val.weightEquiv (b j)) := by
    conv_rhs => rw [← b.sum_repr (g.val.weightEquiv (b j))]
    change (∑ i, color i * ((LinearMap.toMatrix b b (ρ g) i j : ℤ) : ZMod 2)) = _
    simp only [map_sum, AddMonoidHom.map_zsmul, LinearMap.toMatrix_apply, zsmul_eq_mul, color]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hw' : f4SignAction color (M w) = color :=
    funext fun j => (hcolor w j).trans (hw (b j))
  apply (Subgroup.closure_le _).mpr _ (f4_sign_stabilizer_generated s M hM hs
    (simple_reflections_generate P B e) color w hw')
  rintro _ ⟨g, j, rfl, hg⟩
  rw [← conjugate_root_reflection P g (e.symm j).val]
  apply Subgroup.subset_closure
  refine ⟨g.val.indexEquiv (e.symm j).val, ?_, rfl⟩
  change χ (P.root (g.val.indexEquiv (e.symm j).val)) = 0
  rw [← RootPairing.Hom.root_weightMap_apply P P _ g.val.toHom]
  change χ (g.val.weightEquiv (a j)) = 0
  rwa [← hb j, ← hcolor]

open AdelicGroups (PointsIn asMatrix)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.AbstractPairing (Datum Root)
open Specs.CharacterDescent (Character)
open Specs.BruhatOrbitParametrization (Cell IsRepresentative OrderedParametrization)
open Specs.BorelPositivity (RadicalDecomposition)
open Specs.DatumAndWeyl (Identification)
open Specs.IntegralModels (MatrixRealization)
open Specs.OrderedRootProducts (RootSubgroupFamily Enumerates Parametrizes rootProduct)
open Specs.RootGroups (AdditiveLine HasScalarAction rootPoint rankOneWord)
open Specs.CharacterPairing (characterValue)
open private characterEvaluation characterUnit characterUnitOnPoints characterValue_eq_unit
  additivePoints_zero rootPoint_eq rootPoint_comp
  from LinearAlgebraicGroups.RootData.RootGroups
open private pointHom restrictPointHom normalizerLabel
  normalizer_isRepresentative lift_of_range from LinearAlgebraicGroups.Flag.BruhatCells
open private monoSubgroup from LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
open private rootCoordinate_exists
  from LinearAlgebraicGroups.RootData.OrderedRootProducts

local notation "Rℂ" => CommAlgCat.of ℂ ℂ

private def signNumber (z : ℂˣ) : ZMod 2 := if z = 1 then 0 else 1

private theorem signNumber_eq_zero (z : ℂˣ) : signNumber z = 0 ↔ z = 1 := by
  by_cases h : z = 1 <;> simp [signNumber, h]

private theorem signNumber_mul {x y : ℂˣ} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) :
    signNumber (x * y) = signNumber x + signNumber y := by
  have two_values (u : ℂˣ) (hu : u ^ 2 = 1) : u = 1 ∨ u = -1 := by
    have h := congrArg (fun a : ℂˣ => (a : ℂ)) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h
    rw [← one_pow 2, sq_eq_sq_iff_eq_or_eq_neg] at h
    exact h.imp Units.ext (fun h => Units.ext h)
  rcases two_values x hx with rfl | rfl <;> rcases two_values y hy with rfl | rfl <;>
    simp [signNumber, show (1 + 1 : ZMod 2) = 0 by decide]

private def torusSign {T : GroupScheme ℂ} (t : GroupPoints T Rℂ) (ht : t ^ 2 = 1) :
    Additive (Character T) →+ ZMod 2 where
  toFun χ := signNumber (characterUnit χ.toMul Rℂ t)
  map_zero' := by
    change signNumber (characterEvaluation Rℂ t 1) = 0
    simp [signNumber]
  map_add' χ ψ := by
    change signNumber (characterEvaluation Rℂ t (χ.toMul * ψ.toMul)) = _
    rw [map_mul]
    apply signNumber_mul
    all_goals
      change (characterUnitOnPoints _ Rℂ t) ^ 2 = 1
      rw [← map_pow, ht, map_one]

private theorem torusSign_eq_zero {T : GroupScheme ℂ} (t : GroupPoints T Rℂ)
    (ht : t ^ 2 = 1) (χ : Character T) :
    torusSign t ht (Additive.ofMul χ) = 0 ↔ characterValue χ Rℂ t = 1 := by
  change signNumber (characterUnit χ Rℂ t) = 0 ↔ _
  rw [signNumber_eq_zero, characterValue_eq_unit]
  exact ⟨fun h => congrArg Units.val h, fun h => Units.ext h⟩

private def presentedPoint {A : Type} [CommRing A] [Algebra ℂ A]
    {G : AffineAlgebraicGroup ℂ} (i : MatrixRealization G)
    (f : (testSpec ℂ).obj (.op (CommAlgCat.of ℂ A)) ⟶ G.val.X)
    (a : A →ₐ[ℂ] ℂ) : PointsIn i ℂ :=
  (testSpec ℂ).map (CommAlgCat.ofHom a).op ≫ f

private theorem continuous_presentedPoint {X : Type*} {A : Type} [TopologicalSpace X]
    [CommRing A] [Algebra ℂ A] {G : AffineAlgebraicGroup ℂ} (i : MatrixRealization G)
    (f : (testSpec ℂ).obj (.op (CommAlgCat.of ℂ A)) ⟶ G.val.X)
    (a : X → A →ₐ[ℂ] ℂ) (ha : ∀ r, Continuous fun x => a x r) :
    Continuous (fun x => presentedPoint i f (a x)) := by
  let R := CommAlgCat.of ℂ A
  let g : PointsIn i A := f
  let M := asMatrix i A g
  have h (x : X) : asMatrix i ℂ (presentedPoint i f (a x)) =
      Matrix.GeneralLinearGroup.map (a x).toRingHom M := by
    let b : R ⟶ Rℂ := CommAlgCat.ofHom (a x)
    have hn₁ := congrArg (fun m => m g) (((groupPointsFunctor ℂ).map i.embedding).naturality b)
    let hg := (((groupPointsFunctor ℂ).map i.embedding).app R).hom g
    have hn₂ := congrArg (fun m => m hg) (i.matrix.hom.naturality b)
    change (((groupPointsFunctor ℂ).map i.embedding).app Rℂ)
        (presentedPoint i f (a x)) = ((groupPointsFunctor ℂ).obj i.ambient.val).map b hg at hn₁
    change i.matrix.hom.app Rℂ (((groupPointsFunctor ℂ).obj i.ambient.val).map b hg) =
      Matrix.GeneralLinearGroup.map (a x).toRingHom M at hn₂
    exact (congrArg (i.matrix.hom.app Rℂ) hn₁).trans hn₂
  refine (IsInducing.induced (asMatrix i ℂ)).continuous_iff.mpr ?_
  change Continuous fun x => asMatrix i ℂ (presentedPoint i f (a x))
  simp_rw [h]
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun l m => ?_,
      continuous_matrix fun l m => ?_⟩
  · exact ha (M.val l m)
  · exact ha (M⁻¹.val l m)

private def rootMatrixPoint {G : AffineAlgebraicGroup ℂ}
    (i : MatrixRealization G) {A : AdditiveLine ℂ} (x : A.group ⟶ G.val)
    (a : ℂ) : PointsIn i ℂ := rootPoint x Rℂ a

private theorem continuous_rootPoint {G : AffineAlgebraicGroup ℂ}
    (i : MatrixRealization G) {A : AdditiveLine ℂ} (x : A.group ⟶ G.val) :
    Continuous (rootMatrixPoint i x) := by
  change Continuous (fun a : ℂ =>
    presentedPoint i x.hom.hom (Polynomial.aeval a))
  exact continuous_presentedPoint i x.hom.hom Polynomial.aeval fun p => by
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using p.continuous

private def centralizerSubgroup {K : Type*} [Group K] (t : K) : Subgroup K where
  carrier := {g | Commute g t}
  one_mem' := Commute.one_left t
  mul_mem' := fun h₁ h₂ => h₁.mul_left h₂
  inv_mem' := fun h => h.inv_left

private abbrev centralizerComponent {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] (t : K) : Subgroup K :=
  (Subgroup.connectedComponentOfOne (centralizerSubgroup t)).map (centralizerSubgroup t).subtype

private theorem mem_centralizerComponent_of_continuous {K X : Type*}
    [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [TopologicalSpace X] [ConnectedSpace X] {t : K} {f : X → K}
    (hf : Continuous f) (hc : ∀ x, Commute (f x) t) (x₀ : X) (h₀ : f x₀ = 1) (x : X) :
    f x ∈ centralizerComponent t := by
  let g : X → centralizerSubgroup t := fun y =>
    ⟨f y, hc y⟩
  have hg : Continuous g := hf.subtype_mk _
  refine ⟨g x, ?_, rfl⟩
  change g x ∈ connectedComponent (1 : centralizerSubgroup t)
  exact (isConnected_range hg).subset_connectedComponent
    ⟨x₀, Subtype.ext h₀⟩ ⟨x, rfl⟩

private theorem rootPoint_mem_component {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) (t : GroupPoints P.T.group Rℂ)
    {A : AdditiveLine ℂ} {x : A.group ⟶ P.G.val} {χ : Character P.T.group}
    (hx : HasScalarAction P.T χ x) (hχ : characterValue χ Rℂ t = 1) (a : ℂ) :
    (rootPoint x Rℂ a : PointsIn i ℂ) ∈
      centralizerComponent (show PointsIn i ℂ from t ≫ P.T.inclusion.hom.hom) := by
  apply mem_centralizerComponent_of_continuous (continuous_rootPoint i x) _ (0 : ℂ) _ a
  · intro b
    apply Commute.symm
    apply (mul_inv_eq_iff_eq_mul).mp
    let tG : GroupPoints P.G.val Rℂ := t ≫ P.T.inclusion.hom.hom
    change tG * rootPoint x Rℂ b * tG⁻¹ = rootPoint x Rℂ b
    simpa only [hχ, one_mul] using hx Rℂ t b
  · change rootPoint x Rℂ 0 = (1 : GroupPoints P.G.val Rℂ)
    rw [rootPoint_eq, additivePoints_zero]
    exact (pointHom x _).map_one

open private exponentEvaluation exponentsEquiv
  from LinearAlgebraicGroups.Affine.StandardGroups
open Specs.StandardGroups (LaurentPowerCoordinates multiplicativePowerGroup)

private def laurentEval {J : Type} [Fintype J] [DecidableEq J] (a : J → ℂˣ) :
    LaurentPowerCoordinates ℂ J →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (J → ℤ) (Units.coeHom ℂ |>.comp (exponentEvaluation a))

private theorem continuous_laurentEval {J : Type} [Fintype J] [DecidableEq J]
    (p : LaurentPowerCoordinates ℂ J) : Continuous (fun a : J → ℂˣ => laurentEval a p) := by
  induction p using AddMonoidAlgebra.induction_on with
  | of n =>
    change Continuous (fun a : J → ℂˣ => laurentEval a (AddMonoidAlgebra.single n 1))
    simp only [laurentEval, AddMonoidAlgebra.lift_single, one_smul]
    have h : Continuous (fun a : J → ℂˣ => ∏ i, a i ^ n i) :=
      continuous_finsetProd _ fun j _ => (continuous_apply j).zpow _
    exact Units.continuous_val.comp h
  | add p q hp hq =>
    have h : Continuous (fun a : J → ℂˣ => laurentEval a p + laurentEval a q) := hp.add hq
    simpa only [map_add] using h
  | smul c p hp =>
    have h : Continuous (fun a : J → ℂˣ => c * laurentEval a p) := continuous_const.mul hp
    simpa only [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] using h

private theorem laurentEval_surjective {J : Type} [Fintype J] [DecidableEq J] :
    Function.Surjective (laurentEval (J := J)) := by
  let e : (Multiplicative (J → ℤ) →* ℂˣ) ≃ (LaurentPowerCoordinates ℂ J →ₐ[ℂ] ℂ) :=
    (MonoidHom.toHomUnitsMulEquiv :
      (Multiplicative (J → ℤ) →* ℂ) ≃* _).symm.toEquiv.trans
       (AddMonoidAlgebra.lift ℂ ℂ (J → ℤ))
  exact (show Function.Surjective (e ∘ (exponentsEquiv ℂ : _ ≃* (J → ℂˣ)).symm) from
    e.surjective.comp (exponentsEquiv ℂ).symm.surjective)

private theorem torusPoint_mem_component {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X] (t s : GroupPoints P.T.group Rℂ) :
    (s ≫ P.T.inclusion.hom.hom : PointsIn i ℂ) ∈
      centralizerComponent (show PointsIn i ℂ from t ≫ P.T.inclusion.hom.hom) := by
  classical
  obtain ⟨r, ⟨e⟩⟩ := P.split
  let J := ULift (Fin r)
  let L := (multiplicativePowerGroup ℂ J).val
  let f := (e.inv ≫ P.T.inclusion).hom.hom
  let F : (J → ℂˣ) → PointsIn i ℂ := fun a => presentedPoint i f (laurentEval a)
  have hmap (s : GroupPoints P.T.group Rℂ) :
      ∃ a, F a = s ≫ P.T.inclusion.hom.hom := by
    let p : GroupPoints L Rℂ := s ≫ e.hom.hom.hom
    let ff := algSpec.fullyFaithful (R := CommRingCat.of ℂ)
    let b := (ff.preimage p).unop
    obtain ⟨a, ha⟩ := laurentEval_surjective b.hom
    refine ⟨a, ?_⟩
    have hb : CommAlgCat.ofHom (laurentEval a) = b := CommAlgCat.hom_ext ha
    have hp : (testSpec ℂ).map b.op = p := ff.map_preimage p
    change (testSpec ℂ).map (CommAlgCat.ofHom (laurentEval a)).op ≫ f = _
    rw [hb, hp]
    change (s ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ≫ P.T.inclusion.hom.hom = _
    simp only [Category.assoc, ← Grp.comp_hom_hom]
    rw [← Category.assoc e.hom, e.hom_inv_id, Category.id_comp]
  obtain ⟨a₀, ha₀⟩ := hmap 1
  obtain ⟨a, ha⟩ := hmap s
  rw [← ha]
  refine mem_centralizerComponent_of_continuous
    (continuous_presentedPoint i f laurentEval continuous_laurentEval) ?_ a₀ ?_ a
  · intro b
    change Commute ((pointHom P.T.inclusion _) ((testSpec ℂ).map
      (CommAlgCat.ofHom (laurentEval b)).op ≫ e.inv.hom.hom)) (pointHom P.T.inclusion _ t)
    exact (Commute.all _ _).map (pointHom P.T.inclusion _)
  · change F a₀ = 1
    rw [ha₀]
    exact (pointHom P.T.inclusion _).map_one

open Specs.OrderedRootProducts (product)
open CategoryTheory.MonoidalCategory

private abbrev complexTestScheme : SchemeOver ℂ := (testSpec ℂ).obj (.op Rℂ)

local notation "Sℂ" => complexTestScheme

private def rootProductPoint {G : AffineAlgebraicGroup ℂ}
    (i : MatrixRealization G) {T : ClosedSubgroup G.val} (U : RootSubgroupFamily T)
    (l : List (Root T)) (p : Sℂ ⟶ product (fun α => (U α).val.group.X) l) :
    PointsIn i ℂ := p ≫ rootProduct U l

/-- Conjugation acts on each coordinate of an ordered root product by
the root's value. A fixed coordinate contributes to the identity
component of the centralizer. -/
private theorem rootProduct_conjugate {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) (t : GroupPoints P.T.group Rℂ)
    (U : RootSubgroupFamily P.T) (l : List (Root P.T))
    (p : Sℂ ⟶ product (fun α => (U α).val.group.X) l) :
    let tG : PointsIn i ℂ := t ≫ P.T.inclusion.hom.hom
    ∃ q : Sℂ ⟶ product (fun α => (U α).val.group.X) l,
      rootProductPoint i U l q = tG * rootProductPoint i U l p * tG⁻¹ ∧
      (q = p → rootProductPoint i U l p ∈ centralizerComponent tG) := by
  dsimp only
  let tG : PointsIn i ℂ := t ≫ P.T.inclusion.hom.hom
  induction l with
  | nil =>
    have h : rootProductPoint i U [] p = 1 := by
      change (p ≫ 1 : GroupPoints P.G.val Rℂ) = 1
      exact MonObj.comp_one p
    exact ⟨p, by rw [h]; simp, fun _ => h.symm ▸ (centralizerComponent tG).one_mem⟩
  | cons α l ih =>
    obtain ⟨⟨A, xIso, hx, _⟩⟩ := rootCoordinate_exists RootData.RootGroups.rootSubgroups
      P.G P.reductive P.T P.split P.maximal U α
    let x := xIso.hom ≫ (U α).val.inclusion
    let e : ℂ ≃ GroupPoints (U α).val.group Rℂ :=
      (RootData.RootGroups.additivePoints A Rℂ).trans
        (Iso.homCongr (Iso.refl _) ((Grp.forget _).mapIso xIso))
    have he (a : ℂ) : e a = rootPoint xIso.hom Rℂ a := by
      change 𝟙 _ ≫ rootPoint (𝟙 A.group) Rℂ a ≫ xIso.hom.hom.hom = _
      rw [Category.id_comp, ← rootPoint_comp, Category.id_comp]
    let p₁ := p ≫ fst _ _
    let p₂ := p ≫ snd _ _
    let a := e.symm p₁
    let aScaled := characterValue α.val Rℂ t * a
    have hhead : rootMatrixPoint i x a = p₁ ≫ (U α).val.inclusion.hom.hom := by
      change rootPoint x Rℂ a = _
      rw [rootPoint_comp, ← he, Equiv.apply_symm_apply]
    obtain ⟨q₂, hq₂, hfix₂⟩ := ih p₂
    let q := lift (e aScaled) q₂
    have hmul (r : Sℂ ⟶ product (fun α => (U α).val.group.X) (α :: l)) :
        rootProductPoint i U (α :: l) r =
          (show PointsIn i ℂ from (r ≫ fst _ _) ≫ (U α).val.inclusion.hom.hom) *
            rootProductPoint i U l (r ≫ snd _ _) := by
      let h := fst (U α).val.group.X (product (fun b => (U b).val.group.X) l) ≫
        (U α).val.inclusion.hom.hom
      let k := snd (U α).val.group.X (product (fun b => (U b).val.group.X) l) ≫ rootProduct U l
      change r ≫ (h * k) = ((r ≫ fst _ _) ≫ (U α).val.inclusion.hom.hom) *
        ((r ≫ snd _ _) ≫ rootProduct U l)
      simpa only [h, k, Category.assoc] using MonObj.comp_mul r h k
    have hq : rootProductPoint i U (α :: l) q =
        rootMatrixPoint i x aScaled * rootProductPoint i U l q₂ := by
      have hcoord : rootMatrixPoint i x aScaled = (e aScaled ≫ (U α).val.inclusion.hom.hom) := by
        change rootPoint x Rℂ aScaled = _
        rw [rootPoint_comp, ← he]
      rw [hmul, show q ≫ fst _ _ = e aScaled from lift_fst _ _, show q ≫ snd _ _ = q₂ from lift_snd _ _, ← hcoord]
    have hact : tG * rootMatrixPoint i x a * tG⁻¹ = rootMatrixPoint i x aScaled := hx Rℂ t a
    refine ⟨q, ?_, ?_⟩
    · rw [hq, ← hact, hq₂, hmul, ← hhead]
      change (tG * rootMatrixPoint i x a * tG⁻¹) *
        (tG * rootProductPoint i U l p₂ * tG⁻¹) =
          tG * (rootMatrixPoint i x a * rootProductPoint i U l p₂) * tG⁻¹
      simp only [mul_assoc, inv_mul_cancel_left]
    · intro h
      have h₂ : q₂ = p₂ := (lift_snd _ _).symm.trans (congrArg (fun z => z ≫ snd _ _) h)
      have h₁ : aScaled = a := e.injective
        ((lift_fst _ _).symm.trans ((congrArg (fun z => z ≫ fst _ _) h).trans
          (e.apply_symm_apply p₁).symm))
      have hzero : (characterValue α.val Rℂ t - 1) * a = 0 := by
        rw [sub_mul, one_mul, show characterValue α.val Rℂ t * a = a from h₁, sub_self]
      have hmem : rootMatrixPoint i x a ∈ centralizerComponent tG := by
        rcases mul_eq_zero.mp hzero with hs | hz
        · exact rootPoint_mem_component i t hx (sub_eq_zero.mp hs) a
        · have hz' : rootMatrixPoint i x 0 = 1 := by
            change rootPoint x Rℂ 0 = (1 : GroupPoints P.G.val Rℂ)
            rw [rootPoint_eq]
            rw [additivePoints_zero]
            exact (pointHom x _).map_one
          rw [hz, hz']
          exact (centralizerComponent tG).one_mem
      rw [hmul, ← hhead]
      exact (centralizerComponent tG).mul_mem hmem (hfix₂ h₂)

open private labelConjugation inducedConjugation_unique
  from LinearAlgebraicGroups.RootData.DatumAndWeyl
open private schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient

private def torusPoint {P : SplitBorelPair ℂ} (i : MatrixRealization P.G) :
    GroupPoints P.T.group Rℂ →* PointsIn i ℂ := pointHom P.T.inclusion Sℂ

private def normalizerPoint {P : SplitBorelPair ℂ} (i : MatrixRealization P.G)
    [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D) :
    (𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X) →* PointsIn i ℂ :=
  (pointHom I.normalizer.inclusion Sℂ).comp (restrictPointHom I.normalizer.group Sℂ)

private theorem normalizerPoint_conjugates {P : SplitBorelPair ℂ} (i : MatrixRealization P.G)
    [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D)
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X) (t : GroupPoints P.T.group Rℂ) :
    let e := I.image.conjugation (I.labelEquiv (normalizerLabel I n))
    torusPoint i (t ≫ e.hom.hom.hom) =
      normalizerPoint i I n * torusPoint i t * (normalizerPoint i I n)⁻¹ := by
  dsimp only
  have h := labelConjugation I.image _ n (normalizer_isRepresentative I n)
  have hh := congrArg (t ≫ ·) h
  simp only [MonObj.comp_mul, GrpObj.comp_inv] at hh
  have hu : t ≫ (toUnit P.T.group.X ≫ n ≫ I.normalizer.inclusion.hom.hom) =
      (normalizerPoint i I n : PointsIn i ℂ) := by
    rw [← Category.assoc t, toUnit_unique (t ≫ toUnit _) (toUnit Sℂ)]
    rfl
  rw [hu] at hh
  exact hh

private theorem sign_invariant_of_commute {P : SplitBorelPair ℂ} (i : MatrixRealization P.G)
    [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D)
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X) (t : GroupPoints P.T.group Rℂ)
    (ht : t ^ 2 = 1) (hc : Commute (normalizerPoint i I n) (torusPoint i t))
    (z : Additive (Character P.T.group)) :
    torusSign t ht ((normalizerLabel I n).val.weightEquiv z) = torusSign t ht z := by
  let e := I.image.conjugation (I.labelEquiv (normalizerLabel I n))
  have h := normalizerPoint_conjugates i I n t
  have := monoSubgroup P.T
  have ht' : t ≫ e.hom.hom.hom = t := (cancel_mono P.T.inclusion.hom.hom).mp
    (h.trans (by rw [hc.eq, mul_inv_cancel_right]; rfl))
  have ht'' : t ≫ e.inv.hom.hom = t := by
    conv_lhs => rw [← ht']
    simp only [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
  change torusSign t ht ((normalizerLabel I n).val.weightEquiv (Additive.ofMul z.toMul)) = _
  rw [I.characterAction, I.image.characterAction]
  change signNumber (characterUnit (e.inv ≫ z.toMul) Rℂ t) = _
  unfold characterUnit
  simp only [Grp.comp_hom_hom]
  rw [← Category.assoc t, ht'']
  rfl

private theorem opposite_characterValue_one {T : GroupScheme ℂ}
    (t : GroupPoints T Rℂ) (χ : Character T) (hχ : characterValue χ Rℂ t = 1) :
    characterValue χ⁻¹ Rℂ t = 1 := by
  have hu : characterEvaluation Rℂ t χ = 1 := by
    apply Units.ext
    change (characterUnit χ Rℂ t : ℂ) = 1
    rwa [← characterValue_eq_unit]
  rw [characterValue_eq_unit]
  change ((characterEvaluation Rℂ t χ⁻¹ : ℂˣ) : ℂ) = _
  rw [map_inv, hu, inv_one, Units.val_one]

private theorem reflection_label {P : SplitBorelPair ℂ}
    [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D)
    (α : Root P.T) {A : AdditiveLine ℂ} {x y : A.group ⟶ P.G.val}
    (r : RootGroups.CorootReflection P.T α.val x y)
    (hr : r.coroot = Additive.toMul (D.rootDatum.coroot α))
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X)
    (hn : n ≫ I.normalizer.inclusion.hom.hom = r.representative) :
    normalizerLabel I n = RootPairing.weylGroup.ofIdx D.rootDatum α := by
  have hconj : r.conjugation = I.image.conjugation (I.labelEquiv (normalizerLabel I n)) := by
    apply inducedConjugation_unique (g := r.representative) r.conjugates
    rw [← hn]
    exact labelConjugation I.image _ n (normalizer_isRepresentative I n)
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective D.rootDatum
  apply LinearEquiv.ext
  intro z
  change (normalizerLabel I n).val.weightEquiv (Additive.ofMul z.toMul) =
    (RootPairing.Equiv.reflection D.rootDatum α).weightEquiv (Additive.ofMul z.toMul)
  rw [I.characterAction, I.image.characterAction, ← hconj, r.reflection,
    RootPairing.Equiv.reflection_weightEquiv, RootPairing.reflection_apply, D.root_eq]
  have hpair : D.rootDatum.coroot' α (Additive.ofMul z.toMul) =
      CharacterPairing.pairing P.T.group z.toMul r.coroot := by
    rw [hr]
    exact D.pairing_eq z.toMul _
  rw [hpair, sub_eq_add_neg, ← neg_smul, ofMul_mul, ofMul_zpow]

private def rankOneMatrixWord {G : AffineAlgebraicGroup ℂ}
    (i : MatrixRealization G) {A : AdditiveLine ℂ} (x y : A.group ⟶ G.val) (b : ℂˣ) :
    PointsIn i ℂ :=
  rootMatrixPoint i x (b : ℂ) * rootMatrixPoint i y (-(b⁻¹ : ℂˣ).val) *
    rootMatrixPoint i x (b : ℂ)

private theorem rankOneMatrixWord_mem_component {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) (t : GroupPoints P.T.group Rℂ)
    {A : AdditiveLine ℂ} {x y : A.group ⟶ P.G.val} {χ : Character P.T.group}
    (hx : HasScalarAction P.T χ x) (hy : HasScalarAction P.T χ⁻¹ y)
    (hχ : characterValue χ Rℂ t = 1) (b : ℂˣ) :
    rankOneMatrixWord i x y b ∈ centralizerComponent (torusPoint i t) := by
  let H := centralizerComponent (torusPoint i t)
  have h₁ : rootMatrixPoint i x (b : ℂ) ∈ H := rootPoint_mem_component i t hx hχ (b : ℂ)
  have h₂ : rootMatrixPoint i y (-(b⁻¹ : ℂˣ).val) ∈ H :=
    rootPoint_mem_component i t hy (opposite_characterValue_one t χ hχ) (-(b⁻¹ : ℂˣ).val)
  exact H.mul_mem (H.mul_mem h₁ h₂) h₁

private theorem normalizerPoint_eq_rankOneMatrixWord {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X] {D : Datum P.T}
    (I : Identification D) (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X)
    {A : AdditiveLine ℂ} {x y : A.group ⟶ P.G.val} {χ : Character P.T.group}
    (r : RootGroups.CorootReflection P.T χ x y)
    (hn : n ≫ I.normalizer.inclusion.hom.hom = r.representative) :
    normalizerPoint i I n = rankOneMatrixWord i x y 1 := by
  change toUnit Sℂ ≫ (n ≫ I.normalizer.inclusion.hom.hom) = rankOneWord x y Rℂ 1
  exact (congrArg (toUnit Sℂ ≫ ·) hn).trans r.representative_word

private theorem mem_map_comap_of_lift {K N W : Type*} [Group K] [Group N] [Group W]
    (H : Subgroup K) (f : N →* K) (L : N →* W) (n : N) (w : W)
    (hn : f n ∈ H) (hw : L n = w) : w ∈ (H.comap f).map L :=
  ⟨n, hn, hw⟩

private theorem fixing_reflection_lifts_of_coordinates {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X] {D : Datum P.T}
    (I : Identification D) (t : GroupPoints P.T.group Rℂ)
    (α : Root P.T) (hα : characterValue α.val Rℂ t = 1)
    {A : AdditiveLine ℂ} {x y : A.group ⟶ P.G.val}
    (hx : HasScalarAction P.T α.val x) (hy : HasScalarAction P.T α.val⁻¹ y)
    (r : RootGroups.CorootReflection P.T α.val x y)
    (hr : r.coroot = Additive.toMul (D.rootDatum.coroot α)) :
    RootPairing.weylGroup.ofIdx D.rootDatum α ∈
      ((centralizerComponent (torusPoint i t)).comap (normalizerPoint i I)).map
        (normalizerLabel I) := by
  obtain ⟨n, hn⟩ := (I.representsNormalizer (𝟙_ (SchemeOver ℂ)) r.representative).mp r.normalizes
  have hm : normalizerPoint i I n ∈ centralizerComponent (torusPoint i t) := by
    rw [normalizerPoint_eq_rankOneMatrixWord i I n r hn]
    exact rankOneMatrixWord_mem_component i t hx hy hα 1
  exact mem_map_comap_of_lift (centralizerComponent (torusPoint i t))
    (normalizerPoint i I) (normalizerLabel I) n _ hm (reflection_label I α r hr n hn)

private theorem fixing_reflection_lifts {P : SplitBorelPair ℂ} (i : MatrixRealization P.G)
    [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D)
    (t : GroupPoints P.T.group Rℂ) (α : Root P.T) (hα : characterValue α.val Rℂ t = 1) :
    RootPairing.weylGroup.ofIdx D.rootDatum α ∈
      ((centralizerComponent (torusPoint i t)).comap (normalizerPoint i I)).map
        (normalizerLabel I) := by
  obtain ⟨C, c, _, _, L, M, _, Q, F, A, B, p, q, _, _, hh⟩ := D.attached α
  dsimp only at hh
  obtain ⟨hp, hq, r, hr⟩ := hh
  exact fixing_reflection_lifts_of_coordinates i I t α hα hp hq r hr

private theorem normalizer_kernel_mem_component {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X] {D : Datum P.T} (I : Identification D)
    (t : GroupPoints P.T.group Rℂ) (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X)
    (hn : normalizerLabel I n = 1) :
    normalizerPoint i I n ∈ centralizerComponent (torusPoint i t) := by
  have h := normalizer_isRepresentative I n
  change n ≫ I.quotient.hom.hom =
    I.image.constantGroup.sectionPoint (I.labelEquiv (normalizerLabel I n)) at h
  rw [hn, map_one, map_one] at h
  obtain ⟨s, hs⟩ := (schemeKernel_sections I.isQuotient.1 n).mpr h
  have hI := congrArg (Grp.forget (SchemeOver ℂ)).map I.inclusion_eq
  change I.torusInclusion.hom.hom ≫ I.normalizer.inclusion.hom.hom =
    P.T.inclusion.hom.hom at hI
  have he : normalizerPoint i I n = torusPoint i (toUnit Sℂ ≫ s) := by
    change toUnit Sℂ ≫ n ≫ I.normalizer.inclusion.hom.hom =
      (toUnit Sℂ ≫ s) ≫ P.T.inclusion.hom.hom
    change s ≫ I.torusInclusion.hom.hom = n at hs
    rw [← hI, Category.assoc, ← Category.assoc s, hs]
  rw [he]
  exact torusPoint_mem_component i t _

private theorem mem_of_map_of_kernel {K N W : Type*} [Group K] [Group N] [Group W]
    (H : Subgroup K) (f : N →* K) (L : N →* W) (n : N)
    (hkernel : ∀ m, L m = 1 → f m ∈ H)
    (h : L n ∈ (H.comap f).map L) : f n ∈ H := by
  obtain ⟨m, hm, hm'⟩ := h
  have hK : f (m⁻¹ * n) ∈ H := hkernel _ (by rw [map_mul, map_inv, hm', inv_mul_cancel])
  have hh := H.mul_mem hm hK
  simpa only [← map_mul, mul_inv_cancel_left] using hh

private theorem commuting_normalizer_mem_component {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X]
    {D : Datum P.T} (I : Identification D) (B : D.rootDatum.Base)
    [Finite (Root P.T)] [D.rootDatum.IsReduced]
    [Module.Free ℤ (Additive (Specs.CharacterDescent.Cocharacter P.T.group))]
    [Module.Finite ℤ (Additive (Specs.CharacterDescent.Cocharacter P.T.group))]
    (hfull : finrank ℤ (Submodule.span ℤ (Set.range D.rootDatum.coroot)) =
      finrank ℤ (Additive (Specs.CharacterDescent.Cocharacter P.T.group)))
    (hF : HasDynkinType (integralCartan D.rootDatum B) .F4)
    (t : GroupPoints P.T.group Rℂ) (ht : t ^ 2 = 1)
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X)
    (hc : Commute (normalizerPoint i I n) (torusPoint i t)) :
    normalizerPoint i I n ∈ centralizerComponent (torusPoint i t) := by
  let H := (centralizerComponent (torusPoint i t)).comap (normalizerPoint i I)
  let L := normalizerLabel I
  let χ := torusSign t ht
  have hn := weyl_stabilizer_mem_closure D.rootDatum B hfull hF χ (L n)
    (sign_invariant_of_commute i I n t ht hc)
  have hle : Subgroup.closure (RootPairing.weylGroup.ofIdx D.rootDatum ''
        {a | χ (D.rootDatum.root a) = 0}) ≤ H.map L := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, ha, rfl⟩
    change χ (D.rootDatum.root a) = 0 at ha
    rw [D.root_eq] at ha
    exact fixing_reflection_lifts i I t a ((torusSign_eq_zero t ht a.val).mp ha)
  exact mem_of_map_of_kernel _ _ _ n (normalizer_kernel_mem_component i I t) (hle hn)

open Specs.BruhatOrbitParametrization (OrderedParametrization)
open LinearAlgebraicGroups.CocharacterDynamics (multiplyFactors)
open private semisimple_iff_corootFullRank
  from LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private actualDatum_unique
  from LinearAlgebraicGroups.Classification.TransportedRootCoordinates

private theorem exists_rootEnumeration {P : SplitBorelPair ℂ} [Finite (Root P.T)]
    (roots : Set (Root P.T)) : ∃ l, Enumerates l roots := by
  classical
  let f := roots.toFinite.toFinset
  exact ⟨f.toList, f.nodup_toList, fun a => by simp [f]⟩

private theorem lift_complexPoint_of_range {X Y : SchemeOver ℂ} (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] (g : Sℂ ⟶ Y)
    (h : g.left (IsLocalRing.closedPoint ℂ) ∈ Set.range f.left) :
    ∃ p : Sℂ ⟶ X, p ≫ f = g :=
  lift_of_range f g h

private theorem bruhatCoordinates {P : SplitBorelPair ℂ}
    (i : MatrixRealization P.G) [IsCommMonObj P.T.group.X] {D : Datum P.T}
    (I : Identification D)
    (n : 𝟙_ (SchemeOver ℂ) ⟶ I.normalizer.group.X)
    {Q : QuotientEmbedding.Presentation P.B} {a : ModObj P.G.val.X Q.scheme}
    {A : ClosedSubgroup P.G.val}
    (C : Cell (T := P.T) Q a (n ≫ I.normalizer.inclusion.hom.hom) A)
    (R : ClosedSubgroup P.B.group) (j : P.T.group ⟶ P.B.group)
    (hj : j ≫ P.B.inclusion = P.T.inclusion) [IsIso (multiplyFactors j R.inclusion)]
    (U : RootSubgroupFamily P.T) (l m : List (Root P.T))
    (eA : Parametrizes U l A.inclusion.hom.hom)
    (eR : Parametrizes U m (R.inclusion.hom.hom ≫ P.B.inclusion.hom.hom)) :
    let L := product (fun α => (U α).val.group.X) l
    let M := product (fun α => (U α).val.group.X) m
    let value (x : Sℂ ⟶ L) (s : GroupPoints P.T.group Rℂ) (y : Sℂ ⟶ M) :=
      rootProductPoint i U l x * normalizerPoint i I n *
        (torusPoint i s * rootProductPoint i U m y)
    (∀ (x x' : Sℂ ⟶ L) (s s' : GroupPoints P.T.group Rℂ) (y y' : Sℂ ⟶ M),
      value x s y = value x' s' y' → x = x' ∧ s = s' ∧ y = y') ∧
    ∀ p : Sℂ ⟶ C.doubleOrbit,
      ∃ x s y, value x s y = (p ≫ C.doubleOrbitInclusion : PointsIn i ℂ) := by
  dsimp only
  obtain ⟨e, he⟩ := eA
  obtain ⟨f, hf⟩ := eR
  let b (s : GroupPoints P.T.group Rℂ)
      (y : Sℂ ⟶ product (fun α => (U α).val.group.X) m) : Sℂ ⟶ P.B.group.X :=
    lift s (y ≫ f.hom) ≫ multiplyFactors j R.inclusion
  let coords (x : Sℂ ⟶ product (fun α => (U α).val.group.X) l)
      (s : GroupPoints P.T.group Rℂ) (y : Sℂ ⟶ product (fun α => (U α).val.group.X) m) :
      Sℂ ⟶ C.doubleOrbit :=
    lift (x ≫ e.hom) (b s y) ≫ C.doubleOrbitIso.hom
  have hB (s : GroupPoints P.T.group Rℂ) (y : Sℂ ⟶ _) :
      (b s y ≫ P.B.inclusion.hom.hom : PointsIn i ℂ) =
        torusPoint i s * rootProductPoint i U m y := by
    have ht := congrArg (Grp.forget (SchemeOver ℂ)).map hj
    change j.hom.hom ≫ P.B.inclusion.hom.hom = P.T.inclusion.hom.hom at ht
    simp only [b, multiplyFactors, Category.assoc, MonObj.comp_mul, MonObj.mul_comp,
      lift_fst_assoc, lift_snd_assoc, ht, hf]
    rfl
  have hcoords (x : Sℂ ⟶ _) (s : GroupPoints P.T.group Rℂ) (y : Sℂ ⟶ _) :
      (coords x s y ≫ C.doubleOrbitInclusion : PointsIn i ℂ) =
        rootProductPoint i U l x * normalizerPoint i I n *
          (torusPoint i s * rootProductPoint i U m y) := by
    rw [show coords x s y ≫ C.doubleOrbitInclusion =
      lift (x ≫ e.hom) (b s y) ≫ (C.doubleOrbitIso.hom ≫ C.doubleOrbitInclusion) from
        Category.assoc _ _ _]
    rw [C.doubleOrbitIso_eq]
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, Category.assoc, he]
    have ht : lift (x ≫ e.hom) (b s y) ≫ toUnit _ = toUnit Sℂ := Subsingleton.elim _ _
    rw [← Category.assoc (lift (x ≫ e.hom) (b s y)) (toUnit _), ht]
    exact congrArg (fun z : PointsIn i ℂ => rootProductPoint i U l x * normalizerPoint i I n * z)
      (hB s y)
  constructor
  · intro x x' s s' y y' h
    letI := C.doubleOrbitImmersion
    letI : Mono C.doubleOrbitInclusion := Over.mono_of_mono_left _
    have h₁ : coords x s y = coords x' s' y' :=
      (cancel_mono C.doubleOrbitInclusion).mp ((hcoords x s y).trans (h.trans (hcoords x' s' y').symm))
    have h₂ := (cancel_mono C.doubleOrbitIso.hom).mp h₁
    have ha := congrArg (· ≫ fst _ _) h₂
    simp only [lift_fst] at ha
    have hb := congrArg (· ≫ snd _ _) h₂
    simp only [lift_snd] at hb
    have hb' := (cancel_mono (multiplyFactors j R.inclusion)).mp hb
    have hs := congrArg (· ≫ fst _ _) hb'
    have hy := congrArg (· ≫ snd _ _) hb'
    simp only [lift_fst] at hs
    simp only [lift_snd] at hy
    exact ⟨(cancel_mono e.hom).mp ha, hs, (cancel_mono f.hom).mp hy⟩
  · intro p
    let xy := p ≫ C.doubleOrbitIso.inv
    let sy := (xy ≫ snd _ _) ≫ inv (multiplyFactors j R.inclusion)
    let x := xy ≫ fst _ _ ≫ e.inv
    let s := sy ≫ fst _ _
    let y := sy ≫ snd _ _ ≫ f.inv
    have hx : x ≫ e.hom = xy ≫ fst _ _ := by simp [x]
    have hy : y ≫ f.hom = sy ≫ snd _ _ := by simp [y]
    have hb : b s y = xy ≫ snd _ _ := by
      change lift (sy ≫ fst _ _) (y ≫ f.hom) ≫ multiplyFactors j R.inclusion = _
      rw [hy, lift_comp_fst_snd]
      simp only [sy, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    refine ⟨x, s, y, (hcoords x s y).symm.trans ?_⟩
    have hp : coords x s y = p := by
      change lift (x ≫ e.hom) (b s y) ≫ C.doubleOrbitIso.hom = p
      rw [hx, hb, lift_comp_fst_snd]
      simp only [xy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hp]

private theorem conjugate_cell_word {K : Type*} [Group K] (t u n s v : K) :
    (t * u * t⁻¹) * n * (n⁻¹ * t * n * s * t⁻¹ * (t * v * t⁻¹)) =
      t * (u * n * (s * v)) * t⁻¹ := by
  simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

set_option maxHeartbeats 350000 in
/-- The centralizer of a square-one torus point in the split complex
group of type F₄ is connected in its closed matrix point topology. -/
theorem toralCentralizerConnected :
    Specs.ComplexF4ToralCentralizers.ToralCentralizerConnected := by
  classical
  intro P D hss hF i t ht
  letI := D.comm
  change ConnectedSpace {g : PointsIn i ℂ // Commute g (torusPoint i t)}
  let H := centralizerComponent (torusPoint i t)
  suffices h : ∀ g : PointsIn i ℂ, Commute g (torusPoint i t) → g ∈ H by
    change ConnectedSpace (centralizerSubgroup (torusPoint i t))
    rw [connectedSpace_iff_connectedComponent]
    refine ⟨1, Set.eq_univ_of_forall fun g => ?_⟩
    have hg := h (g : PointsIn i ℂ) g.property
    obtain ⟨g', hg', heq⟩ := hg
    exact (Subtype.ext heq : g' = g) ▸ hg'
  intro g hg
  obtain ⟨_, E, I, U, Bneg, Rpos, Rneg, c, B, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, hrep, hQ, hC⟩ :=
    Flag.BruhatCells.bruhatCells P.G P.reductive P.T P.B P.split P.maximal P.borel P.containsTorus
  have hE : E = D.datum := actualDatum_unique P.reductive P.split P.maximal E D.datum
  subst E
  letI := D.datum.finiteRoots
  letI := D.datum.reduced
  letI := D.datum.freeCocharacters
  letI := D.datum.finiteCocharacters
  have hfull := (semisimple_iff_corootFullRank P D).mp hss
  obtain ⟨Q⟩ := hQ
  obtain ⟨a, _, hQ'⟩ := hC Q
  choose n hn using hrep
  obtain ⟨A, C, hA, _, hCover, _⟩ := hQ' n hn
  have hpoint : (show Sℂ ⟶ P.G.val.X from g).left (IsLocalRing.closedPoint ℂ) ∈
      ⋃ w, Set.range (C w).doubleOrbitInclusion.left := hCover ▸ Set.mem_univ _
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hpoint
  letI := (C w).doubleOrbitImmersion
  obtain ⟨p, hp⟩ := lift_complexPoint_of_range (C w).doubleOrbitInclusion g hw
  obtain ⟨_, _, _, _, _, _, hB⟩ :=
    RootData.BorelPositivity.borelPositivity P.G P.reductive P.T P.split P.maximal
  obtain ⟨R, j, q, _, _, hj, _, _, hjR, hR⟩ := hB P.B P.borel P.containsTorus
  letI := hjR
  obtain ⟨l, hl⟩ := exists_rootEnumeration
    (Specs.BorelsAndChambers.subgroupRoots P.T P.B ∩
      D.datum.rootDatum.weylGroupToPerm w '' Specs.BorelsAndChambers.subgroupRoots P.T Bneg)
  obtain ⟨m, hm⟩ := exists_rootEnumeration (Specs.BorelsAndChambers.subgroupRoots P.T P.B)
  obtain ⟨hinj, hsurj⟩ :=
    bruhatCoordinates i I (n w) (C w) R j hj U l m ((hA w).2.1 l hl) (hR U m hm)
  obtain ⟨x, s, y, he⟩ := hsurj p
  change _ = (p ≫ (C w).doubleOrbitInclusion : PointsIn i ℂ) at he
  rw [hp] at he
  let N := normalizerPoint i I (n w)
  let T := torusPoint i t
  let a' := I.image.conjugation (I.labelEquiv (normalizerLabel I (n w)⁻¹))
  let t' : GroupPoints P.T.group Rℂ := t ≫ a'.hom.hom.hom
  have ht' : torusPoint i t' = N⁻¹ * T * N := by
    have h := normalizerPoint_conjugates i I (n w)⁻¹ t
    change torusPoint i t' = normalizerPoint i I (n w)⁻¹ * T *
      (normalizerPoint i I (n w)⁻¹)⁻¹ at h
    rw [map_inv (normalizerPoint i I), inv_inv] at h
    exact h
  obtain ⟨x', hx', hx⟩ := rootProduct_conjugate i t U l x
  obtain ⟨y', hy', hy⟩ := rootProduct_conjugate i t U m y
  have he' :
      rootProductPoint i U l x' * N *
          (torusPoint i (t' * s * t⁻¹) * rootProductPoint i U m y') =
        rootProductPoint i U l x * N * (torusPoint i s * rootProductPoint i U m y) := by
    rw [hx', hy', map_mul, map_mul, map_inv, ht']
    change (T * rootProductPoint i U l x * T⁻¹) * N *
      (N⁻¹ * T * N * torusPoint i s * T⁻¹ * (T * rootProductPoint i U m y * T⁻¹)) = _
    rw [conjugate_cell_word]
    change rootProductPoint i U l x * N * (torusPoint i s * rootProductPoint i U m y) =
      g at he
    rw [he, ← hg.eq, mul_inv_cancel_right]
  have ⟨ex, es, ey⟩ := hinj x' x (t' * s * t⁻¹) s y' y he'
  have hs := torusPoint_mem_component i t s
  have hsT : Commute (torusPoint i s) T := by
    obtain ⟨z, _, hz⟩ := hs
    have hz' : (z : PointsIn i ℂ) = torusPoint i s := hz
    rw [← hz']
    exact z.property
  have heT : torusPoint i t' * torusPoint i s * T⁻¹ = torusPoint i s := by
    have h := congrArg (torusPoint i) es
    simpa only [map_mul, map_inv, T] using h
  have et : torusPoint i t' = T := by
    calc
      torusPoint i t' =
          (torusPoint i t' * torusPoint i s * T⁻¹) * (T * (torusPoint i s)⁻¹) := by
        simp [mul_assoc]
      _ = T := by rw [heT, ← mul_assoc, hsT.eq, mul_inv_cancel_right]
  have hN : Commute N T := by
    rw [et] at ht'
    change N * T = T * N
    calc
      N * T = N * (N⁻¹ * T * N) := congrArg (N * ·) ht'
      _ = T * N := by simp [← mul_assoc]
  have hN' := commuting_normalizer_mem_component i I D.base hfull hF t ht (n w) hN
  rw [← he]
  exact H.mul_mem (H.mul_mem (hx ex) hN') (H.mul_mem hs (hy ey))

end

end LinearAlgebraicGroups.Arithmetic.ComplexF4ToralCentralizers
