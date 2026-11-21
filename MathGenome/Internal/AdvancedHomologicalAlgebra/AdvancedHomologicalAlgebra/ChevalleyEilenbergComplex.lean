import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.ChevalleyEilenbergComplex
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import Mathlib.Tactic.Abel
import Mathlib.Order.Interval.Finset.Fin

/-! The Chevalley--Eilenberg complex (HA-A06).

The boundary is constructed on the original exterior tensor powers over an
arbitrary commutative ring. An ordered free basis splits the alternating bracket
as the antisymmetrization of a bilinear map, so the bracket descent requires no
division. Cartan recursion, the enveloping relation and Jacobi prove square zero
in every degree. Evaluation on `1 ⊗ -` supplies the natural cochain comparison.
-/

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

/-- Extend by `a ⊗ z ↦ a • f z`, with the genuine left U-module structure. -/
noncomputable def extend (n : ℕ) (f : W k g n →ₗ[k] M) : V k g n →ₗ[U k g] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a => a • f
      map_add' := fun a b => add_smul a b f
      map_smul' := fun a b => mul_smul a b f }

@[simp] theorem extend_tmul (n : ℕ) (f : W k g n →ₗ[k] M) (a : U k g) (z : W k g n) :
    extend k g M n f (a ⊗ₜ[k] z) = a • f z := rfl

/-- Evaluation on `1 ⊗ -`, regarded as a k-linear map. -/
def evaluate (n : ℕ) (F : V k g n →ₗ[U k g] M) : W k g n →ₗ[k] M :=
  (F.restrictScalars k).comp (TensorProduct.mk k (U k g) (W k g n) 1)

@[simp] theorem evaluate_apply (n : ℕ) (F : V k g n →ₗ[U k g] M) (z : W k g n) :
    evaluate k g M n F z = F ((1 : U k g) ⊗ₜ[k] z) := rfl

/-- The tensor-Hom adjunction for the free left U-module on Λⁿg. -/
noncomputable def homEquiv (n : ℕ) :
    (V k g n →ₗ[U k g] M) ≃ₗ[k] (W k g n →ₗ[k] M) where
  toFun := evaluate k g M n
  invFun := extend k g M n
  left_inv F := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a z
    simp only [extend_tmul, evaluate_apply]
    rw [← F.map_smul]
    congr 1
    rw [TensorProduct.smul_tmul']
    simp
  right_inv f := by ext z; simp
  map_add' F G := by ext z; rfl
  map_smul' r F := by ext z; rfl

@[simp] theorem homEquiv_apply (n : ℕ) (F : V k g n →ₗ[U k g] M) (z : W k g n) :
    homEquiv k g M n F z = F ((1 : U k g) ⊗ₜ[k] z) := rfl

@[simp] theorem homEquiv_symm_tmul (n : ℕ) (f : W k g n →ₗ[k] M)
    (a : U k g) (z : W k g n) :
    (homEquiv k g M n).symm f (a ⊗ₜ[k] z) = a • f z := rfl

/-- The comparison commutes with every coefficient morphism. -/
theorem homEquiv_natural (N : Type w') [AddCommGroup N] [Module k N]
    [Module (U k g) N] [IsScalarTower k (U k g) N]
    (h : M →ₗ[U k g] N) (n : ℕ) (F : V k g n →ₗ[U k g] M) :
    homEquiv k g N n (h.comp F) = (h.restrictScalars k).comp (homEquiv k g M n F) := by
  ext z
  rfl

/-- Transfer precomposition along the comparison equivalence. -/
noncomputable def coboundary (d : BoundaryFamily k g) (n : ℕ) :
    (W k g n →ₗ[k] M) →ₗ[k] (W k g (n+1) →ₗ[k] M) where
  toFun f := homEquiv k g M (n+1) (((homEquiv k g M n).symm f).comp (d n))
  map_add' f h := by ext z; simp
  map_smul' r f := by ext z; simp

@[simp] theorem coboundary_comparison (d : BoundaryFamily k g) (n : ℕ)
    (F : V k g n →ₗ[U k g] M) :
    coboundary k g M d n (homEquiv k g M n F) =
      homEquiv k g M (n+1) (homCoboundary k g M d n F) := by
  simp [coboundary, homCoboundary]

/-- Transfer of square zero needs no exactness or projectivity. -/
theorem coboundary_squared (d : BoundaryFamily k g)
    (hd : ∀ n, (d n).comp (d (n+1)) = 0) (n : ℕ) :
    (coboundary k g M d (n+1)).comp (coboundary k g M d n) = 0 := by
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro z
  change homEquiv k g M (n+2)
    (((homEquiv k g M (n+1)).symm
      (homEquiv k g M (n+1) (((homEquiv k g M n).symm f).comp (d n)))).comp
        (d (n+1))) z = 0
  rw [LinearEquiv.symm_apply_apply, LinearMap.comp_assoc, hd n, LinearMap.comp_zero]
  simp

/-- The exact action-plus-bracket formula follows from the chain formula. -/
theorem coboundary_formula (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d)
    (n : ℕ) (f : W k g n →ₗ[k] M) (x : Fin (n+1) → g) :
    coboundary k g M d n f (wedge k g (n+1) x) =
      cochainActionSum k g M n f x + cochainBracketSum k g M n f x := by
  change (homEquiv k g M n).symm f
    (d n ((1 : U k g) ⊗ₜ[k] wedge k g (n+1) x)) = _
  rw [hd, map_add]
  congr 1
  · simp only [actionSum, map_sum, map_zsmul, homEquiv_symm_tmul,
      one_mul, cochainActionSum]
  · cases n with
    | zero => simp [bracketSum, cochainBracketSum]
    | succ n =>
      simp only [bracketSum, cochainBracketSum, map_sum, map_zsmul,
        homEquiv_symm_tmul, one_smul]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Seed for the alternating single-removal operation. -/
def actionSeed (n : ℕ) (a : U k g) :
    g →ₗ[k] g [⋀^Fin n]→ₗ[k] V k g n where
  toFun x := (TensorProduct.mk k (U k g) (W k g n)
    (a * Shared.Lie.inclusion k g x)).compAlternatingMap (wedge k g n)
  map_add' x y := by
    ext z
    simp [mul_add]
  map_smul' r x := by
    ext z
    simp [Algebra.mul_smul_comm, TensorProduct.smul_tmul']

/-- The action part descends to exterior powers without any division. -/
def actionAlternating (n : ℕ) (a : U k g) : g [⋀^Fin (n+1)]→ₗ[k] V k g n :=
  AlternatingMap.alternatizeUncurryFin (actionSeed k g n a)

theorem actionAlternating_apply (n : ℕ) (a : U k g) (x : Fin (n+1) → g) :
    actionAlternating k g n a x = actionSum k g n a x := by
  simp only [actionAlternating, AlternatingMap.alternatizeUncurryFin_apply,
    actionSeed, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.compAlternatingMap_apply,
    TensorProduct.mk_apply, actionSum]

@[simp] theorem augmentation_tmul (a : U k g) (z : W k g 0) :
    augmentation k g (a ⊗ₜ[k] z) =
      Shared.Lie.augmentation k g a * exteriorPower.zeroEquiv k g z := rfl

/-- Compatibility with the U-action defined on k by its augmentation. -/
theorem augmentation_smul (a : U k g) (z : V k g 0) :
    augmentation k g (a • z) = Shared.Lie.augmentation k g a * augmentation k g z := by
  induction z using TensorProduct.inductionOn with
  | tmul b z =>
    simp only [TensorProduct.smul_tmul', smul_eq_mul, augmentation_tmul, map_mul, mul_assoc]
  | add z w hz hw => simp only [smul_add, map_add, hz, hw, mul_add]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The single-removal operator as an actual U-linear map in every degree. -/
noncomputable def actionBoundary (n : ℕ) : V k g (n+1) →ₗ[U k g] V k g n :=
  extend k g (V k g n) (n+1)
    (exteriorPower.alternatingMapLinearEquiv (actionAlternating k g n 1))

theorem actionBoundary_tmul (n : ℕ) (a : U k g) (x : Fin (n+1) → g) :
    actionBoundary k g n (a ⊗ₜ[k] wedge k g (n+1) x) = actionSum k g n a x := by
  rw [actionBoundary, extend_tmul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    actionAlternating_apply]
  simp only [actionSum, Finset.smul_sum, TensorProduct.smul_tmul',
    smul_eq_mul, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact smul_comm a ((-1 : ℤ) ^ (i : ℕ)) (Shared.Lie.inclusion k g (x i))

/-- Exterior generators and pure tensors determine every U-linear map. -/
theorem boundary_ext {n : ℕ} {d e : V k g (n+1) →ₗ[U k g] V k g n}
    (h : ∀ a x, d (a ⊗ₜ[k] wedge k g (n+1) x) =
      e (a ⊗ₜ[k] wedge k g (n+1) x)) : d = e := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a
  have he : (TensorProduct.AlgebraTensorModule.curry d a) =
      (TensorProduct.AlgebraTensorModule.curry e a) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    exact h a
  exact DFunLike.congr_fun he

/-- The formula, if realized, has at most one realization. -/
theorem boundary_unique {d e : BoundaryFamily k g}
    (hd : HasBoundaryFormula k g d) (he : HasBoundaryFormula k g e) : d = e := by
  funext n
  apply boundary_ext
  intro a x
  rw [hd, he]

/-- In degree one the bracket sum is empty. -/
theorem boundary_degree_one (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d) :
    d 0 = actionBoundary k g 0 := by
  apply boundary_ext
  intro a x
  rw [hd, actionBoundary_tmul]
  simp [bracketSum]

/-- The augmentation kills every image in degree zero. -/
theorem augmentation_boundary (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d)
    (z : V k g 1) : augmentation k g (d 0 z) = 0 := by
  have h : (augmentation k g).comp ((d 0).restrictScalars k) = 0 := by
    apply TensorProduct.ext'
    intro a
    have he : (TensorProduct.curry
        ((augmentation k g).comp ((d 0).restrictScalars k)) a) = 0 := by
      apply exteriorPower.linearMap_ext
      apply AlternatingMap.ext
      intro x
      change augmentation k g (d 0 (a ⊗ₜ[k] wedge k g 1 x)) = 0
      rw [hd]
      simp [actionSum, bracketSum]
      change Shared.Lie.augmentation k g a *
        Shared.Lie.augmentation k g (Shared.Lie.inclusion k g (x 0)) = 0
      rw [(Shared.Lie.augmentation_properties k g).1, mul_zero]
    exact DFunLike.congr_fun he
  exact DFunLike.congr_fun h z

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v w w'
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The existence of the formula on exterior powers itself supplies its
alternation, including the repeated-input zero property in characteristic two. -/
theorem boundary_formula_alternating (d : BoundaryFamily k g)
    (hd : HasBoundaryFormula k g d) : HasAlternatingBoundary k g := by
  intro n a
  refine ⟨(((d n).restrictScalars k).comp
    (TensorProduct.mk k (U k g) (W k g (n+1)) a)).compAlternatingMap
      (wedge k g (n+1)), ?_⟩
  intro x
  exact hd n a x

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (U k g) M] [IsScalarTower k (U k g) M]

/-- Naturality of the inverse comparison on arbitrary coefficient maps. -/
theorem extend_natural (N : Type w') [AddCommGroup N] [Module k N]
    [Module (U k g) N] [IsScalarTower k (U k g) N]
    (h : M →ₗ[U k g] N) (n : ℕ) (f : W k g n →ₗ[k] M) :
    (homEquiv k g N n).symm ((h.restrictScalars k).comp f) =
      h.comp ((homEquiv k g M n).symm f) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a z
  simp

/-- The transferred coboundary is natural in every coefficient module. -/
theorem coboundary_natural (N : Type w') [AddCommGroup N] [Module k N]
    [Module (U k g) N] [IsScalarTower k (U k g) N]
    (h : M →ₗ[U k g] N) (d : BoundaryFamily k g) (n : ℕ)
    (f : W k g n →ₗ[k] M) :
    coboundary k g N d n ((h.restrictScalars k).comp f) =
      (h.restrictScalars k).comp (coboundary k g M d n f) := by
  change homEquiv k g N (n+1)
    (((homEquiv k g N n).symm ((h.restrictScalars k).comp f)).comp (d n)) = _
  rw [extend_natural]
  apply LinearMap.ext
  intro z
  rfl

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
universe u v w w'

theorem comparison_spec :
    Specs.AdvancedHomologicalAlgebra.CE.comparisonExpected.{u,v,w} := by
  intro k g _ _ _ M _ _ _ _ n
  exact ⟨homEquiv k g M n, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem cochain_spec : Specs.AdvancedHomologicalAlgebra.CE.cochainExpected.{u,v,w} := by
  intro k g _ _ _ M _ _ _ _ d hd hc
  exact ⟨homEquiv k g M, coboundary k g M d, fun _ _ _ => rfl,
    fun _ _ _ _ => rfl, coboundary_comparison k g M d,
    coboundary_squared k g M d hc.1, coboundary_formula k g M d hd⟩

theorem naturality_spec :
    Specs.AdvancedHomologicalAlgebra.CE.naturalityExpected.{u,v,w,w'} := by
  intro k g _ _ _ M _ _ _ _ N _ _ _ _ n eM eN hM hN h F
  apply LinearMap.ext
  intro z
  rw [hN]
  change h (F _) = h (eM F z)
  rw [hM]

theorem actionAlternating_spec :
    Specs.AdvancedHomologicalAlgebra.CE.actionAlternatingExpected.{u,v} := by
  intro k g _ _ _ n a
  exact ⟨actionAlternating k g n a, actionAlternating_apply k g n a⟩

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The first boundary, including its empty wedge. -/
theorem boundary_one_formula (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d)
    (a : U k g) (x : g) :
    d 0 (a ⊗ₜ[k] wedge k g 1 (fun _ => x)) =
      (a * Shared.Lie.inclusion k g x) ⊗ₜ[k] wedge k g 0 Fin.elim0 := by
  rw [hd]
  simp [actionSum, bracketSum]
  congr 2
  exact Subsingleton.elim _ _

/-- Degree two checks the printed negative sign on the bracket term. -/
theorem boundary_two_formula (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d)
    (a : U k g) (x y : g) :
    d 1 (a ⊗ₜ[k] wedge k g 2 ![x,y]) =
      ((a * Shared.Lie.inclusion k g x) ⊗ₜ[k] wedge k g 1 (fun _ => y)) -
      ((a * Shared.Lie.inclusion k g y) ⊗ₜ[k] wedge k g 1 (fun _ => x)) -
      (a ⊗ₜ[k] wedge k g 1 (fun _ => ⁅x,y⁆)) := by
  have hs (z : g) : (![z] : Fin 1 → g) = (fun _ => z) := by
    funext i
    fin_cases i
    rfl
  have hr : Fin.removeNth (1 : Fin 2) ![x,y] = (fun _ : Fin 1 => x) := by
    funext i
    fin_cases i
    rfl
  rw [hd]
  simp [actionSum, bracketSum, Fin.sum_univ_two, sub_eq_add_neg]
  congr 2

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The enveloping relation cancels the square on degree-two generators. -/
theorem boundary_square_two_on_generators (d : BoundaryFamily k g)
    (hd : HasBoundaryFormula k g d) (a : U k g) (x y : g) :
    d 0 (d 1 (a ⊗ₜ[k] wedge k g 2 ![x,y])) = 0 := by
  rw [boundary_two_formula k g d hd]
  simp only [map_sub, boundary_one_formula k g d hd]
  rw [← TensorProduct.sub_tmul, ← TensorProduct.sub_tmul]
  rw [mul_assoc, mul_assoc, ← mul_sub, ← mul_sub,
    (Shared.Lie.quotient k g).2 x y, sub_self, mul_zero, TensorProduct.zero_tmul]

/-- Square zero from degree two to zero for any family satisfying the formula. -/
theorem boundary_square_two (d : BoundaryFamily k g) (hd : HasBoundaryFormula k g d) :
    (d 0).comp (d 1) = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a
  have he : (TensorProduct.AlgebraTensorModule.curry ((d 0).comp (d 1)) a) = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    have hx : x = ![x 0,x 1] := by
      funext i
      fin_cases i <;> rfl
    change d 0 (d 1 (a ⊗ₜ[k] wedge k g 2 x)) = 0
    rw [hx]
    exact boundary_square_two_on_generators k g d hd a (x 0) (x 1)
  exact DFunLike.congr_fun he

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
universe u v

theorem augmentation_spec : Specs.AdvancedHomologicalAlgebra.CE.augmentationExpected.{u,v} := by
  intro k g _ _ _ d hd
  exact ⟨augmentation_boundary k g d hd, augmentation_smul k g⟩

theorem squareTwo_spec : Specs.AdvancedHomologicalAlgebra.CE.squareTwoExpected.{u,v} := by
  intro k g _ _ _ d hd
  exact boundary_square_two k g d hd

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- On a free module an alternating bilinear bracket is the difference of a
bilinear map and its transpose. Only an order on a basis is used: this does
not divide by two, even when the coefficient ring has characteristic two. -/
theorem exists_bracket_split [Module.Free k g] :
    ∃ f : g →ₗ[k] g →ₗ[k] g, ∀ x y, f x y - f y x = ⁅x,y⁆ := by
  classical
  let b := Module.Free.chooseBasis k g
  let := IsWellOrder.linearOrder (WellOrderingRel (α := Module.Free.ChooseBasisIndex k g))
  let f : g →ₗ[k] g →ₗ[k] g :=
    b.constr k (fun i => b.constr k (fun j => if i < j then ⁅b i,b j⁆ else 0))
  refine ⟨f, ?_⟩
  have h : f - f.flip = (LieAlgebra.ad k g).toLinearMap := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    change f (b i) (b j) - f (b j) (b i) = ⁅b i,b j⁆
    simp only [f, Module.Basis.constr_basis]
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt_of_gt hij]
    · simp
    · simp [hji, not_lt_of_gt hji, lie_skew]
  intro x y
  exact congrArg (fun F : g →ₗ[k] g →ₗ[k] g => F x y) h

/-- A choice of such a splitting, used only to construct the alternating map.
The final formula and uniqueness do not depend on the choice. -/
noncomputable def bracketSplit [Module.Free k g] : g →ₗ[k] g →ₗ[k] g :=
  Classical.choose (exists_bracket_split k g)

theorem bracketSplit_sub_flip [Module.Free k g] (x y : g) :
    bracketSplit k g x y - bracketSplit k g y x = ⁅x,y⁆ :=
  Classical.choose_spec (exists_bracket_split k g) x y

/-- The two distinguished variables are fed into the bilinear splitting;
the unused variables are already alternating. -/
noncomputable def bracketSeed [Module.Free k g] (n : ℕ) (a : U k g) :
    g →ₗ[k] g →ₗ[k] g [⋀^Fin n]→ₗ[k] V k g (n+1) :=
  (bracketSplit k g).compr₂
    (((TensorProduct.mk k (U k g) (W k g (n+1)) a).compAlternatingMap
      (wedge k g (n+1))).curryLeft)

/-- Twice uncurrying the triangular splitting enumerates each pair once
with its antisymmetric difference. The minus sign is the printed bracket
sign in the Chevalley--Eilenberg boundary. -/
noncomputable def bracketAlternating [Module.Free k g] :
    ∀ n : ℕ, U k g → g [⋀^Fin (n+1)]→ₗ[k] V k g n
  | 0, _ => 0
  | n+1, a => -AlternatingMap.alternatizeUncurryFin
      (AlternatingMap.alternatizeUncurryFinLM.comp (bracketSeed k g n a))

theorem bracketAlternating_apply [Module.Free k g] (n : ℕ) (a : U k g)
    (x : Fin (n+1) → g) :
    bracketAlternating k g n a x = bracketSum k g n a x := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [bracketAlternating, neg_apply,
      AlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinLM_comp_apply,
      bracketSum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hdiff :
        bracketSeed k g n a (x i.castSucc) (x j.succ)
            (j.removeNth (i.castSucc.removeNth x)) -
          bracketSeed k g n a (x j.succ) (x i.castSucc)
            (j.removeNth (i.castSucc.removeNth x)) =
          a ⊗ₜ[k] wedge k g (n+1)
            (Fin.cons ⁅x i.castSucc, x j.succ⁆
              (j.removeNth (i.castSucc.removeNth x))) := by
      let C := ((TensorProduct.mk k (U k g) (W k g (n+1)) a).compAlternatingMap
        (wedge k g (n+1))).curryLeft
      change C (bracketSplit k g (x i.castSucc) (x j.succ)) _ -
        C (bracketSplit k g (x j.succ) (x i.castSucc)) _ = _
      have hh := congrArg
        (fun F : g [⋀^Fin n]→ₗ[k] V k g (n+1) =>
          F (j.removeNth (i.castSucc.removeNth x)))
        (C.map_sub (bracketSplit k g (x i.castSucc) (x j.succ))
          (bracketSplit k g (x j.succ) (x i.castSucc)))
      rw [bracketSplit_sub_flip] at hh
      exact hh.symm
    rw [hdiff, pow_succ, mul_neg_one, neg_smul]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

/-- The bracket insertion as a genuine left U-linear map on exterior powers. -/
noncomputable def bracketBoundary (n : ℕ) : V k g (n+1) →ₗ[U k g] V k g n :=
  extend k g (V k g n) (n+1)
    (exteriorPower.alternatingMapLinearEquiv (bracketAlternating k g n 1))

theorem bracketBoundary_tmul (n : ℕ) (a : U k g) (x : Fin (n+1) → g) :
    bracketBoundary k g n (a ⊗ₜ[k] wedge k g (n+1) x) = bracketSum k g n a x := by
  rw [bracketBoundary, extend_tmul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    bracketAlternating_apply]
  cases n with
  | zero => simp [bracketSum]
  | succ n =>
    simp only [bracketSum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_comm a, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The Chevalley--Eilenberg boundary, constructed in all degrees. -/
noncomputable def boundary (n : ℕ) : V k g (n+1) →ₗ[U k g] V k g n :=
  actionBoundary k g n + bracketBoundary k g n

theorem boundary_formula : HasBoundaryFormula k g (boundary k g) := by
  intro n a x
  exact congrArg₂ (· + ·) (actionBoundary_tmul k g n a x)
    (bracketBoundary_tmul k g n a x)

theorem hasAlternatingBoundary : HasAlternatingBoundary k g :=
  boundary_formula_alternating k g (boundary k g) (boundary_formula k g)

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Single-removal action on a wedge with a distinguished initial factor. -/
theorem actionBoundary_cons (n : ℕ) (a : U k g) (y : g) (x : Fin (n+1) → g) :
    actionBoundary k g (n+1) (a ⊗ₜ[k] wedge k g (n+2) (Fin.cons y x)) =
      (a * Shared.Lie.inclusion k g y) ⊗ₜ[k] wedge k g (n+1) x -
      ∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) •
        ((a * Shared.Lie.inclusion k g (x i)) ⊗ₜ[k]
          wedge k g (n+1) (Fin.cons y (i.removeNth x))) := by
  have hr (i : Fin (n+1)) :
      i.succ.removeNth (show Fin (n+2) → g from Fin.cons y x) =
        @Fin.cons n (fun _ => g) y (i.removeNth x) := by
    exact Fin.cons_comp_succ_succAbove _ _ _
  rw [actionBoundary_tmul, actionSum, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.removeNth_zero,
    Fin.tail_cons, Fin.val_zero, pow_zero, one_smul, Fin.cons_succ, Fin.val_succ,
    pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg, hr]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- Exterior multiplication by a distinguished vector, on the left. -/
noncomputable def wedgeInsert (n : ℕ) (y : g) : W k g n →ₗ[k] W k g (n+1) :=
  exteriorPower.alternatingMapLinearEquiv ((wedge k g (n+1)).curryLeft y)

@[simp] theorem wedgeInsert_wedge (n : ℕ) (y : g) (x : Fin n → g) :
    wedgeInsert k g n y (wedge k g n x) = wedge k g (n+1) (Fin.cons y x) := by
  rw [wedgeInsert, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- Exterior multiplication on the exterior tensor factor. -/
noncomputable def insert (n : ℕ) (y : g) : V k g n →ₗ[U k g] V k g (n+1) :=
  extend k g (V k g (n+1)) n
    ((TensorProduct.mk k (U k g) (W k g (n+1)) 1).comp (wedgeInsert k g n y))

@[simp] theorem insert_tmul (n : ℕ) (y : g) (a : U k g) (z : W k g n) :
    insert k g n y (a ⊗ₜ[k] z) = a ⊗ₜ[k] wedgeInsert k g n y z := by
  simp [insert, TensorProduct.smul_tmul']

@[simp] theorem insert_wedge (n : ℕ) (y : g) (a : U k g) (x : Fin n → g) :
    insert k g n y (a ⊗ₜ[k] wedge k g n x) =
      a ⊗ₜ[k] wedge k g (n+1) (Fin.cons y x) := by
  simp

/-- Right multiplication on the enveloping factor commutes with its left action. -/
noncomputable def rightAction (n : ℕ) (y : g) : V k g n →ₗ[U k g] V k g n :=
  extend k g (V k g n) n (TensorProduct.mk k (U k g) (W k g n)
    (Shared.Lie.inclusion k g y))

@[simp] theorem rightAction_tmul (n : ℕ) (y : g) (a : U k g) (z : W k g n) :
    rightAction k g n y (a ⊗ₜ[k] z) = (a * Shared.Lie.inclusion k g y) ⊗ₜ[k] z := by
  simp [rightAction, TensorProduct.smul_tmul']

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v w
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
variable {P : Type w} [AddCommGroup P] [Module k P] [Module (U k g) P]
  [IsScalarTower k (U k g) P]

/-- Pure exterior tensors determine every map to a compatible module. -/
theorem tensor_wedge_ext {n : ℕ} {F G : V k g n →ₗ[U k g] P}
    (h : ∀ a x, F (a ⊗ₜ[k] wedge k g n x) = G (a ⊗ₜ[k] wedge k g n x)) : F = G := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a
  have he : TensorProduct.AlgebraTensorModule.curry F a =
      TensorProduct.AlgebraTensorModule.curry G a := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    exact h a
  exact DFunLike.congr_fun he

/-- Exterior tensors in positive degree are generated by left insertion. -/
theorem insert_ext {n : ℕ} {F G : V k g (n+1) →ₗ[U k g] P}
    (h : ∀ y, F.comp (insert k g n y) = G.comp (insert k g n y)) : F = G := by
  apply tensor_wedge_ext k g
  intro a x
  have he := DFunLike.congr_fun (h (x 0)) (a ⊗ₜ[k] wedge k g n (Fin.tail x))
  simpa only [LinearMap.comp_apply, insert_wedge, Fin.cons_self_tail] using he

/-- The right action commutes with exterior multiplication. -/
theorem rightAction_insert (n : ℕ) (x y : g) :
    (rightAction k g (n+1) x).comp (insert k g n y) =
      (insert k g n y).comp (rightAction k g n x) := by
  apply tensor_wedge_ext k g
  intro a z
  simp only [LinearMap.comp_apply, insert_wedge, rightAction_tmul]

/-- Right multiplication is the opposite Lie action. -/
theorem rightAction_commutator (n : ℕ) (x y : g) :
    (rightAction k g n x).comp (rightAction k g n y) -
      (rightAction k g n y).comp (rightAction k g n x) =
        -rightAction k g n ⁅x,y⁆ := by
  apply tensor_wedge_ext k g
  intro a z
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, rightAction_tmul,
    LinearMap.neg_apply]
  rw [← TensorProduct.sub_tmul, mul_assoc, mul_assoc, ← mul_sub]
  rw [show Shared.Lie.inclusion k g y * Shared.Lie.inclusion k g x -
      Shared.Lie.inclusion k g x * Shared.Lie.inclusion k g y =
        -Shared.Lie.inclusion k g ⁅x,y⁆ by
    rw [← neg_sub, (Shared.Lie.quotient k g).2]]
  rw [mul_neg, TensorProduct.neg_tmul]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE.Cartan
universe u v w
variable {k : Type u} [Ring k] {g : Type v} [LieRing g]
variable (N : ℕ → Type w) [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]
variable (d : ∀ n, N (n+1) →ₗ[k] N n)
variable (I : ∀ n, g → N n →ₗ[k] N (n+1))
variable (T : ∀ n, g → N n →ₗ[k] N n)
variable
  (extI : ∀ n m {f h : N (n+1) →ₗ[k] N m},
    (∀ x z, f (I n x z) = h (I n x z)) → f = h)
  (h0 : ∀ x z, d 0 (I 0 x z) = T 0 x z)
  (hC : ∀ n x z, d (n+1) (I (n+1) x z) =
    T (n+1) x z - I n x (d n z))
  (hTI : ∀ n x y z, T (n+1) x (I n y z) =
    I n y (T n x z) - I n ⁅x,y⁆ z)
  (hTT : ∀ n x y z, T n x (T n y z) - T n y (T n x z) =
    -T n ⁅x,y⁆ z)

include I T extI h0 hC hTI hTT
theorem boundary_commutes_of_cartan : ∀ n x z, d n (T (n+1) x z) = T n x (d n z) := by
  intro n
  induction n with
  | zero =>
    intro x
    have h : (d 0).comp (T 1 x) = (T 0 x).comp (d 0) := by
      apply extI 0 0
      intro y z
      simp only [LinearMap.comp_apply, hTI, map_sub, h0]
      have ht := hTT 0 x y z
      rw [sub_eq_iff_eq_add.mp ht]
      abel
    exact fun z => LinearMap.congr_fun h z
  | succ n ih =>
    intro x
    have h : (d (n+1)).comp (T (n+2) x) = (T (n+1) x).comp (d (n+1)) := by
      apply extI (n+1) (n+1)
      intro y z
      simp only [LinearMap.comp_apply, hTI, map_sub, hC, ih]
      have ht := hTT (n+1) x y z
      rw [sub_eq_iff_eq_add.mp ht]
      abel
    exact fun z => LinearMap.congr_fun h z

theorem boundary_squared_of_cartan :
    ∀ n, (d n).comp (d (n+1)) = 0 := by
  have hcomm := boundary_commutes_of_cartan N d I T extI h0 hC hTI hTT
  intro n
  induction n with
  | zero =>
    apply extI 1 0
    intro x z
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hC, map_sub, h0, hcomm,
      sub_self]
  | succ n ih =>
    apply extI (n+2) (n+1)
    intro x z
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, hC, map_sub, hcomm]
    have hz := LinearMap.congr_fun ih z
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hz
    rw [hz, map_zero, sub_zero, sub_self]

end AdvancedHomologicalAlgebra.CE.Cartan

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

lemma swap_cons (n : ℕ) (y z : g) (x : Fin n → g) :
    wedge k g (n+2) (Fin.cons z (Fin.cons y x)) =
      -wedge k g (n+2) (Fin.cons y (Fin.cons z x)) := by
  have he : (Fin.cons y (Fin.cons z x)) ∘ Equiv.swap (0 : Fin (n+2)) 1 =
      Fin.cons z (Fin.cons y x) := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ i =>
      cases i using Fin.cases with
      | zero => simp
      | succ i =>
        simp only [Function.comp_apply]
        have hne : i.succ.succ ≠ (1 : Fin (n+2)) := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
        rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hne]
        rfl
  rw [← he]
  exact (wedge k g (n+2)).map_swap _ Fin.zero_ne_one

lemma bracketSum_cons_aux (n : ℕ) (a : U k g) (y : g) (x : Fin (n+1) → g)
    (C : V k g n →ₗ[k] V k g (n+1))
    (hC : ∀ z : Fin n → g, C (a ⊗ₜ[k] wedge k g n z) =
      a ⊗ₜ[k] wedge k g (n+1) (Fin.cons y z)) :
    bracketSum k g (n+1) a (Fin.cons y x) =
      -(∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) •
        (a ⊗ₜ[k] wedge k g (n+1) (Fin.cons ⁅y, x i⁆ (i.removeNth x)))) -
        C (bracketSum k g n a x) := by
  cases n with
  | zero => simp [bracketSum]
  | succ n =>
    have hzero : Finset.Ici (0 : Fin (n+2)) = Finset.univ := by
      ext i
      simp
    rw [bracketSum, Fin.sum_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.val_zero, zero_add,
      hzero, Fin.removeNth_zero, Fin.tail_cons, Fin.cons_succ]
    rw [sub_eq_add_neg]
    congr 1
    · simp only [pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    · simp only [bracketSum, map_sum, map_zsmul, hC, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Fin.finsetImage_succ_Ici i, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro j hj
        have hr (i : Fin (n+2)) :
            i.succ.removeNth (show Fin (n+3) → g from Fin.cons y x) =
              @Fin.cons (n+1) (fun _ => g) y (i.removeNth x) := by
          exact Fin.cons_comp_succ_succAbove _ _ _
        simp only [Fin.castSucc_succ, Fin.cons_succ, hr]
        have hr' (z : Fin (n+1) → g) (j : Fin (n+1)) :
            j.succ.removeNth (show Fin (n+2) → g from Fin.cons y z) =
              @Fin.cons n (fun _ => g) y (j.removeNth z) := by
          exact Fin.cons_comp_succ_succAbove _ _ _
        rw [hr', swap_cons, TensorProduct.tmul_neg, smul_neg]
        congr 2
        simp only [Fin.val_succ]
        rw [show (i.val+1)+(j.val+1)+1 = (i.val+j.val+1)+2 by omega, pow_add]
        norm_num
      · intro j hj l hl h
        exact Fin.succ_injective _ h
end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE.Cartan
universe u v w
variable {k : Type u} [Ring k] {g : Type v} [LieRing g]
variable (N : ℕ → Type w) [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]
variable (I : ∀ n, g → N n →ₗ[k] N (n+1))
variable (T : ∀ n, g → N n →ₗ[k] N n)

theorem operators_commutator_of_insert
  (extI : ∀ n m {f h : N (n+1) →ₗ[k] N m},
    (∀ x z, f (I n x z) = h (I n x z)) → f = h)
  (hTI : ∀ n x y z, T (n+1) x (I n y z) =
    I n y (T n x z) - I n ⁅x,y⁆ z)
  (hTT0 : ∀ x y z, T 0 x (T 0 y z) - T 0 y (T 0 x z) =
    -T 0 ⁅x,y⁆ z)
  (hIadd : ∀ n (x y : g) (w : N n), I n (x+y) w = I n x w + I n y w)
  (hIneg : ∀ n (x : g) (w : N n), I n (-x) w = -I n x w) :
    ∀ n x y z, T n x (T n y z) - T n y (T n x z) =
      -T n ⁅x,y⁆ z := by
  have hIJ : ∀ n (x y z : g) (w : N n),
      I n ⁅x,⁅y,z⁆⁆ w - I n ⁅y,⁅x,z⁆⁆ w = I n ⁅⁅x,y⁆,z⁆ w := by
    intro n x y z w
    rw [lie_lie]
    simp only [sub_eq_add_neg, hIadd, hIneg]
  intro n
  induction n with
  | zero => exact hTT0
  | succ n ih =>
    intro x y
    have h : (T (n+1) x).comp (T (n+1) y) -
        (T (n+1) y).comp (T (n+1) x) = -T (n+1) ⁅x,y⁆ := by
      apply extI n (n+1)
      intro z w
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        hTI, map_sub]
      calc
        _ = I n z (T n x (T n y w) - T n y (T n x w)) +
            (I n ⁅x,⁅y,z⁆⁆ w - I n ⁅y,⁅x,z⁆⁆ w) := by
          simp only [map_sub]
          abel
        _ = -I n z (T n ⁅x,y⁆ w) + I n ⁅⁅x,y⁆,z⁆ w := by
          rw [ih, map_neg, hIJ]
        _ = _ := by abel
    exact fun z => LinearMap.congr_fun h z

end AdvancedHomologicalAlgebra.CE.Cartan

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
theorem actionBoundary_insert (n : ℕ) (y : g) (z : V k g (n+1)) :
    actionBoundary k g (n+1) (insert k g (n+1) y z) =
      rightAction k g (n+1) y z - insert k g n y (actionBoundary k g n z) := by
  have h : (actionBoundary k g (n+1)).comp (insert k g (n+1) y) =
      rightAction k g (n+1) y - (insert k g n y).comp (actionBoundary k g n) := by
    apply tensor_wedge_ext k g
    intro a x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, insert_wedge, rightAction_tmul]
    rw [actionBoundary_cons, actionBoundary_tmul]
    simp only [actionSum, map_sum, map_zsmul, insert_wedge]
  exact DFunLike.congr_fun h z

theorem wedgeInsert_add (n : ℕ) (x y : g) :
    wedgeInsert k g n (x+y) = wedgeInsert k g n x + wedgeInsert k g n y := by
  simp only [wedgeInsert, map_add]

theorem wedgeInsert_neg (n : ℕ) (x : g) :
    wedgeInsert k g n (-x) = -wedgeInsert k g n x := by
  simp only [wedgeInsert, map_neg]

theorem insert_add (n : ℕ) (x y : g) :
    insert k g n (x+y) = insert k g n x + insert k g n y := by
  apply tensor_wedge_ext k g
  intro a z
  simp only [insert_tmul, wedgeInsert_add, LinearMap.add_apply, TensorProduct.tmul_add]

theorem insert_neg (n : ℕ) (x : g) :
    insert k g n (-x) = -insert k g n x := by
  apply tensor_wedge_ext k g
  intro a z
  simp only [insert_tmul, wedgeInsert_neg, LinearMap.neg_apply, TensorProduct.tmul_neg]

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
theorem bracketBoundary_cons [Module.Free k g] (n : ℕ) (a : U k g)
    (y : g) (x : Fin (n+1) → g) :
    bracketBoundary k g (n+1) (a ⊗ₜ[k] wedge k g (n+2) (Fin.cons y x)) =
      -(∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) •
        (a ⊗ₜ[k] wedge k g (n+1) (Fin.cons ⁅y, x i⁆ (i.removeNth x)))) -
        insert k g n y (bracketBoundary k g n (a ⊗ₜ[k] wedge k g (n+1) x)) := by
  rw [bracketBoundary_tmul, bracketBoundary_tmul]
  exact bracketSum_cons_aux k g n a y x ((insert k g n y).restrictScalars k)
    (insert_wedge k g n y a)
end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
universe u v w
variable {k : Type u} {M : Type v} {N : Type w}
variable [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
variable {n : ℕ}

noncomputable def alternatingDerivML (f : M [⋀^Fin n]→ₗ[k] N) (D : Module.End k M) :
    MultilinearMap k (fun _ : Fin n => M) N := by
  classical
  exact ∑ i : Fin n, f.toMultilinearMap.compLinearMap (fun j => if i = j then D else LinearMap.id)

lemma alternatingDerivML_apply (f : M [⋀^Fin n]→ₗ[k] N) (D : Module.End k M) (x : Fin n → M) :
    alternatingDerivML f D x = ∑ i : Fin n, f (Function.update x i (D (x i))) := by
  classical
  simp only [alternatingDerivML, sum_apply, MultilinearMap.compLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg (fun z : Fin n → M => f z)
  funext j
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

noncomputable def alternatingDeriv (f : M [⋀^Fin n]→ₗ[k] N) (D : Module.End k M) :
    M [⋀^Fin n]→ₗ[k] N := by
  classical
  refine { toMultilinearMap := alternatingDerivML f D, map_eq_zero_of_eq' := ?_ }
  intro x i j h hij
  change alternatingDerivML f D x = 0
  rw [alternatingDerivML_apply]
  have ho : ∀ l ∈ (Finset.univ.erase i).erase j,
      f (Function.update x l (D (x l))) = 0 := by
    intro l hl
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    apply f.map_eq_zero_of_eq _ _ hij
    simpa [Function.update_of_ne (Ne.symm hli), Function.update_of_ne (Ne.symm hlj)] using h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  rw [← Finset.add_sum_erase _ _ (by simp [hij.symm] : j ∈ Finset.univ.erase i)]
  rw [Finset.sum_eq_zero ho, add_zero]
  have heq : Function.update x i (D (x i)) ∘ Equiv.swap i j = Function.update x j (D (x j)) := by
    ext l
    by_cases hli : l = i
    · subst l; simp [hij, hij.symm, h]
    by_cases hlj : l = j
    · subst l; simp [h]
    · simp [Equiv.swap_apply_of_ne_of_ne hli hlj, hli, hlj]
  have hs := f.map_add_swap (Function.update x i (D (x i))) hij
  rwa [heq] at hs

@[simp] lemma alternatingDeriv_apply (f : M [⋀^Fin n]→ₗ[k] N) (D : Module.End k M) (x : Fin n → M) :
    alternatingDeriv f D x = ∑ i : Fin n, f (Function.update x i (D (x i))) :=
  alternatingDerivML_apply f D x

noncomputable def wedgeDeriv (n : ℕ) (D : Module.End k M) : ⋀[k]^n M →ₗ[k] ⋀[k]^n M :=
  exteriorPower.alternatingMapLinearEquiv (alternatingDeriv (exteriorPower.ιMulti k n) D)

@[simp] lemma wedgeDeriv_wedge (n : ℕ) (D : Module.End k M) (x : Fin n → M) :
    wedgeDeriv n D (exteriorPower.ιMulti k n x) =
      ∑ i : Fin n, exteriorPower.ιMulti k n (Function.update x i (D (x i))) := by
  simp [wedgeDeriv]

end AdvancedHomologicalAlgebra.CE
namespace AdvancedHomologicalAlgebra.CE
universe u v
variable {k : Type u} {M : Type v}
variable [CommRing k] [LieRing M] [LieAlgebra k M]

lemma wedgeDeriv_cons (n : ℕ) (D : Module.End k M) (y : M) (x : Fin n → M) :
    wedgeDeriv (n+1) D (exteriorPower.ιMulti k (n+1) (Fin.cons y x)) =
      exteriorPower.ιMulti k (n+1) (Fin.cons (D y) x) +
        wedgeInsert k M n y (wedgeDeriv n D (exteriorPower.ιMulti k n x)) := by
  classical
  have h0 : Function.update (show Fin (n+1) → M from Fin.cons y x) 0 (D y) = @Fin.cons n (fun _ => M) (D y) x := by
    ext i; cases i using Fin.cases <;> simp
  have hs (i : Fin n) :
      Function.update (show Fin (n+1) → M from Fin.cons y x) i.succ (D (x i)) =
        @Fin.cons n (fun _ => M) y (Function.update x i (D (x i))) := by
    ext j; cases j using Fin.cases with
    | zero => simp [Function.update_of_ne (Fin.succ_ne_zero i).symm]
    | succ j => by_cases h : j = i <;> simp [h]
  simp only [wedgeDeriv_wedge, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    map_sum, wedgeInsert_wedge, h0, hs]

lemma wedgeDeriv_insert (n : ℕ) (D : Module.End k M) (y : M) (z : ⋀[k]^n M) :
    wedgeDeriv (n+1) D (wedgeInsert k M n y z) =
      wedgeInsert k M n (D y) z + wedgeInsert k M n y (wedgeDeriv n D z) := by
  have heq : (wedgeDeriv (n+1) D).comp (wedgeInsert k M n y) =
      wedgeInsert k M n (D y) + (wedgeInsert k M n y).comp (wedgeDeriv n D) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.add_apply, wedgeInsert_wedge] using wedgeDeriv_cons n D y x
  exact DFunLike.congr_fun heq z

@[simp] lemma wedgeDeriv_zero (D : Module.End k M) : wedgeDeriv 0 D = 0 := by
  apply exteriorPower.linearMap_ext
  ext x
  simp

lemma wedgeDeriv_wedge_remove (n : ℕ) (D : Module.End k M) (x : Fin (n+1) → M) :
    wedgeDeriv (n+1) D (exteriorPower.ιMulti k (n+1) x) =
      ∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) •
        exteriorPower.ιMulti k (n+1) (Fin.cons (D (x i)) (i.removeNth x)) := by
  classical
  rw [wedgeDeriv_wedge]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.insertNth_removeNth i (D (x i)) x]
  exact (exteriorPower.ιMulti k (n+1)).map_insertNth i (D (x i)) (i.removeNth x)

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

noncomputable def exteriorAction (n : ℕ) (y : g) : V k g n →ₗ[U k g] V k g n :=
  extend k g (V k g n) n
    ((TensorProduct.mk k (U k g) (W k g n) 1).comp (wedgeDeriv n (LieAlgebra.ad k g y)))

@[simp] theorem exteriorAction_tmul (n : ℕ) (y : g) (a : U k g) (z : W k g n) :
    exteriorAction k g n y (a ⊗ₜ[k] z) = a ⊗ₜ[k] wedgeDeriv n (LieAlgebra.ad k g y) z := by
  simp [exteriorAction, TensorProduct.smul_tmul']

@[simp] theorem exteriorAction_zero (y : g) : exteriorAction k g 0 y = 0 := by
  apply tensor_wedge_ext k g
  intro a x
  simp

noncomputable def lieAction (n : ℕ) (y : g) : V k g n →ₗ[U k g] V k g n :=
  rightAction k g n y - exteriorAction k g n y

@[simp] theorem lieAction_zero (y : g) : lieAction k g 0 y = rightAction k g 0 y := by
  rw [lieAction, exteriorAction_zero]
  apply LinearMap.ext
  intro z
  simp only [LinearMap.sub_apply, LinearMap.zero_apply]
  exact sub_zero _

theorem exteriorAction_insert (n : ℕ) (x y : g) (z : V k g n) :
    exteriorAction k g (n+1) x (insert k g n y z) =
      insert k g n ⁅x,y⁆ z + insert k g n y (exteriorAction k g n x z) := by
  have heq : (exteriorAction k g (n+1) x).comp (insert k g n y) =
      insert k g n ⁅x,y⁆ + (insert k g n y).comp (exteriorAction k g n x) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a w
    simp only [LinearMap.comp_apply, LinearMap.add_apply, insert_tmul, exteriorAction_tmul,
      wedgeDeriv_insert, TensorProduct.tmul_add]
    rfl
  exact DFunLike.congr_fun heq z

theorem lieAction_insert (n : ℕ) (x y : g) (z : V k g n) :
    lieAction k g (n+1) x (insert k g n y z) =
      insert k g n y (lieAction k g n x z) - insert k g n ⁅x,y⁆ z := by
  have hr := DFunLike.congr_fun (rightAction_insert k g n x y) z
  simp only [LinearMap.comp_apply] at hr
  simp only [lieAction, LinearMap.sub_apply, exteriorAction_insert, hr, map_sub]
  abel

theorem lieAction_commutator_zero (x y : g) (z : V k g 0) :
    lieAction k g 0 x (lieAction k g 0 y z) -
      lieAction k g 0 y (lieAction k g 0 x z) = -lieAction k g 0 ⁅x,y⁆ z := by
  simpa only [lieAction_zero, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.neg_apply] using
    DFunLike.congr_fun (rightAction_commutator k g 0 x y) z

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
open scoped TensorProduct
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]
  [Module.Free k g]

theorem boundary_insert_zero (y : g) (z : V k g 0) :
    boundary k g 0 (insert k g 0 y z) = rightAction k g 0 y z := by
  have h : (boundary k g 0).comp (insert k g 0 y) = rightAction k g 0 y := by
    apply tensor_wedge_ext k g
    intro a x
    rw [LinearMap.comp_apply, insert_wedge, boundary_formula]
    simp [actionSum, bracketSum]
  exact DFunLike.congr_fun h z

theorem boundary_insert (n : ℕ) (y : g) (z : V k g (n+1)) :
    boundary k g (n+1) (insert k g (n+1) y z) =
      lieAction k g (n+1) y z - insert k g n y (boundary k g n z) := by
  let E := extend k g (V k g (n+1)) (n+1)
        ((TensorProduct.mk k (U k g) (W k g (n+1)) 1).comp
          (wedgeDeriv (n+1) (LieAlgebra.ad k g y)))
  change boundary k g (n+1) (insert k g (n+1) y z) =
    rightAction k g (n+1) y z - E z - insert k g n y (boundary k g n z)
  have h : (boundary k g (n+1)).comp (insert k g (n+1) y) =
      rightAction k g (n+1) y - E - (insert k g n y).comp (boundary k g n) := by
    apply tensor_wedge_ext k g
    intro a x
    simp only [boundary, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply]
    rw [actionBoundary_insert, insert_wedge, bracketBoundary_cons]
    have hE : E (a ⊗ₜ[k] wedge k g (n+1) x) =
        ∑ i : Fin (n+1), (-1 : ℤ)^(i : ℕ) •
          (a ⊗ₜ[k] wedge k g (n+1) (Fin.cons ⁅y,x i⁆ (i.removeNth x))) := by
      change exteriorAction k g (n+1) y (a ⊗ₜ[k] wedge k g (n+1) x) = _
      rw [exteriorAction_tmul, wedgeDeriv_wedge_remove]
      simp only [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact map_zsmul (TensorProduct.mk k (U k g) (W k g (n+1)) a) _ _
    rw [hE, map_add]
    abel
  exact DFunLike.congr_fun h z
end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE
universe u v
variable (k : Type u) (g : Type v) [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The diagonal operation is the opposite Lie action in every degree. -/
theorem lieAction_commutator (n : ℕ) (x y : g) (z : V k g n) :
    lieAction k g n x (lieAction k g n y z) -
      lieAction k g n y (lieAction k g n x z) = -lieAction k g n ⁅x,y⁆ z := by
  apply Cartan.operators_commutator_of_insert (V k g) (insert k g) (lieAction k g)
    (fun n m {F G} h => insert_ext k g (fun y => LinearMap.ext (h y)))
    (lieAction_insert k g) (lieAction_commutator_zero k g)
    (fun n x y z => DFunLike.congr_fun (insert_add k g n x y) z)
    (fun n x z => DFunLike.congr_fun (insert_neg k g n x) z)

/-- Cartan recursion proves square zero without any division or rank bound. -/
theorem boundary_squared [Module.Free k g] (n : ℕ) :
    (boundary k g n).comp (boundary k g (n+1)) = 0 := by
  apply Cartan.boundary_squared_of_cartan (V k g) (boundary k g) (insert k g)
    (lieAction k g)
    (fun n m {F G} h => insert_ext k g (fun y => LinearMap.ext (h y)))
    (fun y z => by simpa only [lieAction_zero] using boundary_insert_zero k g y z)
    (boundary_insert k g) (lieAction_insert k g) (lieAction_commutator k g)

/-- The actual Chevalley--Eilenberg boundary gives the augmented complex. -/
theorem boundary_augmented [Module.Free k g] :
    IsAugmentedComplex k g (boundary k g) :=
  ⟨boundary_squared k g, augmentation_boundary k g (boundary k g) (boundary_formula k g),
    augmentation_smul k g⟩

/-- Complete independent specification for the all-degree construction. -/
theorem complex_spec : Specs.AdvancedHomologicalAlgebra.CE.complexExpected.{u,v} := by
  intro k g _ _ _ _
  exact ⟨hasAlternatingBoundary k g, boundary k g, boundary_formula k g,
    boundary_augmented k g⟩

end AdvancedHomologicalAlgebra.CE

namespace AdvancedHomologicalAlgebra.CE

universe u v w

/-- The augmented Chevalley–Eilenberg boundary with its defining formula. -/
noncomputable def boundaryData :
    Specs.AdvancedHomologicalAlgebra.CE.boundaryDataExpected.{u,v} :=
  fun k g _ _ _ _ =>
    { differential := boundary k g
      formula := boundary_formula k g
      augmented := boundary_augmented k g }

/-- Evaluation and the induced coboundary on the supplied CE boundary. -/
noncomputable def cochainData :
    Specs.AdvancedHomologicalAlgebra.CE.cochainDataExpected.{u,v,w} :=
  fun k g _ _ _ M _ _ _ _ D =>
    { evaluation := homEquiv k g M
      differential := coboundary k g M D.differential
      evaluate_tmul := homEquiv_apply k g M
      inverse_tmul := homEquiv_symm_tmul k g M
      compatible := coboundary_comparison k g M D.differential
      squared := coboundary_squared k g M D.differential D.augmented.1
      formula := coboundary_formula k g M D.differential D.formula }

end AdvancedHomologicalAlgebra.CE
