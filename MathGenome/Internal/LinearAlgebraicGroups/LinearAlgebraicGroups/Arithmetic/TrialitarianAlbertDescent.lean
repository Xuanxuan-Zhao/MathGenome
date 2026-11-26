import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootRelations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Composition.ZornModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitModel
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalDivisionAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.LocalQuadraticSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SubfieldSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.GaloisSplitting
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.RelativeIsomorphism
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent

universe g i a

section InducedCochains

variable {Γ : Type g} [Group Γ] {I : Type i} [MulAction Γ I]
  {A : Type a} [AddCommGroup A] [DistribMulAction Γ A]

/-- A defect on the product indexed by a transitive set is a coboundary
if its component on one stabilizer is a coboundary. Coordinates here
are indexed by the source of an arrow, and the coefficient of an
arrow is acted on at its target. -/
theorem inducedDefect_isCoboundary
    (o : I) (transitive : ∀ i : I, ∃ r : Γ, r • o = i)
    (d : Γ → Γ → I → A)
    (assoc : ∀ g h k : Γ, ∀ i : I,
      d g h (k • i) + d (g * h) k i = g • d h k i + d g (h * k) i)
    (b : MulAction.stabilizer Γ o → A)
    (atBase : ∀ g h : MulAction.stabilizer Γ o,
      d g h o = b g + (g : Γ) • b h - b (g * h)) :
    ∃ f : Γ → I → A, ∀ g h : Γ, ∀ i : I,
      d g h i = f g (h • i) + g • f h i - f (g * h) i := by
  classical
  choose r hr using transitive
  let s (g : Γ) (i : I) : MulAction.stabilizer Γ o :=
    ⟨(r (g • i))⁻¹ * (g * r i), by
      change ((r (g • i))⁻¹ * (g * r i)) • o = o
      rw [mul_smul, mul_smul, hr, inv_smul_eq_iff, hr]⟩
  have hs (g : Γ) (i : I) : r (g • i) * (s g i : Γ) = g * r i := by
    simp [s]
  have hcomp (g h : Γ) (i : I) : s (g * h) i = s g (h • i) * s h i := by
    apply Subtype.ext
    apply mul_left_cancel (a := r ((g * h) • i))
    rw [hs, Subgroup.coe_mul, mul_smul, ← mul_assoc, hs, mul_assoc g (r (h • i)), hs, mul_assoc]
  refine ⟨fun g i => d g (r i) o - d (r (g • i)) (s g i) o +
    r (g • i) • b (s g i), ?_⟩
  intro g h i
  have h₁ := assoc g h (r i) o
  rw [hr] at h₁
  have h₂ := assoc g (r (h • i)) (s h i) o
  have h₃ := assoc (r (g • (h • i))) (s g (h • i)) (s h i) o
  have hfix : (s h i : Γ) • o = o := (s h i).property
  rw [hfix, hs] at h₂
  rw [hfix, hs, ← Subgroup.coe_mul, ← hcomp, atBase, smul_sub, smul_add] at h₃
  have hact : r (g • (h • i)) • ((s g (h • i) : Γ) • b (s h i)) =
      g • (r (h • i) • b (s h i)) := by
    rw [← mul_smul, hs, mul_smul]
  rw [hact] at h₃
  simp only [mul_smul, smul_add, smul_sub]
  have hd := eq_sub_of_add_eq h₁
  have hd₃ := eq_sub_of_add_eq ((add_comm _ _).trans h₃)
  have h₂' : d g (h * r i) o =
      d g (r (h • i)) o + d (g * r (h • i)) (s h i) o -
        g • d (r (h • i)) (s h i) o := by
    rw [eq_sub_iff_add_eq]
    exact (add_comm _ _).trans h₂.symm
  rw [hd, h₂', hd₃, hcomp]
  abel

end InducedCochains


section CubicCoefficients

variable {A : Type a} [AddCommGroup A]

/-- On the three split coordinates the norm is the sum in additive notation. -/
def cubicNormMap : (Fin 3 → A) →+ A where
  toFun x := x 0 + x 1 + x 2
  map_zero' := by simp
  map_add' _ _ := by simp only [Pi.add_apply]; abel

/-- The map giving the torus quotient, in additive notation. -/
def cubicQuotientMap : (Fin 3 → A) →+ (Fin 3 → A) where
  toFun x i := x i + x i - cubicNormMap x
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp only [Pi.add_apply, map_add]; abel

theorem norm_cubicQuotientMap (x : Fin 3 → A) :
    cubicNormMap (cubicQuotientMap x) = -cubicNormMap x := by
  change (x 0 + x 0 - (x 0 + x 1 + x 2)) + (x 1 + x 1 - (x 0 + x 1 + x 2)) +
    (x 2 + x 2 - (x 0 + x 1 + x 2)) = -(x 0 + x 1 + x 2)
  abel

/-- The kernel equations on all test groups, including units of rings with nilpotents. -/
theorem cubicQuotientMap_eq_zero_iff (x : Fin 3 → A) :
    cubicQuotientMap x = 0 ↔ (∀ i, x i + x i = 0) ∧ cubicNormMap x = 0 := by
  constructor
  · intro hx
    have hn : cubicNormMap x = 0 := by
      simpa [hx] using (norm_cubicQuotientMap x).symm
    refine ⟨fun i => ?_, hn⟩
    have hi := congrFun hx i
    change x i + x i - cubicNormMap x = 0 at hi
    simpa [hn] using hi
  · rintro ⟨h₂, hn⟩
    funext i
    change x i + x i - cubicNormMap x = 0
    simp [h₂, hn]

/-- Composition with the integral map `I - 11ᵗ` gives multiplication by two. -/
theorem cubicQuotientMap_sub_norm (x : Fin 3 → A) :
    cubicQuotientMap (fun i => x i - cubicNormMap x) = x + x := by
  funext i
  change (x i - (x 0 + x 1 + x 2)) + (x i - (x 0 + x 1 + x 2)) -
    ((x 0 - (x 0 + x 1 + x 2)) + (x 1 - (x 0 + x 1 + x 2)) +
      (x 2 - (x 0 + x 1 + x 2))) = x i + x i
  abel

section
variable {Γ : Type g} [Group Γ] {I : Type i} [Fintype I] [MulAction Γ I]
  [DistribMulAction Γ A]

/-- The norm of a diagonal cochain sums one copy on every coordinate. This gives
the restriction/corestriction calculation directly at degree two. -/
theorem norm_diagonalDefect_isCoboundary
    (deg : Fintype.card I = 3) (o : I) (transitive : ∀ i : I, ∃ r : Γ, r • o = i)
    (d : Γ → Γ → I → A)
    (assoc : ∀ g h k : Γ, ∀ i : I,
      d g h (k • i) + d (g * h) k i = g • d h k i + d g (h * k) i)
    (c : Γ → Γ → A)
    (c_assoc : ∀ g h k, c g h + c (g * h) k = g • c h k + c g (h * k))
    (b : MulAction.stabilizer Γ o → A)
    (atBase : ∀ g h : MulAction.stabilizer Γ o,
      d g h o - c g h = b g + (g : Γ) • b h - b (g * h))
    (twice : Γ → A)
    (h₂ : ∀ g h, c g h + c g h = twice g + g • twice h - twice (g * h))
    (norm : Γ → A)
    (hN : ∀ g h, ∑ i, d g h i = norm g + g • norm h - norm (g * h)) :
    ∃ f : Γ → I → A, ∀ g h : Γ, ∀ i : I,
      d g h i = f g (h • i) + g • f h i - f (g * h) i := by
  classical
  obtain ⟨f, hf⟩ := inducedDefect_isCoboundary o transitive (fun g h i => d g h i - c g h)
    (by
      intro g h k i
      rw [smul_sub]
      calc
        _ = (d g h (k • i) + d (g * h) k i) - (c g h + c (g * h) k) := by abel
        _ = _ := by rw [assoc, c_assoc]; abel) b atBase
  let s (g : Γ) : A := ∑ i, f g i
  have h₃ (g h : Γ) : c g h + c g h + c g h =
      (norm g - s g) + g • (norm h - s h) - (norm (g * h) - s (g * h)) := by
    have sumEq := congrArg (fun p : I → A => ∑ i, p i) (funext (hf g h))
    have perm : (∑ i, f g (h • i)) = s g := by
      exact Equiv.sum_comp (MulAction.toPerm h) (f g)
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum,
      Finset.sum_const, Finset.card_univ, deg, three_nsmul, perm, hN] at sumEq
    change _ = s g + g • s h - s (g * h) at sumEq
    rw [smul_sub]
    calc
      _ = (norm g + g • norm h - norm (g * h)) -
          ((norm g + g • norm h - norm (g * h)) - (c g h + (c g h + c g h))) := by abel
      _ = _ := by rw [sumEq]; abel
  let adj g := norm g - s g - twice g
  have hc (g h : Γ) : c g h = adj g + g • adj h - adj (g * h) := by
    calc
      c g h = (c g h + c g h + c g h) - (c g h + c g h) := by abel
      _ = _ := by rw [h₃, h₂]; dsimp only [adj]; simp only [smul_sub]; abel
  refine ⟨fun g i => f g i + adj g, fun g h i => ?_⟩
  rw [smul_add]
  calc
    d g h i = (d g h i - c g h) + c g h := (sub_add_cancel _ _).symm
    _ = _ := by rw [hf, hc]; simp only [sub_eq_add_neg, neg_add]; abel

end
end CubicCoefficients

section CentralExtensions

variable {Γ : Type g} [Group Γ] {M L Q C : Type a}
  [Group M] [Group L] [Group Q] [CommGroup C]

/-- The defect of a lifted adjoint cocycle is a two-cocycle in the central
kernel. This calculation applies to the separable points of the smooth
central extension, or at a finite Galois layer with chosen lifts. -/
theorem existsCentralLiftDefect
    (ρ : Γ →* MulAut L) (σ : Γ →* MulAut C) (τ : Γ →* MulAut Q)
    (j : C →* L) (p : L →* Q)
    (central : ∀ x y, Commute (j x) y) (injective : Function.Injective j)
    (kernel : ∀ x, p x = 1 ↔ x ∈ j.range)
    (equivariant : ∀ g x, ρ g (j x) = j (σ g x))
    (quotientEquivariant : ∀ g x, p (ρ g x) = τ g (p x))
    (q : Γ → Q) (cocycle : ∀ g h, q (g * h) = q g * τ g (q h))
    (l : Γ → L) (lift : ∀ g, p (l g) = q g) :
    ∃ d : Γ → Γ → C,
      (∀ g h, l g * ρ g (l h) = j (d g h) * l (g * h)) ∧
      ∀ g h k, d g h * d (g * h) k = σ g (d h k) * d g (h * k) := by
  have mem (g h : Γ) : l g * ρ g (l h) * (l (g * h))⁻¹ ∈ j.range := by
    apply (kernel _).mp
    simp [quotientEquivariant, lift, cocycle]
  choose d hd using mem
  have defect (g h : Γ) : l g * ρ g (l h) = j (d g h) * l (g * h) := by
    rw [hd, inv_mul_cancel_right]
  refine ⟨d, defect, fun g h k => injective (mul_right_cancel (b := l (g * (h * k))) ?_)⟩
  calc
    j (d g h * d (g * h) k) * l (g * (h * k)) =
        (l g * ρ g (l h)) * ρ (g * h) (l k) := by
      rw [← mul_assoc g h k, map_mul, mul_assoc, ← defect, ← mul_assoc, ← defect]
    _ = l g * ρ g (l h * ρ h (l k)) := by
      rw [map_mul, MulAut.mul_apply, map_mul, mul_assoc]
    _ = j (σ g (d h k) * d g (h * k)) * l (g * (h * k)) := by
      rw [defect h k, map_mul, equivariant, ← mul_assoc,
        ← (central (σ g (d h k)) (l g)).eq, mul_assoc, defect, ← mul_assoc, ← map_mul]

/-- Applying a character to the multiplication defect gives a coboundary
in the target coefficient group. In the trialitarian lift the character is
the Peirce multiplier or the norm character of the central product. -/
theorem character_centralLiftDefect {A : Type a} [CommGroup A]
    (ρ : Γ →* MulAut L) (θ : Γ →* MulAut A)
    (j : C →* L) (χ : L →* A) (f : C →* A)
    (equivariant : ∀ g x, χ (ρ g x) = θ g (χ x)) (onKernel : ∀ x, χ (j x) = f x)
    (l : Γ → L) (d : Γ → Γ → C)
    (defect : ∀ g h, l g * ρ g (l h) = j (d g h) * l (g * h)) :
    ∀ g h, f (d g h) = χ (l g) * θ g (χ (l h)) / χ (l (g * h)) := by
  intro g h
  apply eq_div_iff_mul_eq'.mpr
  simpa only [map_mul, equivariant, onKernel] using (congrArg χ (defect g h)).symm

/-- If the central multiplication defect is a coboundary, adjusting the chosen
lifts by its inverse produces a genuine group cocycle lifting the original one. -/
theorem adjustCentralLifts
    (ρ : Γ →* MulAut L) (σ : Γ →* MulAut C) (j : C →* L) (p : L →* Q)
    (central : ∀ x y, Commute (j x) y) (kernel : ∀ x, p (j x) = 1)
    (equivariant : ∀ g x, ρ g (j x) = j (σ g x))
    (q : Γ → Q) (l : Γ → L) (lift : ∀ g, p (l g) = q g)
    (b : Γ → C)
    (defect : ∀ g h, l g * ρ g (l h) = j (b g * σ g (b h) / b (g * h)) * l (g * h)) :
    ∃ l' : Γ → L, (∀ g, p (l' g) = q g) ∧
      ∀ g h, l' (g * h) = l' g * ρ g (l' h) := by
  refine ⟨fun g => j (b g)⁻¹ * l g, ?_, ?_⟩
  · intro g
    simp [kernel, lift]
  · intro g h
    simp only [map_mul, map_inv, equivariant]
    rw [mul_assoc (j (b g))⁻¹, ← mul_assoc (l g), ← (central _ _).inv_left.eq,
      mul_assoc (j (σ g (b h)))⁻¹, defect, ← mul_assoc,
      ← mul_assoc]
    simp only [← map_inv, ← map_mul]
    have scalars : (b g)⁻¹ * (σ g (b h))⁻¹ * (b g * σ g (b h) / b (g * h)) =
        (b (g * h))⁻¹ := by
      rw [← mul_inv_rev, mul_comm (σ g (b h)) (b g), div_eq_mul_inv, inv_mul_cancel_left]
    rw [← map_inv (σ g)] at scalars
    rw [scalars, map_inv]

/-- After a coboundary adjustment in the torus quotient, the lift takes values
in its subgroup kernel. This uses a lift of the adjusting point through the
smooth torsor with fiber the simply connected group. -/
theorem adjustQuotientCocycle
    (ρ : Γ →* MulAut L) (μ : Γ →* MulAut M) (σ : Γ →* MulAut C)
    (p : L →* C) (j : M →* L)
    (equivariant : ∀ g x, p (ρ g x) = σ g (p x))
    (kernel : ∀ x, p x = 1 ↔ x ∈ j.range)
    (injective : Function.Injective j) (stable : ∀ g x, ρ g (j x) = j (μ g x))
    (l : Γ → L) (cocycle : ∀ g h, l (g * h) = l g * ρ g (l h))
    (b : L) (adjustment : ∀ g, p (l g) = p b / σ g (p b)) :
    ∃ l' : Γ → M, (∀ g, j (l' g) = b⁻¹ * l g * ρ g b) ∧
      ∀ g h, l' (g * h) = l' g * μ g (l' h) := by
  have lift (g : Γ) : b⁻¹ * l g * ρ g b ∈ j.range := by
    apply (kernel _).mp
    simp [equivariant, adjustment, div_eq_mul_inv, mul_assoc]
  let l' g := (lift g).choose
  have h' (g : Γ) : j (l' g) = b⁻¹ * l g * ρ g b := (lift g).choose_spec
  refine ⟨l', h', fun g h => injective ?_⟩
  rw [map_mul, ← stable, h', h', h', cocycle, map_mul, MulAut.mul_apply]
  simp only [map_mul, map_inv]
  group

end CentralExtensions

section FramePermutations

open LinearAlgebraicGroups.Composition (Zorn)
open Composition.AdjointSpecification (conjugate)
open Composition.ZornSpecification (norm mapCoordinates)
open LinearAlgebraicGroups.Albert.CubicSpecification
open LinearAlgebraicGroups.Albert.FrameSpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification
open LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification
open LinearAlgebraicGroups.Albert.TrialitySpecification

universe r

variable {R : Type r} [CommRing R]

private theorem perm_cyclic (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (p (cyclicNext i) =
      if Equiv.Perm.sign p = 1 then cyclicNext (p i) else cyclicPrev (p i)) ∧
    (p (cyclicPrev i) =
      if Equiv.Perm.sign p = 1 then cyclicPrev (p i) else cyclicNext (p i)) := by
  revert p i
  decide

private theorem zornNormLaws : Composition.NormLaws (norm R) :=
  ⟨(Composition.Zorn.norm_laws R).1, (Composition.Zorn.norm_laws R).2, (Composition.Zorn.perfect R).nondegenerate⟩

private theorem zorn_conj_involutive (x : Zorn R) :
    conjugate (norm R) (conjugate (norm R) x) = x :=
  Composition.conjugate_involutive zornNormLaws x

private def zornConjugation : Zorn R ≃ₗ[R] Zorn R :=
  LinearEquiv.ofInvolutive (conjugate (norm R)) zorn_conj_involutive

private theorem zornConjugation_apply (x : Zorn R) :
    zornConjugation x = conjugate (norm R) x := rfl

private def blockPermutation (p : Equiv.Perm (Fin 3)) : Zorn R ≃ₗ[R] Zorn R :=
  if Equiv.Perm.sign p = 1 then LinearEquiv.refl R _ else zornConjugation

/-- The row and column permutation of the split Hermitian matrix. The
octonion coordinates must be conjugated when the cyclic order reverses. -/
def framePermutation (p : Equiv.Perm (Fin 3)) : Model R ≃ₗ[R] Model R :=
  (LinearEquiv.piCongrLeft' R (fun _ => R) p).prodCongr
    ((LinearEquiv.piCongrLeft' R (fun _ => Zorn R) p).trans
      (LinearEquiv.piCongrRight fun _ => blockPermutation p))

@[simp] theorem framePermutation_diagonal (p : Equiv.Perm (Fin 3)) (x : Model R) (i : Fin 3) :
    (framePermutation p x).1 (p i) = x.1 i := by
  change x.1 (p.symm (p i)) = _
  rw [p.symm_apply_apply]

@[simp] private theorem framePermutation_block (p : Equiv.Perm (Fin 3)) (x : Model R) (i : Fin 3) :
    (framePermutation p x).2 (p i) = blockPermutation p (x.2 i) := by
  change blockPermutation p (x.2 (p.symm (p i))) = _
  rw [p.symm_apply_apply]

private theorem blockPermutation_mul (p q : Equiv.Perm (Fin 3)) (x : Zorn R) :
    blockPermutation (p * q) x = blockPermutation p (blockPermutation q x) := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign q) with hq | hq <;>
    simp [blockPermutation, Equiv.Perm.sign_mul, hp, hq, zornConjugation_apply, zorn_conj_involutive]

/-- These automorphisms form a group action of the three-letter symmetric group. -/
def framePermutationAction (R : Type r) [CommRing R] :
    Equiv.Perm (Fin 3) →* (Model R ≃ₗ[R] Model R) where
  toFun := framePermutation
  map_one' := by
    ext x : 1
    apply Prod.ext <;> funext i
    · exact framePermutation_diagonal 1 x i
    · exact (framePermutation_block 1 x i).trans (by simp [blockPermutation])
  map_mul' p q := by
    ext x : 1
    apply Prod.ext <;> funext i
    · obtain ⟨j, rfl⟩ := (p * q).surjective i
      change (framePermutation (p * q) x).1 ((p * q) j) =
        (framePermutation p (framePermutation q x)).1 (p (q j))
      rw [framePermutation_diagonal (p * q) x j, framePermutation_diagonal,
        framePermutation_diagonal]
    · obtain ⟨j, rfl⟩ := (p * q).surjective i
      change (framePermutation (p * q) x).2 ((p * q) j) =
        (framePermutation p (framePermutation q x)).2 (p (q j))
      rw [framePermutation_block (p * q) x j, framePermutation_block,
        framePermutation_block, blockPermutation_mul]

theorem framePermutation_unit (p : Equiv.Perm (Fin 3)) :
    framePermutation (R := R) p cubicUnit = cubicUnit := by
  apply Prod.ext <;> funext i <;> obtain ⟨j, rfl⟩ := p.surjective i
  · exact framePermutation_diagonal p cubicUnit j
  · rw [framePermutation_block]
    exact map_zero _

theorem framePermutation_axis (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    framePermutation (R := R) p (frameAxis i) = frameAxis (p i) := by
  apply Prod.ext <;> funext j <;> obtain ⟨k, rfl⟩ := p.surjective j
  · rw [framePermutation_diagonal]
    simp [frameAxis, diagonalCoordinates, Pi.single_apply, p.injective.eq_iff]
  · rw [framePermutation_block]
    exact map_zero _

private theorem norm_blockPermutation (p : Equiv.Perm (Fin 3)) (x : Zorn R) :
    norm R (blockPermutation p x) = norm R x := by
  by_cases hp : Equiv.Perm.sign p = 1
  · simp [blockPermutation, hp]
  · exact (congrArg (norm R) (by simp [blockPermutation, hp, zornConjugation_apply])).trans
      (Composition.norm_conjugate zornNormLaws x)

private theorem polar_blockPermutation (p : Equiv.Perm (Fin 3)) (x y : Zorn R) :
    (norm R).polarBilin (blockPermutation p x) (blockPermutation p y) =
      (norm R).polarBilin x y := by
  simp [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add,
    norm_blockPermutation]

private theorem framePermutation_pairing (p : Equiv.Perm (Fin 3)) (x y : Model R) :
    tracePairing (norm R) (fun _ => 1) (framePermutation p x) (framePermutation p y) =
      tracePairing (norm R) (fun _ => 1) x y := by
  let summand (x y : Model R) (i : Fin 3) :=
    x.1 i * y.1 i + blockWeight (fun _ => (1 : Rˣ)) i * (norm R).polarBilin (x.2 i) (y.2 i)
  change (∑ i, summand (framePermutation p x) (framePermutation p y) i) = ∑ i, summand x y i
  rw [← Equiv.sum_comp p (summand (framePermutation p x) (framePermutation p y))]
  dsimp only [summand]
  simp only [blockWeight, Units.val_one, one_mul, framePermutation_diagonal,
    framePermutation_block, polar_blockPermutation]

private theorem framePermutation_adjoint (p : Equiv.Perm (Fin 3)) (x : Model R) :
    framePermutation p (cubicAdjoint (norm R) (fun _ => 1) x) =
      cubicAdjoint (norm R) (fun _ => 1) (framePermutation p x) := by
  apply Prod.ext <;> funext j <;> obtain ⟨i, rfl⟩ := p.surjective j
  · rw [framePermutation_diagonal]
    simp only [cubicAdjoint, blockWeight, Units.val_one, one_mul,
      framePermutation_block, norm_blockPermutation]
    obtain ⟨hn, hl⟩ := perm_cyclic p i
    by_cases hp : Equiv.Perm.sign p = 1
    · simp only [hp, ite_true] at hn hl
      rw [← hn, ← hl, framePermutation_diagonal, framePermutation_diagonal]
    · simp only [hp, ite_false] at hn hl
      rw [← hn, ← hl, framePermutation_diagonal, framePermutation_diagonal, mul_comm]
  · rw [framePermutation_block]
    simp only [cubicAdjoint, Units.val_one, one_smul, map_add, LinearEquiv.map_smul,
      framePermutation_diagonal, framePermutation_block]
    obtain ⟨hn, hl⟩ := perm_cyclic p i
    by_cases hp : Equiv.Perm.sign p = 1
    · simp only [hp, ite_true] at hn hl
      rw [← hn, ← hl, framePermutation_block, framePermutation_block]
      simp [blockPermutation, hp]
    · simp only [hp, ite_false] at hn hl
      rw [← hn, ← hl, framePermutation_block, framePermutation_block]
      simp only [blockPermutation, hp, ite_false, zornConjugation_apply,
        zorn_conj_involutive]
      rw [← Composition.conjugate_mul zornNormLaws, zorn_conj_involutive]

/-- The frame permutations preserve the quadratic law over all commutative
rings, including in characteristic two. -/
theorem framePermutation_operator (p : Equiv.Perm (Fin 3)) (x y : Model R) :
    framePermutation p (modelOp x y) = modelOp (framePermutation p x) (framePermutation p y) := by
  change framePermutation p (applyOperator _ _ x y) = applyOperator _ _ _ _
  simp only [applyOperator, adjointCross, map_sub, LinearEquiv.map_smul, LinearEquiv.map_add,
    framePermutation_adjoint, framePermutation_pairing]

end FramePermutations

section Scalars

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Composition (Zorn)
open Composition.AdjointSpecification (conjugate)
open Composition.ZornSpecification (norm)

universe r

variable {R : Type r} [CommRing R]

/-- The three scalar actions on the outer Peirce blocks. -/
def scalarTriple (u : Fin 3 → Rˣ) : Triple R :=
  fun i => LinearEquiv.smulOfUnit (u i)

private theorem scalarTriple_apply (u : Fin 3 → Rˣ) (i : Fin 3) (x : Zorn R) :
    scalarTriple u i x = (u i : R) • x := rfl

private theorem scalar_eq_of_smul_zorn_one {a b : R} (h : a • (1 : Zorn R) = b • 1) :
    a = b := by
  have eq := congrArg (fun z => (Composition.Zorn.coordinates R z).1) h
  change a * 1 = b * 1 at eq
  simpa using eq

/-- The scalar triples belonging to the related-triple group are exactly
the sign triples with product one, on every scalar algebra. -/
theorem isRelated_scalarTriple_iff (u : Fin 3 → Rˣ) :
    IsRelated (scalarTriple u) ↔ (∀ i, u i ^ 2 = 1) ∧ ∏ i, u i = 1 := by
  have unit_sq (i : Fin 3) (h : u i ^ 2 = 1) : (u i : R) ^ 2 = 1 :=
    congrArg Units.val h
  constructor
  · rintro ⟨isom, ternary⟩
    have sq (i : Fin 3) : u i ^ 2 = 1 := by
      have hi := isom i (1 : Zorn R)
      rw [scalarTriple_apply, QuadraticMap.map_smul, smul_eq_mul, Composition.Zorn.norm_one,
        mul_one] at hi
      exact Units.ext (by simpa [pow_two] using hi)
    refine ⟨sq, ?_⟩
    have h := ternary 0 (1 : Zorn R) (1 : Zorn R)
    have h₀ : cyclicNext 0 = 1 := rfl
    have h₁ : cyclicPrev 0 = 2 := rfl
    simp only [scalarTriple_apply, h₀, h₁, mul_smul_comm, mul_one, smul_smul,
      map_smul, Composition.conjugate_one zornNormLaws, mul_comm (u 2 : R) (u 1 : R)] at h
    have mult : u 0 = u 1 * u 2 := Units.ext (scalar_eq_of_smul_zorn_one h)
    rw [Fin.prod_univ_three, mul_assoc, ← mult, ← pow_two, sq]
  · rintro ⟨sq, prod⟩
    constructor
    · intro i x
      rw [scalarTriple_apply, QuadraticMap.map_smul, ← pow_two, unit_sq i (sq i), one_smul]
    · intro i x y
      have prodAt (i : Fin 3) : u i * (u (cyclicNext i) *
            u (cyclicPrev i)) = 1 := by
        rw [Fin.prod_univ_three] at prod
        fin_cases i
        · change u 0 * (u 1 * u 2) = 1
          simpa only [mul_assoc] using prod
        · change u 1 * (u 2 * u 0) = 1
          rw [← prod]
          ac_rfl
        · change u 2 * (u 0 * u 1) = 1
          rw [← prod]
          ac_rfl
      have mult (i : Fin 3) : u (cyclicNext i) *
            u (cyclicPrev i) = u i :=
        mul_left_cancel ((prodAt i).trans (by rw [← pow_two, sq]))
      simp only [scalarTriple_apply, smul_mul_assoc, mul_smul_comm,
        smul_smul, map_smul, ← Units.val_mul, mul_comm (u (cyclicPrev i)) (u (cyclicNext i)), mult]

end Scalars

section CyclicValuations

variable {Γ : Type g} [Group Γ] {A : Type a} [AddCommGroup A] [DistribMulAction Γ A]

private theorem sum_shift_difference (x : ℕ → ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (x j - x (j + 1))) = x 0 - x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    abel

/-- The valuation of the accumulated cyclic defect of a coboundary is a
multiple of the order of the chosen cyclic generator. -/
theorem cyclicDefect_valuation_dvd
    (v : A →+ ℤ) (invariant : ∀ g : Γ, ∀ a : A, v (g • a) = v a)
    (t : Γ) (n : ℕ) (order : t ^ n = 1)
    (d : Γ → Γ → A) (b : Γ → A)
    (hd : ∀ g h, d g h = b g + g • b h - b (g * h)) :
    (n : ℤ) ∣ ∑ j ∈ Finset.range n, v (d t (t ^ j)) := by
  refine ⟨v (b t), ?_⟩
  simp only [hd, map_sub, map_add, invariant, ← pow_succ', add_sub_assoc,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  rw [sum_shift_difference (fun j => v (b (t ^ j))) n]
  simp [order]

/-- When the accumulated cyclic defect has uniformizer valuation, its
cohomology class has order divisible by the cyclic degree. -/
theorem cyclicDefect_degree_dvd_exponent
    (v : A →+ ℤ) (invariant : ∀ g : Γ, ∀ a : A, v (g • a) = v a)
    (t : Γ) (n : ℕ) (order : t ^ n = 1)
    (d : Γ → Γ → A) (value : (∑ j ∈ Finset.range n, v (d t (t ^ j))) = 1)
    (m : ℕ) (b : Γ → A)
    (hm : ∀ g h, m • d g h = b g + g • b h - b (g * h)) :
    n ∣ m := by
  have dvd := cyclicDefect_valuation_dvd v invariant t n order (fun g h => m • d g h) b hm
  simp only [map_nsmul, nsmul_eq_mul, ← Finset.mul_sum, value, mul_one] at dvd
  exact Int.natCast_dvd_natCast.mp dvd

end CyclicValuations

section DivisionPresentation

open LocalDivisionAlgebras
open scoped WithZero
open _root_.Specs.RM03.CSA

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {B : Type v} [DivisionRing B] [Algebra F B]
  {w : Valuation B ℤᵐ⁰} {r : ResidueData (F := F) w}

/-- On the right vector space of the cyclic presentation, right multiplication
by the inverse uniformizer is semilinear for the cyclic generator. Its
degree-th power is the inverse of the scalar parameter. -/
theorem cyclicUniformizerOperator (c : CyclicPresentation (F := F) w r) :
    letI := c.fieldL
    letI := c.algebraL
    letI := rightSubfieldModule c.embed
    (∀ (a : c.L) (x : B), (a • x) * (↑(c.uniformizer⁻¹) : B) =
      c.τ a • (x * (↑(c.uniformizer⁻¹) : B))) ∧
    ∀ x : B, ((fun y : B => y * (↑(c.uniformizer⁻¹) : B))^[degree F B]) x =
      ((algebraMap F c.L) c.parameter)⁻¹ • x := by
  let := c.fieldL
  let := c.algebraL
  let := rightSubfieldModule c.embed
  constructor
  · intro a x
    change (x * c.embed a) * (↑(c.uniformizer⁻¹) : B) =
      (x * (↑(c.uniformizer⁻¹) : B)) * c.embed (c.τ a)
    have h := c.conjugation a
    have step : c.embed a * (↑(c.uniformizer⁻¹) : B) =
        (↑(c.uniformizer⁻¹) : B) * c.embed (c.τ a) := by
      calc
        _ = (↑(c.uniformizer⁻¹) : B) * ((c.uniformizer : B) * c.embed a) *
            (↑(c.uniformizer⁻¹) : B) := by simp
        _ = (↑(c.uniformizer⁻¹) : B) * (c.embed (c.τ a) * c.uniformizer) *
            (↑(c.uniformizer⁻¹) : B) := by rw [h]
        _ = _ := by simp [mul_assoc]
    simp only [mul_assoc, step]
  · intro x
    have power (n : ℕ) :
        ((fun y : B => y * (↑(c.uniformizer⁻¹) : B))^[n]) x =
          x * (↑(c.uniformizer⁻¹) : B) ^ n := by
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_assoc]
    rw [power]
    change _ = x * c.embed (((algebraMap F c.L) c.parameter)⁻¹)
    congr 1
    simp only [Units.val_inv_eq_inv_val, inv_pow, c.power_uniformizer,
      map_inv₀, AlgHom.commutes]

end DivisionPresentation

section SemilinearFrame

open LinearAlgebraicGroups.Composition (Zorn)
open Composition.AdjointSpecification (conjugate)
open Composition.ZornSpecification (norm mapCoordinates)
open LinearAlgebraicGroups.Albert.CubicSpecification
open LinearAlgebraicGroups.Albert.FrameSpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification
open LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Descent

universe r

variable {R S T : Type r} [CommRing R] [CommRing S] [CommRing T]

private theorem mapCoordinates_conjugate (f : R →+* S) (x : Zorn R) :
    mapCoordinates f (conjugate (norm R) x) = conjugate (norm S) (mapCoordinates f x) := by
  let e := Composition.Zorn.coordinates R
  obtain ⟨⟨a, u, v, b⟩, rfl⟩ := e.symm.surjective x
  rw [Composition.Zorn.conjugate_formula]
  change Composition.Zorn.ofCoordinates (f b, f ∘ (-u), f ∘ (-v), f a) =
    conjugate (norm S) (Composition.Zorn.ofCoordinates (f a, f ∘ u, f ∘ v, f b))
  rw [Composition.Zorn.conjugate_formula]
  change (f b, f ∘ (-u), f ∘ (-v), f a) = (f b, -(f ∘ u), -(f ∘ v), f a)
  simp only [Prod.mk.injEq, true_and, and_true]
  exact ⟨funext (fun i => map_neg f (u i)), funext (fun i => map_neg f (v i))⟩

/-- Frame permutation commutes with every change of coefficients. -/
theorem framePermutation_natural (f : R →+* S) (p : Equiv.Perm (Fin 3)) (x : Model R) :
    mapModel f (framePermutation p x) = framePermutation p (mapModel f x) := by
  apply Prod.ext <;> funext j <;> obtain ⟨i, rfl⟩ := p.surjective j
  · change f ((framePermutation p x).1 (p i)) = _
    rw [framePermutation_diagonal, framePermutation_diagonal]
    rfl
  · change mapCoordinates f ((framePermutation p x).2 (p i)) = _
    rw [framePermutation_block, framePermutation_block]
    change mapCoordinates f (blockPermutation p (x.2 i)) = blockPermutation p (mapCoordinates f (x.2 i))
    by_cases hp : Equiv.Perm.sign p = 1
    · simp [blockPermutation, hp]
    · simpa only [blockPermutation, hp, ite_false, zornConjugation_apply] using
        mapCoordinates_conjugate f (x.2 i)

private theorem mapModel_id (x : Model R) : mapModel (RingHom.id R) x = x := rfl

private theorem mapModel_comp (f : R →+* S) (g : S →+* T) (x : Model R) :
    mapModel (g.comp f) x = mapModel g (mapModel f x) := rfl

private theorem mapModel_add (f : R →+* S) (x y : Model R) :
    mapModel f (x + y) = mapModel f x + mapModel f y := by
  apply Prod.ext <;> funext i
  · exact map_add f _ _
  · change mapCoordinates f (x.2 i + y.2 i) = _
    let a := (Composition.Zorn.coordinates R) (x.2 i)
    let b := (Composition.Zorn.coordinates R) (y.2 i)
    change (f (a.1 + b.1), (fun j => f (a.2.1 j + b.2.1 j)),
      (fun j => f (a.2.2.1 j + b.2.2.1 j)), f (a.2.2.2 + b.2.2.2)) = _
    simp only [map_add]
    rfl

private theorem mapModel_smul (f : R →+* S) (c : R) (x : Model R) :
    mapModel f (c • x) = f c • mapModel f x := by
  apply Prod.ext <;> funext i
  · exact map_mul f _ _
  · change mapCoordinates f (c • x.2 i) = _
    let a := (Composition.Zorn.coordinates R) (x.2 i)
    change (f (c * a.1), (fun j => f (c * a.2.1 j)),
      (fun j => f (c * a.2.2.1 j)), f (c * a.2.2.2)) = _
    simp only [map_mul]
    rfl

private theorem mapCoordinates_add (f : R →+* S) (x y : Zorn R) :
    mapCoordinates f (x + y) = mapCoordinates f x + mapCoordinates f y :=
  congrArg (fun z : Model S => z.2 0) (mapModel_add f (0, fun _ => x) (0, fun _ => y))

private theorem mapCoordinates_smul (f : R →+* S) (c : R) (x : Zorn R) :
    mapCoordinates f (c • x) = f c • mapCoordinates f x :=
  congrArg (fun z : Model S => z.2 0) (mapModel_smul f c (0, fun _ => x))

private theorem mapModel_sub (f : R →+* S) (x y : Model R) :
    mapModel f (x - y) = mapModel f x - mapModel f y := by
  rw [eq_sub_iff_add_eq, ← mapModel_add, sub_add_cancel]

private theorem mapCoordinates_polar (f : R →+* S) (x y : Zorn R) :
    f ((norm R).polarBilin x y) =
      (norm S).polarBilin (mapCoordinates f x) (mapCoordinates f y) := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, map_sub,
    ← Composition.Zorn.mapCoordinates_norm, mapCoordinates_add]

private theorem mapModel_pairing (f : R →+* S) (x y : Model R) :
    f (tracePairing (norm R) (fun _ => 1) x y) =
      tracePairing (norm S) (fun _ => 1) (mapModel f x) (mapModel f y) := by
  let weights (A : Type r) [CommRing A] : Fin 3 → Aˣ := fun _ => 1
  change f (∑ i, (x.1 i * y.1 i + blockWeight (weights R) i * (norm R).polarBilin (x.2 i) (y.2 i))) =
    ∑ i, (f (x.1 i) * f (y.1 i) + blockWeight (weights S) i *
      (norm S).polarBilin (mapCoordinates f (x.2 i)) (mapCoordinates f (y.2 i)))
  simp only [map_sum, map_add, map_mul, weights, blockWeight, Units.val_one, one_mul,
    mapCoordinates_polar]

private theorem mapModel_adjoint (f : R →+* S) (x : Model R) :
    mapModel f (cubicAdjoint (norm R) (fun _ => 1) x) =
      cubicAdjoint (norm S) (fun _ => 1) (mapModel f x) := by
  apply Prod.ext <;> funext i
  · simp only [mapModel, cubicAdjoint, blockWeight, Units.val_one, one_mul, map_sub, map_mul,
      Composition.Zorn.mapCoordinates_norm]
  · simp only [mapModel, cubicAdjoint, Units.val_one, one_smul, mapCoordinates_add,
      mapCoordinates_smul, mapCoordinates_conjugate, Composition.Zorn.mapCoordinates_mul, map_neg]

theorem mapModel_operator (f : R →+* S) (x y : Model R) :
    mapModel f (modelOp x y) = modelOp (mapModel f x) (mapModel f y) := by
  change mapModel f (applyOperator _ _ x y) = applyOperator _ _ _ _
  simp only [applyOperator, adjointCross, mapModel_sub, mapModel_add, mapModel_smul,
    mapModel_adjoint, mapModel_pairing]

private def coefficientEquiv (f : R ≃+* S) : Model R ≃+ Model S where
  toFun := mapModel f.toRingHom
  invFun := mapModel f.symm.toRingHom
  left_inv x := by
    rw [← mapModel_comp, show f.symm.toRingHom.comp f.toRingHom = RingHom.id R by ext; simp,
      mapModel_id]
  right_inv x := by
    rw [← mapModel_comp, show f.toRingHom.comp f.symm.toRingHom = RingHom.id S by ext; simp,
      mapModel_id]
  map_add' := mapModel_add f.toRingHom

variable {k K E : Type r} [Field k] [Field K] [Field E] [Algebra k K] [Algebra k E]

/-- The Galois permutation of the three embeddings under the given numbering. -/
def diagramPermutation (e : (E →ₐ[k] K) ≃ Fin 3) : Gal(K/k) →* Equiv.Perm (Fin 3) where
  toFun g := {
    toFun := fun i => e (g.toAlgHom.comp (e.symm i))
    invFun := fun i => e (g.symm.toAlgHom.comp (e.symm i))
    left_inv := fun i => by
      dsimp only
      rw [e.symm_apply_apply]
      conv_rhs => rw [← e.apply_symm_apply i]
      congr 1
      ext x
      simp
    right_inv := fun i => by
      dsimp only
      rw [e.symm_apply_apply]
      conv_rhs => rw [← e.apply_symm_apply i]
      congr 1
      ext x
      simp }
  map_one' := by
    ext i : 1
    change e ((AlgHom.id _ _).comp (e.symm i)) = i
    simp
  map_mul' g h := by
    ext i : 1
    change e ((g * h).toAlgHom.comp (e.symm i)) =
      e (g.toAlgHom.comp (e.symm (e (h.toAlgHom.comp (e.symm i)))))
    rw [e.symm_apply_apply]
    rfl

/-- Permutation descent on the split Albert vector space. -/
def frameDescentAction (π : Gal(K/k) →* Equiv.Perm (Fin 3)) :
    SemilinearAction k K (Model K) where
  act g := (coefficientEquiv g.toRingEquiv).trans (framePermutation (π g)).toAddEquiv
  one_act x := by
    change framePermutation (π 1) (mapModel (RingHom.id K) x) = x
    rw [map_one, mapModel_id]
    exact LinearEquiv.congr_fun (map_one (framePermutationAction K)) x
  mul_act g h x := by
    change framePermutation (π (g * h)) (mapModel (g * h).toRingHom x) =
      framePermutation (π g) (mapModel g.toRingHom (framePermutation (π h) (mapModel h.toRingHom x)))
    rw [framePermutation_natural, ← mapModel_comp]
    have hπ : framePermutationAction K (π (g * h)) =
        framePermutationAction K (π g) * framePermutationAction K (π h) := by
      rw [map_mul, map_mul]
    exact LinearEquiv.congr_fun hπ _
  map_smul g c x := by
    change framePermutation (π g) (mapModel g.toRingHom (c • x)) =
      g c • framePermutation (π g) (mapModel g.toRingHom x)
    rw [mapModel_smul, map_smul]
    rfl

local instance : Module k (Model K) := Module.compHom _ (algebraMap k K)

local instance : IsScalarTower k K (Model K) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

theorem frameDescentAction_operator (π : Gal(K/k) →* Equiv.Perm (Fin 3))
    (g : Gal(K/k)) (x y : Model K) :
    (frameDescentAction π).act g (modelOp x y) =
      modelOp ((frameDescentAction π).act g x) ((frameDescentAction π).act g y) := by
  change framePermutation _ (mapModel g.toRingHom (modelOp x y)) =
    modelOp (framePermutation _ (mapModel g.toRingHom x))
      (framePermutation _ (mapModel g.toRingHom y))
  rw [mapModel_operator, framePermutation_operator]

/-- The reference quadratic operator on the fixed vectors in the split model. -/
def fixedFrameOperator (π : Gal(K/k) →* Equiv.Perm (Fin 3))
    (x y : (frameDescentAction π).fixed) : (frameDescentAction π).fixed :=
  ⟨modelOp x.val y.val, fun g => by rw [frameDescentAction_operator, x.property g, y.property g]⟩

open scoped TensorProduct in
/-- The actual scalar-extension comparison for the reference module at a
finite Galois splitting layer. -/
noncomputable def frameDescentEquivalence [FiniteDimensional k K] [IsGalois k K]
    (π : Gal(K/k) →* Equiv.Perm (Fin 3)) :
    K ⊗[k] (frameDescentAction π).fixed ≃ₗ[K] Model K :=
  (frameDescentAction π).descentEquiv

/-- The actual cubic field lies in the fixed module as the diagonal given
by evaluation in its three embeddings. -/
def diagonalInFrameDescent (e : (E →ₐ[k] K) ≃ Fin 3) :
    E →ₗ[k] (frameDescentAction (diagramPermutation e)).fixed where
  toFun a := ⟨(fun i => e.symm i a, 0), fun g => by
    apply Prod.ext <;> funext j <;> obtain ⟨i, rfl⟩ := (diagramPermutation e g).surjective j
    · change (framePermutation (diagramPermutation e g) (mapModel g.toRingHom _)).1
        (diagramPermutation e g i) = e.symm (diagramPermutation e g i) a
      rw [framePermutation_diagonal]
      change g (e.symm i a) = e.symm (e (g.toAlgHom.comp (e.symm i))) a
      rw [e.symm_apply_apply]
      rfl
    · change (framePermutation (diagramPermutation e g) (mapModel g.toRingHom
        ((fun i => e.symm i a), 0))).2 (diagramPermutation e g i) = 0
      rw [framePermutation_block]
      have hz : (mapModel g.toRingHom ((fun i => e.symm i a), 0)).2 i = 0 := by
        change (g 0, g ∘ (0 : Fin 3 → K), g ∘ (0 : Fin 3 → K), g 0) = _
        simp [Function.comp_def, Pi.zero_def]
        rfl
      rw [hz, map_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · exact map_add (e.symm i) a b
    · simp
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext <;> funext i
    · change e.symm i (c • a) = algebraMap k K c * e.symm i a
      simpa only [Algebra.smul_def, AlgHom.toLinearMap_apply] using (e.symm i).toLinearMap.map_smul c a
    · change (0 : Zorn K) = algebraMap k K c • (0 : Zorn K)
      rw [smul_zero]

theorem diagonalInFrameDescent_injective (e : (E →ₐ[k] K) ≃ Fin 3) :
    Function.Injective (diagonalInFrameDescent e) := by
  intro a b h
  exact (e.symm 0).injective
    (congrArg (fun x : (frameDescentAction (diagramPermutation e)).fixed => x.val.1 0) h)

end SemilinearFrame

section TorusCover

open Polynomial

universe r

private theorem adjoinUnitSquareRoot (R : Type r) [CommRing R] (a : Rˣ) :
    ∃ (S : Type r) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧ ∃ b : Sˣ, b ^ 2 = Units.map (algebraMap R S).toMonoidHom a := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨R, inferInstance, inferInstance, inferInstance, 1, Units.ext (Subsingleton.elim _ _)⟩
  let f : R[X] := X ^ 2 - C (a : R)
  let S := AdjoinRoot f
  have monic : f.Monic := monic_X_pow_sub_C _ (by decide)
  have hdeg : f.natDegree = 2 := natDegree_X_pow_sub_C
  have : Nonempty (Fin f.natDegree) := ⟨⟨0, by simp [hdeg]⟩⟩
  have hff : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_linearEquiv R _ (AdjoinRoot.powerBasisAux' monic).repr
  have root : (AdjoinRoot.root f) ^ 2 = algebraMap R S (a : R) := by
    have h := AdjoinRoot.eval₂_root f
    dsimp only [f] at h
    simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero,
      ← AdjoinRoot.algebraMap_eq] using h
  have unit : IsUnit (AdjoinRoot.root f) := (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
    (root.symm ▸ ((a.isUnit).map (algebraMap R S)))
  exact ⟨S, inferInstance, inferInstance, hff, unit.unit,
    Units.ext (by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_map]
      exact root)⟩

private theorem adjoinUnitSquareRoots (n : ℕ) (R : Type r) [CommRing R] (a : Fin n → Rˣ) :
    ∃ (S : Type r) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧
        ∃ b : Fin n → Sˣ, ∀ i, b i ^ 2 = Units.map (algebraMap R S).toMonoidHom (a i) := by
  induction n generalizing R with
  | zero => exact ⟨R, inferInstance, inferInstance, inferInstance, Fin.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨S, _, _, hS, b, hb⟩ := ih R (fun i => a i.castSucc)
    let s := Units.map (algebraMap R S).toMonoidHom
    obtain ⟨T, _, _, hT, root, hroot⟩ := adjoinUnitSquareRoot S (s (a (Fin.last n)))
    let t := Units.map (algebraMap S T).toMonoidHom
    let : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    refine ⟨T, inferInstance, inferInstance, Module.FaithfullyFlat.trans R S T,
      Fin.lastCases root (fun i => t (b i)), ?_⟩
    intro i
    have ht (x : Rˣ) : t (s x) = Units.map (algebraMap R T).toMonoidHom x := Units.ext rfl
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp only
      rw [Fin.lastCases_last, hroot, ht]
    · dsimp only
      rw [Fin.lastCases_castSucc, ← map_pow, hb, ht]

/-- The map (x ↦ x²/N(x)) of the split three-dimensional torus
is surjective locally for the faithfully flat topology. The cover uses
quadratic monic extensions and is valid even in characteristic two. -/
theorem cubicQuotient_lifts_afterFaithfullyFlat (R : Type r) [CommRing R] (a : Fin 3 → Rˣ) :
    ∃ (S : Type r) (_ : CommRing S) (_ : Algebra R S),
      Module.FaithfullyFlat R S ∧
        ∃ x : Fin 3 → Sˣ, ∀ i,
          x i ^ 2 / (∏ j, x j) = Units.map (algebraMap R S).toMonoidHom (a i) := by
  obtain ⟨S, _, _, hS, t, ht⟩ := adjoinUnitSquareRoots 3 R a
  let q : Additive Sˣ := cubicNormMap (fun i => Additive.ofMul (t i))
  let x (i : Fin 3) : Sˣ := Additive.toMul (Additive.ofMul (t i) - q)
  refine ⟨S, inferInstance, inferInstance, hS, x, fun i => ?_⟩
  rw [← ht]
  apply Additive.ofMul.injective
  have ofTo (a : Additive Sˣ) : Additive.ofMul (Additive.toMul a) = a := rfl
  have hc := congrFun (cubicQuotientMap_sub_norm (fun i => Additive.ofMul (t i))) i
  simpa only [ofMul_div, ofMul_pow, cubicQuotientMap, cubicNormMap, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Fin.prod_univ_three, ofMul_mul, two_nsmul, Pi.add_apply, x, q, ofTo] using hc

end TorusCover

section LocalAmbient

open TrialitarianAlbertDescentSpecification
open SplitAlbertLocalFormsSpecification (LocalAlbertSplitting)
open LinearAlgebraicGroups.Albert.SplitSpecification

universe u

theorem ambientAlbert_isSplit (splitting : LocalAlbertSplitting.{u,u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (J : AlbertModel F) : IsSplitModel J.law .octonion :=
  splitting F J.law J.albert

end LocalAmbient

section QuaternionRestriction

open LocalQuadraticSplitting
open _root_.Specs.RM03.CSA (degree isCentralDivision)
open _root_.RM03.CSA (isCentralSimple_of_isCentralDivision isCentralSimple_baseChange finrank_baseChange)
open _root_.RM03.Brauer
open MulOpposite

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Any quaternion division algebra over the cubic orbit field is obtained by
scalar extension of the unique quaternion division algebra over the base. -/
theorem quaternionOverCubic_isBaseChange
    {E : Type u} [Field E] [Algebra F E] [Module.Finite F E]
    (cubic : Module.finrank F E = 3)
    {D : Type v} [DivisionRing D] [Algebra E D]
    (hD : isCentralDivision E D) (dD : degree E D = 2) :
    ∃ (B : Type u) (_ : DivisionRing B) (_ : Algebra F B),
      isCentralDivision F B ∧ degree F B = 2 ∧ Nonempty (_root_.Specs.RM03.CSA.baseChange F E B ≃ₐ[E] D) := by
  obtain ⟨r, T, _, hE, _⟩ := finiteExtension_localField (K := F) (L := E)
  let : ValuativeRel E := r
  let : TopologicalSpace E := T
  obtain ⟨B, _, _, hB, dB⟩ := local_division_exists (F := F)
  have odd : Odd (Module.finrank F E) := cubic ▸ (by decide : Odd 3)
  obtain ⟨nt, hu⟩ := odd_extension_division (E := E) hB dB odd
  let : Nontrivial (_root_.Specs.RM03.CSA.baseChange F E B) := nt
  let : DivisionRing (_root_.Specs.RM03.CSA.baseChange F E B) :=
    DivisionRing.ofIsUnitOrEqZero (fun x => (eq_or_ne x 0).elim Or.inr (fun h => Or.inl (hu x h)))
  have hsimple := isCentralSimple_of_isCentralDivision F B hB
  have hs := isCentralSimple_baseChange (L := E) hsimple
  have hc : isCentralDivision E (_root_.Specs.RM03.CSA.baseChange F E B) := ⟨hs.2.1, hs.2.2⟩
  have deg : degree E (_root_.Specs.RM03.CSA.baseChange F E B) = 2 := by
    unfold degree
    change Nat.sqrt (Module.finrank E (_root_.RM03.CSA.BaseChange F E B)) = 2
    rw [finrank_baseChange hsimple]
    exact dB
  exact ⟨B, inferInstance, inferInstance, hB, dB, local_division_unique hc deg hD dD⟩

/-- Local quaternion uniqueness identifies the algebra with its opposite,
which makes its Brauer class 2-torsion. -/
theorem localQuaternion_two_nsmul_class
    {B : Type u} [DivisionRing B] [Algebra F B]
    (hB : isCentralDivision F B) (dB : degree F B = 2) :
    2 • classOf (_root_.RM03.CSA.toCSA (isCentralSimple_of_isCentralDivision F B hB)) = 0 := by
  let A := _root_.RM03.CSA.toCSA (isCentralSimple_of_isCentralDivision F B hB)
  let : Algebra.IsCentral F B := hB.1
  let : Module.Finite F B := hB.2
  have hO : isCentralDivision F Bᵐᵒᵖ := ⟨inferInstance, inferInstance⟩
  have dO : degree F Bᵐᵒᵖ = 2 := by
    unfold degree
    rw [← (opLinearEquiv F : B ≃ₗ[F] Bᵐᵒᵖ).finrank_eq]
    exact dB
  obtain ⟨e⟩ := local_division_unique hB dB hO dO
  have cls : classOf A = classOf (oppositeCSA A) := classOf_eq_of_algEquiv e
  rw [← classOf_neg] at cls
  change 2 • classOf A = 0
  rw [two_nsmul, ← neg_eq_iff_add_eq_zero]
  exact cls.symm

end QuaternionRestriction

open _root_.Specs.LinearAlgebraicGroups.Albert (QuadraticOperatorLaw)
open LinearAlgebraicGroups.Albert.SplitSpecification
open LinearMap (BilinMap)
open Module TensorProduct

universe u v w
noncomputable section

set_option linter.style.haveILetI false

section ExtendQuadraticLaw

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- A quadratic map on a finite-dimensional vector space has a bilinear
representative by putting each mixed coefficient in one triangular position. -/
private theorem exists_bilinearRepresentative [FiniteDimensional k V]
    (Q : QuadraticMap k V (End k V)) :
    ∃ B : BilinMap k V (End k V), B.toQuadraticMap = Q := by
  classical
  let b := finBasis k V
  let c i j := if i = j then Q (b i) else if i < j then Q.polarBilin (b i) (b j) else 0
  let B : BilinMap k V (End k V) := b.constr k fun i => b.constr k (c i)
  have hb (i j) : B (b i) (b j) = c i j := by simp [B, b]
  have hpolar : B.toQuadraticMap.polarBilin = Q.polarBilin := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    rw [LinearMap.BilinMap.polarBilin_toQuadraticMap, LinearMap.add_apply, LinearMap.add_apply,
      LinearMap.flip_apply, hb, hb]
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [c, ne_of_lt hij, ne_of_gt hij, hij, not_lt_of_ge hij.le]
    · simp [c, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    · simp [c, ne_of_lt hji, ne_of_gt hji, hji, not_lt_of_ge hji.le,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (b j) (b i)]
  refine ⟨B, QuadraticMap.ext fun x => ?_⟩
  rw [← b.sum_repr x]
  suffices ∀ s : Finset (Fin (finrank k V)),
      B.toQuadraticMap (∑ i ∈ s, (b.repr x i) • b i) =
        Q (∑ i ∈ s, (b.repr x i) • b i) by exact this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, QuadraticMap.map_add, ← QuadraticMap.polarBilin_apply_apply,
      hpolar, ih, QuadraticMap.map_smul]
    simp [LinearMap.BilinMap.toQuadraticMap_apply, hb, c]

variable (B : BilinMap k V (End k V))

private def extendedBilinearOperator (A : Type u) [CommRing A] [Algebra k A] :
    BilinMap A (A ⊗[k] V) (End A (A ⊗[k] V)) :=
  (B.baseChange A).compr₂ (LinearMap.tensorProduct k A V V)

private theorem extendedBilinearOperator_tmul (A : Type u) [CommRing A] [Algebra k A]
    (a b c : A) (x y z : V) :
    extendedBilinearOperator B A (a ⊗ₜ[k] x) (b ⊗ₜ[k] y) (c ⊗ₜ[k] z) =
      (a * b * c) ⊗ₜ[k] B x y z := by
  change LinearMap.tensorProduct k A V V (B.baseChange A (a ⊗ₜ[k] x) (b ⊗ₜ[k] y))
    (c ⊗ₜ[k] z) = _
  rw [LinearMap.BilinMap.baseChange_tmul]
  change ((a * b) • (B x y).baseChange A) (c ⊗ₜ[k] z) = _
  rw [LinearMap.smul_apply, LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul]

private theorem extendedBilinearOperator_natural {A C : Type u} [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] (f : A →ₐ[k] C)
    (x y z : A ⊗[k] V) :
    f.toLinearMap.rTensor V (extendedBilinearOperator B A x y z) =
      extendedBilinearOperator B C (f.toLinearMap.rTensor V x) (f.toLinearMap.rTensor V y)
        (f.toLinearMap.rTensor V z) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | tmul b y =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul c z =>
        simp only [extendedBilinearOperator_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          map_mul]

private def operatorLawOfBilinear : QuadraticOperatorLaw k V where
  op A _ _ := (extendedBilinearOperator B A).toQuadraticMap
  natural f x y := extendedBilinearOperator_natural B f x x y

private theorem operatorLawOfBilinear_tmul (A : Type u) [CommRing A] [Algebra k A]
    (x y : V) :
    (operatorLawOfBilinear B).op A (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y) = 1 ⊗ₜ[k] B x x y := by
  change extendedBilinearOperator B A (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y) = _
  rw [extendedBilinearOperator_tmul, one_mul, one_mul]

private def lawOfBilinear (e : V) (he : ∀ y, B e e y = y) : ParaQuadratic k V where
  toQuadraticOperatorLaw := operatorLawOfBilinear B
  unit := e
  op_unit A _ _ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    change extendedBilinearOperator B A (1 ⊗ₜ[k] e) (1 ⊗ₜ[k] e) (a ⊗ₜ[k] y) = a ⊗ₜ[k] y
    simp only [extendedBilinearOperator_tmul, one_mul, he]

private theorem lawOfBilinear_ground (e : V) (he : ∀ y, B e e y = y) (x y : V) :
    (lawOfBilinear B e he).groundOp x y = B x x y := by
  change TensorProduct.lid k V ((operatorLawOfBilinear B).op k (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)) = _
  rw [operatorLawOfBilinear_tmul, TensorProduct.lid_tmul, one_smul]

open LinearAlgebraicGroups.Descent

private theorem lawOfBilinear_compare
    {A : Type u} [CommRing A] [Algebra k A]
    {W : Type w} [AddCommGroup W] [Module A W]
    (unit : V) (hunit : ∀ y, B unit unit y = y)
    (e : A ⊗[k] V ≃ₗ[A] W) (q : QuadraticMap A W (End A W))
    (h : ∀ x y : V, e (1 ⊗ₜ[k] B x x y) = q (e (1 ⊗ₜ[k] x)) (e (1 ⊗ₜ[k] y))) :
    ∀ x y, e ((lawOfBilinear B unit hunit).op A x y) = q (e x) (e y) := by
  let J := lawOfBilinear B unit hunit
  let Q := e.conj.toLinearMap.compQuadraticMap (J.op A)
  let P := q.comp e.toLinearMap
  letI : Module k (End A W) := Module.compHom _ (algebraMap k A)
  letI : IsScalarTower k A (End A W) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hQP : Q = P := by
    apply baseChange_ext
    intro x
    apply (e.conj.symm.injective)
    apply TensorProduct.AlgebraTensorModule.ext
    intro a y
    apply e.injective
    change e (e.symm (e (J.op A (1 ⊗ₜ[k] x) (e.symm (e (a ⊗ₜ[k] y)))))) =
      e (e.symm (q (e (1 ⊗ₜ[k] x)) (e (a ⊗ₜ[k] y))))
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    rw [show a ⊗ₜ[k] y = a • (1 ⊗ₜ[k] y) by simp [smul_tmul', smul_eq_mul]]
    simp only [map_smul]
    change a • e ((operatorLawOfBilinear B).op A (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)) =
      a • q (e (1 ⊗ₜ[k] x)) (e (1 ⊗ₜ[k] y))
    rw [operatorLawOfBilinear_tmul, h]
  intro x y
  have he := LinearMap.congr_fun (congrArg (fun r : QuadraticMap A (A ⊗[k] V) (End A W) => r x) hQP) (e y)
  change e (J.op A x (e.symm (e y))) = q (e x) (e y) at he
  rwa [LinearEquiv.symm_apply_apply] at he

end ExtendQuadraticLaw

section StableQuadraticOperator

open LinearAlgebraicGroups.Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {W : Type w} [AddCommGroup W] [Module K W] [Module k W] [IsScalarTower k K W]

/-- A fixed unit and an equivariant quadratic operator descend to a law on
all scalar algebras. The comparison also holds in additional scalar
extensions admitting a compatible operator. -/
private theorem exists_fixedQuadraticLaw [FiniteDimensional K W] [FiniteDimensional k K]
    [IsGalois k K] (ρ : SemilinearAction k K W) (q : QuadraticMap K W (End K W))
    (e : ρ.fixed) (he : q e.val = 1)
    (hop : ∀ (g : Gal(K/k)) (x y : W), ρ.act g (q x y) = q (ρ.act g x) (ρ.act g y)) :
    ∃ J : ParaQuadratic k ρ.fixed,
      J.unit = e ∧ (∀ x y : ρ.fixed, (J.groundOp x y).val = q x.val y.val) ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        {N : Type w} [AddCommGroup N] [Module A N]
        (t : A ⊗[k] ρ.fixed ≃ₗ[A] N) (p : QuadraticMap A N (End A N)),
        (∀ x y : ρ.fixed, t (1 ⊗ₜ[k] J.groundOp x y) =
          p (t (1 ⊗ₜ[k] x)) (t (1 ⊗ₜ[k] y))) →
        ∀ x y, t (J.op A x y) = p (t x) (t y) := by
  let j := ρ.fixed.subtype
  let restrict : End K W →ₗ[k] End k ρ.fixed := {
    toFun L := j.leftInverse.comp ((L.restrictScalars k).comp j)
    map_add' L M := by
      apply LinearMap.ext
      intro x
      change j.leftInverse (L (j x) + M (j x)) = j.leftInverse (L (j x)) + j.leftInverse (M (j x))
      exact map_add _ _ _
    map_smul' a L := by
      apply LinearMap.ext
      intro x
      change j.leftInverse (a • L (j x)) = a • j.leftInverse (L (j x))
      exact map_smul _ _ _ }
  let Q : QuadraticMap k ρ.fixed (End k ρ.fixed) :=
    restrict.compQuadraticMap ((q.restrictScalars (S := k)).comp j)
  have hQ (x y : ρ.fixed) : (Q x y).val = q x.val y.val := by
    let z : ρ.fixed := ⟨q x.val y.val, fun g => by rw [hop, x.property g, y.property g]⟩
    change (j.leftInverse (j z)).val = z.val
    rw [LinearMap.leftInverse_apply_of_inj (ρ.fixed).ker_subtype]
  letI : FiniteDimensional k ρ.fixed := ρ.finiteDimensional_fixed.1
  obtain ⟨B, hB⟩ := exists_bilinearRepresentative Q
  have hB' (x y : ρ.fixed) : (B x x y).val = q x.val y.val :=
    (congrArg (fun r : QuadraticMap k ρ.fixed (End k ρ.fixed) => (r x y).val) hB).trans (hQ x y)
  have hu (y : ρ.fixed) : B e e y = y := by
    apply Subtype.ext
    rw [hB', he, Module.End.one_apply]
  refine ⟨lawOfBilinear B e hu, rfl, ?_, ?_⟩
  · intro x y
    rw [lawOfBilinear_ground, hB']
  · intro A _ _ N _ _ t p hp
    apply lawOfBilinear_compare
    intro x y
    simpa only [lawOfBilinear_ground] using hp x y

end StableQuadraticOperator

section AlbertDescent

open LinearAlgebraicGroups.Albert (coordinatesBaseChange_tmul)
open LinearAlgebraicGroups.Albert.CubicSpecification (cubicUnit)
open LinearAlgebraicGroups.Albert.TrialitySpecification (Model modelOp mapModel modelBaseChange)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm mapCoordinates)
open LinearAlgebraicGroups.Descent
open private opQuadratic opQuadratic_apply opUnit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.QuadraticOperators

private def splitOperator (A : Type u) [CommRing A] :
    QuadraticMap A (Model A) (End A (Model A)) :=
  opQuadratic (n := norm A) (fun _ => 1)

private theorem splitOperator_apply (A : Type u) [CommRing A] (x y : Model A) :
    splitOperator A x y = modelOp x y := opQuadratic_apply _ _ _

@[simp] private theorem mapModel_unit {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) : mapModel f (cubicUnit : Model A) = cubicUnit := by
  apply Prod.ext
  · funext i
    exact map_one f
  · funext i
    change Zorn.ofCoordinates (f 0, f ∘ (0 : Fin 3 → A), f ∘ (0 : Fin 3 → A), f 0) = 0
    simp only [map_zero, Function.comp_def, Pi.zero_apply]
    rfl

private theorem modelBaseChange_tmul {K A : Type u} [CommRing K] [CommRing A] [Algebra K A]
    (a : A) (x : Model K) :
    modelBaseChange K A (a ⊗ₜ[K] x) = a • mapModel (algebraMap K A) x := by
  unfold modelBaseChange
  rw [LinearEquiv.trans_apply, coordinatesBaseChange_tmul]
  apply Prod.ext
  · rfl
  · funext i
    exact Zorn.baseChange_tmul a (x.2 i)

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

local instance : Module k (Model K) := Module.compHom _ (algebraMap k K)
local instance : IsScalarTower k K (Model K) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- Coordinates on the scalar extension of the fixed model, using the finite
Galois comparison and the canonical scalar extension of Zorn coordinates. -/
noncomputable def descentModelEquiv (ρ : SemilinearAction k K (Model K))
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    A ⊗[k] ρ.fixed ≃ₗ[A] Model A :=
  ((AlgebraTensorModule.cancelBaseChange k K A A ρ.fixed).symm.trans
    (ρ.descentEquiv.baseChange K A _ _)).trans (modelBaseChange K A)

theorem descentModelEquiv_tmul (ρ : SemilinearAction k K (Model K))
    (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (a : A) (x : ρ.fixed) :
    descentModelEquiv ρ A (a ⊗ₜ[k] x) = a • mapModel (algebraMap K A) x.val := by
  simp only [descentModelEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  change modelBaseChange K A (a ⊗ₜ[K] ρ.descentEquiv (1 ⊗ₜ[k] x)) = _
  rw [SemilinearAction.descentEquiv_tmul, one_smul, modelBaseChange_tmul]

/-- A semilinear action on the split Albert model preserving its unit and
operator gives an Albert law on the fixed vectors. Its comparison holds
over all commutative algebras over the finite Galois splitting field. -/
theorem exists_descendedAlbertLaw (ρ : SemilinearAction k K (Model K))
    (hu : ∀ g, ρ.act g (cubicUnit : Model K) = cubicUnit)
    (hop : ∀ (g : Gal(K/k)) (x y : Model K),
      ρ.act g (modelOp x y) = modelOp (ρ.act g x) (ρ.act g y)) :
    ∃ J : ParaQuadratic k ρ.fixed, IsAlbert J ∧ J.unit.val = cubicUnit ∧
      (∀ x y : ρ.fixed, (J.groundOp x y).val = modelOp x.val y.val) ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A],
        descentModelEquiv ρ A (1 ⊗ₜ[k] J.unit) = cubicUnit ∧
        ∀ x y, descentModelEquiv ρ A (J.op A x y) =
          modelOp (descentModelEquiv ρ A x) (descentModelEquiv ρ A y) := by
  let e : ρ.fixed := ⟨cubicUnit, hu⟩
  obtain ⟨J, hJunit, hground, hcompare⟩ := exists_fixedQuadraticLaw ρ (splitOperator K) e
    (LinearMap.ext fun x => by rw [splitOperator_apply]; exact opUnit _ x)
    (by simpa only [splitOperator_apply] using hop)
  have hunit : J.unit.val = cubicUnit := congrArg Subtype.val hJunit
  have hcompare' (A : Type u) [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
      descentModelEquiv ρ A (1 ⊗ₜ[k] J.unit) = cubicUnit ∧
      ∀ x y, descentModelEquiv ρ A (J.op A x y) =
        modelOp (descentModelEquiv ρ A x) (descentModelEquiv ρ A y) := by
    constructor
    · rw [descentModelEquiv_tmul, one_smul, hunit, mapModel_unit]
    · intro x y
      rw [← splitOperator_apply]
      apply hcompare
      intro z w
      simp only [descentModelEquiv_tmul, one_smul, hground, splitOperator_apply,
        mapModel_operator]
  refine ⟨J, ?_, hunit, (by simpa only [splitOperator_apply] using hground), @hcompare'⟩
  apply (albert_iff_split_octonion_after_cover J).mpr
  exact ⟨K, inferInstance, inferInstance, inferInstance, descentModelEquiv ρ K,
    (hcompare' K).1, (hcompare' K).2⟩

end AlbertDescent

end
section ReferenceSplitField

open LinearAlgebraicGroups.Albert.SplitSpecification
open LinearAlgebraicGroups.Albert.CubicSpecification
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm mapCoordinates)
open LinearAlgebraicGroups.Descent
open LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open scoped TensorProduct

variable {k E K S : Type u} [Field k] [Field E] [Field K] [Field S]
  [Algebra k E] [Algebra k K] [Algebra k S]

local instance : Module k (Model K) := Module.compHom _ (algebraMap k K)
local instance : IsScalarTower k K (Model K) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- A finite Galois layer containing the images of the three embeddings.
The new numbering is obtained by restricting the given numbering along
the actual field inclusion. -/
theorem exists_cubicSplittingLayer [Module.Finite k E] [IsSepClosure k S]
    (numbering : (E →ₐ[k] S) ≃ Fin 3) :
    ∃ (L : FiniteGaloisIntermediateField k S) (e : (E →ₐ[k] L) ≃ Fin 3),
      ∀ f : E →ₐ[k] L, e f = numbering (L.toIntermediateField.val.comp f) := by
  classical
  let b := Module.finBasis k E
  let s : Set S := Set.range fun p : Fin 3 × Fin (Module.finrank k E) => numbering.symm p.1 (b p.2)
  let : Finite s := (Set.finite_range _).to_subtype
  let L := FiniteGaloisIntermediateField.adjoin k s
  have hmem (f : E →ₐ[k] S) (x : E) : f x ∈ L.toIntermediateField := by
    rw [← b.sum_repr x, map_sum]
    apply L.toIntermediateField.toSubalgebra.sum_mem
    intro i _
    rw [map_smul]
    apply L.toIntermediateField.toSubalgebra.smul_mem
    apply FiniteGaloisIntermediateField.subset_adjoin k s
    exact ⟨(numbering f, i), by simp⟩
  let j : (E →ₐ[k] L) → (E →ₐ[k] S) := fun f => L.toIntermediateField.val.comp f
  have hj : Function.Bijective j := by
    constructor
    · intro f g h
      ext x
      exact AlgHom.congr_fun h x
    · intro f
      refine ⟨f.codRestrict L.toIntermediateField.toSubalgebra (hmem f), ?_⟩
      ext x
      rfl
  exact ⟨L, (Equiv.ofBijective j hj).trans numbering, fun _ => rfl⟩

private theorem mapModel_restriction
    (L : FiniteGaloisIntermediateField k S) (σ : Gal(S/k)) (x : Model L) :
    mapModel (algebraMap L S) (mapModel (restriction L σ).toRingHom x) =
      mapModel σ.toRingHom (mapModel (algebraMap L S) x) := by
  rw [← mapModel_comp, ← mapModel_comp]
  congr 1
  ext z
  exact AlgEquiv.restrictNormal_apply L.toIntermediateField σ z

private theorem diagramPermutation_restriction
    (L : FiniteGaloisIntermediateField k S) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (e : (E →ₐ[k] L) ≃ Fin 3)
    (he : ∀ f : E →ₐ[k] L, e f = numbering (L.toIntermediateField.val.comp f))
    (σ : Gal(S/k)) :
    diagramPermutation e (restriction L σ) = diagramPermutation numbering σ := by
  apply Equiv.ext
  intro i
  obtain ⟨f, rfl⟩ := e.surjective i
  change e ((restriction L σ).toAlgHom.comp (e.symm (e f))) =
    numbering (σ.toAlgHom.comp (numbering.symm (e f)))
  rw [Equiv.symm_apply_apply, he ((restriction L σ).toAlgHom.comp f), he f, Equiv.symm_apply_apply]
  congr 1
  ext x
  exact AlgEquiv.restrictNormal_apply L.toIntermediateField σ (f x)

/-- The finite-level comparison intertwines the original Galois action with
permutation of the frame and coefficient conjugation. -/
theorem descentModelEquiv_permutation
    (L : FiniteGaloisIntermediateField k S) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (e : (E →ₐ[k] L) ≃ Fin 3)
    (he : ∀ f : E →ₐ[k] L, e f = numbering (L.toIntermediateField.val.comp f))
    (σ : Gal(S/k)) (x : S ⊗[k] (frameDescentAction (diagramPermutation e)).fixed) :
    let t := descentModelEquiv (frameDescentAction (diagramPermutation e)) S
    t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id x) =
      framePermutation (diagramPermutation numbering σ) (mapModel σ.toRingHom (t x)) := by
  let t := descentModelEquiv (frameDescentAction (diagramPermutation e)) S
  change t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id x) =
    framePermutation (diagramPermutation numbering σ) (mapModel σ.toRingHom (t x))
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
    have hz := z.property (restriction L σ)
    change framePermutation (diagramPermutation e (restriction L σ))
      (mapModel (restriction L σ).toRingHom z.val) = z.val at hz
    have hfix := congrArg (mapModel (algebraMap L S : L →+* S)) hz
    rw [framePermutation_natural, mapModel_restriction, diagramPermutation_restriction L numbering e he] at hfix
    simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, t,
      descentModelEquiv_tmul, mapModel_smul, map_smul, hfix]
    rfl
  | add x y hx hy => simp only [map_add, mapModel_add, hx, hy]

/-- Under the scalar extension comparison the cubic-field inclusion is
evaluation in the numbered embeddings. -/
theorem descentModelEquiv_diagonal
    (L : FiniteGaloisIntermediateField k S) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (e : (E →ₐ[k] L) ≃ Fin 3)
    (he : ∀ f : E →ₐ[k] L, e f = numbering (L.toIntermediateField.val.comp f))
    (a : E) :
    descentModelEquiv (frameDescentAction (diagramPermutation e)) S
      (1 ⊗ₜ[k] diagonalInFrameDescent e a) = (fun i => numbering.symm i a, 0) := by
  rw [descentModelEquiv_tmul, one_smul]
  apply Prod.ext <;> funext i
  · have hi := he (e.symm i)
    rw [Equiv.apply_symm_apply] at hi
    have hf : numbering.symm i = L.toIntermediateField.val.comp (e.symm i) := by
      exact (congrArg numbering.symm hi).trans (numbering.symm_apply_apply _)
    change (algebraMap L S) (e.symm i a) = numbering.symm i a
    rw [hf]
    rfl
  · change Zorn.ofCoordinates ((algebraMap L S) 0, (algebraMap L S) ∘ (0 : Fin 3 → L),
      (algebraMap L S) ∘ (0 : Fin 3 → L), (algebraMap L S) 0) = 0
    simp only [map_zero, Function.comp_def, Pi.zero_apply]
    rfl

theorem frameDescentAction_unit (π : Gal(K/k) →* Equiv.Perm (Fin 3)) (σ : Gal(K/k)) :
    (frameDescentAction π).act σ (cubicUnit : Model K) = cubicUnit := by
  change framePermutation (π σ) (mapModel σ.toRingHom (cubicUnit : Model K)) = cubicUnit
  rw [mapModel_unit, framePermutation_unit]

end ReferenceSplitField

section CubicDiagonal

open LinearAlgebraicGroups.Albert (cubic_diagonal_formulas tracePairing_apply)
open LinearAlgebraicGroups.Albert.CubicSpecification
open LinearAlgebraicGroups.Albert.TrialitySpecification (Model modelOp)
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Albert.SplitSpecification
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open scoped TensorProduct

private theorem modelOp_diagonal {A : Type u} [CommRing A] (a b : Fin 3 → A) :
    modelOp ((a, 0) : Model A) (b, 0) = ((fun i => a i ^ 2 * b i), 0) := by
  let adj (x : Fin 3 → A) : Fin 3 → A := fun i => x (cyclicNext i) * x (cyclicPrev i)
  have hAdj (x : Fin 3 → A) :
      cubicAdjoint (norm A) (fun _ => 1) (x, 0) = (adj x, 0) := by
    apply Prod.ext <;> funext j
    · change _ - _ * norm A 0 = _
      simp [adj]
    · simp [cubicAdjoint, LinearAlgebraicGroups.Composition.AdjointSpecification.conjugate]
  have hTrace : tracePairing (norm A) (fun _ => 1) ((a, 0) : Model A) (b, 0) =
      ∑ j, a j * b j := by
    simp [tracePairing_apply]
  change LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification.applyOperator
    (norm A) (fun _ => 1) (a, 0) (b, 0) = _
  rw [LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification.applyOperator, hTrace, hAdj,
    adjointCross, show (adj a, (0 : Fin 3 → Zorn A)) + (b, 0) = (adj a + b, 0) by simp,
    hAdj, hAdj, hAdj]
  apply Prod.ext <;> funext i
  · simp only [Prod.fst_sub, Pi.sub_apply,
      Fin.sum_univ_three, adj, Pi.add_apply]
    fin_cases i <;> simp [cyclicNext, cyclicPrev] <;> ring
  · simp

variable {k E : Type u} [Field k] [CommRing E] [Algebra k E]
  {V : Type u} [AddCommGroup V] [Module k V]

/-- A ground-level embedding of an associative commutative algebra
intertwining its quadratic operator extends on all test algebras. -/
theorem cubicInclusion_respectsOperator
    (J : ParaQuadratic k V) (d : E →ₗ[k] V)
    (h : ∀ x y : E, d (x ^ 2 * y) = J.groundOp (d x) (d y))
    (A : Type u) [CommRing A] [Algebra k A] (x y : A ⊗[k] E) :
    d.baseChange A (x ^ 2 * y) = J.op A (d.baseChange A x) (d.baseChange A y) := by
  let N := A ⊗[k] E
  let W := A ⊗[k] V
  let f := d.baseChange A
  let l : LinearMap.BilinMap A N N := LinearMap.mul A N
  let Q : QuadraticMap A N (N →ₗ[A] W) :=
    (LinearMap.llcomp A N N W f).compQuadraticMap (l.compQuadraticMap l.toQuadraticMap)
  let P : QuadraticMap A N (N →ₗ[A] W) :=
    (LinearMap.lcomp A W f).compQuadraticMap ((J.op A).comp f)
  have hQP : Q = P := by
    let hMod := Module.compHom (N →ₗ[A] W) (algebraMap k A)
    have hTower := @IsScalarTower.of_algebraMap_smul k A (N →ₗ[A] W) _ _ _ _ hMod.toSMul
      (fun _ _ => rfl)
    refine @baseChange_ext k A E (N →ₗ[A] W) _ _ _ _ _ hMod _ hTower _ Q P ?_
    intro e
    apply TensorProduct.AlgebraTensorModule.ext
    intro a e'
    rw [show a ⊗ₜ[k] e' = a • (1 ⊗ₜ[k] e') by simp [TensorProduct.smul_tmul', smul_eq_mul]]
    simp only [map_smul]
    congr 1
    change f (((1 ⊗ₜ[k] e) * (1 ⊗ₜ[k] e)) * (1 ⊗ₜ[k] e')) =
      J.op A (f (1 ⊗ₜ[k] e)) (f (1 ⊗ₜ[k] e'))
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, one_mul, ← pow_two]
    simp only [f, LinearMap.baseChange_tmul, ParaQuadratic.natural_ground, h]
  have hf := LinearMap.congr_fun (congrArg (fun q : QuadraticMap A N (N →ₗ[A] W) => q x) hQP) y
  change f (x * x * y) = J.op A (f x) (f y) at hf
  simpa only [pow_two] using hf

end CubicDiagonal

section AlbertSchemes

noncomputable section

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open LinearAlgebraicGroups.Specs (ClosedSubgroup)
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open LinearAlgebraicGroups.Albert.SplitSpecification
open TrialitarianAlbertDescentSpecification
open scoped TensorProduct CategoryTheory.MonObj

open private matrixActionEquiv matrixAction_natural basisChange_natural coordinates_zero_iff
  quotientRepresentation representMatrixInclusion spectrumOverProperties
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.AutomorphismScheme

variable {k : Type u} [Field k]
  {V : Type u} [AddCommGroup V] [Module k V]
  {n m : Type u} [Fintype n] [DecidableEq n]

private def matrixAutomorphism (b : Module.Basis n k V) (A : Type u) [CommRing A] [Algebra k A] :
    Matrix.GeneralLinearGroup n A ≃* (A ⊗[k] V ≃ₗ[A] A ⊗[k] V) :=
  (matrixActionEquiv b A).trans (LinearMap.GeneralLinearGroup.generalLinearEquiv A (A ⊗[k] V))

private theorem matrixAutomorphism_apply (b : Module.Basis n k V) {A : Type u}
    [CommRing A] [Algebra k A] (g : Matrix.GeneralLinearGroup n A) (x : A ⊗[k] V) :
    matrixAutomorphism b A g x = matrixAction b A g x := rfl

private def pointwiseMatrices (b : Module.Basis n k V) (v : m → V) : MatrixSubgroup k n where
  subgroup A _ _ :=
    { carrier := {g | ∀ j, matrixAutomorphism b A g (1 ⊗ₜ[k] v j) = 1 ⊗ₜ[k] v j}
      one_mem' := by intro j; rw [map_one]; rfl
      mul_mem' := by
        intro g h hg hh j
        change matrixAutomorphism b A (g * h) (1 ⊗ₜ[k] v j) = _
        rw [map_mul, LinearEquiv.mul_apply, hh j, hg j]
      inv_mem' := by
        intro g hg j
        change matrixAutomorphism b A g⁻¹ (1 ⊗ₜ[k] v j) = _
        rw [map_inv]
        apply (matrixAutomorphism b A g).injective
        change (matrixAutomorphism b A g) ((matrixAutomorphism b A g).symm (1 ⊗ₜ[k] v j)) = _
        rw [LinearEquiv.apply_symm_apply, hg j] }
  map_mem {A C} _ _ _ _ f g hg := by
    intro j
    change matrixAction b C (Matrix.GeneralLinearGroup.map f.toRingHom g) (1 ⊗ₜ[k] v j) = _
    have h := congrArg (f.toLinearMap.rTensor V) (hg j)
    simpa only [matrixAutomorphism_apply, matrixAction_natural, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, map_one] using h

private def pointwiseEquations [Finite m] (b : Module.Basis n k V) (v : m → V) :
    MatrixEquations.{u,u} k n where
  Index := m × n
  finite := inferInstance
  equation A _ _ g j :=
    (b.baseChange A).repr (matrixAction b A g (1 ⊗ₜ[k] v j.1) - 1 ⊗ₜ[k] v j.1) j.2
  natural f g j := by
    rw [← basisChange_natural b f]
    simp only [map_sub, matrixAction_natural, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one]

private theorem pointwiseEquations_iff [Finite m] (b : Module.Basis n k V) (v : m → V)
    (A : Type u) [CommRing A] [Algebra k A] (g : Matrix.GeneralLinearGroup n A) :
    g ∈ (pointwiseMatrices b v).subgroup A ↔
      ∀ j, (pointwiseEquations b v).equation A g j = 0 := by
  constructor
  · intro hg j
    change (b.baseChange A).repr (matrixAction b A g (1 ⊗ₜ[k] v j.1) - 1 ⊗ₜ[k] v j.1) j.2 = 0
    rw [← matrixAutomorphism_apply, hg j.1, sub_self, map_zero]
    rfl
  · intro h j
    apply sub_eq_zero.mp
    exact (coordinates_zero_iff b _).mp (fun i => h (j, i))

private def intersectMatrices (M N : MatrixSubgroup k n) : MatrixSubgroup k n where
  subgroup S _ _ := M.subgroup S ⊓ N.subgroup S
  map_mem f g h := ⟨M.map_mem f g h.1, N.map_mem f g h.2⟩

private theorem cutsOut_intersection
    {M N : MatrixSubgroup k n} {I K : Ideal (MatrixCoordinates k n)}
    (hI : CutsOut I M) (hK : CutsOut K N) : CutsOut (I ⊔ K) (intersectMatrices M N) := by
  intro A _ _ f g hf
  change (g ∈ M.subgroup A ∧ g ∈ N.subgroup A) ↔ I ⊔ K ≤ RingHom.ker f.toRingHom
  rw [sup_le_iff, hI A f g hf, hK A f g hf]
  rfl

variable {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]

omit [Module.Finite k E] in
private theorem fixes_cubicInclusion_iff (c : Module.Basis m k E) (d : E →ₗ[k] V) (A : Type u) [CommRing A]
    [Algebra k A] (g : A ⊗[k] V ≃ₗ[A] A ⊗[k] V) :
    (∀ x, g (d.baseChange A x) = d.baseChange A x) ↔
      ∀ j, g (1 ⊗ₜ[k] d (c j)) = 1 ⊗ₜ[k] d (c j) := by
  constructor
  · intro h j
    simpa only [LinearMap.baseChange_tmul] using h (1 ⊗ₜ[k] c j)
  · intro h
    have hd : g.toLinearMap.comp (d.baseChange A) = d.baseChange A := by
      apply (c.baseChange A).ext
      intro j
      simpa only [Module.Basis.baseChange_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul,
        LinearEquiv.coe_coe]
        using h j
    exact LinearMap.congr_fun hd

open LinearAlgebraicGroups.Albert.Automorphisms (quadraticCoordinates matrixEquationsPresent)

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The automorphism scheme of an Albert law and the closed pointwise stabilizer
of an embedded field can be represented by adjoining its fixing equations
to the operator-preservation equations. -/
theorem exists_albertModel_withCubicStabilizer
    (J : ParaQuadratic k V) (hJ : IsAlbert J) (d : E →ₗ[k] V) (hd : Function.Injective d)
    (hunit : d 1 = J.unit)
    (hoperator : ∀ a b : E, d (a ^ 2 * b) = J.groundOp (d a) (d b)) :
    ∃ (A : AlbertModel k) (B : CubicStabilizer A E) (e : V ≃ₗ[k] A.V),
      J.IsIso A.law e ∧ ∀ a, e (d a) = B.diagonal a := by
  classical
  letI : Module.Finite k V := (freudenthal_finite_projective J hJ.1).1
  let b : Module.Basis (ULift.{u} (Fin (Module.finrank k V))) k V :=
    (Module.finBasis k V).reindex Equiv.ulift.symm
  let cE : Module.Basis (ULift.{u} (Fin (Module.finrank k E))) k E :=
    (Module.finBasis k E).reindex Equiv.ulift.symm
  let v := d ∘ cE
  let Q := J.toJordan (freudenthal_is_jordan J hJ.1)
  obtain ⟨H, c, hH, hAut, _⟩ := quadraticCoordinates b Q
  obtain ⟨f, hF, _⟩ := matrixEquationsPresent k _ (pointwiseMatrices b v) (pointwiseEquations b v)
    (pointwiseEquations_iff b v)
  let I := Ideal.span (Set.range c)
  let K := Ideal.span (Set.range f)
  let M := intersectMatrices H (pointwiseMatrices b v)
  have hM : CutsOut (I ⊔ K) M := cutsOut_intersection hH hF
  let q : MatrixCoordinates k (ULift.{u} (Fin (Module.finrank k V))) ⧸ I →ₐ[k] _ :=
    Ideal.Quotient.factorₐ k (le_sup_left : I ≤ I ⊔ K)
  have hq : Function.Surjective q := Ideal.Quotient.factor_surjective le_sup_left
  obtain ⟨D, G, j, ed, eg, p, a, hj, _, heval⟩ :=
    representMatrixInclusion (quotientRepresentation hM) (quotientRepresentation hH)
      (fun _ => inf_le_left) (CommAlgCat.ofHom q) hq (fun _ _ => rfl)
  have hG := spectrumOverProperties eg
  let evalAut (R : TestAlgebra k) : Points G.X R ≃* H.subgroup R :=
    (a.app R).groupIsoToMulEquiv
  let evalFix (R : TestAlgebra k) : Points D.X R ≃* M.subgroup R :=
    (p.app R).groupIsoToMulEquiv
  have evalInclusion (R : TestAlgebra k) (h : Points D.X R) :
      (evalAut R (h ≫ j.hom.hom)).val = (evalFix R h).val := heval R h
  let A : AlbertModel k := {
    V := V
    law := J
    albert := hJ
    automorphisms := ⟨G, hG.1, hG.2, by
      haveI : IsAffine G.X.left := hG.1
      infer_instance⟩
    action R := ((matrixAutomorphism b R).toMonoidHom.comp (H.subgroup R).subtype).comp
      (evalAut R).toMonoidHom
    faithful R := (matrixAutomorphism b R).injective.comp
      (Subtype.val_injective.comp (evalAut R).injective)
    image R := by
      ext g
      let m := (matrixAutomorphism b R).symm g
      have hm := (matrixAutomorphism b R).apply_symm_apply g
      change (∃ x, matrixAutomorphism b R (evalAut R x).val = g) ↔ _
      rw [← hm]
      simp only [(matrixAutomorphism b R).injective.eq_iff]
      change (∃ x, (evalAut R x).val = m) ↔ _
      have hr : (∃ x, (evalAut R x).val = m) ↔ m ∈ H.subgroup R := by
        constructor
        · rintro ⟨x, hx⟩
          rw [← hx]
          exact (evalAut R x).property
        · intro hx
          exact ⟨(evalAut R).symm ⟨m, hx⟩,
            congrArg Subtype.val ((evalAut R).apply_symm_apply ⟨m, hx⟩)⟩
      have hmPreserves := hAut R m
      dsimp only at hmPreserves
      rw [hr, hmPreserves]
      simp only [Option.mem_some_iff, forall_eq', ← matrixAutomorphism_apply, Set.mem_ofPred_eq]
      rfl
    natural f g x := by
      have h : a.hom.app _ (((schemePoints k).obj G).map f g) =
          H.points.map f (a.hom.app _ g) :=
        DFunLike.congr_fun (congrArg GrpCat.Hom.hom (a.hom.naturality f)) g
      have hv : Matrix.GeneralLinearGroup.map f.hom.toRingHom (evalAut _ g).val =
          (evalAut _ (mapPoints f g)).val :=
        congrArg (fun q : H.subgroup _ => q.val) h.symm
      change f.hom.toLinearMap.rTensor V (matrixAction b _ (evalAut _ g).val x) =
        matrixAction b _ (evalAut _ (mapPoints f g)).val (f.hom.toLinearMap.rTensor V x)
      rw [matrixAction_natural, hv] }
  refine ⟨A, ⟨d, hd, hunit, (fun R => cubicInclusion_respectsOperator J d hoperator R),
    ⟨D, j, hj⟩, ?_⟩, LinearEquiv.refl _ _, ?_, fun _ => rfl⟩
  · intro R g
    have hf := fixes_cubicInclusion_iff cE d R (A.action R g)
    rw [hf]
    change (evalAut R g).val ∈ (pointwiseMatrices b v).subgroup R ↔
      ∃ h : Points D.X R, h ≫ j.hom.hom = g
    constructor
    · intro hg
      let m : M.subgroup R := ⟨(evalAut R g).val, ⟨(evalAut R g).property, hg⟩⟩
      let h := (evalFix R).symm m
      refine ⟨h, (evalAut R).injective (Subtype.ext ?_)⟩
      rw [evalInclusion, (evalFix R).apply_symm_apply]
    · rintro ⟨h, rfl⟩
      rw [evalInclusion]
      exact (evalFix R h).property.2
  · refine ⟨rfl, ?_⟩
    intro R _ _ x y
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id]
    rfl

end
end AlbertSchemes

section ReferenceAlbertModel

open LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open LinearAlgebraicGroups.Albert.CubicSpecification (cubicUnit)
open LinearAlgebraicGroups.Albert.TrialitySpecification (Model modelOp mapModel)
open LinearAlgebraicGroups.Albert.SplitSpecification
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open TrialitarianAlbertDescentSpecification
open scoped TensorProduct

variable {k E S : Type u} [Field k] [Field E] [Field S]
  [Algebra k E] [Algebra k S] [Module.Finite k E] [IsSepClosure k S]

local instance {K : Type u} [Field K] [Algebra k K] : Module k (Model K) :=
  Module.compHom _ (algebraMap k K)
local instance {K : Type u} [Field K] [Algebra k K] : IsScalarTower k K (Model K) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

omit [IsSepClosure k S] in
private theorem changeCoordinates_commutes
    {V W : Type u} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (e : V ≃ₗ[k] W) (σ : Gal(S/k)) (x : S ⊗[k] V) :
    e.baseChange k S V W (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id x) =
      TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id (e.baseChange k S V W x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]


open AlgebraicGeometry CategoryTheory

/-- Split coordinates of the marked algebra on each test algebra equipped
with a map from the splitting field. -/
private structure FrameCharts (J : AlbertModel k) (B : CubicStabilizer J E)
    (numbering : (E →ₐ[k] S) ≃ Fin 3) where
  chart : ∀ R : TestAlgebra k, (CommAlgCat.of k S ⟶ R) → (R ⊗[k] J.V ≃ₗ[R] Model R)
  unit : ∀ R f, chart R f (1 ⊗ₜ[k] J.law.unit) = cubicUnit
  op : ∀ R f x y, chart R f (J.law.op R x y) = modelOp (chart R f x) (chart R f y)
  diagonal : ∀ R f (a : E),
    chart R f (1 ⊗ₜ[k] B.diagonal a) = (fun i => f.hom (numbering.symm i a), 0)
  natural : ∀ {R T : TestAlgebra k} (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T)
    (x : R ⊗[k] J.V),
    mapModel g.hom.toRingHom (chart R f x) =
      chart T (f ≫ g) (TensorProduct.map g.hom.toLinearMap LinearMap.id x)
  permutation : ∀ (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (σ : Gal(S/k))
    (x : R ⊗[k] J.V),
    chart R f x = framePermutation (diagramPermutation numbering σ)
      (chart R (CommAlgCat.ofHom σ.toAlgHom ≫ f) x)

set_option linter.style.haveILetI false in
/-- The reference Albert algebra and the closed pointwise stabilizer of the
cubic diagonal are obtained by the permutation descent prescribed by the
three embeddings. -/
private theorem exists_permutationReferenceWithCharts (numbering : (E →ₐ[k] S) ≃ Fin 3) :
    ∃ (J : AlbertModel k) (B : CubicStabilizer J E), IsPermutationDescent J B numbering ∧ Nonempty (FrameCharts J B numbering) := by
  obtain ⟨L, labels, hlabels⟩ := exists_cubicSplittingLayer numbering
  let ρ := frameDescentAction (diagramPermutation labels)
  obtain ⟨J, hJ, hunit, hground, hcompare⟩ :=
    exists_descendedAlbertLaw ρ (frameDescentAction_unit _) (frameDescentAction_operator _)
  let d := diagonalInFrameDescent labels
  have hunit' : d 1 = J.unit := by
    apply Subtype.ext
    rw [hunit]
    change ((fun i => labels.symm i 1), 0) = cubicUnit
    simp [map_one, cubicUnit]
  have hop' (x y : E) : d (x ^ 2 * y) = J.groundOp (d x) (d y) := by
    apply Subtype.ext
    rw [hground]
    change ((fun i => labels.symm i (x ^ 2 * y)), 0) =
      modelOp ((fun i => labels.symm i x), 0) ((fun i => labels.symm i y), 0)
    rw [modelOp_diagonal]
    simp only [map_mul, map_pow]
  obtain ⟨A, B, e, he, hd⟩ :=
    exists_albertModel_withCubicStabilizer J hJ d (diagonalInFrameDescent_injective labels) hunit' hop'
  let es := e.baseChange k S ρ.fixed A.V
  let t₀ := descentModelEquiv ρ S
  let t := es.symm.trans t₀
  have ht (x : S ⊗[k] ρ.fixed) : t (es x) = t₀ x := by
    simp only [t, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  let changeRing (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) :=
    f.hom.comp L.toIntermediateField.val
  let t' (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) : R ⊗[k] A.V ≃ₗ[R] Model R := by
    letI : Algebra L R := (changeRing R f).toRingHom.toAlgebra
    letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq fun x => ((changeRing R f).commutes x).symm
    exact (e.baseChange k R ρ.fixed A.V).symm.trans (descentModelEquiv ρ R)
  have t'_tmul (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (r : R) (x : A.V) :
      t' R f (r ⊗ₜ[k] x) = r • mapModel (changeRing R f).toRingHom (e.symm x).val := by
    letI : Algebra L R := (changeRing R f).toRingHom.toAlgebra
    letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq fun x => ((changeRing R f).commutes x).symm
    change descentModelEquiv ρ R (r ⊗ₜ[k] e.symm x) =
      r • mapModel (changeRing R f).toRingHom (e.symm x).val
    rw [descentModelEquiv_tmul]
    rfl
  have HC : Nonempty (FrameCharts A B numbering) := by
    refine ⟨⟨t', ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro R f
      letI : Algebra L R := (changeRing R f).toRingHom.toAlgebra
      letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq fun x => ((changeRing R f).commutes x).symm
      have he' : e.symm A.law.unit = J.unit := (e.symm_apply_eq).mpr he.1.symm
      rw [t'_tmul, one_smul, he', hunit, mapModel_unit]
    · intro R f x y
      letI : Algebra L R := (changeRing R f).toRingHom.toAlgebra
      letI : IsScalarTower k L R := IsScalarTower.of_algebraMap_eq fun x => ((changeRing R f).commutes x).symm
      let eR := e.baseChange k R ρ.fixed A.V
      obtain ⟨x, rfl⟩ := eR.surjective x
      obtain ⟨y, rfl⟩ := eR.surjective y
      have hop : eR (J.op R x y) = A.law.op R (eR x) (eR y) := he.2 R x y
      have htR (x : R ⊗[k] ρ.fixed) : t' R f (eR x) = descentModelEquiv ρ R x := by
        change descentModelEquiv ρ R (eR.symm (eR x)) = _
        rw [LinearEquiv.symm_apply_apply]
      rw [← hop, htR, htR, htR]
      exact (hcompare R).2 x y
    · intro R f a
      rw [t'_tmul, one_smul, ← hd a, LinearEquiv.symm_apply_apply]
      have h := descentModelEquiv_diagonal L numbering labels hlabels a
      rw [descentModelEquiv_tmul, one_smul] at h
      have hh : mapModel (changeRing R f).toRingHom (d a).val =
          mapModel f.hom.toRingHom (mapModel (algebraMap L S) (d a).val) :=
        (mapModel_comp (algebraMap L S) f.hom.toRingHom (d a).val).symm
      rw [hh, h]
      exact Prod.ext rfl (funext fun i => by
        change Composition.ZornSpecification.mapCoordinates f.hom.toRingHom (0 : Composition.Zorn S) = 0
        change Composition.Zorn.ofCoordinates (f.hom 0, f.hom ∘ (0 : Fin 3 → S),
          f.hom ∘ (0 : Fin 3 → S), f.hom 0) = 0
        simp only [map_zero, Function.comp_def, Pi.zero_apply]
        rfl)
    · intro R T f g x
      induction x using TensorProduct.inductionOn with
      | tmul r x =>
        rw [TensorProduct.map_tmul, LinearMap.id_apply, t'_tmul, t'_tmul, mapModel_smul,
          ← mapModel_comp]
        rfl
      | add x y hx hy =>
        simp only [map_add, mapModel_add, hx, hy]
    · intro R f σ x
      induction x using TensorProduct.inductionOn with
      | tmul r x =>
        let z := (e.symm x).val
        have hfix : framePermutation (diagramPermutation labels (restriction L σ))
            (mapModel (restriction L σ).toRingHom z) = z :=
          (e.symm x).property (restriction L σ)
        have hn : mapModel (changeRing R f).toRingHom z =
            mapModel f.hom.toRingHom (mapModel (algebraMap L S) z) :=
          (mapModel_comp (algebraMap L S) f.hom.toRingHom z).symm
        have hm : mapModel (changeRing R (CommAlgCat.ofHom σ.toAlgHom ≫ f)).toRingHom z =
            mapModel f.hom.toRingHom (mapModel σ.toRingHom (mapModel (algebraMap L S) z)) := by
          rw [← mapModel_comp, ← mapModel_comp]
          rfl
        rw [t'_tmul, t'_tmul, map_smul]
        change r • mapModel (changeRing R f).toRingHom z = _
        rw [hn, hm, ← mapModel_restriction L σ, ← framePermutation_natural,
          ← framePermutation_natural, ← diagramPermutation_restriction L numbering labels hlabels σ, hfix]
      | add x y hx hy =>
        simp only [map_add, hx, hy]
  refine ⟨A, B, ?_, HC⟩
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · rw [← show es (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] A.law.unit by change 1 ⊗ₜ[k] e J.unit = _; rw [he.1]]
    exact (ht _).trans (hcompare S).1
  · intro x y
    obtain ⟨x, rfl⟩ := es.surjective x
    obtain ⟨y, rfl⟩ := es.surjective y
    have hop : es (J.op S x y) = A.law.op S (es x) (es y) := he.2 S x y
    rw [← hop, ht, ht, ht]
    exact (hcompare S).2 x y
  · intro a
    rw [← show es (1 ⊗ₜ[k] d a) = 1 ⊗ₜ[k] B.diagonal a by change 1 ⊗ₜ[k] e (d a) = _; rw [hd a]]
    exact (ht _).trans (descentModelEquiv_diagonal L numbering labels hlabels a)
  · intro σ
    let π := diagramPermutation numbering σ
    refine ⟨π, fun f => ?_, ?_⟩
    · change numbering (σ.toAlgHom.comp (numbering.symm (numbering f))) =
        numbering (σ.toAlgHom.comp f)
      rw [Equiv.symm_apply_apply]
    · intro x
      obtain ⟨x, rfl⟩ := es.surjective x
      have hz : t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id (es x)) =
          framePermutation π (mapModel σ.toRingHom (t (es x))) := by
        rw [← changeCoordinates_commutes, ht, ht]
        exact descentModelEquiv_permutation L numbering labels hlabels σ x
      change (∀ i, (t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id (es x))).1 (π i) =
        (mapModel σ.toRingHom (t (es x))).1 i) ∧
        ∀ i, (t (TensorProduct.map σ.toAlgHom.toLinearMap LinearMap.id (es x))).2 (π i) =
          if Equiv.Perm.sign π = 1 then (mapModel σ.toRingHom (t (es x))).2 i else
            conjugate (norm S) ((mapModel σ.toRingHom (t (es x))).2 i)
      rw [hz]
      constructor
      · exact framePermutation_diagonal π _
      · intro i
        rw [framePermutation_block]
        by_cases h : Equiv.Perm.sign π = 1
        · simp [blockPermutation, h]
        · simp [blockPermutation, h, zornConjugation_apply]

theorem exists_permutationReference (numbering : (E →ₐ[k] S) ≃ Fin 3) :
    ∃ (J : AlbertModel k) (B : CubicStabilizer J E), IsPermutationDescent J B numbering := by
  obtain ⟨J, B, h, _⟩ := exists_permutationReferenceWithCharts numbering
  exact ⟨J, B, h⟩

end ReferenceAlbertModel

section SplitCubicCoordinates

open scoped TensorProduct

variable {k E K : Type u} [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]

private def evaluateCubicCoordinate (e : E →ₐ[k] K) : K ⊗[k] E →ₐ[K] K :=
  Algebra.TensorProduct.lift (AlgHom.id K K) e (fun _ _ => Commute.all _ _)

/-- The algebra map taking a tensor to its values in the three numbered
embeddings. -/
def evaluateCubicDiagonal (numbering : (E →ₐ[k] K) ≃ Fin 3) : K ⊗[k] E →ₐ[K] (Fin 3 → K) :=
  AlgHom.pi fun i => evaluateCubicCoordinate (numbering.symm i)

@[simp] theorem evaluateCubicDiagonal_tmul (numbering : (E →ₐ[k] K) ≃ Fin 3)
    (a : K) (e : E) (i : Fin 3) :
    evaluateCubicDiagonal numbering (a ⊗ₜ[k] e) i = a * numbering.symm i e := rfl

private theorem evaluateCubicDiagonal_surjective (numbering : (E →ₐ[k] K) ≃ Fin 3) :
    Function.Surjective (evaluateCubicDiagonal numbering) := by
  classical
  let p := evaluateCubicDiagonal numbering
  have hsingle (i : Fin 3) : Pi.single i 1 ∈ LinearMap.range p.toLinearMap := by
    let I := {j : Fin 3 // j ≠ i}
    have hex (j : I) : ∃ a : E, numbering.symm i a ≠ numbering.symm j.val a := by
      by_contra! h
      exact j.property (numbering.symm.injective (AlgHom.ext h)).symm
    choose a ha using hex
    let w (j : I) : K ⊗[k] E := (numbering.symm i (a j) - numbering.symm j.val (a j))⁻¹ •
      ((1 ⊗ₜ[k] a j) - (numbering.symm j.val (a j) ⊗ₜ[k] 1))
    have hw (j : I) (l : Fin 3) :
        evaluateCubicCoordinate (numbering.symm l) (w j) =
          (numbering.symm i (a j) - numbering.symm j.val (a j))⁻¹ *
            (numbering.symm l (a j) - numbering.symm j.val (a j)) := by
      simp [w, evaluateCubicCoordinate, smul_eq_mul]
    refine ⟨∏ j, w j, ?_⟩
    funext l
    change evaluateCubicCoordinate (numbering.symm l) (∏ j, w j) = (Pi.single i 1 : Fin 3 → K) l
    rw [map_prod]
    by_cases h : l = i
    · subst l
      rw [Pi.single_eq_same]
      apply Finset.prod_eq_one
      intro j _
      rw [hw]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr (ha j))
    · rw [Pi.single_eq_of_ne h]
      exact Finset.prod_eq_zero (Finset.mem_univ (⟨l, h⟩ : I)) (by rw [hw]; simp)
  change Function.Surjective p.toLinearMap
  apply LinearMap.range_eq_top.mp
  apply eq_top_iff.mpr
  intro x _
  rw [← (Pi.basisFun K (Fin 3)).sum_repr x]
  apply Submodule.sum_mem
  intro i _
  rw [Pi.basisFun_apply]
  exact Submodule.smul_mem _ _ (hsingle i)

/-- Evaluation is the split cubic étale algebra isomorphism. The proof
constructs each coordinate idempotent by interpolation in distinct
embeddings. -/
noncomputable def cubicDiagonalEquiv [Module.Finite k E] (degree : Module.finrank k E = 3)
    (numbering : (E →ₐ[k] K) ≃ Fin 3) : K ⊗[k] E ≃ₐ[K] (Fin 3 → K) := by
  let p := evaluateCubicDiagonal numbering
  have hs := evaluateCubicDiagonal_surjective numbering
  have hdim : Module.finrank K (K ⊗[k] E) = Module.finrank K (Fin 3 → K) := by
    rw [Module.finrank_baseChange, degree, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  exact AlgEquiv.ofBijective p
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := p.toLinearMap) hdim).mpr hs, hs⟩

@[simp] theorem cubicDiagonalEquiv_tmul [Module.Finite k E] (degree : Module.finrank k E = 3)
    (numbering : (E →ₐ[k] K) ≃ Fin 3) (a : K) (e : E) (i : Fin 3) :
    cubicDiagonalEquiv degree numbering (a ⊗ₜ[k] e) i = a * numbering.symm i e := rfl

end SplitCubicCoordinates

section RelatedSimilarities

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)

variable {R : Type u} [CommRing R]

/-- A related similarity of the three Peirce spaces, with its norm
multipliers and the common multiplier on the trilinear term. -/
def IsRelatedSimilarity (h : Triple R) (μ : Fin 3 → Rˣ) (ν : Rˣ) : Prop :=
  (∀ i x, norm R (h i x) = (μ i : R) * norm R x) ∧
    (∀ i x y, (ν : R) • h i (conjugate (norm R) (x * y)) =
      (μ i : R) • conjugate (norm R) (h (cyclicNext i) x * h (cyclicPrev i) y)) ∧
    (∏ i, μ i) = ν ^ 2

private theorem product_cyclic (a : Fin 3 → Rˣ) (i : Fin 3) :
    (∏ j, a j) = a i * (a (cyclicNext i) * a (cyclicPrev i)) := by
  rw [Fin.prod_univ_three]
  fin_cases i
  · change a 0 * a 1 * a 2 = a 0 * (a 1 * a 2)
    exact mul_assoc _ _ _
  · change a 0 * a 1 * a 2 = a 1 * (a 2 * a 0)
    ac_rfl
  · change a 0 * a 1 * a 2 = a 2 * (a 0 * a 1)
    ac_rfl

/-- Scaling a related triple gives the stated similarity multipliers.
Conversely, a triple of this form satisfies the similarity identities
exactly when the remaining triple is related. -/
theorem isRelatedSimilarity_scaled_iff (t : Fin 3 → Rˣ) (h : Triple R) :
    IsRelatedSimilarity (scalarTriple t * h) (fun i => t i ^ 2) (∏ i, t i) ↔ IsRelated h := by
  have hn (i : Fin 3) (x : Zorn R) :
      norm R ((scalarTriple t * h) i x) = ((t i ^ 2 : Rˣ) : R) * norm R (h i x) := by
    simp only [Pi.mul_apply, LinearEquiv.mul_apply, scalarTriple_apply, QuadraticMap.map_smul,
      smul_eq_mul, pow_two, Units.val_mul]
  let a (i : Fin 3) : Rˣ := t i ^ 2 * t (cyclicNext i) * t (cyclicPrev i)
  have ha (i : Fin 3) : (∏ j, t j) * t i = a i := by
    rw [product_cyclic t i]
    dsimp only [a]
    rw [pow_two]
    ac_rfl
  have hleft (i : Fin 3) (x y : Zorn R) :
      ((∏ j, t j : Rˣ) : R) • (scalarTriple t * h) i (conjugate (norm R) (x * y)) =
        (a i : R) • h i (conjugate (norm R) (x * y)) := by
    simp only [Pi.mul_apply, LinearEquiv.mul_apply, scalarTriple_apply, smul_smul,
      ← Units.val_mul, ha]
  have hright (i : Fin 3) (x y : Zorn R) :
      ((t i ^ 2 : Rˣ) : R) • conjugate (norm R)
        ((scalarTriple t * h) (cyclicNext i) x * (scalarTriple t * h) (cyclicPrev i) y) =
        (a i : R) • conjugate (norm R) (h (cyclicNext i) x * h (cyclicPrev i) y) := by
    simp only [Pi.mul_apply, LinearEquiv.mul_apply, scalarTriple_apply, smul_mul_assoc,
      mul_smul_comm, smul_smul, map_smul, ← Units.val_mul]
    congr 2
    dsimp only [a]
    ac_rfl
  constructor
  · rintro ⟨hN, hC, _⟩
    refine ⟨fun i x => ?_, fun i x y => ?_⟩
    · have hh := hN i x
      rw [hn] at hh
      exact (t i ^ 2).isUnit.mul_left_cancel hh
    · have hh := hC i x y
      rw [hleft, hright] at hh
      exact (LinearEquiv.smulOfUnit (a i) : Zorn R ≃ₗ[R] Zorn R).injective hh
  · intro hh
    refine ⟨fun i x => (hn i x).trans (congrArg _ (hh.1 i x)), fun i x y => ?_, ?_⟩
    · rw [hleft, hright, hh.2]
    · rw [Finset.prod_pow]

/-- When the total norm multiplier is the square of the trilinear
multiplier, the three square roots can be chosen fppf locally with the
prescribed product. -/
theorem trialityMultipliers_lift_afterFaithfullyFlat (R : Type u) [CommRing R]
    (μ : Fin 3 → Rˣ) (ν : Rˣ) (hμ : (∏ i, μ i) = ν ^ 2) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A),
      Module.FaithfullyFlat R A ∧ ∃ x : Fin 3 → Aˣ,
        (∀ i, x i ^ 2 = Units.map (algebraMap R A).toMonoidHom (μ i)) ∧
          (∏ i, x i) = Units.map (algebraMap R A).toMonoidHom ν := by
  obtain ⟨A, _, _, hA, x, hx⟩ := adjoinUnitSquareRoots 3 R μ
  let j := Units.map (algebraMap R A).toMonoidHom
  let c := j ν / (∏ i, x i)
  have hx' (i : Fin 3) : x i ^ 2 = j (μ i) := hx i
  have hc : c ^ 2 = 1 := by
    simp only [c, div_pow, ← map_pow, ← hμ, map_prod, ← Finset.prod_pow, hx', div_self']
  let y : Fin 3 → Aˣ := fun i => if i = 0 then c * x i else x i
  refine ⟨A, inferInstance, inferInstance, hA, y, ?_, ?_⟩
  · intro i
    by_cases h : i = 0 <;> simp [y, h, mul_pow, hc, hx]
  · rw [Fin.prod_univ_three, show y 0 = c * x 0 by simp [y],
      show y 1 = x 1 by simp [y], show y 2 = x 2 by simp [y]]
    change (j ν / (∏ i, x i)) * x 0 * x 1 * x 2 = j ν
    rw [Fin.prod_univ_three]
    calc
      _ = (j ν / (x 0 * x 1 * x 2)) * (x 0 * x 1 * x 2) := by ac_rfl
      _ = j ν := div_mul_cancel _ _

end RelatedSimilarities

section FrameStabilizerPoints

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Albert.FrameSpecification (frameAxis)
open LinearAlgebraicGroups.Albert.CubicSpecification (cubicUnit diagonalCoordinates)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open TrialitarianAlbertDescentSpecification
open scoped TensorProduct CategoryTheory.MonObj

variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  {J : AlbertModel k} (B : CubicStabilizer J E) (A : TestAlgebra k)

private theorem diagonal_sum (d : Fin 3 → A) :
    (d, (0 : Fin 3 → _root_.LinearAlgebraicGroups.Composition.Zorn A)) =
      ∑ j : Fin 3, d j • (frameAxis j : Model A) := by
  classical
  apply Prod.ext <;> funext i
  · simp [Prod.fst_sum, Finset.sum_apply, frameAxis, diagonalCoordinates, Pi.single_apply,
      smul_eq_mul, mul_ite]
  · simp [Prod.snd_sum, Finset.sum_apply, frameAxis, diagonalCoordinates]

set_option backward.isDefEq.respectTransparency false in
/-- Under a split chart identifying the entire cubic diagonal, the actual
stabilizer points are the ordered-frame stabilizer. This applies to
test algebras with nilpotents as well. -/
theorem cubicStabilizerPoints_equiv_frameStabilizer
    (t : A ⊗[k] J.V ≃ₗ[A] Model A)
    (hunit : t (1 ⊗ₜ[k] J.law.unit) = cubicUnit)
    (hop : ∀ x y, t (J.law.op A x y) = modelOp (t x) (t y))
    (hdiag : Set.range (fun x => t (B.diagonal.baseChange A x)) = {v | v.2 = 0}) :
    ∃ e : Points B.stabilizer.group.X A ≃* frameStabilizer (R := A),
      ∀ a x, (e a).val (t x) = t (J.action A (a ≫ B.stabilizer.inclusion.hom.hom) x) := by
  let X := A ⊗[k] J.V
  let Y := Model A
  let inc : Points B.stabilizer.group.X A →* Points J.automorphisms.val.X A :=
    (((groupPointsFunctor k).map B.stabilizer.inclusion).app A).hom
  let conjugation : (X ≃ₗ[A] X) →* (Y ≃ₗ[A] Y) := {
    toFun := fun g => t.symm.trans (g.trans t)
    map_one' := LinearEquiv.ext fun x => t.apply_symm_apply x
    map_mul' := fun f g => LinearEquiv.ext fun x => by
      change t (f (g (t.symm x))) = t (f (t.symm (t (g (t.symm x)))))
      rw [LinearEquiv.symm_apply_apply] }
  let action := conjugation.comp ((J.action A).comp inc)
  have haction (b : Points B.stabilizer.group.X A) (x : X) :
      action b (t x) = t (J.action A (inc b) x) := by
    change t (J.action A (inc b) (t.symm (t x))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hfaithful : Function.Injective action := by
    intro b c hbc
    have hj : J.action A (inc b) = J.action A (inc c) := by
      apply LinearEquiv.ext
      intro x
      exact t.injective ((haction b x).symm.trans ((LinearEquiv.congr_fun hbc (t x)).trans (haction c x)))
    let : IsClosedImmersion B.stabilizer.inclusion.hom.hom.left := B.stabilizer.isClosedImmersion
    let : Mono B.stabilizer.inclusion.hom.hom := Over.mono_of_mono_left _
    exact (cancel_mono B.stabilizer.inclusion.hom.hom).mp (J.faithful A hj)
  have hmem (b : Points B.stabilizer.group.X A) : action b ∈ frameStabilizer (R := A) := by
    change FixesFrame (action b)
    constructor
    · intro i
      have haxis : (frameAxis i : Model A) ∈ Set.range (fun x => t (B.diagonal.baseChange A x)) := by
        rw [hdiag]
        rfl
      obtain ⟨x, hx⟩ := haxis
      change t (B.diagonal.baseChange A x) = frameAxis i at hx
      rw [← hx]
      have hfix := (B.fixesExactly A (inc b)).mpr ⟨b, rfl⟩
      rw [haction, hfix]
    · intro x y
      obtain ⟨x, rfl⟩ := t.surjective x
      obtain ⟨y, rfl⟩ := t.surjective y
      have hg : J.action A (inc b) ∈ Set.range (J.action A) := ⟨inc b, rfl⟩
      rw [J.image A] at hg
      have hg' : ∀ x y, J.action A (inc b) (J.law.op A x y) =
          J.law.op A (J.action A (inc b) x) (J.action A (inc b) y) := hg.2
      rw [← hop, haction, hg', hop, haction, haction]
  let f : Points B.stabilizer.group.X A →* frameStabilizer (R := A) :=
    action.codRestrict _ hmem
  have hsurj : Function.Surjective f := by
    intro g
    have hg : FixesFrame g.val := g.property
    have hfix (x : Y) (hx : x.2 = 0) : g.val x = x := by
      obtain ⟨d, v⟩ := x
      change v = 0 at hx
      subst v
      rw [diagonal_sum A]
      simp only [map_sum, map_smul, hg.1]
    let a : X ≃ₗ[A] X := t.trans (g.val.trans t.symm)
    have ha (x : X) : t (a x) = g.val (t x) := t.apply_symm_apply _
    have ha' : a ∈ Set.range (J.action A) := by
      rw [J.image A]
      constructor
      · apply t.injective
        rw [ha, hunit]
        exact hfix cubicUnit rfl
      · intro x y
        apply t.injective
        rw [ha, hop, hg.2, hop, ha, ha]
    obtain ⟨p, hp⟩ := ha'
    have hfixed (x : A ⊗[k] E) : J.action A p (B.diagonal.baseChange A x) =
        B.diagonal.baseChange A x := by
      rw [hp]
      apply t.injective
      rw [ha]
      apply hfix
      have hx : t (B.diagonal.baseChange A x) ∈ Set.range (fun x => t (B.diagonal.baseChange A x)) :=
        ⟨x, rfl⟩
      rw [hdiag] at hx
      exact hx
    obtain ⟨b, hb⟩ := (B.fixesExactly A p).mp hfixed
    refine ⟨b, Subtype.ext (LinearEquiv.ext fun y => ?_)⟩
    obtain ⟨x, rfl⟩ := t.surjective y
    change action b (t x) = g.val (t x)
    rw [haction, show inc b = p from hb, hp, ha]
  refine ⟨MulEquiv.ofBijective f ⟨fun _ _ h => hfaithful (congrArg Subtype.val h), hsurj⟩, ?_⟩
  exact haction

/-- The cubic diagonal fills the diagonal coordinates over every scalar
algebra over a splitting field. -/
theorem splitChart_cubicDiagonalRange
    [Module.Finite k E] (degree : Module.finrank k E = 3)
    {K : Type u} [Field K] [Algebra k K] [Algebra K A] [IsScalarTower k K A]
    (numbering : (E →ₐ[k] K) ≃ Fin 3)
    (t : A ⊗[k] J.V ≃ₗ[A] Model A)
    (ht : ∀ e : E, t (1 ⊗ₜ[k] B.diagonal e) =
      (fun i => (algebraMap K A) (numbering.symm i e), 0)) :
    Set.range (fun x => t (B.diagonal.baseChange A x)) = {v | v.2 = 0} := by
  let eval := cubicDiagonalEquiv degree numbering
  let l : A ⊗[k] E ≃ₗ[A] (Fin 3 → A) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange k K A A E).symm.trans
      (eval.toLinearEquiv.baseChange K A _ _)).trans (TensorProduct.piScalarRight K A A (Fin 3))
  have hl (r : A) (e : E) (i : Fin 3) :
      l (r ⊗ₜ[k] e) i = r * (algebraMap K A) (numbering.symm i e) := by
    simp only [l, LinearEquiv.trans_apply, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    change TensorProduct.piScalarRight K A A (Fin 3)
      (r ⊗ₜ[K] eval (1 ⊗ₜ[k] e)) i = _
    rw [TensorProduct.piScalarRight_apply]
    change (eval (1 ⊗ₜ[k] e) i) • r = _
    simp [eval, Algebra.smul_def, mul_comm]
  have h (z : A ⊗[k] E) : t (B.diagonal.baseChange A z) = (l z, 0) := by
    induction z using TensorProduct.inductionOn with
    | tmul r e =>
      have hm : r ⊗ₜ[k] B.diagonal e = r • (1 ⊗ₜ[k] B.diagonal e) := by
        simp [TensorProduct.smul_tmul', smul_eq_mul]
      rw [LinearMap.baseChange_tmul, hm, map_smul, ht]
      apply Prod.ext
      · funext i
        exact (hl r e i).symm
      · simp
    | add x y hx hy => simp [hx, hy]
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    change (t (B.diagonal.baseChange A z)).2 = 0
    rw [h]
  · intro hv
    have hv' : v.2 = 0 := hv
    obtain ⟨z, hz⟩ := l.surjective v.1
    refine ⟨z, ?_⟩
    change t (B.diagonal.baseChange A z) = v
    rw [h, hz]
    exact Prod.ext rfl hv'.symm

end FrameStabilizerPoints

section SimilarityGroup

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open scoped BigOperators

variable {R : Type u} [CommRing R]

private def quotientNormMultiplier (q : Fin 3 → Rˣ) (i : Fin 3) : Rˣ :=
  (q (cyclicNext i) * q (cyclicPrev i))⁻¹

/-- Related similarities in composition-multiplier coordinates. The second
coordinate is the quotient parameter, the inverse of the factor relating the
product of two transformed vectors to the transform of their product. -/
def relatedSimilarities : Subgroup (Triple R × (Fin 3 → Rˣ)) where
  carrier := {p |
    (∀ i x, norm R (p.1 i x) = (quotientNormMultiplier p.2 i : R) * norm R x) ∧
    ∀ i x y, p.1 i (conjugate (norm R) (x * y)) =
      (p.2 i : R) • conjugate (norm R) (p.1 (cyclicNext i) x * p.1 (cyclicPrev i) y)}
  one_mem' := by
    change (∀ i x, norm R x = (quotientNormMultiplier (R := R) 1 i : R) * norm R x) ∧
      ∀ i x y, conjugate (norm R) (x * y) = (1 : R) • conjugate (norm R) (x * y)
    simp [quotientNormMultiplier]
  mul_mem' := by
    intro g h hg hh
    obtain ⟨ng, cg⟩ := hg
    obtain ⟨nh, ch⟩ := hh
    constructor
    · intro i x
      change norm R (g.1 i (h.1 i x)) = (quotientNormMultiplier (g.2 * h.2) i : R) * norm R x
      rw [ng, nh]
      have hm : quotientNormMultiplier (g.2 * h.2) i =
          quotientNormMultiplier g.2 i * quotientNormMultiplier h.2 i := by
        simp only [quotientNormMultiplier, Pi.mul_apply, mul_inv_rev]
        ac_rfl
      rw [hm, Units.val_mul, mul_assoc]
    · intro i x y
      change g.1 i (h.1 i (conjugate (norm R) (x * y))) =
        ((g.2 i * h.2 i : Rˣ) : R) • conjugate (norm R)
          (g.1 (cyclicNext i) (h.1 (cyclicNext i) x) *
            g.1 (cyclicPrev i) (h.1 (cyclicPrev i) y))
      rw [ch, map_smul, cg, smul_smul, Units.val_mul, mul_comm (g.2 i : R)]
  inv_mem' := by
    intro g hg
    obtain ⟨ng, cg⟩ := hg
    constructor
    · intro i x
      change norm R ((g.1 i).symm x) = (quotientNormMultiplier g.2⁻¹ i : R) * norm R x
      have hm : quotientNormMultiplier g.2⁻¹ i = (quotientNormMultiplier g.2 i)⁻¹ := by
        simp only [quotientNormMultiplier, Pi.inv_apply, mul_inv_rev, inv_inv, mul_comm]
      rw [hm]
      conv_rhs => rw [← (g.1 i).apply_symm_apply x, ng i]
      simp only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    · intro i x y
      change (g.1 i).symm (conjugate (norm R) (x * y)) =
        (((g.2 i)⁻¹ : Rˣ) : R) • conjugate (norm R) ((g.1 (cyclicNext i)).symm x * (g.1 (cyclicPrev i)).symm y)
      apply (g.1 i).injective
      rw [LinearEquiv.apply_symm_apply, map_smul, cg]
      simp only [LinearEquiv.apply_symm_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

abbrev RelatedSimilarities (R : Type u) [CommRing R] := ↥(relatedSimilarities (R := R))

/-- The quotient of the related-similarity group by the triality group. -/
def compositionQuotient : RelatedSimilarities R →* (Fin 3 → Rˣ) where
  toFun p := p.val.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Inclusion of the related triples in the related-similarity group. -/
def relatedTripleInclusion : relatedTriples (R := R) →* RelatedSimilarities R where
  toFun p := ⟨(p.val, 1), by
    refine ⟨?_, ?_⟩
    · intro i x
      simpa [quotientNormMultiplier] using p.property.1 i x
    · intro i x y
      simpa using p.property.2 i x y⟩
  map_one' := rfl
  map_mul' _ _ := by
    apply Subtype.ext
    exact Prod.ext rfl (one_mul 1).symm

theorem compositionQuotient_kernel (p : RelatedSimilarities R) :
    compositionQuotient p = 1 ↔ p ∈ (relatedTripleInclusion (R := R)).range := by
  constructor
  · intro hp
    have h : p.val.2 = 1 := hp
    refine ⟨⟨p.val.1, ?_⟩, Subtype.ext (Prod.ext rfl h.symm)⟩
    obtain ⟨hn, hc⟩ := p.property
    exact ⟨by simpa [quotientNormMultiplier, h] using hn, by simpa [h] using hc⟩
  · rintro ⟨p, rfl⟩
    rfl

theorem relatedTripleInclusion_injective :
    Function.Injective (relatedTripleInclusion (R := R)) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p : RelatedSimilarities R => p.val.1) h)

open LinearAlgebraicGroups.Composition.Specification (zornNorm zornProduct)
open scoped Matrix

private def scaleZorn (a u v b : Rˣ) : Zorn R ≃ₗ[R] Zorn R :=
  ((Zorn.coordinates R).trans
    ((LinearEquiv.smulOfUnit a).prodCongr
      ((LinearEquiv.smulOfUnit u).prodCongr
        ((LinearEquiv.smulOfUnit v).prodCongr (LinearEquiv.smulOfUnit b))))).trans
    (Zorn.coordinates R).symm

private theorem scaleZorn_coordinates (a u v b : Rˣ) (x : Zorn R) :
    let X := Zorn.coordinates R x
    Zorn.coordinates R (scaleZorn a u v b x) =
      ((a : R) * X.1, (u : R) • X.2.1, (v : R) • X.2.2.1, (b : R) * X.2.2.2) := by
  simp only [scaleZorn, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.prodCongr_apply]
  rfl

private theorem scaleZorn_norm (a u v b m : Rˣ) (hab : a * b = m) (huv : u * v = m) (x : Zorn R) :
    norm R (scaleZorn a u v b x) = (m : R) * norm R x := by
  have hab' : (a : R) * (b : R) = (m : R) := congrArg Units.val hab
  have huv' : (u : R) * (v : R) = (m : R) := congrArg Units.val huv
  simp only [Composition.Zorn.norm_formula, scaleZorn_coordinates, zornNorm, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [show (a : R) * (Zorn.coordinates R x).1 * ((b : R) * (Zorn.coordinates R x).2.2.2) =
      ((a : R) * (b : R)) * ((Zorn.coordinates R x).1 * (Zorn.coordinates R x).2.2.2) by ac_rfl,
    hab', ← mul_assoc (↑v : R), mul_comm (↑v : R) (↑u : R), huv', mul_sub]

private def diagonalSimilarity (t : Rˣ) : Triple R :=
  ![scaleZorn t⁻¹ 1 1 t, scaleZorn t t 1 1, scaleZorn t 1 t 1]

private theorem conjugate_product_coordinates (x y : Zorn R) :
    let X := Zorn.coordinates R x
    let Y := Zorn.coordinates R y
    Zorn.coordinates R (conjugate (norm R) (x * y)) =
      (X.2.2.2 * Y.2.2.2 + X.2.2.1 ⬝ᵥ Y.2.1,
        -(X.1 • Y.2.1 + Y.2.2.2 • X.2.1 - X.2.2.1 ⨯₃ Y.2.2.1),
        -(Y.1 • X.2.2.1 + X.2.2.2 • Y.2.2.1 + X.2.1 ⨯₃ Y.2.1),
        X.1 * Y.1 + X.2.1 ⬝ᵥ Y.2.2.1) := by
  rw [← (Zorn.coordinates R).symm_apply_apply (x * y), Composition.Zorn.coordinates_mul]
  unfold zornProduct
  rw [Composition.Zorn.conjugate_formula, LinearEquiv.apply_symm_apply]

set_option linter.unusedSimpArgs false in
private theorem diagonalSimilarity_comp (t : Rˣ) (i : Fin 3) (x y : Zorn R) :
    diagonalSimilarity t i (conjugate (norm R) (x * y)) =
      (((![t⁻¹, 1, 1] : Fin 3 → Rˣ) i) : R) • conjugate (norm R)
        (diagonalSimilarity t (cyclicNext i) x * diagonalSimilarity t (cyclicPrev i) y) := by
  have hti : (t : R) * ((t⁻¹ : Rˣ) : R) = 1 := t.val_inv
  have hit : ((t⁻¹ : Rˣ) : R) * (t : R) = 1 := t.inv_val
  have cancel (a b : R) : (t : R) * a * (((t⁻¹ : Rˣ) : R) * b) = a * b := by
    calc
      _ = ((t : R) * ((t⁻¹ : Rˣ) : R)) * (a * b) := by ac_rfl
      _ = _ := by rw [hti, one_mul]
  have cancel' (a b : R) : ((t⁻¹ : Rˣ) : R) * a * ((t : R) * b) = a * b := by
    rw [mul_comm, cancel]
    ac_rfl
  have cancelRight (a : R) : a * ((t⁻¹ : Rˣ) : R) * (t : R) = a := by
    rw [mul_assoc, hit, mul_one]
  have cancelSquare (a : R) : (t : R) ^ 2 * a * ((t⁻¹ : Rˣ) : R) = (t : R) * a := by
    rw [pow_two]
    calc
      _ = ((t : R) * ((t⁻¹ : Rˣ) : R)) * ((t : R) * a) := by ac_rfl
      _ = _ := by rw [hti, one_mul]
  have cancelSquare' (a : R) : (t : R) ^ 2 * (a * ((t⁻¹ : Rˣ) : R)) = (t : R) * a := by
    rw [← mul_assoc, cancelSquare]
  have crossL (a : R) (v w : Fin 3 → R) : (a • v) ⨯₃ w = a • (v ⨯₃ w) := by
    rw [map_smul, LinearMap.smul_apply]
  have crossR (a : R) (v w : Fin 3 → R) : v ⨯₃ (a • w) = a • (v ⨯₃ w) := by
    rw [map_smul]
  have cases (j : Fin 3) : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have hnext₀ : cyclicNext 0 = 1 := rfl
  have hnext₁ : cyclicNext 1 = 2 := rfl
  have hnext₂ : cyclicNext 2 = 0 := rfl
  have hprev₀ : cyclicPrev 0 = 2 := rfl
  have hprev₁ : cyclicPrev 1 = 0 := rfl
  have hprev₂ : cyclicPrev 2 = 1 := rfl
  apply (Zorn.coordinates R).injective
  rcases cases i with rfl | rfl | rfl <;>
    simp only [diagonalSimilarity, hnext₀, hnext₁, hnext₂, hprev₀, hprev₁, hprev₂,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_smul,
      scaleZorn_coordinates, conjugate_product_coordinates, Prod.smul_mk, Prod.mk.injEq,
      smul_eq_mul, Units.val_one, one_mul, one_smul, smul_dotProduct, dotProduct_smul] <;>
    refine ⟨?_, funext fun j => ?_, funext fun j => ?_, ?_⟩ <;>
    (try simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, crossL, crossR]) <;>
    (try simp only [mul_add, mul_sub, mul_neg, mul_one, one_mul, cancel, cancel']) <;>
    (try simp only [mul_comm _ (↑t : R), ← mul_assoc (↑t⁻¹ : R) (↑t : R), hit, one_mul]) <;>
    first
    | ring1
    | ring_nf
      simp only [cancelRight, mul_assoc ((t : R) ^ 2), cancelSquare']
      try ring1

private theorem diagonalSimilarity_mem (t : Rˣ) :
    (diagonalSimilarity t, ![t⁻¹, 1, 1]) ∈ relatedSimilarities := by
  constructor
  · intro i x
    fin_cases i
    · change norm R (scaleZorn t⁻¹ 1 1 t x) = ((1 * 1)⁻¹ : Rˣ) * norm R x
      simp only [one_mul, inv_one]
      exact scaleZorn_norm t⁻¹ 1 1 t 1 (inv_mul_cancel t) (one_mul 1) x
    · change norm R (scaleZorn t t 1 1 x) = ((1 * t⁻¹)⁻¹ : Rˣ) * norm R x
      simp only [one_mul, inv_inv]
      exact scaleZorn_norm t t 1 1 t (mul_one t) (mul_one t) x
    · change norm R (scaleZorn t 1 t 1 x) = ((t⁻¹ * 1)⁻¹ : Rˣ) * norm R x
      simp only [mul_one, inv_inv]
      exact scaleZorn_norm t 1 t 1 t (mul_one t) (one_mul t) x
  · exact diagonalSimilarity_comp t

private def rotateSimilarities (offset : Fin 3) (p : RelatedSimilarities R) : RelatedSimilarities R :=
  ⟨(fun i => p.val.1 (i + offset), fun i => p.val.2 (i + offset)), by
    have hn (i : Fin 3) : cyclicNext (i + offset) = cyclicNext i + offset :=
      add_right_comm _ _ _
    have hp (i : Fin 3) : cyclicPrev (i + offset) = cyclicPrev i + offset :=
      add_right_comm _ _ _
    obtain ⟨hN, hP⟩ := p.property
    constructor
    · intro i x
      simpa only [quotientNormMultiplier, hn, hp] using hN (i + offset) x
    · intro i x y
      simpa only [hn, hp] using hP (i + offset) x y⟩

/-- Over each split test algebra, a unit in any chosen composition coordinate
has a related-similarity lift. The lift uses diagonal maps of the Zorn blocks. -/
theorem compositionQuotient_surjective : Function.Surjective (compositionQuotient (R := R)) := by
  intro q
  let lift (t : Rˣ) : RelatedSimilarities R := ⟨_, diagonalSimilarity_mem t⁻¹⟩
  let a := lift (q 0) * rotateSimilarities 2 (lift (q 1)) * rotateSimilarities 1 (lift (q 2))
  refine ⟨a, funext fun i => ?_⟩
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rw [map_mul, map_mul]
  rcases cases with rfl | rfl | rfl
  · change (q 0)⁻¹⁻¹ * 1 * 1 = q 0
    simp
  · change 1 * (q 1)⁻¹⁻¹ * 1 = q 1
    simp
  · change 1 * 1 * (q 2)⁻¹⁻¹ = q 2
    simp

/-- The parameter of the scalar block action in the composition quotient. -/
def scalarCompositionQuotient : (Fin 3 → Rˣ) →* (Fin 3 → Rˣ) where
  toFun t i := t i ^ 2 / ∏ j, t j
  map_one' := by ext; simp
  map_mul' x y := by
    funext i
    simp only [Pi.mul_apply, mul_pow, Finset.prod_mul_distrib, mul_div_mul_comm]

theorem scalarCompositionQuotient_apply (t : Fin 3 → Rˣ) (i : Fin 3) :
    scalarCompositionQuotient t i = t i / (t (cyclicNext i) * t (cyclicPrev i)) := by
  change t i ^ 2 / (∏ j, t j) = _
  rw [product_cyclic t i, pow_two, mul_div_mul_left_eq_div]

private theorem quotientNormMultiplier_scalar (t : Fin 3 → Rˣ) (i : Fin 3) :
    quotientNormMultiplier (scalarCompositionQuotient t) i = t i ^ 2 := by
  have hc : (∏ j, scalarCompositionQuotient t j) = (∏ j, t j)⁻¹ := by
    change (∏ j, t j ^ 2 / (∏ l, t l)) = _
    rw [Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_fin]
    rw [pow_succ _ 2]
    simpa only [mul_one, one_div] using
      mul_div_mul_left_eq_div 1 (∏ j, t j) ((∏ j, t j) ^ 2)
  have h (q : Fin 3 → Rˣ) : quotientNormMultiplier q i = q i / ∏ j, q j := by
    rw [product_cyclic q i, quotientNormMultiplier]
    simpa only [mul_one, one_div] using
      (mul_div_mul_left_eq_div 1 (q (cyclicNext i) * q (cyclicPrev i)) (q i)).symm
  rw [h, hc]
  change t i ^ 2 / (∏ j, t j) / (∏ j, t j)⁻¹ = _
  rw [div_inv_eq_mul, div_mul_cancel]

/-- In the composition coordinates the scalar block action is given by
`x ↦ x² / N(x)`. -/
def scalarSimilarity : (Fin 3 → Rˣ) →* RelatedSimilarities R where
  toFun t := ⟨(scalarTriple t, scalarCompositionQuotient t), by
    constructor
    · intro i x
      rw [quotientNormMultiplier_scalar, scalarTriple_apply, QuadraticMap.map_smul, smul_eq_mul,
        Units.val_pow_eq_pow_val, pow_two]
    · intro i x y
      change scalarTriple t i (conjugate (norm R) (x * y)) =
        (scalarCompositionQuotient t i : R) • conjugate (norm R)
          (scalarTriple t (cyclicNext i) x * scalarTriple t (cyclicPrev i) y)
      rw [scalarCompositionQuotient_apply]
      simp only [scalarTriple_apply, smul_mul_assoc, mul_smul_comm, map_smul, smul_smul,
        ← Units.val_mul]
      congr 2
      rw [mul_comm (t (cyclicPrev i)) (t (cyclicNext i)), div_mul_cancel]⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply LinearEquiv.ext
      intro x
      change scalarTriple 1 i x = x
      simp [scalarTriple_apply]
    · exact map_one scalarCompositionQuotient
  map_mul' t s := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply LinearEquiv.ext
      intro x
      change scalarTriple (t * s) i x = scalarTriple t i (scalarTriple s i x)
      simp only [Pi.mul_apply, scalarTriple_apply, smul_smul, Units.val_mul]
    · exact map_mul scalarCompositionQuotient t s

@[simp] theorem compositionQuotient_scalarSimilarity (t : Fin 3 → Rˣ) :
    compositionQuotient (scalarSimilarity t) = scalarCompositionQuotient t := rfl

theorem scalarSimilarity_injective : Function.Injective (scalarSimilarity (R := R)) := by
  intro a b h
  funext i
  apply Units.ext
  apply scalar_eq_of_smul_zorn_one (R := R)
  have he := congrArg (fun g : RelatedSimilarities R => g.val.1 i (1 : Zorn R)) h
  simpa only [scalarSimilarity, MonoidHom.coe_mk, OneHom.coe_mk, scalarTriple_apply] using he

theorem scalarSimilarity_central (t : Fin 3 → Rˣ) (p : RelatedSimilarities R) :
    Commute (scalarSimilarity t) p := by
  apply Subtype.ext
  refine Prod.ext (funext fun i => LinearEquiv.ext fun x => ?_) (mul_comm _ _)
  change scalarTriple t i (p.val.1 i x) = p.val.1 i (scalarTriple t i x)
  rw [scalarTriple_apply, scalarTriple_apply, map_smul]

end SimilarityGroup

section TwistingAlbertAlgebra

open AlgebraicGeometry CategoryTheory
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Descent (SemilinearAction)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (pointAction)
open TrialitarianAlbertDescentSpecification
open scoped CategoryTheory.MonObj

variable {k E K : Type u} [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]
  {J : AlbertModel k} (B : CubicStabilizer J E)

/-- The faithful linear action of the pointwise cubic stabilizer on the
scalar-extended Albert algebra. -/
noncomputable def cubicStabilizerAction (R : TestAlgebra k) :
    Points B.stabilizer.group.X R →* (R ⊗[k] J.V ≃ₗ[R] R ⊗[k] J.V) :=
  (J.action R).comp (((groupPointsFunctor k).map B.stabilizer.inclusion).app R).hom

theorem cubicStabilizerAction_faithful (R : TestAlgebra k) :
    Function.Injective (cubicStabilizerAction B R) := by
  intro g h he
  let : IsClosedImmersion B.stabilizer.inclusion.hom.hom.left :=
    B.stabilizer.isClosedImmersion
  let : Mono B.stabilizer.inclusion.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono B.stabilizer.inclusion.hom.hom).mp
  exact J.faithful R he

theorem cubicStabilizerAction_natural {R T : TestAlgebra k} (f : R ⟶ T)
    (g : Points B.stabilizer.group.X R) (x : R ⊗[k] J.V) :
    let m := TensorProduct.map f.hom.toLinearMap (LinearMap.id : J.V →ₗ[k] J.V)
    m (cubicStabilizerAction B R g x) = cubicStabilizerAction B T (mapPoints f g) (m x) := by
  change TensorProduct.map f.hom.toLinearMap LinearMap.id
      (J.action R (g ≫ B.stabilizer.inclusion.hom.hom) x) =
    J.action T (((testSpec k).map f.op ≫ g) ≫ B.stabilizer.inclusion.hom.hom)
      (TensorProduct.map f.hom.toLinearMap LinearMap.id x)
  rw [Category.assoc]
  exact J.natural f (g ≫ B.stabilizer.inclusion.hom.hom) x

theorem cubicStabilizerAction_spec (R : TestAlgebra k) (g : Points B.stabilizer.group.X R) :
    let s := cubicStabilizerAction B R g
    s (1 ⊗ₜ[k] J.law.unit) = 1 ⊗ₜ[k] J.law.unit ∧
    (∀ x y, s (J.law.op R x y) = J.law.op R (s x) (s y)) ∧
    ∀ x, s (B.diagonal.baseChange R x) = B.diagonal.baseChange R x := by
  let p := g ≫ B.stabilizer.inclusion.hom.hom
  have hp : J.action R p ∈ Set.range (J.action R) := ⟨p, rfl⟩
  rw [J.image R] at hp
  exact ⟨hp.1, hp.2, (B.fixesExactly R p).mpr ⟨g, rfl⟩⟩

private noncomputable abbrev coefficientAction : SemilinearAction k K (K ⊗[k] J.V) :=
  SemilinearAction.scalarExtension J.V

private theorem pointAction_intertwines (g : Gal(K/k))
    (p : Points B.stabilizer.group.X (CommAlgCat.of k K)) (x : K ⊗[k] J.V) :
    coefficientAction.act g (cubicStabilizerAction B (CommAlgCat.of k K) p x) =
      cubicStabilizerAction B (CommAlgCat.of k K) (pointAction k K B.stabilizer.group.X g p)
        (coefficientAction.act g x) :=
  cubicStabilizerAction_natural B (CommAlgCat.ofHom g.toAlgHom) p x

/-- Twisting the scalar action by a stabilizer cocycle gives a semilinear
Galois action on the Albert vector space. -/
noncomputable def twistedAlbertAction
    (a : Gal(K/k) → Points B.stabilizer.group.X (CommAlgCat.of k K))
    (ha : ∀ g h, a (g * h) = a g * pointAction k K B.stabilizer.group.X g (a h)) :
    SemilinearAction k K (K ⊗[k] J.V) where
  act g := (coefficientAction.act g).trans ((cubicStabilizerAction B _ (a g)).toAddEquiv)
  one_act x := by
    have ha₁ : a 1 = 1 := by
      have h := ha 1 1
      simp only [mul_one, map_one, MulAut.one_apply] at h
      apply mul_left_cancel (a := a 1)
      simpa only [mul_one] using h.symm
    change cubicStabilizerAction B _ (a 1) (coefficientAction.act 1 x) = x
    rw [coefficientAction.one_act, ha₁, map_one]
    rfl
  mul_act g h x := by
    change cubicStabilizerAction B _ (a (g * h)) (coefficientAction.act (g * h) x) =
      cubicStabilizerAction B _ (a g) (coefficientAction.act g
        (cubicStabilizerAction B _ (a h) (coefficientAction.act h x)))
    rw [ha, map_mul, coefficientAction.mul_act, LinearEquiv.mul_apply, pointAction_intertwines]
  map_smul g r x := by
    change cubicStabilizerAction B _ (a g) (coefficientAction.act g (r • x)) =
      g r • cubicStabilizerAction B _ (a g) (coefficientAction.act g x)
    rw [coefficientAction.map_smul, map_smul]

variable (a : Gal(K/k) → Points B.stabilizer.group.X (CommAlgCat.of k K))
  (ha : ∀ g h, a (g * h) = a g * pointAction k K B.stabilizer.group.X g (a h))

theorem twistedAlbertAction_unit (g : Gal(K/k)) :
    (twistedAlbertAction B a ha).act g (1 ⊗ₜ[k] J.law.unit) = 1 ⊗ₜ[k] J.law.unit := by
  change cubicStabilizerAction B _ (a g) (g 1 ⊗ₜ[k] J.law.unit) = _
  rw [map_one]
  exact (cubicStabilizerAction_spec B _ (a g)).1

theorem twistedAlbertAction_operator (g : Gal(K/k)) (x y : K ⊗[k] J.V) :
    (twistedAlbertAction B a ha).act g (J.law.op K x y) =
      J.law.op K ((twistedAlbertAction B a ha).act g x) ((twistedAlbertAction B a ha).act g y) := by
  have h := J.law.natural g.toAlgHom x y
  change coefficientAction.act g (J.law.op K x y) =
    J.law.op K (coefficientAction.act g x) (coefficientAction.act g y) at h
  change cubicStabilizerAction B _ (a g) (coefficientAction.act g (J.law.op K x y)) =
    J.law.op K _ _
  rw [h]
  exact (cubicStabilizerAction_spec B _ (a g)).2.1 _ _

theorem twistedAlbertAction_diagonal (g : Gal(K/k)) (x : E) :
    (twistedAlbertAction B a ha).act g (1 ⊗ₜ[k] B.diagonal x) = 1 ⊗ₜ[k] B.diagonal x := by
  change cubicStabilizerAction B _ (a g) (g 1 ⊗ₜ[k] B.diagonal x) = _
  rw [map_one]
  exact (cubicStabilizerAction_spec B _ (a g)).2.2 (1 ⊗ₜ[k] x)

variable [FiniteDimensional k K] [IsGalois k K]

private noncomputable def twistComparison (R : Type u) [CommRing R] [Algebra k R] [Algebra K R]
    [IsScalarTower k K R] : R ⊗[k] (twistedAlbertAction B a ha).fixed ≃ₗ[R] R ⊗[k] J.V :=
  let ρ := twistedAlbertAction B a ha
  ((TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R ρ.fixed).symm.trans
    (ρ.descentEquiv.baseChange K R _ _)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R J.V)

private theorem twistComparison_tmul (R : Type u) [CommRing R] [Algebra k R] [Algebra K R]
    [IsScalarTower k K R] (r : R) (x : (twistedAlbertAction B a ha).fixed) :
    twistComparison B a ha R (r ⊗ₜ[k] x) = r •
      TensorProduct.map (IsScalarTower.toAlgHom k K R).toLinearMap LinearMap.id x.val := by
  simp only [twistComparison, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  change TensorProduct.AlgebraTensorModule.cancelBaseChange k K R R J.V
    (r ⊗ₜ[K] (twistedAlbertAction B a ha).descentEquiv (1 ⊗ₜ[k] x)) = _
  rw [SemilinearAction.descentEquiv_tmul, one_smul]
  induction x.val using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, TensorProduct.map_tmul,
      LinearMap.id_apply, TensorProduct.smul_tmul', Algebra.smul_def]
    change (algebraMap K R b * r) ⊗ₜ[k] v = (r * algebraMap K R b) ⊗ₜ[k] v
    rw [mul_comm]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy, smul_add]

open LinearAlgebraicGroups.Albert.TrialitySpecification (Model modelOp)
open LinearAlgebraicGroups.Albert.CubicSpecification (cubicUnit)

set_option maxHeartbeats 1100000 in
/-- The finite Galois twist of an Albert law by a cocycle in the pointwise
stabilizer has the same marked cubic field. The comparisons of the descended
law and cubic embedding hold on every test algebra over the splitting layer. -/
theorem exists_twistedAlbertLaw
    {S : Type u} [Field S] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    (numbering : (E →ₐ[k] S) ≃ Fin 3) (hs : IsDiagonalOver J B numbering) :
    let ρ := twistedAlbertAction B a ha
    ∃ (J' : ParaQuadratic k ρ.fixed) (d : E →ₗ[k] ρ.fixed),
      IsAlbert J' ∧ Function.Injective d ∧ d 1 = J'.unit ∧
      (∀ x y, d (x ^ 2 * y) = J'.groundOp (d x) (d y)) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R],
        let t := twistComparison B a ha R
        t (1 ⊗ₜ[k] J'.unit) = 1 ⊗ₜ[k] J.law.unit ∧
        (∀ x y, t (J'.op R x y) = J.law.op R (t x) (t y)) ∧
        ∀ x : E, t (1 ⊗ₜ[k] d x) = 1 ⊗ₜ[k] B.diagonal x := by
  obtain ⟨s, hsu, hsop, _⟩ := hs
  let ρ := twistedAlbertAction B a ha
  let e : ρ.fixed := ⟨1 ⊗ₜ[k] J.law.unit, twistedAlbertAction_unit B a ha⟩
  let : Module.Finite k J.V := (freudenthal_finite_projective J.law J.albert.1).1
  obtain ⟨J', hu, hop, hcomp⟩ := exists_fixedQuadraticLaw ρ (J.law.op K) e
    (J.law.op_unit K) (twistedAlbertAction_operator B a ha)
  let d : E →ₗ[k] ρ.fixed := ((TensorProduct.mk k K J.V 1).comp B.diagonal).codRestrict _
    (fun x => fun σ => twistedAlbertAction_diagonal B a ha σ x)
  have compare (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R] :
      let t := twistComparison B a ha R
      t (1 ⊗ₜ[k] J'.unit) = 1 ⊗ₜ[k] J.law.unit ∧
      (∀ x y, t (J'.op R x y) = J.law.op R (t x) (t y)) ∧
      ∀ x : E, t (1 ⊗ₜ[k] d x) = 1 ⊗ₜ[k] B.diagonal x := by
    constructor
    · rw [twistComparison_tmul, one_smul, hu]
      change ((algebraMap K R) 1) ⊗ₜ[k] J.law.unit = _
      rw [map_one]
    constructor
    · apply hcomp
      intro x y
      change twistComparison B a ha R (1 ⊗ₜ[k] J'.groundOp x y) =
        J.law.op R (twistComparison B a ha R (1 ⊗ₜ[k] x))
          (twistComparison B a ha R (1 ⊗ₜ[k] y))
      rw [twistComparison_tmul, twistComparison_tmul, twistComparison_tmul]
      simp only [one_smul, hop]
      exact J.law.natural (IsScalarTower.toAlgHom k K R) x.val y.val
    · intro x
      rw [twistComparison_tmul, one_smul]
      change ((algebraMap K R) 1) ⊗ₜ[k] B.diagonal x = _
      rw [map_one]
  refine ⟨J', d, ?_, ?_, ?_, ?_, @compare⟩
  · apply (albert_iff_split_octonion_after_cover J').mpr
    refine ⟨S, inferInstance, inferInstance, inferInstance,
      (twistComparison B a ha S).trans s, ?_, ?_⟩
    · simp only [LinearEquiv.trans_apply, (compare S).1, hsu]
    · intro x y
      rw [LinearEquiv.trans_apply, (compare S).2.1]
      exact hsop _ _
  · intro x y hxy
    apply B.injective
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := k) (B := K) J.V
    exact congrArg Subtype.val hxy
  · apply Subtype.ext
    rw [hu]
    exact congrArg (fun x : J.V => (1 : K) ⊗ₜ[k] x) B.unit
  · intro x y
    apply Subtype.ext
    rw [hop]
    change (1 : K) ⊗ₜ[k] B.diagonal (x ^ 2 * y) =
      J.law.op K ((1 : K) ⊗ₜ[k] B.diagonal x) ((1 : K) ⊗ₜ[k] B.diagonal y)
    have h := B.respectsOperator (CommAlgCat.of k K) (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)
    simpa only [Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_pow,
      one_mul, LinearMap.baseChange_tmul] using h

end TwistingAlbertAlgebra

section StabilizerComparison

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Albert.SplitSpecification
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence (relativePoints innerAut restrictIso)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open OctonionEquivariantAutomorphisms (affineTest extendComparison)
open LinearAlgebraicGroups.Composition.PeirceSpecification (tensorMap)
open private extendEquiv extend_tmul extend_natural tensorMap_comp exists_relativeIso
  relativeHom_ext restrictIso_affine_apply from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms


variable {k E K : Type u} [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]
  {J J' : AlbertModel k} (B : CubicStabilizer J E) (B' : CubicStabilizer J' E)

theorem cubicStabilizerAction_image (R : TestAlgebra k) :
    Set.range (cubicStabilizerAction B R) =
      {g | g (1 ⊗ₜ[k] J.law.unit) = 1 ⊗ₜ[k] J.law.unit ∧
        (∀ x y, g (J.law.op R x y) = J.law.op R (g x) (g y)) ∧
        ∀ x, g (B.diagonal.baseChange R x) = B.diagonal.baseChange R x} := by
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    exact cubicStabilizerAction_spec B R a
  · intro h
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp (J.image R) g).mpr ⟨h.1, h.2.1⟩
    obtain ⟨q, hq⟩ := (B.fixesExactly R a).mp (ha ▸ h.2.2)
    exact ⟨q, by
      change J.action R (q ≫ B.stabilizer.inclusion.hom.hom) = g
      rw [hq, ha]⟩

set_option backward.isDefEq.respectTransparency false in
/-- A marked isomorphism of Albert laws induces a comparison of their
pointwise stabilizers over the same coefficient algebra. -/
theorem cubicStabilizerPointEquiv (R : TestAlgebra k) (t : R ⊗[k] J'.V ≃ₗ[R] R ⊗[k] J.V)
    (hu : t (1 ⊗ₜ[k] J'.law.unit) = 1 ⊗ₜ[k] J.law.unit)
    (ho : ∀ x y, t (J'.law.op R x y) = J.law.op R (t x) (t y))
    (hd : ∀ x, t (B'.diagonal.baseChange R x) = B.diagonal.baseChange R x) :
    ∃ φ : Points B.stabilizer.group.X R ≃* Points B'.stabilizer.group.X R,
      ∀ a x, t (cubicStabilizerAction B' R (φ a) x) = cubicStabilizerAction B R a (t x) := by
  classical
  let a := cubicStabilizerAction B R
  let a' := cubicStabilizerAction B' R
  let conj : (R ⊗[k] J.V ≃ₗ[R] R ⊗[k] J.V) →*
      (R ⊗[k] J'.V ≃ₗ[R] R ⊗[k] J'.V) :=
    { toFun := fun g => t.trans (g.trans t.symm)
      map_one' := LinearEquiv.ext fun x => t.symm_apply_apply x
      map_mul' := fun g h => LinearEquiv.ext fun x => by
        change t.symm (g (h (t x))) = t.symm (g (t (t.symm (h (t x)))))
        rw [LinearEquiv.apply_symm_apply] }
  have conj_apply (g : R ⊗[k] J.V ≃ₗ[R] R ⊗[k] J.V) (x : R ⊗[k] J'.V) :
      t (conj g x) = g (t x) := t.apply_symm_apply _
  have hconj (g : Points B.stabilizer.group.X R) : conj (a g) ∈ Set.range a' := by
    change _ ∈ Set.range (cubicStabilizerAction B' R)
    rw [cubicStabilizerAction_image]
    have h := cubicStabilizerAction_spec B R g
    refine ⟨t.injective ?_, fun x y => t.injective ?_, fun x => t.injective ?_⟩
    · rw [conj_apply, hu, h.1]
    · rw [conj_apply, ho, h.2.1, ho, conj_apply, conj_apply]
    · rw [conj_apply, hd, h.2.2]
  choose f hf using hconj
  let p : Points B.stabilizer.group.X R →* Points B'.stabilizer.group.X R :=
    { toFun := f
      map_one' := cubicStabilizerAction_faithful B' R (by
        change a' (f 1) = a' 1
        rw [hf, map_one, map_one, map_one])
      map_mul' := fun g h => cubicStabilizerAction_faithful B' R (by
        change a' (f (g * h)) = a' (f g * f h)
        rw [hf, map_mul a, map_mul conj, map_mul a', hf, hf]) }
  have hp (g : Points B.stabilizer.group.X R) (x : R ⊗[k] J'.V) :
      t (a' (p g) x) = a g (t x) := by
    change t (a' (f g) x) = _
    rw [hf, conj_apply]
  refine ⟨MulEquiv.ofBijective p ⟨?_, ?_⟩, hp⟩
  · intro g h hh
    apply cubicStabilizerAction_faithful B R
    apply LinearEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := t.surjective y
    change a g (t x) = a h (t x)
    rw [← hp, ← hp, hh]
  · intro q
    let s := t.symm.trans ((a' q).trans t)
    have hs (x : R ⊗[k] J'.V) : s (t x) = t (a' q x) := by
      change t (a' q (t.symm (t x))) = _
      rw [t.symm_apply_apply]
    have h : s ∈ Set.range a := by
      change _ ∈ Set.range (cubicStabilizerAction B R)
      rw [cubicStabilizerAction_image]
      have hq := cubicStabilizerAction_spec B' R q
      refine ⟨?_, ?_, fun x => ?_⟩
      · rw [← hu, hs, hq.1]
      · intro x y
        obtain ⟨x, rfl⟩ := t.surjective x
        obtain ⟨y, rfl⟩ := t.surjective y
        rw [← ho, hs, hq.2.1, ho, hs, hs]
      · rw [← hd, hs, hq.2.2]
    obtain ⟨g, hg⟩ := h
    refine ⟨g, cubicStabilizerAction_faithful B' R ?_⟩
    apply LinearEquiv.ext
    intro x
    apply t.injective
    change t (a' (p g) x) = t (a' q x)
    rw [hp, hg, hs]

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by an isomorphism of the marked Albert laws gives a relative
isomorphism, with inner displacement read from its coefficient action. -/
theorem cubicStabilizerRelativeIso (c : Gal(K/k) → Points B.stabilizer.group.X (CommAlgCat.of k K))
    (C : K ⊗[k] J'.V ≃ₗ[K] K ⊗[k] J.V)
    (hIso : ∀ (R : TestAlgebra k) (f : CommAlgCat.of k K ⟶ R),
      let t := extendEquiv f C
      t (1 ⊗ₜ[k] J'.law.unit) = 1 ⊗ₜ[k] J.law.unit ∧
      (∀ x y, t (J'.law.op R x y) = J.law.op R (t x) (t y)) ∧
      (∀ x, t (B'.diagonal.baseChange R x) = B.diagonal.baseChange R x))
    (hc : ∀ σ (w : J'.V),
      cubicStabilizerAction B (CommAlgCat.of k K) (c σ)
        (tensorMap σ.toAlgHom (C (1 ⊗ₜ[k] w))) = C (1 ⊗ₜ[k] w)) :
    ∃ j : relativePoints B.stabilizer.group (fieldTest k K) ≅
        relativePoints B'.stabilizer.group (fieldTest k K),
      ∀ σ, transportedAut k K j σ = innerAut (c σ) := by
  classical
  have aff (A : AlbertModel k) (D : CubicStabilizer A E) : IsAffine D.stabilizer.group.X.left := by
    let : IsClosedImmersion D.stabilizer.inclusion.hom.hom.left := D.stabilizer.isClosedImmersion
    let : IsAffine A.automorphisms.val.X.left := A.automorphisms.property.1
    exact isAffine_of_isAffineHom D.stabilizer.inclusion.hom.hom.left
  have nat {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (b : R ⟶ T) (x : R ⊗[k] J'.V) :
      extendEquiv (f ≫ b) C (tensorMap b.hom x) = tensorMap b.hom (extendEquiv f C x) :=
    extend_natural f b C.toLinearMap x
  have exist := fun (R : TestAlgebra k) (f : CommAlgCat.of k K ⟶ R) =>
    cubicStabilizerPointEquiv B B' R (extendEquiv f C) (hIso R f).1 (hIso R f).2.1 (hIso R f).2.2
  choose φ hφ using exist
  have hNat {R T : TestAlgebra k} (f : CommAlgCat.of k K ⟶ R) (b : R ⟶ T)
      (g : Points B.stabilizer.group.X R) :
      φ T (f ≫ b) (mapPoints b g) = mapPoints b (φ R f g) := by
    apply cubicStabilizerAction_faithful B' T
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    apply (extendEquiv (f ≫ b) C).injective
    change extendEquiv (f ≫ b) C (cubicStabilizerAction B' T (φ T (f ≫ b) (mapPoints b g)) (r ⊗ₜ[k] w)) =
      extendEquiv (f ≫ b) C (cubicStabilizerAction B' T (mapPoints b (φ R f g)) (r ⊗ₜ[k] w))
    rw [hφ]
    have h (x : R ⊗[k] J'.V) :
        extendEquiv (f ≫ b) C (cubicStabilizerAction B' T (mapPoints b (φ R f g)) (tensorMap b.hom x)) =
        cubicStabilizerAction B T (mapPoints b g) (extendEquiv (f ≫ b) C (tensorMap b.hom x)) := by
      have h₁ : tensorMap b.hom (cubicStabilizerAction B' R (φ R f g) x) =
          cubicStabilizerAction B' T (mapPoints b (φ R f g)) (tensorMap b.hom x) :=
        cubicStabilizerAction_natural B' b (φ R f g) x
      have h₂ : tensorMap b.hom (cubicStabilizerAction B R g (extendEquiv f C x)) =
          cubicStabilizerAction B T (mapPoints b g) (tensorMap b.hom (extendEquiv f C x)) :=
        cubicStabilizerAction_natural B b g (extendEquiv f C x)
      rw [← h₁, nat, hφ, h₂, nat]
    have h₁ := h ((1 : R) ⊗ₜ[k] w)
    rw [LinearAlgebraicGroups.Composition.Peirce.tensorMap_tmul, map_one] at h₁
    have hr : (r ⊗ₜ[k] w : T ⊗[k] J'.V) = r • ((1 : T) ⊗ₜ[k] w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]
    rw [hr, map_smul, map_smul, map_smul, map_smul, h₁]
  obtain ⟨j, hj⟩ := exists_relativeIso (aff J B) (aff J' B') φ hNat
  refine ⟨j, fun σ => ?_⟩
  have hjσ : restrictIso (fieldMap k K σ) j = (innerAut (c σ)).asIso ≪≫ j := by
    apply Iso.ext
    apply relativeHom_ext (aff J B)
    intro R f g
    rw [restrictIso_affine_apply]
    let s := CommAlgCat.ofHom σ.toAlgHom
    let a := mapPoints f (c σ)
    change (j.hom.app (op (affineTest (s ≫ f)))).hom g =
      (j.hom.app (op (affineTest f))).hom (a * g * a⁻¹)
    rw [hj, hj]
    have hCoe (x : R ⊗[k] J'.V) :
        cubicStabilizerAction B R a (extendEquiv (s ≫ f) C x) = extendEquiv f C x := by
      induction x using TensorProduct.inductionOn with
      | tmul r w =>
        change cubicStabilizerAction B R a (extendComparison (s ≫ f) C.toLinearMap (r ⊗ₜ[k] w)) =
          extendComparison f C.toLinearMap (r ⊗ₜ[k] w)
        rw [extend_tmul, extend_tmul, map_smul, tensorMap_comp]
        have h := congrArg (tensorMap f.hom) (hc σ w)
        have hn : tensorMap f.hom (cubicStabilizerAction B (CommAlgCat.of k K) (c σ)
            (tensorMap σ.toAlgHom (C (1 ⊗ₜ[k] w)))) =
            cubicStabilizerAction B R a (tensorMap f.hom (tensorMap σ.toAlgHom (C (1 ⊗ₜ[k] w)))) :=
          cubicStabilizerAction_natural B f (c σ) _
        exact congrArg (r • ·) (hn.symm.trans h)
      | add x y hx hy => simp only [map_add, hx, hy]
    apply cubicStabilizerAction_faithful B' R
    apply LinearEquiv.ext
    intro x
    apply (extendEquiv f C).injective
    rw [← hCoe (cubicStabilizerAction B' R (φ R (s ≫ f) g) x), hφ, hφ, map_mul, map_mul, map_inv]
    change cubicStabilizerAction B R a (cubicStabilizerAction B R g (extendEquiv (s ≫ f) C x)) =
      cubicStabilizerAction B R a (cubicStabilizerAction B R g
        ((cubicStabilizerAction B R a).symm (extendEquiv f C x)))
    rw [← hCoe x, LinearEquiv.symm_apply_apply]
  apply Aut.ext
  change restrictIso (fieldMap k K σ) j ≪≫ j.symm = (innerAut (c σ)).asIso
  rw [hjσ, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

end StabilizerComparison


section TwistRealization

set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Albert.SplitSpecification
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence (relativePoints innerAut restrictIso restrictAut)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open OctonionEquivariantAutomorphisms (extendComparison)
open LinearAlgebraicGroups.Composition.PeirceSpecification (tensorMap)
open LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle IsCocycle pointMap pointAction restriction levelAction quotientAction_apply
    finitePointsIdentification finiteLevel)
open private extendEquiv extend_tmul from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
open private restrict_innerAut from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
  [IsSepClosure k S] [Module.Finite k E]

private theorem restrictIso_comp {G H : GroupScheme k} {U V W : SchemeOver k}
    (a : U ⟶ V) (b : V ⟶ W) (j : relativePoints G W ≅ relativePoints H W) :
    restrictIso a (restrictIso b j) = restrictIso (a ≫ b) j := by
  apply Iso.ext
  apply NatTrans.ext
  funext T
  change j.hom.app (op (Over.mk ((T.unop.hom ≫ a) ≫ b))) =
    j.hom.app (op (Over.mk (T.unop.hom ≫ (a ≫ b))))
  rw [Category.assoc]

set_option maxHeartbeats 850000 in
omit [IsSepClosure k S] in
private theorem restrict_transport {M H : GroupScheme k} (K : FiniteGaloisIntermediateField k S)
    (p : fieldTest k S ⟶ fieldTest k K)
    (j : relativePoints M (fieldTest k K) ≅ relativePoints H (fieldTest k K))
    (a : Gal(K/k) → (fieldTest k K ⟶ M.X))
    (ha : ∀ σ, transportedAut k K j σ = innerAut (a σ))
    (hSquare : ∀ σ, fieldMap k S σ ≫ p = p ≫ fieldMap k K (restriction K σ)) (σ : Gal(S/k)) :
    transportedAut k S (restrictIso p j) σ = innerAut (p ≫ a (restriction K σ)) := by
  have he : restrictIso (fieldMap k S σ) (restrictIso p j) =
      restrictIso p (restrictIso (fieldMap k K (restriction K σ)) j) := by
    rw [restrictIso_comp, restrictIso_comp, hSquare]
  rw [transportedAut, he]
  have h := congrArg (restrictAut p) (ha (restriction K σ))
  rw [restrict_innerAut] at h
  exact h

set_option maxHeartbeats 800000 in
private theorem iso_of_equalTransport {M G G' : AffineAlgebraicGroup k}
    (i : relativePoints M.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (j : relativePoints M.val (fieldTest k S) ≅ relativePoints G'.val (fieldTest k S))
    (h : ∀ σ, transportedAut k S i σ = transportedAut k S j σ) :
    Nonempty (G.val ≅ G'.val) := by
  obtain ⟨c⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification (S := S) M
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
    (S := S) M.val G.val
  obtain ⟨e', he'⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
    (S := S) M.val G'.val
  let g : LinearAlgebraicGroups.Descent.Forms.SchemeModels S M := ⟨G, ⟨e.symm i⟩⟩
  let g' : LinearAlgebraicGroups.Descent.Forms.SchemeModels S M := ⟨G', ⟨e'.symm j⟩⟩
  obtain ⟨a, ha, hca⟩ := c.computes g i
  obtain ⟨b, hb, hcb⟩ := c.computes g' j
  have hab : a = b := Subtype.ext (funext fun σ => (ha σ).trans ((h σ).trans (hb σ).symm))
  exact Quotient.exact (c.equiv.injective (hca.trans (hab ▸ hcb.symm)))

private def stabilizerAffineModel {J : AlbertModel k} (B : CubicStabilizer J E) :
    AffineAlgebraicGroup k := by
  haveI : IsClosedImmersion B.stabilizer.inclusion.hom.hom.left := B.stabilizer.isClosedImmersion
  haveI : IsAffine J.automorphisms.val.X.left := J.automorphisms.property.1
  haveI : LocallyOfFiniteType J.automorphisms.val.X.hom := J.automorphisms.property.2.1
  haveI : QuasiCompact J.automorphisms.val.X.hom := J.automorphisms.property.2.2
  have h := Over.w B.stabilizer.inclusion.hom.hom
  exact ⟨B.stabilizer.group, isAffine_of_isAffineHom B.stabilizer.inclusion.hom.hom.left,
    h ▸ inferInstance, h ▸ inferInstance⟩

set_option maxHeartbeats 1900000 in
set_option backward.isDefEq.respectTransparency false in
/-- An inner lift in the reference stabilizer gives a marked Albert algebra
whose pointwise cubic stabilizer is the specified group scheme. -/
theorem exists_albertOfInnerLift {J : AlbertModel k} (B : CubicStabilizer J E)
    (numbering : (E →ₐ[k] S) ≃ Fin 3) (hDiag : IsDiagonalOver J B numbering)
    (G : AffineAlgebraicGroup k) (hLift : HasInnerLift B.stabilizer.group G.val S) :
    ∃ (J' : AlbertModel k) (B' : CubicStabilizer J' E),
      Nonempty (G.val ≅ B'.stabilizer.group) ∧ IsDiagonalOver J' B' numbering := by
  letI : TopologicalSpace (Gal(S/k)) := krullTopology k S
  letI : TopologicalSpace (Points B.stabilizer.group.X (CommAlgCat.of k S)) := ⊥
  letI : DiscreteTopology (Points B.stabilizer.group.X (CommAlgCat.of k S)) := ⟨rfl⟩
  obtain ⟨a, i, ha, hi⟩ := hLift
  let ac : Cocycle (pointAction k S B.stabilizer.group.X) := ⟨a, ha⟩
  obtain ⟨K, c, _, hc⟩ := finiteLevel (⊥ : FiniteGaloisIntermediateField k S) ac
  obtain ⟨φ, hφ, hequiv⟩ := finitePointsIdentification (H := B.stabilizer.group.X) K
  let b (δ : Gal(K/k)) := φ.symm (c δ)
  have hb (σ τ : Gal(K/k)) :
      b (σ * τ) = b σ * pointAction k K B.stabilizer.group.X σ (b τ) := by
    apply φ.injective
    change φ (φ.symm (c (σ * τ))) = _
    rw [φ.apply_symm_apply, map_mul, hequiv, show φ (b σ) = c σ from φ.apply_symm_apply _,
      show φ (b τ) = c τ from φ.apply_symm_apply _]
    exact c.property.2 σ τ
  let fS := CommAlgCat.ofHom K.toIntermediateField.val
  have hcoeff (σ : Gal(S/k)) : mapPoints fS (b (restriction K σ)) = a σ := by
    change pointMap k K B.stabilizer.group.X K.toIntermediateField.val (b (restriction K σ)) = _
    rw [← hφ, show φ (b (restriction K σ)) = c (restriction K σ) from φ.apply_symm_apply _]
    exact hc σ
  let ρ := twistedAlbertAction B b hb
  obtain ⟨J₁, d, hJ₁, hd, hUnit, hOp, hCompare⟩ := exists_twistedAlbertLaw B b hb numbering hDiag
  obtain ⟨J', B', e, he, hE⟩ := exists_albertModel_withCubicStabilizer J₁ hJ₁ d hd hUnit hOp
  let tK := twistComparison B b hb K
  let t (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R] :=
    (e.baseChange k R ρ.fixed J'.V).symm.trans (twistComparison B b hb R)
  have htK (w : ρ.fixed) : tK ((1 : K) ⊗ₜ[k] w) = w.val := by
    change twistComparison B b hb K (1 ⊗ₜ[k] w) = _
    rw [twistComparison_tmul, one_smul]
    change TensorProduct.map (LinearMap.id : K →ₗ[k] K) LinearMap.id w.val = _
    rw [TensorProduct.map_id]
    rfl
  have ht (R : TestAlgebra k) (f : CommAlgCat.of k K ⟶ R) :
      letI : Algebra K R := f.hom.toRingHom.toAlgebra
      letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
      extendEquiv f (t K) = t R := by
    letI : Algebra K R := f.hom.toRingHom.toAlgebra
    letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    change extendComparison f (t K).toLinearMap (r ⊗ₜ[k] w) =
      twistComparison B b hb R (r ⊗ₜ[k] e.symm w)
    rw [extend_tmul]
    change r • tensorMap f.hom (tK (1 ⊗ₜ[k] e.symm w)) = _
    rw [htK, twistComparison_tmul]
    rfl
  have preserves (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R] :
      t R (1 ⊗ₜ[k] J'.law.unit) = 1 ⊗ₜ[k] J.law.unit ∧
      (∀ x y, t R (J'.law.op R x y) = J.law.op R (t R x) (t R y)) ∧
      (∀ x, t R (B'.diagonal.baseChange R x) = B.diagonal.baseChange R x) := by
    let er := e.baseChange k R ρ.fixed J'.V
    have et (x : R ⊗[k] ρ.fixed) : t R (er x) = twistComparison B b hb R x := by
      change twistComparison B b hb R (er.symm (er x)) = _
      rw [er.symm_apply_apply]
    have sUnit : er (1 ⊗ₜ[k] J₁.unit) = 1 ⊗ₜ[k] J'.law.unit := by
      change 1 ⊗ₜ[k] e J₁.unit = _
      rw [he.1]
    refine ⟨?_, ?_, ?_⟩
    · rw [← sUnit, et]
      exact (hCompare R).1
    · intro x y
      obtain ⟨x, rfl⟩ := er.surjective x
      obtain ⟨y, rfl⟩ := er.surjective y
      have hop : er (J₁.op R x y) = J'.law.op R (er x) (er y) := he.2 R x y
      rw [← hop, et, et, et]
      exact (hCompare R).2.1 x y
    · have gen (x : E) : t R (1 ⊗ₜ[k] B'.diagonal x) = 1 ⊗ₜ[k] B.diagonal x := by
        have h : er (1 ⊗ₜ[k] d x) = 1 ⊗ₜ[k] B'.diagonal x := by
          change 1 ⊗ₜ[k] e (d x) = _
          rw [hE x]
        rw [← h, et]
        exact (hCompare R).2.2 x
      have h : (t R).toLinearMap.comp (B'.diagonal.baseChange R) = B.diagonal.baseChange R := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro r x
        change t R (B'.diagonal.baseChange R (r ⊗ₜ[k] x)) = B.diagonal.baseChange R (r ⊗ₜ[k] x)
        simp only [LinearMap.baseChange_tmul]
        rw [show ∀ z : J'.V, r ⊗ₜ[k] z = r • ((1 : R) ⊗ₜ[k] z) by
              intro z; rw [smul_tmul', smul_eq_mul, mul_one],
          show ∀ z : J.V, r ⊗ₜ[k] z = r • ((1 : R) ⊗ₜ[k] z) by
              intro z; rw [smul_tmul', smul_eq_mul, mul_one], map_smul, gen]
      exact LinearMap.congr_fun h
  obtain ⟨j, hj⟩ := cubicStabilizerRelativeIso B B' b (t K) (fun R f => by
    letI : Algebra K R := f.hom.toRingHom.toAlgebra
    letI : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
    rw [ht R f]
    exact preserves R) (fun σ w => by
      have he : t K (1 ⊗ₜ[k] w) = (e.symm w).val := htK _
      rw [he]
      exact (e.symm w).property σ)
  let p : fieldTest k S ⟶ fieldTest k K := (testSpec k).map fS.op
  have hSquare (σ : Gal(S/k)) : fieldMap k S σ ≫ p = p ≫ fieldMap k K (restriction K σ) := by
    change (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫ (testSpec k).map fS.op =
      (testSpec k).map fS.op ≫ (testSpec k).map (CommAlgCat.ofHom (restriction K σ).toAlgHom).op
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    ext z
    exact (AlgEquiv.restrictNormal_commutes σ K z).symm
  have hJ' (σ : Gal(S/k)) :
      transportedAut k S i σ = transportedAut k S (restrictIso p j) σ := by
    rw [hi σ, restrict_transport K p j b hj hSquare]
    exact congrArg innerAut (hcoeff σ).symm
  refine ⟨J', B', iso_of_equalTransport (M := stabilizerAffineModel B)
    (G' := stabilizerAffineModel B') i (restrictIso p j) hJ', ?_⟩
  obtain ⟨s, hu, ho, hdiag⟩ := hDiag
  refine ⟨(t S).trans s, ?_, ?_, ?_⟩
  · exact (congrArg s (preserves S).1).trans hu
  · intro x y
    change s (t S (J'.law.op S x y)) = _
    rw [(preserves S).2.1]
    exact ho _ _
  · intro x
    have h := (preserves S).2.2 (1 ⊗ₜ[k] x)
    simp only [LinearMap.baseChange_tmul] at h
    exact (congrArg s h).trans (hdiag x)

end TwistRealization

section LocalBrauerDefects

open scoped MatrixGroups WithZero TensorProduct
open Matrix groupCohomology
open _root_.RM03.Brauer
open _root_.RM03.Brauer.ScalarObstruction
open _root_.RM03.Brauer.RelativeIsomorphism
open _root_.RM03.Brauer.ProjectiveClassification
open _root_.Specs.RM03.Brauer.ScalarObstruction (RecordsDefect Presents)
open _root_.Specs.RM03.CSA (degree isCentralDivision rightSubfieldModule)
open _root_.RM03.CSA (isCentralSimple_of_isCentralDivision degree_pos)
open LocalDivisionAlgebras
open private presents_apply presents_of_formula records_mul from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ScalarObstruction
open private coefficient unitConj conjugation conjugation_mk conjugation_injective from
  MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification


section DegreeFromDefect

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
    {n : ℕ}

private theorem valuation_det_dvd [Finite Gal(K/k)]
    (G : Gal(K/k) → GL (Fin n) K) (c : ScalarCocycle k K) (hc : RecordsDefect G c)
    (v : Additive Kˣ →+ ℤ) (hv : ∀ (g : Gal(K/k)) (a : Kˣ), v (Additive.ofMul (g • a)) = v (Additive.ofMul a))
    (m : ℕ) (hm : IsMulCoboundary₂ (fun p => c.val p ^ m)) (g : Gal(K/k)) :
    (n : ℤ) ∣ (m : ℤ) * v (Additive.ofMul (G g).det) := by
  obtain ⟨b, hb⟩ := hm
  let d (g : Gal(K/k)) := v (Additive.ofMul (G g).det)
  let e (g : Gal(K/k)) := v (Additive.ofMul (b g))
  have hd (g h : Gal(K/k)) : (n : ℤ) * v (Additive.ofMul (c.val (g,h))) =
      d g + d h - d (g * h) := by
    have h' := congrArg (fun M : GL (Fin n) K => v (Additive.ofMul M.det)) (hc g h)
    simp only [GeneralLinearGroup.det_scalar, Fintype.card_fin,
      map_mul, map_inv, mapGL, GeneralLinearGroup.map_det, ofMul_mul, ofMul_inv,
      ofMul_pow, map_add, map_neg, map_nsmul, nsmul_eq_mul] at h'
    have hmap : Units.map g.toRingHom (G h).det = g • (G h).det := by
      apply Units.ext
      exact (coefficientAction_formula g (G h).det).symm
    rw [hmap, hv] at h'
    exact h'
  have he (g h : Gal(K/k)) : (m : ℤ) * v (Additive.ofMul (c.val (g,h))) =
      e g + e h - e (g * h) := by
    have h' := congrArg (fun a : Kˣ => v (Additive.ofMul a)) (hb g h)
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, ofMul_pow,
      map_add, map_neg, map_nsmul, nsmul_eq_mul, hv] at h'
    change _ = v (Additive.ofMul (b g)) + v (Additive.ofMul (b h)) - v (Additive.ofMul (b (g * h)))
    omega
  let w : Gal(K/k) →* Multiplicative ℤ :=
    { toFun := fun g => Multiplicative.ofAdd ((m : ℤ) * d g - (n : ℤ) * e g)
      map_one' := by
        have hx := congrArg ((m : ℤ) * ·) (hd 1 1)
        have hy := congrArg ((n : ℤ) * ·) (he 1 1)
        rw [mul_one] at hx hy
        change (m : ℤ) * d 1 - (n : ℤ) * e 1 = 0
        simp only [add_sub_cancel_right] at hx hy
        rw [← hx, ← hy, mul_left_comm (m : ℤ) n, sub_self]
      map_mul' := fun g h => by
        have hx := congrArg ((m : ℤ) * ·) (hd g h)
        have hy := congrArg ((n : ℤ) * ·) (he g h)
        change (m : ℤ) * d (g * h) - (n : ℤ) * e (g * h) =
          (m * d g - n * e g) + (m * d h - n * e h)
        rw [mul_left_comm (m : ℤ) n] at hx
        simp only [mul_sub, mul_add] at hx hy
        omega }
  have hz : w g = 1 := by
    have heq : (orderOf g : ℤ) * ((w g).toAdd) = 0 := by
      have h := congrArg Multiplicative.toAdd (congrArg w (pow_orderOf_eq_one g))
      change _ = (1 : Multiplicative ℤ).toAdd
      simpa only [map_pow, map_one, toAdd_pow, nsmul_eq_mul] using h
    have hpos : (orderOf g : ℤ) ≠ 0 := by exact_mod_cast (orderOf_pos g).ne'
    exact Multiplicative.toAdd.injective ((mul_eq_zero.mp heq).resolve_left hpos)
  refine ⟨e g, ?_⟩
  change (m : ℤ) * d g = (n : ℤ) * e g
  exact sub_eq_zero.mp (congrArg Multiplicative.toAdd hz)

private def unitValuation (v : Valuation K ℤᵐ⁰) : Additive Kˣ →+ ℤ where
  toFun a := WithZero.log (v (a.toMul : K))
  map_zero' := by simp
  map_add' a b := by
    change WithZero.log (v ((a.toMul : K) * (b.toMul : K))) = _
    rw [map_mul, WithZero.log_mul ((map_ne_zero v).mpr a.toMul.ne_zero)
      ((map_ne_zero v).mpr b.toMul.ne_zero)]

/-- The matrix of an iterated semilinear operator after removing its
coefficient automorphism. -/
private def semilinearPower (g : Gal(K/k)) (H : GL (Fin n) K) : ℕ → GL (Fin n) K
  | 0 => 1
  | j + 1 => H * mapGL g (semilinearPower g H j)

private theorem semilinearPower_mulVec (g : Gal(K/k)) (H : GL (Fin n) K) (j : ℕ)
    (x : Fin n → K) :
    ((fun y : Fin n → K => (H : Mat K n) *ᵥ (g ∘ y))^[j]) x =
      (semilinearPower g H j : Mat K n) *ᵥ ((g ^ j) ∘ x) := by
  induction j with
  | zero =>
    simp only [Function.iterate_zero_apply, semilinearPower, GeneralLinearGroup.coe_one, one_mulVec, pow_zero]
    rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, semilinearPower, GeneralLinearGroup.coe_mul,
      ← mulVec_mulVec, pow_succ']
    congr 1
    funext i
    exact RingHom.map_mulVec g.toRingHom _ _ i

private theorem semilinearPower_det (g : Gal(K/k)) (H : GL (Fin n) K) (j : ℕ)
    (v : Additive Kˣ →+ ℤ) (hv : ∀ a : Kˣ, v (Additive.ofMul (g • a)) = v (Additive.ofMul a)) :
    v (Additive.ofMul (semilinearPower g H j).det) = (j : ℤ) * v (Additive.ofMul H.det) := by
  induction j with
  | zero => simp [semilinearPower]
  | succ j ih =>
    rw [semilinearPower, map_mul, ofMul_mul, map_add, mapGL,
      GeneralLinearGroup.map_det]
    have hmap : Units.map g.toRingHom (semilinearPower g H j).det =
        g • (semilinearPower g H j).det := by
      apply Units.ext
      exact (coefficientAction_formula g (semilinearPower g H j).det).symm
    rw [hmap, hv, ih, Nat.cast_succ, add_mul, one_mul, add_comm]

end DegreeFromDefect

section CyclicDefect

variable {F B : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [DivisionRing B] [Algebra F B]
  {w : Valuation B ℤᵐ⁰} {r : ResidueData (F := F) w}

set_option linter.style.haveILetI false in
set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
private theorem cyclicPresentation_defect (hB : isCentralDivision F B)
    (c : CyclicPresentation (F := F) w r) :
    letI := c.fieldL
    letI := c.algebraL
    ∃ (s : c.L ⊗[F] B ≃ₐ[c.L] Mat c.L (degree F B))
      (G : Gal(c.L/F) → GL (Fin (degree F B)) c.L) (a : ScalarCocycle F c.L),
      Presents s G ∧ RecordsDefect G a ∧ unitValuation c.vL (Additive.ofMul (G c.τ).det) = 1 := by
  classical
  letI := c.fieldL
  letI := c.algebraL
  letI := c.galois
  let n := degree F B
  have hn : 0 < n := degree_pos (isCentralSimple_of_isCentralDivision F B hB)
  haveI : FiniteDimensional F B := hB.2
  haveI : FiniteDimensional F c.L := Module.Finite.of_injective c.embed.toLinearMap c.embed.injective
  letI : Module c.L B := rightSubfieldModule c.embed
  letI : Algebra c.L (B ⊗[F] c.L) := Algebra.TensorProduct.rightAlgebra (R := F) (A := B) (B := c.L)
  obtain ⟨iso, hiso⟩ := _root_.RM03.CSA.subfieldTensorAction_isomorphism c.embed hB c.degree
  let b := c.basis
  let e := b.equivFun
  let s := ((_root_.RM03.CSA.baseChangeEquivTensor F c.L B).trans iso).trans (LinearMap.toMatrixAlgEquiv b)
  let τ := c.τ
  let σ : (Fin n → c.L) ≃+ (Fin n → c.L) := AddEquiv.piCongrRight fun _ => τ.toRingEquiv.toAddEquiv
  let T : B ≃+ B :=
    { toFun x := x * (↑(c.uniformizer⁻¹) : B)
      invFun x := x * (c.uniformizer : B)
      left_inv x := by simp
      right_inv x := by simp
      map_add' x y := add_mul _ _ _ }
  have ht (a : c.L) (x : B) : T (a • x) = τ a • T x := (cyclicUniformizerOperator c).1 a x
  let l : (Fin n → c.L) ≃ₗ[c.L] (Fin n → c.L) :=
    { toAddEquiv := ((σ.symm.trans e.symm.toAddEquiv).trans T).trans e.toAddEquiv
      map_smul' a x := by
        have hs : σ.symm (a • x) = τ.symm a • σ.symm x := by
          funext i
          exact map_mul τ.symm a (x i)
        change e (T (e.symm (σ.symm (a • x)))) = a • e (T (e.symm (σ.symm x)))
        rw [hs, map_smul, ht, AlgEquiv.apply_symm_apply, map_smul] }
  let H : GL (Fin n) c.L := GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv l)
  have actH (x : B) : (H : Mat c.L n) *ᵥ (τ ∘ e x) = e (T x) := by
    change Matrix.mulVecLin (H : Mat c.L n) (σ (e x)) = _
    rw [← GeneralLinearGroup.toLin_apply]
    change (GeneralLinearGroup.toLin H).toLinearEquiv (σ (e x)) = _
    rw [GeneralLinearGroup.toLin.apply_symm_apply]
    change e (T (e.symm (σ.symm (σ (e x))))) = _
    rw [σ.symm_apply_apply, e.symm_apply_apply]
  have actS (a : c.L) (x y : B) : s (a ⊗ₜ[F] x) *ᵥ e y = e (x * y * c.embed a) := by
    change LinearMap.toMatrix b b (iso (x ⊗ₜ[F] a)) *ᵥ (b.repr y) = _
    rw [LinearMap.toMatrix_mulVec_repr]
    change e (iso.toAlgHom (x ⊗ₜ[F] a) y) = _
    rw [hiso, _root_.RM03.CSA.subfieldTensorAction_tmul]
  have intertwine (a : c.L) (x : B) :
      (H : Mat c.L n) * (s (a ⊗ₜ[F] x)).map τ = s (τ a ⊗ₜ[F] x) * H := by
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro v
    obtain ⟨z, rfl⟩ := (e.toEquiv.trans σ.toEquiv).surjective v
    change ((H : Mat c.L n) * (s (a ⊗ₜ[F] x)).map τ) *ᵥ (τ ∘ e z) =
      (s (τ a ⊗ₜ[F] x) * (H : Mat c.L n)) *ᵥ (τ ∘ e z)
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    have hmap : (s (a ⊗ₜ[F] x)).map τ *ᵥ (τ ∘ e z) = τ ∘ (s (a ⊗ₜ[F] x) *ᵥ e z) := by
      funext i
      exact (RingHom.map_mulVec τ.toRingHom _ _ i).symm
    rw [hmap, actS, actH, actH, actS]
    have hcomp : T (x * z * c.embed a) = x * T z * c.embed (τ a) := by
      have h := ht a z
      change T (z * c.embed a) = T z * c.embed (τ a) at h
      change (x * z * c.embed a) * ↑(c.uniformizer⁻¹) = x * (z * ↑(c.uniformizer⁻¹)) * c.embed (τ a)
      rw [mul_assoc x z, mul_assoc x, show z * c.embed a * ↑(c.uniformizer⁻¹) =
        (z * ↑(c.uniformizer⁻¹)) * c.embed (τ a) from h, mul_assoc x]
    rw [hcomp]
  obtain ⟨ρ, hρ, p, hp⟩ := transported_cocycle hn s
  have hH : ProjGenLinGroup.mk H = p.val τ := by
    obtain ⟨Q, hQ⟩ := ProjGenLinGroup.mk_surjective (p.val τ)
    rw [← hQ]
    apply conjugation_injective
    apply AlgEquiv.ext
    intro X
    obtain ⟨Y, rfl⟩ := (coefficient τ).surjective X
    have he : unitConj H (coefficient τ Y) = ρ.act τ Y := by
      obtain ⟨y, rfl⟩ := s.surjective Y
      induction y using TensorProduct.inductionOn with
      | tmul a x =>
        rw [hρ]
        change (H : Mat c.L n) * (s (a ⊗ₜ[F] x)).map τ * (↑H⁻¹ : Mat c.L n) = _
        rw [intertwine, Matrix.mul_assoc, H.mul_inv, Matrix.mul_one]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [conjugation_mk, conjugation_mk]
    exact he.trans (hp τ Q hQ Y)
  choose G₀ hG₀ using fun g : Gal(c.L/F) => ProjGenLinGroup.mk_surjective (p.val g)
  let G := Function.update G₀ τ H
  have hg (g : Gal(c.L/F)) : ProjGenLinGroup.mk (G g) = p.val g := by
    by_cases h : g = τ
    · subst g
      simpa only [G, Function.update_self] using hH
    · simpa only [G, Function.update_of_ne h] using hG₀ g
  have pres : Presents s G := ⟨ρ, p, hρ, hp, hg⟩
  obtain ⟨a, ha⟩ := exists_recorded_defect hn pres
  refine ⟨s, G, a, pres, ha, ?_⟩
  have hG : G τ = H := Function.update_self τ H G₀
  rw [hG]
  have horder : orderOf τ = n :=
    (orderOf_eq_card_of_zpowers_eq_top c.gen).trans ((IsGalois.card_aut_eq_finrank F c.L).trans c.degree)
  have hpow : τ ^ n = 1 := horder ▸ pow_orderOf_eq_one τ
  let v := unitValuation c.vL
  have hval (a : c.Lˣ) : v (Additive.ofMul (τ • a)) = v (Additive.ofMul a) := by
    change WithZero.log (c.vL (↑(τ • a) : c.L)) = _
    rw [coefficientAction_formula, c.τ_preserves_value]
    rfl
  have hparam : algebraMap F c.L c.parameter ≠ 0 := by
    intro hp
    have hv := c.base_value c.parameter
    rw [hp, c.value_parameter, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  let π := (Units.mk0 (algebraMap F c.L c.parameter) hparam)⁻¹
  have powScalar : semilinearPower τ H n = GeneralLinearGroup.scalar (Fin n) π := by
    apply Units.ext
    apply Matrix.toLinAlgEquiv'.injective
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := e.surjective z
    change (semilinearPower τ H n : Mat c.L n) *ᵥ e x = Matrix.scalar _ (π : c.L) *ᵥ e x
    have hm := semilinearPower_mulVec τ H n (e x)
    rw [hpow] at hm
    change ((fun y : Fin n → c.L => (H : Mat c.L n) *ᵥ (τ ∘ y))^[n]) (e x) =
      (semilinearPower τ H n : Mat c.L n) *ᵥ e x at hm
    rw [← hm]
    have hIter (j : ℕ) (y : B) :
        ((fun z : Fin n → c.L => (H : Mat c.L n) *ᵥ (τ ∘ z))^[j]) (e y) = e ((T^[j]) y) := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Function.iterate_succ_apply', ih, actH, Function.iterate_succ_apply']
    have hT : ((T : B → B)^[n]) x = ((algebraMap F c.L) c.parameter)⁻¹ • x :=
      (cyclicUniformizerOperator c).2 x
    rw [hIter, hT, map_smul]
    have hs : Matrix.scalar (Fin n) (π : c.L) = (π : c.L) • (1 : Mat c.L n) :=
      (Matrix.smul_one_eq_diagonal _).symm
    rw [hs, smul_mulVec, one_mulVec]
    rfl
  have hπ : v (Additive.ofMul π) = 1 := by
    change WithZero.log (c.vL ((algebraMap F c.L c.parameter)⁻¹)) = 1
    rw [map_inv₀, c.base_value, c.value_parameter]
    simp
  have h := (semilinearPower_det τ H n v hval).symm
  rw [powScalar, GeneralLinearGroup.det_scalar, Fintype.card_fin, ofMul_pow, map_nsmul,
    nsmul_eq_mul, hπ] at h
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast hn.ne')
  exact h

end CyclicDefect


section LocalClassOrder

variable {F B : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [DivisionRing B] [Algebra F B]

set_option maxHeartbeats 950000 in
set_option backward.isDefEq.respectTransparency false in
/-- Over a nonarchimedean local field, the degree of the division representative
divides any integer that kills its Brauer class. -/
theorem localDivisionDegree_dvd_brauerExponent (hB : isCentralDivision F B) (m : ℕ)
    (hm : m • classOf (divisionCSA hB) = 0) :
    degree F B ∣ m := by
  let h := isCentralSimple_of_isCentralDivision F B hB
  obtain ⟨w, hw, _⟩ := valuation_exists h
  obtain ⟨r⟩ := residue_field h w hw
  obtain ⟨_, _, ⟨c⟩⟩ := cyclic_structure h w hw r
  let := c.fieldL
  let := c.algebraL
  let := c.galois
  let : FiniteDimensional F B := hB.2
  let : FiniteDimensional F c.L := Module.Finite.of_injective c.embed.toLinearMap c.embed.injective
  let n := degree F B
  have hn : 0 < n := degree_pos h
  obtain ⟨s, G, a, hs, ha, hval⟩ := cyclicPresentation_defect hB c
  let A := divisionCSA hB
  have hr : classOf A ∈ relativeBrauerGroup.{u,u,u} F c.L :=
    (classOf_mem_relativeBrauerGroup_iff F c.L A).mpr ⟨n, hn, ⟨s⟩⟩
  let x : relativeBrauerGroup.{u,u,u} F c.L := ⟨classOf A, hr⟩
  have hx : m • x = 0 := Subtype.ext hm
  have hf : obstruction.{u,u,u} F c.L x = Additive.ofMul (cocycleClass F c.L a) :=
    obstruction_formula.{u,u,u} F c.L A hr hn s G hs a ha
  have heq := congrArg (obstruction.{u,u,u} F c.L) hx
  rw [map_nsmul, hf, map_zero] at heq
  have hclass : cocycleClass F c.L (a ^ m) = 1 := by
    rw [map_pow]
    exact Additive.ofMul.injective heq
  have hCob : IsMulCoboundary₂ (fun p => a.val p ^ m) :=
    (cocycleClass_eq_one_iff (a ^ m)).mp hclass
  let v := unitValuation c.vL
  let fixed : Subgroup (Gal(c.L/F)) :=
    { carrier := {g | ∀ x : c.L, c.vL (g x) = c.vL x}
      one_mem' := fun _ => rfl
      mul_mem' := by
        intro g j hg hj x
        change c.vL (g (j x)) = c.vL x
        rw [hg (j x), hj x]
      inv_mem' := by
        intro g hg x
        have hz : c.vL (g (g⁻¹ x)) = c.vL (g⁻¹ x) := hg (g⁻¹ x)
        rw [show g (g⁻¹ x) = x from g.apply_symm_apply x] at hz
        exact hz.symm }
  have hfixed : (⊤ : Subgroup (Gal(c.L/F))) ≤ fixed := by
    rw [← c.gen, Subgroup.zpowers_le]
    exact c.τ_preserves_value
  have hv (g : Gal(c.L/F)) (a : c.Lˣ) : v (Additive.ofMul (g • a)) = v (Additive.ofMul a) := by
    change WithZero.log (c.vL ((g • a : c.Lˣ) : c.L)) = _
    rw [coefficientAction_formula, (hfixed (Subgroup.mem_top g) : ∀ x, c.vL (g x) = c.vL x)]
    rfl
  have hd := valuation_det_dvd G a ha v hv m hCob c.τ
  rw [show v (Additive.ofMul (G c.τ).det) = 1 from hval, mul_one] at hd
  exact Int.natCast_dvd_natCast.mp hd

/-- The two-torsion of the local Brauer group consists of the split class and
the quaternion division class, also in residue characteristic two. -/
theorem localBrauer_twoTorsion (x : BrauerGroup.{u,u} F) (hx : 2 • x = 0) :
    x = 0 ∨ ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra F D)
      (hD : isCentralDivision F D), degree F D = 2 ∧ classOf (divisionCSA hD) = x := by
  obtain ⟨D, _, _, hD, hclass⟩ := exists_division_representative F x
  have hp : 0 < degree F D := degree_pos (isCentralSimple_of_isCentralDivision F D hD)
  have hd := localDivisionDegree_dvd_brauerExponent hD 2 (hclass.symm ▸ hx)
  have hle := Nat.le_of_dvd (by decide : (0 : ℕ) < 2) hd
  by_cases htwo : degree F D = 2
  · exact Or.inr ⟨D, inferInstance, inferInstance, hD, htwo, hclass⟩
  · left
    have hone : degree F D = 1 := by omega
    have hdim : Module.finrank F D = 1 := by
      have h : Module.finrank F D = (degree F D) ^ 2 :=
        _root_.RM03.CSA.finrank_eq_degree_sq (isCentralSimple_of_isCentralDivision F D hD)
      rw [h, hone, one_pow]
    let : FiniteDimensional F D := hD.2
    have hBij : Function.Bijective (algebraMap F D) := by
      refine ⟨(algebraMap F D).injective, ?_⟩
      let e := LinearEquiv.ofInjectiveOfFinrankEq (Algebra.linearMap F D)
        (algebraMap F D).injective (by rw [Module.finrank_self, hdim])
      intro y
      obtain ⟨x, hx⟩ := e.surjective y
      exact ⟨x, hx⟩
    let e := AlgEquiv.ofBijective (Algebra.ofId F D) hBij
    have hEq : classOf (divisionCSA hD) = classOf (scalarCSA.{u,u} F) :=
      classOf_eq_of_algEquiv (e.symm.trans ULift.algEquiv.symm)
    rw [← hclass, hEq, ← zero_eq_classOf_scalar]

end LocalClassOrder


section ScalarRestriction

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra F L] [Algebra E L] [IsScalarTower F E L]

private theorem restriction_coefficients (g : Gal(L/E)) (a : Lˣ) :
    ((g.restrictScalars F) • a : Lˣ) = g • a := by
  apply Units.ext
  rw [coefficientAction_formula, coefficientAction_formula]
  rfl

private def restrictedScalarCocycle (a : ScalarCocycle F L) : ScalarCocycle E L :=
  ⟨fun p => a.val (p.1.restrictScalars F, p.2.restrictScalars F), by
    intro g h j
    have hr (g h : Gal(L/E)) : (g * h).restrictScalars F = g.restrictScalars F * h.restrictScalars F :=
      map_mul (AlgEquiv.restrictScalarsHom F (S := E) (A := L)) g h
    change a.val ((g * h).restrictScalars F, j.restrictScalars F) *
        a.val (g.restrictScalars F, h.restrictScalars F) =
      g • a.val (h.restrictScalars F, j.restrictScalars F) *
        a.val (g.restrictScalars F, (h * j).restrictScalars F)
    rw [hr, hr, ← restriction_coefficients (F := F) g]
    exact a.property (g.restrictScalars F) (h.restrictScalars F) (j.restrictScalars F)⟩

set_option maxHeartbeats 750000 in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting the scalar factor set gives the obstruction of the same
matrix presentation after base change to the intermediate field. -/
theorem restrictScalarDefect {A : Type u} [Ring A] [Algebra F A] {n : ℕ}
    (hn : 0 < n) (s : L ⊗[F] A ≃ₐ[L] Mat L n) (G : Gal(L/F) → GL (Fin n) L)
    (hG : Presents s G) (a : ScalarCocycle F L) (ha : RecordsDefect G a) :
    let t := (baseChangeTower F E L A).trans s
    let H := fun g : Gal(L/E) => G (g.restrictScalars F)
    Presents t H ∧ RecordsDefect H (restrictedScalarCocycle (E := E) a) := by
  let t := (baseChangeTower F E L A).trans s
  let H (g : Gal(L/E)) := G (g.restrictScalars F)
  refine ⟨presents_of_formula hn t H ?_, ?_⟩
  · intro g b x
    induction x using TensorProduct.inductionOn with
    | tmul e z =>
      simp only [t, AlgEquiv.trans_apply, baseChangeTower_tmul]
      have h := presents_apply hG (g.restrictScalars F) (e • b) z
      have he : (g.restrictScalars F) (e • b) = e • g b := by
        rw [AlgEquiv.restrictScalars_apply, Algebra.smul_def, Algebra.smul_def, map_mul, g.commutes]
      rw [he] at h
      exact h
    | add x y hx hy =>
      rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add,
        Matrix.map_add _ (map_add g), Matrix.mul_add, Matrix.add_mul, hx, hy]
  · intro g h
    exact ha (g.restrictScalars F) (h.restrictScalars F)

private theorem relativeObstruction_two_eq_one [FiniteDimensional F L] [IsGalois F L]
    (A : _root_.CSA.{u,u} F) (hA : classOf A ∈ relativeBrauerGroup.{u,u,u} F L)
    (htwo : 2 • classOf A = 0) {n : ℕ} (hn : 0 < n)
    (s : L ⊗[F] A ≃ₐ[L] Mat L n) (G : Gal(L/F) → GL (Fin n) L)
    (hG : Presents s G) (a : ScalarCocycle F L) (ha : RecordsDefect G a) :
    cocycleClass F L (a ^ 2) = 1 := by
  let x : relativeBrauerGroup.{u,u,u} F L := ⟨classOf A, hA⟩
  have h : 2 • x = 0 := Subtype.ext htwo
  have hz := congrArg (obstruction.{u,u,u} F L) h
  have hcomp : obstruction.{u,u,u} F L x = Additive.ofMul (cocycleClass F L a) :=
    obstruction_formula.{u,u,u} F L A hA hn s G hG a ha
  rw [map_nsmul, hcomp, map_zero] at hz
  exact (map_pow (cocycleClass F L) a 2).trans (Additive.ofMul.injective hz)

end ScalarRestriction

section LocalInducedDefect

local instance galAdditiveUnits {k L : Type u} [Field k] [Field L] [Algebra k L] :
    DistribMulAction Gal(L/k) (Additive Lˣ) where
  smul g x := Additive.ofMul (g • x.toMul)
  one_smul x := congrArg Additive.ofMul (one_smul Gal(L/k) x.toMul)
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h x.toMul)
  smul_zero g := congrArg Additive.ofMul (smul_one g : g • (1 : Lˣ) = 1)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g x.toMul y.toMul)

variable {F E L B : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field E] [Field L] [Algebra F E] [Algebra F L]
  [Algebra E L] [IsScalarTower F E L] [FiniteDimensional F E] [FiniteDimensional F L]
  [IsGalois F L] [IsGalois E L] [DivisionRing B] [Algebra F B]
  {I : Type*} [Fintype I] [MulAction Gal(L/F) I]

private def scalarDefectAtCoordinate (o : I)
    (φ : Gal(L/E) ≃* MulAction.stabilizer (Gal(L/F)) o)
    (hφ : ∀ g, (φ g : Gal(L/F)) = g.restrictScalars F)
    (d : Gal(L/F) → Gal(L/F) → I → Additive Lˣ)
    (hD : ∀ g h k, ∀ i : I, d g h (k • i) + d (g * h) k i =
      g • d h k i + d g (h * k) i) : ScalarCocycle E L :=
  ⟨fun (g,h) => (d (φ g) (φ h) o).toMul, by
    intro g h j
    have hj : (φ j : Gal(L/F)) • o = o := (φ j).property
    have he := hD (φ g) (φ h) (φ j) o
    rw [hj, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul] at he
    have hs : ((φ g : Gal(L/F)) • d (φ h) (φ j) o).toMul =
        g • (d (φ h) (φ j) o).toMul := by
      change (φ g : Gal(L/F)) • (d (φ h) (φ j) o).toMul = _
      rw [hφ g, restriction_coefficients]
    have hm := congrArg Additive.toMul he
    simp only [toMul_add, hs] at hm
    exact (mul_comm _ _).trans hm⟩

set_option maxHeartbeats 2300000 in
set_option backward.isDefEq.respectTransparency false in
/-- A defect on the three coordinates of a cubic field over a local field is
a coboundary if its restriction to the chosen coordinate has order dividing
two and its norm is a coboundary. The layer includes a splitting field of
the base quaternion class. -/
theorem localInducedDefect_isCoboundary (cubic : Module.finrank F E = 3)
    (hB : isCentralDivision F B) (dB : degree F B = 2)
    (splitB : _root_.Specs.RM03.CSA.isSplit L (L ⊗[F] B))
    (deg : Fintype.card I = 3) (o : I) (transitive : ∀ i : I, ∃ r : Gal(L/F), r • o = i)
    (φ : Gal(L/E) ≃* MulAction.stabilizer (Gal(L/F)) o)
    (hφ : ∀ g, (φ g : Gal(L/F)) = g.restrictScalars F)
    (d : Gal(L/F) → Gal(L/F) → I → Additive Lˣ)
    (assoc : ∀ g h k, ∀ i : I, d g h (k • i) + d (g * h) k i =
      g • d h k i + d g (h * k) i)
    (twice : MulAction.stabilizer (Gal(L/F)) o → Additive Lˣ)
    (h₂ : ∀ g h : MulAction.stabilizer (Gal(L/F)) o,
      d g h o + d g h o = twice g + (g : Gal(L/F)) • twice h - twice (g * h))
    (norm : Gal(L/F) → Additive Lˣ)
    (hN : ∀ g h, ∑ i, d g h i = norm g + g • norm h - norm (g * h)) :
    ∃ f : Gal(L/F) → I → Additive Lˣ,
      ∀ g h, ∀ i : I, d g h i = f g (h • i) + g • f h i - f (g * h) i := by
  let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite F E L
  let a := scalarDefectAtCoordinate o φ hφ d assoc
  have valA (g h : Gal(L/E)) : Additive.ofMul (a.val (g,h)) = d (φ g) (φ h) o := rfl
  have hact (g : Gal(L/E)) (u : Additive Lˣ) : ((φ g : Gal(L/F)) • u : Additive Lˣ) = g • u := by
    apply Additive.toMul.injective
    rw [hφ g]
    exact restriction_coefficients g u.toMul
  have hCob : IsMulCoboundary₂ (a ^ 2).val := by
    refine ⟨fun g => (twice (φ g)).toMul, ?_⟩
    intro g h
    apply Additive.ofMul.injective
    have ht := (h₂ (φ g) (φ h)).symm
    rw [← map_mul, hact] at ht
    change Additive.ofMul (g • (twice (φ h)).toMul / (twice (φ (g * h))).toMul *
        (twice (φ g)).toMul) = Additive.ofMul ((a ^ 2).val (g,h))
    rw [pow_two, Subgroup.coe_mul, Pi.mul_apply]
    simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv, valA]
    change g • twice (φ h) + -twice (φ (g * h)) + twice (φ g) = _
    rw [← ht]
    abel
  have he := (cocycleClass_eq_one_iff (a ^ 2)).mpr hCob
  let eqv := relativeBrauerEquiv.{u,u,u} (k := E) (K := L)
  let x : relativeBrauerGroup.{u,u,u} E L := eqv.symm (Additive.ofMul (cocycleClass E L a))
  have hx : eqv x = Additive.ofMul (cocycleClass E L a) := eqv.apply_symm_apply _
  have hx₂ : 2 • x = 0 := by
    apply eqv.injective
    rw [map_nsmul, hx, map_zero]
    exact congrArg Additive.ofMul ((map_pow (cocycleClass E L) a 2).symm.trans he)
  obtain ⟨r, T, _, hE, _⟩ := finiteExtension_localField (K := F) (L := E)
  let : ValuativeRel E := r
  let : TopologicalSpace E := T
  rcases localBrauer_twoTorsion (x : BrauerGroup.{u,u} E) (congrArg Subtype.val hx₂) with hz | hq
  · have h0 : x = 0 := Subtype.ext hz
    have h1 : cocycleClass E L a = 1 := by
      apply Additive.ofMul.injective
      rw [← hx, h0, map_zero]
      rfl
    obtain ⟨f, hf⟩ := (cocycleClass_eq_one_iff a).mp h1
    apply inducedDefect_isCoboundary o transitive d assoc (fun g => Additive.ofMul (f (φ.symm g)))
    intro g h
    obtain ⟨g, rfl⟩ := φ.surjective g
    obtain ⟨h, rfl⟩ := φ.surjective h
    simp only [MulEquiv.symm_apply_apply, ← map_mul, hact]
    have hh := congrArg Additive.ofMul (hf g h)
    change g • Additive.ofMul (f h) - Additive.ofMul (f (g * h)) + Additive.ofMul (f g) =
      d (φ g) (φ h) o at hh
    rw [← hh]
    abel
  · obtain ⟨D, _, _, hD, dD, hclass⟩ := hq
    obtain ⟨B', _, _, hB', dB', ⟨e⟩⟩ := quaternionOverCubic_isBaseChange cubic hD dD
    obtain ⟨e₀⟩ := LocalQuadraticSplitting.local_division_unique hB dB hB' dB'
    let A := divisionCSA hB
    let AE := baseChangeCSA F E A
    let eE : (AE : Type u) ≃ₐ[E] D :=
      (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[E] E) e₀).trans e
    have hAE : classOf AE = (x : BrauerGroup.{u,u} E) :=
      (classOf_eq_of_algEquiv eE).trans hclass
    obtain ⟨n, hn, ⟨s⟩⟩ := splitB
    obtain ⟨G, hG⟩ := exists_presentation hn s
    obtain ⟨c, hc⟩ := exists_recorded_defect hn hG
    let t := (baseChangeTower F E L B).trans s
    let H (g : Gal(L/E)) := G (g.restrictScalars F)
    obtain ⟨hH, hcE⟩ := restrictScalarDefect hn s G hG c hc (E := E)
    have hA : classOf A ∈ relativeBrauerGroup.{u,u,u} F L :=
      (classOf_mem_relativeBrauerGroup_iff F L A).mpr ⟨n, hn, ⟨s⟩⟩
    have htwo : 2 • classOf A = 0 := localQuaternion_two_nsmul_class hB dB
    have hsq := relativeObstruction_two_eq_one A hA htwo hn s G hG c hc
    obtain ⟨l, hl⟩ := (cocycleClass_eq_one_iff (c ^ 2)).mp hsq
    have hCE : cocycleClass E L a = cocycleClass E L (restrictedScalarCocycle (E := E) c) := by
      have hm : classOf AE ∈ relativeBrauerGroup.{u,u,u} E L :=
        (classOf_mem_relativeBrauerGroup_iff E L AE).mpr ⟨n, hn, ⟨t⟩⟩
      have hsame : (⟨classOf AE, hm⟩ : relativeBrauerGroup.{u,u,u} E L) = x := Subtype.ext hAE
      have hh := obstruction_formula.{u,u,u} E L AE hm hn t H hH
        (restrictedScalarCocycle (E := E) c) hcE
      change eqv ⟨classOf AE, hm⟩ = _ at hh
      rw [hsame] at hh
      exact Additive.ofMul.injective (hx.symm.trans hh)
    obtain ⟨b, hb⟩ := (cocycleClass_eq_iff (restrictedScalarCocycle (E := E) c) a).mp hCE.symm
    apply norm_diagonalDefect_isCoboundary deg o transitive d assoc
      (fun g h => Additive.ofMul (c.val (g,h))) ?_
      (fun g => Additive.ofMul (b (φ.symm g))) ?_
      (fun g => Additive.ofMul (l g)) ?_ norm hN
    · intro g h j
      have hh := congrArg Additive.ofMul (c.property g h j)
      change Additive.ofMul (c.val (g * h,j)) + Additive.ofMul (c.val (g,h)) =
        g • Additive.ofMul (c.val (h,j)) + Additive.ofMul (c.val (g,h * j)) at hh
      rw [add_comm]
      exact hh
    · intro g h
      obtain ⟨g, rfl⟩ := φ.surjective g
      obtain ⟨h, rfl⟩ := φ.surjective h
      simp only [MulEquiv.symm_apply_apply, ← map_mul, hact]
      have hh := congrArg Additive.ofMul (hb g h)
      change g • Additive.ofMul (b h) - Additive.ofMul (b (g * h)) + Additive.ofMul (b g) =
        d (φ g) (φ h) o - Additive.ofMul (c.val (g.restrictScalars F, h.restrictScalars F)) at hh
      rw [← hφ g, ← hφ h] at hh
      rw [← hh]
      abel
    · intro g h
      have hh := congrArg Additive.ofMul (hl g h)
      change Additive.ofMul (g • l h / l (g * h) * l g) =
        Additive.ofMul ((c ^ 2).val (g,h)) at hh
      rw [pow_two, Subgroup.coe_mul, Pi.mul_apply] at hh
      simp only [div_eq_mul_inv, ofMul_mul, ofMul_inv] at hh
      change g • Additive.ofMul (l h) + -Additive.ofMul (l (g * h)) + Additive.ofMul (l g) = _ at hh
      rw [← hh]
      abel

section InducedHilbert90

private theorem inducedCocycle_isCoboundary {Γ I A : Type*} [Group Γ] [MulAction Γ I]
    [AddCommGroup A] [DistribMulAction Γ A]
    (o : I) (transitive : ∀ i : I, ∃ r : Γ, r • o = i)
    (f : Γ → I → A)
    (hf : ∀ g h i, f (g * h) i = f g (h • i) + g • f h i)
    (b : A) (hb : ∀ g : MulAction.stabilizer Γ o, f g o = (g : Γ) • b - b) :
    ∃ z : I → A, ∀ g i, f g i = g • z i - z (g • i) := by
  classical
  choose r hr using transitive
  let s (g : Γ) (i : I) : MulAction.stabilizer Γ o :=
    ⟨(r (g • i))⁻¹ * (g * r i), by
      change ((r (g • i))⁻¹ * (g * r i)) • o = o
      rw [mul_smul, mul_smul, hr, inv_smul_eq_iff, hr]⟩
  have hs (g : Γ) (i : I) : r (g • i) * (s g i : Γ) = g * r i := by simp [s]
  refine ⟨fun i => r i • b - f (r i) o, fun g i => ?_⟩
  have h₁ := hf g (r i) o
  have h₂ := hf (r (g • i)) (s g i) o
  rw [hr] at h₁
  rw [(s g i).property, hb, smul_sub, ← mul_smul, hs, mul_smul] at h₂
  rw [← add_sub_cancel_right (f g i) (g • f (r i) o), ← h₁, h₂, smul_sub]
  simp only [sub_eq_add_neg, neg_add, neg_neg]
  abel

variable {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E] [Algebra F L]
  [Algebra E L] [IsScalarTower F E L] [FiniteDimensional E L]
  {I : Type*} [MulAction Gal(L/F) I]

/-- Scalar Hilbert 90 on the permuted coordinates, evaluated at the chosen
embedding and transported to the other embeddings. -/
theorem inducedUnitCocycle_isCoboundary
    (o : I) (transitive : ∀ i : I, ∃ r : Gal(L/F), r • o = i)
    (φ : Gal(L/E) ≃* MulAction.stabilizer (Gal(L/F)) o)
    (hφ : ∀ g, (φ g : Gal(L/F)) = g.restrictScalars F)
    (f : Gal(L/F) → I → Lˣ)
    (hf : ∀ g h (i : I), f (g * h) i = f g (h • i) * g • f h i) :
    ∃ z : I → Lˣ, ∀ g i, f g i = z (g • i) / (g • z i) := by
  let h (g : Gal(L/E)) := f (φ g) o
  have hC : IsMulCocycle₁ h := by
    intro g j
    change f (φ (g * j)) o = g • f (φ j) o * f (φ g) o
    rw [map_mul, Subgroup.coe_mul, hf, (φ j).property, hφ g, restriction_coefficients]
    exact mul_comm (f (g.restrictScalars F) o) (g • f (φ j) o)
  obtain ⟨b, hb⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units h hC
  have he (g : MulAction.stabilizer (Gal(L/F)) o) :
      Additive.ofMul (f g o) = (g : Gal(L/F)) • Additive.ofMul b - Additive.ofMul b := by
    obtain ⟨j, rfl⟩ := φ.surjective g
    have hh := hb j
    change j • b / b = f (φ j) o at hh
    rw [← restriction_coefficients (F := F), ← hφ] at hh
    exact congrArg Additive.ofMul hh.symm
  obtain ⟨z, hz⟩ := inducedCocycle_isCoboundary o transitive
    (fun g i => Additive.ofMul (f g i)) (fun g j i => congrArg Additive.ofMul (hf g j i))
    (Additive.ofMul b) he
  refine ⟨fun i => (z i).toMul⁻¹, ?_⟩
  intro g i
  have h := congrArg Additive.toMul (hz g i)
  change f g i = g • (z i).toMul / (z (g • i)).toMul at h
  rw [h, smul_inv', inv_div_inv]

end InducedHilbert90
end LocalInducedDefect

end LocalBrauerDefects

section SplitRootComparison


open LinearAlgebraicGroups.Specs.Pinning (BasedRootDatum BasedIso)
open LinearAlgebraicGroups.Classification.IntegralRootRelations (simpleCorootBasis simpleCorootBasis_apply)
open scoped BigOperators


section RootDatumComparison

private theorem transportRootPairs (P Q : BasedRootDatum.{u})
    (f : P.X ≃ₗ[ℤ] Q.X) (g : P.Y ≃ₗ[ℤ] Q.Y)
    (hPair : ∀ x y, Q.datum.toLinearMap (f x) (g y) = P.datum.toLinearMap x y)
    (s : P.base.support ≃ Q.base.support)
    (hf : ∀ i : P.base.support, f (P.datum.root i) = Q.datum.root (s i))
    (hg : ∀ i : P.base.support, g (P.datum.coroot i) = Q.datum.coroot (s i)) :
    ∀ i, ∃ j, f (P.datum.root i) = Q.datum.root j ∧ g (P.datum.coroot i) = Q.datum.coroot j := by
  let : P.datum.IsReduced := P.reduced
  let : Finite P.I := P.finiteRoots
  intro i
  apply P.base.induction_reflect i
  · rintro a ⟨b, h₁, h₂⟩
    refine ⟨Q.datum.reflectionPerm b b, ?_, ?_⟩
    · rw [P.datum.root_reflectionPerm, Q.datum.root_reflectionPerm, P.datum.reflection_apply_self,
        Q.datum.reflection_apply_self, map_neg, h₁]
    · rw [P.datum.coroot_reflectionPerm, Q.datum.coroot_reflectionPerm, P.datum.coreflection_apply_self,
        Q.datum.coreflection_apply_self, map_neg, h₂]
  · intro a ha
    exact ⟨s ⟨a, ha⟩, hf ⟨a, ha⟩, hg ⟨a, ha⟩⟩
  · rintro a b ⟨d, h₁, h₂⟩ hb
    let b₀ : P.base.support := ⟨b, hb⟩
    let d₀ := (s b₀).val
    have hb₁ : f (P.datum.root b) = Q.datum.root d₀ := hf b₀
    have hb₂ : g (P.datum.coroot b) = Q.datum.coroot d₀ := hg b₀
    have hp₁ : Q.datum.pairing d d₀ = P.datum.pairing a b := by
      simpa only [h₁, hb₂, RootPairing.root_coroot_eq_pairing] using
        hPair (P.datum.root a) (P.datum.coroot b)
    have hp₂ : Q.datum.pairing d₀ d = P.datum.pairing b a := by
      simpa only [hb₁, h₂, RootPairing.root_coroot_eq_pairing] using
        hPair (P.datum.root b) (P.datum.coroot a)
    refine ⟨Q.datum.reflectionPerm d₀ d, ?_, ?_⟩
    · rw [P.datum.root_reflectionPerm, Q.datum.root_reflectionPerm, P.datum.reflection_apply_root,
        Q.datum.reflection_apply_root, map_sub, map_smul, h₁, hb₁, hp₁]
    · rw [P.datum.coroot_reflectionPerm, Q.datum.coroot_reflectionPerm, P.datum.coreflection_apply_coroot,
        Q.datum.coreflection_apply_coroot, map_sub, map_smul, h₂, hb₂, hp₂]

set_option maxHeartbeats 1200000 in
/-- The Cartan matrix determines a based root datum whose simple coroots
are a basis of the full cocharacter lattice. -/
theorem simplyConnectedDatum_iso (P Q : BasedRootDatum.{u})
    (hP : Submodule.span ℤ (Set.range P.datum.coroot) = ⊤)
    (hQ : Submodule.span ℤ (Set.range Q.datum.coroot) = ⊤)
    (s : P.base.support ≃ Q.base.support)
    (h : ∀ i j : P.base.support, P.datum.pairing i j = Q.datum.pairing (s i) (s j)) :
    ∃ e : BasedIso P Q, ∀ i : P.base.support, e.val.indexEquiv i = (s i).val := by
  classical
  let b := simpleCorootBasis P hP
  let c := simpleCorootBasis Q hQ
  let g := b.equiv c s
  have hg (i : P.base.support) : g (P.datum.coroot i) = Q.datum.coroot (s i) := by
    rw [← simpleCorootBasis_apply P hP i, ← simpleCorootBasis_apply Q hQ (s i)]
    exact b.equiv_apply i c s
  let f := P.datum.toPerfPair.trans (g.symm.dualMap.trans Q.datum.toPerfPair.symm)
  have hPair (x : P.X) (y : P.Y) :
      Q.datum.toLinearMap (f x) (g y) = P.datum.toLinearMap x y := by
    let v := g.symm.dualMap (P.datum.toPerfPair x)
    have hv := DFunLike.congr_fun (Q.datum.toPerfPair.apply_symm_apply v) (g y)
    change Q.datum.toLinearMap (f x) (g y) = P.datum.toLinearMap x (g.symm (g y)) at hv
    simpa only [g.symm_apply_apply] using hv
  have hf (i : P.base.support) : f (P.datum.root i) = Q.datum.root (s i) := by
    apply Q.datum.toPerfPair.injective
    apply c.ext
    intro j
    obtain ⟨j, rfl⟩ := s.surjective j
    have hc : c (s j) = Q.datum.coroot (s j) := simpleCorootBasis_apply Q hQ (s j)
    change Q.datum.toLinearMap (f (P.datum.root i)) (c (s j)) =
      Q.datum.toLinearMap (Q.datum.root (s i)) (c (s j))
    rw [hc, ← hg j, hPair, hg j, RootPairing.root_coroot_eq_pairing, RootPairing.root_coroot_eq_pairing]
    exact h i j
  choose m hm using transportRootPairs P Q f g hPair s hf hg
  have hPairInv (x : Q.X) (y : Q.Y) :
      P.datum.toLinearMap (f.symm x) (g.symm y) = Q.datum.toLinearMap x y := by
    simpa only [f.apply_symm_apply, g.apply_symm_apply] using (hPair (f.symm x) (g.symm y)).symm
  have hfInv (i : Q.base.support) : f.symm (Q.datum.root i) = P.datum.root (s.symm i) := by
    have he := hf (s.symm i)
    rw [s.apply_symm_apply] at he
    exact (f.symm_apply_eq).mpr he.symm
  have hgInv (i : Q.base.support) : g.symm (Q.datum.coroot i) = P.datum.coroot (s.symm i) := by
    have he := hg (s.symm i)
    rw [s.apply_symm_apply] at he
    exact (g.symm_apply_eq).mpr he.symm
  have hmi : Function.Injective m := by
    intro i j he
    apply P.datum.root.injective
    apply f.injective
    rw [(hm i).1, (hm j).1, he]
  have hms : Function.Surjective m := by
    intro j
    obtain ⟨i, hi, _⟩ := transportRootPairs Q P f.symm g.symm hPairInv s.symm hfInv hgInv j
    refine ⟨i, Q.datum.root.injective ?_⟩
    rw [← (hm i).1, ← hi, f.apply_symm_apply]
  let eI := Equiv.ofBijective m ⟨hmi, hms⟩
  let e : P.datum.Equiv Q.datum :=
    { weightMap := f
      coweightMap := g.symm
      indexEquiv := eI
      weight_coweight_transpose := by
        ext y x
        change Q.datum.toLinearMap (f x) y = P.datum.toLinearMap x (g.symm y)
        simpa only [g.apply_symm_apply] using hPair x (g.symm y)
      root_weightMap := funext fun i => (hm i).1
      coroot_coweightMap := by
        funext j
        obtain ⟨i, rfl⟩ := eI.surjective j
        change g.symm (Q.datum.coroot (eI i)) = P.datum.coroot (eI.symm (eI i))
        rw [Equiv.symm_apply_apply]
        exact (g.symm_apply_eq).mpr (hm i).2.symm
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.symm.bijective }
  have hes (i : P.base.support) : e.indexEquiv i = (s i).val :=
    Q.datum.root.injective ((hm i).1.symm.trans (hf i))
  refine ⟨⟨e, ?_⟩, hes⟩
  ext j
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hes ⟨a, ha⟩]
    exact (s ⟨a, ha⟩).property
  · intro hj
    obtain ⟨a, ha⟩ := s.surjective ⟨j, hj⟩
    exact ⟨a.val, a.property, (hes a).trans (congrArg Subtype.val ha)⟩

end RootDatumComparison


section SplitSpinDatum

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.SpinWeights
open LinearAlgebraicGroups.Specs.Pinning (AttachedDatum SplitBorelPair)
open RankOneFlag (IsGeometricallyMaximal)
open CharacterDescent (Character Cocharacter)
open CharacterPairing (absoluteRoots pairing)
open AbstractPairing (Root)
open TrialitarianAlbertDescentSpecification (cartanD4)
open private even_sum_iff vectorPullback_injective latticePairing_vectorPullback from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights

private def simpleD4 : Fin 4 → VectorExponents :=
  ![![1, -1, 0, 0], ![0, 0, 1, -1], ![0, 0, 1, 1], ![0, 1, -1, 0]]

private theorem simpleD4_mem (i : Fin 4) : simpleD4 i ∈ vectorRoots := by
  fin_cases i
  · refine ⟨0, 1, by decide, Or.inr (Or.inl ?_)⟩
    funext j
    fin_cases j <;> decide
  · refine ⟨2, 3, by decide, Or.inr (Or.inl ?_)⟩
    funext j
    fin_cases j <;> decide
  · refine ⟨2, 3, by decide, Or.inl ?_⟩
    funext j
    fin_cases j <;> decide
  · refine ⟨1, 2, by decide, Or.inr (Or.inl ?_)⟩
    funext j
    fin_cases j <;> decide

private theorem simpleD4_independent : LinearIndependent ℤ simpleD4 := by
  apply Fintype.linearIndependent_iff.mpr
  intro c h i
  have h₀ := congrFun h (0 : Fin 4)
  have h₁ := congrFun h (1 : Fin 4)
  have h₂ := congrFun h (2 : Fin 4)
  have h₃ := congrFun h (3 : Fin 4)
  simp [Finset.sum_apply, Fin.sum_univ_four, simpleD4] at h₀ h₁ h₂ h₃
  fin_cases i
  · change c 0 = 0; omega
  · change c 1 = 0; omega
  · change c 2 = 0; omega
  · change c 3 = 0; omega

private theorem simpleD4_spans (x : evenSumLattice) :
    ∃ c : Fin 4 → ℤ, (∑ i, c i • simpleD4 i) = x.val := by
  obtain ⟨m, hm⟩ := (even_sum_iff x.val).mp x.property
  refine ⟨![x.val 0, m - x.val 3, m, x.val 0 + x.val 1], ?_⟩
  funext i
  rw [Fin.sum_univ_four] at hm
  fin_cases i <;> simp [Finset.sum_apply, Fin.sum_univ_four, simpleD4]
  omega

private theorem simpleD4_pairing (i j : Fin 4) :
    simpleD4 i ⬝ᵥ simpleD4 j = cartanD4 i j := by
  fin_cases i <;> fin_cases j <;> decide

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The marked spin datum admits the integral D₄ base with the three
outer roots numbered first. -/
theorem spinDatum_D4 {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (A : AbstractPairing.Datum T)
    (X : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
    (hpair : ∀ (χ : Character T.group) (c : Cocharacter T.group),
      pairing T.group χ c = latticePairing (X (Additive.ofMul χ)) (Y (Additive.ofMul c)))
    (hroot : Set.SurjOn (fun χ : Character T.group => X (Additive.ofMul χ))
      (absoluteRoots T) rootCharacters)
    (hc : ∀ α : Root T, vectorPullback (Y (A.rootDatum.coroot α)).val = X (Additive.ofMul α.val)) :
    ∃ (B : A.rootDatum.Base) (s : Fin 4 ≃ B.support),
      (∀ i j, A.rootDatum.pairing (s i).val (s j).val = cartanD4 i j) ∧
        Submodule.span ℤ (Set.range A.rootDatum.coroot) = ⊤ := by
  classical
  let : Finite (Root T) := A.finiteRoots
  let : Fintype (Root T) := Fintype.ofFinite _
  have hr (i : Fin 4) : ∃ α : Root T, X (A.rootDatum.root α) = vectorPullback (simpleD4 i) := by
    obtain ⟨χ, hχ, h⟩ := hroot ⟨simpleD4 i, simpleD4_mem i, rfl⟩
    exact ⟨⟨χ, hχ⟩, by rw [A.root_eq]; exact h⟩
  choose r hr using hr
  let y : Additive (Cocharacter T.group) →ₗ[ℤ] VectorExponents :=
    evenSumLattice.subtype.comp Y.toLinearMap
  have hy (i : Fin 4) : y (A.rootDatum.coroot (r i)) = simpleD4 i := by
    apply vectorPullback_injective
    rw [show vectorPullback (y (A.rootDatum.coroot (r i))) = X (A.rootDatum.root (r i)) by
      rw [A.root_eq]
      exact hc (r i)]
    exact hr i
  have hyi : Function.Injective y := Subtype.val_injective.comp Y.injective
  have hli : LinearIndependent ℤ (fun i => A.rootDatum.coroot (r i)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c h i
    have h' := congrArg y h
    simp only [map_sum, map_smul, map_zero, hy] at h'
    exact Fintype.linearIndependent_iff.mp simpleD4_independent c h' i
  have hri : Function.Injective r := by
    intro i j hij
    apply hli.injective
    exact congrArg A.rootDatum.coroot hij
  let supp : Finset (Root T) := Finset.univ.map ⟨r, hri⟩
  let s : Fin 4 ≃ supp := Equiv.ofBijective
    (fun i => ⟨r i, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
    ⟨fun i j h => hri (congrArg Subtype.val h), fun x => by
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp x.property
      exact ⟨i, Subtype.ext hi⟩⟩
  have hli' : LinearIndepOn ℤ A.rootDatum.coroot supp := by
    change LinearIndependent ℤ (fun i : supp => A.rootDatum.coroot i)
    exact (linearIndependent_equiv s).mp hli
  have hspan : ∀ c : Additive (Cocharacter T.group),
      ∃ b : Fin 4 → ℤ, c = ∑ i, b i • A.rootDatum.coroot (r i) := by
    intro c
    obtain ⟨b, hb⟩ := simpleD4_spans (Y c)
    refine ⟨b, hyi ?_⟩
    rw [map_sum]
    simp only [map_smul, hy]
    exact hb.symm
  have pair (i j : Fin 4) : A.rootDatum.pairing (r i) (r j) = cartanD4 i j := by
    rw [← RootPairing.root_coroot_eq_pairing, A.root_eq]
    have hp := A.pairing_eq (r i).val (Additive.toMul (A.rootDatum.coroot (r j)))
    change A.rootDatum.toLinearMap (Additive.ofMul (r i).val) (A.rootDatum.coroot (r j)) = _ at hp
    rw [hp, hpair]
    change latticePairing (X (Additive.ofMul (r i).val)) (Y (A.rootDatum.coroot (r j))) = _
    have h₁ : X (Additive.ofMul (r i).val) = vectorPullback (simpleD4 i) :=
      (congrArg X (A.root_eq (r i))).symm.trans (hr i)
    rw [h₁, latticePairing_vectorPullback]
    change simpleD4 i ⬝ᵥ y (A.rootDatum.coroot (r j)) = _
    rw [hy, simpleD4_pairing]
  have nonpos : Set.Pairwise (supp : Set (Root T)) fun a b => A.rootDatum.pairingIn ℤ a b ≤ 0 := by
    intro a ha b hb hab
    obtain ⟨i, hi⟩ := s.surjective ⟨a, ha⟩
    obtain ⟨j, hj⟩ := s.surjective ⟨b, hb⟩
    have h₁ : r i = a := congrArg Subtype.val hi
    have h₂ : r j = b := congrArg Subtype.val hj
    have hne : i ≠ j := fun h => hab (h₁.symm.trans (h ▸ h₂))
    rw [← h₁, ← h₂, show A.rootDatum.pairingIn ℤ (r i) (r j) =
      A.rootDatum.pairing (r i) (r j) from A.rootDatum.algebraMap_pairingIn ℤ _ _,
      pair, cartanD4, ite_eq_right hne]
    split <;> omega
  have spanY (i : Root T) :
      A.rootDatum.coroot i ∈ Submodule.span ℤ (A.rootDatum.coroot '' (supp : Set (Root T))) := by
    obtain ⟨b, h⟩ := hspan (A.rootDatum.coroot i)
    rw [h]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨r j, (s j).property, rfl⟩)
  let cc := X.symm.toLinearMap.comp (vectorPullback.comp y)
  have cc_eq (α : Root T) : cc (A.rootDatum.coroot α) = A.rootDatum.root α := by
    change X.symm (vectorPullback (Y (A.rootDatum.coroot α)).val) = _
    rw [hc, LinearEquiv.symm_apply_apply, A.root_eq]
  have spanX (i : Root T) :
      A.rootDatum.root i ∈ Submodule.span ℤ (A.rootDatum.root '' (supp : Set (Root T))) := by
    obtain ⟨b, h⟩ := hspan (A.rootDatum.coroot i)
    have h' := congrArg cc h
    simp only [cc_eq, map_sum, map_smul] at h'
    rw [h']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨r j, (s j).property, rfl⟩)
  let B := RootPairing.Base.mkOfPairwiseLEZero A.rootDatum
    ((A.rootDatum.linearIndepOn_coroot_iff).mp hli') nonpos spanY spanX
  refine ⟨B, s, pair, ?_⟩
  apply top_unique
  intro c _
  obtain ⟨b, hb⟩ := hspan c
  rw [hb]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self (r i)))

end SplitSpinDatum


section SplitClassification

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.Pinning (AttachedDatum SplitBorelPair)
open LinearAlgebraicGroups.Specs.SpinWeights
open LinearAlgebraicGroups.Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus)
open LinearAlgebraicGroups.Specs.RankOneFlag (IsGeometricallyMaximal)
open LinearAlgebraicGroups.Specs.SimplyConnectedLattice (GeometricallySimplyConnected corootLattice)
open LinearAlgebraicGroups.Specs.CharacterDescent (Character Cocharacter)
open LinearAlgebraicGroups.Specs.CharacterPairing (absoluteRoots pairing)
open LinearAlgebraicGroups.Specs.AbstractPairing (Root)
open TrialitarianAlbertDescentSpecification (cartanD4)
open private splitBorelPair from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private actualDatum_unique from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.TransportedRootCoordinates

set_option maxHeartbeats 1900000 in
set_option backward.isDefEq.respectTransparency false in
/-- The split spin scheme of the marked rank-eight norm is isomorphic to a
split simply connected semisimple group with based Cartan matrix D₄. -/
theorem spinGroup_iso_of_D4 {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (hG : IsReductive G) (T : ClosedSubgroup G.val) (hT : IsSplitTorus T.group)
    (hmax : IsGeometricallyMaximal T) [IsCommMonObj T.group.X]
    (A : AbstractPairing.Datum T)
    (X : Additive (Character T.group) ≃ₗ[ℤ] CharacterExponents)
    (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSumLattice)
    (hpair : ∀ (χ : Character T.group) (c : Cocharacter T.group),
      pairing T.group χ c = latticePairing (X (Additive.ofMul χ)) (Y (Additive.ofMul c)))
    (hroot : Set.SurjOn (fun χ : Character T.group => X (Additive.ofMul χ))
      (absoluteRoots T) rootCharacters)
    (hc : ∀ α : Root T, vectorPullback (Y (A.rootDatum.coroot α)).val = X (Additive.ofMul α.val))
    (P : SplitBorelPair k) (D : AttachedDatum P) (hS : IsSemisimple P.G)
    (hSC : GeometricallySimplyConnected P.G)
    (roots : Fin 4 ≃ D.toBased.base.support)
    (cartan : ∀ i j, D.toBased.datum.pairing (roots i).val (roots j).val = cartanD4 i j) :
    Nonempty (P.G.val ≅ G.val) := by
  let Q := splitBorelPair G hG T hT hmax
  let E := LinearAlgebraicGroups.Classification.Pinning.attachedDatum Q
  have hA : A = E.datum := actualDatum_unique hG hT hmax A E.datum
  subst A
  let : IsCommMonObj Q.T.group.X := E.comm
  obtain ⟨B, r, hcartan, hY⟩ := spinDatum_D4 E.datum X Y hpair hroot hc
  let E' : BasedRootDatum := { E.toBased with base := B }
  let : IsCommMonObj P.T.group.X := D.comm
  have hD : corootLattice D = ⊤ :=
    (LinearAlgebraicGroups.Classification.SimplyConnectedLattice.latticeCriterion
      P.G hS P.T P.split P.maximal D.datum).mp hSC
  let f : D.toBased.base.support ≃ E'.base.support := roots.symm.trans r
  have hm (i j : D.toBased.base.support) :
      D.toBased.datum.pairing i j = E'.datum.pairing (f i) (f j) := by
    obtain ⟨i, rfl⟩ := roots.surjective i
    obtain ⟨j, rfl⟩ := roots.surjective j
    have hf (i : Fin 4) : f (roots i) = r i := by
      change r (roots.symm (roots i)) = r i
      rw [roots.symm_apply_apply]
    rw [cartan, hf, hf]
    exact (hcartan i j).symm
  obtain ⟨e, _⟩ := simplyConnectedDatum_iso D.toBased E' hD hY f hm
  exact ((LinearAlgebraicGroups.Classification.PinnedEquivalence.pinnedEquivalence.2 k).2.1
    P Q D E).mpr ⟨e.val⟩

end SplitClassification

end SplitRootComparison

section SplitSpinFrames


open CategoryTheory Matrix CliffordAlgebra
open scoped CategoryTheory.MonObj TensorProduct Matrix
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open LinearAlgebraicGroups.Specs.SpinWeights
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open SplitSpinSpecification (integralForm ExtendedModule HasActionMatrix middle hyperbolicBasis PairIndex)
open SpinSpecification (ScalarClifford spinUnits coefficientMap vectors)
open private integralZornIsometry scalarIsometry scalarIsometry_spin scalarIsometry_natural
  spinPoints spinRelatedEquiv spinRelated_naturality spinRelated_spec extendedClifford extendedClifford_vector
  clifford_vector_injective zornBasis from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.Triality
open private middle_diagonal vectorEigenvalue from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SpinWeights
open private splitCoordinates from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Albert.SplitSpin

variable (R : Type u) [CommRing R]

private noncomputable abbrev zornVectorComparison : ExtendedModule 4 R ≃ₗ[R] Zorn R :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
    integralZornIsometry.toLinearEquiv).trans (Composition.Zorn.baseChange ℤ R)

private noncomputable abbrev zornCliffordComparison :
    SplitSpinSpecification.ScalarClifford 4 R ≃ₐ[R] CliffordAlgebra (norm R) :=
  (scalarIsometry R integralZornIsometry).trans (extendedClifford ℤ R)

private theorem zornCliffordComparison_vector (x : ExtendedModule 4 R) :
    zornCliffordComparison R (vectors (integralForm 4) R x) =
      CliffordAlgebra.ι (norm R) (zornVectorComparison R x) := by
  have aux (x : ExtendedModule 4 R) :
      scalarIsometry R integralZornIsometry (vectors (integralForm 4) R x) =
        vectors (norm ℤ) R
          (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl R R)
            integralZornIsometry.toLinearEquiv x) := by
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.congr_tmul,
        LinearMap.baseChange_tmul]
      change r ⊗ₜ[ℤ] CliffordAlgebra.map integralZornIsometry.toIsometry (CliffordAlgebra.ι _ x) = _
      rw [map_apply_ι]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  change extendedClifford ℤ R (scalarIsometry R integralZornIsometry (vectors (integralForm 4) R x)) = _
  rw [aux, extendedClifford_vector]
  rfl

private noncomputable abbrev zornSpinPoint (a : (SplitSpinSpecification.ScalarClifford 4 R)ˣ)
    (ha : a ∈ spinUnits (integralForm 4) R) : spinPoints ℤ R :=
  ⟨Units.map (scalarIsometry R integralZornIsometry).toMonoidHom a,
    scalarIsometry_spin R integralZornIsometry ha⟩

private theorem vectorBlock_scalar (a : (SplitSpinSpecification.ScalarClifford 4 R)ˣ)
    (ha : a ∈ spinUnits (integralForm 4) R) (t : DiagonalPoints R) (c : Rˣ)
    (hscales : ∀ j, scales t j = c) (hc : c ^ 2 = 1)
    (hA : HasActionMatrix 4 a (middle (diagonalBlock t))) (z : Zorn R) :
    (spinRelatedEquiv ℤ R (zornSpinPoint R a ha)).val 1 z = (c : R) • z := by
  obtain ⟨g, hg, hmat⟩ := hA
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hc)
  have hm : middle (diagonalBlock t) = Matrix.diagonal (fun _ => (c : R)) := by
    rw [middle_diagonal]
    congr 1
    funext i
    cases i <;> simp [vectorEigenvalue, hscales, hci]
  have hs (x : ExtendedModule 4 R) : g x = (c : R) • x := by
    apply (splitCoordinates 4 R).injective
    have h := LinearMap.toMatrix_mulVec_repr ((hyperbolicBasis ℤ 4).baseChange R)
      ((hyperbolicBasis ℤ 4).baseChange R) g.toLinearMap x
    change SplitSpinSpecification.vectorMatrix 4 g *ᵥ (splitCoordinates 4 R x : PairIndex 4 → R) =
      splitCoordinates 4 R (g x) at h
    rw [hmat, hm] at h
    rw [map_smul, ← h]
    exact funext (Matrix.mulVec_diagonal _ _)
  obtain ⟨x, rfl⟩ := (zornVectorComparison R).surjective z
  let M := zornCliffordComparison R
  have hw := congrArg M (hg x)
  change M (vectors (integralForm 4) R (g x)) =
    M ((a : SplitSpinSpecification.ScalarClifford 4 R) * vectors (integralForm 4) R x * ↑a⁻¹) at hw
  rw [map_mul, map_mul, zornCliffordComparison_vector, zornCliffordComparison_vector,
    hs, map_smul] at hw
  let q := spinRelatedEquiv ℤ R (zornSpinPoint R a ha)
  have hq := (spinRelated_spec ℤ R (zornSpinPoint R a ha)).2 (zornVectorComparison R x)
  change M (a : SplitSpinSpecification.ScalarClifford 4 R) * CliffordAlgebra.ι (norm R) (zornVectorComparison R x) =
    CliffordAlgebra.ι (norm R) (q.val 1 (zornVectorComparison R x)) * M (a : SplitSpinSpecification.ScalarClifford 4 R) at hq
  rw [hq, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one] at hw
  exact clifford_vector_injective CliffordModel.octonionEquiv CliffordModel.octonionEquiv_ι hw.symm


set_option maxHeartbeats 1300000 in
set_option backward.isDefEq.respectTransparency false in
/-- The integral spin-point presentation identifies the three Peirce blocks
and the ordered Albert frame stabilizer on every field test algebra. -/
theorem splitSpinFramePoints {k : Type u} [Field k] (G : AffineAlgebraicGroup k)
    (e : ∀ R : TestAlgebra k, Points G.val.X R →* (SplitSpinSpecification.ScalarClifford 4 R)ˣ)
    (he : SpinPointPresentation G e) :
    ∃ p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R),
      (∀ {R S : TestAlgebra k} (f : R ⟶ S) (a : Points G.val.X R) (x : Model R),
        mapModel f.hom.toRingHom ((p R a).val x) =
          (p S (mapPoints f a)).val (mapModel f.hom.toRingHom x)) ∧
      ∀ (T : ClosedSubgroup G.val) (d : ∀ R : TestAlgebra k, Points T.group.X R ≃* DiagonalPoints R),
        TorusPointPresentation e T d → CentreCoordinates T d →
        ∀ (R : TestAlgebra k) (g : Points G.val.X R), Centralizes (𝟙 G.val) g →
          ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R g).val x).2 1 = (c : R) • x.2 1 := by
  let D := integralZornIsometry
  let u (R : TestAlgebra k) := Units.map (scalarIsometry R D).toMonoidHom
  let v (R : TestAlgebra k) : Points G.val.X R →* spinPoints ℤ R :=
    ((u R).comp (e R)).codRestrict (spinPoints ℤ R) fun a =>
      scalarIsometry_spin R D ((he.1 R).2 ▸ Set.mem_range_self (f := e R) a)
  have hv (R : TestAlgebra k) : Function.Bijective (v R) := by
    constructor
    · intro a b hab
      apply (he.1 R).1
      apply Units.ext
      apply (scalarIsometry R D).injective
      exact congrArg (fun q : spinPoints ℤ R => q.val.val) hab
    · intro q
      let z := Units.map (scalarIsometry R D.symm).toMonoidHom q.val
      have hz : z ∈ spinUnits (integralForm 4) R :=
        scalarIsometry_spin R D.symm q.property
      rw [← (he.1 R).2] at hz
      obtain ⟨a, ha⟩ := hz
      refine ⟨a, Subtype.ext (Units.ext ?_)⟩
      change scalarIsometry R D (e R a).val = q.val.val
      rw [ha]
      exact (scalarIsometry R D).apply_symm_apply _
  choose ψ hψ using fun R : TestAlgebra k => Triality.frameTriality.{u} R
  let p (R : TestAlgebra k) := (MulEquiv.ofBijective (v R) (hv R)).trans
    ((spinRelatedEquiv ℤ R).trans (ψ R))
  refine ⟨p, ?_, ?_⟩
  · intro R S f a x
    let g := f.hom.restrictScalars ℤ
    let b : spinPoints ℤ S := SpinFunctor.map (norm ℤ) (zornBasis ℤ) g (v R a)
    have hb : v S (mapPoints f a) = b := by
      apply Subtype.ext
      apply Units.ext
      change scalarIsometry S D (e S (mapPoints f a)).val =
        coefficientMap (norm ℤ) R g (scalarIsometry R D (e R a).val)
      rw [he.2 f a]
      exact scalarIsometry_natural R D g (e R a).val
    change mapModel f.hom.toRingHom ((ψ R (spinRelatedEquiv ℤ R (v R a))).val x) =
      (ψ S (spinRelatedEquiv ℤ S (v S (mapPoints f a)))).val (mapModel f.hom.toRingHom x)
    rw [hb, hψ, hψ]
    apply Prod.ext
    · rfl
    · funext i
      exact spinRelated_naturality ℤ g (v R a) i (x.2 i)
  · intro T d hd hZ R g hg
    obtain ⟨Z, j, hZ, hj, w, hw⟩ := hZ
    obtain ⟨z, rfl⟩ := (hZ _ g).mp hg
    let t : Points T.group.X R := z ≫ j.hom.hom
    have ht : t ≫ T.inclusion.hom.hom = z ≫ Z.inclusion.hom.hom := by
      calc
        _ = z ≫ (j ≫ T.inclusion).hom.hom := Category.assoc _ _ _
        _ = _ := by rw [hj]
    let c : Rˣ := (w R z).1.val
    have hc : c ^ 2 = 1 := (mem_rootsOfUnity 2 c).mp (w R z).1.property
    refine ⟨c, hc, fun x => ?_⟩
    have hmat := ((hd.2.2 R).choose_spec.2 t).1
    rw [ht] at hmat
    let g' : Points G.val.X R := z ≫ Z.inclusion.hom.hom
    have hs : e R g' ∈ spinUnits (integralForm 4) R :=
      (he.1 R).2 ▸ Set.mem_range_self (f := e R) g'
    have hsc : ∀ i, scales (d R t) i = c := (hw R z).1
    have hv := vectorBlock_scalar R (e R g') hs (d R t) c hsc hc hmat (x.2 1)
    change ((ψ R (spinRelatedEquiv ℤ R (v R g'))).val x).2 1 = _
    rw [hψ]
    exact hv

end SplitSpinFrames


section SplitReferenceComparison

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.SpinWeights (SpinPointPresentation)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence (relativePoints)
open RelativeFormComparison (fieldTest)
open OctonionEquivariantAutomorphisms (affineTest)
open private exists_relativeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
open private scalarGroupIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
  [Module.Finite k E]

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The split spin scheme and the cubic stabilizer become isomorphic on the
slice over the chosen splitting field, via conjugation on the marked
Albert law. -/
private theorem cubicStabilizerRelativeFrameIso
    {J : AlbertModel k} (B : CubicStabilizer J E) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (C : FrameCharts J B numbering) (cubic : Module.finrank k E = 3)
    (G : AffineAlgebraicGroup k)
    (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
    (hp : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points G.val.X R) (x : Model R),
      mapModel f.hom.toRingHom ((p R a).val x) =
        (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x)) :
    ∃ j : relativePoints G.val (fieldTest k S) ≅
        relativePoints B.stabilizer.group (fieldTest k S),
      ∀ (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R)
        (x : R ⊗[k] J.V),
        (p R b).val (C.chart R f x) =
          C.chart R f (cubicStabilizerAction B R ((j.hom.app (op (affineTest f))).hom b) x) := by
  have h (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) :
      ∃ q : Points B.stabilizer.group.X R ≃* frameStabilizer (R := R),
        ∀ g x, (q g).val (C.chart R f x) = C.chart R f (cubicStabilizerAction B R g x) := by
    let : Algebra S R := f.hom.toRingHom.toAlgebra
    let : IsScalarTower k S R := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
    apply cubicStabilizerPoints_equiv_frameStabilizer B R (C.chart R f) (C.unit R f) (C.op R f)
    exact splitChart_cubicDiagonalRange B R cubic numbering (C.chart R f) (C.diagonal R f)
  choose q hq using h
  let e (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) := (p R).trans (q R f).symm
  have he (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R)
      (b : Points G.val.X R) (x : R ⊗[k] J.V) :
      (p R b).val (C.chart R f x) = C.chart R f (cubicStabilizerAction B R (e R f b) x) := by
    have eq : q R f (e R f b) = p R b := (q R f).apply_symm_apply _
    rw [← eq, hq]
  have hNat {R T : TestAlgebra k} (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T)
      (b : Points G.val.X R) :
      e T (f ≫ g) (mapPoints g b) = mapPoints g (e R f b) := by
    apply cubicStabilizerAction_faithful B T
    apply LinearEquiv.toLinearMap_injective
    apply TensorProduct.AlgebraTensorModule.ext
    intro r w
    apply (C.chart T (f ≫ g)).injective
    change C.chart T (f ≫ g) (cubicStabilizerAction B T (e T (f ≫ g) (mapPoints g b)) (r ⊗ₜ[k] w)) =
      C.chart T (f ≫ g) (cubicStabilizerAction B T (mapPoints g (e R f b)) (r ⊗ₜ[k] w))
    have hx (x : R ⊗[k] J.V) :
        (p T (mapPoints g b)).val (C.chart T (f ≫ g) (TensorProduct.map g.hom.toLinearMap LinearMap.id x)) =
          C.chart T (f ≫ g) (cubicStabilizerAction B T (mapPoints g (e R f b))
            (TensorProduct.map g.hom.toLinearMap LinearMap.id x)) := by
      rw [← C.natural, ← hp, he, C.natural, cubicStabilizerAction_natural]
    have ht := hx ((1 : R) ⊗ₜ[k] w)
    rw [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, map_one] at ht
    rw [← he, show (r ⊗ₜ[k] w : T ⊗[k] J.V) = r • ((1 : T) ⊗ₜ[k] w) by
      rw [smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul, map_smul, map_smul, ht]
  obtain ⟨j, hj⟩ := exists_relativeIso (G := G.val) (H := B.stabilizer.group)
    G.property.1 (stabilizerAffineModel B).property.1 e hNat
  exact ⟨j, fun R f b x => (he R f b x).trans (by rw [hj])⟩


private theorem cubicStabilizerRelativeSpinIso
    {J : AlbertModel k} (B : CubicStabilizer J E) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (C : FrameCharts J B numbering) (cubic : Module.finrank k E = 3)
    (G : AffineAlgebraicGroup k)
    (a : ∀ R : TestAlgebra k, Points G.val.X R →*
      (LinearAlgebraicGroups.Albert.SplitSpinSpecification.ScalarClifford 4 R)ˣ)
    (ha : SpinPointPresentation G a) :
    Nonempty (relativePoints G.val (fieldTest k S) ≅
      relativePoints B.stabilizer.group (fieldTest k S)) := by
  obtain ⟨p, hp, _⟩ := splitSpinFramePoints G a ha
  obtain ⟨j, _⟩ := cubicStabilizerRelativeFrameIso B numbering C cubic G p hp
  exact ⟨j⟩

set_option maxHeartbeats 1900000 in
set_option backward.isDefEq.respectTransparency false in
/-- The reference algebra from the permutation descent has the same
separable-closure stabilizer scheme as the pinned D₄ model. -/
theorem exists_permutationReference_splitIso [IsSepClosure k S]
    (cubic : Module.finrank k E = 3) (G : AffineAlgebraicGroup k)
    (D : DiagramPresentation G E S) :
    ∃ (J : AlbertModel k) (B : CubicStabilizer J E),
      IsPermutationDescent J B D.numbering ∧
      Nonempty (relativePoints D.pinned.pair.G.val (fieldTest k S) ≅
        relativePoints B.stabilizer.group (fieldTest k S)) := by
  obtain ⟨J, B, hp, ⟨C⟩⟩ := exists_permutationReferenceWithCharts D.numbering
  obtain ⟨G₀, a, ha, hG₀, _, _, T, d, _, hT, hmax, _, hc,
    X, Y, A, _, hpairs, hroots, hcoroot⟩ := LinearAlgebraicGroups.Albert.SpinWeights.fieldStructure.{u} k
  let : IsCommMonObj T.group.X := hc
  obtain ⟨f⟩ := spinGroup_iso_of_D4 hG₀ T hT hmax A X Y hpairs hroots.surjOn hcoroot
    D.pinned.pair D.datum D.semisimple D.simplyConnected D.roots D.cartan
  obtain ⟨j⟩ := cubicStabilizerRelativeSpinIso B D.numbering C cubic G₀ a ha
  exact ⟨J, B, hp, ⟨scalarGroupIso f (fieldTest k S) ≪≫ j⟩⟩

end SplitReferenceComparison

section FrameCentreComparison

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct BigOperators
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.FrameSpecification (frameAxis)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open private centralizes_iff comp_conjugateFamily from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes

noncomputable section

private theorem modelMap_ext {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) {a b : Model T ≃ₗ[T] Model T}
    (h : ∀ x : Model R, a (mapModel f x) = b (mapModel f x)) :
    a = b := by
  let : Algebra R T := f.toAlgebra
  let : Module R (Model T) := Module.compHom _ (algebraMap R T)
  let : IsScalarTower R T (Model T) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e := modelBaseChange R T
  have he : a.toLinearMap.comp e.toLinearMap = b.toLinearMap.comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro t x
    change a (modelBaseChange R T (t ⊗ₜ[R] x)) = b (modelBaseChange R T (t ⊗ₜ[R] x))
    rw [modelBaseChange_tmul, map_smul, map_smul]
    exact congrArg (t • ·) (h x)
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he y

section FrameAction

variable {R : Type u} [CommRing R]

private theorem framePermutation_symm (p : Equiv.Perm (Fin 3)) :
    (framePermutation (R := R) p).symm = framePermutation p⁻¹ :=
  (map_inv (framePermutationAction R) p).symm

private theorem framePermutation_conj_mem (p : Equiv.Perm (Fin 3))
    (a : frameStabilizer (R := R)) :
    MulAut.conj (framePermutation p) a.val ∈ frameStabilizer := by
  let f := framePermutation (R := R) p
  change FixesFrame (MulAut.conj f a.val)
  have h : ∀ x, MulAut.conj f a.val (f x) = f (a.val x) := by
    intro x
    change f (a.val (f.symm (f x))) = f (a.val x)
    rw [f.symm_apply_apply]
  have ha : FixesFrame a.val := a.property
  constructor
  · intro i
    obtain ⟨j, rfl⟩ := p.surjective i
    rw [← framePermutation_axis p j, h, ha.1]
  · intro x y
    obtain ⟨x, rfl⟩ := f.surjective x
    obtain ⟨y, rfl⟩ := f.surjective y
    change MulAut.conj f a.val (modelOp (framePermutation p x) (framePermutation p y)) = _
    rw [← framePermutation_operator p, h, ha.2, framePermutation_operator p, h, h]

/-- Permuting the frame acts by conjugation on its pointwise stabilizer. -/
def frameStabilizerPermutation (p : Equiv.Perm (Fin 3)) :
    MulAut (frameStabilizer (R := R)) where
  toFun a := ⟨MulAut.conj (framePermutation p) a.val, framePermutation_conj_mem p a⟩
  invFun a := ⟨MulAut.conj (framePermutation p⁻¹) a.val, framePermutation_conj_mem p⁻¹ a⟩
  left_inv a := by
    apply Subtype.ext
    change MulAut.conj (framePermutation p⁻¹) (MulAut.conj (framePermutation p) a.val) = a.val
    rw [← framePermutation_symm]
    change MulAut.conj (framePermutation (R := R) p)⁻¹ (MulAut.conj (framePermutation p) a.val) = a.val
    simp [MulAut.conj_apply, mul_assoc]
  right_inv a := by
    apply Subtype.ext
    change MulAut.conj (framePermutation p) (MulAut.conj (framePermutation p⁻¹) a.val) = a.val
    rw [← framePermutation_symm]
    change MulAut.conj (framePermutation (R := R) p) (MulAut.conj (framePermutation p)⁻¹ a.val) = a.val
    simp [MulAut.conj_apply, mul_assoc]
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem frameStabilizerPermutation_apply (p : Equiv.Perm (Fin 3))
    (a : frameStabilizer (R := R)) (x : Model R) :
    (frameStabilizerPermutation p a).val (framePermutation p x) =
      framePermutation p (a.val x) :=
  congrArg (fun y => framePermutation p (a.val y)) ((framePermutation p).symm_apply_apply x)

end FrameAction

section Centre

variable {k : Type u} [Field k]

private theorem centralizes_iff_affinePoints (G : AffineAlgebraicGroup k)
    (R : TestAlgebra k) (g : Points G.val.X R) :
    Centralizes (𝟙 G.val) g ↔ ∀ (T : TestAlgebra k) (f : R ⟶ T) (h : Points G.val.X T),
      Commute (mapPoints f g) h := by
  constructor
  · intro hc T f h
    simpa using (centralizes_iff _ _).mp hc _ ((testSpec k).map f.op) h
  · intro h
    let S := (testSpec k).obj (op R)
    have : IsAffine G.val.X.left := G.property.1
    have : IsAffine S.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
    have ha : IsAffine (G.val.X ⊗ S).left := by
      rw [Over.tensorObj_left]
      infer_instance
    unfold Centralizes
    apply hom_ext_of_points ha
    intro T t
    let ff := algSpec.fullyFaithful (R := CommRingCat.of k)
    let f : R ⟶ T := (ff.preimage (t ≫ snd G.val.X S)).unop
    have hf : (testSpec k).map f.op = t ≫ snd G.val.X S := ff.map_preimage _
    have h' := h T f (t ≫ fst G.val.X S)
    change Commute ((testSpec k).map f.op ≫ g) (t ≫ fst G.val.X S) at h'
    rw [hf] at h'
    rw [comp_conjugateFamily]
    have hid : (𝟙 G.val : G.val ⟶ G.val).hom.hom = 𝟙 G.val.X := rfl
    rw [hid, Category.comp_id]
    rw [Category.assoc] at h'
    exact mul_inv_eq_iff_eq_mul.mpr h'.eq

variable (G : AffineAlgebraicGroup k)
  (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
  (hNat : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (a : Points G.val.X R) (x : Model R),
     mapModel f.hom.toRingHom ((p R a).val x) =
       (p S (mapPoints f a)).val (mapModel f.hom.toRingHom x))

private def permuteFramePoint (π : Equiv.Perm (Fin 3)) (R : TestAlgebra k) :
    MulAut (Points G.val.X R) :=
  (p R).trans ((frameStabilizerPermutation π).trans (p R).symm)

private theorem permuteFramePoint_compare (π : Equiv.Perm (Fin 3)) (R : TestAlgebra k)
    (a : Points G.val.X R) :
    p R (permuteFramePoint G p π R a) = frameStabilizerPermutation π (p R a) :=
  (p R).apply_symm_apply _

include hNat in
private theorem permuteFramePoint_natural (π : Equiv.Perm (Fin 3)) {R S : TestAlgebra k}
    (f : R ⟶ S) (a : Points G.val.X R) :
    mapPoints f (permuteFramePoint G p π R a) =
      permuteFramePoint G p π S (mapPoints f a) := by
  apply (p S).injective
  apply Subtype.ext
  apply modelMap_ext f.hom.toRingHom
  intro x
  obtain ⟨x, rfl⟩ := (framePermutation (R := R) π).surjective x
  rw [← hNat, permuteFramePoint_compare, frameStabilizerPermutation_apply,
    framePermutation_natural, framePermutation_natural, hNat, permuteFramePoint_compare,
    frameStabilizerPermutation_apply]

include hNat in
private theorem permuteFramePoint_central (π : Equiv.Perm (Fin 3)) {R : TestAlgebra k}
    {a : Points G.val.X R} (ha : Centralizes (𝟙 G.val) a) :
    Centralizes (𝟙 G.val) (permuteFramePoint G p π R a) := by
  apply (centralizes_iff_affinePoints G R _).mpr
  intro T f h
  obtain ⟨h, rfl⟩ := (permuteFramePoint G p π T).surjective h
  rw [permuteFramePoint_natural G p hNat]
  exact ((centralizes_iff_affinePoints G R a).mp ha T f h).map (permuteFramePoint G p π T)

private theorem frameAction_commute_scalar {R : Type u} [CommRing R]
    {a : frameStabilizer (R := R)} (t : Fin 3 → Rˣ)
    (h : ∀ x : Model R, a.val x = (x.1, fun i => (t i : R) • x.2 i))
    (b : frameStabilizer (R := R)) :
    Commute a b := by
  obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
  obtain ⟨c, rfl⟩ := e.surjective b
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change a.val ((e c).val x) = (e c).val (a.val x)
  rw [h, he, he, h]
  exact Prod.ext rfl (funext fun i => (map_smul (c.val i) _ _).symm)

include hNat in
/-- The centre of the split frame stabilizer is the scalar triples whose squares
and product are one. The comparison uses arbitrary commutative test rings. -/
theorem splitFrameCentreScalars
    (vectorCentre : ∀ (R : TestAlgebra k) (g : Points G.val.X R), Centralizes (𝟙 G.val) g →
      ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R g).val x).2 1 = (c : R) • x.2 1)
    (R : TestAlgebra k) (g : Points G.val.X R) :
    Centralizes (𝟙 G.val) g ↔
      ∃ t : Fin 3 → Rˣ, (∀ i, t i ^ 2 = 1) ∧ (∏ i, t i) = 1 ∧
        ∀ x : Model R, (p R g).val x = (x.1, fun i => (t i : R) • x.2 i) := by
  constructor
  · intro hg
    have h (i : Fin 3) :
        ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R g).val x).2 i = (c : R) • x.2 i := by
      classical
      let π := Equiv.swap i (1 : Fin 3)
      have hi : π i = 1 := Equiv.swap_apply_left _ _
      let z := permuteFramePoint G p π R g
      have hz := permuteFramePoint_central G p hNat π hg
      obtain ⟨c, hc, he⟩ := vectorCentre R z hz
      refine ⟨c, hc, fun x => (blockPermutation π).injective ?_⟩
      have hh := he (framePermutation π x)
      change ((p R (permuteFramePoint G p π R g)).val (framePermutation π x)).2 1 =
        (c : R) • (framePermutation π x).2 1 at hh
      rw [← hi, permuteFramePoint_compare, frameStabilizerPermutation_apply,
        framePermutation_block, framePermutation_block] at hh
      simpa only [map_smul] using hh
    choose t ht ht' using h
    obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
    obtain ⟨q, hq⟩ := e.surjective (p R g)
    have hh (x : Model R) : (p R g).val x = (x.1, fun i => (t i : R) • x.2 i) := by
      apply Prod.ext
      · rw [← hq, he]
      · exact funext fun i => ht' i x
    have hscalar : IsRelated (scalarTriple t) := by
      have hq' : q.val = scalarTriple t := by
        funext i
        apply LinearEquiv.ext
        intro z
        let x : Model R := (0, fun _ => z)
        have hx := congrArg (fun y : Model R => y.2 i) (hh x)
        rw [← hq, he] at hx
        exact hx
      rw [← hq']
      exact q.property
    exact ⟨t, ht, ((isRelated_scalarTriple_iff t).mp hscalar).2, hh⟩
  · rintro ⟨t, ht, hprod, h⟩
    apply (centralizes_iff_affinePoints G R g).mpr
    intro T f b
    let s : Fin 3 → Tˣ := fun i => Units.map f.hom.toRingHom.toMonoidHom (t i)
    have hs : IsRelated (scalarTriple s) := by
      apply (isRelated_scalarTriple_iff s).mpr
      constructor
      · intro i
        change Units.map f.hom.toRingHom.toMonoidHom (t i) ^ 2 = 1
        rw [← map_pow, ht, map_one]
      · change (∏ i, Units.map f.hom.toRingHom.toMonoidHom (t i)) = 1
        rw [← map_prod, hprod, map_one]
    obtain ⟨e, he⟩ := Triality.frameTriality.{u} T
    let a := e ⟨scalarTriple s, hs⟩
    have ha (x : Model T) : a.val x = (x.1, fun i => (s i : T) • x.2 i) := by
      change (e ⟨scalarTriple s, hs⟩).val x = _
      rw [he]
      rfl
    have hab : (p T (mapPoints f g)).val = a.val := by
      apply modelMap_ext f.hom.toRingHom
      intro x
      rw [← hNat, h, ha]
      exact Prod.ext rfl (funext fun i => mapCoordinates_smul _ _ _)
    apply (p T).injective
    simp only [map_mul]
    change Commute (p T (mapPoints f g)) (p T b)
    rw [Subtype.ext hab]
    exact frameAction_commute_scalar s ha (p T b)

end Centre

end

end FrameCentreComparison

section SimilarityTransport

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm mapCoordinates)
open scoped BigOperators
noncomputable section

section CoefficientTransport

variable {R T : Type u} [CommRing R] [CommRing T]

private def zornCoefficientEquiv (f : R ≃+* T) :
    Zorn R ≃+ Zorn T where
  toFun := mapCoordinates f.toRingHom
  invFun := mapCoordinates f.symm.toRingHom
  left_inv x := by
    apply (Zorn.coordinates R).injective
    simp [mapCoordinates, Function.comp_def]
  right_inv x := by
    apply (Zorn.coordinates T).injective
    simp [mapCoordinates, Function.comp_def]
  map_add' := mapCoordinates_add _

private theorem zornCoefficientEquiv_apply (f : R ≃+* T) (x : Zorn R) :
    zornCoefficientEquiv f x = mapCoordinates f.toRingHom x := rfl

private theorem mapCoordinates_blockPermutation (f : R →+* T)
    (p : Equiv.Perm (Fin 3)) (x : Zorn R) :
    mapCoordinates f (blockPermutation p x) = blockPermutation p (mapCoordinates f x) := by
  by_cases hp : Equiv.Perm.sign p = 1
  · simp [blockPermutation, hp]
  · simpa [blockPermutation, hp, zornConjugation_apply] using mapCoordinates_conjugate f x

private def transportZorn (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) :
    Zorn R ≃+ Zorn T :=
  (blockPermutation p).toAddEquiv.trans (zornCoefficientEquiv f)

private theorem transportZorn_apply (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (x : Zorn R) :
    transportZorn f p x = mapCoordinates f.toRingHom (blockPermutation p x) := rfl

private theorem transportZorn_norm (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (x : Zorn R) :
    norm T (transportZorn f p x) = f (norm R x) := by
  rw [transportZorn_apply, Composition.Zorn.mapCoordinates_norm, norm_blockPermutation]
  rfl

private theorem transportZorn_product (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (x y : Zorn R) :
    transportZorn f p (conjugate (norm R) (x * y)) =
      if Equiv.Perm.sign p = 1
      then conjugate (norm T) (transportZorn f p x * transportZorn f p y)
      else conjugate (norm T) (transportZorn f p y * transportZorn f p x) := by
  by_cases hp : Equiv.Perm.sign p = 1
  · simp [transportZorn_apply, blockPermutation, hp, mapCoordinates_conjugate,
      Composition.Zorn.mapCoordinates_mul]
  · simp only [transportZorn_apply, blockPermutation, hp, ite_false, zornConjugation_apply,
      zorn_conj_involutive]
    rw [← Composition.Zorn.mapCoordinates_mul f.toRingHom,
      ← mapCoordinates_conjugate f.toRingHom, ← Composition.conjugate_mul zornNormLaws,
      zorn_conj_involutive]

private theorem transportZorn_smul (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (c : R) (x : Zorn R) :
    transportZorn f p (c • x) = f c • transportZorn f p x := by
  rw [transportZorn_apply, map_smul, mapCoordinates_smul]
  rfl

private def transportZornLinear (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (a : Zorn R ≃ₗ[R] Zorn R) :
    Zorn T ≃ₗ[T] Zorn T where
  toAddEquiv := ((transportZorn f p).symm.trans a.toAddEquiv).trans (transportZorn f p)
  map_smul' c x := by
    obtain ⟨c, rfl⟩ := f.surjective c
    obtain ⟨x, rfl⟩ := (transportZorn f p).surjective x
    change transportZorn f p (a ((transportZorn f p).symm (f c • transportZorn f p x))) =
      f c • transportZorn f p (a ((transportZorn f p).symm (transportZorn f p x)))
    rw [← transportZorn_smul f p c x, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
      map_smul, transportZorn_smul]

private theorem transportZornLinear_apply (f : R ≃+* T) (p : Equiv.Perm (Fin 3))
    (a : Zorn R ≃ₗ[R] Zorn R) (x : Zorn R) :
    transportZornLinear f p a (transportZorn f p x) = transportZorn f p (a x) := by
  change transportZorn f p (a ((transportZorn f p).symm (transportZorn f p x))) = _
  rw [AddEquiv.symm_apply_apply]

/-- Scalar transport acts on the block at the image of its original index. -/
def transportBlockUnits (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) :
    (Fin 3 → Rˣ) →* (Fin 3 → Tˣ) where
  toFun c i := Units.map f.toMonoidHom (c (p.symm i))
  map_one' := by funext i; exact map_one _
  map_mul' x y := by funext i; exact map_mul _ _ _

@[simp] theorem transportBlockUnits_apply (f : R ≃+* T) (p : Equiv.Perm (Fin 3))
    (c : Fin 3 → Rˣ) (i : Fin 3) :
    transportBlockUnits f p c (p i) = Units.map f.toMonoidHom (c i) := by
  change Units.map f.toMonoidHom (c (p.symm (p i))) = _
  rw [p.symm_apply_apply]

/-- The Peirce norm multiplier is permuted with the block. -/
private theorem quotientNormMultiplier_transport (f : R ≃+* T) (p : Equiv.Perm (Fin 3))
    (c : Fin 3 → Rˣ) (i : Fin 3) :
    quotientNormMultiplier (transportBlockUnits f p c) (p i) =
      Units.map f.toMonoidHom (quotientNormMultiplier c i) := by
  rw [quotientNormMultiplier, quotientNormMultiplier, map_inv, map_mul]
  obtain ⟨h₁, h₂⟩ := perm_cyclic p i
  by_cases hp : Equiv.Perm.sign p = 1
  · rw [ite_eq_left hp] at h₁ h₂
    rw [← h₁, ← h₂, transportBlockUnits_apply, transportBlockUnits_apply]
  · rw [ite_eq_right hp] at h₁ h₂
    rw [← h₂, ← h₁, transportBlockUnits_apply, transportBlockUnits_apply, mul_comm]

/-- Simultaneous scalar transport and permutation of the three similarity blocks.
For odd permutations conjugation of the octonions exchanges the product arguments. -/
def transportSimilarities (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) :
    RelatedSimilarities R →* RelatedSimilarities T where
  toFun a := ⟨(fun i => transportZornLinear f p (a.val.1 (p.symm i)),
    transportBlockUnits f p a.val.2), by
    constructor
    · intro j x
      obtain ⟨i, rfl⟩ := p.surjective j
      obtain ⟨z, rfl⟩ := (transportZorn f p).surjective x
      change norm T (transportZornLinear f p (a.val.1 (p.symm (p i))) (transportZorn f p z)) = _
      rw [Equiv.symm_apply_apply, transportZornLinear_apply, transportZorn_norm,
        a.property.1, map_mul, quotientNormMultiplier_transport, transportZorn_norm]
      rfl
    · intro j x y
      obtain ⟨i, rfl⟩ := p.surjective j
      obtain ⟨x, rfl⟩ := (transportZorn f p).surjective x
      obtain ⟨y, rfl⟩ := (transportZorn f p).surjective y
      obtain ⟨hn, hv⟩ := perm_cyclic p i
      change transportZornLinear f p (a.val.1 (p.symm (p i)))
        (conjugate (norm T) (transportZorn f p x * transportZorn f p y)) =
        (transportBlockUnits f p a.val.2 (p i) : T) • conjugate (norm T)
          (transportZornLinear f p (a.val.1 (p.symm (cyclicNext (p i)))) (transportZorn f p x) *
            transportZornLinear f p (a.val.1 (p.symm (cyclicPrev (p i)))) (transportZorn f p y))
      rw [Equiv.symm_apply_apply, transportBlockUnits_apply]
      by_cases he : Equiv.Perm.sign p = 1
      · rw [ite_eq_left he] at hn hv
        have h (v w : Zorn R) := transportZorn_product f p v w
        simp only [ite_eq_left he] at h
        rw [← hn, ← hv, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
          ← h, transportZornLinear_apply, a.property.2, transportZorn_smul,
          transportZornLinear_apply, transportZornLinear_apply, h]
        rfl
      · rw [ite_eq_right he] at hn hv
        have h (v w : Zorn R) := transportZorn_product f p v w
        simp only [ite_eq_right he] at h
        rw [← hv, ← hn, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
          ← h y x, transportZornLinear_apply, a.property.2, transportZorn_smul,
          transportZornLinear_apply, transportZornLinear_apply, h]
        rfl⟩
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply LinearEquiv.ext
      intro x
      obtain ⟨x, rfl⟩ := (transportZorn f p).surjective x
      change transportZornLinear f p 1 (transportZorn f p x) = _
      rw [transportZornLinear_apply]
      rfl
    · exact map_one (transportBlockUnits f p)
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      apply LinearEquiv.ext
      intro x
      obtain ⟨x, rfl⟩ := (transportZorn f p).surjective x
      change transportZornLinear f p (a.val.1 (p.symm i) * b.val.1 (p.symm i))
        (transportZorn f p x) = transportZornLinear f p (a.val.1 (p.symm i))
        (transportZornLinear f p (b.val.1 (p.symm i)) (transportZorn f p x))
      rw [transportZornLinear_apply, transportZornLinear_apply, transportZornLinear_apply]
      rfl
    · exact map_mul (transportBlockUnits f p) _ _

theorem transportSimilarities_action (f : R ≃+* T) (p : Equiv.Perm (Fin 3))
    (a : RelatedSimilarities R) (i : Fin 3) (x : Zorn R) :
    (transportSimilarities f p a).val.1 (p i) (transportZorn f p x) =
      transportZorn f p (a.val.1 i x) := by
  change transportZornLinear f p (a.val.1 (p.symm (p i))) (transportZorn f p x) = _
  rw [p.symm_apply_apply, transportZornLinear_apply]

@[simp] theorem compositionQuotient_transportSimilarities (f : R ≃+* T) (p : Equiv.Perm (Fin 3))
    (a : RelatedSimilarities R) :
    compositionQuotient (transportSimilarities f p a) =
      transportBlockUnits f p (compositionQuotient a) := rfl

private theorem mapCoordinates_comp_hom {U : Type u} [CommRing U]
    (f : R →+* T) (g : T →+* U) (x : Zorn R) :
    mapCoordinates g (mapCoordinates f x) = mapCoordinates (g.comp f) x := by
  apply (Zorn.coordinates U).injective
  rfl

private theorem transportZorn_refl (x : Zorn R) :
    transportZorn (RingEquiv.refl R) 1 x = x := by
  rw [transportZorn_apply]
  have h : blockPermutation (R := R) 1 x = x := by simp [blockPermutation]
  rw [h]
  apply (Zorn.coordinates R).injective
  rfl

private theorem transportZorn_trans {U : Type u} [CommRing U] (f : R ≃+* T) (g : T ≃+* U)
    (p q : Equiv.Perm (Fin 3)) (x : Zorn R) :
    transportZorn (f.trans g) (q * p) x = transportZorn g q (transportZorn f p x) := by
  rw [transportZorn_apply, transportZorn_apply, transportZorn_apply,
    ← mapCoordinates_blockPermutation, ← blockPermutation_mul, mapCoordinates_comp_hom]
  rfl

private theorem transportBlockUnits_refl (c : Fin 3 → Rˣ) :
    transportBlockUnits (RingEquiv.refl R) 1 c = c := by
  funext i
  obtain ⟨i, rfl⟩ := (1 : Equiv.Perm (Fin 3)).surjective i
  rw [transportBlockUnits_apply]
  apply Units.ext
  rfl

private theorem transportBlockUnits_trans {U : Type u} [CommRing U] (f : R ≃+* T) (g : T ≃+* U)
    (p q : Equiv.Perm (Fin 3)) (a : Fin 3 → Rˣ) :
    transportBlockUnits (f.trans g) (q * p) a = transportBlockUnits g q (transportBlockUnits f p a) := by
  funext i
  obtain ⟨i, rfl⟩ := (q * p).surjective i
  rw [transportBlockUnits_apply]
  change Units.map (f.trans g).toMonoidHom (a i) =
    transportBlockUnits g q (transportBlockUnits f p a) (q (p i))
  rw [transportBlockUnits_apply, transportBlockUnits_apply]
  apply Units.ext
  rfl

private theorem transportSimilarities_refl (a : RelatedSimilarities R) :
    transportSimilarities (RingEquiv.refl R) 1 a = a := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply LinearEquiv.ext
    intro x
    have h := transportSimilarities_action (RingEquiv.refl R) 1 a i x
    simpa only [transportZorn_refl, Equiv.Perm.one_apply] using h
  · exact transportBlockUnits_refl _

private theorem transportSimilarities_trans {U : Type u} [CommRing U] (f : R ≃+* T) (g : T ≃+* U)
    (p q : Equiv.Perm (Fin 3)) (a : RelatedSimilarities R) :
    transportSimilarities (f.trans g) (q * p) a =
      transportSimilarities g q (transportSimilarities f p a) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    obtain ⟨i, rfl⟩ := (q * p).surjective i
    apply LinearEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := (transportZorn (f.trans g) (q * p)).surjective x
    change (transportSimilarities (f.trans g) (q * p) a).val.1 ((q * p) i)
        (transportZorn (f.trans g) (q * p) x) =
      (transportSimilarities g q (transportSimilarities f p a)).val.1 (q (p i))
        (transportZorn (f.trans g) (q * p) x)
    rw [transportSimilarities_action, transportZorn_trans, transportZorn_trans,
      transportSimilarities_action, transportSimilarities_action]
  · exact transportBlockUnits_trans f g p q a.val.2

private theorem blockUnits_product_transport (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (c : Fin 3 → Rˣ) :
    (∏ j, transportBlockUnits f p c j) = Units.map f.toMonoidHom (∏ j, c j) := by
  rw [map_prod, ← Equiv.prod_comp p (transportBlockUnits f p c)]
  exact Finset.prod_congr rfl fun i _ => transportBlockUnits_apply f p c i

theorem transportSimilarities_scalar (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (c : Fin 3 → Rˣ) :
    transportSimilarities f p (scalarSimilarity c) = scalarSimilarity (transportBlockUnits f p c) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    obtain ⟨i, rfl⟩ := p.surjective i
    apply LinearEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := (transportZorn f p).surjective x
    rw [transportSimilarities_action]
    change transportZorn f p (scalarTriple c i x) =
      scalarTriple (transportBlockUnits f p c) (p i) (transportZorn f p x)
    rw [scalarTriple_apply, scalarTriple_apply, transportBlockUnits_apply, transportZorn_smul]
    rfl
  · funext i
    obtain ⟨i, rfl⟩ := p.surjective i
    change transportBlockUnits f p (scalarCompositionQuotient c) (p i) =
      scalarCompositionQuotient (transportBlockUnits f p c) (p i)
    rw [transportBlockUnits_apply]
    change Units.map f.toMonoidHom (c i ^ 2 / ∏ j, c j) =
      transportBlockUnits f p c (p i) ^ 2 / ∏ j, transportBlockUnits f p c j
    rw [transportBlockUnits_apply, blockUnits_product_transport, map_div, map_pow]

/-- Coordinatewise quadratic similarity multipliers. -/
def peirceMultiplier : RelatedSimilarities R →* (Fin 3 → Rˣ) where
  toFun a := quotientNormMultiplier a.val.2
  map_one' := by
    funext i
    simp [quotientNormMultiplier]
  map_mul' a b := by
    funext i
    change quotientNormMultiplier (a.val.2 * b.val.2) i =
      quotientNormMultiplier a.val.2 i * quotientNormMultiplier b.val.2 i
    simp only [quotientNormMultiplier, Pi.mul_apply, mul_inv_rev]
    ac_rfl

theorem peirceMultiplier_transport (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (a : RelatedSimilarities R) :
    peirceMultiplier (transportSimilarities f p a) = transportBlockUnits f p (peirceMultiplier a) := by
  funext i
  obtain ⟨i, rfl⟩ := p.surjective i
  rw [transportBlockUnits_apply]
  exact quotientNormMultiplier_transport f p a.val.2 i

theorem peirceMultiplier_scalarSimilarity (t : Fin 3 → Rˣ) :
    peirceMultiplier (scalarSimilarity t) = t ^ 2 := by
  funext i
  exact quotientNormMultiplier_scalar t i

/-- The norm character extends from the scalar torus to the central product. -/
def similarityNorm : RelatedSimilarities R →* Rˣ where
  toFun a := (∏ i, compositionQuotient a i)⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv_rev, mul_comm]

theorem similarityNorm_transport (f : R ≃+* T) (p : Equiv.Perm (Fin 3)) (a : RelatedSimilarities R) :
    similarityNorm (transportSimilarities f p a) = Units.map f.toMonoidHom (similarityNorm a) := by
  change (∏ i, compositionQuotient (transportSimilarities f p a) i)⁻¹ =
    Units.map f.toMonoidHom (∏ i, compositionQuotient a i)⁻¹
  rw [compositionQuotient_transportSimilarities, blockUnits_product_transport, map_inv]

theorem similarityNorm_scalarSimilarity (c : Fin 3 → Rˣ) :
    similarityNorm (scalarSimilarity c) = ∏ i, c i := by
  change (∏ i, c i ^ 2 / ∏ j, c j)⁻¹ = _
  rw [Finset.prod_div_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_fin,
    pow_succ _ 2, div_mul_cancel_left, inv_inv]

end CoefficientTransport

end

end SimilarityTransport

section SimilarityGaloisAction

open LinearAlgebraicGroups.Albert.TrialitySpecification (relatedTriples)
open LinearAlgebraicGroups.Composition (Zorn)
open scoped BigOperators TensorProduct
open _root_.Specs.RM03.CSA (degree isCentralDivision isSplit)

noncomputable section

variable {F L : Type u} [Field F] [Field L] [Algebra F L]

private theorem gal_ringEquiv_mul (g h : Gal(L/F)) :
    (g * h).toRingEquiv = h.toRingEquiv.trans g.toRingEquiv := by
  ext x
  rfl

private theorem gal_ringEquiv_one :
    (1 : Gal(L/F)).toRingEquiv = RingEquiv.refl L := by
  ext x
  rfl

private theorem gal_units_map (g : Gal(L/F)) (a : Lˣ) :
    Units.map g.toRingEquiv.toMonoidHom a = g • a := by
  apply Units.ext
  rfl

variable (π : Gal(L/F) →* Equiv.Perm (Fin 3))

/-- The numbered Peirce blocks are permuted by their given diagram action. -/
private abbrev peirceIndexAction : MulAction Gal(L/F) (Fin 3) :=
  MulAction.compHom (Fin 3) π

/-- The coefficient action on the units of the split cubic algebra. -/
def blockUnitsAction : Gal(L/F) →* MulAut (Fin 3 → Lˣ) := by
  let f (g : Gal(L/F)) := transportBlockUnits g.toRingEquiv (π g)
  have hOne (a : Fin 3 → Lˣ) : f 1 a = a := by
    simp only [f, gal_ringEquiv_one, map_one, transportBlockUnits_refl]
  have hMul (g h : Gal(L/F)) (a : Fin 3 → Lˣ) : f (g * h) a = f g (f h a) := by
    change transportBlockUnits (g * h).toRingEquiv (π (g * h)) a =
      transportBlockUnits g.toRingEquiv (π g) (transportBlockUnits h.toRingEquiv (π h) a)
    rw [gal_ringEquiv_mul, map_mul, transportBlockUnits_trans]
  let e (g : Gal(L/F)) : MulAut (Fin 3 → Lˣ) := MulEquiv.ofBijective (f g)
    ⟨fun a b h => by
        have hh := congrArg (f g⁻¹) h
        rwa [← hMul, ← hMul, inv_mul_cancel, hOne, hOne] at hh,
      fun a => ⟨f g⁻¹ a, by rw [← hMul, mul_inv_cancel, hOne]⟩⟩
  exact
    { toFun := e
      map_one' := MulEquiv.ext hOne
      map_mul' := fun g h => MulEquiv.ext (hMul g h) }

theorem blockUnitsAction_apply (g : Gal(L/F)) (c : Fin 3 → Lˣ) (i : Fin 3) :
    blockUnitsAction π g c (π g i) = g • c i :=
  (transportBlockUnits_apply g.toRingEquiv (π g) c i).trans (gal_units_map g (c i))

/-- The descended coefficient action is the product of scalar transport and
the indicated simultaneous block permutation. -/
def relatedSimilarityAction : Gal(L/F) →* MulAut (RelatedSimilarities L) := by
  let f (g : Gal(L/F)) := transportSimilarities g.toRingEquiv (π g)
  have hOne (a : RelatedSimilarities L) : f 1 a = a := by
    simp only [f, gal_ringEquiv_one, map_one, transportSimilarities_refl]
  have hMul (g h : Gal(L/F)) (a : RelatedSimilarities L) : f (g * h) a = f g (f h a) := by
    change transportSimilarities (g * h).toRingEquiv (π (g * h)) a =
      transportSimilarities g.toRingEquiv (π g) (transportSimilarities h.toRingEquiv (π h) a)
    rw [gal_ringEquiv_mul, map_mul, transportSimilarities_trans]
  let e (g : Gal(L/F)) : MulAut (RelatedSimilarities L) := MulEquiv.ofBijective (f g)
    ⟨fun a b h => by
        have hh := congrArg (f g⁻¹) h
        rwa [← hMul, ← hMul, inv_mul_cancel, hOne, hOne] at hh,
      fun a => ⟨f g⁻¹ a, by rw [← hMul, mul_inv_cancel, hOne]⟩⟩
  exact
    { toFun := e
      map_one' := MulEquiv.ext hOne
      map_mul' := fun g h => MulEquiv.ext (hMul g h) }

theorem compositionQuotient_equivariant (g : Gal(L/F)) (a : RelatedSimilarities L) :
    compositionQuotient (relatedSimilarityAction π g a) =
      blockUnitsAction π g (compositionQuotient a) := rfl

theorem relatedSimilarityAction_scalar (g : Gal(L/F)) (c : Fin 3 → Lˣ) :
    relatedSimilarityAction π g (scalarSimilarity c) =
      scalarSimilarity (blockUnitsAction π g c) :=
  transportSimilarities_scalar g.toRingEquiv (π g) c

private theorem peirceMultiplier_equivariant (g : Gal(L/F)) (a : RelatedSimilarities L) :
    peirceMultiplier (relatedSimilarityAction π g a) = blockUnitsAction π g (peirceMultiplier a) :=
  peirceMultiplier_transport g.toRingEquiv (π g) a

private theorem similarityNorm_equivariant (g : Gal(L/F)) (a : RelatedSimilarities L) :
    similarityNorm (relatedSimilarityAction π g a) = g • similarityNorm a :=
  (similarityNorm_transport g.toRingEquiv (π g) a).trans (gal_units_map g (similarityNorm a))

private theorem relatedSimilarityAction_preserves (g : Gal(L/F)) (a : relatedTriples (R := L)) :
    relatedSimilarityAction π g (relatedTripleInclusion a) ∈ (relatedTripleInclusion (R := L)).range := by
  apply (compositionQuotient_kernel _).mp
  rw [compositionQuotient_equivariant, (compositionQuotient_kernel (relatedTripleInclusion a)).mpr ⟨a, rfl⟩,
    map_one]

/-- The linear group of the three octonion blocks contains the invariant kernel
of the composition quotient. -/
def relatedTripleAction : Gal(L/F) →* MulAut (relatedTriples (R := L)) := by
  let ρ := relatedSimilarityAction π
  let j := relatedTripleInclusion (R := L)
  let f (g : Gal(L/F)) (a : relatedTriples (R := L)) := (relatedSimilarityAction_preserves π g a).choose
  have hf (g : Gal(L/F)) (a : relatedTriples (R := L)) : j (f g a) = ρ g (j a) := (relatedSimilarityAction_preserves π g a).choose_spec
  have hi := relatedTripleInclusion_injective (R := L)
  have hOne a : f 1 a = a := by
    apply hi
    change j (f 1 a) = j a
    rw [hf, map_one]
    rfl
  have hMul g h a : f (g * h) a = f g (f h a) := by
    apply hi
    rw [hf, hf, hf, map_mul, MulAut.mul_apply]
  let e (g : Gal(L/F)) : MulAut (relatedTriples (R := L)) :=
    { toFun := f g
      invFun := f g⁻¹
      left_inv := fun a => by rw [← hMul, inv_mul_cancel, hOne]
      right_inv := fun a => by rw [← hMul, mul_inv_cancel, hOne]
      map_mul' := fun a b => hi (by
        change j (f g (a * b)) = j (f g a * f g b)
        rw [hf, map_mul j, map_mul (ρ g), map_mul j, hf, hf]) }
  exact { toFun := e, map_one' := MulEquiv.ext hOne, map_mul' := fun g h => MulEquiv.ext (hMul g h) }

theorem relatedTripleInclusion_equivariant (g : Gal(L/F)) (a : relatedTriples (R := L)) :
    relatedTripleInclusion (relatedTripleAction π g a) =
      relatedSimilarityAction π g (relatedTripleInclusion a) :=
  (relatedSimilarityAction_preserves π g a).choose_spec

section LocalField

variable {E B Q : Type u} [Field E] [Algebra F E] [Algebra E L] [IsScalarTower F E L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F E] [FiniteDimensional F L] [IsGalois F L] [IsGalois E L]
  [DivisionRing B] [Algebra F B] [Group Q]

attribute [local instance] galAdditiveUnits

set_option maxHeartbeats 1300000 in
/-- A cubic permutation descent of the split related-similarity group lifts an
adjoint cocycle to a related-triple cocycle up to adjoint coboundary, once
given the equivariant central projection and lifts at this finite layer. -/
theorem localRelatedSimilarityLift (cubic : Module.finrank F E = 3)
    (hB : isCentralDivision F B) (dB : degree F B = 2) (splitB : isSplit L (L ⊗[F] B))
    (τ : Gal(L/F) →* MulAut Q) (p : RelatedSimilarities L →* Q)
    (pEquiv : ∀ g x, p (relatedSimilarityAction π g x) = τ g (p x))
    (pKernel : ∀ x, p x = 1 ↔ x ∈ (scalarSimilarity (R := L)).range)
    (a : Gal(L/F) → Q) (ha : ∀ g h, a (g * h) = a g * τ g (a h))
    (l : Gal(L/F) → RelatedSimilarities L) (hl : ∀ g, p (l g) = a g) :
    letI := peirceIndexAction π
    ∀ (o : Fin 3) (_transitive : ∀ i, ∃ r : Gal(L/F), r • o = i)
      (φ : Gal(L/E) ≃* MulAction.stabilizer (Gal(L/F)) o),
      (∀ g, (φ g : Gal(L/F)) = g.restrictScalars F) →
      ∃ (b : RelatedSimilarities L) (c : Gal(L/F) → relatedTriples (R := L)),
        (∀ g h, c (g * h) = c g * relatedTripleAction π g (c h)) ∧
        ∀ g, p (relatedTripleInclusion (c g)) = (p b)⁻¹ * a g * τ g (p b) := by
  let := peirceIndexAction π
  intro o transitive φ hφ
  let ρ := relatedSimilarityAction π
  let σ := blockUnitsAction π
  let j := scalarSimilarity (R := L)
  obtain ⟨d, hdef, hassoc⟩ := existsCentralLiftDefect ρ σ τ j p scalarSimilarity_central
    scalarSimilarity_injective pKernel (relatedSimilarityAction_scalar π) pEquiv a ha l hl
  let D (g h : Gal(L/F)) (i : Fin 3) := Additive.ofMul (d g h ((g * h) • i))
  have hs (g : Gal(L/F)) (x : Fin 3 → Lˣ) (i : Fin 3) : σ g x (g • i) = g • x i :=
    blockUnitsAction_apply π g x i
  have assoc (g h k : Gal(L/F)) (i : Fin 3) :
      D g h (k • i) + D (g * h) k i = g • D h k i + D g (h * k) i := by
    have hh := congrFun (hassoc g h k) (g • ((h * k) • i))
    simp only [Pi.mul_apply, hs] at hh
    have he := congrArg Additive.ofMul hh
    change D g h (k • i) + D (g * h) k i =
      Additive.ofMul (g • d h k ((h * k) • i)) + D g (h * k) i
    simpa only [D, ofMul_mul, mul_smul, mul_assoc] using he
  let m (g : MulAction.stabilizer (Gal(L/F)) o) := Additive.ofMul (peirceMultiplier (l g) o)
  have twice (g h : MulAction.stabilizer (Gal(L/F)) o) :
      D g h o + D g h o = m g + (g : Gal(L/F)) • m h - m (g * h) := by
    have hg : (g : Gal(L/F)) • o = o := g.property
    have hj : (h : Gal(L/F)) • o = o := h.property
    have he := congrArg peirceMultiplier (hdef g h)
    rw [map_mul, map_mul, peirceMultiplier_equivariant, peirceMultiplier_scalarSimilarity] at he
    have hh := congrFun he o
    simp only [Pi.mul_apply, Pi.pow_apply] at hh
    have he' : blockUnitsAction π g (peirceMultiplier (l h)) o =
        (g : Gal(L/F)) • peirceMultiplier (l h) o := by
      exact congrArg (blockUnitsAction π g (peirceMultiplier (l h))) hg.symm |>.trans (hs _ _ _)
    rw [he', pow_two] at hh
    have hz := congrArg Additive.ofMul hh
    simp only [D, mul_smul, hj, hg]
    rw [eq_sub_iff_add_eq]
    exact hz.symm
  let n (g : Gal(L/F)) := Additive.ofMul (similarityNorm (l g))
  have norm (g h : Gal(L/F)) :
      ∑ i, D g h i = n g + g • n h - n (g * h) := by
    have he := congrArg similarityNorm (hdef g h)
    rw [map_mul, map_mul, similarityNorm_equivariant, similarityNorm_scalarSimilarity] at he
    have hh := congrArg Additive.ofMul he
    have hp : (∏ i, d g h ((g * h) • i)) = ∏ i, d g h i :=
      Equiv.prod_comp (π (g * h)) (d g h)
    rw [show ∑ i, D g h i = Additive.ofMul (∏ i, d g h i) by
      rw [← hp]
      exact (ofMul_prod _ _).symm]
    rw [eq_sub_iff_add_eq]
    exact hh.symm
  obtain ⟨v, hv⟩ := localInducedDefect_isCoboundary (F := F) (E := E) (L := L) (I := Fin 3)
    cubic hB dB splitB (Fintype.card_fin 3) o transitive φ hφ D assoc m twice n (fun g h => by
      exact norm g h)
  let v' (g : Gal(L/F)) (i : Fin 3) := (v g (π g |>.symm i)).toMul
  have dv (g h : Gal(L/F)) : d g h = v' g * σ g (v' h) / v' (g * h) := by
    funext i
    obtain ⟨i, rfl⟩ := (π (g * h)).surjective i
    have ha := congrArg Additive.toMul (hv g h i)
    have hIdx : π (g * h) i = π g (π h i) := by rw [map_mul]; rfl
    rw [Pi.div_apply, Pi.mul_apply]
    rw [show v' (g * h) (π (g * h) i) = (v (g * h) i).toMul from
      congrArg (fun j => (v (g * h) j).toMul) ((π (g * h)).symm_apply_apply i)]
    rw [show σ g (v' h) (π (g * h) i) = g • v' h (π h i) by rw [hIdx]; exact hs _ _ _]
    rw [show v' g (π (g * h) i) = (v g (π h i)).toMul by rw [hIdx]; simp [v'],
      show v' h (π h i) = (v h i).toMul by simp [v']]
    exact ha
  have ker (x : Fin 3 → Lˣ) : p (j x) = 1 := (pKernel _).mpr ⟨x, rfl⟩
  obtain ⟨l', hl', hc⟩ := adjustCentralLifts ρ σ j p scalarSimilarity_central ker
    (relatedSimilarityAction_scalar π) a l hl v' fun g h => by rw [← dv, hdef]
  let f (g : Gal(L/F)) (i : Fin 3) := compositionQuotient (l' g) (g • i)
  have hf (g h : Gal(L/F)) (i : Fin 3) : f (g * h) i = f g (h • i) * g • f h i := by
    change compositionQuotient (l' (g * h)) ((g * h) • i) =
      compositionQuotient (l' g) (g • (h • i)) * g • compositionQuotient (l' h) (h • i)
    rw [hc, map_mul, Pi.mul_apply, compositionQuotient_equivariant, mul_smul, hs]
  let : FiniteDimensional E L := Module.Finite.of_restrictScalars_finite F E L
  obtain ⟨z, hz⟩ := inducedUnitCocycle_isCoboundary o transitive φ hφ f hf
  obtain ⟨b, hb⟩ := compositionQuotient_surjective z
  have hb' (g : Gal(L/F)) : compositionQuotient (l' g) =
      compositionQuotient b / σ g (compositionQuotient b) := by
    funext i
    obtain ⟨i, rfl⟩ := (π g).surjective i
    rw [Pi.div_apply, hb]
    change f g i = z (g • i) / σ g z (g • i)
    rw [hs]
    exact hz g i
  obtain ⟨c, hC, hCocycle⟩ := adjustQuotientCocycle ρ (relatedTripleAction π) σ
    compositionQuotient relatedTripleInclusion (compositionQuotient_equivariant π)
    compositionQuotient_kernel relatedTripleInclusion_injective
    (fun g a => (relatedTripleInclusion_equivariant π g a).symm)
    l' hc b hb'
  refine ⟨b, c, hCocycle, fun g => ?_⟩
  rw [hC, map_mul, map_mul, map_inv, pEquiv, hl']

end LocalField

end

end SimilarityGaloisAction

section ProjectiveDescent

open scoped TensorProduct Matrix
open Matrix Algebra.TensorProduct
noncomputable section

/-- Matrix representatives descend through a field extension when the two
base changes have the same projective class over its tensor square. -/
theorem matrixRepresentative_descends
    {K T ι : Type u} [Field K] [Field T] [Algebra K T]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : (Matrix ι ι T)ˣ)
    (h : ∃ t : (T ⊗[K] T)ˣ,
      A.val.map (includeLeftRingHom : T →+* T ⊗[K] T) =
        (t : T ⊗[K] T) • A.val.map (includeRight.toRingHom : T →+* T ⊗[K] T)) :
    ∃ (B : (Matrix ι ι K)ˣ) (c : Tˣ), A.val = (c : T) • B.val.map (algebraMap K T) := by
  obtain ⟨t, ht⟩ := h
  classical
  have hA : ∃ i j, A.val i j ≠ 0 := by
    by_contra! hA
    apply Units.ne_zero A
    ext i j
    exact hA i j
  obtain ⟨i₀, j₀, h₀⟩ := hA
  let c := Units.mk0 (A.val i₀ j₀) h₀
  let l : T →+* T ⊗[K] T := includeLeftRingHom
  let r : T →+* T ⊗[K] T := includeRight.toRingHom
  have hc : Units.map l.toMonoidHom c = t * Units.map r.toMonoidHom c := by
    apply Units.ext
    exact congrFun (congrFun ht i₀) j₀
  have effective := Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (Algebra.IsEffective.of_faithfullyFlat K T)
  have hentry (i j : ι) : ∃ b : K, algebraMap K T b = (↑c⁻¹ : T) * A.val i j := by
    apply Set.mem_range.mp
    rw [← effective]
    change l ((↑c⁻¹ : T) * A.val i j) = r ((↑c⁻¹ : T) * A.val i j)
    rw [map_mul, map_mul]
    change ((Units.map l.toMonoidHom c⁻¹ : (T ⊗[K] T)ˣ) : T ⊗[K] T) * l (A.val i j) =
      ((Units.map r.toMonoidHom c⁻¹ : (T ⊗[K] T)ˣ) : T ⊗[K] T) * r (A.val i j)
    have hij : l (A.val i j) = (t : T ⊗[K] T) * r (A.val i j) :=
      congrFun (congrFun ht i) j
    rw [hij, map_inv, map_inv, hc, _root_.mul_inv_rev, Units.val_mul, mul_assoc, ← mul_assoc (↑t⁻¹ : T ⊗[K] T),
      Units.inv_mul, one_mul]
  choose b hb using hentry
  let M : Matrix ι ι K := of b
  have hM : M.map (algebraMap K T) = (↑c⁻¹ : T) • A.val := by
    ext i j
    exact hb i j
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he := congrArg Matrix.det hM
    change ((algebraMap K T).mapMatrix M).det = _ at he
    rw [← RingHom.map_det, hz, map_zero, det_smul] at he
    have hd : A.val.det ≠ 0 := isUnit_iff_ne_zero.mp (A.val.isUnit_iff_isUnit_det.mp A.isUnit)
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hd he.symm
  obtain ⟨B, hB⟩ := M.isUnit_iff_isUnit_det.mpr hdet
  refine ⟨B, c, ?_⟩
  rw [hB, hM, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end

end ProjectiveDescent

section SimilarityBaseChange

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Composition.ZornSpecification (norm mapCoordinates)
open scoped TensorProduct
noncomputable section

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

variable {R T : Type u} [CommRing R] [CommRing T]

private def zornLinearBaseChange (f : R →+* T) :
    (Zorn R ≃ₗ[R] Zorn R) →* (Zorn T ≃ₗ[T] Zorn T) := by
  let : Algebra R T := f.toAlgebra
  let e := Composition.Zorn.baseChange R T
  exact
    { toFun := fun a => e.symm.trans ((a.baseChange R T _ _).trans e)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        change e ((1 : Zorn R ≃ₗ[R] Zorn R).baseChange R T _ _ (e.symm x)) = x
        rw [LinearEquiv.baseChange_one]
        exact e.apply_symm_apply x
      map_mul' := fun a b => by
        apply LinearEquiv.ext
        intro x
        change e ((a * b).baseChange R T _ _ (e.symm x)) =
          e (a.baseChange R T _ _ (e.symm (e (b.baseChange R T _ _ (e.symm x)))))
        rw [LinearEquiv.baseChange_mul, e.symm_apply_apply]
        rfl }

private theorem zornLinearBaseChange_apply (f : R →+* T) (a : Zorn R ≃ₗ[R] Zorn R) (x : Zorn R) :
    zornLinearBaseChange f a (mapCoordinates f x) = mapCoordinates f (a x) := by
  let : Algebra R T := f.toAlgebra
  let e := Composition.Zorn.baseChange R T
  have h (v : Zorn R) : e ((1 : T) ⊗ₜ[R] v) = mapCoordinates f v := by
    rw [Composition.Zorn.baseChange_tmul, one_smul]
    rfl
  rw [← h x, ← h (a x)]
  change e (a.baseChange R T _ _ (e.symm (e ((1 : T) ⊗ₜ[R] x)))) = _
  rw [e.symm_apply_apply, LinearEquiv.baseChange_tmul]

private theorem zornLinearBaseChange_norm
    (f : R →+* T) (a : Zorn R ≃ₗ[R] Zorn R) (c : R)
    (h : ∀ x, norm R (a x) = c * norm R x) :
    ∀ x, norm T (zornLinearBaseChange f a x) = f c * norm T x := by
  let : Algebra R T := f.toAlgebra
  let e := Composition.Zorn.baseChange R T
  have he : (norm T).comp ((zornLinearBaseChange f a).toLinearMap.comp e.toLinearMap) =
      f c • (norm T).comp e.toLinearMap := by
    apply baseChange_ext
    intro v
    change norm T (zornLinearBaseChange f a (e (1 ⊗ₜ[R] v))) = f c * norm T (e (1 ⊗ₜ[R] v))
    have h₀ : e ((1 : T) ⊗ₜ[R] v) = mapCoordinates f v := by
      rw [Composition.Zorn.baseChange_tmul, one_smul]
      rfl
    rw [h₀, zornLinearBaseChange_apply, Composition.Zorn.mapCoordinates_norm,
      Composition.Zorn.mapCoordinates_norm, h, map_mul]
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  exact congrArg (fun q : QuadraticForm T (T ⊗[R] Zorn R) => q x) he

private theorem zornLinearBaseChange_product
    (f : R →+* T) (a b c : Zorn R ≃ₗ[R] Zorn R) (r : R)
    (h : ∀ x y, a (conjugate (norm R) (x * y)) = r • conjugate (norm R) (b x * c y)) :
    ∀ x y, zornLinearBaseChange f a (conjugate (norm T) (x * y)) =
      f r • conjugate (norm T) (zornLinearBaseChange f b x * zornLinearBaseChange f c y) := by
  let : Algebra R T := f.toAlgebra
  let e := Composition.Zorn.baseChange R T
  intro x y
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  induction x using TensorProduct.inductionOn with
  | tmul t x =>
    induction y using TensorProduct.inductionOn with
    | tmul u y =>
      have h₀ (v : Zorn R) (z : T) : e (z ⊗ₜ[R] v) = z • mapCoordinates f v :=
        Composition.Zorn.baseChange_tmul z v
      rw [h₀, h₀]
      simp only [map_smul, smul_mul_assoc, mul_smul_comm, zornLinearBaseChange_apply,
        ← Composition.Zorn.mapCoordinates_mul, ← mapCoordinates_conjugate, h, mapCoordinates_smul]
      simp only [smul_smul]
      congr 1
      ac_rfl
    | add x₁ x₂ h₁ h₂ =>
      simp only [map_add, mul_add, smul_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add, add_mul, smul_add, h₁, h₂]

/-- Related similarity triples extend to every coefficient algebra. -/
def relatedSimilarityBaseChange (f : R →+* T) : RelatedSimilarities R →* RelatedSimilarities T where
  toFun a := ⟨(fun i => zornLinearBaseChange f (a.val.1 i),
    fun i => Units.map f.toMonoidHom (a.val.2 i)), by
    constructor
    · intro i x
      have he : quotientNormMultiplier (fun j => Units.map f.toMonoidHom (a.val.2 j)) i =
          Units.map f.toMonoidHom (quotientNormMultiplier a.val.2 i) := by
        unfold quotientNormMultiplier
        rw [map_inv, map_mul]
      simp only [he]
      exact zornLinearBaseChange_norm f _ _ (a.property.1 i) x
    · intro i x y
      exact zornLinearBaseChange_product f _ _ _ _ (a.property.2 i) x y⟩
  map_one' := by
    apply Subtype.ext
    exact Prod.ext (funext fun _ => map_one _) (funext fun _ => map_one _)
  map_mul' a b := by
    apply Subtype.ext
    exact Prod.ext (funext fun _ => map_mul _ _ _) (funext fun _ => map_mul _ _ _)

/-- The block actions after extending coefficients agree on the embedded vectors. -/
theorem relatedSimilarityBaseChange_apply (f : R →+* T) (a : RelatedSimilarities R) (i : Fin 3) (x : Zorn R) :
    (relatedSimilarityBaseChange f a).val.1 i (mapCoordinates f x) =
      mapCoordinates f (a.val.1 i x) :=
  zornLinearBaseChange_apply f _ x

private theorem zornMap_ext (f : R →+* T) {a b : Zorn T ≃ₗ[T] Zorn T}
    (h : ∀ x : Zorn R, a (mapCoordinates f x) = b (mapCoordinates f x)) : a = b := by
  let : Algebra R T := f.toAlgebra
  let : Module R (Zorn T) := Module.compHom _ (algebraMap R T)
  let : IsScalarTower R T (Zorn T) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e := Composition.Zorn.baseChange R T
  have he : a.toLinearMap.comp e.toLinearMap = b.toLinearMap.comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro t x
    change a (e (t ⊗ₜ[R] x)) = b (e (t ⊗ₜ[R] x))
    rw [Composition.Zorn.baseChange_tmul, map_smul, map_smul]
    exact congrArg (t • ·) (h x)
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact DFunLike.congr_fun he y

private theorem relatedSimilarityBaseChange_comp {A : Type u} [CommRing A]
    (f : R →+* T) (g : T →+* A) (a : RelatedSimilarities R) :
    relatedSimilarityBaseChange g (relatedSimilarityBaseChange f a) = relatedSimilarityBaseChange (g.comp f) a := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply zornMap_ext (g.comp f)
    intro x
    rw [← mapCoordinates_comp_hom f g, relatedSimilarityBaseChange_apply,
      relatedSimilarityBaseChange_apply, mapCoordinates_comp_hom, mapCoordinates_comp_hom,
      relatedSimilarityBaseChange_apply]
  · funext i
    apply Units.ext
    rfl

section CentralProduct

open scoped BigOperators

/-- Multiplication of the triality subgroup and the scalar torus in the group
of related similarities. -/
def relatedCentralProductMap : (relatedTriples (R := R) × (Fin 3 → Rˣ)) →* RelatedSimilarities R where
  toFun p := scalarSimilarity p.2 * relatedTripleInclusion p.1
  map_one' := by rw [show (1 : relatedTriples (R := R) × (Fin 3 → Rˣ)).1 = 1 from rfl,
    show (1 : relatedTriples (R := R) × (Fin 3 → Rˣ)).2 = 1 from rfl, map_one, map_one, mul_one]
  map_mul' x y := by
    change scalarSimilarity (x.2 * y.2) * relatedTripleInclusion (x.1 * y.1) =
      (scalarSimilarity x.2 * relatedTripleInclusion x.1) *
        (scalarSimilarity y.2 * relatedTripleInclusion y.1)
    rw [map_mul, map_mul, mul_assoc, mul_assoc, ← mul_assoc (scalarSimilarity y.2),
      (scalarSimilarity_central y.2 (relatedTripleInclusion x.1)).eq, mul_assoc]

private theorem scalarCompositionQuotient_kernel_iff (t : Fin 3 → Rˣ) :
    scalarCompositionQuotient t = 1 ↔ (∀ i, t i ^ 2 = 1) ∧ (∏ i, t i) = 1 := by
  constructor
  · intro ht
    have hn := similarityNorm_scalarSimilarity t
    change (∏ i, scalarCompositionQuotient t i)⁻¹ = ∏ i, t i at hn
    rw [ht] at hn
    simp only [Pi.one_apply, Finset.prod_const_one, inv_one] at hn
    refine ⟨fun i => ?_, hn.symm⟩
    have hh := congrFun ht i
    change t i ^ 2 / (∏ j, t j) = 1 at hh
    rwa [← hn, div_one] at hh
  · rintro ⟨h, hn⟩
    funext i
    change t i ^ 2 / (∏ j, t j) = 1
    rw [h, hn, div_one]

/-- The kernel of multiplication is the anti-diagonal copy of the centre.
The equations are imposed on the full coefficient ring. -/
theorem relatedCentralProductMap_kernel (a : relatedTriples (R := R)) (t : Fin 3 → Rˣ) :
    relatedCentralProductMap (a, t) = 1 ↔
      a.val = scalarTriple t⁻¹ ∧ (∀ i, t i ^ 2 = 1) ∧ (∏ i, t i) = 1 := by
  constructor
  · intro h
    have he : relatedTripleInclusion a = scalarSimilarity t⁻¹ := by
      change scalarSimilarity t * relatedTripleInclusion a = 1 at h
      rw [map_inv]
      exact eq_inv_of_mul_eq_one_right h
    have hf := congrArg compositionQuotient he
    change (1 : Fin 3 → Rˣ) = scalarCompositionQuotient t⁻¹ at hf
    rw [map_inv, eq_comm, inv_eq_one] at hf
    exact ⟨congrArg (fun z : RelatedSimilarities R => z.val.1) he,
      (scalarCompositionQuotient_kernel_iff t).mp hf⟩
  · rintro ⟨ha, ht, hn⟩
    have hx : relatedTripleInclusion a = scalarSimilarity t⁻¹ := by
      apply Subtype.ext
      apply Prod.ext
      · exact ha
      · change 1 = scalarCompositionQuotient t⁻¹
        rw [map_inv, (scalarCompositionQuotient_kernel_iff t).mpr ⟨ht, hn⟩, inv_one]
    change scalarSimilarity t * relatedTripleInclusion a = 1
    rw [hx, map_inv, mul_inv_cancel]

/-- Every related similarity is locally a scalar times a related triple.
The quadratic adjunction provides the faithfully flat coefficient cover. -/
theorem relatedCentralProduct_lift (a : RelatedSimilarities R) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Module.FaithfullyFlat R T ∧
        ∃ (b : relatedTriples (R := T)) (t : Fin 3 → Tˣ),
          relatedSimilarityBaseChange (algebraMap R T) a = relatedCentralProductMap (b, t) := by
  obtain ⟨T, _, _, hT, t, ht⟩ := cubicQuotient_lifts_afterFaithfullyFlat R (compositionQuotient a)
  let x := relatedSimilarityBaseChange (algebraMap R T) a
  have he : compositionQuotient (scalarSimilarity t) = compositionQuotient x := funext ht
  have hc : compositionQuotient ((scalarSimilarity t)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, he, inv_mul_cancel]
  obtain ⟨b, hb⟩ := (compositionQuotient_kernel _).mp hc
  refine ⟨T, inferInstance, inferInstance, hT, b, t, ?_⟩
  change x = scalarSimilarity t * relatedTripleInclusion b
  rw [hb, mul_inv_cancel_left]

end CentralProduct

end

end SimilarityBaseChange

section CubicGalois

noncomputable section

variable {F E L : Type u} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra F L]

/-- The three embeddings into the splitting layer are a transitive permutation
set, with the stabilizer of an embedding the Galois group over its image. -/
theorem cubicEmbeddingStabilizer [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional F L] [IsGalois F L] [Algebra E L] [IsScalarTower F E L]
    (num : (E →ₐ[F] L) ≃ Fin 3) (o : Fin 3)
    (hE : IsScalarTower.toAlgHom F E L = num.symm o) :
    letI := MulAction.compHom (Fin 3) (diagramPermutation num)
    (∀ i, ∃ r : Gal(L/F), r • o = i) ∧
      ∃ φ : Gal(L/E) ≃* MulAction.stabilizer (Gal(L/F)) o,
        ∀ g, (φ g : Gal(L/F)) = g.restrictScalars F := by
  let := MulAction.compHom (Fin 3) (diagramPermutation num)
  have action (g : Gal(L/F)) (i : Fin 3) : g • i = num (g.toAlgHom.comp (num.symm i)) := rfl
  have fix_iff (g : Gal(L/F)) : g • o = o ↔ ∀ e : E, g (algebraMap E L e) = algebraMap E L e := by
    rw [action, ← Equiv.eq_symm_apply]
    rw [← hE, AlgHom.ext_iff]
    rfl
  constructor
  · intro i
    obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
    let e₀ := num.symm o
    let eᵢ := num.symm i
    have hr : Polynomial.aeval (eᵢ θ) (minpoly F (e₀ θ)) = 0 := by
      rw [minpoly.algHom_eq e₀ e₀.injective]
      exact minpoly.aeval_algHom F eᵢ θ
    obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic (e₀ θ)) hr
    have h : g.toAlgHom.comp e₀ = eᵢ := by
      let j : (⊤ : IntermediateField F E) →ₐ[F] E := (⊤ : IntermediateField F E).val
      have hh : (g.toAlgHom.comp e₀).comp j = eᵢ.comp j := by
        apply IntermediateField.algHom_ext_of_eq_adjoin F hθ.symm
        intro x hx
        obtain rfl : x = θ := Set.mem_singleton_iff.mp hx
        exact hg
      ext x
      exact AlgHom.congr_fun hh ⟨x, IntermediateField.mem_top⟩
    refine ⟨g, ?_⟩
    rw [action, h, Equiv.apply_symm_apply]
  · let p : Gal(L/E) →* MulAction.stabilizer (Gal(L/F)) o :=
      { toFun := fun g => ⟨g.restrictScalars F, (fix_iff _).mpr g.commutes⟩
        map_one' := Subtype.ext (AlgEquiv.ext fun _ => rfl)
        map_mul' := fun _ _ => Subtype.ext (AlgEquiv.ext fun _ => rfl) }
    have hp : Function.Bijective p := by
      constructor
      · intro g h hh
        exact AlgEquiv.ext fun x => AlgEquiv.congr_fun (congrArg Subtype.val hh) x
      · intro g
        let e : L ≃ₐ[E] L := { g.val.toRingEquiv with
          commutes' := (fix_iff g.val).mp g.property }
        exact ⟨e, Subtype.ext (AlgEquiv.ext fun _ => rfl)⟩
    exact ⟨MulEquiv.ofBijective p hp, fun _ => rfl⟩

end

end CubicGalois

section D4Diagram

open CategoryTheory
open LinearAlgebraicGroups.Specs.Pinning
open LinearAlgebraicGroups.Classification.IntegralRootRelations (simpleCorootBasis simpleCorootBasis_apply)
open TrialitarianAlbertDescentSpecification (cartanD4)
noncomputable section

variable (D : BasedRootDatum.{u}) (s : Fin 4 ≃ D.base.support)
  (hD : Submodule.span ℤ (Set.range D.datum.coroot) = ⊤)
  (hC : ∀ i j, D.datum.pairing (s i).val (s j).val = cartanD4 i j)

private def actionOnSimpleRoots (a : Aut D) : Equiv.Perm D.base.support :=
  let e := a.asIso.hom.val.indexEquiv
  have he : e '' (D.base.support : Set D.I) = D.base.support := a.asIso.hom.property
  e.subtypeEquiv fun i => by
    change i ∈ (D.base.support : Set D.I) ↔ e i ∈ (D.base.support : Set D.I)
    constructor
    · intro hi
      exact he ▸ Set.mem_image_of_mem e hi
    · intro hi
      rw [← he] at hi
      obtain ⟨j, hj, h⟩ := hi
      exact e.injective h ▸ hj

private def actionOnAllD4Vertices : Aut D →* Equiv.Perm (Fin 4) where
  toFun a := s.trans ((actionOnSimpleRoots D a).trans s.symm)
  map_one' := by
    apply Equiv.ext
    intro x
    change s.symm (s x) = x
    exact s.symm_apply_apply x
  map_mul' a b := by
    apply Equiv.ext
    intro x
    change s.symm (actionOnSimpleRoots D (a * b) (s x)) =
      s.symm (actionOnSimpleRoots D a (s (s.symm (actionOnSimpleRoots D b (s x)))))
    rw [s.apply_symm_apply]
    congr 1

private theorem actionOnAllD4Vertices_root (a : Aut D) (j : Fin 4) :
    (s (actionOnAllD4Vertices D s a j)).val = a.asIso.hom.val.indexEquiv (s j).val := by
  change (s (s.symm (actionOnSimpleRoots D a (s j)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

private theorem cartanFixesCentre (p : Equiv.Perm (Fin 4))
    (h : ∀ i j, cartanD4 (p i) (p j) = cartanD4 i j) : p 3 = 3 := by
  revert p
  decide

include hC in
private theorem actionOnAllD4Vertices_last (a : Aut D) :
    actionOnAllD4Vertices D s a 3 = 3 := by
  apply cartanFixesCentre
  intro i j
  rw [← hC (actionOnAllD4Vertices D s a i) (actionOnAllD4Vertices D s a j),
    ← hC i j, actionOnAllD4Vertices_root, actionOnAllD4Vertices_root]
  exact a.asIso.hom.val.toHom.pairing

private def outerD4Vertices : Fin 3 ≃ {i : Fin 4 // i ≠ 3} where
  toFun i := ⟨i.castSucc, Fin.ne_of_lt (Fin.castSucc_lt_last i)⟩
  invFun i := i.val.castPred i.property
  left_inv _ := Fin.castPred_castSucc
  right_inv i := Subtype.ext (Fin.castSucc_castPred i.val i.property)

private def restrictOuterVertices (p : Equiv.Perm (Fin 4)) (hp : p 3 = 3) :
    Equiv.Perm (Fin 3) :=
  let q : Equiv.Perm {i : Fin 4 // i ≠ 3} := p.subtypeEquiv fun i => by
    change i ≠ 3 ↔ p i ≠ 3
    calc
      i ≠ 3 ↔ p i ≠ p 3 := p.injective.ne_iff.symm
      _ ↔ p i ≠ 3 := by rw [hp]
  outerD4Vertices.trans (q.trans outerD4Vertices.symm)

private theorem restrictOuterVertices_castSucc (p : Equiv.Perm (Fin 4)) (hp : p 3 = 3)
    (i : Fin 3) :
    (restrictOuterVertices p hp i).castSucc = p i.castSucc := by
  unfold restrictOuterVertices
  simp only [Equiv.trans_apply]
  apply Fin.castSucc_castPred
  change p i.castSucc ≠ 3
  intro h
  exact (outerD4Vertices i).property (p.injective (h.trans hp.symm))

/-- The numbering of the outer vertices gives the permutation homomorphism
of the automorphism group of the based D₄ datum. -/
def actionOnOuterD4Vertices : Aut D →* Equiv.Perm (Fin 3) where
  toFun a := restrictOuterVertices (actionOnAllD4Vertices D s a) (actionOnAllD4Vertices_last D s hC a)
  map_one' := by
    apply Equiv.ext
    intro i
    apply Fin.castSucc_inj.mp
    rw [restrictOuterVertices_castSucc, map_one]
    rfl
  map_mul' a b := by
    apply Equiv.ext
    intro i
    apply Fin.castSucc_inj.mp
    change (restrictOuterVertices _ (actionOnAllD4Vertices_last D s hC (a * b)) i).castSucc =
      (restrictOuterVertices _ (actionOnAllD4Vertices_last D s hC a)
        (restrictOuterVertices _ (actionOnAllD4Vertices_last D s hC b) i)).castSucc
    rw [restrictOuterVertices_castSucc, restrictOuterVertices_castSucc,
      restrictOuterVertices_castSucc, map_mul]
    rfl

theorem actionOnOuterD4Vertices_root (a : Aut D) (i : Fin 3) :
    (s (actionOnOuterD4Vertices D s hC a i).castSucc).val =
      a.asIso.hom.val.indexEquiv (s i.castSucc).val := by
  change (s (restrictOuterVertices _ (actionOnAllD4Vertices_last D s hC a) i).castSucc).val = _
  rw [restrictOuterVertices_castSucc, actionOnAllD4Vertices_root]

include hD in
private theorem actionOnAllD4Vertices_injective : Function.Injective (actionOnAllD4Vertices D s) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  let e := a.asIso.hom.val
  have hroot (j : D.base.support) : e.indexEquiv j = j := by
    obtain ⟨i, rfl⟩ := s.surjective j
    rw [← actionOnAllD4Vertices_root D s a i, ha, Equiv.Perm.one_apply]
  have he : e.coweightMap = LinearMap.id := by
    apply (simpleCorootBasis D hD).ext
    intro i
    rw [simpleCorootBasis_apply, LinearMap.id_apply]
    have hi := congrFun e.coroot_coweightMap (e.indexEquiv i)
    change e.coweightMap (D.datum.coroot (e.indexEquiv i)) =
      D.datum.coroot (e.indexEquiv.symm (e.indexEquiv i)) at hi
    rw [hroot i] at hi
    rw [show e.indexEquiv.symm i = i from (e.indexEquiv.symm_apply_eq).mpr (hroot i).symm] at hi
    exact hi
  have hw : e.weightMap = LinearMap.id := by
    ext x
    apply D.datum.toPerfPair.injective
    apply LinearMap.ext
    intro y
    have hh := DFunLike.congr_fun (DFunLike.congr_fun e.weight_coweight_transpose y) x
    change D.datum.toLinearMap (e.weightMap x) y =
      D.datum.toLinearMap x (e.coweightMap y) at hh
    change D.datum.toLinearMap (e.weightMap x) y = D.datum.toLinearMap x y
    simpa only [he, LinearMap.id_apply] using hh
  have hi (i : D.I) : e.indexEquiv i = i := by
    apply D.datum.root.injective
    have h := congrFun e.root_weightMap i
    change e.weightMap (D.datum.root i) = D.datum.root (e.indexEquiv i) at h
    simpa only [hw, LinearMap.id_apply] using h.symm
  apply Aut.ext
  apply Iso.ext
  apply Subtype.ext
  apply RootPairing.Equiv.ext
  · exact hw
  · exact he
  · exact Equiv.ext hi

include hD in
theorem actionOnOuterD4Vertices_injective : Function.Injective (actionOnOuterD4Vertices D s hC) := by
  intro a b h
  apply actionOnAllD4Vertices_injective D s hD
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (actionOnAllD4Vertices_last D s hC a).trans (actionOnAllD4Vertices_last D s hC b).symm
  · apply s.injective
    apply Subtype.ext
    rw [actionOnAllD4Vertices_root, actionOnAllD4Vertices_root,
      ← actionOnOuterD4Vertices_root D s hC a j, ← actionOnOuterD4Vertices_root D s hC b j, h]

end

end D4Diagram

section InnerCentreComparison

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AutomorphismSequence
open Fppf (schemeTopology)
open private groupSectionsMap groupSectionsMap_locallySurjective groupSections_isSheaf
  groupSheaf_separated from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
  {Q : AdjointQuotient G} {O : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{u+1}}

set_option backward.isDefEq.respectTransparency false in
/-- Inner automorphisms act trivially on the scheme centre, including sections
over nonreduced test schemes. The central quotient is lifted fppf locally. -/
theorem innerSection_fixesCentre
    (A : ExactSequence G Q O) {S : SchemeOver k}
    (q : (groupSections Q.quotient.val).obj (op S))
    (U : Over S) (z : U.left ⟶ G.val.X) (hz : Centralizes (𝟙 G.val) z) :
    ((A.inner.app (op S) q).asIso.hom.app (op U)).hom z = z := by
  let m := groupSectionsMap Q.projection
  let := groupSectionsMap_locallySurjective Q.projection Q.fppf
  let qU := ((groupSections Q.quotient.val).map U.hom.op) q
  let f := A.inner.app (op S) q
  let z' : U.left ⟶ G.val.X := (f.asIso.hom.app (op U)).hom z
  change z' = z
  apply ULift.up_injective
  refine groupSheaf_separated (groupSections_isSheaf G.val)
    (Presheaf.imageSieve_mem (schemeTopology k) m qU) ⟨z'⟩ ⟨z⟩ ?_
  intro W a ha
  change W ⟶ U.left at a
  obtain ⟨w, hw⟩ := ha
  let V : Over S := (Over.map (a ≫ U.hom)).obj (Over.mk (𝟙 W))
  let b : V ⟶ U := Over.homMk a (Category.id_comp _).symm
  have hn := ConcreteCategory.congr_hom (f.asIso.hom.naturality b.op) z
  change (f.asIso.hom.app (op V)).hom (a ≫ z) = a ≫ z' at hn
  have hq : m.app (op W) w =
      (groupSections Q.quotient.val).map (a ≫ U.hom).op q := by
    rw [op_comp, Functor.map_comp]
    exact hw
  have hinner : restrictAut (a ≫ U.hom) f = innerAut w.down := by
    have hn := NatTrans.naturality_apply A.inner (a ≫ U.hom).op q
    change A.inner.app (op W) ((groupSections Q.quotient.val).map (a ≫ U.hom).op q) =
      restrictAut (a ≫ U.hom) f at hn
    rw [← hn, ← hq]
    exact A.onLift W w.down
  have he := congrArg (fun t : RelativeAut G.val W =>
    (t.asIso.hom.app (op (Over.mk (𝟙 W)))).hom (a ≫ z)) hinner
  change (f.asIso.hom.app (op V)).hom (a ≫ z) =
    (𝟙 W ≫ w.down) * (a ≫ z) * (𝟙 W ≫ w.down)⁻¹ at he
  rw [hn, Category.id_comp] at he
  apply ULift.ext
  change a ≫ z' = a ≫ z
  rw [he]
  have hc := (centralizes_iff (𝟙 G.val) z).mp hz W a w.down
  change Commute (a ≫ z) (w.down ≫ 𝟙 G.val.X) at hc
  rw [Category.comp_id] at hc
  rw [hc.symm.eq, mul_inv_cancel_right]

end

end InnerCentreComparison

section ReferenceDisplacement

open AlgebraicGeometry CategoryTheory Opposite TensorProduct
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Specs
open AutomorphismSequence (relativePoints RelativeAut restrictIso)
open RelativeFormComparison (fieldTest fieldMap transportedAut)
open TrialitarianAlbertDescentSpecification
open OctonionEquivariantAutomorphisms (affineTest)
open private exists_relativeIso relativeHom_ext restrictIso_affine_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
noncomputable section

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
variable (G : AffineAlgebraicGroup k)
  (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
  (hNat : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points G.val.X R) (x : Model R),
    mapModel f.hom.toRingHom ((p R a).val x) =
      (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x))

private theorem permuteFramePoint_one (R : TestAlgebra k) (a : Points G.val.X R) :
    permuteFramePoint G p 1 R a = a := by
  apply (p R).injective
  rw [permuteFramePoint_compare]
  apply Subtype.ext
  change (MulAut.conj (framePermutationAction (R : Type u) 1)) (p R a).val = _
  rw [map_one, map_one, MulAut.one_apply]

private theorem permuteFramePoint_mul (π ν : Equiv.Perm (Fin 3))
    (R : TestAlgebra k) (a : Points G.val.X R) :
    permuteFramePoint G p (π * ν) R a =
      permuteFramePoint G p π R (permuteFramePoint G p ν R a) := by
  apply (p R).injective
  rw [permuteFramePoint_compare, permuteFramePoint_compare, permuteFramePoint_compare]
  apply Subtype.ext
  change (MulAut.conj (framePermutationAction (R : Type u) (π * ν))) (p R a).val =
    (MulAut.conj (framePermutationAction (R : Type u) π))
      ((MulAut.conj (framePermutationAction (R : Type u) ν)) (p R a).val)
  rw [map_mul, map_mul, MulAut.mul_apply]

include hNat in
private theorem permutationRelativeIso_exists (π : Equiv.Perm (Fin 3)) :
    ∃ j : relativePoints G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S),
      ∀ (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R),
        (j.hom.app (op (affineTest f))).hom b = permuteFramePoint G p π R b :=
  exists_relativeIso G.property.1 G.property.1 (fun R _ => permuteFramePoint G p π R)
    (fun _ g b => (permuteFramePoint_natural G p hNat π g b).symm)

/-- The permutations of the split frame act on the relative scheme of its
pointwise spin stabilizer over the splitting field. -/
def framePermutationRelativeAut : Equiv.Perm (Fin 3) →* RelativeAut G.val (fieldTest k S) where
  toFun π := Aut.of ((permutationRelativeIso_exists (S := S) G p hNat π).choose)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext G.property.1
    intro R f b
    change _ = b
    rw [(permutationRelativeIso_exists G p hNat 1).choose_spec R f b, permuteFramePoint_one]
  map_mul' π ν := by
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext G.property.1
    intro R f b
    let a (r : Equiv.Perm (Fin 3)) := (permutationRelativeIso_exists (S := S) G p hNat r).choose
    have h (r : Equiv.Perm (Fin 3)) (x : Points G.val.X R) :
        ((a r).hom.app (op (affineTest f))).hom x = permuteFramePoint G p r R x :=
      (permutationRelativeIso_exists G p hNat r).choose_spec R f x
    change ((a (π * ν)).hom.app (op (affineTest f))).hom b =
      ((a π).hom.app (op (affineTest f))).hom (((a ν).hom.app (op (affineTest f))).hom b)
    rw [h, h, h, permuteFramePoint_mul]

theorem framePermutationRelativeAut_apply (π : Equiv.Perm (Fin 3))
    (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R) :
    (((framePermutationRelativeAut G p hNat π).asIso.hom).app (op (affineTest f))).hom b =
      permuteFramePoint G p π R b :=
  (permutationRelativeIso_exists G p hNat π).choose_spec R f b

variable [Module.Finite k E]

set_option maxHeartbeats 1300000 in
include hNat in
/-- In the split coordinates for the permutation reference, the relative
displacement is exactly the automorphism induced by the frame permutation. -/
private theorem referencePermutationDisplacement
    {J : AlbertModel k} (B : CubicStabilizer J E) (numbering : (E →ₐ[k] S) ≃ Fin 3)
    (C : FrameCharts J B numbering) (cubic : Module.finrank k E = 3) :
    ∃ j : relativePoints G.val (fieldTest k S) ≅ relativePoints B.stabilizer.group (fieldTest k S),
      ∀ σ, transportedAut k S j σ = framePermutationRelativeAut G p hNat (diagramPermutation numbering σ) := by
  obtain ⟨j, hj⟩ := cubicStabilizerRelativeFrameIso B numbering C cubic G p hNat
  refine ⟨j, fun σ => ?_⟩
  let π := diagramPermutation numbering σ
  let a := framePermutationRelativeAut (S := S) G p hNat π
  have heq : restrictIso (fieldMap k S σ) j = a.asIso ≪≫ j := by
    apply Iso.ext
    apply relativeHom_ext G.property.1
    intro R f b
    rw [restrictIso_affine_apply]
    let f' : CommAlgCat.of k S ⟶ R := CommAlgCat.ofHom σ.toAlgHom ≫ f
    change (j.hom.app (op (affineTest f'))).hom b =
      (j.hom.app (op (affineTest f))).hom ((a.asIso.hom.app (op (affineTest f))).hom b)
    have happ (x : Points G.val.X R) :
        (a.asIso.hom.app (op (affineTest f))).hom x = permuteFramePoint G p π R x :=
      framePermutationRelativeAut_apply G p hNat π R f x
    rw [happ]
    apply cubicStabilizerAction_faithful B R
    apply LinearEquiv.ext
    intro x
    apply (C.chart R f).injective
    rw [← hj, C.permutation R f σ, ← hj, permuteFramePoint_compare]
    rw [C.permutation R f σ x, frameStabilizerPermutation_apply]
  apply Aut.ext
  change restrictIso (fieldMap k S σ) j ≪≫ j.symm = a.asIso
  rw [heq, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]

section FaithfulOuterAction

open AutomorphismSequence
open QuasiSplitInnerForms (outerHom)
open Pinning (PinnedGroup AttachedDatum)
open RootGroups (AdditiveLine)
open LinearAlgebraicGroups.Composition (Zorn)
open scoped BigOperators
private abbrev signProbe (S : Type u) [Field S] := MonoidAlgebra S (Multiplicative (ZMod 2))

private def signProbeUnit (S : Type u) [Field S] : (signProbe S)ˣ :=
  let a := Multiplicative.ofAdd (1 : ZMod 2)
  Units.map (MonoidAlgebra.of S (Multiplicative (ZMod 2)))
    ⟨a, a⁻¹, mul_inv_cancel a, inv_mul_cancel a⟩

private theorem signProbeUnit_square (S : Type u) [Field S] : signProbeUnit S ^ 2 = 1 := by
  apply Units.ext
  let f := MonoidAlgebra.of S (Multiplicative (ZMod 2))
  change f (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1
  rw [← map_pow]
  have h : Multiplicative.ofAdd (1 : ZMod 2) ^ 2 = 1 := by decide
  rw [h, map_one]

private theorem signProbeUnit_ne_one (S : Type u) [Field S] : signProbeUnit S ≠ 1 := by
  intro h
  have he := congrArg Units.val h
  change MonoidAlgebra.of S _ (Multiplicative.ofAdd (1 : ZMod 2)) = (1 : signProbe S) at he
  rw [← map_one (MonoidAlgebra.of S (Multiplicative (ZMod 2)))] at he
  have hh := MonoidAlgebra.of_injective he
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) hh

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
  {A : AdditiveLine k} {P : PinnedGroup A} {D : AttachedDatum P.pair}
  {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}

set_option maxHeartbeats 1250000 in
set_option backward.isDefEq.respectTransparency false in
/-- A frame permutation which is inner must fix all three scalar sign
characters. They remain distinguishable on nonreduced test algebras. -/
theorem outerFramePermutation_injective (A : SplitSequence P D l Q)
    (p : ∀ R : TestAlgebra k, Points P.pair.G.val.X R ≃* frameStabilizer (R := R))
    (hNat : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points P.pair.G.val.X R) (x : Model R),
      mapModel f.hom.toRingHom ((p R a).val x) =
        (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x))
    (vectorCentre : ∀ (R : TestAlgebra k) (g : Points P.pair.G.val.X R),
      Centralizes (𝟙 P.pair.G.val) g →
        ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R g).val x).2 1 = (c : R) • x.2 1) :
    Function.Injective ((outerHom (S := S) A).comp (framePermutationRelativeAut P.pair.G p hNat)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro π hp
  let fπ := framePermutationRelativeAut (S := S) P.pair.G p hNat π
  have ho : outerHom (S := S) A fπ = 1 := hp
  have he : A.toExactSequence.outer.app (op (fieldTest k S)) fπ = 1 :=
    (QuasiSplitInnerForms.constantEvaluation k S _).injective (by exact ho)
  obtain ⟨q, hq⟩ := (A.toExactSequence.exact _ fπ).mp he
  let : Algebra k (signProbe S) := ((algebraMap S (signProbe S)).comp (algebraMap k S)).toAlgebra
  let : IsScalarTower k S (signProbe S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let R := CommAlgCat.of k (signProbe S)
  let f : CommAlgCat.of k S ⟶ R := CommAlgCat.ofHom (IsScalarTower.toAlgHom k S (signProbe S))
  apply Equiv.ext
  intro i
  let c := signProbeUnit S
  let t (j : Fin 3) : Rˣ := if j = i then 1 else c
  have ht (j : Fin 3) : t j ^ 2 = 1 := by
    by_cases h : j = i
    · simp [t, h]
    · simpa only [t, ite_eq_right h] using signProbeUnit_square S
  have hprod : (∏ j, t j) = 1 := by
    have hc : c * c = 1 := (pow_two c).symm ▸ signProbeUnit_square S
    fin_cases i <;> simp [Fin.prod_univ_three, t, hc]
  have hs : IsRelated (scalarTriple t) := (isRelated_scalarTriple_iff t).mpr ⟨ht, hprod⟩
  obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
  let z := (p R).symm (e ⟨scalarTriple t, hs⟩)
  have hscalar (x : Model R) : (p R z).val x = (x.1, fun j => (t j : R) • x.2 j) := by
    change (p R ((p R).symm (e ⟨scalarTriple t, hs⟩))).val x = _
    rw [MulEquiv.apply_symm_apply, he]
    rfl
  have hz : Centralizes (𝟙 P.pair.G.val) z :=
    (splitFrameCentreScalars P.pair.G p hNat vectorCentre R z).mpr ⟨t, ht, hprod, hscalar⟩
  have hw := innerSection_fixesCentre A.toExactSequence q (affineTest f) z hz
  change ((A.toExactSequence.inner.app _ q).asIso.hom.app (op (affineTest f))).hom z = z at hw
  rw [show A.toExactSequence.inner.app (op (fieldTest k S)) q = fπ from hq] at hw
  change _ = z at hw
  have hperm : permuteFramePoint P.pair.G p π R z = z :=
    (framePermutationRelativeAut_apply P.pair.G p hNat π R f z).symm.trans hw
  let x : Model R := (0, fun _ => 1)
  have hh := frameStabilizerPermutation_apply π (p R z) x
  rw [← permuteFramePoint_compare P.pair.G p π R z, hperm] at hh
  simp only [hscalar] at hh
  have hb := congrArg (fun y : Model R => y.2 (π i)) hh
  change (t (π i) : R) • (framePermutation π x).2 (π i) =
    (framePermutation π (x.1, fun j => (t j : R) • x.2 j)).2 (π i) at hb
  rw [framePermutation_block, framePermutation_block, ← map_smul] at hb
  have hh' : t (π i) = t i := Units.ext (scalar_eq_of_smul_zorn_one
    ((blockPermutation π).injective hb))
  by_contra h
  change π i ≠ i at h
  have hc : c = 1 := by simpa [t, h] using hh'
  exact signProbeUnit_ne_one S hc

end FaithfulOuterAction

end

end ReferenceDisplacement

section OuterFrameGroup

open CategoryTheory LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (transportedAut)
noncomputable section

private def outerTransposition (i : Fin 3) : Equiv.Perm (Fin 3) :=
  Equiv.swap (i + 1) (i + 2)

private theorem outerTransposition_injective : Function.Injective outerTransposition := by decide

private theorem outerTransposition_square (i : Fin 3) : outerTransposition i ^ 2 = 1 := by
  revert i
  decide

private theorem outerTransposition_ne_one (i : Fin 3) : outerTransposition i ≠ 1 := by
  revert i
  decide

private theorem permThree_involution (a : Equiv.Perm (Fin 3)) :
    a ^ 2 = 1 → a ≠ 1 → ∃ i, outerTransposition i = a := by
  revert a
  decide

private theorem outerTransposition_conj (p : Equiv.Perm (Fin 3)) (i : Fin 3) :
    MulAut.conj p (outerTransposition i) = outerTransposition (p i) := by
  revert p i
  decide

private theorem outerTransposition_generates (a : Equiv.Perm (Fin 3)) :
    a = 1 ∨ (∃ i, a = outerTransposition i) ∨
      ∃ i j, a = outerTransposition i * outerTransposition j := by
  revert a
  decide

/-- Every automorphism of the three-letter symmetric group is conjugation
by a relabelling of the three letters. -/
theorem permThree_automorphism_inner (a : MulAut (Equiv.Perm (Fin 3))) :
    ∃ p : Equiv.Perm (Fin 3), a = MulAut.conj p := by
  have h (i : Fin 3) : ∃ j, outerTransposition j = a (outerTransposition i) := by
    apply permThree_involution
    · rw [← map_pow, outerTransposition_square, map_one]
    · simpa using outerTransposition_ne_one i
  choose p hp using h
  have hinj : Function.Injective p := by
    intro i j hij
    apply outerTransposition_injective
    apply a.injective
    rw [← hp, ← hp, hij]
  let q := Equiv.ofBijective p ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have hq (i : Fin 3) : a (outerTransposition i) = MulAut.conj q (outerTransposition i) :=
    (hp i).symm.trans (outerTransposition_conj q i).symm
  refine ⟨q, MulEquiv.ext fun g => ?_⟩
  rcases outerTransposition_generates g with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · rw [map_one, map_one]
  · exact hq i
  · rw [map_mul, map_mul, hq, hq]

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]

/-- On the given form the outer permutation is the action on the numbered
embeddings of the cubic orbit field. -/
theorem diagramPresentation_outerPermutation (G : AffineAlgebraicGroup k)
    (D : DiagramPresentation G E S) (σ : Gal(S/k)) :
    actionOnOuterD4Vertices D.datum.toBased D.roots D.cartan
        (outerHom D.autSequence (transportedAut k S D.form σ)) =
      diagramPermutation D.numbering σ := by
  apply Equiv.ext
  intro i
  obtain ⟨e, rfl⟩ := D.numbering.surjective i
  apply Fin.castSucc_inj.mp
  apply D.roots.injective
  apply Subtype.ext
  rw [actionOnOuterD4Vertices_root, D.diagramAction]
  have h : diagramPermutation D.numbering σ (D.numbering e) =
      D.numbering (σ.toAlgHom.comp e) := by
    change D.numbering (σ.toAlgHom.comp (D.numbering.symm (D.numbering e))) = _
    rw [Equiv.symm_apply_apply]
  rw [h]

end

end OuterFrameGroup


section ReferenceOuterIdentification

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open LinearAlgebraicGroups.Specs.SimplyConnectedLattice (corootLattice)
open LinearAlgebraicGroups.Classification.SimplyConnectedLattice (latticeCriterion)
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence
open QuasiSplitInnerForms (outerHom)
open RelativeFormComparison (fieldTest fieldMap transportedAut automorphismAction)
open Pinning (AttachedDatum)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open OctonionEquivariantAutomorphisms (affineTest)
open private relativeHom_ext restrictIso_affine_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers

noncomputable section

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]

private def pointIsoOfIso {G H : GroupScheme k} (f : G ≅ H) (R : TestAlgebra k) :
    Points G.X R ≃* Points H.X R where
  toFun b := b ≫ f.hom.hom.hom
  invFun b := b ≫ f.inv.hom.hom
  left_inv b := by
    have h : f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 G.X :=
      congrArg (fun q : G ⟶ G => q.hom.hom) f.hom_inv_id
    change (b ≫ f.hom.hom.hom) ≫ f.inv.hom.hom = b
    rw [Category.assoc, h, Category.comp_id]
  right_inv b := by
    have h : f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 H.X :=
      congrArg (fun q : H ⟶ H => q.hom.hom) f.inv_hom_id
    change (b ≫ f.inv.hom.hom) ≫ f.hom.hom.hom = b
    rw [Category.assoc, h, Category.comp_id]
  map_mul' b c := MonObj.mul_comp _ _ _

private theorem pointIsoOfIso_natural {G H : GroupScheme k} (i : G ≅ H)
    {R T : TestAlgebra k} (f : R ⟶ T) (b : Points G.X R) :
    mapPoints f (pointIsoOfIso i R b) = pointIsoOfIso i T (mapPoints f b) :=
  (Category.assoc _ _ _).symm

private theorem centralizes_postcomp_iso {G H : GroupScheme k} (i : G ≅ H)
    {R : SchemeOver k} (g : R ⟶ G.X) (h : Centralizes (𝟙 G) g) :
    Centralizes (𝟙 H) (g ≫ i.hom.hom.hom) := by
  apply (centralizes_iff _ _).mpr
  intro U b x
  have hcomm := (centralizes_iff _ _).mp h U b (x ≫ i.inv.hom.hom)
  change Commute (b ≫ g) ((x ≫ i.inv.hom.hom) ≫ 𝟙 G.X) at hcomm
  rw [Category.comp_id] at hcomm
  let m : (U ⟶ G.X) →* (U ⟶ H.X) :=
    { toFun := fun z => z ≫ i.hom.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  have hm := hcomm.map m
  change Commute ((b ≫ g) ≫ i.hom.hom.hom) ((x ≫ i.inv.hom.hom) ≫ i.hom.hom.hom) at hm
  have hi : i.inv.hom.hom ≫ i.hom.hom.hom = 𝟙 H.X :=
    congrArg (fun q : H ⟶ H => q.hom.hom) i.inv_hom_id
  rw [Category.assoc, Category.assoc, hi, Category.comp_id] at hm
  simpa using hm

private theorem framePermutationRelativeAut_invariant (G : AffineAlgebraicGroup k)
    (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
    (hp : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points G.val.X R) (x : Model R),
      mapModel f.hom.toRingHom ((p R a).val x) =
        (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x))
    (π : Equiv.Perm (Fin 3)) (σ : Gal(S/k)) :
    automorphismAction k S G.val σ (framePermutationRelativeAut G p hp π) =
      framePermutationRelativeAut G p hp π := by
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext G.property.1
  intro R f b
  let a := framePermutationRelativeAut (S := S) G p hp π
  change (((restrictIso (fieldMap k S σ) a.asIso).hom.app (op (affineTest f))).hom b) =
    (a.asIso.hom.app (op (affineTest f))).hom b
  rw [restrictIso_affine_apply, framePermutationRelativeAut_apply, framePermutationRelativeAut_apply]

set_option maxHeartbeats 2100000 in
set_option backward.isDefEq.respectTransparency false in
/-- The descended frame stabilizer realizes the specified outer cocycle.
Relabelling the split comparison aligns the induced outer permutation with
the original pinned numbering. -/
theorem exists_permutationReference_sameOuter [Module.Finite k E] [IsSepClosure k S]
    (cubic : Module.finrank k E = 3) (G : AffineAlgebraicGroup k)
    (D : DiagramPresentation G E S) :
    ∃ (J : AlbertModel k) (B : CubicStabilizer J E),
      IsPermutationDescent J B D.numbering ∧ Nonempty (FrameCharts J B D.numbering) ∧
      ∃ j : relativePoints D.pinned.pair.G.val (fieldTest k S) ≅
        relativePoints B.stabilizer.group (fieldTest k S),
      ∀ σ, outerHom D.autSequence (transportedAut k S j σ) =
        outerHom D.autSequence (transportedAut k S D.form σ) := by
  obtain ⟨J, B, hJ, ⟨C⟩⟩ := exists_permutationReferenceWithCharts D.numbering
  obtain ⟨G₀, a, ha, hG₀, _, _, T, d, hd, hT, hmax, hZ, hc,
    X, Y, A, _, hpairs, hroots, hcoroot⟩ :=
    LinearAlgebraicGroups.Albert.SpinWeights.fieldStructure.{u} k
  let : IsCommMonObj T.group.X := hc
  obtain ⟨f⟩ := spinGroup_iso_of_D4 hG₀ T hT hmax A X Y hpairs hroots.surjOn hcoroot
    D.pinned.pair D.datum D.semisimple D.simplyConnected D.roots D.cartan
  obtain ⟨p₀, hNat₀, hCentre₀⟩ := splitSpinFramePoints G₀ a ha
  let P := D.pinned.pair.G
  let p (R : TestAlgebra k) := (pointIsoOfIso f R).trans (p₀ R)
  have hp {R T : TestAlgebra k} (m : R ⟶ T) (b : Points P.val.X R) (x : Model R) :
      mapModel m.hom.toRingHom ((p R b).val x) =
        (p T (mapPoints m b)).val (mapModel m.hom.toRingHom x) := by
    change mapModel m.hom.toRingHom ((p₀ R (pointIsoOfIso f R b)).val x) =
      (p₀ T (pointIsoOfIso f T (mapPoints m b))).val (mapModel m.hom.toRingHom x)
    rw [hNat₀, pointIsoOfIso_natural]
  have hCentre (R : TestAlgebra k) (b : Points P.val.X R) (hb : Centralizes (𝟙 P.val) b) :
      ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R b).val x).2 1 = (c : R) • x.2 1 :=
    hCentre₀ T d hd hZ R (pointIsoOfIso f R b) (centralizes_postcomp_iso f b hb)
  obtain ⟨j, hj⟩ := referencePermutationDisplacement P p hp B D.numbering C cubic
  let : IsCommMonObj D.pinned.pair.T.group.X := D.datum.comm
  have hD : corootLattice D.datum = ⊤ :=
    (latticeCriterion P D.semisimple D.pinned.pair.T D.pinned.pair.split D.pinned.pair.maximal D.datum.datum).mp
      D.simplyConnected
  let θ := actionOnOuterD4Vertices D.datum.toBased D.roots D.cartan
  have hθ : Function.Injective θ :=
    actionOnOuterD4Vertices_injective D.datum.toBased D.roots hD D.cartan
  let frameAut := framePermutationRelativeAut (S := S) P p hp
  let q := outerHom (S := S) D.autSequence
  let τ := θ.comp (q.comp frameAut)
  have hτ : Function.Injective τ :=
    hθ.comp (outerFramePermutation_injective (S := S) D.autSequence p hp hCentre)
  let e := MulEquiv.ofBijective τ ⟨hτ, Finite.injective_iff_surjective.mp hτ⟩
  obtain ⟨π, hπ⟩ := permThree_automorphism_inner e
  have he (ν : Equiv.Perm (Fin 3)) : τ ν = π * ν * π⁻¹ := by
    exact congrArg (fun e' : MulAut (Equiv.Perm (Fin 3)) => e' ν) hπ
  have hself : τ π = π := by rw [he, mul_inv_cancel_right]
  let b := frameAut π
  refine ⟨J, B, hJ, ⟨C⟩, b.asIso ≪≫ j, fun σ => hθ ?_⟩
  rw [LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.changeOfTrivialization,
    show automorphismAction k S P.val σ b = b from framePermutationRelativeAut_invariant P p hp π σ]
  simp only [hj, map_mul, map_inv]
  have hpinned : θ (q (transportedAut k S D.form σ)) = diagramPermutation D.numbering σ :=
    diagramPresentation_outerPermutation G D σ
  rw [hpinned]
  change (τ π)⁻¹ * τ (diagramPermutation D.numbering σ) * τ π = diagramPermutation D.numbering σ
  rw [hself, he]
  group

end

end ReferenceOuterIdentification

section SimilarityConjugation

open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
noncomputable section

variable {R T : Type u} [CommRing R] [CommRing T]

private def similarityOnModel : RelatedSimilarities R →* (Model R ≃ₗ[R] Model R) where
  toFun a := (LinearEquiv.refl R (Fin 3 → R)).prodCongr
    (LinearEquiv.piCongrRight fun i => a.val.1 i)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    rfl
  map_mul' a b := by
    apply LinearEquiv.ext
    intro x
    rfl

private theorem similarityOnModel_apply (a : RelatedSimilarities R) (x : Model R) :
    similarityOnModel a x = (x.1, fun i => a.val.1 i (x.2 i)) := rfl

private theorem similarityOnModel_natural (f : R →+* T) (a : RelatedSimilarities R) (x : Model R) :
    mapModel f (similarityOnModel a x) =
      similarityOnModel (relatedSimilarityBaseChange f a) (mapModel f x) := by
  rw [similarityOnModel_apply, similarityOnModel_apply]
  exact Prod.ext rfl (funext fun i => (relatedSimilarityBaseChange_apply f a i (x.2 i)).symm)

private theorem similarityOnModel_triality
    (e : relatedTriples (R := R) ≃* frameStabilizer (R := R))
    (he : ∀ r : relatedTriples (R := R), ∀ x : Model R,
      (e r).val x = (x.1, fun i => r.val i (x.2 i))) (r : relatedTriples (R := R)) :
    similarityOnModel (relatedTripleInclusion r) = (e r).val := by
  apply LinearEquiv.ext
  intro x
  exact (he r x).symm

private theorem similarityOnModel_normalizes (a : RelatedSimilarities R) (b : frameStabilizer (R := R)) :
    MulAut.conj (similarityOnModel a) b.val ∈ frameStabilizer (R := R) := by
  obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
  obtain ⟨r, rfl⟩ := e.surjective b
  let z := a * relatedTripleInclusion r * a⁻¹
  have h : compositionQuotient z = 1 := by
    change compositionQuotient (a * relatedTripleInclusion r * a⁻¹) = 1
    have hr : compositionQuotient (relatedTripleInclusion r) = 1 := rfl
    rw [map_mul, map_mul, map_inv, hr, mul_one, mul_inv_cancel]
  obtain ⟨t, ht⟩ := (compositionQuotient_kernel z).mp h
  have hm : (e t).val = MulAut.conj (similarityOnModel a) (e r).val := by
    rw [← similarityOnModel_triality e he t, ht, ← similarityOnModel_triality e he r]
    change similarityOnModel (a * relatedTripleInclusion r * a⁻¹) = _
    rw [map_mul, map_mul, map_inv, MulAut.conj_apply]
  exact hm ▸ (e t).property

/-- Blockwise conjugation by related similarities acts on the pointwise
frame stabilizer. Its action is defined on every coefficient ring. -/
def similarityFrameAction : RelatedSimilarities R →* MulAut (frameStabilizer (R := R)) where
  toFun a :=
    { toFun := fun b => ⟨MulAut.conj (similarityOnModel a) b.val, similarityOnModel_normalizes a b⟩
      invFun := fun b => ⟨MulAut.conj (similarityOnModel a⁻¹) b.val, similarityOnModel_normalizes a⁻¹ b⟩
      left_inv := fun b => by
        apply Subtype.ext
        change MulAut.conj (similarityOnModel a⁻¹) (MulAut.conj (similarityOnModel a) b.val) = b.val
        rw [map_inv, MulAut.conj_apply, MulAut.conj_apply]
        group
      right_inv := fun b => by
        apply Subtype.ext
        change MulAut.conj (similarityOnModel a) (MulAut.conj (similarityOnModel a⁻¹) b.val) = b.val
        rw [map_inv, MulAut.conj_apply, MulAut.conj_apply]
        group
      map_mul' := fun b c => Subtype.ext (map_mul (MulAut.conj (similarityOnModel a)) b.val c.val) }
  map_one' := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change MulAut.conj (similarityOnModel (1 : RelatedSimilarities R)) b.val = b.val
    rw [map_one, map_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change MulAut.conj (similarityOnModel (a * b)) c.val =
      MulAut.conj (similarityOnModel a) (MulAut.conj (similarityOnModel b) c.val)
    rw [map_mul, map_mul, MulAut.mul_apply]

theorem similarityFrameAction_apply (a : RelatedSimilarities R) (b : frameStabilizer (R := R)) (x : Model R) :
    (similarityFrameAction a b).val (similarityOnModel a x) =
      similarityOnModel a (b.val x) := by
  change similarityOnModel a (b.val ((similarityOnModel a).symm (similarityOnModel a x))) = _
  rw [LinearEquiv.symm_apply_apply]

private theorem similarityOnModel_scalar_commute (t : Fin 3 → Rˣ)
    (b : frameStabilizer (R := R)) : Commute (similarityOnModel (scalarSimilarity t)) b.val := by
  obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
  obtain ⟨r, rfl⟩ := e.surjective b
  rw [← similarityOnModel_triality e he r]
  exact (scalarSimilarity_central t (relatedTripleInclusion r)).map similarityOnModel

theorem similarityFrameAction_scalar (t : Fin 3 → Rˣ) :
    similarityFrameAction (scalarSimilarity t) = 1 := by
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  change MulAut.conj (similarityOnModel (scalarSimilarity t)) b.val = b.val
  rw [MulAut.conj_apply, (similarityOnModel_scalar_commute t b).eq, mul_inv_cancel_right]

section SimilarityRelativeConjugation

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj BigOperators
open LinearAlgebraicGroups.Specs
open AutomorphismSequence (relativePoints RelativeAut innerAut)
open RelativeFormComparison (fieldTest)
open OctonionEquivariantAutomorphisms (affineTest)
open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open private exists_relativeIso relativeHom_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms

theorem relatedSimilarityBaseChange_scalar {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (a : Fin 3 → Rˣ) :
    relatedSimilarityBaseChange f (scalarSimilarity a) =
      scalarSimilarity (fun i => Units.map f.toMonoidHom (a i)) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply zornMap_ext f
    intro x
    rw [relatedSimilarityBaseChange_apply]
    change mapCoordinates f (scalarTriple a i x) =
      scalarTriple (fun j => Units.map f.toMonoidHom (a j)) i (mapCoordinates f x)
    rw [scalarTriple_apply, scalarTriple_apply, mapCoordinates_smul]
    rfl
  · funext i
    change Units.map f.toMonoidHom (a i ^ 2 / ∏ j, a j) =
      Units.map f.toMonoidHom (a i) ^ 2 / ∏ j, Units.map f.toMonoidHom (a j)
    rw [map_div, map_pow, map_prod]

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
variable (G : AffineAlgebraicGroup k)
  (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
  (hNat : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points G.val.X R) (x : Model R),
    mapModel f.hom.toRingHom ((p R a).val x) =
      (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x))

private def similarityOnPoints (a : RelatedSimilarities S) (R : TestAlgebra k)
    (f : CommAlgCat.of k S ⟶ R) : MulAut (Points G.val.X R) :=
  (p R).trans ((similarityFrameAction (relatedSimilarityBaseChange f.hom.toRingHom a)).trans (p R).symm)

private theorem similarityOnPoints_compare (a : RelatedSimilarities S) (R : TestAlgebra k)
    (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R) :
    p R (similarityOnPoints G p a R f b) =
      similarityFrameAction (relatedSimilarityBaseChange f.hom.toRingHom a) (p R b) :=
  (p R).apply_symm_apply _

include hNat in
private theorem similarityOnPoints_natural (a : RelatedSimilarities S) {R T : TestAlgebra k}
    (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T) (b : Points G.val.X R) :
    similarityOnPoints G p a T (f ≫ g) (mapPoints g b) =
      mapPoints g (similarityOnPoints G p a R f b) := by
  apply (p T).injective
  apply Subtype.ext
  apply modelMap_ext g.hom.toRingHom
  intro x
  let aR := relatedSimilarityBaseChange f.hom.toRingHom a
  let aT := relatedSimilarityBaseChange (f ≫ g).hom.toRingHom a
  have ha : relatedSimilarityBaseChange g.hom.toRingHom aR = aT :=
    relatedSimilarityBaseChange_comp f.hom.toRingHom g.hom.toRingHom a
  obtain ⟨x, rfl⟩ := (similarityOnModel aR).surjective x
  rw [similarityOnPoints_compare, ← hNat,
    similarityOnPoints_compare, similarityFrameAction_apply, similarityOnModel_natural, ha,
    similarityOnModel_natural, ha, similarityFrameAction_apply, hNat]

include hNat in
private theorem similarityRelativeIso_exists (a : RelatedSimilarities S) :
    ∃ j : relativePoints G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S),
      ∀ (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R),
        (j.hom.app (op (affineTest f))).hom b = similarityOnPoints G p a R f b :=
  exists_relativeIso G.property.1 G.property.1 (similarityOnPoints G p a)
    (fun f g b => similarityOnPoints_natural G p hNat a f g b)

/-- Blockwise similarity conjugation as an automorphism of the actual
split frame group scheme over the coefficient field. -/
def similarityRelativeAut : RelatedSimilarities S →* RelativeAut G.val (fieldTest k S) where
  toFun a := Aut.of ((similarityRelativeIso_exists G p hNat a).choose)
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext G.property.1
    intro R f b
    change _ = b
    rw [(similarityRelativeIso_exists G p hNat 1).choose_spec R f b]
    apply (p R).injective
    rw [similarityOnPoints_compare, map_one, map_one, MulAut.one_apply]
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    apply relativeHom_ext G.property.1
    intro R f c
    let j (x : RelatedSimilarities S) := (similarityRelativeIso_exists G p hNat x).choose
    have h (x : RelatedSimilarities S) (y : Points G.val.X R) :
        ((j x).hom.app (op (affineTest f))).hom y = similarityOnPoints G p x R f y :=
      (similarityRelativeIso_exists G p hNat x).choose_spec R f y
    change ((j (a * b)).hom.app (op (affineTest f))).hom c =
      ((j a).hom.app (op (affineTest f))).hom (((j b).hom.app (op (affineTest f))).hom c)
    rw [h, h, h]
    apply (p R).injective
    rw [similarityOnPoints_compare, similarityOnPoints_compare, similarityOnPoints_compare, map_mul,
      map_mul, MulAut.mul_apply]

theorem similarityRelativeAut_apply (a : RelatedSimilarities S)
    (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (b : Points G.val.X R) :
    ((similarityRelativeAut G p hNat a).asIso.hom.app (op (affineTest f))).hom b =
      similarityOnPoints G p a R f b :=
  (similarityRelativeIso_exists G p hNat a).choose_spec R f b

theorem similarityRelativeAut_scalar (a : Fin 3 → Sˣ) :
    similarityRelativeAut G p hNat (scalarSimilarity a) = 1 := by
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext G.property.1
  intro R f b
  change _ = b
  rw [similarityRelativeAut_apply]
  apply (p R).injective
  rw [similarityOnPoints_compare, relatedSimilarityBaseChange_scalar,
    similarityFrameAction_scalar, MulAut.one_apply]

set_option backward.isDefEq.respectTransparency false in
theorem similarityRelativeAut_onTriality
    (r : relatedTriples (R := S)) (g : Points G.val.X (CommAlgCat.of k S))
    (hg : (p (CommAlgCat.of k S) g).val = similarityOnModel (relatedTripleInclusion r)) :
    similarityRelativeAut G p hNat (relatedTripleInclusion r) = innerAut g := by
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext G.property.1
  intro R f b
  rw [similarityRelativeAut_apply]
  have he : (p R (mapPoints f g)).val =
      similarityOnModel (relatedSimilarityBaseChange f.hom.toRingHom (relatedTripleInclusion r)) := by
    apply modelMap_ext f.hom.toRingHom
    intro x
    rw [← hNat, hg, similarityOnModel_natural]
  change similarityOnPoints G p (relatedTripleInclusion r) R f b =
    mapPoints f g * b * (mapPoints f g)⁻¹
  apply (p R).injective
  apply Subtype.ext
  rw [similarityOnPoints_compare, map_mul, map_mul, map_inv]
  change MulAut.conj (similarityOnModel
      (relatedSimilarityBaseChange f.hom.toRingHom (relatedTripleInclusion r))) (p R b).val =
    (p R (mapPoints f g)).val * (p R b).val * (p R (mapPoints f g)).val⁻¹
  rw [he, MulAut.conj_apply]

end SimilarityRelativeConjugation

section ScalarDescent

open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open LinearAlgebraicGroups.Composition.Specification (zornUnit)

private theorem mapCoordinates_injective (f : R →+* T) (hf : Function.Injective f) :
    Function.Injective (mapCoordinates f) := by
  intro x y h
  apply (Zorn.coordinates R).injective
  have h' := congrArg (Zorn.coordinates T) h
  exact Prod.ext (hf (congrArg Prod.fst h'))
    (Prod.ext (funext fun i => hf (congrArg (fun a => a.2.1 i) h'))
      (Prod.ext (funext fun i => hf (congrArg (fun a => a.2.2.1 i) h'))
        (hf (congrArg (fun a => a.2.2.2) h'))))

private theorem mapCoordinates_one_hom (f : R →+* T) :
    mapCoordinates f (1 : Zorn R) = (1 : Zorn T) := by
  apply (Zorn.coordinates T).injective
  rw [Zorn.coordinates_one]
  simp [mapCoordinates, Zorn.coordinates_one, zornUnit, Function.comp_def, Pi.zero_def]

theorem relatedSimilarityBaseChange_injective (f : R →+* T) (hf : Function.Injective f) :
    Function.Injective (relatedSimilarityBaseChange f) := by
  intro a b h
  apply Subtype.ext
  apply Prod.ext
  · funext i
    apply LinearEquiv.ext
    intro x
    apply mapCoordinates_injective f hf
    rw [← relatedSimilarityBaseChange_apply, ← relatedSimilarityBaseChange_apply, h]
  · funext i
    apply Units.ext
    apply hf
    exact congrArg (fun a : RelatedSimilarities T => (a.val.2 i : T)) h

/-- Being a scalar similarity descends along an injective coefficient map.
The scalar and its inverse can be read from the first coordinate of a block
acting on the unit. -/
theorem relatedSimilarity_scalar_of_baseChange (f : R →+* T) (hf : Function.Injective f)
    (a : RelatedSimilarities R) (t : Fin 3 → Tˣ)
    (ht : relatedSimilarityBaseChange f a = scalarSimilarity t) :
    a ∈ (scalarSimilarity (R := R)).range := by
  let c (i : Fin 3) := (Zorn.coordinates R (a.val.1 i 1)).1
  have h (i : Fin 3) (x : Zorn R) :
      mapCoordinates f (a.val.1 i x) = (t i : T) • mapCoordinates f x := by
    rw [← relatedSimilarityBaseChange_apply, ht]
    exact scalarTriple_apply t i (mapCoordinates f x)
  have hc (i : Fin 3) : f (c i) = (t i : T) := by
    have hh := congrArg (fun x : Zorn T => (Zorn.coordinates T x).1) (h i 1)
    change f (c i) = (Zorn.coordinates T ((t i : T) • mapCoordinates f 1)).1 at hh
    simpa [mapCoordinates_one_hom, map_smul, Zorn.coordinates_one, zornUnit, smul_eq_mul] using hh
  have hs (i : Fin 3) (x : Zorn R) : a.val.1 i x = c i • x := by
    apply mapCoordinates_injective f hf
    rw [h, mapCoordinates_smul, hc]
  let d (i : Fin 3) := (Zorn.coordinates R ((a.val.1 i).symm 1)).1
  have hd (i : Fin 3) : c i * d i = 1 := by
    have hh := hs i ((a.val.1 i).symm 1)
    rw [LinearEquiv.apply_symm_apply] at hh
    have he := congrArg (fun x : Zorn R => (Zorn.coordinates R x).1) hh
    simpa [map_smul, Zorn.coordinates_one, zornUnit, smul_eq_mul, d] using he.symm
  let u (i : Fin 3) : Rˣ := ⟨c i, d i, hd i, (mul_comm _ _).trans (hd i)⟩
  refine ⟨u, relatedSimilarityBaseChange_injective f hf ?_⟩
  rw [relatedSimilarityBaseChange_scalar, ht]
  congr 1
  exact funext fun i => Units.ext (hc i)

end ScalarDescent

section ActualCentralKernel

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj BigOperators
open LinearAlgebraicGroups.Specs
open AutomorphismSequence (RelativeAut)
open RelativeFormComparison (fieldTest)
open OctonionEquivariantAutomorphisms (affineTest)

variable {k S : Type u} [Field k] [Field S] [Algebra k S]

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- In the relative automorphism scheme the kernel of similarity conjugation
is precisely the scalar torus. The proof uses the full centre on test
algebras after a faithfully flat factorization. -/
theorem similarityRelativeAut_kernel (G : AffineAlgebraicGroup k)
    (p : ∀ R : TestAlgebra k, Points G.val.X R ≃* frameStabilizer (R := R))
    (hp : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points G.val.X R) (x : Model R),
      mapModel f.hom.toRingHom ((p R a).val x) =
        (p T (mapPoints f a)).val (mapModel f.hom.toRingHom x))
    (hCentre : ∀ (R : TestAlgebra k) (g : Points G.val.X R), Centralizes (𝟙 G.val) g →
          ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((p R g).val x).2 1 = (c : R) • x.2 1)
    (a : RelatedSimilarities S) :
    similarityRelativeAut G p hp a = 1 ↔ a ∈ (scalarSimilarity (R := S)).range := by
  constructor
  · intro h
    obtain ⟨T, _, _, hT, r, t, ht⟩ := relatedCentralProduct_lift a
    let : Algebra k T := ((algebraMap S T).comp (algebraMap k S)).toAlgebra
    let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let R := CommAlgCat.of k T
    let f : CommAlgCat.of k S ⟶ R := CommAlgCat.ofHom (IsScalarTower.toAlgHom k S T)
    have hf : f.hom.toRingHom = algebraMap S T := rfl
    obtain ⟨e, he⟩ := Triality.frameTriality.{u} R
    let z := (p R).symm (e r)
    have hz : (p R z).val = similarityOnModel (relatedTripleInclusion r) :=
      (congrArg Subtype.val ((p R).apply_symm_apply _)).trans (similarityOnModel_triality e he r).symm
    have hcentral : Centralizes (𝟙 G.val) z := by
      apply (centralizes_iff_affinePoints G R z).mpr
      intro U g b
      have hh := congrArg
        (fun x : RelativeAut G.val (fieldTest k S) => (x.asIso.hom.app (op (affineTest (f ≫ g)))).hom b) h
      change ((similarityRelativeAut G p hp a).asIso.hom.app (op (affineTest (f ≫ g)))).hom b = b at hh
      rw [similarityRelativeAut_apply] at hh
      have hU : (p U (mapPoints g z)).val =
          similarityOnModel (relatedSimilarityBaseChange g.hom.toRingHom (relatedTripleInclusion r)) := by
        apply modelMap_ext g.hom.toRingHom
        intro x
        rw [← hp, hz, similarityOnModel_natural]
      have heq : relatedSimilarityBaseChange (f ≫ g).hom.toRingHom a =
          scalarSimilarity (fun i => Units.map g.hom.toRingHom.toMonoidHom (t i)) *
            relatedSimilarityBaseChange g.hom.toRingHom (relatedTripleInclusion r) := by
        calc
          _ = relatedSimilarityBaseChange g.hom.toRingHom
              (relatedSimilarityBaseChange f.hom.toRingHom a) :=
            (relatedSimilarityBaseChange_comp f.hom.toRingHom g.hom.toRingHom a).symm
          _ = _ := by
            rw [hf, ht]
            change relatedSimilarityBaseChange g.hom.toRingHom (scalarSimilarity t * relatedTripleInclusion r) = _
            rw [map_mul, relatedSimilarityBaseChange_scalar]
      have hcom := similarityOnPoints_compare G p a U (f ≫ g) b
      rw [hh, heq, map_mul, similarityFrameAction_scalar, one_mul] at hcom
      apply (p U).injective
      simp only [map_mul]
      apply Subtype.ext
      have hc := congrArg Subtype.val hcom
      change (p U b).val = similarityOnModel (relatedSimilarityBaseChange g.hom.toRingHom
          (relatedTripleInclusion r)) * (p U b).val *
            (similarityOnModel (relatedSimilarityBaseChange g.hom.toRingHom (relatedTripleInclusion r)))⁻¹ at hc
      rw [← hU] at hc
      exact mul_inv_eq_iff_eq_mul.mp hc.symm
    obtain ⟨c, hc, hprod, hscale⟩ := (splitFrameCentreScalars G p hp hCentre R z).mp hcentral
    have hr : relatedTripleInclusion r = scalarSimilarity c := by
      apply Subtype.ext
      apply Prod.ext
      · funext i
        apply LinearEquiv.ext
        intro x
        let y : Model R := (0, fun _ => x)
        have heq := LinearEquiv.congr_fun hz y
        rw [hscale, similarityOnModel_apply] at heq
        exact (congrArg (fun y : Model R => y.2 i) heq).symm
      · change 1 = scalarCompositionQuotient c
        exact ((scalarCompositionQuotient_kernel_iff c).mpr ⟨hc, hprod⟩).symm
    let : Module.FaithfullyFlat S T := hT
    apply relatedSimilarity_scalar_of_baseChange (algebraMap S T) (FaithfulSMul.algebraMap_injective S T) a (t * c)
    rw [ht, map_mul]
    change scalarSimilarity t * relatedTripleInclusion r = _
    rw [hr]
  · rintro ⟨s, rfl⟩
    exact similarityRelativeAut_scalar G p hp s

end ActualCentralKernel

end

end SimilarityConjugation

section AdjointFieldLifts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open AutomorphismSequence
open private projection_eq_one_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence
noncomputable section

variable {k S : Type u} [Field k] [Field S] [Algebra k S]
  {G : AffineAlgebraicGroup k}

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- A point of the central quotient has a lift over a field extension, by
taking a residue field of a point in the actual scheme fibre. -/
theorem adjointPoint_lifts_over_field (Q : AdjointQuotient G)
    (q : Points Q.quotient.val.X (CommAlgCat.of k S)) :
    ∃ (T : Type u) (_ : Field T) (_ : Algebra k T) (f : CommAlgCat.of k S ⟶ CommAlgCat.of k T)
      (g : Points G.val.X (CommAlgCat.of k T)),
      g ≫ Q.projection.hom.hom = mapPoints f q := by
  let S₀ := (testSpec k).obj (op (CommAlgCat.of k S))
  let X := pullback Q.projection.hom.hom q
  let a : X ⟶ G.val.X := pullback.fst _ _
  let b : X ⟶ S₀ := pullback.snd _ _
  have hpb := (IsPullback.of_hasPullback Q.projection.hom.hom q).map
    (Over.forget (Spec (CommRingCat.of k)))
  have hs : Surjective b.left := MorphismProperty.of_isPullback hpb Q.fppf.2.1
  obtain ⟨y, _⟩ := hs.1 (IsLocalRing.closedPoint S)
  let T := X.left.residueField y
  let p := X.left.fromSpecResidueField y
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (p ≫ b.left)
  let : Algebra S T := φ.hom.toAlgebra
  let : Algebra k T := (φ.hom.comp (algebraMap k S)).toAlgebra
  let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : CommAlgCat.of k S ⟶ CommAlgCat.of k T := CommAlgCat.ofHom (IsScalarTower.toAlgHom k S T)
  have hf : ((testSpec k).map f.op).left = p ≫ b.left := hφ
  have hp : p ≫ X.hom = ((testSpec k).obj (op (CommAlgCat.of k T))).hom := by
    rw [← Over.w b, ← Category.assoc, ← hf, Over.w]
  let x : (testSpec k).obj (op (CommAlgCat.of k T)) ⟶ X := Over.homMk p hp
  have hx : x ≫ b = (testSpec k).map f.op := Over.OverMorphism.ext hf.symm
  refine ⟨T, inferInstance, inferInstance, f, x ≫ a, ?_⟩
  rw [Category.assoc, show a ≫ Q.projection.hom.hom = b ≫ q
    from pullback.condition, ← Category.assoc, hx]

/-- The discrepancy of two lifts of the same adjoint point is a section
of the full scheme centre. -/
theorem adjointLift_ratio_central (Q : AdjointQuotient G)
    (R : TestAlgebra k) (a b : Points G.val.X R)
    (h : a ≫ Q.projection.hom.hom = b ≫ Q.projection.hom.hom) :
    Centralizes (𝟙 G.val) (a * b⁻¹) := by
  apply (LinearAlgebraicGroups.Descent.AutomorphismSequence.innerAut_eq_one_iff (a * b⁻¹)).mp
  apply (projection_eq_one_iff Q (a * b⁻¹)).mp
  rw [MonObj.mul_comp, GrpObj.inv_comp, h, mul_inv_cancel]

end

end AdjointFieldLifts


section TrialitarianAdjointCocycle

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence
open RelativeFormComparison (fieldTest transportedAut)
open LinearAlgebraicGroups.Descent.NonabelianCohomology (Cocycle pointAction)
open LinearAlgebraicGroups.Descent.Forms (SchemeModels)
open private innerComparison from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

noncomputable section

variable {k E S : Type u} [Field k] [Field E] [Field S]
  [Algebra k E] [Algebra k S] [Module.Finite k E] [IsSepClosure k S]

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- The given form has an adjoint-valued continuous cocycle relative to
the permutation-descended stabilizer of the marked cubic algebra. -/
theorem exists_trialitarianAdjointCocycle
    (cubic : Module.finrank k E = 3) (G : AffineAlgebraicGroup k)
    (D : DiagramPresentation G E S) :
    ∃ (J : AlbertModel k) (B : CubicStabilizer J E),
      IsPermutationDescent J B D.numbering ∧ Nonempty (FrameCharts J B D.numbering) ∧
      ∃ (Q : AdjointQuotient (stabilizerAffineModel B))
        (inn : groupSections Q.quotient.val ⟶ automorphisms B.stabilizer.group),
        (∀ (U : SchemeOver k) (g : U ⟶ B.stabilizer.group.X),
          inn.app (op U) ⟨g ≫ Q.projection.hom.hom⟩ = innerAut g) ∧
        (∀ U, Function.Injective (inn.app U)) ∧
        ∃ (i : relativePoints B.stabilizer.group (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
          (d : @Cocycle (Gal(S/k)) (Points Q.quotient.val.X (CommAlgCat.of k S))
            _ (krullTopology k S) _ ⊥ (pointAction k S Q.quotient.val.X)),
          ∀ σ, inn.app (op (fieldTest k S)) ⟨d σ⟩ = transportedAut k S i σ := by
  obtain ⟨J, B, hJ, hc, j, hj⟩ := exists_permutationReference_sameOuter cubic G D
  let M := stabilizerAffineModel B
  obtain ⟨Q⟩ := LinearAlgebraicGroups.Descent.AutomorphismSequence.adjointQuotient_exists M
  obtain ⟨inn, hinn, hinj⟩ := LinearAlgebraicGroups.Descent.AutomorphismSequence.adjointInner M Q
  let i := j.symm ≪≫ D.form
  have hRange : ∀ σ, transportedAut k S i σ ∈ (inn.app (op (fieldTest k S))).hom.range :=
    (innerComparison D.autSequence Q inn hinn hinj j D.form).mpr fun σ => (hj σ).symm
  obtain ⟨C⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.relativeFormClassification (S := S) M
  obtain ⟨e, _⟩ := LinearAlgebraicGroups.Descent.RelativeFormComparison.schemeIsomorphismComparison
    (k := k) (S := S) M.val G.val
  let G' : SchemeModels S M := ⟨G, ⟨e.symm i⟩⟩
  obtain ⟨a, ha, _⟩ := C.computes G' i
  obtain ⟨d, hd, _⟩ := LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.liftInnerCocycle
    M.val Q.quotient.val inn (hinj _) a (fun σ => ha σ ▸ hRange σ)
  exact ⟨J, B, hJ, hc, Q, inn, hinn, hinj, i, d, fun σ => (hd σ).trans (ha σ)⟩

end

end TrialitarianAdjointCocycle

section BrauerSplittingLayer

open _root_.Specs.RM03.CSA (isCentralSimple isSplit degree)
open _root_.RM03.Brauer (baseChangeMatrix baseChangeTower)
open scoped TensorProduct
noncomputable section

/-- Finite Galois descent data in a separable closure can be enlarged to a
layer that also splits the given central simple algebra. -/
theorem exists_splittingLayer_above {F S B : Type u} [Field F] [Field S] [Algebra F S]
    [IsSepClosure F S] [Ring B] [Algebra F B] (hB : isCentralSimple F B)
    (L₀ : FiniteGaloisIntermediateField F S) :
    ∃ L : FiniteGaloisIntermediateField F S, L₀ ≤ L ∧ isSplit L (L ⊗[F] B) := by
  obtain ⟨hn, _, K, _, _, _, _, ⟨e⟩⟩ := _root_.RM03.CSA.galois_splitting hB
  let : IsSepClosed S := IsSepClosure.sep_closed F
  let f : K →ₐ[F] S := IsSepClosed.lift
  let b := Module.finBasis F K
  let s := Set.range fun i => f (b i)
  let : Finite s := (Set.finite_range _).to_subtype
  let L₁ := FiniteGaloisIntermediateField.adjoin F s
  let L := L₀ ⊔ L₁
  have hmem (x : K) : f x ∈ L.toIntermediateField := by
    apply (show L₁ ≤ L from le_sup_right)
    rw [← b.sum_repr x, map_sum]
    apply L₁.toIntermediateField.toSubalgebra.sum_mem
    intro i _
    rw [map_smul]
    apply L₁.toIntermediateField.toSubalgebra.smul_mem
    exact FiniteGaloisIntermediateField.subset_adjoin F s ⟨i, rfl⟩
  let g : K →ₐ[F] L := f.codRestrict L.toIntermediateField.toSubalgebra hmem
  let : Algebra K L := g.toRingHom.toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  refine ⟨L, le_sup_left, degree F B, hn, ⟨?_⟩⟩
  let h : L ⊗[K] (K ⊗[F] B) ≃ₐ[L] L ⊗[K] Matrix (Fin (degree F B)) (Fin (degree F B)) K :=
    Algebra.TensorProduct.congr (.refl : L ≃ₐ[L] L) e
  exact (baseChangeTower F K L B).symm.trans (h.trans
    ((baseChangeMatrix K L (degree F B) K).trans (Algebra.TensorProduct.rid K L L).mapMatrix))

end

end BrauerSplittingLayer

section ProjectiveSimilarityDescent

open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open scoped TensorProduct Matrix
noncomputable section

private abbrev ZornIndex : Type u := ULift.{u} (Option (Fin 3) ⊕ Option (Fin 3))

private def liftedZornBasis (R : Type u) [CommRing R] : Module.Basis (ZornIndex.{u}) R (Zorn R) :=
  (Zorn.coordinateBasis R).reindex Equiv.ulift.symm

private theorem pairedFunctions_natural {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (x : Zorn R) (i : Option (Fin 3) ⊕ Option (Fin 3)) :
    Zorn.pairedFunctions T (mapCoordinates f x) i = f (Zorn.pairedFunctions R x i) := by
  rcases x with ⟨a,u,v,b⟩
  rcases i with i | i <;> cases i
  · rfl
  · rfl
  · rfl
  · exact (f.map_neg _).symm

private theorem liftedZornRepr_natural {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (x : Zorn R) (i : ZornIndex.{u}) :
    (liftedZornBasis T).repr (mapCoordinates f x) i = f ((liftedZornBasis R).repr x i) := by
  rw [liftedZornBasis, Module.Basis.repr_reindex_apply, liftedZornBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun T _).repr (Zorn.pairedFunctions T (mapCoordinates f x))) i.down =
    f (((Pi.basisFun R _).repr (Zorn.pairedFunctions R x)) i.down)
  simpa only [Pi.basisFun_repr] using pairedFunctions_natural f x i.down

private theorem liftedZornBasis_natural {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (i : ZornIndex.{u}) :
    mapCoordinates f (liftedZornBasis R i) = liftedZornBasis T i := by
  apply (liftedZornBasis T).repr.injective
  ext j
  rw [liftedZornRepr_natural, Module.Basis.repr_self, Module.Basis.repr_self]
  by_cases h : j = i <;> simp [h]

private def zornGL (R : Type u) [CommRing R] :
    (Zorn R ≃ₗ[R] Zorn R) ≃* (Matrix (ZornIndex.{u}) ZornIndex.{u} R)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Zorn R)).symm.trans
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (liftedZornBasis R)).toMulEquiv)

private theorem zornGL_val {R : Type u} [CommRing R] (a : Zorn R ≃ₗ[R] Zorn R) :
    (zornGL R a).val = LinearMap.toMatrixAlgEquiv (liftedZornBasis R) a.toLinearMap := rfl

private theorem zornGL_baseChange {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (a : Zorn R ≃ₗ[R] Zorn R) :
    (zornGL T (zornLinearBaseChange f a)).val = (zornGL R a).val.map f := by
  ext i j
  simp only [zornGL_val, LinearMap.toMatrixAlgEquiv_apply, Matrix.map_apply, LinearEquiv.coe_coe]
  rw [← liftedZornBasis_natural f j, zornLinearBaseChange_apply, liftedZornRepr_natural]

private theorem zornGL_smul {R : Type u} [CommRing R] (t : Rˣ) (a : Zorn R ≃ₗ[R] Zorn R) :
    (zornGL R ((LinearEquiv.smulOfUnit t) * a)).val = (t : R) • (zornGL R a).val := by
  ext i j
  simp only [zornGL_val, LinearMap.toMatrixAlgEquiv_apply, Matrix.smul_apply,
    LinearEquiv.coe_coe, LinearEquiv.mul_apply]
  change (liftedZornBasis R).repr ((t : R) • a (liftedZornBasis R j)) i =
    (t : R) • (liftedZornBasis R).repr (a (liftedZornBasis R j)) i
  rw [map_smul, Finsupp.smul_apply]

open Algebra.TensorProduct

/-- Projective descent of a Peirce block supplies a linear representative over
the base field and a scalar relating it to the lifted block. -/
theorem zornLinearRepresentative_descends {K T : Type u} [Field K] [Field T] [Algebra K T]
    (a : Zorn T ≃ₗ[T] Zorn T)
    (h : ∃ c : (T ⊗[K] T)ˣ,
      zornLinearBaseChange (includeLeftRingHom : T →+* T ⊗[K] T) a =
        LinearEquiv.smulOfUnit c *
          zornLinearBaseChange (includeRight.toRingHom : T →+* T ⊗[K] T) a) :
    ∃ (b : Zorn K ≃ₗ[K] Zorn K) (c : Tˣ),
      a = LinearEquiv.smulOfUnit c * zornLinearBaseChange (algebraMap K T) b := by
  obtain ⟨c, hc⟩ := h
  have hmap := congrArg (fun z => (zornGL (T ⊗[K] T) z).val) hc
  rw [zornGL_baseChange, zornGL_smul, zornGL_baseChange] at hmap
  obtain ⟨B, b, hB⟩ := matrixRepresentative_descends (K := K) (zornGL T a) ⟨c, hmap⟩
  let v := (zornGL K).symm B
  refine ⟨v, b, (zornGL T).injective (Units.ext ?_)⟩
  rw [zornGL_smul, zornGL_baseChange, MulEquiv.apply_symm_apply, ← hB]

open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open LinearAlgebraicGroups.Composition.AdjointSpecification (conjugate)
open LinearAlgebraicGroups.Albert.HermitianSpecification (cyclicNext cyclicPrev)

private theorem zornLinearBaseChange_comp {R T U : Type u} [CommRing R] [CommRing T]
    [CommRing U] (f : R →+* T) (g : T →+* U) (a : Zorn R ≃ₗ[R] Zorn R) :
    zornLinearBaseChange g (zornLinearBaseChange f a) = zornLinearBaseChange (g.comp f) a := by
  apply zornMap_ext (g.comp f)
  intro x
  rw [← mapCoordinates_comp_hom f g, zornLinearBaseChange_apply, zornLinearBaseChange_apply,
    mapCoordinates_comp_hom, mapCoordinates_comp_hom, zornLinearBaseChange_apply]

private theorem similarity_blocks_injective {R : Type u} [CommRing R] :
    Function.Injective (fun a : RelatedSimilarities R => a.val.1) := by
  intro a b h
  apply Subtype.ext
  refine Prod.ext h (funext fun i => Units.ext ?_)
  let x := (b.val.1 (cyclicNext i)).symm 1
  let y := (b.val.1 (cyclicPrev i)).symm 1
  have hb := b.property.2 i x y
  have ha := a.property.2 i x y
  change a.val.1 i (conjugate (norm R) (x * y)) = (a.val.2 i : R) •
    conjugate (norm R) (a.val.1 (cyclicNext i) x * a.val.1 (cyclicPrev i) y) at ha
  change a.val.1 = b.val.1 at h
  rw [h] at ha
  have hunit : conjugate (norm R) (b.val.1 (cyclicNext i) x * b.val.1 (cyclicPrev i) y) = 1 := by
    change conjugate (norm R) (b.val.1 (cyclicNext i) ((b.val.1 (cyclicNext i)).symm 1) *
      b.val.1 (cyclicPrev i) ((b.val.1 (cyclicPrev i)).symm 1)) = 1
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, mul_one]
    exact Composition.conjugate_one zornNormLaws
  apply scalar_eq_of_smul_zorn_one
  rw [← hunit, ← ha]
  exact hb

private theorem relatedSimilarity_of_baseChange {K T : Type u} [Field K] [Field T]
    (f : K →+* T) (a : RelatedSimilarities T) (v : Triple K) (w : Fin 3 → Kˣ)
    (hv : ∀ i, zornLinearBaseChange f (v i) = a.val.1 i)
    (hw : ∀ i, Units.map f.toMonoidHom (w i) = a.val.2 i) :
    ∃ b : RelatedSimilarities K, relatedSimilarityBaseChange f b = a := by
  have hn (i : Fin 3) : f (quotientNormMultiplier w i : K) = (quotientNormMultiplier a.val.2 i : T) := by
    change (Units.map f.toMonoidHom (quotientNormMultiplier w i) : T) = _
    unfold quotientNormMultiplier
    rw [map_inv, map_mul, hw, hw]
  have hb : (v, w) ∈ relatedSimilarities := by
    constructor
    · intro i x
      apply f.injective
      rw [map_mul, hn]
      have hq := a.property.1 i (mapCoordinates f x)
      rw [← hv, zornLinearBaseChange_apply, Composition.Zorn.mapCoordinates_norm,
        Composition.Zorn.mapCoordinates_norm] at hq
      exact hq
    · intro i x y
      apply mapCoordinates_injective f f.injective
      have hxy := a.property.2 i (mapCoordinates f x) (mapCoordinates f y)
      change a.val.1 i (conjugate (norm T) (mapCoordinates f x * mapCoordinates f y)) =
        (a.val.2 i : T) • conjugate (norm T)
          (a.val.1 (cyclicNext i) (mapCoordinates f x) *
           a.val.1 (cyclicPrev i) (mapCoordinates f y)) at hxy
      rw [← hv, ← hv, ← hv, ← Composition.Zorn.mapCoordinates_mul, ← mapCoordinates_conjugate,
        zornLinearBaseChange_apply, zornLinearBaseChange_apply, zornLinearBaseChange_apply,
        ← Composition.Zorn.mapCoordinates_mul, ← mapCoordinates_conjugate, ← hw] at hxy
      rw [mapCoordinates_smul, hxy]
      rfl
  refine ⟨⟨(v,w), hb⟩, ?_⟩
  apply similarity_blocks_injective
  exact funext hv

/-- Projectively compatible related similarities have a related-similarity
representative over the base field. The composition factors descend with
the normalized block maps. -/
theorem relatedSimilarityRepresentative_descends {K T : Type u} [Field K] [Field T] [Algebra K T]
    (a : RelatedSimilarities T)
    (h : ∀ i, ∃ c : (T ⊗[K] T)ˣ,
      zornLinearBaseChange (includeLeftRingHom : T →+* T ⊗[K] T) (a.val.1 i) =
        LinearEquiv.smulOfUnit c *
          zornLinearBaseChange (includeRight.toRingHom : T →+* T ⊗[K] T) (a.val.1 i)) :
    ∃ (b : RelatedSimilarities K) (t : Fin 3 → Tˣ),
      a = scalarSimilarity t * relatedSimilarityBaseChange (algebraMap K T) b := by
  choose v t ht using fun i => zornLinearRepresentative_descends (a.val.1 i) (h i)
  let f : K →+* T := algebraMap K T
  let a₀ := scalarSimilarity t⁻¹ * a
  have ha (i : Fin 3) : a₀.val.1 i = zornLinearBaseChange f (v i) := by
    apply LinearEquiv.ext
    intro x
    change scalarTriple t⁻¹ i (a.val.1 i x) = zornLinearBaseChange f (v i) x
    rw [ht, scalarTriple_apply]
    change (↑((t i)⁻¹) : T) • ((t i : T) • zornLinearBaseChange f (v i) x) = _
    rw [smul_smul, Units.inv_mul, one_smul]
  let l : T →+* T ⊗[K] T := includeLeftRingHom
  let r : T →+* T ⊗[K] T := includeRight.toRingHom
  have hlr : l.comp f = r.comp f := by
    ext x
    exact ((includeLeft : T →ₐ[K] T ⊗[K] T).commutes x).trans
      ((includeRight : T →ₐ[K] T ⊗[K] T).commutes x).symm
  have hpair : relatedSimilarityBaseChange l a₀ = relatedSimilarityBaseChange r a₀ := by
    apply similarity_blocks_injective
    funext i
    change zornLinearBaseChange l (a₀.val.1 i) = zornLinearBaseChange r (a₀.val.1 i)
    rw [ha, zornLinearBaseChange_comp, zornLinearBaseChange_comp, hlr]
  have heff := Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (Algebra.IsEffective.of_faithfullyFlat K T)
  have hscalar (i : Fin 3) : ∃ w : Kˣ, Units.map f.toMonoidHom w = a₀.val.2 i := by
    have he := congrArg (fun a : RelatedSimilarities (T ⊗[K] T) => (a.val.2 i : T ⊗[K] T)) hpair
    have hmem : (a₀.val.2 i : T) ∈ Set.range f := by
      rw [← heff]
      exact he
    obtain ⟨w, hw⟩ := hmem
    have hnz : w ≠ 0 := fun hz => Units.ne_zero (a₀.val.2 i) (by rw [← hw, hz, map_zero])
    exact ⟨Units.mk0 w hnz, Units.ext hw⟩
  choose w hw using hscalar
  obtain ⟨b, he⟩ := relatedSimilarity_of_baseChange f a₀ v w (fun i => (ha i).symm) hw
  refine ⟨b, t, ?_⟩
  change a = scalarSimilarity t * relatedSimilarityBaseChange f b
  rw [he]
  change a = scalarSimilarity t * (scalarSimilarity t⁻¹ * a)
  rw [map_inv, mul_inv_cancel_left]

end

end ProjectiveSimilarityDescent

section ReferenceSimilarities

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj BigOperators TensorProduct
open LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence
open RelativeFormComparison (fieldTest fieldMap automorphismAction)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Composition.ZornSpecification (mapCoordinates)
open OctonionEquivariantAutomorphisms (affineTest)
open private relativeHom_ext restrictIso_affine_apply
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.OctonionEquivariantAutomorphisms

noncomputable section


variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
  {J : AlbertModel k} {B : CubicStabilizer J E} {numbering : (E →ₐ[k] S) ≃ Fin 3}

/-- A split frame comparison retaining the action on the Peirce modules. -/
private structure SplitFrameComparison (C : FrameCharts J B numbering) where
  group : AffineAlgebraicGroup k
  points : ∀ R : TestAlgebra k, Points group.val.X R ≃* frameStabilizer (R := R)
  natural : ∀ {R T : TestAlgebra k} (f : R ⟶ T) (a : Points group.val.X R) (x : Model R),
    mapModel f.hom.toRingHom ((points R a).val x) =
      (points T (mapPoints f a)).val (mapModel f.hom.toRingHom x)
  centre : ∀ (R : TestAlgebra k) (g : Points group.val.X R), Centralizes (𝟙 group.val) g →
    ∃ c : Rˣ, c ^ 2 = 1 ∧ ∀ x : Model R, ((points R g).val x).2 1 = (c : R) • x.2 1
  iso : relativePoints group.val (fieldTest k S) ≅
    relativePoints B.stabilizer.group (fieldTest k S)
  computes : ∀ (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R)
    (b : Points group.val.X R) (x : R ⊗[k] J.V),
    (points R b).val (FrameCharts.chart C R f x) =
      FrameCharts.chart C R f (cubicStabilizerAction B R ((iso.hom.app (op (affineTest f))).hom b) x)

private theorem exists_splitFrameComparison [Module.Finite k E]
    (C : FrameCharts J B numbering) (cubic : Module.finrank k E = 3) :
    Nonempty (SplitFrameComparison C) := by
  obtain ⟨G, a, ha, _, _, _, T, d, hd, _, _, hZ, _, _⟩ :=
    LinearAlgebraicGroups.Albert.SpinWeights.fieldStructure.{u} k
  obtain ⟨p, hp, hz⟩ := splitSpinFramePoints G a ha
  obtain ⟨i, hi⟩ := cubicStabilizerRelativeFrameIso B numbering C cubic G p hp
  exact ⟨⟨G, p, hp, hz T d hd hZ, i, hi⟩⟩

variable {C : FrameCharts J B numbering} (A : SplitFrameComparison C)

private def referenceFramePoints (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) :
    Points B.stabilizer.group.X R ≃* frameStabilizer (R := R) :=
  ((A.iso.app (op (affineTest f))).groupIsoToMulEquiv.symm).trans (A.points R)

private theorem referenceFramePoints_apply (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R)
    (b : Points B.stabilizer.group.X R) (x : R ⊗[k] J.V) :
    (referenceFramePoints A R f b).val (FrameCharts.chart C R f x) =
      FrameCharts.chart C R f (cubicStabilizerAction B R b x) := by
  let e : Points A.group.val.X R ≃* Points B.stabilizer.group.X R :=
    (A.iso.app (op (affineTest f))).groupIsoToMulEquiv
  have h := A.computes R f (e.symm b) x
  change (A.points R (e.symm b)).val (FrameCharts.chart C R f x) =
    FrameCharts.chart C R f (cubicStabilizerAction B R (e (e.symm b)) x) at h
  rw [e.apply_symm_apply] at h
  exact h

private theorem referenceFramePoints_natural {R T : TestAlgebra k}
    (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T) (b : Points B.stabilizer.group.X R) (x : Model R) :
    mapModel g.hom.toRingHom ((referenceFramePoints A R f b).val x) =
      (referenceFramePoints A T (f ≫ g) (mapPoints g b)).val (mapModel g.hom.toRingHom x) := by
  obtain ⟨x, rfl⟩ := (FrameCharts.chart C R f).surjective x
  rw [referenceFramePoints_apply, FrameCharts.natural C, FrameCharts.natural C, referenceFramePoints_apply,
    cubicStabilizerAction_natural]

set_option backward.isDefEq.respectTransparency false in
private theorem referenceFramePoints_centre (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R)
    (b : Points B.stabilizer.group.X R) (hb : Centralizes (𝟙 B.stabilizer.group) b) :
    ∃ t : Fin 3 → Rˣ, (∀ i, t i ^ 2 = 1) ∧ (∏ i, t i) = 1 ∧
      ∀ x : Model R, (referenceFramePoints A R f b).val x = (x.1, fun i => (t i : R) • x.2 i) := by
  let z := (A.points R).symm (referenceFramePoints A R f b)
  have hz : A.points R z = referenceFramePoints A R f b := (A.points R).apply_symm_apply _
  have hZ : Centralizes (𝟙 A.group.val) z := by
    apply (centralizes_iff_affinePoints A.group R z).mpr
    intro T g y
    have ht : A.points T (mapPoints g z) =
        referenceFramePoints A T (f ≫ g) (mapPoints g b) := by
      apply Subtype.ext
      apply modelMap_ext g.hom.toRingHom
      intro x
      rw [← A.natural, hz, referenceFramePoints_natural]
    obtain ⟨w, hw⟩ := (referenceFramePoints A T (f ≫ g)).surjective (A.points T y)
    have hm := (centralizes_iff_affinePoints (stabilizerAffineModel B) R b).mp hb T g w
    apply (A.points T).injective
    rw [map_mul, map_mul, ht, ← hw]
    exact (hm.map (referenceFramePoints A T (f ≫ g))).eq
  obtain ⟨t, ht, hprod, hact⟩ :=
    (splitFrameCentreScalars A.group A.points A.natural A.centre R z).mp hZ
  exact ⟨t, ht, hprod, fun x => (congrArg (fun g : frameStabilizer (R := R) => g.val x) hz).symm.trans (hact x)⟩

private def referenceSimilarityAut :
    RelatedSimilarities S →* RelativeAut B.stabilizer.group (fieldTest k S) :=
  (Aut.autMulEquivOfIso A.iso).toMonoidHom.comp
    (similarityRelativeAut A.group A.points A.natural)

private theorem referenceSimilarityAut_kernel (a : RelatedSimilarities S) :
    referenceSimilarityAut A a = 1 ↔ a ∈ (scalarSimilarity (R := S)).range := by
  rw [← similarityRelativeAut_kernel A.group A.points A.natural A.centre a]
  change Aut.autMulEquivOfIso A.iso (similarityRelativeAut A.group A.points A.natural a) = 1 ↔ _
  rw [← (Aut.autMulEquivOfIso A.iso).map_one, (Aut.autMulEquivOfIso A.iso).injective.eq_iff]

set_option backward.isDefEq.respectTransparency false in
private theorem referenceSimilarityAut_apply (a : RelatedSimilarities S) (R : TestAlgebra k)
    (f : CommAlgCat.of k S ⟶ R) (b : Points B.stabilizer.group.X R) :
    referenceFramePoints A R f (((referenceSimilarityAut A a).asIso.hom.app (op (affineTest f))).hom b) =
      similarityFrameAction (relatedSimilarityBaseChange f.hom.toRingHom a) (referenceFramePoints A R f b) := by
  let U := op (affineTest f)
  let e : Points A.group.val.X R ≃* Points B.stabilizer.group.X R :=
    (A.iso.app U).groupIsoToMulEquiv
  let h := similarityRelativeAut A.group A.points A.natural a
  change A.points R (e.symm (e ((h.asIso.hom.app U).hom (e.symm b)))) =
    similarityFrameAction _ (A.points R (e.symm b))
  rw [e.symm_apply_apply]
  exact (congrArg (A.points R) (similarityRelativeAut_apply A.group A.points A.natural a R f (e.symm b))).trans
    (similarityOnPoints_compare A.group A.points a R f (e.symm b))

private theorem referenceFramePoints_permutation (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R)
    (σ : Gal(S/k)) (b : Points B.stabilizer.group.X R) :
    referenceFramePoints A R f b = frameStabilizerPermutation (diagramPermutation numbering σ)
      (referenceFramePoints A R (CommAlgCat.ofHom σ.toAlgHom ≫ f) b) := by
  let f' := CommAlgCat.ofHom σ.toAlgHom ≫ f
  let π := diagramPermutation numbering σ
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := ((FrameCharts.chart C R f').trans (framePermutation π)).surjective x
  change (referenceFramePoints A R f b).val (framePermutation π (FrameCharts.chart C R f' x)) =
    (frameStabilizerPermutation π (referenceFramePoints A R f' b)).val
      (framePermutation π (FrameCharts.chart C R f' x))
  rw [frameStabilizerPermutation_apply, ← FrameCharts.permutation C R f σ x, referenceFramePoints_apply,
    referenceFramePoints_apply, FrameCharts.permutation C R f σ (cubicStabilizerAction B R b x)]

private theorem similarityOnModel_transport {R T : Type u} [CommRing R] [CommRing T]
    (f : R ≃+* T) (π : Equiv.Perm (Fin 3)) (a : RelatedSimilarities R) (x : Model R) :
    similarityOnModel (transportSimilarities f π a) (framePermutation π (mapModel f.toRingHom x)) =
      framePermutation π (mapModel f.toRingHom (similarityOnModel a x)) := by
  apply Prod.ext
  · funext j
    obtain ⟨i, rfl⟩ := π.surjective j
    change (framePermutation π (mapModel f.toRingHom x)).1 (π i) = _
    rw [framePermutation_diagonal, framePermutation_diagonal]
    rfl
  · funext j
    obtain ⟨i, rfl⟩ := π.surjective j
    change (transportSimilarities f π a).val.1 (π i)
      ((framePermutation π (mapModel f.toRingHom x)).2 (π i)) =
      (framePermutation π (mapModel f.toRingHom (similarityOnModel a x))).2 (π i)
    rw [framePermutation_block, framePermutation_block]
    change (transportSimilarities f π a).val.1 (π i)
      (blockPermutation π (mapCoordinates f.toRingHom (x.2 i))) =
      blockPermutation π (mapCoordinates f.toRingHom (a.val.1 i (x.2 i)))
    rw [← mapCoordinates_blockPermutation, ← mapCoordinates_blockPermutation]
    exact transportSimilarities_action f π a i (x.2 i)

private theorem similarityFrameAction_transport {R T : Type u} [CommRing R] [CommRing T]
    (f : R ≃+* R) (π : Equiv.Perm (Fin 3)) (g : R →+* T)
    (a : RelatedSimilarities R) (b : frameStabilizer (R := T)) :
    similarityFrameAction (relatedSimilarityBaseChange g (transportSimilarities f π a))
      (frameStabilizerPermutation π b) =
      frameStabilizerPermutation π
        (similarityFrameAction (relatedSimilarityBaseChange (g.comp f.toRingHom) a) b) := by
  let z := framePermutation (R := T) π
  let a₁ := similarityOnModel (relatedSimilarityBaseChange g (transportSimilarities f π a))
  let a₂ := similarityOnModel (relatedSimilarityBaseChange (g.comp f.toRingHom) a)
  have h : a₁ * z = z * a₂ := by
    apply modelMap_ext (g.comp f.toRingHom)
    intro x
    change a₁ (z (mapModel (g.comp f.toRingHom) x)) = z (a₂ (mapModel (g.comp f.toRingHom) x))
    change similarityOnModel _ (framePermutation π (mapModel (g.comp f.toRingHom) x)) =
      framePermutation π (similarityOnModel _ (mapModel (g.comp f.toRingHom) x))
    conv_lhs =>
      rw [mapModel_comp, ← framePermutation_natural, ← similarityOnModel_natural,
        similarityOnModel_transport, framePermutation_natural, ← mapModel_comp, similarityOnModel_natural]
  have ha : a₁ = z * a₂ * z⁻¹ := (eq_mul_inv_iff_mul_eq).2 h
  apply Subtype.ext
  change a₁ * (z * b.val * z⁻¹) * a₁⁻¹ = z * (a₂ * b.val * a₂⁻¹) * z⁻¹
  rw [ha]
  group

set_option backward.isDefEq.respectTransparency false in
private theorem referenceSimilarityAut_equivariant (σ : Gal(S/k)) (a : RelatedSimilarities S) :
    referenceSimilarityAut A (relatedSimilarityAction (diagramPermutation numbering) σ a) =
      automorphismAction k S B.stabilizer.group σ (referenceSimilarityAut A a) := by
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext (stabilizerAffineModel B).property.1
  intro R f b
  let f' := CommAlgCat.ofHom σ.toAlgHom ≫ f
  let π := diagramPermutation numbering σ
  let h := referenceSimilarityAut A a
  change (((referenceSimilarityAut A (relatedSimilarityAction (diagramPermutation numbering) σ a)).asIso.hom.app
      (op (affineTest f))).hom b) = (((restrictIso (fieldMap k S σ) h.asIso).hom.app (op (affineTest f))).hom b)
  rw [restrictIso_affine_apply]
  apply (referenceFramePoints A R f).injective
  conv_rhs => rw [referenceFramePoints_permutation A R f σ]
  rw [referenceSimilarityAut_apply, referenceSimilarityAut_apply, referenceFramePoints_permutation A R f σ b]
  exact similarityFrameAction_transport σ.toRingEquiv π f.hom.toRingHom a (referenceFramePoints A R f' b)

/-- Extending the coefficients commutes with transport for compatible maps
of the coefficient rings. -/
private theorem transportSimilarities_baseChange {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (g : R ≃+* R) (h : T ≃+* T) (hf : f.comp g.toRingHom = h.toRingHom.comp f)
    (π : Equiv.Perm (Fin 3)) (a : RelatedSimilarities R) :
    relatedSimilarityBaseChange f (transportSimilarities g π a) =
      transportSimilarities h π (relatedSimilarityBaseChange f a) := by
  have hn (x : Zorn R) : mapCoordinates f (transportZorn g π x) = transportZorn h π (mapCoordinates f x) := by
    rw [transportZorn_apply, transportZorn_apply, ← mapCoordinates_blockPermutation,
      mapCoordinates_comp_hom, mapCoordinates_comp_hom, hf]
  apply similarity_blocks_injective
  funext j
  obtain ⟨i, rfl⟩ := π.surjective j
  apply zornMap_ext f
  intro x
  obtain ⟨x, rfl⟩ := (transportZorn g π).surjective x
  change (relatedSimilarityBaseChange f (transportSimilarities g π a)).val.1 (π i)
      (mapCoordinates f (transportZorn g π x)) =
    (transportSimilarities h π (relatedSimilarityBaseChange f a)).val.1 (π i)
      (mapCoordinates f (transportZorn g π x))
  rw [relatedSimilarityBaseChange_apply, transportSimilarities_action, hn, hn,
    transportSimilarities_action, relatedSimilarityBaseChange_apply]

open Algebra.TensorProduct
open private mapPoints_injective_of_affine
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRootRelations

private theorem affineTest_comp {T R : TestAlgebra k}
    (f : CommAlgCat.of k S ⟶ T) (g : T ⟶ R) :
    (testSpec k).map g.op ≫ (affineTest f).hom = (affineTest (f ≫ g)).hom := by
  change (testSpec k).map g.op ≫ (testSpec k).map f.op = (testSpec k).map (f ≫ g).op
  rw [op_comp, Functor.map_comp]

private theorem mapPoints_comp_apply {X : SchemeOver k} {R T U : TestAlgebra k}
    (f : R ⟶ T) (g : T ⟶ U) (b : Points X R) :
    mapPoints (f ≫ g) b = mapPoints g (mapPoints f b) := by
  change (testSpec k).map (f ≫ g).op ≫ b = (testSpec k).map g.op ≫ (testSpec k).map f.op ≫ b
  rw [op_comp, Functor.map_comp, Category.assoc]

private theorem relativeAut_affine_natural {M : GroupScheme k} (a : RelativeAut M (fieldTest k S))
    {R T : TestAlgebra k} (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T) (b : Points M.X R) :
    (a.asIso.hom.app (op (affineTest (f ≫ g)))).hom (mapPoints g b) =
      mapPoints g ((a.asIso.hom.app (op (affineTest f))).hom b) := by
  let m : affineTest (f ≫ g) ⟶ affineTest f :=
    Over.homMk ((testSpec k).map g.op) (affineTest_comp f g)
  exact ConcreteCategory.congr_hom (a.asIso.hom.naturality m.op) b

set_option backward.isDefEq.respectTransparency false in
/-- An equality of relative automorphisms can be checked after a field
extension, by testing over the tensor product of each affine test ring. -/
private theorem relativeAut_eq_afterFieldExtension {T : Type u} [Field T] [Algebra k T]
    (M : AffineAlgebraicGroup k) (f : CommAlgCat.of k S ⟶ CommAlgCat.of k T)
    {a b : RelativeAut M.val (fieldTest k S)}
    (h : ∀ (R : TestAlgebra k) (g : CommAlgCat.of k T ⟶ R) (x : Points M.val.X R),
      (a.asIso.hom.app (op (affineTest (f ≫ g)))).hom x =
        (b.asIso.hom.app (op (affineTest (f ≫ g)))).hom x) : a = b := by
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext M.property.1
  intro R g x
  let : Algebra S R := g.hom.toRingHom.toAlgebra
  let : IsScalarTower k S R := IsScalarTower.of_algebraMap_eq fun x => (g.hom.commutes x).symm
  let : Algebra S T := f.hom.toRingHom.toAlgebra
  let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
  let l : R →ₐ[S] R ⊗[S] T := includeLeft
  let r : T →ₐ[S] R ⊗[S] T := includeRight
  let U := CommAlgCat.of k (R ⊗[S] T)
  let l' : R ⟶ U := CommAlgCat.ofHom (l.restrictScalars k)
  let r' : CommAlgCat.of k T ⟶ U := CommAlgCat.ofHom (r.restrictScalars k)
  have hl : Function.Injective l'.hom :=
    includeLeft_injective (S := S) (algebraMap S T).injective
  have hcomm : f ≫ r' = g ≫ l' := by
    apply CommAlgCat.hom_ext
    ext x
    exact (r.commutes x).trans (l.commutes x).symm
  apply mapPoints_injective_of_affine M.property.1 l' hl
  rw [← relativeAut_affine_natural, ← relativeAut_affine_natural, ← hcomm]
  exact h U r' (mapPoints l' x)

private theorem referenceFramePoints_baseChange {R T : TestAlgebra k}
    (f : CommAlgCat.of k S ⟶ R) (g : R ⟶ T) (x : Points B.stabilizer.group.X R)
    (a : RelatedSimilarities R) (hx : (referenceFramePoints A R f x).val = similarityOnModel a) :
    (referenceFramePoints A T (f ≫ g) (mapPoints g x)).val =
      similarityOnModel (relatedSimilarityBaseChange g.hom.toRingHom a) := by
  apply modelMap_ext g.hom.toRingHom
  intro v
  rw [← referenceFramePoints_natural, hx, similarityOnModel_natural]

set_option backward.isDefEq.respectTransparency false in
private theorem relativeInner_apply_of_lift {M : AffineAlgebraicGroup k} (Q : AdjointQuotient M)
    (inn : groupSections Q.quotient.val ⟶ automorphisms M.val)
    (hinn : ∀ (U : SchemeOver k) (b : U ⟶ M.val.X),
      inn.app (op U) ⟨b ≫ Q.projection.hom.hom⟩ = innerAut b)
    (d : Points Q.quotient.val.X (CommAlgCat.of k S))
    (R : TestAlgebra k) (f : CommAlgCat.of k S ⟶ R) (y z : Points M.val.X R)
    (hy : y ≫ Q.projection.hom.hom = mapPoints f d) :
    ((inn.app (op (fieldTest k S)) ⟨d⟩).asIso.hom.app (op (affineTest f))).hom z = y * z * y⁻¹ := by
  let U := (testSpec k).obj (op R)
  let m := (testSpec k).map f.op
  have h := NatTrans.naturality_apply inn m.op ⟨d⟩
  change inn.app (op U) ⟨mapPoints f d⟩ =
    restrictAut m (inn.app (op (fieldTest k S)) ⟨d⟩) at h
  rw [← hy, hinn] at h
  have hh := congrArg (fun a : RelativeAut M.val U => (a.asIso.hom.app (op (Over.mk (𝟙 U)))).hom z) h.symm
  change ((inn.app (op (fieldTest k S)) ⟨d⟩).asIso.hom.app (op (Over.mk (𝟙 U ≫ m)))).hom z =
    (𝟙 U ≫ y) * z * (𝟙 U ≫ y)⁻¹ at hh
  rw [Category.id_comp, Category.id_comp] at hh
  exact hh

private theorem referenceFramePoints_compareSimilarity {R : TestAlgebra k}
    (f : CommAlgCat.of k S ⟶ R) (a : RelatedSimilarities S)
    (y z : Points B.stabilizer.group.X R) (t : Fin 3 → Rˣ)
    (hy : (referenceFramePoints A R f y).val =
      similarityOnModel (scalarSimilarity t * relatedSimilarityBaseChange f.hom.toRingHom a)) :
    ((referenceSimilarityAut A a).asIso.hom.app (op (affineTest f))).hom z = y * z * y⁻¹ := by
  apply (referenceFramePoints A R f).injective
  rw [referenceSimilarityAut_apply, map_mul, map_mul, map_inv]
  apply Subtype.ext
  change _ = (referenceFramePoints A R f y).val * (referenceFramePoints A R f z).val *
    ((referenceFramePoints A R f y).val)⁻¹
  simp only [hy]
  change _ = (similarityFrameAction (scalarSimilarity t * relatedSimilarityBaseChange f.hom.toRingHom a)
    (referenceFramePoints A R f z)).val
  rw [map_mul, similarityFrameAction_scalar, one_mul]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- The actual adjoint point has a representative by related similarities.
The central ratio of its two lifts is tested over the full tensor square. -/
private theorem exists_referenceSimilarityLift
    (Q : AdjointQuotient (stabilizerAffineModel B))
    (inn : groupSections Q.quotient.val ⟶ automorphisms B.stabilizer.group)
    (hinn : ∀ (U : SchemeOver k) (b : U ⟶ B.stabilizer.group.X),
      inn.app (op U) ⟨b ≫ Q.projection.hom.hom⟩ = innerAut b)
    (d : Points Q.quotient.val.X (CommAlgCat.of k S)) :
    ∃ a : RelatedSimilarities S,
      referenceSimilarityAut A a = inn.app (op (fieldTest k S)) ⟨d⟩ := by
  obtain ⟨T, _, _, f, g, hg⟩ := adjointPoint_lifts_over_field Q d
  let : Algebra S T := f.hom.toRingHom.toAlgebra
  let : IsScalarTower k S T := IsScalarTower.of_algebraMap_eq fun x => (f.hom.commutes x).symm
  let l₀ : T →ₐ[S] T ⊗[S] T := includeLeft
  let r₀ : T →ₐ[S] T ⊗[S] T := includeRight
  let U := CommAlgCat.of k (T ⊗[S] T)
  let l : CommAlgCat.of k T ⟶ U := CommAlgCat.ofHom (l₀.restrictScalars k)
  let r : CommAlgCat.of k T ⟶ U := CommAlgCat.ofHom (r₀.restrictScalars k)
  have hcomp : f ≫ l = f ≫ r := by
    apply CommAlgCat.hom_ext
    ext z
    exact (l₀.commutes z).trans (r₀.commutes z).symm
  let gl := mapPoints l g
  let gr := mapPoints r g
  have hproj : gl ≫ Q.projection.hom.hom = gr ≫ Q.projection.hom.hom := by
    change ((testSpec k).map l.op ≫ g) ≫ _ = ((testSpec k).map r.op ≫ g) ≫ _
    rw [Category.assoc, Category.assoc, hg]
    change mapPoints l (mapPoints f d) = mapPoints r (mapPoints f d)
    rw [← mapPoints_comp_apply, ← mapPoints_comp_apply, hcomp]
  obtain ⟨t, _, _, ht⟩ := referenceFramePoints_centre A U (f ≫ l) (gl * gr⁻¹)
    (adjointLift_ratio_central Q U gl gr hproj)
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.Albert.Triality.frameTriality.{u} T
  obtain ⟨v, hv⟩ := e.surjective (referenceFramePoints A (CommAlgCat.of k T) f g)
  let a := relatedTripleInclusion v
  have ha : (referenceFramePoints A (CommAlgCat.of k T) f g).val = similarityOnModel a :=
    (congrArg Subtype.val hv).symm.trans (similarityOnModel_triality e he v).symm
  have hl := referenceFramePoints_baseChange A f l g a ha
  have hr := referenceFramePoints_baseChange A f r g a ha
  change (referenceFramePoints A U (f ≫ l) gl).val =
    similarityOnModel (relatedSimilarityBaseChange l.hom.toRingHom a) at hl
  change (referenceFramePoints A U (f ≫ r) gr).val =
    similarityOnModel (relatedSimilarityBaseChange r.hom.toRingHom a) at hr
  rw [← hcomp] at hr
  have hmul : similarityOnModel (relatedSimilarityBaseChange l.hom.toRingHom a) =
      (referenceFramePoints A U (f ≫ l) (gl * gr⁻¹)).val *
        similarityOnModel (relatedSimilarityBaseChange r.hom.toRingHom a) := by
    rw [← hl, ← hr, map_mul, map_inv]
    change _ = (_ * _⁻¹) * _
    rw [inv_mul_cancel_right]
  have hp (i : Fin 3) : ∃ c : (T ⊗[S] T)ˣ,
      zornLinearBaseChange (includeLeftRingHom : T →+* T ⊗[S] T) (a.val.1 i) =
        LinearEquiv.smulOfUnit c *
          zornLinearBaseChange (includeRight.toRingHom : T →+* T ⊗[S] T) (a.val.1 i) := by
    refine ⟨t i, LinearEquiv.ext fun x => ?_⟩
    have hx := LinearEquiv.congr_fun hmul (0, fun _ => x)
    rw [LinearEquiv.mul_apply, ht] at hx
    exact congrArg (fun z : Model U => z.2 i) hx
  obtain ⟨s, c, hs⟩ := relatedSimilarityRepresentative_descends a hp
  refine ⟨s, relativeAut_eq_afterFieldExtension (stabilizerAffineModel B) f ?_⟩
  intro R m z
  let f' := f ≫ m
  have hm := referenceFramePoints_baseChange A f m g a ha
  have eq : relatedSimilarityBaseChange m.hom.toRingHom a =
      scalarSimilarity (fun i => Units.map m.hom.toRingHom.toMonoidHom (c i)) *
        relatedSimilarityBaseChange f'.hom.toRingHom s := by
    rw [hs, map_mul, relatedSimilarityBaseChange_scalar, relatedSimilarityBaseChange_comp]
    rfl
  rw [eq] at hm
  have hg' : mapPoints m g ≫ Q.projection.hom.hom = mapPoints f' d := by
    change ((testSpec k).map m.op ≫ g) ≫ _ = _
    rw [Category.assoc, hg, mapPoints_comp_apply]
  exact (referenceFramePoints_compareSimilarity A f' s (mapPoints m g) z _ hm).trans
    (relativeInner_apply_of_lift Q inn hinn d R f' (mapPoints m g) z hg').symm

set_option backward.isDefEq.respectTransparency false in
private theorem referenceSimilarityAut_onTriple (v : relatedTriples (R := S))
    (e : relatedTriples (R := S) ≃* frameStabilizer (R := S))
    (he : ∀ r : relatedTriples (R := S), ∀ x : Model S, (e r).val x = (x.1, fun i => r.val i (x.2 i))) :
    referenceSimilarityAut A (relatedTripleInclusion v) =
      innerAut ((referenceFramePoints A _ (𝟙 (CommAlgCat.of k S))).symm (e v)) := by
  let g := (referenceFramePoints A _ (𝟙 (CommAlgCat.of k S))).symm (e v)
  have hg : (referenceFramePoints A _ (𝟙 (CommAlgCat.of k S)) g).val =
      similarityOnModel (relatedTripleInclusion v) := by
    change ((referenceFramePoints A _ (𝟙 (CommAlgCat.of k S)))
      ((referenceFramePoints A _ (𝟙 (CommAlgCat.of k S))).symm (e v))).val = _
    rw [MulEquiv.apply_symm_apply, similarityOnModel_triality e he]
  apply Aut.ext
  apply Iso.ext
  apply relativeHom_ext (stabilizerAffineModel B).property.1
  intro R f z
  change Points B.stabilizer.group.X R at z
  change _ = mapPoints f g * z * (mapPoints f g)⁻¹
  have h := referenceFramePoints_baseChange A (𝟙 (CommAlgCat.of k S)) f g _ hg
  rw [Category.id_comp] at h
  apply referenceFramePoints_compareSimilarity A f _ (mapPoints f g) z 1
  rw [map_one, one_mul]
  exact h

end

end ReferenceSimilarities

section SimilarityFields

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
open scoped BigOperators TensorProduct

noncomputable section


variable {F S : Type u} [Field F] [Field S] [Algebra F S]

private theorem zornBlock_defined_over (L : FiniteGaloisIntermediateField F S)
    (a : Zorn S ≃ₗ[S] Zorn S)
    (ha : ∀ i j, (zornGL S a).val i j ∈ L.toIntermediateField) :
    ∃ b : Zorn L ≃ₗ[L] Zorn L, zornLinearBaseChange (algebraMap L S) b = a := by
  classical
  let M : Matrix (ZornIndex.{u}) ZornIndex.{u} L := Matrix.of fun i j => ⟨(zornGL S a).val i j, ha i j⟩
  have hM : (algebraMap L S).mapMatrix M = (zornGL S a).val := rfl
  have hdet : IsUnit M.det := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have he := congrArg Matrix.det hM
    rw [← RingHom.map_det, hz, map_zero] at he
    exact (isUnit_iff_ne_zero.mp ((zornGL S a).val.isUnit_iff_isUnit_det.mp (zornGL S a).isUnit)) he.symm
  obtain ⟨N, hN⟩ := M.isUnit_iff_isUnit_det.mpr hdet
  refine ⟨(zornGL L).symm N, (zornGL S).injective (Units.ext ?_)⟩
  rw [zornGL_baseChange, MulEquiv.apply_symm_apply, hN]
  exact hM

/-- Finitely many representatives by Peirce similarities are defined over
one finite Galois subextension containing any prescribed finite layer. -/
private theorem exists_similarityLayer_above [IsGalois F S] {I : Type u} [Finite I]
    (a : I → RelatedSimilarities S) (L₀ : FiniteGaloisIntermediateField F S) :
    ∃ L : FiniteGaloisIntermediateField F S, L₀ ≤ L ∧
      ∀ j, ∃ b : RelatedSimilarities L, relatedSimilarityBaseChange (algebraMap L S) b = a j := by
  classical
  let coefficients := Set.range fun p : I × Fin 3 × ZornIndex.{u} × ZornIndex.{u} =>
    (zornGL S ((a p.1).val.1 p.2.1)).val p.2.2.1 p.2.2.2
  let factors := Set.range fun p : I × Fin 3 => ((a p.1).val.2 p.2 : S)
  let s := coefficients ∪ factors
  let : Finite s := ((Set.finite_range _).union (Set.finite_range _)).to_subtype
  let L₁ := FiniteGaloisIntermediateField.adjoin F s
  let L := L₀ ⊔ L₁
  have hmem (x : S) (hx : x ∈ s) : x ∈ L.toIntermediateField :=
    (show L₁ ≤ L from le_sup_right) (FiniteGaloisIntermediateField.subset_adjoin F s hx)
  refine ⟨L, le_sup_left, fun j => ?_⟩
  have hb (i : Fin 3) := zornBlock_defined_over L ((a j).val.1 i) fun m n =>
    hmem _ (Or.inl ⟨(j,i,m,n), rfl⟩)
  choose v hv using hb
  let w (i : Fin 3) : Lˣ := Units.mk0
    ⟨((a j).val.2 i : S), hmem _ (Or.inr ⟨(j,i), rfl⟩)⟩
    (fun h => Units.ne_zero ((a j).val.2 i) (congrArg Subtype.val h))
  exact relatedSimilarity_of_baseChange (algebraMap L S) (a j) v w hv (fun i => Units.ext rfl)

private theorem cubicNumbering_over_larger_layer {E : Type u} [Field E] [Algebra F E]
    {K L : FiniteGaloisIntermediateField F S} (h : K ≤ L)
    (numbering : (E →ₐ[F] S) ≃ Fin 3) (labels : (E →ₐ[F] K) ≃ Fin 3)
    (hl : ∀ e, labels e = numbering (K.toIntermediateField.val.comp e)) :
    ∃ labels' : (E →ₐ[F] L) ≃ Fin 3, ∀ e, labels' e = numbering (L.toIntermediateField.val.comp e) := by
  let f : (E →ₐ[F] L) → (E →ₐ[F] S) := fun e => L.toIntermediateField.val.comp e
  have hbij : Function.Bijective f := by
    constructor
    · intro e₁ e₂ hh
      ext x
      exact AlgHom.congr_fun hh x
    · intro e
      let e₀ := labels.symm (numbering e)
      have he : K.toIntermediateField.val.comp e₀ = e := by
        apply numbering.injective
        rw [← hl, Equiv.apply_symm_apply]
      let m := IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp h)
      refine ⟨m.comp e₀, ?_⟩
      exact he
  exact ⟨(Equiv.ofBijective f hbij).trans numbering, fun _ => rfl⟩

end

end SimilarityFields

section ProjectiveSimilarityAction

open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Descent.NonabelianCohomology (restriction)
open _root_.Specs.RM03.CSA (isCentralDivision degree isSplit)
open scoped TensorProduct

noncomputable section


private instance scalarSimilarity_normal {L : Type u} [CommRing L] :
    (scalarSimilarity (R := L)).range.Normal := by
  apply Subgroup.normal_of_le_center
  rintro _ ⟨t, rfl⟩
  exact Subgroup.mem_center_iff.mpr fun p => (scalarSimilarity_central t p).symm.eq

private abbrev ProjectiveSimilarities (L : Type u) [CommRing L] :=
  RelatedSimilarities L ⧸ (scalarSimilarity (R := L)).range

private abbrev projectSimilarity (L : Type u) [CommRing L] :
    RelatedSimilarities L →* ProjectiveSimilarities L :=
  QuotientGroup.mk' _

variable {F L : Type u} [Field F] [Field L] [Algebra F L]
  (π : Gal(L/F) →* Equiv.Perm (Fin 3))

private theorem relatedSimilarityAction_scalars (g : Gal(L/F)) :
    Subgroup.map (relatedSimilarityAction π g).toMonoidHom (scalarSimilarity (R := L)).range =
      (scalarSimilarity (R := L)).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨blockUnitsAction π g t, (relatedSimilarityAction_scalar π g t).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨s, rfl⟩ := (blockUnitsAction π g).surjective t
    exact ⟨scalarSimilarity s, ⟨s, rfl⟩, relatedSimilarityAction_scalar π g s⟩

private def projectiveSimilarityAction :
    Gal(L/F) →* MulAut (ProjectiveSimilarities L) := by
  let m (g : Gal(L/F)) := QuotientGroup.congr _ _ (relatedSimilarityAction π g)
    (relatedSimilarityAction_scalars π g)
  have hm (g : Gal(L/F)) (x : RelatedSimilarities L) :
      m g (projectSimilarity L x) = projectSimilarity L (relatedSimilarityAction π g x) :=
    QuotientGroup.congr_mk' _ _ _ _ x
  refine ⟨⟨m, ?_⟩, ?_⟩
  · apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [hm, map_one]
    rfl
  · intro g h
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    change m (g * h) (projectSimilarity L x) = m g (m h (projectSimilarity L x))
    rw [hm, hm, hm, map_mul]
    rfl

private theorem projectSimilarity_equivariant (g : Gal(L/F)) (x : RelatedSimilarities L) :
    projectSimilarity L (relatedSimilarityAction π g x) =
      projectiveSimilarityAction π g (projectSimilarity L x) :=
  rfl

variable {E S : Type u} [Field E] [Field S] [Algebra F E] [Algebra F S]

private theorem relatedSimilarityAction_restrict
    (L : FiniteGaloisIntermediateField F S) (numbering : (E →ₐ[F] S) ≃ Fin 3)
    (labels : (E →ₐ[F] L) ≃ Fin 3)
    (hlabels : ∀ e, labels e = numbering (L.toIntermediateField.val.comp e))
    (σ : Gal(S/F)) (a : RelatedSimilarities L) :
    relatedSimilarityBaseChange (algebraMap L S) (relatedSimilarityAction (diagramPermutation labels) (restriction L σ) a) =
      relatedSimilarityAction (diagramPermutation numbering) σ (relatedSimilarityBaseChange (algebraMap L S) a) := by
  change relatedSimilarityBaseChange (algebraMap L S) (transportSimilarities (restriction L σ).toRingEquiv
      (diagramPermutation labels (restriction L σ)) a) =
    transportSimilarities σ.toRingEquiv (diagramPermutation numbering σ)
      (relatedSimilarityBaseChange (algebraMap L S) a)
  rw [diagramPermutation_restriction L numbering labels hlabels σ]
  apply transportSimilarities_baseChange
  ext x
  exact AlgEquiv.restrictNormal_apply L.toIntermediateField σ x

variable {D : Type u} [DivisionRing D] [Algebra F D] [IsGalois F S]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]
  {Q : Type w} [Group Q]

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- At a layer carrying the representatives, the scalar quotient embeds
in the actual coefficient group at the separable closure. Its finite
cocycle therefore has the same multiplication defects there. -/
private theorem localSimilarityLift_atLayer
    (L : FiniteGaloisIntermediateField F S) (cubic : Module.finrank F E = 3)
    (hD : isCentralDivision F D) (dD : degree F D = 2) (splitD : isSplit L (L ⊗[F] D))
    (numbering : (E →ₐ[F] S) ≃ Fin 3) (labels : (E →ₐ[F] L) ≃ Fin 3)
    (hlabels : ∀ e, labels e = numbering (L.toIntermediateField.val.comp e))
    (ρ : Gal(S/F) →* MulAut Q) (p : RelatedSimilarities S →* Q)
    (pEquiv : ∀ σ x, p (relatedSimilarityAction (diagramPermutation numbering) σ x) = ρ σ (p x))
    (pKernel : ∀ x, p x = 1 ↔ x ∈ (scalarSimilarity (R := S)).range)
    (a : Gal(S/F) → Q) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ))
    (l : Gal(L/F) → RelatedSimilarities L)
    (hl : ∀ σ, p (relatedSimilarityBaseChange (algebraMap L S) (l (restriction L σ))) = a σ) :
    ∃ (b : RelatedSimilarities L) (c : Gal(L/F) → relatedTriples (R := L)),
      (∀ g h, c (g * h) = c g * relatedTripleAction (diagramPermutation labels) g (c h)) ∧
      ∀ σ, p (relatedSimilarityBaseChange (algebraMap L S)
          (relatedTripleInclusion (c (restriction L σ)))) =
        (p (relatedSimilarityBaseChange (algebraMap L S) b))⁻¹ * a σ *
          ρ σ (p (relatedSimilarityBaseChange (algebraMap L S) b)) := by
  let β := relatedSimilarityBaseChange (algebraMap L S)
  let π := diagramPermutation labels
  let q := projectSimilarity L
  let τ := projectiveSimilarityAction π
  let r := restriction L
  have hker : (scalarSimilarity (R := L)).range = (p.comp β).ker := by
    ext x
    change x ∈ (scalarSimilarity (R := L)).range ↔ p (β x) = 1
    rw [pKernel]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, (relatedSimilarityBaseChange_scalar (algebraMap L S) t).symm⟩
    · rintro ⟨t, ht⟩
      exact relatedSimilarity_scalar_of_baseChange (algebraMap L S) (algebraMap L S).injective x t ht.symm
  let j := QuotientGroup.lift (scalarSimilarity (R := L)).range (p.comp β) (le_of_eq hker)
  have hj : Function.Injective j :=
    (QuotientGroup.injective_lift_iff _ _ _).2 hker
  have hjq (x : RelatedSimilarities L) : j (q x) = p (β x) := QuotientGroup.lift_mk' _ _ x
  have restr (σ : Gal(S/F)) (x : RelatedSimilarities L) :
      β (relatedSimilarityAction π (r σ) x) = relatedSimilarityAction (diagramPermutation numbering) σ (β x) :=
    relatedSimilarityAction_restrict L numbering labels hlabels σ x
  have hjτ (σ : Gal(S/F)) (x : RelatedSimilarities L) :
      j (τ (r σ) (q x)) = ρ σ (j (q x)) := by
    change j (projectiveSimilarityAction π (r σ) (projectSimilarity L x)) = _
    rw [← projectSimilarity_equivariant, hjq, restr, pEquiv, hjq]
  let u (g : Gal(L/F)) := q (l g)
  have hu (g h : Gal(L/F)) : u (g * h) = u g * τ g (u h) := by
    obtain ⟨σ, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S : Function.Surjective r) g
    obtain ⟨ν, rfl⟩ := (AlgEquiv.restrictNormalHom_surjective S : Function.Surjective r) h
    apply hj
    change j (q (l (r σ * r ν))) = j (q (l (r σ)) * τ (r σ) (q (l (r ν))))
    rw [← map_mul r, map_mul j, hjτ, hjq, hjq, hjq, hl, hl, hl, ha]
  let o : Fin 3 := 0
  let e := labels.symm o
  let : Algebra E L := e.toRingHom.toAlgebra
  let : IsScalarTower F E L := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let : IsGalois E L := IsGalois.tower_top_of_isGalois F E L
  have hE : IsScalarTower.toAlgHom F E L = labels.symm o := by ext x; rfl
  obtain ⟨htrans, ψ, hψ⟩ := cubicEmbeddingStabilizer labels o hE
  obtain ⟨b, c, hc, hadd⟩ := localRelatedSimilarityLift π cubic hD dD splitD τ q
    (projectSimilarity_equivariant π) (fun x => QuotientGroup.eq_one_iff x) u hu l (fun _ => rfl)
    o htrans ψ hψ
  refine ⟨b,c,hc, fun σ => ?_⟩
  have h := congrArg j (hadd (r σ))
  change j (q (relatedTripleInclusion (c (r σ)))) = j ((q b)⁻¹ * q (l (r σ)) * τ (r σ) (q b)) at h
  simp only [map_mul, map_inv, hjτ, hjq] at h
  rw [show p (β (l (r σ))) = a σ from hl σ] at h
  exact h

end

end ProjectiveSimilarityAction

section Realization

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Specs
open TrialitarianAlbertDescentSpecification
open AutomorphismSequence
open RelativeFormComparison (fieldTest fieldMap automorphismAction transportedAut)
open LinearAlgebraicGroups.Albert.TrialitySpecification
open LinearAlgebraicGroups.Composition (Zorn)
open LinearAlgebraicGroups.Descent.NonabelianCohomology
  (Cocycle pointAction restriction finiteLevel)
open _root_.Specs.RM03.CSA (isCentralSimple isSplit)

noncomputable section


private theorem exists_similarityLayer_splitting {k S D : Type u} [Field k] [Field S]
    [Algebra k S] [IsSepClosure k S] [Ring D] [Algebra k D] (hD : isCentralSimple k D)
    (K : FiniteGaloisIntermediateField k S) (l : Gal(K/k) → RelatedSimilarities S) :
    ∃ (L : FiniteGaloisIntermediateField k S) (b : Gal(L/k) → RelatedSimilarities L),
      K ≤ L ∧ isSplit L (L ⊗[k] D) ∧ ∀ σ : Gal(S/k),
        relatedSimilarityBaseChange (algebraMap L S) (b (restriction L σ)) = l (restriction K σ) := by
  obtain ⟨K', hK', hh⟩ := exists_similarityLayer_above l K
  choose b hb using hh
  obtain ⟨L, hL, hsplit⟩ := exists_splittingLayer_above hD K'
  let i : K' →ₐ[k] L := IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp hL)
  let j : K →ₐ[k] L := IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff _ _).mp (hK'.trans hL))
  let : Algebra K L := j.toRingHom.toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  let : IsScalarTower K L S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let r : Gal(L/k) →* Gal(K/k) := AlgEquiv.restrictNormalHom K
  have hr (σ : Gal(S/k)) : r (restriction L σ) = restriction K σ :=
    (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply K L σ).symm
  refine ⟨L, fun τ => relatedSimilarityBaseChange i.toRingHom (b (r τ)), hK'.trans hL, hsplit, fun σ => ?_⟩
  rw [relatedSimilarityBaseChange_comp, hr]
  exact hb (restriction K σ)

variable {k E S : Type u} [Field k] [Field E] [Field S] [Algebra k E] [Algebra k S]
  {J : AlbertModel k} {B : CubicStabilizer J E} {numbering : (E →ₐ[k] S) ≃ Fin 3}
  {C : FrameCharts J B numbering} (A : SplitFrameComparison C)

private theorem similarityOnModel_injective {R : Type u} [CommRing R] :
    Function.Injective (similarityOnModel (R := R)) := by
  intro a b h
  apply similarity_blocks_injective
  funext i
  apply LinearEquiv.ext
  intro x
  exact congrArg (fun z : Model R => z.2 i) (LinearEquiv.congr_fun h (0, fun _ => x))

private def similarityOfPoint (e : relatedTriples (R := S) ≃* frameStabilizer (R := S)) :
    Points B.stabilizer.group.X (CommAlgCat.of k S) →* RelatedSimilarities S :=
  relatedTripleInclusion.comp
    ((referenceFramePoints A (CommAlgCat.of k S) (𝟙 (CommAlgCat.of k S))).trans e.symm).toMonoidHom

private theorem similarityOfPoint_injective (e : relatedTriples (R := S) ≃* frameStabilizer (R := S)) :
    Function.Injective (similarityOfPoint A e) :=
  relatedTripleInclusion_injective.comp
    ((referenceFramePoints A (CommAlgCat.of k S) (𝟙 (CommAlgCat.of k S))).trans e.symm).injective

private theorem similarityOfPoint_compare (e : relatedTriples (R := S) ≃* frameStabilizer (R := S))
    (he : ∀ r : relatedTriples (R := S), ∀ x : Model S, (e r).val x = (x.1, fun i => r.val i (x.2 i)))
    (x : Points B.stabilizer.group.X (CommAlgCat.of k S)) :
    similarityOnModel (similarityOfPoint A e x) =
      (referenceFramePoints A _ (𝟙 (CommAlgCat.of k S)) x).val := by
  change similarityOnModel (relatedTripleInclusion (e.symm (referenceFramePoints A _ (𝟙 _) x))) = _
  rw [similarityOnModel_triality e he, e.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem similarityOfPoint_equivariant (e : relatedTriples (R := S) ≃* frameStabilizer (R := S))
    (he : ∀ r : relatedTriples (R := S), ∀ x : Model S, (e r).val x = (x.1, fun i => r.val i (x.2 i)))
    (σ : Gal(S/k)) (g : Points B.stabilizer.group.X (CommAlgCat.of k S)) :
    similarityOfPoint A e (pointAction k S B.stabilizer.group.X σ g) =
      relatedSimilarityAction (diagramPermutation numbering) σ (similarityOfPoint A e g) := by
  let R := CommAlgCat.of k S
  let f : R ⟶ R := CommAlgCat.ofHom σ.toAlgHom
  let π := diagramPermutation numbering σ
  apply similarityOnModel_injective
  apply LinearEquiv.ext
  intro x
  have hsurj : Function.Surjective (fun x : Model S => framePermutation π (mapModel σ.toRingHom x)) :=
    (framePermutation (R := S) π).surjective.comp (coefficientEquiv σ.toRingEquiv).surjective
  obtain ⟨x, rfl⟩ := hsurj x
  change similarityOnModel (similarityOfPoint A e (mapPoints f g))
      (framePermutation π (mapModel σ.toRingHom x)) =
    similarityOnModel (transportSimilarities σ.toRingEquiv π (similarityOfPoint A e g))
      (framePermutation π (mapModel σ.toRingHom x))
  rw [similarityOnModel_transport, similarityOfPoint_compare A e he, similarityOfPoint_compare A e he]
  have h := referenceFramePoints_permutation A R (𝟙 R) σ (mapPoints f g)
  change referenceFramePoints A R (𝟙 R) (mapPoints f g) =
    frameStabilizerPermutation π (referenceFramePoints A R (f ≫ 𝟙 R) (mapPoints f g)) at h
  rw [Category.comp_id] at h
  have hn := referenceFramePoints_natural A (𝟙 R) f g x
  rw [Category.id_comp] at hn
  rw [h, frameStabilizerPermutation_apply]
  exact congrArg (framePermutation π) hn.symm

variable [Module.Finite k E] [Algebra.IsSeparable k E] [IsSepClosure k S]
  [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
include A in
/-- Combining the local defect computation with the actual adjoint and frame
comparisons produces a continuous lift in the reference stabilizer. -/
private theorem exists_referenceInnerLift
    (cubic : Module.finrank k E = 3) (G : AffineAlgebraicGroup k)
    (Q : AdjointQuotient (stabilizerAffineModel B))
    (inn : groupSections Q.quotient.val ⟶ automorphisms B.stabilizer.group)
    (hinn : ∀ (U : SchemeOver k) (b : U ⟶ B.stabilizer.group.X),
      inn.app (op U) ⟨b ≫ Q.projection.hom.hom⟩ = innerAut b)
    (i : relativePoints B.stabilizer.group (fieldTest k S) ≅ relativePoints G.val (fieldTest k S))
    (d : @Cocycle (Gal(S/k)) (Points Q.quotient.val.X (CommAlgCat.of k S))
      _ (krullTopology k S) _ ⊥ (pointAction k S Q.quotient.val.X))
    (hd : ∀ σ, inn.app (op (fieldTest k S)) ⟨d σ⟩ = transportedAut k S i σ) :
    HasInnerLift B.stabilizer.group G.val S := by
  let : TopologicalSpace (Gal(S/k)) := krullTopology k S
  let : TopologicalSpace (Points Q.quotient.val.X (CommAlgCat.of k S)) := ⊥
  let : DiscreteTopology (Points Q.quotient.val.X (CommAlgCat.of k S)) := ⟨rfl⟩
  let φ : Points Q.quotient.val.X (CommAlgCat.of k S) →* RelativeAut B.stabilizer.group (fieldTest k S) :=
    { toFun := fun x => inn.app (op (fieldTest k S)) ⟨x⟩
      map_one' := (inn.app (op (fieldTest k S))).hom.map_one
      map_mul' := fun x y => (inn.app (op (fieldTest k S))).hom.map_mul ⟨x⟩ ⟨y⟩ }
  let ρ := automorphismAction k S B.stabilizer.group
  have φeq (σ : Gal(S/k)) (x : Points Q.quotient.val.X (CommAlgCat.of k S)) :
      φ (pointAction k S Q.quotient.val.X σ x) = ρ σ (φ x) :=
    NatTrans.naturality_apply inn (fieldMap k S σ).op ⟨x⟩
  let a (σ : Gal(S/k)) := φ (d σ)
  have ha (σ τ : Gal(S/k)) : a (σ * τ) = a σ * ρ σ (a τ) := by
    change φ (d (σ * τ)) = φ (d σ) * ρ σ (φ (d τ))
    rw [d.property.2, map_mul, φeq]
  obtain ⟨L₀, labels₀, hlabels₀⟩ := exists_cubicSplittingLayer numbering
  obtain ⟨K, cK, hK, hcK⟩ := finiteLevel L₀ d
  let p := referenceSimilarityAut A
  have hLifts (τ : Gal(K/k)) : ∃ s : RelatedSimilarities S, p s = φ (cK τ).val :=
    exists_referenceSimilarityLift A Q inn hinn (cK τ).val
  choose l hl using hLifts
  obtain ⟨D, _, _, hD, dD⟩ := LocalQuadraticSplitting.local_division_exists (F := k)
  obtain ⟨L, lL, hKL, splitD, hL⟩ :=
    exists_similarityLayer_splitting (_root_.RM03.CSA.isCentralSimple_of_isCentralDivision k D hD) K l
  obtain ⟨labels, hlabels⟩ := cubicNumbering_over_larger_layer (hK.trans hKL) numbering labels₀ hlabels₀
  have hLift (σ : Gal(S/k)) :
      p (relatedSimilarityBaseChange (algebraMap L S) (lL (restriction L σ))) = a σ := by
    change p (relatedSimilarityBaseChange (algebraMap L S) (lL (restriction L σ))) = φ (d σ)
    rw [hL, hl, hcK σ]
  obtain ⟨b, c, hc, hclass⟩ := localSimilarityLift_atLayer L cubic hD dD splitD numbering labels hlabels ρ p
    (referenceSimilarityAut_equivariant A) (referenceSimilarityAut_kernel A) a ha lL hLift
  let β := relatedSimilarityBaseChange (algebraMap L S)
  let proj := relatedTripleInclusion (R := L)
  have hx (τ : Gal(L/k)) : ∃ t : relatedTriples (R := S), relatedTripleInclusion t = β (proj (c τ)) := by
    have hh : compositionQuotient (β (proj (c τ))) = 1 := by
      funext j
      change Units.map (algebraMap L S).toMonoidHom (1 : Lˣ) = 1
      exact map_one _
    exact (compositionQuotient_kernel _).mp hh
  choose t ht using hx
  obtain ⟨e, he⟩ := LinearAlgebraicGroups.Albert.Triality.frameTriality.{u} S
  let b₀ := p (β b)
  let y (τ : Gal(L/k)) := (referenceFramePoints A _ (𝟙 (CommAlgCat.of k S))).symm (e (t τ))
  have hy (τ : Gal(L/k)) : similarityOfPoint A e (y τ) = β (proj (c τ)) := by
    change relatedTripleInclusion (e.symm (referenceFramePoints A _ (𝟙 _) (y τ))) = _
    rw [show referenceFramePoints A _ (𝟙 _) (y τ) = e (t τ) from MulEquiv.apply_symm_apply _ _,
      e.symm_apply_apply, ht]
  let z (σ : Gal(S/k)) := y (restriction L σ)
  let : TopologicalSpace (Points B.stabilizer.group.X (CommAlgCat.of k S)) := ⊥
  have hz : Continuous z :=
    (continuous_of_discreteTopology (f := y)).comp (InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField)
  have hz' (σ τ : Gal(S/k)) : z (σ * τ) = z σ * pointAction k S B.stabilizer.group.X σ (z τ) := by
    apply similarityOfPoint_injective A e
    change similarityOfPoint A e (y (restriction L (σ * τ))) =
      similarityOfPoint A e (y (restriction L σ) * pointAction k S B.stabilizer.group.X σ (y (restriction L τ)))
    rw [map_mul (similarityOfPoint A e), similarityOfPoint_equivariant A e he, hy, hy, hy,
      map_mul (restriction L), hc, map_mul proj, map_mul β]
    rw [relatedTripleInclusion_equivariant, relatedSimilarityAction_restrict L numbering labels hlabels]
  refine ⟨z, b₀.asIso ≪≫ i, ⟨hz, hz'⟩, fun σ => ?_⟩
  rw [LinearAlgebraicGroups.Descent.QuasiSplitInnerForms.changeOfTrivialization, ← hd σ]
  change b₀⁻¹ * a σ * ρ σ b₀ = innerAut (y (restriction L σ))
  rw [← hclass σ, ← ht]
  exact referenceSimilarityAut_onTriple A (t (restriction L σ)) e he

/-- The continuous lift descends the original group as the pointwise
stabilizer of the same cubic field in a split Albert algebra. -/
theorem trialitarianRealization : TrialitarianRealization.{u} := by
  intro k E S _ _ _ _ _ _ _ _ _ _ _ cubic G D
  obtain ⟨J, B, hJ, ⟨C⟩, Q, inn, hinn, _, i, d, hd⟩ := exists_trialitarianAdjointCocycle cubic G D
  obtain ⟨A⟩ := exists_splitFrameComparison C cubic
  have hLift := exists_referenceInnerLift A cubic G Q inn hinn i d hd
  have hDiag : IsDiagonalOver J B D.numbering := by
    obtain ⟨t, hu, ho, he, _⟩ := hJ
    exact ⟨t, hu, ho, he⟩
  obtain ⟨J', B', hG, hDiag'⟩ := exists_albertOfInnerLift B D.numbering hDiag G hLift
  exact ⟨J, B, hJ, hLift, J', B', hG, ambientAlbert_isSplit SplitAlbertLocalForms.localAlbertSplitting J', hDiag'⟩

end

end Realization

end LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent
