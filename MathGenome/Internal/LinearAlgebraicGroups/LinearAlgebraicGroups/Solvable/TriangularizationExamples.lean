import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.TriangularizationExamples
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.NormOneTorus
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Topology.Separation.Connected

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv Coalgebra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Algebra.TensorProduct
open scoped TensorProduct DualNumber Matrix CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.TriangularizationExamples

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open Specs.TriangularizationExamples

private theorem quarterTurn_no_line (P : Submodule ℝ (Fin 2 → ℝ))
    (hd : Module.finrank ℝ P = 1) :
    ¬ ∀ x ∈ P, (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x ∈ P := by
  intro h
  obtain ⟨x, hx, hspan⟩ := finrank_eq_one_iff'.mp hd
  obtain ⟨a, ha⟩ := hspan ⟨_, h x.val x.property⟩
  have hx' : x.val ≠ 0 := fun hzero => hx (Subtype.ext hzero)
  have e (i : Fin 2) := congrFun (congrArg Subtype.val ha) i
  have h0 : a * x.val 0 = -x.val 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e 0
  have h1 : a * x.val 1 = x.val 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using e 1
  have h : (a ^ 2 + 1) * x.val 1 = 0 := by linear_combination a * h1 + h0
  have ha' : a ^ 2 + 1 ≠ 0 := by positivity
  have hz1 := (mul_eq_zero.mp h).resolve_left ha'
  have hz0 : x.val 0 = 0 := by simpa [hz1] using h1.symm
  apply hx'
  funext i
  fin_cases i <;> assumption

private theorem realMultiplicationBoundary {W H L : Specs.AffineAlgebraicGroup ℝ}
    {e : (groupPointsFunctor ℝ).obj W.val ≅ WeilRestriction.extendedUnits ℝ ℂ}
    {n : W.val ⟶ H.val} (T : Specs.NormOneTorus.KernelModel e n)
    (g : (groupPointsFunctor ℝ).obj L.val ≅ Specs.StandardGroups.generalLinearPoints ℝ (Fin 2)) :
    RealMultiplicationBoundary T g := by
  obtain ⟨ρ, hρ⟩ := NormOneTorus.realCircleAction W H L e n T g
  refine ⟨ρ, hρ, ?_⟩
  intro R action
  let z : R ⊗[ℝ] ℂ := 1 ⊗ₜ[ℝ] Complex.I
  have hz : Specs.NormOneTorus.complexCoordinates R z = Pi.single 1 1 := by
    have h : (Complex.basisOneI.baseChange R) 1 = z := by
      simp [Module.Basis.baseChange_apply, Complex.coe_basisOneI, z]
    rw [← h]
    funext j
    fin_cases j <;> simp
  have hn : WeilRestriction.pointNorm ℝ ℂ R z = 1 := by
    rw [(NormOneTorus.complexMultiplication R z).2, hz]
    simp
  let v : Specs.NormOneTorus.normOnePoints ℝ ℂ R :=
    ⟨Units.ofPowEqOne z 4 (by
      simp [z, Algebra.TensorProduct.tmul_pow, Complex.I_pow_four, ← Algebra.TensorProduct.one_def]) (by decide),
      Units.ext hn⟩
  let f := (T.points R).symm v
  have hcoords : Specs.NormOneTorus.complexCoordinates R (T.points R f).val.val =
      Pi.single 1 1 := by
    rw [MulEquiv.apply_symm_apply]
    exact hz
  have hrot : action f = !![0, -1; 1, 0] := by
    dsimp only [action]
    rw [hρ R f, hcoords]
    simp
  refine ⟨⟨f, hrot⟩, ?_⟩
  intro P hd hp
  apply quarterTurn_no_line P hd
  intro x hx
  simpa only [hrot] using hp x hx f

theorem realNormOneBoundary : RealNormOneBoundary := by
  let _ : Algebra.IsQuadraticExtension ℝ ℂ := { finrank_eq_two' := Complex.finrank_real_complex }
  let T := NormOneTorus.determinantKernel ℝ ℂ
  let g := StandardGroups.generalLinearGroupPointsIso ℝ (Fin 2)
  exact ⟨_, _, _, _, StandardGroups.multiplicativeGroupPointsIso ℝ, _, T, g,
    WeilRestriction.norm_apply ℝ ℂ, NormOneTorus.determinantKernel_isTorus ℝ ℂ,
    realMultiplicationBoundary T g⟩

theorem infinitesimalSizes : InfinitesimalSizes.{u} :=
  ⟨RelativeFrobenius.kernelLengths, RelativeFrobenius.kernelFieldPoints⟩

/-- A nonidentity group-like coefficient gives a one-dimensional representation
with zero invariant space. -/
private theorem not_hasInvariantVectors {k : Type u} [Field k] (A : HopfAlgebraCategory k)
    (t : A) (hΔ : Coalgebra.comul (R := k) t = t ⊗ₜ[k] t)
    (hε : Coalgebra.counit (R := k) t = 1) (ht : t ≠ 1) :
    ¬ Specs.Unipotent.HasInvariantVectors A := by
  intro h
  let ρ : RightComodule k A k :=
    { coaction := (TensorProduct.mk k k A).flip t
      coassoc := fun x => by simp [hΔ]
      counit := fun x => by simp [hε] }
  obtain ⟨x, hx, hfix⟩ := h k ρ
  have he : x ⊗ₜ[k] t = x ⊗ₜ[k] (1 : A) := by
    exact sub_eq_zero.mp hfix
  have hs : x • t = x • (1 : A) := by
    simpa using congrArg (TensorProduct.lid k A) he
  exact ht ((smul_right_injective A hx) hs)

private theorem not_unipotent_of_parameter {k : Type u} [Field k]
    {M Q : HopfAlgebraCategory k} (q : M ⟶ Q) (t : M)
    (hΔ : Coalgebra.comul (R := k) t = t ⊗ₜ[k] t)
    (hε : Coalgebra.counit (R := k) t = 1) (ht : q.hom t ≠ 1)
    (finite : Algebra.FiniteType k Q) :
    ¬ Specs.Unipotent.IsUnipotent ((finiteTypeHopfSpec k).obj (op ⟨Q, finite⟩)) := by
  intro hu
  refine not_hasInvariantVectors Q (q.hom t) ?_ ?_ ht
    ((Unipotent.unipotenceCriteria _ Q (Iso.refl _)).1.mp hu)
  · rw [← CoalgHomClass.map_comp_comul_apply q.hom, hΔ, TensorProduct.map_tmul]
    rfl
  · exact (CoalgHomClass.counit_comp_apply q.hom t).trans hε

theorem multiplicativeKernelBoundary : MultiplicativeKernelBoundary.{u} := by
  intro k _ p _ _
  obtain ⟨m, hΔ, hε, _, _⟩ := StandardGroups.multiplicativeGroupSpecification k
  obtain ⟨a, _, h₀, _, _⟩ := StandardGroups.additiveGroupSpecification k
  let M := @CommHopfAlgCat.of k _ (LaurentPolynomial k) _ m.hopf
  let A := @CommHopfAlgCat.of k _ (Polynomial k) _ a.hopf
  let F₀ := RelativeFrobenius.pullback p A
  let F := RelativeFrobenius.pullback p M
  let I := kernelIdeal F
  let h := hopfKernelIdeal k F
  let _ := h
  obtain ⟨_, hpb, _, j, hj'⟩ := (RelativeFrobenius.frobeniusKernelSchemes k p A M
    AlgEquiv.refl AlgEquiv.refl h₀ hε F₀ F
    (RelativeFrobenius.pullback_formula p A) (RelativeFrobenius.pullback_formula p M)).2
  let Q := hopfQuotient M I
  let q := hopfQuotientMap M I
  let t : M := LaurentPolynomial.T 1
  have hj : j (q.hom t) = Specs.RelativeFrobenius.muCoordinate k p :=
    AlgHom.congr_fun hj' t
  obtain ⟨_, _, E, _, d, _, hd⟩ :=
    (RelativeFrobenius.kernelTangentSpaces k p).2
  let f := (d.symm (E.symm 1)).val.comp j.toAlgHom
  have hf : f (q.hom t) = ((1 : k[ε]) + (ε : k[ε])) := by
    change (d.symm (E.symm 1)).val (j (q.hom t)) = _
    rw [hj, hd]
    simp
  have hne : f (q.hom t) ≠ 1 := by
    rw [hf]
    intro hz
    have hz' := congrArg TrivSqZeroExt.snd hz
    simp at hz'
  let finite : Algebra.FiniteType k Q := inferInstance
  refine ⟨M, AlgEquiv.refl, F, h, RelativeFrobenius.pullback_formula p M, hΔ, hε,
    hpb, ⟨j, hj⟩, finite, ⟨f, hf, hne⟩, ?_⟩
  exact not_unipotent_of_parameter q t hΔ hε (fun he => hne (by rw [he, map_one])) finite

section FiniteConstant

variable (k : Type u) [Field k]
variable {G H : Type u}

private abbrev evalAt (g : G) : (G → k) →ₐ[k] k :=
  Pi.evalAlgHom k (fun _ : G ↦ k) g

private def reindex (f : G → H) : (H → k) →ₐ[k] (G → k) :=
  AlgHom.pi fun g => evalAt k (f g)

private theorem pair_eval_tmul (g : G) (h : H) (x : G → k) (y : H → k) :
    pairEvaluation k g h (x ⊗ₜ[k] y) = x g * y h := by
  simp [pairEvaluation]

private theorem pair_eval_eq (g : G) (h : H) [Fintype H] [DecidableEq H]
    (x : (G → k) ⊗[k] (H → k)) :
    pairEvaluation k g h x = piScalarRight k k (G → k) H x h g := by
  induction x using TensorProduct.inductionOn with
  | tmul x y => simp [pair_eval_tmul, mul_comm]
  | add x y hx hy => simp [hx, hy]

private theorem pair_ext [Fintype H] [DecidableEq H]
    {x y : (G → k) ⊗[k] (H → k)}
    (h : ∀ g h, pairEvaluation k g h x = pairEvaluation k g h y) : x = y :=
  (piScalarRight k k (G → k) H).injective (funext fun j =>
    funext fun i => by simpa only [pair_eval_eq] using h i j)

variable (G) [Group G] [Fintype G] [DecidableEq G]

private def constantDelta : (G → k) →ₐ[k] (G → k) ⊗[k] (G → k) :=
  (piScalarRight k k (G → k) G).symm.toAlgHom.comp
    (AlgHom.pi fun h => reindex k (· * h))

@[simp] private theorem eval_constantDelta (x : G → k) (g h : G) :
    pairEvaluation k g h (constantDelta k G x) = x (g * h) := by
  rw [pair_eval_eq]
  change (piScalarRight k k (G → k) G)
    ((piScalarRight k k (G → k) G).symm (fun h g => x (g * h))) h g = _
  rw [AlgEquiv.apply_symm_apply]

private def rightTriple (g h l : G) :
    ((G → k) ⊗[k] ((G → k) ⊗[k] (G → k))) →ₐ[k] k :=
  Algebra.TensorProduct.lift (evalAt k g) (pairEvaluation k h l) (fun _ _ => Commute.all _ _)

omit [Group G] in
private theorem rightTriple_ext {x y : (G → k) ⊗[k] ((G → k) ⊗[k] (G → k))}
    (he : ∀ g h l, rightTriple k G g h l x = rightTriple k G g h l y) : x = y := by
  let e := Algebra.TensorProduct.assoc k k k (G → k) (G → k) (G → k)
  apply e.symm.injective
  apply (piScalarRight k k ((G → k) ⊗[k] (G → k)) G).injective
  funext l
  apply pair_ext k
  intro g h
  have hEval (z : ((G → k) ⊗[k] (G → k)) ⊗[k] (G → k)) :
      pairEvaluation k g h (piScalarRight k k ((G → k) ⊗[k] (G → k)) G z l) =
        rightTriple k G g h l (e z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [piScalarRight_tmul_apply, map_smul]
      induction a using TensorProduct.inductionOn with
      | tmul a c => simp [e, rightTriple, pair_eval_tmul, smul_eq_mul]; ring
      | add a c ha hc => simp only [TensorProduct.add_tmul, map_add, smul_add, ← ha, ← hc]
    | add a b ha hb => simp [ha, hb]
  rw [hEval, hEval, e.apply_symm_apply, e.apply_symm_apply, he]

private def constantOperations : Specs.StandardGroups.HopfOperations k (G → k) where
  delta := constantDelta k G
  epsilon := evalAt k 1
  inverse := reindex k Inv.inv
  coassoc := by
    ext x : 1
    apply rightTriple_ext k G
    intro g h l
    change rightTriple k G g h l
      (Algebra.TensorProduct.assoc k k k (G → k) (G → k) (G → k)
        (map (constantDelta k G) (.id k _) (constantDelta k G x))) =
      rightTriple k G g h l (map (.id k _) (constantDelta k G) (constantDelta k G x))
    have h₁ (z : (G → k) ⊗[k] (G → k)) :
        rightTriple k G g h l
          (Algebra.TensorProduct.assoc k k k (G → k) (G → k) (G → k) (map (constantDelta k G) (.id k _) z)) =
        pairEvaluation k (g * h) l z := by
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        rw [map_tmul, AlgHom.id_apply]
        have ha (y : (G → k) ⊗[k] (G → k)) :
            rightTriple k G g h l (Algebra.TensorProduct.assoc k k k (G → k) (G → k) (G → k)
              (y ⊗ₜ[k] b)) = pairEvaluation k g h y * b l := by
          induction y using TensorProduct.inductionOn with
          | tmul a c => simp [rightTriple, pair_eval_tmul, mul_assoc]
          | add a c ha hc => simp [TensorProduct.add_tmul, add_mul, ha, hc]
        rw [ha, eval_constantDelta, pair_eval_tmul]
      | add a b ha hb => simp [ha, hb]
    have h₂ : (rightTriple k G g h l).comp (map (.id k _) (constantDelta k G)) =
        pairEvaluation k g (h * l) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [rightTriple, pair_eval_tmul]
    rw [h₁]
    change pairEvaluation k (g * h) l (constantDelta k G x) =
      ((rightTriple k G g h l).comp (map (.id k _) (constantDelta k G))) (constantDelta k G x)
    rw [h₂, eval_constantDelta, eval_constantDelta, mul_assoc]
  counitLeft := by
    ext x : 1
    apply (Algebra.TensorProduct.lid k (G → k)).injective
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    funext g
    have he : ((evalAt k g).comp (Algebra.TensorProduct.lid k (G → k)).toAlgHom).comp
        (map (evalAt k (1 : G)) (.id k _)) = pairEvaluation k (1 : G) g := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [pair_eval_tmul, smul_eq_mul]
    change (((evalAt k g).comp (Algebra.TensorProduct.lid k (G → k)).toAlgHom).comp
      (map (evalAt k (1 : G)) (.id k _))) (constantDelta k G x) = x g
    rw [he, eval_constantDelta, one_mul]
  counitRight := by
    ext x : 1
    apply (Algebra.TensorProduct.rid k k (G → k)).injective
    simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    funext g
    have he : ((evalAt k g).comp (Algebra.TensorProduct.rid k k (G → k)).toAlgHom).comp
        (map (.id k _) (evalAt k (1 : G))) = pairEvaluation k g (1 : G) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [pair_eval_tmul, smul_eq_mul, mul_comm]
    change (((evalAt k g).comp (Algebra.TensorProduct.rid k k (G → k)).toAlgHom).comp
      (map (.id k _) (evalAt k (1 : G)))) (constantDelta k G x) = x g
    rw [he, eval_constantDelta, mul_one]
  inverseLeft := by
    ext x g : 2
    have he : (evalAt k g).comp (Algebra.TensorProduct.lift (reindex k (Inv.inv : G → G)) (.id k _)
        (fun _ _ => Commute.all _ _)) = pairEvaluation k g⁻¹ g := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rfl
    change ((evalAt k g).comp (Algebra.TensorProduct.lift (reindex k (Inv.inv : G → G)) (.id k _)
      (fun _ _ => Commute.all _ _))) (constantDelta k G x) = x 1
    rw [he, eval_constantDelta, inv_mul_cancel]
  inverseRight := by
    ext x g : 2
    have he : (evalAt k g).comp (Algebra.TensorProduct.lift (.id k _) (reindex k (Inv.inv : G → G))
        (fun _ _ => Commute.all _ _)) = pairEvaluation k g g⁻¹ := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [pair_eval_tmul, reindex]
    change ((evalAt k g).comp (Algebra.TensorProduct.lift (.id k _) (reindex k (Inv.inv : G → G))
      (fun _ _ => Commute.all _ _))) (constantDelta k G x) = x 1
    rw [he, eval_constantDelta, mul_inv_cancel]

end FiniteConstant
section ConstantSchemes

variable (k : Type u) [Field k]

private def constantHopf (G : Type u) [Group G] [Fintype G] [DecidableEq G] :
    HopfAlgebraCategory k :=
  letI := (constantOperations k G).hopf
  CommHopfAlgCat.of k (G → k)

private def constantScheme (G : Type u) [Group G] [Fintype G] [DecidableEq G] :=
  specGroup (constantHopf k G)

private abbrev affineSpec (A : Type u) [CommRing A] [Algebra k A] : SchemeOver k :=
  (testSpec k).obj (op (CommAlgCat.of k A))

private abbrev affineMap {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : B →ₐ[k] A) : affineSpec k A ⟶ affineSpec k B :=
  (testSpec k).map (CommAlgCat.ofHom f).op

private abbrev pointAt {G : Type u} (g : G) :
    affineSpec k k ⟶ affineSpec k (G → k) :=
  affineMap k (evalAt k g)

private abbrev groupPointAt {G : Type u} [Group G] [Fintype G] [DecidableEq G] (g : G) :
    affineSpec k k ⟶ (constantScheme k G).X :=
  pointAt k g

private theorem pointAt_comp {G H : Type u} (f : G → H) (g : G) :
    pointAt k g ≫ affineMap k (reindex k f) = pointAt k (f g) := by
  rw [← (testSpec k).map_comp]
  rfl

private theorem pointAt_mul (G : Type u) [Group G] [Fintype G] [DecidableEq G] (g h : G) :
    groupPointAt k g * groupPointAt k h = groupPointAt k (g * h) := by
  let A := constantHopf k G
  let R := CommAlgCat.of k k
  let E := (hopfSpecPointIso A).hom.app R
  let x : (convolutionPoints A).obj R := toConv (evalAt k g)
  let y : (convolutionPoints A).obj R := toConv (evalAt k h)
  have he : x * y = toConv (evalAt k (g * h)) := by
    apply WithConv.ofConv_injective
    ext f : 1
    exact (AlgHom.convMul_apply (R := k) x y f).trans (eval_constantDelta k G f g h)
  change E x * E y = E (toConv (evalAt k (g * h)))
  rw [← map_mul, he]

private theorem pointAt_one (G : Type u) [Group G] [Fintype G] [DecidableEq G] :
    groupPointAt k (1 : G) = 1 := by
  let A := constantHopf k G
  let R := CommAlgCat.of k k
  have he : (toConv (evalAt k (1 : G)) : (convolutionPoints A).obj R) = 1 := by
    apply WithConv.ofConv_injective
    ext f : 1
    rfl
  change (hopfSpecPointIso A).hom.app R (toConv (evalAt k (1 : G))) = _
  rw [he, map_one]

private theorem pointAt_inv (G : Type u) [Group G] [Fintype G] [DecidableEq G] (g : G) :
    (groupPointAt k g)⁻¹ = groupPointAt k g⁻¹ := by
  apply mul_left_cancel (a := groupPointAt k g)
  rw [mul_inv_cancel, pointAt_mul, mul_inv_cancel, pointAt_one]

private def affineProduct (G H : Type u) :
    affineSpec k ((G → k) ⊗[k] (H → k)) ≅ affineSpec k (G → k) ⊗ affineSpec k (H → k) :=
  letI : (testSpec k).Braided := braidedAlgSpec (R := CommRingCat.of k)
  (Functor.Monoidal.μIso (testSpec k)
    (op (CommAlgCat.of k (G → k))) (op (CommAlgCat.of k (H → k)))).symm

private theorem pointAt_pair {G H : Type u} (g : G) (h : H) :
    affineMap k (pairEvaluation k g h) ≫ (affineProduct k G H).hom =
      CartesianMonoidalCategory.lift (pointAt k g) (pointAt k h) := by
  let a := (CommAlgCat.ofHom (evalAt k g)).op
  let b := (CommAlgCat.ofHom (evalAt k h)).op
  let _ : (testSpec k).Braided := braidedAlgSpec (R := CommRingCat.of k)
  have h := Functor.OplaxMonoidal.lift_δ (testSpec k) a b
  exact h

private theorem constantProduct_hom_ext {G H K : Type u} [Fintype H] [DecidableEq H]
    {f g : affineSpec k (G → k) ⊗ affineSpec k (H → k) ⟶ affineSpec k (K → k)}
    (h : ∀ (x : G) (y : H), CartesianMonoidalCategory.lift (pointAt k x) (pointAt k y) ≫ f =
      CartesianMonoidalCategory.lift (pointAt k x) (pointAt k y) ≫ g) : f = g := by
  let i := affineProduct k G H
  let E := algSpec.fullyFaithful (R := CommRingCat.of k)
  let a := E.preimage (i.hom ≫ f)
  let b := E.preimage (i.hom ≫ g)
  have ha : (testSpec k).map a = i.hom ≫ f := E.map_preimage _
  have hb : (testSpec k).map b = i.hom ≫ g := E.map_preimage _
  apply (cancel_epi i.hom).mp
  rw [← ha, ← hb]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  apply pair_ext k
  intro x y
  have hp := h x y
  rw [← pointAt_pair, Category.assoc, ← ha, Category.assoc, ← hb,
    ← (testSpec k).map_comp, ← (testSpec k).map_comp] at hp
  have hp' := Quiver.Hom.op_inj (E.map_injective hp)
  exact congrArg (fun e : CommAlgCat.of k (K → k) ⟶ CommAlgCat.of k k => e.hom z) hp'

private theorem constantScheme_product_hom_ext {G H K : Type u}
    [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H]
    [Group K] [Fintype K] [DecidableEq K]
    {f g : (constantScheme k G).X ⊗ (constantScheme k H).X ⟶ (constantScheme k K).X}
    (h : ∀ (x : G) (y : H), lift (groupPointAt k x) (groupPointAt k y) ≫ f =
      lift (groupPointAt k x) (groupPointAt k y) ≫ g) : f = g :=
  constantProduct_hom_ext k h

private def constantProductMap {G H K : Type u} [Fintype H] [DecidableEq H] (f : G → H → K) :
    affineSpec k (G → k) ⊗ affineSpec k (H → k) ⟶ affineSpec k (K → k) :=
  (affineProduct k G H).inv ≫ affineMap k
    ((piScalarRight k k (G → k) H).symm.toAlgHom.comp
      (AlgHom.pi fun y => reindex k (fun x => f x y)))

private theorem pointAt_comp_productMap {G H K : Type u} [Fintype H] [DecidableEq H]
    (f : G → H → K) (x : G) (y : H) :
    CartesianMonoidalCategory.lift (pointAt k x) (pointAt k y) ≫ constantProductMap k f = pointAt k (f x y) := by
  rw [← pointAt_pair, constantProductMap, Category.assoc, Iso.hom_inv_id_assoc,
    ← (testSpec k).map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  change pairEvaluation k x y ((piScalarRight k k (G → k) H).symm
    (fun h g => z (f g h))) = z (f x y)
  rw [pair_eval_eq, AlgEquiv.apply_symm_apply]

private def constantHopfMap {G H : Type u} [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H] (f : G →* H) :
    constantHopf k H ⟶ constantHopf k G := by
  refine ⟨BialgHom.ofAlgHom (reindex k f) ?_ ?_⟩
  · ext x : 1
    change x (f 1) = x 1
    rw [map_one]
  · ext x : 1
    change _ = constantDelta k G (reindex k f (x : H → k))
    apply pair_ext k
    intro g h
    have hp : (pairEvaluation k g h).comp (map (reindex k f) (reindex k f)) =
        pairEvaluation k (f g) (f h) := by
      apply Algebra.TensorProduct.ext'
      intro a b
      simp [pair_eval_tmul, reindex]
    change ((pairEvaluation k g h).comp (map (reindex k f) (reindex k f)))
        (constantDelta k H x) = pairEvaluation k g h (constantDelta k G (reindex k f x))
    rw [hp]
    exact (eval_constantDelta k H (x : H → k) (f g) (f h)).trans
      ((congrArg (x : H → k) (map_mul f g h).symm).trans
        (eval_constantDelta k G (reindex k f (x : H → k)) g h).symm)

end ConstantSchemes
section Solvability

open Specs.SchemeDerivedGroup (IsCommutative)
open scoped CategoryTheory.MonObj

private theorem solvable_of_commutative_normal {k : Type u} [Field k]
    (G : Specs.AffineAlgebraicGroup k) (N : ClosedSubgroup G.val)
    (hN : IsNormalSubgroup N.inclusion) (hc : IsCommutative N.group)
    (hf : Specs.SchemeDerivedGroup.FactorsThrough N
      (Specs.SchemeDerivedGroup.commutatorMap (𝟙 G.val) (𝟙 G.val))) :
    Specs.SchemeDerivedGroup.IsSolvable G.val := by
  obtain ⟨D, hD⟩ := SchemeDerivedGroup.derivedSubgroupExists G
  obtain ⟨j, hj⟩ := hD.2.2 N hN hf
  let C := SchemeOver k
  let H := D.group
  have hi : Mono D.inclusion.hom.hom :=
    letI : IsClosedImmersion D.inclusion.hom.hom.left := D.isClosedImmersion
    Over.mono_of_mono_left _
  have hj' : j.hom.hom ≫ N.inclusion.hom.hom = D.inclusion.hom.hom :=
    congrArg (Grp.forget C).map hj
  have hjmono : Mono j.hom.hom := by
    have : Mono (j.hom.hom ≫ N.inclusion.hom.hom) := hj' ▸ hi
    exact mono_of_mono j.hom.hom N.inclusion.hom.hom
  have hH : IsCommutative H := by
    intro T a b
    apply (cancel_mono j.hom.hom).mp
    let m : (T ⟶ H.X) →* (T ⟶ N.group.X) := ((yonedaGrp.map j).app (op T)).hom
    change m (a * b) = m (b * a)
    rw [map_mul, map_mul, hc]
  let J := Grp.trivial C
  let e : J ⟶ H := default
  have he : e.hom.hom = η[H.X] := rfl
  let E : ClosedSubgroup H := ⟨J, e, by
    apply isClosedImmersion_of_comp_eq_id H.X.hom e.hom.hom.left
    exact e.hom.hom.w⟩
  have heq {T : SchemeOver k} : toUnit T ≫ e.hom.hom = (1 : T ⟶ H.X) := by
    rw [he]
    rfl
  have hE : Specs.SchemeDerivedGroup.IsDerivedSubgroup E := by
    refine ⟨⟨toUnit _, ?_⟩, ⟨toUnit _, ?_⟩, ?_⟩
    · change toUnit _ ≫ e.hom.hom = Specs.subgroupConjugation e
      rw [heq]
      unfold Specs.subgroupConjugation
      have h : snd H.X J.X = toUnit (H.X ⊗ J.X) :=
        (isTerminalTensorUnit (C := C)).hom_ext _ _
      rw [h, heq, mul_one, mul_inv_cancel]
    · change toUnit _ ≫ e.hom.hom =
        Specs.SchemeDerivedGroup.commutatorMap (𝟙 H) (𝟙 H)
      rw [heq]
      change 1 = fst H.X H.X * snd H.X H.X * (fst H.X H.X)⁻¹ * (snd H.X H.X)⁻¹
      rw [hH _ (fst _ _) (snd _ _), mul_assoc (snd _ _), mul_inv_cancel, mul_one,
        mul_inv_cancel]
    · intro N' _ _
      exact ⟨default, Subsingleton.elim _ _⟩
  refine ⟨2, J, ?_, ⟨Iso.refl _⟩⟩
  exact .succ (.succ .zero D hD) E hE

private abbrev A₃ := alternatingGroup (Fin 3)

private theorem s3_solvable :
    Specs.SchemeDerivedGroup.IsSolvable (constantScheme ℂ S₃) := by
  classical
  let G := constantScheme ℂ S₃
  let H := constantScheme ℂ A₃
  let i : H ⟶ G := specGroupMap (constantHopfMap ℂ (alternatingGroup (Fin 3)).subtype)
  have hi : i.hom.hom = affineMap ℂ (reindex ℂ (fun a : A₃ => (a : S₃))) := rfl
  let N : ClosedSubgroup G := ⟨H, i, by
    apply (hopfMapClosedImmersion ℂ _).mpr
    intro f
    refine ⟨fun g => if h : g ∈ alternatingGroup (Fin 3) then f ⟨g, h⟩ else 0, ?_⟩
    funext g
    change (if h : (g : S₃) ∈ alternatingGroup (Fin 3) then f ⟨g, h⟩ else 0) = f g
    simp only [g.property, dite_true]⟩
  have hfinite : Algebra.FiniteType ℂ (constantHopf ℂ S₃) := by
    change Algebra.FiniteType ℂ (S₃ → ℂ)
    infer_instance
  let GA : Specs.AffineAlgebraicGroup ℂ :=
    (finiteTypeHopfSpec ℂ).obj (op ⟨constantHopf ℂ S₃, hfinite⟩)
  apply solvable_of_commutative_normal GA N
  · let c (x : S₃) (y : A₃) : A₃ :=
      ⟨x * y.val * x⁻¹, by
        rw [Equiv.Perm.mem_alternatingGroup] at ⊢
        simp [Equiv.Perm.mem_alternatingGroup.mp y.property]⟩
    refine ⟨constantProductMap ℂ c, ?_⟩
    apply constantScheme_product_hom_ext (k := ℂ)
    intro x y
    rw [← Category.assoc, pointAt_comp_productMap, hi, pointAt_comp]
    change _ = _ ≫ (fst G.X H.X * (snd G.X H.X ≫ i.hom.hom) * (fst G.X H.X)⁻¹)
    have hx : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ fst G.X H.X =
        groupPointAt ℂ x := CartesianMonoidalCategory.lift_fst _ _
    have hy : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ snd G.X H.X =
        groupPointAt ℂ y := CartesianMonoidalCategory.lift_snd _ _
    have hi_y : groupPointAt ℂ y ≫ i.hom.hom = groupPointAt ℂ (y : S₃) :=
      hi ▸ pointAt_comp ℂ (fun a : A₃ => (a : S₃)) y
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, hx, ← Category.assoc, hy, hi_y,
      pointAt_inv, pointAt_mul, pointAt_mul]
  · have hcomm : IsMulCommutative A₃ :=
      alternatingGroup.isMulCommutative_of_card_le_three (by simp : Nat.card (Fin 3) ≤ 3)
    have h : fst H.X H.X * snd H.X H.X = snd H.X H.X * fst H.X H.X := by
      apply constantScheme_product_hom_ext (k := ℂ)
      intro x y
      have hx : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ fst H.X H.X =
          groupPointAt ℂ x := CartesianMonoidalCategory.lift_fst _ _
      have hy : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ snd H.X H.X =
          groupPointAt ℂ y := CartesianMonoidalCategory.lift_snd _ _
      rw [MonObj.comp_mul, MonObj.comp_mul, hx, hy, pointAt_mul, pointAt_mul]
      exact congrArg (groupPointAt ℂ) (hcomm.is_comm.comm x y)
    intro T x y
    have he := congrArg (CartesianMonoidalCategory.lift x y ≫ ·) h
    have hx : lift x y ≫ fst H.X H.X = x := CartesianMonoidalCategory.lift_fst x y
    have hy : lift x y ≫ snd H.X H.X = y := CartesianMonoidalCategory.lift_snd x y
    rw [MonObj.comp_mul, MonObj.comp_mul, hx, hy] at he
    exact he
  · let c (x y : S₃) : A₃ :=
      ⟨x * y * x⁻¹ * y⁻¹, by
        rw [Equiv.Perm.mem_alternatingGroup]
        simp [mul_comm, mul_left_comm]⟩
    refine ⟨constantProductMap ℂ c, ?_⟩
    change constantProductMap ℂ c ≫ i.hom.hom = _
    apply constantScheme_product_hom_ext (k := ℂ)
    intro x y
    rw [← Category.assoc, pointAt_comp_productMap, hi, pointAt_comp]
    change _ = _ ≫ (fst G.X G.X * snd G.X G.X * (fst G.X G.X)⁻¹ * (snd G.X G.X)⁻¹)
    have hx : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ fst G.X G.X =
        groupPointAt ℂ x := CartesianMonoidalCategory.lift_fst _ _
    have hy : lift (groupPointAt ℂ x) (groupPointAt ℂ y) ≫ snd G.X G.X =
        groupPointAt ℂ y := CartesianMonoidalCategory.lift_snd _ _
    simp only [MonObj.comp_mul, GrpObj.comp_inv, hx, hy]
    rw [pointAt_inv, pointAt_inv, pointAt_mul, pointAt_mul, pointAt_mul]

private theorem s3_disconnected :
    ¬ ConnectedSpace (constantScheme ℂ S₃).X.left := by
  intro h
  change ConnectedSpace (PrimeSpectrum (S₃ → ℂ)) at h
  let _ : TopologicalSpace S₃ := ⊥
  let _ : DiscreteTopology S₃ := ⟨rfl⟩
  let e := PrimeSpectrum.sigmaToPiHomeo (fun _ : S₃ => ℂ)
  let f : PrimeSpectrum (S₃ → ℂ) → S₃ := fun x => (e.symm x).1
  have hf : Continuous f := (continuous_sigma fun _ => continuous_const).comp e.symm.continuous
  have hs : Function.Surjective f := by
    intro x
    let p : PrimeSpectrum ℂ := ⟨⊥, inferInstance⟩
    exact ⟨e ⟨x, p⟩, by simp [f]⟩
  let _ := hs.connectedSpace hf
  have hs₃ : Subsingleton S₃ := PreconnectedSpace.trivial_of_discrete
  have he : (Equiv.swap 0 1 : S₃) = 1 := hs₃.elim _ _
  have he' := congrArg (fun σ : S₃ => σ 0) he
  simp at he'

end Solvability
section PermutationPlane

private theorem plane_sum (x : SumZeroPlane) : ∑ i : Fin 3, x.val i = 0 := by
  simpa only [LinearMap.sum_apply, LinearMap.proj_apply] using
    (LinearMap.mem_ker.mp x.property)

private theorem plane_sum_three (x : SumZeroPlane) : x.val 0 + x.val 1 + x.val 2 = 0 := by
  simpa [Fin.sum_univ_three, add_assoc] using plane_sum x

private def planeVector (a b : ℂ) : SumZeroPlane :=
  ⟨![a, b, -a - b], LinearMap.mem_ker.mpr (by
    simp [Fin.sum_univ_three])⟩

private def planeEquiv : SumZeroPlane ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun x := ![x.val 0, x.val 1]
  invFun x := planeVector (x 0) (x 1)
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · change -x.val 0 - x.val 1 = x.val 2
      linear_combination -plane_sum_three x
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' x y := by
    funext i
    fin_cases i <;> rfl
  map_smul' c x := by
    funext i
    fin_cases i <;> rfl

private def permutationAction (g : S₃) : SumZeroPlane →ₗ[ℂ] SumZeroPlane where
  toFun x :=
    ⟨fun i => x.val (g⁻¹ i), LinearMap.mem_ker.mpr (by
      change (∑ i, (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)) _ = 0
      simp only [LinearMap.sum_apply, LinearMap.proj_apply]
      exact (Equiv.sum_comp (g⁻¹) x.val).trans (plane_sum x))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem permutationAction_mul (g h : S₃) :
    permutationAction (g * h) = permutationAction g ∘ₗ permutationAction h := by
  ext x i
  rfl

private theorem permutationAction_one : permutationAction (1 : S₃) = LinearMap.id := by
  ext x i
  rfl

private def root01 : SumZeroPlane := planeVector 1 (-1)
private def root12 : SumZeroPlane := planeVector 0 1

private theorem simple_permutationAction (P : Submodule ℂ SumZeroPlane)
    (hP : ∀ x ∈ P, ∀ g : S₃, permutationAction g x ∈ P) : P = ⊥ ∨ P = ⊤ := by
  classical
  by_cases hbot : P = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  let s : S₃ := Equiv.swap 0 1
  let t : S₃ := Equiv.swap 1 2
  have hs : x - permutationAction s x = (x.val 0 - x.val 1) • root01 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [s, permutationAction, Equiv.swap_apply_def, root01, planeVector, Pi.sub_apply,
        smul_eq_mul]
  have ht : x - permutationAction t x = (x.val 1 - x.val 2) • root12 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [t, permutationAction, Equiv.swap_apply_def, root12, planeVector, Pi.sub_apply,
        smul_eq_mul]
  let c : S₃ := s * t
  have hc : permutationAction c root01 = root12 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      norm_num [c, s, t, permutationAction, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
        root01, root12, planeVector]
  have hc' : permutationAction c⁻¹ root12 = root01 := by
    rw [← hc, ← LinearMap.comp_apply, ← permutationAction_mul, inv_mul_cancel,
      permutationAction_one, LinearMap.id_apply]
  have hroots : root01 ∈ P ∧ root12 ∈ P := by
    by_cases h01 : x.val 0 = x.val 1
    · have h12 : x.val 1 ≠ x.val 2 := by
        intro he
        have hzero : x.val 2 = 0 := by
          have hz := plane_sum_three x
          rw [h01, he] at hz
          linear_combination (1 / 3 : ℂ) * hz
        apply hx0
        apply Subtype.ext
        funext i
        fin_cases i <;> simp [h01, he, hzero]
      have ht' := P.sub_mem hx (hP x hx t)
      rw [ht] at ht'
      have hr := P.smul_mem (x.val 1 - x.val 2)⁻¹ ht'
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr h12), one_smul] at hr
      exact ⟨hc' ▸ hP root12 hr c⁻¹, hr⟩
    · have hs' := P.sub_mem hx (hP x hx s)
      rw [hs] at hs'
      have hr := P.smul_mem (x.val 0 - x.val 1)⁻¹ hs'
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr h01), one_smul] at hr
      exact ⟨hr, hc ▸ hP root01 hr c⟩
  apply eq_top_iff.mpr
  intro y _
  have hy : y = y.val 0 • root01 + (-y.val 2) • root12 := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [root01, root12, planeVector, smul_eq_mul]
    linear_combination plane_sum_three y
  rw [hy]
  exact P.add_mem (P.smul_mem _ hroots.1) (P.smul_mem _ hroots.2)

end PermutationPlane
section PermutationCoaction

open RationalRepresentations

private theorem permutation_comodule :
    SimplePermutationComodule (constantHopf ℂ S₃) (evalAt ℂ) := by
  let A := constantHopf ℂ S₃
  let ev (g : S₃) : A →ₐ[ℂ] ℂ := evalAt ℂ g
  let b : Module.Basis (Fin 2) ℂ SumZeroPlane := (Pi.basisFun ℂ (Fin 2)).map planeEquiv.symm
  let M : Matrix (Fin 2) (Fin 2) A :=
    fun i j g => LinearMap.toMatrix b b (permutationAction g) i j
  have hM : IsCoactionMatrix A M := by
    constructor
    · intro i j
      apply pair_ext ℂ
      intro g h
      change pairEvaluation ℂ g h (constantDelta ℂ S₃ (M i j)) = _
      rw [eval_constantDelta, map_sum]
      change LinearMap.toMatrix b b (permutationAction (g * h)) i j =
        ∑ l, pairEvaluation ℂ g h
          (((M i l : S₃ → ℂ)) ⊗ₜ[ℂ] ((M l j : S₃ → ℂ)))
      simp only [pair_eval_tmul]
      change LinearMap.toMatrix b b (permutationAction (g * h)) i j =
        (LinearMap.toMatrix b b (permutationAction g) *
          LinearMap.toMatrix b b (permutationAction h)) i j
      exact congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => X i j) (by
        rw [permutationAction_mul, LinearMap.toMatrix_comp b b b])
    · intro i j
      change LinearMap.toMatrix b b (permutationAction 1) i j = _
      rw [permutationAction_one, LinearMap.toMatrix_id]
  let ρ := coactionOfMatrix A b M hM
  have he (g : S₃) (x : SumZeroPlane) :
      (TensorProduct.rid ℂ SumZeroPlane) (evaluate A ρ (ev g) x) =
        permutationAction g x := by
    have he' : (TensorProduct.rid ℂ SumZeroPlane).toLinearMap.comp
        (evaluate A ρ (ev g)) = permutationAction g := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, evaluate]
      rw [coaction_apply_basis A b ρ, coefficients_coactionOfMatrix]
      simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      have hentry (i : Fin 2) : (ev g).toLinearMap (M i j) =
          b.repr (permutationAction g (b j)) i := LinearMap.toMatrix_apply b b _ i j
      simp only [hentry]
      exact b.sum_repr _
    exact DFunLike.congr_fun he' x
  refine ⟨ρ, fun g x i => ?_, ?_⟩
  · change ((TensorProduct.rid ℂ SumZeroPlane) (evaluate A ρ (ev g) x)).val i = _
    rw [he]
    rfl
  · intro P hP
    apply simple_permutationAction P
    intro x hx g
    have hx' := (stableSubspaces A ρ P).mpr hP (CommAlgCat.of ℂ ℂ) (ev g) ⟨x, hx⟩
    obtain ⟨w, hw⟩ := hx'
    rw [← he g x, ← hw]
    have h (y : P ⊗[ℂ] ℂ) :
        (TensorProduct.rid ℂ SumZeroPlane) (P.subtype.rTensor ℂ y) =
          ((TensorProduct.rid ℂ P) y).val := by
      induction y using TensorProduct.inductionOn with
      | tmul a c => simp
      | add a c ha hc => simp [ha, hc]
    rw [h]
    exact ((TensorProduct.rid ℂ P) w).property

theorem symmetricGroupBoundary : SymmetricGroupBoundary := by
  refine ⟨constantOperations ℂ S₃, eval_constantDelta ℂ S₃, fun _ => rfl, fun _ _ => rfl,
    ?_, s3_disconnected, s3_solvable, ?_, permutation_comodule⟩
  · rw [Module.finrank_pi, Fintype.card_perm, Fintype.card_fin]
    decide
  · calc
      Module.finrank ℂ SumZeroPlane = Module.finrank ℂ (Fin 2 → ℂ) := planeEquiv.finrank_eq
      _ = 2 := by rw [Module.finrank_pi, Fintype.card_fin]

end PermutationCoaction

end
end LinearAlgebraicGroups.TriangularizationExamples
