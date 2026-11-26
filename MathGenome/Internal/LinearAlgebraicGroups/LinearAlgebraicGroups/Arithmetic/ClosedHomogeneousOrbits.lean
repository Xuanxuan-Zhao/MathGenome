import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.GeometricReductivity
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralDerived
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped BigOperators CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits

open Specs.GeometricReductivity
open Specs.ClosedHomogeneousOrbits (vectorSpace vectorPoint)
open Specs.RootWeightAction (act)
open Specs.GeometricRadicals (IsSemisimple)
open Specs.RootWeightAction (Representation)
open Specs.AdjointRepresentation (GroupPoints)

noncomputable section

variable {k J S : Type u} [Field k] [Fintype J] [DecidableEq J] [Fintype S]
variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- A tuple of coefficients, represented as a linear polynomial with those coefficients. -/
private def tuplePolynomial (a : S → A) : MvPolynomial S A :=
  ∑ i, C (a i) * X i

private theorem map_tuplePolynomial {T : TestAlgebra k} (l : A →ₐ[k] T) (a : S → A) :
    mapAlgHom l (tuplePolynomial a) = tuplePolynomial (fun i ↦ l (a i)) := by
  simp [tuplePolynomial, mapAlgHom_apply]

omit [DecidableEq J] in
private theorem subst_polynomialAction {T : Type u} [CommRing T] (M : Matrix J J T)
    (a b : J → S → T)
    (h : ∀ j i, ∑ l, M l j * a l i = b j i) (F : MvPolynomial J T) :
    aeval (fun j ↦ tuplePolynomial (a j)) (polynomialAction M F) =
      aeval (fun j ↦ tuplePolynomial (b j)) F := by
  suffices (aeval (fun j ↦ tuplePolynomial (a j))).comp (polynomialAction M) =
      (aeval (fun j ↦ tuplePolynomial (b j)) : MvPolynomial J T →ₐ[T] _) from
    DFunLike.congr_fun this F
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, polynomialAction, bind₁_X_right, linearPolynomial, map_sum,
    MvPolynomial.smul_eq_C_mul, map_mul, aeval_C, aeval_X, tuplePolynomial]
  simp_rw [MvPolynomial.algebraMap_eq, Finset.mul_sum, ← mul_assoc, ← C_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← map_sum, h]

omit [Fintype S] in
private theorem eval_mem_span_of_zero_constant (f : S → B) (F : MvPolynomial S B)
    (hF : eval (fun _ ↦ 0) F = 0) :
    eval f F ∈ Ideal.span (Set.range f) := by
  let I := Ideal.span (Set.range f)
  have h : ∀ i, Ideal.Quotient.mk I (f i) = 0 :=
    fun i ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk I (eval f F) = 0
  rw [eval₂_comp, show ((Ideal.Quotient.mk I) ∘ f) = fun _ ↦ 0 from funext h]
  simpa only [Function.comp_def, map_zero, hF] using
    (eval₂_comp (Ideal.Quotient.mk I) (fun _ ↦ 0) F).symm

/-- If the pullbacks of the boundary functions admit a coefficient tuple in a finite
rational module above the trivial line, geometric reductivity makes the original
functions generate the unit ideal. The two maps are the right action and projection
on the fibre product, and `descend` is the descent property of regular functions. -/
theorem span_eq_top_of_invariant_lifting (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Specs.AffineAlgebraicGroup k) (hH : IsSemisimple H)
    (ρ : Representation H.val J) (q : (J → k) →ₗ[k] k) (hq : IsTrivialQuotient ρ q)
    (e : B →ₐ[k] A) (he : Function.Injective e) (T : TestAlgebra k)
    (a b : A →ₐ[k] T) (g : GroupPoints H.val T)
    (descend : ∀ z : A, a z = b z → ∃ w : B, e w = z)
    (f : S → B) (c : J → S → A)
    (hc : ∀ j i, ∑ l, (ρ.app T g).val l j * a (c l i) = b (c j i))
    (hqc : ∀ j, ∑ i, c j i * e (f i) = algebraMap k A (q (Pi.single j 1))) :
    Ideal.span (Set.range f) = ⊤ := by
  obtain ⟨d, F, hd, hF, hfixed, hqF⟩ := LinearAlgebraicGroups.Arithmetic.GeometricReductivity.invariantLifting p H hH ρ q hq
  let P : MvPolynomial S A := aeval (fun j ↦ tuplePolynomial (c j)) F
  have hmap (l : A →ₐ[k] T) :
      map l.toRingHom P =
        aeval (fun j ↦ tuplePolynomial (fun i ↦ l (c j i))) (map (algebraMap k T) F) := by
    change map l.toRingHom (aeval (fun j ↦ tuplePolynomial (c j)) F) = _
    rw [MvPolynomial.map_aeval]
    change eval₂Hom _ _ F = eval₂Hom _ _ (map (algebraMap k T) F)
    rw [eval₂Hom_map_hom]
    apply eval₂Hom_congr
    · ext1 x
      change map l.toRingHom (C (algebraMap k A x)) = C (algebraMap k T x)
      rw [map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, l.commutes]
    · funext j
      exact map_tuplePolynomial l (c j)
    · rfl
  have hP : map a.toRingHom P = map b.toRingHom P := by
    rw [hmap a, hmap b]
    conv_lhs => rw [← hfixed T g]
    exact subst_polynomialAction (ρ.app T g).val _ _ hc _
  have hRange : P ∈ Set.range (map e.toRingHom) := by
    apply mem_range_map_iff_coeffs_subset.mpr
    intro z hz
    obtain ⟨n, _, rfl⟩ := mem_coeffs_iff.mp hz
    apply descend
    change a.toRingHom (P.coeff n) = b.toRingHom (P.coeff n)
    simpa only [coeff_map] using congrArg (fun G : MvPolynomial S T ↦ G.coeff n) hP
  obtain ⟨Q, hQ⟩ := hRange
  have evalP (v : S → A) :
      eval v P = eval₂ (algebraMap k A) (fun j ↦ ∑ i, c j i * v i) F := by
    change eval v (aeval (fun j ↦ tuplePolynomial (c j)) F) = _
    rw [MvPolynomial.map_aeval]
    change eval₂Hom _ _ F = eval₂Hom _ _ F
    apply eval₂Hom_congr
    · ext1 x
      exact eval_C (algebraMap k A x)
    · funext j
      simp [tuplePolynomial]
    · rfl
  have hP1 : eval (e ∘ f) P = 1 := by
    rw [evalP, show (fun j ↦ ∑ i, c j i * (e ∘ f) i) =
      (algebraMap k A) ∘ (fun j ↦ q (Pi.single j 1)) from funext hqc,
      ← eval₂_comp, hqF, map_one]
  have hP0 : eval (fun _ ↦ 0) P = 0 := by
    rw [evalP]
    simp only [mul_zero, Finset.sum_const_zero, eval₂_zero'_apply]
    have hz : F.coeff 0 = 0 := by
      by_contra h
      have hh := hF h
      simp at hh
      omega
    change algebraMap k A (F.coeff 0) = 0
    rw [hz, map_zero]
  have hQ1 : eval f Q = 1 := by
    apply he
    rw [map_one, ← hP1, ← hQ]
    change e.toRingHom (eval f Q) = _
    rw [eval₂_comp, eval_map]
    rfl
  have hQ0 : eval (fun _ ↦ 0) Q = 0 := by
    apply he
    rw [map_zero, ← hP0, ← hQ]
    change e.toRingHom (eval (fun _ ↦ 0) Q) = _
    rw [eval₂_comp, eval_map]
    simp only [Function.comp_def, map_zero]
  exact (Ideal.eq_top_iff_one _).mpr (hQ1 ▸ eval_mem_span_of_zero_constant f Q hQ0)

end

section Descent
noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The coordinate algebra of global sections over the fixed ground field. -/
abbrev globalSections (X : SchemeOver k) : TestAlgebra k :=
  ((algΓ (CommRingCat.of k)).obj X).unop

/-- Pullback on global sections, as a map of algebras over the ground field. -/
abbrev pullSections {X Y : SchemeOver k} (f : X ⟶ Y) :
    globalSections Y →ₐ[k] globalSections X :=
  (((algΓ (CommRingCat.of k)).map f).unop).hom

private def sectionPointEquiv (X : SchemeOver k) :
    globalSections X ≃ (X ⟶ Specs.ClosedHomogeneousOrbits.vectorSpace k PUnit.{u+1}) := by
  let F := algΓAlgSpecAdjunction (CommRingCat.of k)
  let P := op (CommAlgCat.of k (MvPolynomial PUnit.{u+1} k))
  refine (Equiv.trans ?_ (F.homEquiv X P))
  exact
    { toFun := fun s ↦ (CommAlgCat.ofHom (MvPolynomial.aeval fun _ ↦ s)).op
      invFun := fun f ↦ f.unop.hom (MvPolynomial.X PUnit.unit)
      left_inv := by intro s; exact MvPolynomial.aeval_X _ _
      right_inv := by
        intro f
        apply Quiver.Hom.unop_inj
        apply CommAlgCat.hom_ext
        apply MvPolynomial.algHom_ext
        rintro ⟨⟩
        exact MvPolynomial.aeval_X _ _ }

private theorem sectionPointEquiv_natural {X Y : SchemeOver k} (q : X ⟶ Y)
    (s : globalSections Y) :
    sectionPointEquiv X (pullSections q s) = q ≫ sectionPointEquiv Y s := by
  change (algΓAlgSpecAdjunction _).homEquiv _ _
      (CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : PUnit.{u+1} ↦ pullSections q s))).op =
    q ≫ (algΓAlgSpecAdjunction _).homEquiv _ _
      (CommAlgCat.ofHom (MvPolynomial.aeval (fun _ : PUnit.{u+1} ↦ s))).op
  rw [← Adjunction.homEquiv_naturality_left]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact (MvPolynomial.comp_aeval (fun _ : PUnit.{u+1} ↦ s) (pullSections q)).symm

/-- Global sections satisfy the equalizer condition for an fppf projection.
The two test maps are any chosen presentation of its kernel pair. -/
theorem sections_descent {X Y W : SchemeOver k} (q : X ⟶ Y) (a b : W ⟶ X)
    (hab : IsPullback a b q q)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left] :
    Function.Injective (pullSections q) ∧
      ∀ z : globalSections X, pullSections a z = pullSections b z →
        ∃ w : globalSections Y, pullSections q w = z := by
  have : Epi q := Over.epi_of_epi_left q
  refine ⟨fun x y h ↦ (sectionPointEquiv Y).injective ((cancel_epi q).mp ?_), ?_⟩
  · simpa only [sectionPointEquiv_natural] using congrArg (sectionPointEquiv X) h
  · intro z hz
    let e := sectionPointEquiv X z
    have h : a ≫ e = b ≫ e := by
      simpa only [sectionPointEquiv_natural] using congrArg (sectionPointEquiv W) hz
    have hp := hab.map (Over.forget _)
    have he {Z : Scheme} (l r : Z ⟶ X.left) (hEq : l ≫ q.left = r ≫ q.left) :
        l ≫ e.left = r ≫ e.left := by
      let p := hp.lift l r hEq
      have ha : p ≫ a.left = l := hp.lift_fst l r hEq
      have hb : p ≫ b.left = r := hp.lift_snd l r hEq
      rw [← ha, ← hb, Category.assoc, Category.assoc, ← Over.comp_left, h, Over.comp_left]
    let d := EffectiveEpi.desc q.left e.left he
    have hd : q.left ≫ d = e.left := EffectiveEpi.fac q.left e.left he
    let w := Over.homMk d (show d ≫ _ = Y.hom by
      rw [← cancel_epi q.left, ← Category.assoc, hd, Over.w, Over.w])
    refine ⟨(sectionPointEquiv Y).symm w, (sectionPointEquiv X).injective ?_⟩
    rw [sectionPointEquiv_natural, Equiv.apply_symm_apply]
    exact Over.OverMorphism.ext hd


/-- A morphism with affine source of a quasi-affine scheme pulls back a finite collection
of affine basic opens to sections generating the unit ideal upstairs. -/
theorem exists_basicOpen_cover {X Y : SchemeOver k} (q : X ⟶ Y)
    [IsAffine X.left] [Y.left.IsQuasiAffine] :
    ∃ (S : Type u) (_ : Fintype S) (f : S → globalSections Y),
      (∀ i, IsAffineOpen (Y.left.basicOpen (f i))) ∧
        Ideal.span (Set.range (pullSections q ∘ f)) = ⊤ := by
  classical
  let I := { r : globalSections Y // IsAffineOpen (Y.left.basicOpen r) }
  let U (i : I) := Y.left.basicOpen i.val
  have hU : (⨆ i : I, U i) = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
      (Scheme.IsQuasiAffine.isBasis_basicOpen Y.left).exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    exact Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hxr⟩
  have hUs : (Set.univ : Set Y.left) ⊆ ⋃ i : I, (U i : Set Y.left) := by
    rw [← Opens.coe_iSup, hU, Opens.coe_top]
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set Y.left)).elim_finite_subcover
    (fun i : I ↦ (U i : Set Y.left)) (fun i ↦ (U i).2) hUs
  let f : t → globalSections Y := fun i ↦ i.val.val
  refine ⟨t, inferInstance, f, fun i ↦ i.val.property, ?_⟩
  change Ideal.span (Set.range (fun i ↦ q.left.appTop (f i))) = ⊤
  apply (isAffineOpen_top X.left).iSup_basicOpen_eq_self_iff.mp
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (q.left x)))
  refine Opens.mem_iSup.mpr ⟨⟨q.left.appTop (f ⟨i, hi⟩), ⟨⟨i, hi⟩, rfl⟩⟩, ?_⟩
  change x ∈ X.left.basicOpen (q.left.appTop (f ⟨i, hi⟩))
  rw [← Scheme.preimage_basicOpen_top]
  exact hxi

/-- The affine basic-open criterion, written for a finite family of global sections. -/
theorem affine_of_basicOpen_cover {Y : SchemeOver k} {S : Type u} (f : S → globalSections Y)
    (hf : ∀ i, IsAffineOpen (Y.left.basicOpen (f i)))
    (hspan : Ideal.span (Set.range f) = ⊤) : IsAffine Y.left := by
  apply isAffine_of_isAffineOpen_basicOpen (Set.range f) hspan
  rintro _ ⟨i, rfl⟩
  exact hf i

end

end Descent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {k I : Type u} [Field k] {G : Specs.GroupScheme k}

private theorem affineHom_ext {X Y : SchemeOver k} [IsAffine X.left] {f g : X ⟶ Y}
    (h : ∀ (R : TestAlgebra k) (p : Points X R), p ≫ f = p ≫ g) : f = g := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  exact (cancel_epi e.hom).mp (h A.unop e.hom)

private theorem exists_affineHom_of_points {X Y : SchemeOver k} [IsAffine X.left]
    (f : ∀ R : TestAlgebra k, Points X R → Points Y R)
    (hf : ∀ {R S : TestAlgebra k} (a : R ⟶ S) (x : Points X R),
      f S (mapPoints a x) = mapPoints a (f R x)) :
    ∃ g : X ⟶ Y, ∀ (R : TestAlgebra k) (x : Points X R), x ≫ g = f R x := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  refine ⟨e.inv ≫ f A.unop e.hom, fun R x ↦ ?_⟩
  obtain ⟨a, ha⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective (x ≫ e.inv)
  rw [← Category.assoc, ← ha]
  have hx : mapPoints a.unop e.hom = x := by change (testSpec k).map a ≫ e.hom = x; simp [ha]
  rw [← hx, hf]
  rfl

private theorem map_vectorPoint {R S : TestAlgebra k} (f : R ⟶ S) (v : I → R) :
    mapPoints f (vectorPoint R v) = vectorPoint S (fun i ↦ f.hom (v i)) := by
  rw [show mapPoints f (vectorPoint R v) = (testSpec k).map
    (f.op ≫ (CommAlgCat.ofHom (MvPolynomial.aeval v)).op) from
      ((testSpec k).map_comp _ _).symm]
  congr 1
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  exact MvPolynomial.comp_aeval v f.hom

private theorem vectorPoint_bijective (R : TestAlgebra k) :
    Function.Bijective (vectorPoint (I := I) R) := by
  constructor
  · intro v w h
    apply _root_.funext
    have eq : MvPolynomial.aeval (R := k) v = MvPolynomial.aeval w :=
      congrArg (fun f ↦ f.unop.hom) ((algSpec.fullyFaithful (R := CommRingCat.of k)).map_injective h)
    intro i
    simpa only [MvPolynomial.aeval_X] using
      DFunLike.congr_fun eq (MvPolynomial.X i)
  · intro x
    obtain ⟨f, hf⟩ := (algSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective x
    refine ⟨fun i ↦ f.unop.hom (MvPolynomial.X i), ?_⟩
    rw [← hf, vectorPoint]
    congr 1
    apply Quiver.Hom.unop_inj
    apply CommAlgCat.hom_ext
    apply MvPolynomial.algHom_ext
    exact MvPolynomial.aeval_X _

private def vectorPointEquiv (R : TestAlgebra k) : (I → R) ≃ Points (vectorSpace k I) R :=
  Equiv.ofBijective (vectorPoint R) (vectorPoint_bijective R)

variable [Fintype I] [DecidableEq I]

private theorem map_act (ρ : Representation G I) {R S : TestAlgebra k} (f : R ⟶ S)
    (g : Points G.X R) (v : I → R) :
    (fun i ↦ f.hom (act ρ R g v i)) = act ρ S (mapPoints f g) (fun i ↦ f.hom (v i)) := by
  have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (ρ.naturality f)) g
  change ρ.app S (mapPoints f g) = Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ.app R g) at hn
  unfold act
  rw [hn]
  funext i
  exact RingHom.map_mulVec _ _ _ i

private theorem act_one (ρ : Representation G I) (R : TestAlgebra k) (v : I → R) :
    act ρ R (1 : GroupPoints G R) v = v := by
  simp [act]

private theorem act_mul (ρ : Representation G I) (R : TestAlgebra k)
    (g h : GroupPoints G R) (v : I → R) :
    act ρ R (g * h) v = act ρ R g (act ρ R h v) := by
  simp [act, Matrix.mulVec_mulVec]
  rfl

/-- The natural action of a rational representation on the corresponding affine
space, with the coordinate formula over every test algebra. -/
theorem exists_vectorAction (ρ : Representation G I) [IsAffine G.X.left] :
    ∃ a : ModObj G.X (vectorSpace k I), ∀ (R : TestAlgebra k)
      (g : Points G.X R) (v : I → R),
      lift g (vectorPoint R v) ≫ a.smul = vectorPoint R (act ρ R g v) := by
  let V := vectorSpace k I
  have : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (G.X ⊗ V).left := inferInstanceAs (IsAffine (pullback G.X.hom V.hom))
  let f (R : TestAlgebra k) (x : Points (G.X ⊗ V) R) : Points V R :=
    vectorPoint R (act ρ R (x ≫ fst _ _) ((vectorPointEquiv R).symm (x ≫ snd _ _)))
  have hf {R S : TestAlgebra k} (l : R ⟶ S) (x : Points (G.X ⊗ V) R) :
      f S (mapPoints l x) = mapPoints l (f R x) := by
    obtain ⟨v, hv⟩ := (vectorPoint_bijective R).2 (x ≫ snd _ _)
    have h : (vectorPointEquiv R).symm (x ≫ snd _ _) = v :=
      (vectorPointEquiv R).symm_apply_eq.mpr hv.symm
    have h' : (vectorPointEquiv S).symm (mapPoints l x ≫ snd _ _) = fun i ↦ l.hom (v i) := by
      apply (vectorPointEquiv S).symm_apply_eq.mpr
      change mapPoints l x ≫ snd _ _ = vectorPoint S (fun i ↦ l.hom (v i))
      rw [show mapPoints l x ≫ snd _ _ = mapPoints l (x ≫ snd _ _) from Category.assoc ..,
        ← hv, map_vectorPoint]
    simp only [f, h, h', map_vectorPoint, map_act]
    rfl
  obtain ⟨a, ha⟩ := exists_affineHom_of_points f hf
  have hact (R : TestAlgebra k) (g : Points G.X R) (v : I → R) :
      lift g (vectorPoint R v) ≫ a = vectorPoint R (act ρ R g v) := by
    rw [ha]
    have hfst : lift g (vectorPoint R v) ≫ fst G.X V = g := lift_fst _ _
    have hsnd : lift g (vectorPoint R v) ≫ snd G.X V = vectorPoint R v := lift_snd _ _
    have hv : (vectorPointEquiv R).symm (vectorPoint R v) = v :=
      (vectorPointEquiv R).symm_apply_apply v
    simp only [f, hfst, hsnd, hv]
  refine ⟨⟨a, ?_, ?_⟩, hact⟩
  · have : IsAffine ((𝟙_ (SchemeOver k)) ⊗ V).left :=
      inferInstanceAs (IsAffine (pullback (𝟙 (Spec (CommRingCat.of k))) V.hom))
    apply affineHom_ext
    intro R x
    obtain ⟨v, hv⟩ := (vectorPoint_bijective R).2 (x ≫ snd _ _)
    have e : x ≫ (η[G.X] ▷ V) = lift (1 : Points G.X R) (vectorPoint R v) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerRight_fst, lift_fst, Hom.one_def]
        exact congrArg (fun t ↦ t ≫ η[G.X]) (toUnit_unique (x ≫ fst _ _) (toUnit _))
      · rw [Category.assoc, whiskerRight_snd, lift_snd]
        exact hv.symm
    change x ≫ (η[G.X] ▷ V) ≫ a = x ≫ (λ_ V).hom
    rw [← Category.assoc, e, hact, act_one, hv, leftUnitor_hom]
  · have : IsAffine (G.X ⊗ G.X).left := inferInstanceAs (IsAffine (pullback G.X.hom G.X.hom))
    have : IsAffine ((G.X ⊗ G.X) ⊗ V).left :=
      inferInstanceAs (IsAffine (pullback (G.X ⊗ G.X).hom V.hom))
    apply affineHom_ext
    intro R x
    let g : Points G.X R := x ≫ fst (G.X ⊗ G.X) V ≫ fst G.X G.X
    let h : Points G.X R := x ≫ fst (G.X ⊗ G.X) V ≫ snd G.X G.X
    obtain ⟨v, hv⟩ := (vectorPoint_bijective R).2 (x ≫ snd _ _)
    have el : x ≫ (μ[G.X] ▷ V) = lift (g * h) (vectorPoint R v) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, whiskerRight_fst, lift_fst, Hom.mul_def]
        have ee : lift g h = x ≫ fst (G.X ⊗ G.X) V := by
          apply CartesianMonoidalCategory.hom_ext
          · exact lift_fst _ _
          · exact lift_snd _ _
        rw [ee, Category.assoc]
      · rw [Category.assoc, whiskerRight_snd, lift_snd]
        exact hv.symm
    have er : x ≫ (α_ G.X G.X V).hom ≫ G.X ◁ a =
        lift g (lift h (vectorPoint R v) ≫ a) := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [g, Category.assoc, whiskerLeft_fst, associator_hom_fst, lift_fst]
      · have e : x ≫ (α_ G.X G.X V).hom ≫ snd G.X (G.X ⊗ V) =
            lift h (vectorPoint R v) := by
          apply CartesianMonoidalCategory.hom_ext
          · rw [lift_fst, Category.assoc, Category.assoc, associator_hom_snd_fst]
          · rw [lift_snd, Category.assoc, Category.assoc, associator_hom_snd_snd]
            exact hv.symm
        simp only [Category.assoc, whiskerLeft_snd, lift_snd]
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ a) e
    change x ≫ (μ[G.X] ▷ V) ≫ a = x ≫ (α_ G.X G.X V).hom ≫ (G.X ◁ a) ≫ a
    calc
      _ = vectorPoint R (act ρ R (g * h) v) := by rw [← Category.assoc, el, hact]
      _ = _ := by
        rw [← Category.assoc (α_ G.X G.X V).hom, ← Category.assoc x, er, hact, hact, act_mul]

end

section SpecialLinear

open Specs.StandardGroups (SLCoordinates determinantOneIdeal universalMatrix specialLinearPoints)
open private slEvaluation evaluatedSpecialLinear slEvaluation_entry glCoordinates_ext
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k I : Type u} [Field k] [Fintype I] [DecidableEq I]

private theorem lift_specialLinear {B : Type u} [CommRing B]
    (J : Ideal B) (hJ : J ^ 2 = ⊥) (g : Matrix.SpecialLinearGroup I (B ⧸ J)) :
    ∃ h : Matrix.SpecialLinearGroup I B, Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk J) h = g := by
  classical
  by_cases hI : Nonempty I
  · let i := Classical.choice hI
    choose s hs using (Ideal.Quotient.mk_surjective (I := J))
    let M : Matrix I I B := fun l j ↦ s (g l j)
    have hM : (Ideal.Quotient.mk J).mapMatrix M = g.val := Matrix.ext fun l j ↦ hs _
    have hd : Ideal.Quotient.mk J M.det = 1 := by
      rw [RingHom.map_det, hM, g.det_coe]
    have hδ : M.det - 1 ∈ J := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hd, map_one, sub_self]
    have hδ₂ : (M.det - 1) * (M.det - 1) = 0 := by
      have h := Ideal.mul_mem_mul hδ hδ
      rw [← pow_two, hJ] at h
      exact h
    let d : I → B := fun l ↦ if l = i then 1 - (M.det - 1) else 1
    have hd₁ : ∏ l, d l = 1 - (M.det - 1) := by
      simp [d, Finset.prod_ite_eq']
    have hd₂ : (Ideal.Quotient.mk J).mapMatrix (Matrix.diagonal d) = 1 := by
      ext l j
      by_cases hl : l = j
      · subst j
        change Ideal.Quotient.mk J (Matrix.diagonal d l l) = _
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        simp [d, apply_ite, hd]
      · change Ideal.Quotient.mk J (Matrix.diagonal d l j) = _
        simp [Matrix.diagonal_apply_ne _ hl, Matrix.one_apply_ne hl]
    let N := Matrix.diagonal d * M
    have hN : N.det = 1 := by
      rw [Matrix.det_mul, Matrix.det_diagonal, hd₁]
      linear_combination -hδ₂
    refine ⟨⟨N, hN⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro l j
    change (Ideal.Quotient.mk J).mapMatrix N l j = _
    have hn : (Ideal.Quotient.mk J).mapMatrix N =
        (Ideal.Quotient.mk J).mapMatrix (Matrix.diagonal d) *
          (Ideal.Quotient.mk J).mapMatrix M :=
      Matrix.map_mul (f := Ideal.Quotient.mk J)
    rw [hn, hd₂, one_mul, hM]
  · haveI : IsEmpty I := not_nonempty_iff.mp hI
    exact ⟨1, Subsingleton.elim _ _⟩

private theorem specialLinearCoordinates_formallySmooth :
    Algebra.FormallySmooth k (SLCoordinates k I) := by
  apply Algebra.FormallySmooth.iff_comp_surjective.mpr
  intro B _ _ J hJ f
  obtain ⟨h, hh⟩ := lift_specialLinear J hJ (evaluatedSpecialLinear f)
  refine ⟨slEvaluation h, ?_⟩
  apply Ideal.Quotient.algHom_ext k
  apply glCoordinates_ext
  intro l j
  change Ideal.Quotient.mk J
    (slEvaluation h (Ideal.Quotient.mkₐ k (determinantOneIdeal k I) (universalMatrix k I l j))) = _
  rw [slEvaluation_entry]
  exact congrArg (fun M : Matrix.SpecialLinearGroup I (B ⧸ J) ↦ M l j) hh

private theorem specialLinear_smooth (P : Specs.AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj P.val ≅ specialLinearPoints k I) :
    Smooth P.val.X.hom := by
  let Q := StandardGroups.specialLinearGroup k I
  let e' := e ≪≫ (StandardGroups.specialLinearGroupPointsIso k I).symm
  let f := (AffineAlgebraicGroup.groupHomEquiv P Q).symm e'.hom
  let g := (AffineAlgebraicGroup.groupHomEquiv Q P).symm e'.inv
  have hf : (groupPointsFunctor k).map f = e'.hom :=
    (AffineAlgebraicGroup.groupHomEquiv P Q).apply_symm_apply _
  have hg : (groupPointsFunctor k).map g = e'.inv :=
    (AffineAlgebraicGroup.groupHomEquiv Q P).apply_symm_apply _
  let iso : P.val ≅ Q.val :=
    ⟨f, g,
      (AffineAlgebraicGroup.groupHomEquiv P P).injective (by
        change (groupPointsFunctor k).map (f ≫ g) = (groupPointsFunctor k).map _
        simp [hf, hg]),
      (AffineAlgebraicGroup.groupHomEquiv Q Q).injective (by
        change (groupPointsFunctor k).map (g ≫ f) = (groupPointsFunctor k).map _
        simp [hf, hg])⟩
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hi : IsIso iso.hom.hom.hom.left := by
    change IsIso (F.map iso.hom)
    rw [← F.mapIso_hom]
    infer_instance
  haveI : Algebra.FormallySmooth k (SLCoordinates k I) := specialLinearCoordinates_formallySmooth
  haveI : Algebra.Smooth k (SLCoordinates k I) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have hQ : Smooth Q.val.X.hom := by
    change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (SLCoordinates k I))))
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  rw [← Over.w iso.hom.hom.hom]
  infer_instance

end

end SpecialLinear

section Characters

open Specs.GeometricRadicals (IsSemisimple)
open Specs.RootWeightAction (Representation act)
open Specs.AdjointRepresentation (GroupPoints)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

open private reductive_of_semisimple from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private trivial_baseChange_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private hom_ext_of_points from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.GroupSchemes
open private coordinateLine_iff_unit from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ChevalleyLine

/-- Every morphism from a semisimple group to a commutative affine algebraic group
sends all scheme-valued sections to the identity. -/
theorem hom_to_commutative_eq_one (G L : Specs.AffineAlgebraicGroup k)
    (hG : IsSemisimple G) (hL : Specs.SchemeDerivedGroup.IsCommutative L.val)
    (χ : G.val ⟶ L.val) : χ.hom.hom = 1 := by
  have hr := reductive_of_semisimple G hG
  obtain ⟨Z, hZ, T, hT, _⟩ := Reductive.CentralDerived.centralTorusExists G hr
  obtain ⟨D, hD⟩ := SchemeDerivedGroup.derivedSubgroupExists G
  obtain ⟨m, hm, _⟩ := Reductive.CentralDerived.centralProductKernel G hr Z hZ T hT D hD
  obtain ⟨hmf, hms⟩ := Reductive.CentralDerived.centralProductFaithfullyFlat G hr Z hZ T hT D hD m hm
  obtain ⟨e, _⟩ := Reductive.CentralDerived.geometricSolvableRadical G hr Z hZ T hT
  obtain ⟨d⟩ := hG.2.2
  obtain ⟨t⟩ := (trivial_baseChange_iff (K := AlgebraicClosure k) T.group).mp ⟨e.symm ≪≫ d⟩
  obtain ⟨Q, q, hker, _, _, hq⟩ := SchemeDerivedGroup.abelianization G D hD
  obtain ⟨l, hl, _⟩ := hq L hL χ
  have hDt : D.inclusion.hom.hom ≫ q.hom.hom = 1 :=
    (schemeKernel_sections hker (D.inclusion.hom.hom)).mp (by
      refine ⟨𝟙 _, ?_⟩
      change 𝟙 _ ≫ D.inclusion.hom.hom = _
      exact Category.id_comp _)
  have hDχ : D.inclusion.hom.hom ≫ χ.hom.hom = 1 := by
    rw [← hl, Grp.comp_hom_hom, ← Category.assoc, hDt, MonObj.one_comp]
  have hTχ : (T.inclusion ≫ Z.inclusion ≫ χ).hom.hom = 1 := by
    let r := T.inclusion ≫ Z.inclusion ≫ χ
    have h : (t.inv ≫ r).hom.hom = η[L.val.X] := by
      rw [← IsMonHom.one_hom (t.inv ≫ r).hom.hom]
      exact (Category.id_comp _).symm
    calc
      r.hom.hom = t.hom.hom.hom ≫ (t.inv ≫ r).hom.hom := by
        rw [← Grp.comp_hom_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = 1 := by
        rw [h, Hom.one_def, toUnit_unique t.hom.hom.hom (toUnit _)]
  let AT := Specs.Unipotent.closedSubgroupAlgebraicGroup (Specs.GeometricBorelConjugacy.subgroupOfSubgroup Z T)
  let AD := Specs.Unipotent.closedSubgroupAlgebraicGroup D
  letI : IsAffine T.group.X.left := AT.property.1
  letI : IsAffine D.group.X.left := AD.property.1
  haveI : IsAffine ((T.group ⊗ D.group).X).left :=
    inferInstanceAs (IsAffine (pullback T.group.X.hom D.group.X.hom))
  haveI : IsAffine G.val.X.left := G.property.1
  haveI : IsAffineHom m.hom.hom.left := inferInstance
  haveI : Epi m.hom.hom := Over.epi_of_epi_left _
  apply (cancel_epi m.hom.hom).mp
  rw [MonObj.comp_one, hm, MonObj.mul_comp]
  simp only [Grp.comp_hom_hom, Category.assoc] at hTχ ⊢
  rw [hTχ, hDχ, MonObj.comp_one, MonObj.comp_one, one_mul]

private theorem multiplicativeGroup_isCommutative :
    Specs.SchemeDerivedGroup.IsCommutative (StandardGroups.multiplicativeGroup k).val := by
  let L := StandardGroups.multiplicativeGroup k
  letI : IsAffine L.val.X.left := L.property.1
  have hA : IsAffine (L.val.X ⊗ L.val.X).left :=
    inferInstanceAs (IsAffine (pullback L.val.X.hom L.val.X.hom))
  let f := fst L.val.X L.val.X
  let s := snd L.val.X L.val.X
  have h : f * s = s * f := by
    apply hom_ext_of_points hA
    intro R p
    rw [MonObj.comp_mul, MonObj.comp_mul]
    let e := StandardGroups.multiplicativeGroupPointsIso (k := k)
    change (p ≫ f) * (p ≫ s) = (p ≫ s) * (p ≫ f)
    apply (ConcreteCategory.bijective_of_isIso (e.hom.app R)).1
    change e.hom.app R ((p ≫ f) * (p ≫ s)) = e.hom.app R ((p ≫ s) * (p ≫ f))
    simp only [map_mul]
    change (e.hom.app R (p ≫ f) : Rˣ) * e.hom.app R (p ≫ s) =
      (e.hom.app R (p ≫ s) : Rˣ) * e.hom.app R (p ≫ f)
    exact @mul_comm Rˣ _ _ _
  intro T x y
  have he := congrArg (fun z ↦ lift x y ≫ z) h
  rw [MonObj.comp_mul, MonObj.comp_mul] at he
  change (lift x y ≫ fst L.val.X L.val.X) * (lift x y ≫ snd L.val.X L.val.X) =
    (lift x y ≫ snd L.val.X L.val.X) * (lift x y ≫ fst L.val.X L.val.X) at he
  rwa [lift_fst, lift_snd] at he

private theorem coordinateLine_fixed {P : Specs.AffineAlgebraicGroup k} {I : Type u}
    [Fintype I] [DecidableEq I] (i : I) (ρ : Representation P.val I)
    (H : Specs.ClosedSubgroup P.val)
    (hH : IsSemisimple (Specs.Unipotent.closedSubgroupAlgebraicGroup H))
    (hline : ∀ (R : TestAlgebra k) (g : Points P.val.X R),
      Specs.StabilizesCoordinateLine (ρ.app R g) i ↔
        ∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = g) :
    ∀ (R : TestAlgebra k) (g : Points P.val.X R),
      act ρ R g (Pi.single i 1) = Pi.single i 1 ↔
        ∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = g := by
  let A := Specs.Unipotent.closedSubgroupAlgebraicGroup H
  let σ : Representation A.val I := (groupPointsFunctor k).map H.inclusion ≫ ρ
  have hui (R : TestAlgebra k) (g : GroupPoints A.val R) :
      ∃ a : Rˣ, ∀ j, (σ.app R g).val j i = if j = i then (a : R) else 0 :=
    (coordinateLine_iff_unit _ _).mp ((hline R (g ≫ H.inclusion.hom.hom)).mpr ⟨g, rfl⟩)
  let u (R : TestAlgebra k) (g : GroupPoints A.val R) : Rˣ := (hui R g).choose
  have hu (R : TestAlgebra k) (g : GroupPoints A.val R) (j : I) :
      (σ.app R g).val j i = if j = i then (u R g : R) else 0 := (hui R g).choose_spec j
  have hd (R : TestAlgebra k) (g : GroupPoints A.val R) :
      (u R g : R) = (σ.app R g).val i i := by rw [hu]; simp
  let φ : (groupPointsFunctor k).obj A.val ⟶ Specs.StandardGroups.multiplicativePoints k :=
    { app := fun R ↦ GrpCat.ofHom
        { toFun := u R
          map_one' := by
            apply Units.ext
            rw [hd, map_one]
            simp
          map_mul' := by
            intro g h
            apply Units.ext
            rw [hd, map_mul]
            change ∑ j, (σ.app R g).val i j * (σ.app R h).val j i =
                (u R g : R) * (u R h : R)
            simp_rw [hu R h]
            simp [mul_ite, hd R g] }
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro g
        change u S (mapPoints f g) = Units.map f.hom.toMonoidHom (u R g)
        apply Units.ext
        have hn := DFunLike.congr_fun (congrArg GrpCat.Hom.hom (σ.naturality f)) g
        change σ.app S (mapPoints f g) =
          Matrix.GeneralLinearGroup.map f.hom.toRingHom (σ.app R g) at hn
        rw [hd, hn]
        change f.hom ((σ.app R g).val i i) = f.hom (u R g : R)
        rw [hd] }
  let L := StandardGroups.multiplicativeGroup k
  let E := StandardGroups.multiplicativeGroupPointsIso (k := k)
  let χ := (AffineAlgebraicGroup.groupHomEquiv A L).symm (φ ≫ E.inv)
  have hχ : (groupPointsFunctor k).map χ ≫ E.hom = φ := by
    have hh := (AffineAlgebraicGroup.groupHomEquiv A L).apply_symm_apply (φ ≫ E.inv)
    change (groupPointsFunctor k).map χ = _ at hh
    rw [hh]
    simp
  have hχ₁ := hom_to_commutative_eq_one A L hH multiplicativeGroup_isCommutative χ
  have hu₁ (R : TestAlgebra k) (g : GroupPoints A.val R) : u R g = 1 := by
    have hh := DFunLike.congr_fun (congrArg (fun f ↦ (f.app R).hom) hχ) g
    change E.hom.app R (g ≫ χ.hom.hom) = u R g at hh
    rw [hχ₁, MonObj.comp_one, map_one] at hh
    exact hh.symm
  intro R g
  have hcol (j : I) : act ρ R g (Pi.single i 1) j = (ρ.app R g).val j i := by
    simp [act, Matrix.col_apply]
  constructor
  · intro hg
    apply (hline R g).mp
    apply (coordinateLine_iff_unit _ _).mpr
    refine ⟨1, fun j ↦ ?_⟩
    rw [← hcol, hg]
    simp [Pi.single_apply]
  · rintro ⟨h, rfl⟩
    funext j
    rw [hcol]
    change (σ.app R h).val j i = _
    rw [hu, hu₁]
    simp [Pi.single_apply]

end

end Characters

section QuasiAffineOrbit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private compareRepresentatives compareRepresentatives_projection
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient
open private projection_eq_iff isQuasiProjective_of_immersion
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private orbitMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit
open private affineBaseTerminal from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Solvable.SplitFixedPoint

variable {k : Type u} [Field k]

private theorem representsSubgroup_of_points {P : Specs.AffineAlgebraicGroup k}
    {Z : SchemeOver k} (a : ModObj P.val.X Z) (x : 𝟙_ (SchemeOver k) ⟶ Z)
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (H : Specs.ClosedSubgroup P.val)
    (h : ∀ (R : TestAlgebra k) (g : Points P.val.X R),
      Stabilizes a.smul x g ↔ ∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = g) :
    RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) := by
  obtain ⟨S, hS⟩ := stabilizerScheme k P.val Z a x inferInstance inferInstance inferInstance
  have hcongr (R : TestAlgebra k) (g : Points P.val.X R) :
      (∃ h : Points H.group.X R, h ≫ H.inclusion.hom.hom = g) ↔
        (∃ s : Points S.group.X R, s ≫ S.inclusion.hom.hom = g) :=
    (h R g).symm.trans (hS _ g)
  have hh := (Specs.Unipotent.closedSubgroupAlgebraicGroup H).property.1
  have hs := (Specs.Unipotent.closedSubgroupAlgebraicGroup S).property.1
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr hh
  obtain ⟨B, ⟨d⟩⟩ := essImage_algSpec.mpr hs
  obtain ⟨l, hl⟩ := (hcongr A.unop (e.hom ≫ H.inclusion.hom.hom)).mp ⟨e.hom, rfl⟩
  obtain ⟨r, hr⟩ := (hcongr B.unop (d.hom ≫ S.inclusion.hom.hom)).mpr ⟨d.hom, rfl⟩
  have hl' : (e.inv ≫ l) ≫ S.inclusion.hom.hom = H.inclusion.hom.hom := by
    rw [Category.assoc, hl, Iso.inv_hom_id_assoc]
  have hr' : (d.inv ≫ r) ≫ H.inclusion.hom.hom = S.inclusion.hom.hom := by
    rw [Category.assoc, hr, Iso.inv_hom_id_assoc]
  intro T g
  rw [hS]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s ≫ (d.inv ≫ r), by rw [Category.assoc, hr']⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f ≫ (e.inv ≫ l), by rw [Category.assoc, hl']⟩

private theorem exists_quasiAffine_quotient (P : Specs.AffineAlgebraicGroup k)
    (H : Specs.ClosedSubgroup P.val) (hs : Smooth P.val.X.hom)
    (hH : IsSemisimple (Specs.Unipotent.closedSubgroupAlgebraicGroup H)) :
    ∃ (Q : Specs.QuotientEmbedding.Presentation H) (b : ModObj P.val.X Q.scheme),
      Q.scheme.left.IsQuasiAffine ∧ LocallyOfFiniteType Q.scheme.hom ∧
        μ[P.val.X] ≫ Q.projection = (𝟙 P.val.X ⊗ₘ Q.projection) ≫ b.smul := by
  classical
  obtain ⟨I, _, _, i, L, E, f, hf⟩ := chevalleyLine k P H
  let ρ : Representation P.val I := (groupPointsFunctor k).map f ≫ E.hom
  have hρ := coordinateLine_fixed i ρ H hH hf
  letI : IsAffine P.val.X.left := P.property.1
  obtain ⟨a, ha⟩ := exists_vectorAction ρ
  let V := vectorSpace k I
  let R₀ := CommAlgCat.of k k
  let t : 𝟙_ (SchemeOver k) ⟶ (testSpec k).obj (op R₀) := (affineBaseTerminal k).from _
  let x : 𝟙_ (SchemeOver k) ⟶ V := t ≫ vectorPoint R₀ (Pi.single i 1)
  have hx (R : TestAlgebra k) :
      toUnit ((testSpec k).obj (op R)) ≫ x = vectorPoint R (Pi.single i 1) := by
    let α : R₀ ⟶ R := CommAlgCat.ofHom (Algebra.ofId k R)
    have ht : toUnit ((testSpec k).obj (op R)) ≫ t = (testSpec k).map α.op :=
      (affineBaseTerminal k).hom_ext _ _
    rw [show x = t ≫ vectorPoint R₀ (Pi.single i 1) from rfl, ← Category.assoc, ht]
    change mapPoints α (vectorPoint R₀ (Pi.single i 1)) = _
    rw [map_vectorPoint]
    congr 1
    funext j
    by_cases hji : j = i <;> simp [hji, α]
  haveI : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
  haveI : LocallyOfFiniteType V.hom := by
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial I k))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hS : RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul x g) := by
    apply representsSubgroup_of_points a x H
    intro R g
    unfold Stabilizes
    rw [hx R, ha, (vectorPoint_bijective R).1.eq_iff, hρ R g]
  obtain ⟨O⟩ := SmoothOrbit.schemeOrbit k P V a x hs inferInstance inferInstance inferInstance
  let j := O.openInClosure ≫ Specs.SmoothOrbit.closureInclusion a x
  haveI : IsOpenImmersion O.openInClosure.left := O.isOpen
  haveI : IsClosedImmersion (Specs.SmoothOrbit.closureInclusion a x).left := by
    change IsClosedImmersion (Specs.SmoothOrbit.orbitMap a x).left.imageι
    infer_instance
  haveI : IsImmersion j.left := by
    change IsImmersion (O.openInClosure.left ≫ (Specs.SmoothOrbit.closureInclusion a x).left)
    infer_instance
  haveI : Mono j := Over.mono_of_mono_left _
  have hj : O.projection ≫ j = Specs.SmoothOrbit.orbitMap a x := by
    apply Over.OverMorphism.ext
    change (O.projection.left ≫ O.openInClosure.left) ≫
      (Specs.SmoothOrbit.orbitMap a x).left.imageι = _
    rw [O.factors, Scheme.Hom.toImage_imageι]
  obtain ⟨e, he⟩ := SmoothOrbit.orbitQuotient k P.val V O.orbit a x j O.projection H
    inferInstance hj O.flat O.surjective O.finitePresentation hS
  obtain ⟨Q₀⟩ := (HomogeneousQuotient.homogeneousQuotient k P H).1
  let d := compareRepresentatives Q₀ e
  letI : IsImmersion d.inv.left := inferInstance
  let Q : Specs.QuotientEmbedding.Presentation H :=
    ⟨O.orbit, isQuasiProjective_of_immersion d.inv inferInstance Q₀.quasiProjective,
      O.projection, O.flat, O.surjective, O.finitePresentation, e, he⟩
  haveI : CompactSpace O.orbit.left := O.surjective.1.compactSpace O.projection.left.continuous
  have hq : O.orbit.left.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion j.left
  have hft : LocallyOfFiniteType O.orbit.hom := by
    rw [← Over.w j]
    infer_instance
  exact ⟨Q, O.action, hq, hft, O.actionProjection⟩

end

end QuasiAffineOrbit

open WithConv
open scoped TensorProduct CategoryTheory.GrpObj
open Specs.GeometricReductivity
open Specs.GeometricRadicals (IsSemisimple)
open Specs.RootWeightAction (Representation act)
open Specs.AdjointRepresentation (GroupPoints)
open RationalRepresentations

open Specs.HomogeneousQuotient (rightMultiplication)
open Specs.QuotientEmbedding (Presentation)


noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
variable {A C : HopfAlgebraCategory k}

/-- Restriction of right translation along a homomorphism of affine groups. -/
private def translation (φ : A ⟶ C) : A →ₐ[k] A ⊗[k] C :=
  (Algebra.TensorProduct.map (AlgHom.id k A) φ.hom.toAlgHom).comp (Bialgebra.comulAlgHom k A)

private theorem translation_apply (φ : A ⟶ C) (v : A) :
    translation φ v =
      φ.hom.toAlgHom.toLinearMap.lTensor A (Coalgebra.comul (R := k) v) := rfl

private def translationComodule (φ : A ⟶ C) : RightComodule k C A where
  coaction := (translation φ).toLinearMap
  coassoc x := by
    let f := φ.hom.toAlgHom.toLinearMap
    let d : A →ₗ[k] A ⊗[k] A := Coalgebra.comul
    let d' : C →ₗ[k] C ⊗[k] C := Coalgebra.comul
    let δ := f.lTensor A ∘ₗ d
    have h₁ (t : A ⊗[k] A) :
        δ.rTensor C (f.lTensor A t) = TensorProduct.map (f.lTensor A) f (d.rTensor A t) := by
      induction t with
      | tmul v a => simp [δ]
      | add t s ht hs => simp [ht, hs]
    have h₂ (t : A ⊗[k] A) :
        d'.lTensor A (f.lTensor A t) =
          (TensorProduct.map f f).lTensor A (d.lTensor A t) := by
      induction t with
      | tmul v a =>
        simp only [LinearMap.lTensor_tmul]
        congr 1
        exact (CoalgHomClass.map_comp_comul_apply φ.hom a).symm
      | add t s ht hs => simp [ht, hs]
    change TensorProduct.assoc k A C C (δ.rTensor C (f.lTensor A (d x))) =
      d'.lTensor A (f.lTensor A (d x))
    rw [h₁, h₂, show f.lTensor A = TensorProduct.map LinearMap.id f from rfl,
      ← TensorProduct.map_map_assoc, Coalgebra.coassoc_apply]
    rfl
  counit x := by
    let f := φ.hom.toAlgHom.toLinearMap
    have hf : (Coalgebra.counit (R := k) (A := C)).comp f = Coalgebra.counit := by
      ext v
      exact CoalgHomClass.counit_comp_apply φ.hom v
    change TensorProduct.rid k A ((Coalgebra.counit (R := k) (A := C)).lTensor A
      (f.lTensor A (Coalgebra.comul x))) = x
    rw [← LinearMap.lTensor_comp_apply, hf]
    exact (RightComodule.regular : RightComodule k A A).counit x

variable {S V : Type u} [Fintype S] [DecidableEq S] [AddCommGroup V] [Module k V]

private theorem tensor_proj {D : Type u} [AddCommGroup D] [Module k D]
    (t : (S → V) ⊗[k] D) (i : S) :
    TensorProduct.piLeft k D (fun _ : S ↦ V) t i =
      (LinearMap.proj (R := k) i).rTensor D t := by
  induction t with
  | tmul v d => simp
  | add t s ht hs => rw [map_add, Pi.add_apply, map_add, ht, hs]

/-- The diagonal coaction on a finite tuple of elements of a comodule. -/
private def tupleComodule (σ : RightComodule k C V) : RightComodule k C (S → V) := by
  let E := TensorProduct.piLeft k C (fun _ : S ↦ V)
  let δ := E.symm.toLinearMap.comp (LinearMap.pi fun i ↦ σ.coaction.comp (LinearMap.proj i))
  have hδ (x : S → V) (i : S) :
      (LinearMap.proj (R := k) i).rTensor C (δ x) = σ.coaction (x i) := by
    rw [← tensor_proj]
    exact congrFun (E.apply_symm_apply _) i
  refine ⟨δ, ?_, ?_⟩
  · intro x
    apply (TensorProduct.piLeft k (C ⊗[k] C) (fun _ : S ↦ V)).injective
    funext i
    simp only [tensor_proj]
    let p : (S → V) →ₗ[k] V := LinearMap.proj i
    have h₁ (t : (S → V) ⊗[k] C) :
        (p.rTensor C).rTensor C (δ.rTensor C t) =
          σ.coaction.rTensor C (p.rTensor C t) := by
      rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
      rw [show (p.rTensor C).comp δ = σ.coaction.comp p from
        LinearMap.ext fun v ↦ hδ v i]
    have h₂ (t : (S → V) ⊗[k] C) :
        p.rTensor (C ⊗[k] C) ((Coalgebra.comul (R := k) (A := C)).lTensor _ t) =
          (Coalgebra.comul (R := k) (A := C)).lTensor _ (p.rTensor C t) := by
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    have h₃ (t : ((S → V) ⊗[k] C) ⊗[k] C) :
        p.rTensor (C ⊗[k] C) (TensorProduct.assoc k _ C C t) =
          TensorProduct.assoc k V C C ((p.rTensor C).rTensor C t) := by
      simpa only [LinearMap.rTensor, TensorProduct.map_id] using
        TensorProduct.map_map_assoc p (LinearMap.id : C →ₗ[k] C) (LinearMap.id : C →ₗ[k] C) t
    change p.rTensor _ (TensorProduct.assoc k _ C C (δ.rTensor C (δ x))) =
      p.rTensor _ ((Coalgebra.comul (R := k) (A := C)).lTensor _ (δ x))
    rw [h₃, h₁, h₂, hδ]
    exact σ.coassoc (x i)
  · intro x
    funext i
    let p : (S → V) →ₗ[k] V := LinearMap.proj i
    let ε := Coalgebra.counit (R := k) (A := C)
    have h (t : (S → V) ⊗[k] C) :
        p (TensorProduct.rid k _ (ε.lTensor _ t)) =
          TensorProduct.rid k _ (ε.lTensor _ (p.rTensor C t)) := by
      induction t with
      | tmul v c => simp [p]
      | add t s ht hs => simp [ht, hs]
    change p (TensorProduct.rid k _ (ε.lTensor _ (δ x))) = x i
    rw [h, hδ]
    exact σ.counit (x i)

private theorem tupleComodule_proj (σ : RightComodule k C V) (x : S → V) (i : S) :
    (LinearMap.proj (R := k) i).rTensor C ((tupleComodule σ).coaction x) =
      σ.coaction (x i) := by
  rw [← tensor_proj]
  exact congrFun ((TensorProduct.piLeft k C (fun _ : S ↦ V)).apply_symm_apply _) i

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000
variable {k : Type u} [Field k] {A C : HopfAlgebraCategory k}
section Coefficients

variable {S : Type u} [Fintype S] [DecidableEq S]

private def weightedSum (f : S → A) : (S → A) →ₗ[k] A :=
  ∑ i, (LinearMap.mul k A (f i)).comp (LinearMap.proj i)

omit [DecidableEq S] in
private theorem weightedSum_apply (f v : S → A) :
    weightedSum (k := k) f v = ∑ i, v i * f i := by
  simp [weightedSum, mul_comm]

omit [DecidableEq S] in
private theorem weightedSum_tensor (f : S → A) (t : (S → A) ⊗[k] C) :
    (weightedSum f).rTensor C t =
      ∑ i, (LinearMap.mul k A (f i)).rTensor C
        ((LinearMap.proj (R := k) i).rTensor C t) := by
  induction t with
  | tmul v c => simp [weightedSum_apply, TensorProduct.sum_tmul, mul_comm]
  | add t s ht hs => simp [ht, hs, Finset.sum_add_distrib]

private theorem weightedSum_coaction (φ : A ⟶ C) (f : S → A)
    (hf : ∀ i, translation φ (f i) = f i ⊗ₜ[k] (1 : C)) (v : S → A) :
    (weightedSum f).rTensor C ((tupleComodule (translationComodule φ)).coaction v) =
      translation φ (weightedSum f v) := by
  rw [weightedSum_tensor, weightedSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tupleComodule_proj]
  change (LinearMap.mul k A (f i)).rTensor C (translation φ (v i)) =
    translation φ (v i * f i)
  rw [map_mul, hf]
  generalize translation φ (v i) = z
  induction z with
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add t s ht hs => simp [ht, hs, add_mul]

private theorem translation_scalar (φ : A ⟶ C) (x : k) :
    translation φ (algebraMap k A x) = algebraMap k A x ⊗ₜ[k] (1 : C) :=
  (translation φ).commutes x

private def constantProjection (A : HopfAlgebraCategory k) : A →ₗ[k] A :=
  (Algebra.ofId k A).toLinearMap.comp (Coalgebra.counit (R := k))

private theorem constantProjection_apply (v : A) :
    constantProjection A v = algebraMap k A (Coalgebra.counit v) := rfl

private theorem constantProjection_scalar (x : k) :
    constantProjection A (algebraMap k A x) = algebraMap k A x := by
  rw [constantProjection_apply, Bialgebra.counit_algebraMap]

/-- The tuples mapping to the constant line under the weighted sum form a
subcomodule. A finite subcomodule containing a tuple over `1` still surjects
onto that line. -/
private theorem finite_coefficient_module (φ : A ⟶ C)
    (f : S → A) (hf : ∀ i, translation φ (f i) = f i ⊗ₜ[k] (1 : C))
    (v : S → A) (hv : ∑ i, v i * f i = 1) :
    ∃ (U : Type u) (_ : AddCommGroup U) (_ : Module k U) (_ : FiniteDimensional k U)
      (τ : RightComodule k C U) (i : U →ₗ[k] (S → A)) (q : U →ₗ[k] k),
      Function.Surjective q ∧
      (∀ x s, translation φ (i x s) = (LinearMap.proj (R := k) s).rTensor C
        (i.rTensor C (τ.coaction x))) ∧
      (∀ x, ∑ s, i x s * f s = algebraMap k A (q x)) ∧
      ∀ x, q.rTensor C (τ.coaction x) = q x ⊗ₜ[k] (1 : C) := by
  classical
  let F := weightedSum (k := k) f
  let δ : RightComodule k C (S → A) := tupleComodule (translationComodule φ)
  let D := F - (constantProjection A).comp F
  let L := LinearMap.ker D
  have hv₁ : F v = 1 := (weightedSum_apply f v).trans hv
  have hvL : v ∈ L := by
    change F v - constantProjection A (F v) = 0
    rw [hv₁, ← map_one (algebraMap k A), constantProjection_scalar, sub_self]
  have hL (w : L) : F w.val = algebraMap k A (Coalgebra.counit (F w.val)) :=
    sub_eq_zero.mp w.property
  have hstable : δ.IsSubcomodule L := by
    intro w
    apply (Module.Flat.rTensor_exact C D.exact_subtype_ker_map (δ.coaction w.val)).mp
    change (F - (constantProjection A).comp F).rTensor C (δ.coaction w.val) = 0
    rw [LinearMap.rTensor_sub, LinearMap.sub_apply, LinearMap.rTensor_comp_apply,
      weightedSum_coaction φ f hf, hL w, translation_scalar, LinearMap.rTensor_tmul,
      constantProjection_scalar, sub_self]
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction δ L).mp hstable
  let w : L := ⟨v, hvL⟩
  obtain ⟨W, hW⟩ := σ.exists_finiteSubcomodule w
  let U := W.val
  haveI : FiniteDimensional k U := W.property.2
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction σ U).mp W.property.1
  let i : U →ₗ[k] (S → A) := L.subtype.comp U.subtype
  have hi (x : U) : i.rTensor C (τ.coaction x) = δ.coaction (i x) := by
    rw [LinearMap.rTensor_comp_apply, show U.subtype.rTensor C (τ.coaction x) =
        σ.coaction (U.subtype x) from DFunLike.congr_fun hτ x,
      show L.subtype.rTensor C (σ.coaction (U.subtype x)) =
        δ.coaction (L.subtype (U.subtype x)) from DFunLike.congr_fun hσ (U.subtype x)]
    rfl
  let q₀ : U →ₗ[k] k := Coalgebra.counit ∘ₗ F ∘ₗ i
  have hF (x : U) : F (i x) = algebraMap k A (q₀ x) := hL x.val
  have hq₁ : q₀ (⟨w, hW⟩ : U) = 1 := by
    change Coalgebra.counit (F v) = 1
    rw [hv₁, Bialgebra.counit_one]
  have hq' (x : U) : q₀.rTensor C (τ.coaction x) = q₀ x ⊗ₜ[k] (1 : C) := by
    change (Coalgebra.counit ∘ₗ F ∘ₗ i).rTensor C (τ.coaction x) = _
    rw [LinearMap.rTensor_comp_apply, LinearMap.rTensor_comp_apply, hi,
      weightedSum_coaction φ f hf, hF x, translation_scalar, LinearMap.rTensor_tmul,
      Bialgebra.counit_algebraMap]
  refine ⟨U, inferInstance, inferInstance, inferInstance, τ, i, q₀, ?_, ?_, ?_, hq'⟩
  · intro x
    exact ⟨x • (⟨w, hW⟩ : U), by rw [map_smul, hq₁, smul_eq_mul, mul_one]⟩
  · intro x s
    rw [hi, tupleComodule_proj]
    rfl
  · intro x
    rw [← weightedSum_apply]
    exact hF x

private theorem basisColumn {U J : Type u} [AddCommGroup U] [Module k U] [Fintype J]
    [DecidableEq J] (b : Module.Basis J k U) (j : J) :
    b.equivFun.symm (Pi.single j 1) = b j := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext l
  simp only [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]

omit [Fintype S] [DecidableEq S] in
private theorem trivialQuotient_of_coaction
    {U J : Type u} [AddCommGroup U] [Module k U] [Fintype J] [DecidableEq J]
    (H : Specs.AffineAlgebraicGroup k)
    (e : convolutionPoints C ≅ (groupPointsFunctor k).obj H.val)
    (τ : RightComodule k C U) (b : Module.Basis J k U) (q₀ : U →ₗ[k] k)
    (hq : Function.Surjective q₀)
    (hq' : ∀ x, q₀.rTensor C (τ.coaction x) = q₀ x ⊗ₜ[k] (1 : C)) :
    IsTrivialQuotient (e.inv ≫ matrixPointHom C (coefficients C b τ)
      (coefficients_isCoactionMatrix C b τ)) (q₀.comp b.equivFun.symm.toLinearMap) := by
  let M := coefficients C b τ
  let ρ : Representation H.val J := e.inv ≫ matrixPointHom C M (coefficients_isCoactionMatrix C b τ)
  let q := q₀.comp b.equivFun.symm.toLinearMap
  have hqb (j : J) : q (Pi.single j 1) = q₀ (b j) := by
    change q₀ (b.equivFun.symm (Pi.single j 1)) = _
    rw [basisColumn]
  have hrow₀ (j : J) :
      ∑ l, algebraMap k C (q₀ (b l)) * M l j = algebraMap k C (q₀ (b j)) := by
    have h := hq' (b j)
    rw [coaction_apply_basis C b τ, map_sum] at h
    have hr := congrArg (TensorProduct.lid k C) h
    simpa only [LinearMap.rTensor_tmul, map_sum, TensorProduct.lid_tmul, Algebra.smul_def,
      mul_one, M] using hr
  have hmatrix (R : TestAlgebra k) (g : GroupPoints H.val R) (l j : J) :
      (ρ.app R g).val l j = (e.inv.app R g).ofConv (M l j) := rfl
  have hrow (R : TestAlgebra k) (g : GroupPoints H.val R) (j : J) :
      ∑ l, algebraMap k R (q (Pi.single l 1)) * (ρ.app R g).val l j =
        algebraMap k R (q (Pi.single j 1)) := by
    simp only [hqb, hmatrix]
    simpa only [map_sum, map_mul, AlgHom.commutes] using
      congrArg (fun z : C ↦ (e.inv.app R g).ofConv z) (hrow₀ j)
  change IsTrivialQuotient ρ q
  refine ⟨hq.comp b.equivFun.symm.surjective, ?_⟩
  intro R g x
  simp only [act, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hrow]

private theorem translation_coefficients (φ : A ⟶ C)
    (H : Specs.AffineAlgebraicGroup k)
    (e : convolutionPoints C ≅ (groupPointsFunctor k).obj H.val)
    (f : S → A) (hf : ∀ i, translation φ (f i) = f i ⊗ₜ[k] (1 : C))
    (v : S → A) (hv : ∑ i, v i * f i = 1) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
      (ρ : Representation H.val J) (q : (J → k) →ₗ[k] k)
      (c : J → S → A) (M : Matrix J J C), IsTrivialQuotient ρ q ∧
        (∀ (R : TestAlgebra k) (r : C →ₐ[k] R) l j,
          (ρ.app R (e.hom.app R (toConv r))).val l j = r (M l j)) ∧
        (∀ j s, translation φ (c j s) = ∑ l, c l s ⊗ₜ[k] M l j) ∧
        (∀ j, ∑ i, c j i * f i = algebraMap k A (q (Pi.single j 1))) := by
  classical
  obtain ⟨U, _, _, _, τ, i, q₀, hq, hi, hF, hq'⟩ := finite_coefficient_module φ f hf v hv
  let J := ULift.{u} (Fin (Module.finrank k U))
  letI : Module.Free k U := Module.Free.of_divisionRing k U
  let b : Module.Basis J k U := (Module.finBasis k U).reindex Equiv.ulift.symm
  let M := coefficients C b τ
  let ρ : Representation H.val J :=
    e.inv ≫ matrixPointHom C M (coefficients_isCoactionMatrix C b τ)
  let q := q₀.comp b.equivFun.symm.toLinearMap
  let c (j : J) := i (b j)
  refine ⟨J, inferInstance, inferInstance, ρ, q, c, M,
    trivialQuotient_of_coaction H e τ b q₀ hq hq', ?_, ?_, ?_⟩
  · intro R r l j
    have hr : e.inv.app R (e.hom.app R (toConv r)) = toConv r :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (e.app R).hom_inv_id) (toConv r)
    change (e.inv.app R (e.hom.app R (toConv r))).ofConv (M l j) = _
    rw [hr]
  · intro j s
    rw [hi (b j) s, coaction_apply_basis C b τ, map_sum, map_sum]
    simp only [LinearMap.rTensor_tmul]
    rfl
  · intro j
    change (∑ i', i (b j) i' * f i') = algebraMap k A (q₀ (b.equivFun.symm (Pi.single j 1)))
    rw [basisColumn, hF]

end Coefficients
end

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable {k : Type u} [Field k]

private def specSectionsIso :
    𝟭 _ ≅ testSpec k ⋙ algΓ (CommRingCat.of k) := by
  let : (algSpec (CommRingCat.of k)).Full := algSpec.instFull
  let : (algSpec (CommRingCat.of k)).Faithful := algSpec.instFaithful
  exact (asIso (algΓAlgSpecAdjunction (CommRingCat.of k)).counit).symm

private def specSections (R : TestAlgebra k) :
    globalSections ((testSpec k).obj (op R)) →ₐ[k] R :=
  ((specSectionsIso (k := k)).hom.app (op R)).unop.hom

private def evaluateSections {X : SchemeOver k} {R : TestAlgebra k} (t : Points X R) :
    globalSections X →ₐ[k] R :=
  (specSections R).comp (pullSections t)

private theorem pullSections_comp {X Y Z : SchemeOver k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullSections (f ≫ g) = (pullSections f).comp (pullSections g) := by
  change (((algΓ _).map (f ≫ g)).unop).hom = _
  rw [Functor.map_comp]
  rfl

private theorem evaluateSections_comp {X Y : SchemeOver k} {R : TestAlgebra k}
    (t : Points X R) (f : X ⟶ Y) (s : globalSections Y) :
    evaluateSections (t ≫ f) s = evaluateSections t (pullSections f s) := by
  simp only [evaluateSections, pullSections_comp, AlgHom.comp_apply]

private theorem evaluateSections_natural {X : SchemeOver k} {R T : TestAlgebra k}
    (f : R ⟶ T) (t : Points X R) (s : globalSections X) :
    evaluateSections (mapPoints f t) s = f.hom (evaluateSections t s) := by
  change evaluateSections ((testSpec k).map f.op ≫ t) s = _
  rw [evaluateSections_comp]
  have h := (specSectionsIso (k := k)).hom.naturality f.op
  exact congrArg (fun z ↦ z.unop.hom (pullSections t s)) h.symm

private theorem evaluateSections_bijective {X : SchemeOver k} {R : TestAlgebra k}
    (t : Points X R) [IsIso t] : Function.Bijective (evaluateSections t) := by
  have h : IsIso (((algΓ (CommRingCat.of k)).map t).unop) := inferInstance
  have h₁ := ConcreteCategory.bijective_of_isIso ((specSectionsIso (k := k)).hom.app (op R)).unop
  have h₂ := ConcreteCategory.bijective_of_isIso (((algΓ (CommRingCat.of k)).map t).unop)
  exact h₁.comp h₂

private theorem sections_eq_of_eval {X : SchemeOver k} [IsAffine X.left]
    {s t : globalSections X}
    (h : ∀ (R : TestAlgebra k) (x : Points X R),
      evaluateSections x s = evaluateSections x t) : s = t := by
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  exact (evaluateSections_bijective e.hom).1 (h R.unop e.hom)

private theorem finiteType_globalSections (X : SchemeOver k) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : Algebra.FiniteType k (globalSections X) := by
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  have h := locallyOfFiniteType_comp e.hom.left X.hom
  rw [Over.w e.hom] at h
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k (R.unop : Type u)))) at h
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have := RingHom.finiteType_algebraMap.mp h
  let i := AlgEquiv.ofBijective (evaluateSections e.hom) (evaluateSections_bijective e.hom)
  exact .of_surjective i.symm.toAlgHom i.symm.surjective

section GroupCoordinates

variable {A C : HopfAlgebraCategory k} {G H : Specs.GroupScheme k}

private def groupCoordinateIso (e : specGroup A ≅ G) :
    convolutionPoints A ≅ (groupPointsFunctor k).obj G :=
  hopfSpecPointIso A ≪≫ (groupPointsFunctor k).mapIso e

private abbrev universalGroupPoint (e : specGroup A ≅ G) :
    Points G.X (CommAlgCat.of k A) := e.hom.hom.hom

private abbrev coordinatePoint (e : specGroup A ≅ G) (R : TestAlgebra k)
    (g : WithConv (A →ₐ[k] R)) : Points G.X R :=
  (groupCoordinateIso e).hom.app R g

private theorem coordinatePoint_mul (e : specGroup A ≅ G) (R : TestAlgebra k)
    (g h : WithConv (A →ₐ[k] R)) :
    coordinatePoint e R (g * h) = coordinatePoint e R g * coordinatePoint e R h :=
  map_mul ((groupCoordinateIso e).hom.app R).hom g h

private theorem groupCoordinateIso_apply (e : specGroup A ≅ G) (R : TestAlgebra k)
    (g : A →ₐ[k] R) :
    (groupCoordinateIso e).hom.app R (toConv g) =
      mapPoints (CommAlgCat.ofHom g) (universalGroupPoint e) := rfl

private theorem groupCoordinateIso_inclusion (e : specGroup A ≅ G) (d : specGroup C ≅ H)
    (i : H ⟶ G) (φ : A ⟶ C) (hφ : d.hom ≫ i = specGroupMap φ ≫ e.hom)
    (R : TestAlgebra k) (h : C →ₐ[k] R) :
    ((groupCoordinateIso d).hom.app R (toConv h) : Points H.X R) ≫ i.hom.hom =
      (groupCoordinateIso e).hom.app R (toConv (h.comp φ.hom.toAlgHom)) := by
  have ht := congrArg (fun z : specGroup C ⟶ G ↦ z.hom.hom) hφ
  change d.hom.hom.hom ≫ i.hom.hom = (specGroupMap φ).hom.hom ≫ e.hom.hom.hom at ht
  rw [groupCoordinateIso_apply, groupCoordinateIso_apply]
  change ((testSpec k).map (CommAlgCat.ofHom h).op ≫ d.hom.hom.hom) ≫ i.hom.hom = _
  rw [Category.assoc, ht, ← Category.assoc]
  change ((testSpec k).map (CommAlgCat.ofHom h).op ≫
      (testSpec k).map (CommAlgCat.ofHom φ.hom.toAlgHom).op) ≫ e.hom.hom.hom = _
  rw [← (testSpec k).map_comp]
  rfl

private theorem groupCoordinateIso_eval (e : specGroup A ≅ G) (R : TestAlgebra k)
    (g : A →ₐ[k] R) (s : globalSections G.X) :
    evaluateSections (X := G.X) ((groupCoordinateIso e).hom.app R (toConv g)) s =
      g (evaluateSections (universalGroupPoint e) s) := by
  rw [groupCoordinateIso_apply, evaluateSections_natural]
  rfl

private theorem exists_subgroupCoordinates (P : Specs.AffineAlgebraicGroup k)
    (H : Specs.ClosedSubgroup P.val) :
    ∃ (A C : HopfAlgebraCategory k) (e : specGroup A ≅ P.val)
      (d : specGroup C ≅ H.group) (φ : A ⟶ C), d.hom ≫ H.inclusion = specGroupMap φ ≫ e.hom := by
  obtain ⟨A, ⟨e⟩⟩ := essImage_hopfSpec.mpr P.property.1
  obtain ⟨C, ⟨d⟩⟩ :=
    essImage_hopfSpec.mpr (Specs.Unipotent.closedSubgroupAlgebraicGroup H).property.1
  obtain ⟨φ, hφ⟩ := (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_surjective
    (d.hom ≫ H.inclusion ≫ e.inv)
  refine ⟨A.unop, C.unop, e, d, φ.unop, ?_⟩
  change d.hom ≫ H.inclusion = (hopfSpec (CommRingCat.of k)).map φ ≫ e.hom
  rw [hφ]
  simp

end GroupCoordinates

section QuotientSections

variable {P : Specs.AffineAlgebraicGroup k} {H : Specs.ClosedSubgroup P.val}

open private comp_rightMultiplication from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.HomogeneousQuotient

private theorem quotientSections_descent (Q : Presentation H) (s : globalSections P.val.X) :
    (∀ (R : TestAlgebra k) (g : Points P.val.X R) (h : Points H.group.X R),
      evaluateSections (g * (h ≫ H.inclusion.hom.hom)) s = evaluateSections g s) ↔
      ∃ w : globalSections Q.scheme, pullSections Q.projection w = s := by
  let a : P.val.X ⨯ H.group.X ⟶ P.val.X := prod.fst
  let b : P.val.X ⨯ H.group.X ⟶ P.val.X := rightMultiplication H
  haveI := Q.flat
  haveI := Q.surjective
  haveI := Q.finitePresentation
  have hp : IsPullback a b Q.projection Q.projection := HomogeneousQuotient.quotientPullback Q
  constructor
  · intro hs
    apply (sections_descent Q.projection a b hp).2 s
    haveI : IsAffine P.val.X.left := P.property.1
    haveI : IsAffine H.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup H).property.1
    haveI : IsAffine (P.val.X ⨯ H.group.X).left :=
      IsAffine.of_isIso (Over.prodLeftIsoPullback P.val.X H.group.X).hom
    apply sections_eq_of_eval
    intro R x
    have hx : x = prod.lift (x ≫ prod.fst) (x ≫ prod.snd) := by
      apply prod.hom_ext <;> simp
    have hb : x ≫ b = (x ≫ prod.fst) * ((x ≫ prod.snd) ≫ H.inclusion.hom.hom) :=
      (congrArg (· ≫ b) hx).trans (comp_rightMultiplication _ _)
    rw [← evaluateSections_comp, ← evaluateSections_comp, hb]
    exact (hs R (x ≫ prod.fst) (x ≫ prod.snd)).symm
  · rintro ⟨w, rfl⟩ R g h
    have he := congrArg (fun z ↦ prod.lift g h ≫ z) hp.w
    change prod.lift g h ≫ a ≫ Q.projection = prod.lift g h ≫ b ≫ Q.projection at he
    rw [← Category.assoc, ← Category.assoc, show prod.lift g h ≫ a = g from prod.lift_fst _ _,
      show prod.lift g h ≫ b = g * (h ≫ H.inclusion.hom.hom) from comp_rightMultiplication g h] at he
    rw [← evaluateSections_comp, ← evaluateSections_comp, he]

private theorem quotientSections_injective (Q : Presentation H) :
    Function.Injective (pullSections Q.projection) := by
  haveI := Q.flat
  haveI := Q.surjective
  haveI := Q.finitePresentation
  exact (sections_descent _ _ _ (HomogeneousQuotient.quotientPullback Q)).1

end QuotientSections

end

section Affineness

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open private rightInvariant_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.NormalAffineQuotient

variable {k : Type u} [Field k] {P : Specs.AffineAlgebraicGroup k}
  {H : Specs.ClosedSubgroup P.val} {A C : HopfAlgebraCategory k}

private theorem rightInvariant_quotient (Q : Presentation H)
    (e : specGroup A ≅ P.val) (d : specGroup C ≅ H.group)
    (φ : A ⟶ C) (hφ : d.hom ≫ H.inclusion = specGroupMap φ ≫ e.hom)
    (s : globalSections P.val.X) :
    translation φ (evaluateSections (universalGroupPoint e) s) =
      (evaluateSections (universalGroupPoint e) s) ⊗ₜ[k] (1 : C) ↔
        ∃ w : globalSections Q.scheme, pullSections Q.projection w = s := by
  rw [translation_apply, rightInvariant_iff, ← quotientSections_descent]
  have hm (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : C →ₐ[k] R) :
      (g * toConv (h.comp φ.hom.toAlgHom)) (evaluateSections (universalGroupPoint e) s) =
        evaluateSections (coordinatePoint e R g *
          (coordinatePoint d R (toConv h) ≫ H.inclusion.hom.hom)) s := by
    rw [show coordinatePoint d R (toConv h) ≫ H.inclusion.hom.hom =
      coordinatePoint e R (toConv (h.comp φ.hom.toAlgHom)) from
      groupCoordinateIso_inclusion e d H.inclusion φ hφ R h, ← coordinatePoint_mul]
    exact (groupCoordinateIso_eval e R (g * toConv (h.comp φ.hom.toAlgHom)).ofConv s).symm
  constructor
  · intro h R g sH
    obtain ⟨g₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((groupCoordinateIso e).hom.app R)).2 g
    obtain ⟨h₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((groupCoordinateIso d).hom.app R)).2 sH
    change evaluateSections (coordinatePoint e R g₀ *
      (coordinatePoint d R h₀ ≫ H.inclusion.hom.hom)) s = evaluateSections (coordinatePoint e R g₀) s
    exact (hm R g₀ h₀.ofConv).symm.trans
      ((h R g₀ h₀.ofConv).trans (groupCoordinateIso_eval e R g₀.ofConv s).symm)
  · intro h R g sH
    exact (hm R g sH).trans
      ((h R (coordinatePoint e R g) (coordinatePoint d R (toConv sH))).trans
        (groupCoordinateIso_eval e R g.ofConv s))

private theorem affine_of_invariant_lifting (p : ℕ) [Fact p.Prime] [CharP k p]
    (hH : IsSemisimple (Specs.Unipotent.closedSubgroupAlgebraicGroup H))
    (Q : Presentation H) [Q.scheme.left.IsQuasiAffine]
    (e : specGroup A ≅ P.val) (d : specGroup C ≅ H.group)
    (φ : A ⟶ C) (hφ : d.hom ≫ H.inclusion = specGroupMap φ ≫ e.hom) :
    IsAffine Q.scheme.left := by
  classical
  letI : IsAffine P.val.X.left := P.property.1
  obtain ⟨S, _, f, hf, hfspan⟩ := exists_basicOpen_cover Q.projection
  let u := universalGroupPoint e
  haveI : IsIso u := (Grp.forget _).map_isIso e.hom
  let E := (evaluateSections u).comp (pullSections Q.projection)
  have hE : Function.Injective E :=
    (evaluateSections_bijective u).1.comp (quotientSections_injective Q)
  let a : A →ₐ[k] A ⊗[k] C := Algebra.TensorProduct.includeLeft
  let b := translation φ
  have hdesc (z : A) (hz : a z = b z) : ∃ w, E w = z := by
    obtain ⟨s, hs⟩ := (evaluateSections_bijective u).2 z
    have h : translation φ (evaluateSections u s) =
        (evaluateSections u s) ⊗ₜ[k] (1 : C) := by
      rw [hs]
      exact hz.symm
    obtain ⟨w, hw⟩ := (rightInvariant_quotient Q e d φ hφ s).mp h
    exact ⟨w, congrArg (evaluateSections u) hw |>.trans hs⟩
  have hfinv (i : S) : translation φ (E (f i)) = E (f i) ⊗ₜ[k] (1 : C) :=
    (rightInvariant_quotient Q e d φ hφ _).mpr ⟨f i, rfl⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp hfspan)
  have hv' : ∑ i, (evaluateSections u) (v i) * E (f i) = 1 := by
    simpa only [map_sum, map_mul, map_one, Function.comp_apply, E, AlgHom.comp_apply] using
      congrArg (evaluateSections u) hv
  let H₀ := Specs.Unipotent.closedSubgroupAlgebraicGroup H
  let T := CommAlgCat.of k (A ⊗[k] C)
  let r : C →ₐ[k] T := Algebra.TensorProduct.includeRight
  let g : GroupPoints H.group T := (groupCoordinateIso d).hom.app T (toConv r)
  obtain ⟨J, _, _, ρ, q, c, M, hq, hmat, hc, hqc⟩ :=
    translation_coefficients φ H₀ (groupCoordinateIso d) (E ∘ f) hfinv _ hv'
  apply affine_of_basicOpen_cover f hf
  refine span_eq_top_of_invariant_lifting p H₀ hH ρ q hq E hE T a b g hdesc f c ?_ hqc
  intro j i
  change (∑ l, (ρ.app T ((groupCoordinateIso d).hom.app T (toConv r))).val l j * a (c l i)) =
    translation φ (c j i)
  rw [hc j i]
  apply Finset.sum_congr rfl
  intro l _
  calc
    _ = r (M l j) * a (c l i) := congrArg (fun z : T ↦ z * a (c l i)) (hmat T r l j)
    _ = c l i ⊗ₜ[k] M l j := by
      change ((1 : A) ⊗ₜ[k] M l j) * (c l i ⊗ₜ[k] (1 : C)) = c l i ⊗ₜ[k] M l j
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

end
end Affineness

section Embedding

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open Specs.ClosedHomogeneousOrbits (vectorSpace vectorPoint)
open private dualPoints inverseTranspose from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.RationalRepresentations
open private isPullback_tensor_snd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

variable {k : Type u} [Field k] {P : Specs.AffineAlgebraicGroup k}
  {H : Specs.ClosedSubgroup P.val} {A C : HopfAlgebraCategory k}

local instance (A : HopfAlgebraCategory k) (R : TestAlgebra k) :
    Group (WithConv (A →ₐ[k] R)) := convolutionGroup A R

private theorem coordinatePoint_inv (e : specGroup A ≅ P.val) (R : TestAlgebra k)
    (g : WithConv (A →ₐ[k] R)) : coordinatePoint e R g⁻¹ = (coordinatePoint e R g)⁻¹ :=
  map_inv ((groupCoordinateIso e).hom.app R).hom g

private abbrev inverseQuotientProjection (Q : Presentation H) :
    P.val.X ⟶ Q.scheme := ι[P.val.X] ≫ Q.projection

private theorem inverse_quotientSections_descent (Q : Presentation H)
    (s : globalSections P.val.X) :
    (∀ (R : TestAlgebra k) (g : Points P.val.X R) (h : Points H.group.X R),
      evaluateSections ((h ≫ H.inclusion.hom.hom) * g) s = evaluateSections g s) ↔
      ∃ w : globalSections Q.scheme, pullSections (inverseQuotientProjection Q) w = s := by
  let i := H.inclusion.hom.hom
  let inv := ι[P.val.X]
  have hinv (r : globalSections P.val.X) : pullSections inv (pullSections inv r) = r := by
    rw [← AlgHom.comp_apply, ← pullSections_comp, GrpObj.inv_comp_inv]
    change (((algΓ _).map (𝟙 P.val.X)).unop).hom r = r
    rw [show (algΓ (CommRingCat.of k)).map (𝟙 P.val.X) = 𝟙 _ from (algΓ (CommRingCat.of k)).map_id _]
    rfl
  have he (R : TestAlgebra k) (g : Points P.val.X R) :
      evaluateSections g (pullSections inv s) = evaluateSections g⁻¹ s :=
    (evaluateSections_comp g inv s).symm
  constructor
  · intro h
    have hright (R : TestAlgebra k) (g : Points P.val.X R) (z : Points H.group.X R) :
        evaluateSections (g * (z ≫ i)) (pullSections inv s) =
          evaluateSections g (pullSections inv s) := by
      rw [he, he, mul_inv_rev, ← GrpObj.inv_comp]
      exact h R g⁻¹ z⁻¹
    obtain ⟨w, hw⟩ := (quotientSections_descent Q (pullSections inv s)).mp hright
    refine ⟨w, ?_⟩
    change pullSections (inv ≫ Q.projection) w = s
    rw [pullSections_comp, AlgHom.comp_apply, hw, hinv]
  · rintro ⟨w, hw⟩
    have hright := (quotientSections_descent Q (pullSections inv s)).mpr ⟨w, by
      change pullSections (inv ≫ Q.projection) w = s at hw
      rw [pullSections_comp, AlgHom.comp_apply] at hw
      rw [← hw, hinv]⟩
    intro R g z
    have h := hright R g⁻¹ z⁻¹
    rwa [he, he, mul_inv_rev, ← GrpObj.inv_comp, inv_inv, inv_inv] at h

/-- Composing the quotient projection with inversion identifies its functions
with the functions on the group invariant under left multiplication. -/
private theorem inverseQuotient_invariants (Q : Presentation H)
    (e : specGroup A ≅ P.val) (d : specGroup C ≅ H.group)
    (φ : A ⟶ C) (hφ : d.hom ≫ H.inclusion = specGroupMap φ ≫ e.hom)
    (s : globalSections P.val.X) :
    evaluateSections (universalGroupPoint e) s ∈ leftInvariantFunctions φ ↔
      ∃ w : globalSections Q.scheme, pullSections (inverseQuotientProjection Q) w = s := by
  rw [leftInvariantFunctions_iff, ← inverse_quotientSections_descent]
  have he (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (h : C →ₐ[k] R) :
      (toConv (h.comp φ.hom.toAlgHom) * g) (evaluateSections (universalGroupPoint e) s) =
        evaluateSections
          ((coordinatePoint d R (toConv h) ≫ H.inclusion.hom.hom) * coordinatePoint e R g) s := by
    rw [show coordinatePoint d R (toConv h) ≫ H.inclusion.hom.hom =
      coordinatePoint e R (toConv (h.comp φ.hom.toAlgHom)) from
      groupCoordinateIso_inclusion e d H.inclusion φ hφ R h, ← coordinatePoint_mul]
    exact (groupCoordinateIso_eval e R (toConv (h.comp φ.hom.toAlgHom) * g).ofConv s).symm
  constructor
  · intro h R g z
    obtain ⟨g₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((groupCoordinateIso e).hom.app R)).2 g
    obtain ⟨z₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      ((groupCoordinateIso d).hom.app R)).2 z
    change evaluateSections ((coordinatePoint d R z₀ ≫ H.inclusion.hom.hom) *
      coordinatePoint e R g₀) s = evaluateSections (coordinatePoint e R g₀) s
    exact (he R g₀ z₀.ofConv).symm.trans
      ((h R g₀ z₀.ofConv).trans (groupCoordinateIso_eval e R g₀.ofConv s).symm)
  · intro h R g z
    exact (he R g z).trans
      ((h R (coordinatePoint e R g) (coordinatePoint d R (toConv z))).trans
        (groupCoordinateIso_eval e R g.ofConv s))

private theorem exists_closed_coordinateMap {X : SchemeOver k} [IsAffine X.left]
    {I : Type u} (f : I → globalSections X)
    (hf : Algebra.adjoin k (Set.range f) = ⊤) :
    ∃ j : X ⟶ vectorSpace k I, IsClosedImmersion j.left ∧
      ∀ (R : TestAlgebra k) (x : Points X R),
        x ≫ j = vectorPoint R (fun i ↦ evaluateSections x (f i)) := by
  have hnat {R T : TestAlgebra k} (l : R ⟶ T) (x : Points X R) :
      vectorPoint T (fun i ↦ evaluateSections (mapPoints l x) (f i)) =
        mapPoints l (vectorPoint R (fun i ↦ evaluateSections x (f i))) := by
    rw [map_vectorPoint]
    simp only [evaluateSections_natural]
  obtain ⟨j, hj⟩ := exists_affineHom_of_points
    (fun R x ↦ vectorPoint R (fun i ↦ evaluateSections x (f i))) hnat
  refine ⟨j, ?_, hj⟩
  obtain ⟨R, ⟨e⟩⟩ := essImage_algSpec.mpr (inferInstance : IsAffine X.left)
  let g := evaluateSections e.hom
  have hg : Function.Surjective g := (evaluateSections_bijective e.hom).2
  let p : MvPolynomial I k →ₐ[k] globalSections X := MvPolynomial.aeval f
  have hp : Function.Surjective p := by
    intro x
    change x ∈ p.range
    rw [← Algebra.adjoin_range_eq_range_aeval, hf]
    exact Algebra.mem_top
  have hgp : g.comp p = MvPolynomial.aeval (fun i ↦ g (f i)) :=
    MvPolynomial.comp_aeval f g
  have hc : IsClosedImmersion (e.hom ≫ j).left := by
    rw [hj]
    change IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := k) (fun i ↦ g (f i))).toRingHom))
    rw [← hgp]
    exact IsClosedImmersion.spec_of_surjective _ (hg.comp hp)
  haveI : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom.left j.left).mp hc

private theorem action_on_quotientProjection (Q : Presentation H)
    (b : ModObj P.val.X Q.scheme)
    (hb : μ[P.val.X] ≫ Q.projection = (𝟙 P.val.X ⊗ₘ Q.projection) ≫ b.smul)
    {T : SchemeOver k} (g h : T ⟶ P.val.X) :
    lift g (h ≫ Q.projection) ≫ b.smul = (g * h) ≫ Q.projection := by
  rw [Hom.mul_def, Category.assoc, hb, ← Category.assoc, lift_map, Category.comp_id]

private theorem equivariant_from_projection (Q : Presentation H)
    (b : ModObj P.val.X Q.scheme) {V : SchemeOver k} (a : ModObj P.val.X V)
    (j : Q.scheme ⟶ V)
    (h : ∀ (R : TestAlgebra k) (g r : Points P.val.X R),
      (lift g (r ≫ inverseQuotientProjection Q) ≫ b.smul) ≫ j =
        lift g ((r ≫ inverseQuotientProjection Q) ≫ j) ≫ a.smul) :
    b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul := by
  let ψ := inverseQuotientProjection Q
  letI : Flat Q.projection.left := Q.flat
  letI : Surjective Q.projection.left := Q.surjective
  letI : LocallyOfFinitePresentation Q.projection.left := Q.finitePresentation
  haveI : IsIso (ι[P.val.X]).left := (Over.forget _).map_isIso _
  haveI : Flat ψ.left := inferInstanceAs (Flat ((ι[P.val.X]).left ≫ Q.projection.left))
  haveI : Surjective ψ.left :=
    inferInstanceAs (Surjective ((ι[P.val.X]).left ≫ Q.projection.left))
  haveI : LocallyOfFinitePresentation ψ.left :=
    inferInstanceAs (LocallyOfFinitePresentation ((ι[P.val.X]).left ≫ Q.projection.left))
  let w := 𝟙 P.val.X ⊗ₘ ψ
  have hw := ((isPullback_tensor_snd (A := P.val.X) ψ).map (Over.forget _)).flip
  haveI : Flat w.left := MorphismProperty.of_isPullback (P := @Flat) hw (inferInstance : Flat ψ.left)
  haveI : Surjective w.left := MorphismProperty.of_isPullback (P := @Surjective) hw (inferInstance : Surjective ψ.left)
  haveI : LocallyOfFinitePresentation w.left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hw
      (inferInstance : LocallyOfFinitePresentation ψ.left)
  haveI : Epi w := Over.epi_of_epi_left w
  apply (cancel_epi w).mp
  letI : IsAffine P.val.X.left := P.property.1
  haveI : IsAffine (P.val.X ⊗ P.val.X).left :=
    inferInstanceAs (IsAffine (pullback P.val.X.hom P.val.X.hom))
  apply affineHom_ext
  intro R t
  let g := t ≫ fst _ _
  let r := t ≫ snd _ _
  have hl : t = lift g r := (lift_comp_fst_snd t).symm
  have ht : t ≫ w = lift g (r ≫ ψ) := by
    rw [hl]
    change lift g r ≫ (𝟙 P.val.X ⊗ₘ ψ) = _
    rw [lift_map, Category.comp_id]
  calc
    t ≫ w ≫ b.smul ≫ j = (lift g (r ≫ ψ) ≫ b.smul) ≫ j := by
      rw [← Category.assoc t w, ht, ← Category.assoc]
    _ = lift g ((r ≫ ψ) ≫ j) ≫ a.smul := h R g r
    _ = t ≫ w ≫ (𝟙 P.val.X ⊗ₘ j) ≫ a.smul := by
      rw [← Category.assoc t w, ht, ← Category.assoc (lift g (r ≫ ψ)), lift_map, Category.comp_id]

private theorem comodule_translation_eval {V J : Type u} [AddCommGroup V] [Module k V]
    [Fintype J] (τ : RightComodule k A V) (b : Module.Basis J k V) (i : V →ₗ[k] A)
    (hi : ∀ x, i.rTensor A (τ.coaction x) = Coalgebra.comul (i x))
    (R : TestAlgebra k) (r g : WithConv (A →ₐ[k] R)) (j : J) :
    (r * g) (i (b j)) = ∑ l, r (i (b l)) * g (coefficients A b τ l j) := by
  classical
  change (r * g).ofConv (i (b j)) = _
  rw [AlgHom.convMul_apply, ← hi, coaction_apply_basis A b τ]
  simp only [map_sum, LinearMap.rTensor_tmul, Algebra.TensorProduct.lift_tmul]

/-- Finite sets of left-invariant functions lie in finite subcomodules for
right translation. -/
private theorem exists_finite_invariant_comodule (φ : A ⟶ C) {S : Type u} [Finite S]
    (s : S → A) (hs : ∀ j, s j ∈ leftInvariantFunctions φ) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : FiniteDimensional k V)
      (τ : RightComodule k A V) (i : V →ₗ[k] A),
      (∀ v, i v ∈ leftInvariantFunctions φ) ∧
      (∀ v, i.rTensor A (τ.coaction v) = Coalgebra.comul (i v)) ∧
      ∀ j, ∃ v, i v = s j := by
  let U := leftInvariantFunctions φ
  let t (j : S) : U := ⟨s j, hs j⟩
  let reg := RightComodule.regular (k := k) (C := A)
  obtain ⟨σ, hσ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction reg U).mp
    (leftInvariantFunctions_isSubcomodule φ)
  obtain ⟨W, hW⟩ := σ.exists_finiteSubcomodule_containing_range t
  haveI : FiniteDimensional k W.val := W.property.2
  obtain ⟨τ, hτ⟩ := (RightComodule.isSubcomodule_iff_exists_coaction σ W.val).mp W.property.1
  let i := U.subtype.comp W.val.subtype
  have hi (x : W.val) : i.rTensor A (τ.coaction x) = Coalgebra.comul (i x) := by
    rw [LinearMap.rTensor_comp_apply, show W.val.subtype.rTensor A (τ.coaction x) =
        σ.coaction (W.val.subtype x) from DFunLike.congr_fun hτ x,
      show U.subtype.rTensor A (σ.coaction (W.val.subtype x)) =
        reg.coaction (U.subtype (W.val.subtype x)) from DFunLike.congr_fun hσ (W.val.subtype x)]
    rfl
  exact ⟨W.val, inferInstance, inferInstance, inferInstance, τ, i,
    fun v ↦ v.val.property, hi, fun j ↦ ⟨⟨t j, hW j⟩, rfl⟩⟩

/-- Descend a basis of a finite subcomodule containing algebra generators.
The descended functions still generate the quotient algebra. -/
private theorem exists_invariant_generators {B : Type u} [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] (φ : A ⟶ C) (E : B →ₐ[k] A) (hE : Function.Injective E)
    (hmem : ∀ x, E x ∈ leftInvariantFunctions φ)
    (hdesc : ∀ y ∈ leftInvariantFunctions φ, ∃ x, E x = y) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
      (f : J → B) (M : Matrix J J A), IsCoactionMatrix A M ∧
        Algebra.adjoin k (Set.range f) = ⊤ ∧
        ∀ (R : TestAlgebra k) (r g : WithConv (A →ₐ[k] R)) (j : J),
          (r * g) (E (f j)) = ∑ l, r (E (f l)) * g (M l j) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k B).out
  let t (x : s) := E x.val
  obtain ⟨V, _, _, _, τ, i, hi_mem, hi, hsV⟩ :=
    exists_finite_invariant_comodule φ t (fun x ↦ hmem x.val)
  letI : Module.Free k V := Module.Free.of_divisionRing k V
  let J := ULift.{u} (Fin (Module.finrank k V))
  let β : Module.Basis J k V := (Module.finBasis k V).reindex Equiv.ulift.symm
  have hex (j : J) : ∃ x : B, E x = i (β j) := hdesc _ (hi_mem (β j))
  choose f hf using hex
  have hgen : Algebra.adjoin k (Set.range f) = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hs]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨v, hv⟩ := hsV ⟨x, hx⟩
    have heq : x = ∑ j, (β.repr v j) • f j := by
      apply hE
      change E.toLinearMap x = E.toLinearMap (∑ j, (β.repr v j) • f j)
      rw [map_sum]
      simp only [map_smul, AlgHom.toLinearMap_apply, hf]
      rw [← show i v = E x from hv]
      simpa only [map_sum, map_smul] using congrArg i (β.sum_repr v).symm
    rw [heq]
    apply Subalgebra.sum_mem
    intro j _
    apply Subalgebra.smul_mem
    exact Algebra.subset_adjoin (Set.mem_range_self j)
  let M : Matrix J J A := coefficients A β τ
  have hM : IsCoactionMatrix A M := coefficients_isCoactionMatrix A β τ
  have htrans (R : TestAlgebra k) (r g : WithConv (A →ₐ[k] R)) (j : J) :
      (r * g) (E (f j)) = ∑ l, r (E (f l)) * g (M l j) := by
    simp only [hf]
    exact comodule_translation_eval τ β i hi R r g j
  exact ⟨J, (inferInstance : Fintype J), (inferInstance : DecidableEq J), f, M, hM, hgen, htrans⟩

private theorem exists_closed_quotientEmbedding (Q : Presentation H)
    [IsAffine Q.scheme.left] [LocallyOfFiniteType Q.scheme.hom]
    (b : ModObj P.val.X Q.scheme)
    (hb : μ[P.val.X] ≫ Q.projection = (𝟙 P.val.X ⊗ₘ Q.projection) ≫ b.smul)
    (e : specGroup A ≅ P.val) (d : specGroup C ≅ H.group)
    (φ : A ⟶ C) (hφ : d.hom ≫ H.inclusion = specGroupMap φ ≫ e.hom) :
    ∃ (J : Type u) (_ : Fintype J) (_ : DecidableEq J)
      (ρ : Representation P.val J) (a : ModObj P.val.X (vectorSpace k J))
      (j : Q.scheme ⟶ vectorSpace k J),
      IsClosedImmersion j.left ∧
      (∀ (R : TestAlgebra k) (g : Points P.val.X R) (v : J → R),
        lift g (vectorPoint R v) ≫ a.smul = vectorPoint R (act ρ R g v)) ∧
      b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul := by
  classical
  let B := globalSections Q.scheme
  let ψ := inverseQuotientProjection Q
  let u := universalGroupPoint e
  haveI : IsIso u := (Grp.forget _).map_isIso e.hom
  let E := (evaluateSections u).comp (pullSections ψ)
  have hinv : Function.Injective (pullSections ι[P.val.X]) :=
    (ConcreteCategory.bijective_of_isIso (((algΓ (CommRingCat.of k)).map ι[P.val.X]).unop)).1
  have hE : Function.Injective E := by
    change Function.Injective ((evaluateSections u).comp (pullSections (ι[P.val.X] ≫ Q.projection)))
    rw [pullSections_comp]
    exact (evaluateSections_bijective u).1.comp (hinv.comp (quotientSections_injective Q))
  have hmem (x : B) : E x ∈ leftInvariantFunctions φ :=
    (inverseQuotient_invariants Q e d φ hφ _).mpr ⟨x, rfl⟩
  have hdesc (z : A) (hz : z ∈ leftInvariantFunctions φ) : ∃ x : B, E x = z := by
    obtain ⟨y, hy⟩ := (evaluateSections_bijective u).2 z
    obtain ⟨x, hx⟩ := (inverseQuotient_invariants Q e d φ hφ y).mp (hy.symm ▸ hz)
    exact ⟨x, (congrArg (evaluateSections u) hx).trans hy⟩
  haveI : Algebra.FiniteType k B := finiteType_globalSections Q.scheme
  obtain ⟨J, _, _, f, M, hM, hgen, htrans⟩ := exists_invariant_generators φ E hE hmem hdesc
  obtain ⟨j, hj, heval⟩ := exists_closed_coordinateMap f hgen
  let α := matrixPointHom A M hM
  let ρ : Representation P.val J := (groupCoordinateIso e).inv ≫ α ≫ dualPoints
  haveI : IsAffine P.val.X.left := P.property.1
  obtain ⟨a, ha⟩ := exists_vectorAction ρ
  refine ⟨J, inferInstance, inferInstance, ρ, a, j, hj, ha, ?_⟩
  apply equivariant_from_projection Q b a j
  have hpoint (R : TestAlgebra k) (r : WithConv (A →ₐ[k] R)) (l : J) :
      evaluateSections (coordinatePoint e R r ≫ ψ) (f l) = r (E (f l)) := by
    rw [evaluateSections_comp, groupCoordinateIso_eval e R r.ofConv]
    rfl
  have hmatrix (R : TestAlgebra k) (g : WithConv (A →ₐ[k] R)) (l j : J) :
      (ρ.app R (coordinatePoint e R g)).val l j = g⁻¹ (M j l) := by
    let I := groupCoordinateIso e
    have hg : I.inv.app R (I.hom.app R g) = g :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (I.app R).hom_inv_id) g
    change ((α.app R (I.inv.app R (I.hom.app R g)))⁻¹).val j l = _
    rw [hg, ← map_inv]
    rfl
  intro R g r
  obtain ⟨g₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((groupCoordinateIso e).hom.app R)).2 g
  obtain ⟨r₀, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((groupCoordinateIso e).hom.app R)).2 r
  change (lift (coordinatePoint e R g₀) (coordinatePoint e R r₀ ≫ ψ) ≫ b.smul) ≫ j =
    lift (coordinatePoint e R g₀) ((coordinatePoint e R r₀ ≫ ψ) ≫ j) ≫ a.smul
  have hact : (lift (coordinatePoint e R g₀) (coordinatePoint e R r₀ ≫ ψ) ≫ b.smul) =
      coordinatePoint e R (r₀ * g₀⁻¹) ≫ ψ := by
    change (lift (coordinatePoint e R g₀) ((coordinatePoint e R r₀)⁻¹ ≫ Q.projection) ≫ b.smul) =
      (coordinatePoint e R (r₀ * g₀⁻¹))⁻¹ ≫ Q.projection
    rw [action_on_quotientProjection Q b hb, ← coordinatePoint_inv, ← coordinatePoint_inv,
      ← coordinatePoint_mul, mul_inv_rev, inv_inv]
  rw [hact, heval, heval, ha]
  congr 1
  funext l
  rw [hpoint, act, Matrix.mulVec, dotProduct]
  change (show WithConv (A →ₐ[k] R) from r₀ * g₀⁻¹).ofConv (E (f l)) = ∑ j,
    (ρ.app R (coordinatePoint e R g₀)).val l j * evaluateSections (coordinatePoint e R r₀ ≫ ψ) (f j)
  rw [htrans R r₀ g₀⁻¹ l]
  apply Finset.sum_congr rfl
  intro j _
  rw [hmatrix R g₀ l j, hpoint R r₀ j, mul_comm]

end
end Embedding

section ClosedOrbit

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Specs.ClosedHomogeneousOrbits (vectorSpace)
open private projection_eq_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.QuotientEmbedding
open private orbitMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Flag.SmoothOrbit

variable {k : Type u} [Field k] {P : Specs.AffineAlgebraicGroup k}
  {H : Specs.ClosedSubgroup P.val}

private theorem orbitMap_of_quotientEmbedding (Q : Presentation H)
    (b : ModObj P.val.X Q.scheme)
    (hb : μ[P.val.X] ≫ Q.projection = (𝟙 P.val.X ⊗ₘ Q.projection) ≫ b.smul)
    {V : SchemeOver k} (a : ModObj P.val.X V) (j : Q.scheme ⟶ V)
    (hj : b.smul ≫ j = (𝟙 P.val.X ⊗ₘ j) ≫ a.smul) :
    Q.projection ≫ j = Specs.SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) := by
  let g : P.val.X ⟶ P.val.X := 𝟙 _
  let h : P.val.X ⟶ P.val.X := 1
  symm
  calc
    Specs.SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j) =
        lift g ((h ≫ Q.projection) ≫ j) ≫ a.smul := by
      simp only [Specs.SmoothOrbit.orbitMap, g, h, Hom.one_def, Category.assoc]
    _ = (lift g (h ≫ Q.projection) ≫ (𝟙 P.val.X ⊗ₘ j)) ≫ a.smul := by
      rw [lift_map, Category.comp_id]
    _ = (lift g (h ≫ Q.projection) ≫ b.smul) ≫ j := by
      rw [Category.assoc, ← hj, ← Category.assoc]
    _ = Q.projection ≫ j := by
      rw [action_on_quotientProjection Q b hb, mul_one]
      rfl

private theorem stabilizer_of_quotientEmbedding (Q : Presentation H)
    {V : SchemeOver k} (a : ModObj P.val.X V) (j : Q.scheme ⟶ V)
    (hj : IsClosedImmersion j.left)
    (horb : Q.projection ≫ j =
      Specs.SmoothOrbit.orbitMap a (η[P.val.X] ≫ Q.projection ≫ j)) :
    RepresentsSubgroup H (fun _ g ↦ Stabilizes a.smul (η[P.val.X] ≫ Q.projection ≫ j) g) := by
  haveI : IsClosedImmersion j.left := hj
  haveI : Mono j := Over.mono_of_mono_left j
  intro T g
  let x := η[P.val.X] ≫ Q.projection ≫ j
  have e₁ : toUnit T ≫ x = ((1 : T ⟶ P.val.X) ≫ Q.projection) ≫ j := by
    simp only [x, Hom.one_def, Category.assoc]
  have e₂ : lift g (toUnit T ≫ x) ≫ a.smul = (g ≫ Q.projection) ≫ j := by
    calc
      _ = g ≫ Specs.SmoothOrbit.orbitMap a x := (orbitMap_comp a x g).symm
      _ = (g ≫ Q.projection) ≫ j := by rw [← horb, Category.assoc]
  change Stabilizes a.smul x g ↔ _
  rw [Stabilizes, e₂, e₁, cancel_mono, eq_comm]
  change ((1 : T ⟶ P.val.X) ≫ Q.projection = g ≫ Q.projection) ↔
    g ∈ Specs.SubgroupSections H T
  simpa only [inv_one, one_mul] using (projection_eq_iff Q (1 : T ⟶ P.val.X) g)

/-- The affine right quotient of a special linear group by a closed semisimple
subgroup admits an equivariant closed embedding into a finite-dimensional
rational representation. Its identity coset has the prescribed scheme stabilizer. -/
theorem closedHomogeneousOrbit : Specs.ClosedHomogeneousOrbits.ClosedHomogeneousOrbit.{u} := by
  intro k _ p _ _ m P eSL H hH
  have hs := specialLinear_smooth P eSL
  obtain ⟨Q, b, haff₀, hft, hb⟩ := exists_quasiAffine_quotient P H hs hH
  obtain ⟨A, C, e, d, φ, hφ⟩ := exists_subgroupCoordinates P H
  haveI : Q.scheme.left.IsQuasiAffine := haff₀
  haveI : LocallyOfFiniteType Q.scheme.hom := hft
  have haff := affine_of_invariant_lifting p hH Q e d φ hφ
  haveI : IsAffine Q.scheme.left := haff
  obtain ⟨I, _, _, ρ, a, j, hj, ha, hej⟩ := exists_closed_quotientEmbedding Q b hb e d φ hφ
  have horb := orbitMap_of_quotientEmbedding Q b hb a j hej
  have hstab := stabilizer_of_quotientEmbedding Q a j hj horb
  obtain ⟨ht, hq⟩ := (HomogeneousQuotient.homogeneousQuotient k P H).2 Q
  refine ⟨Q, I, inferInstance, inferInstance, ρ, a, b, j,
    haff, ht, hq hH.1, hj, ha, hej, horb, hstab, ?_⟩
  intro K _ _
  exact stabilizerSchemeBaseChange k K a.smul (η[P.val.X] ≫ Q.projection ≫ j) H hstab

end
end ClosedOrbit

end LinearAlgebraicGroups.Arithmetic.ClosedHomogeneousOrbits
