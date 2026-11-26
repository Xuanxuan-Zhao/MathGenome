import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.FieldDiagonalTor
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.ExteriorTensorExactness
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.PowerSeriesDiagonal
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CoefficientRings.CompleteRegularPowerSeries
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.RegularFiniteProjectiveDimension
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Depth.Type
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.CategoryTheory

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace CommutativeAlgebraNotes.Intersection.FieldDiagonalTor

open ExteriorTensorProduct (S Y includeX toY)
open PowerSeriesDiagonal
open scoped ExteriorTensorProduct PowerSeriesDiagonal
open IsolatedTorSupport.Specs (Tor)

universe u

variable (k : Type u) [Field k] (d : ℕ)

theorem diagonal_action : Spec.DiagonalAction := by
  intro k _ d M N i s x
  have h : s - includeX k d d (identify k d s) ∈ diagonalIdeal k d := by
    rw [← identifyKernel k d]
    change identify k d (s - includeX k d d (identify k d s)) = 0
    rw [map_sub, identify_includeX, sub_self]
  have h' : s - includeX k d d (identify k d s) ∈
      AdvCommAlg.Koszul.listIdeal (diagonalList k d) := by
    change _ ∈ Ideal.ofList (List.ofFn (difference k d))
    rwa [ofList_difference]
  have hzero := AdvCommAlg.Koszul.annihilates_homology (exteriorPair M N)
    (diagonalList k d) _ h' i x
  exact sub_eq_zero.mp (by simpa only [sub_smul] using hzero)

private theorem length_restrict_left (M N : ModuleCat.{u} (R k d)) (i : ℕ) :
    Module.length (S k d d) (koszulHomology k d M N i) =
      Module.length (R k d) ↥((restrictLeft k d).obj (koszulHomology k d M N i)) := by
  let H := koszulHomology k d M N i
  let : Module (R k d) H := ((restrictLeft k d).obj H).isModule
  let : IsScalarTower (S k d d) (R k d) H := IsScalarTower.mk fun s r x => by
    change includeX k d d (identify k d s * r) • x = s • (includeX k d d r • x)
    rw [diagonal_action k d M N i s, map_mul, mul_smul]
  exact Module.length_eq_of_surjective (identify_surjective k d)

private theorem exists_free_resolution (M : ModuleCat.{u} (R k d)) [Module.Finite (R k d) M] :
    ∃ P : ProjectiveResolution M,
      (∀ i, Module.Free (R k d) (P.complex.X i) ∧ Module.Finite (R k d) (P.complex.X i)) ∧
      (∀ i : ℕ, d < i → Subsingleton (P.complex.X i)) := by
  have hK := CommutativeAlgebraNotes.CompleteRegularPowerSeries.overField k d
  let : IsRegularLocalRing (R k d) := hK.2.1
  rcases subsingleton_or_nontrivial M with hM | hM
  · let : ∀ i, Subsingleton (((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj M).X i) :=
      fun i => by
        by_cases hi : i = 0
        · subst i
          exact (HomologicalComplex.singleObjXSelf _ _ M).toLinearEquiv.injective.subsingleton
        · exact ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)
    let P : ProjectiveResolution M :=
      { complex := (HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj M
        projective := fun i => by
          apply ModuleCat.projective_of_categoryTheory_projective
        π := 𝟙 _
        quasiIso := inferInstance }
    exact ⟨P, fun i => ⟨inferInstanceAs (Module.Free (R k d) (P.complex.X i)),
      inferInstanceAs (Module.Finite (R k d) (P.complex.X i))⟩, fun i _ => by
      change Subsingleton (((HomologicalComplex.single _ (ComplexShape.down ℕ) 0).obj M).X i)
      infer_instance⟩
  · obtain ⟨P, hfin, hfree, hbound⟩ :=
      AdvCommAlg.CohenMacaulay.regularLocal_exists_finiteFreeResolution (R k d) M d
        (AdvCommAlg.Depth.depthDegree (R k d) M) hK.2.2.2.2.1
        (AdvCommAlg.Depth.depth_finite (R k d) M).2.symm
    exact ⟨P, fun i => ⟨hfree i, hfin i⟩, fun i hi => hbound i ((Nat.sub_le ..).trans_lt hi)⟩

section FiniteExactFunctors

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B]
variable {ι : Type} {c : ComplexShape ι}

private def finiteComplex (C : HomologicalComplex (ModuleCat.{u} A) c)
    (h : ∀ i, Module.Finite A (C.X i)) : HomologicalComplex (FGModuleCat.{u} A) c where
  X i := ⟨C.X i, h i⟩
  d i j := ⟨C.d i j⟩
  shape i j hij := ObjectProperty.hom_ext _ (C.shape i j hij)
  d_comp_d' i j l _ _ := ObjectProperty.hom_ext _ (C.d_comp_d i j l)

private theorem map_quasiIso_of_finite (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.Additive]
    (hF : ∀ (U : ShortComplex (ModuleCat.{u} A)), Module.Finite A U.X₁ →
      Module.Finite A U.X₂ → Module.Finite A U.X₃ → U.ShortExact → (U.map F).ShortExact)
    {C D : HomologicalComplex (ModuleCat.{u} A) c} (f : C ⟶ D) [QuasiIso f]
    (hC : ∀ i, Module.Finite A (C.X i)) (hD : ∀ i, Module.Finite A (D.X i)) :
    QuasiIso ((F.mapHomologicalComplex c).map f) := by
  let I : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := forget₂ _ _
  let g : finiteComplex C hC ⟶ finiteComplex D hD :=
    { f i := ⟨f.f i⟩
      comm' i j _ := ObjectProperty.hom_ext _ (f.comm i j) }
  have hg : QuasiIso g :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology g I).mp (show QuasiIso f by infer_instance)
  let G := I ⋙ F
  have he : ∀ U : ShortComplex (FGModuleCat.{u} A), U.ShortExact → (U.map G).ShortExact := by
    intro U hU
    exact hF (U.map I) U.X₁.property U.X₂.property U.X₃.property (hU.map_of_exact I)
  have hG : G.PreservesHomology := ((Functor.exact_tfae G).out 1 3).mp he
  exact HomologicalComplex.quasiIso_map_of_preservesHomology g G

end FiniteExactFunctors

private instance exterior_right_additive (M : ModuleCat.{u} (R k d)) :
    ((exteriorBifunctor k d).obj M).Additive where
  map_add := by
    intro N N' f g
    apply exteriorPair_hom_ext
    intro s m n
    change (s ⊗ₜ[R k d] m) ⊗ₜ[Y k d] toY (f n + g n) =
      (s ⊗ₜ[R k d] m) ⊗ₜ[Y k d] toY (f n) + (s ⊗ₜ[R k d] m) ⊗ₜ[Y k d] toY (g n)
    exact TensorProduct.tmul_add _ _ _

private instance exterior_left_additive (N : ModuleCat.{u} (R k d)) :
    ((exteriorBifunctor k d).flip.obj N).Additive where
  map_add := by
    intro M M' f g
    apply exteriorPair_hom_ext
    intro s m n
    change ((s ⊗ₜ[R k d] (f m + g m)) ⊗ₜ[Y k d] toY n) =
      ((s ⊗ₜ[R k d] f m) ⊗ₜ[Y k d] toY n) + ((s ⊗ₜ[R k d] g m) ⊗ₜ[Y k d] toY n)
    rw [TensorProduct.tmul_add, TensorProduct.add_tmul]

private theorem exterior_right_exact (M : ModuleCat.{u} (R k d)) [Module.Finite (R k d) M]
    (U : ShortComplex (ModuleCat.{u} (R k d)))
    [Module.Finite (R k d) U.X₁] [Module.Finite (R k d) U.X₂] [Module.Finite (R k d) U.X₃]
    (hU : U.ShortExact) : (U.map ((exteriorBifunctor k d).obj M)).ShortExact := by
  let f := ExteriorTensorProduct.Spec.onYMapValue (D := k) (a := d) U.f.hom
  let g := ExteriorTensorProduct.Spec.onYMapValue (D := k) (a := d) U.g.hom
  have h : ExteriorTensorExactness.Spec.ShortExact f g :=
    ⟨hU.moduleCat_injective_f,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact,
      hU.moduleCat_surjective_g⟩
  obtain ⟨hi, he, hs⟩ := ExteriorTensorExactness.exactRight k d d M
    (ExteriorTensorProduct.OnY U.X₁) (ExteriorTensorProduct.OnY U.X₂)
    (ExteriorTensorProduct.OnY U.X₃) f g h
  exact ModuleCat.shortComplex_shortExact _ he hi hs

private theorem exterior_left_exact (N : ModuleCat.{u} (R k d)) [Module.Finite (R k d) N]
    (U : ShortComplex (ModuleCat.{u} (R k d)))
    [Module.Finite (R k d) U.X₁] [Module.Finite (R k d) U.X₂] [Module.Finite (R k d) U.X₃]
    (hU : U.ShortExact) : (U.map ((exteriorBifunctor k d).flip.obj N)).ShortExact := by
  obtain ⟨hi, he, hs⟩ := ExteriorTensorExactness.exactLeft k d d U.X₁ U.X₂ U.X₃
    (ExteriorTensorProduct.OnY N) U.f.hom U.g.hom
    ⟨hU.moduleCat_injective_f,
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact U).mp hU.exact,
      hU.moduleCat_surjective_g⟩
  exact ModuleCat.shortComplex_shortExact _ he hi hs

private theorem extendChain_isZero {A : Type u} [Ring A]
    (P : ChainComplex (ModuleCat.{u} A) ℕ) (i : ℤ) (hi : i < 0) :
    IsZero ((extendChain P).X i) :=
  P.isZero_extend_X _ _ (fun n hn => by change (n : ℤ) = i at hn; omega)

private theorem extendChain_finite {A : Type u} [Ring A]
    (P : ChainComplex (ModuleCat.{u} A) ℕ) (h : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    Module.Finite A ((extendChain P).X i) := by
  by_cases hi : i < 0
  · have := ModuleCat.subsingleton_of_isZero (extendChain_isZero P i hi)
    infer_instance
  · have e := P.extendXIso nonnegativeEmbedding (i := i.toNat) (i' := i)
      (Int.toNat_of_nonneg (by omega))
    have := h i.toNat
    exact Module.Finite.equiv e.toLinearEquiv.symm

private theorem extendChain_free {A : Type u} [Ring A]
    (P : ChainComplex (ModuleCat.{u} A) ℕ) (h : ∀ n, Module.Free A (P.X n)) (i : ℤ) :
    Module.Free A ((extendChain P).X i) := by
  by_cases hi : i < 0
  · have := ModuleCat.subsingleton_of_isZero (extendChain_isZero P i hi)
    infer_instance
  · have e := P.extendXIso nonnegativeEmbedding (i := i.toNat) (i' := i)
      (Int.toNat_of_nonneg (by omega))
    have := h i.toNat
    exact Module.Free.of_equiv e.toLinearEquiv.symm

private theorem single_finite {A : Type u} [Ring A] (M : ModuleCat.{u} A) [Module.Finite A M]
    (i : ℤ) : Module.Finite A (((HomologicalComplex.single _ chainShape 0).obj M).X i) := by
  by_cases hi : i = 0
  · subst i
    exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (V := ModuleCat A) chainShape 0 M).toLinearEquiv.symm
  · have := ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_single_obj_X chainShape 0 M i hi)
    infer_instance

open HomologicalComplex in
private def extendAugmentation {A : Type u} [Ring A] {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) : extendChain P.complex ⟶ (single _ chainShape 0).obj M :=
  (nonnegativeEmbedding.extendFunctor _).map P.π ≫
    (extendSingleIso nonnegativeEmbedding M (i := 0) (i' := 0) rfl).hom

private instance {A : Type u} [Ring A] {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) : QuasiIso (extendAugmentation P) := by
  unfold extendAugmentation
  change QuasiIso (HomologicalComplex.extendMap P.π nonnegativeEmbedding ≫ _)
  infer_instance

section ColumnComparison

open HomologicalComplex
open AdvancedHomologicalAlgebra.AugmentedDoubleComplexComparison

variable {A B : Type u} [CommRing A] [CommRing B]
variable (F : ModuleCat.{u} A ⥤ ModuleCat.{u} A ⥤ ModuleCat.{u} B)
variable [F.PreservesZeroMorphisms] [∀ M, (F.obj M).PreservesZeroMorphisms]
variable [∀ N, (F.flip.obj N).PreservesZeroMorphisms]

private abbrev pairBicomplex (P Q : ChainComplex (ModuleCat.{u} A) ℤ) :=
  ((F.mapBifunctorHomologicalComplex chainShape chainShape).obj P).obj Q

private theorem pair_quadrant (P Q : ChainComplex (ModuleCat.{u} A) ℕ)
    (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (((pairBicomplex F (extendChain P) (extendChain Q)).X p).X q) := by
  rcases h with hp | hq
  · exact Functor.map_isZero (F.flip.obj ((extendChain Q).X q)) (extendChain_isZero P p hp)
  · exact Functor.map_isZero (F.obj ((extendChain P).X p)) (extendChain_isZero Q q hq)

set_option backward.isDefEq.respectTransparency false in
private theorem total_column (P Q : ChainComplex (ModuleCat.{u} A) ℕ) {N : ModuleCat.{u} A}
    (a : extendChain Q ⟶ (single _ chainShape 0).obj N)
    (ha : ∀ p : ℤ, QuasiIso (((F.obj ((extendChain P).X p)).mapHomologicalComplex chainShape).map a)) :
    ∃ e : (pairBicomplex F (extendChain P) (extendChain Q)).total chainShape ⟶
        ((F.flip.obj N).mapHomologicalComplex chainShape).obj (extendChain P),
      QuasiIso e := by
  let K := pairBicomplex F (extendChain P) (extendChain Q)
  let L := ((F.flip.obj N).mapHomologicalComplex chainShape).obj (extendChain P)
  let η := F.flip.map (a.f 0 ≫ (singleObjXSelf chainShape 0 N).hom)
  let b : K.flip.X 0 ⟶ L := (η.mapHomologicalComplex chainShape).app (extendChain P)
  have hz : ∀ p q, chainShape.Rel q 0 → (K.X p).d q 0 ≫ b.f p = 0 := by
    intro p q hq
    let G := F.obj ((extendChain P).X p)
    change G.map ((extendChain Q).d q 0) ≫ G.map
      (a.f 0 ≫ (singleObjXSelf chainShape 0 N).hom) = 0
    rw [← G.map_comp, ← Category.assoc, ← a.comm q 0, single_obj_d, comp_zero,
      zero_comp, G.map_zero]
  have hc (p : ℤ) : QuasiIso (mkHomToSingle (K := K.X p) (j := 0) (b.f p) (hz p)) := by
    let G := F.obj ((extendChain P).X p)
    let v := (G.mapHomologicalComplex chainShape).map a ≫
      (singleMapHomologicalComplex G chainShape 0).hom.app N
    have he : mkHomToSingle (K := K.X p) (j := 0) (b.f p) (hz p) = v := by
      apply to_single_hom_ext
      simp only [mkHomToSingle_f, v, comp_f, singleMapHomologicalComplex_hom_app_self]
      change G.map (a.f 0 ≫ (singleObjXSelf chainShape 0 N).hom) ≫ _ = _
      rw [G.map_comp, Category.assoc]
      rfl
    rw [he]
    have := ha p
    dsimp only [v, G]
    infer_instance
  obtain ⟨e, he, _⟩ := chain_column_assembly K (pair_quadrant F P Q) L b hz
    (fun p => by have := hc p; infer_instance) (fun p q hq => by
      have := hc p
      exact (isZero_single_obj_homology _ 0 (L.X p) q (ne_of_gt hq)).of_iso
        (isoOfQuasiIsoAt (mkHomToSingle (K := K.X p) (j := 0) (b.f p) (hz p)) q))
  exact ⟨e, he⟩

end ColumnComparison

private theorem exterior_pair_free (U V : ModuleCat.{u} (R k d))
    [Module.Free (R k d) U] [Module.Free (R k d) V] :
    Module.Free (S k d d) (exteriorPair U V) := by
  let σ := (ExteriorTensorProduct.xToY k d).toRingEquiv
  let : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
  let : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv σ.symm
  let e : V ≃ₛₗ[σ.toRingHom] ExteriorTensorProduct.OnY V :=
    { __ := (ExteriorTensorProduct.toYSemilinear (D := k) (a := d) (P := V))
      __ := Equiv.ofBijective toY ExteriorTensorProduct.toY_bijective }
  have := Module.Free.of_equiv (σ' := σ.symm.toRingHom) e
  change Module.Free (S k d d) ((S k d d ⊗[R k d] U) ⊗[Y k d] ExteriorTensorProduct.OnY V)
  infer_instance

/-- Zero summands outside a finite subset can be removed from a module coproduct. -/
private def finiteCoproductEquiv {A : Type u} [CommRing A] {ι : Type}
    (U : ι → ModuleCat.{u} A) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i, ¬ p i → IsZero (U i)) :
    (∐ U) ≅ ∐ (fun i : Subtype p => U i) := by
  let V := fun i : Subtype p => U i
  let f : ∐ U ⟶ ∐ V := Sigma.desc fun i => if hi : p i then Sigma.ι V ⟨i, hi⟩ else 0
  let g : ∐ V ⟶ ∐ U := Sigma.desc fun i => Sigma.ι U i
  refine ⟨f, g, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro i
    by_cases hi : p i
    · simp [f, g, hi, V]
    · exact (h i hi).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp [f, g, V, i.property]

private theorem exterior_total_terms (P Q : ChainComplex (ModuleCat.{u} (R k d)) ℕ)
    (hP : ∀ i, Module.Free (R k d) (P.X i) ∧ Module.Finite (R k d) (P.X i))
    (hQ : ∀ i, Module.Free (R k d) (Q.X i) ∧ Module.Finite (R k d) (Q.X i)) (n : ℤ) :
    Module.Free (S k d d) ((exteriorTotal k d P Q).X n) ∧
      Module.Finite (S k d d) ((exteriorTotal k d P Q).X n) := by
  let K := exteriorBicomplex k d (extendChain P) (extendChain Q)
  let I := {i : ℤ × ℤ // i.1 + i.2 = n}
  let U (i : I) := (K.X i.val.1).X i.val.2
  let p (i : I) := 0 ≤ i.val.1 ∧ 0 ≤ i.val.2
  let : DecidablePred p := fun i => inferInstanceAs (Decidable (_ ∧ _))
  have hzero (i : I) (hi : ¬p i) : IsZero (U i) :=
    pair_quadrant (exteriorBifunctor k d) P Q i.val.1 i.val.2 (by dsimp [p] at hi; omega)
  have : Finite (Subtype p) := by
    apply Finite.of_injective (fun i : Subtype p =>
      (⟨i.val.val.1.toNat, by
        have h := i.val.property
        have h' := i.property
        dsimp [p] at h'
        omega⟩ : Fin (n.toNat + 1)))
    intro i j hij
    have hi := i.val.property
    have hj := j.val.property
    have hip := i.property
    have hjp := j.property
    dsimp [p] at hip hjp
    have hh := congrArg Fin.val hij
    dsimp at hh
    exact Subtype.ext (Subtype.ext (Prod.ext (by omega) (by omega)))
  let V (i : Subtype p) := U i
  have : ∀ i, Module.Free (S k d d) (V i) := fun i => by
    have := extendChain_free P (fun j => (hP j).1) i.val.val.1
    have := extendChain_free Q (fun j => (hQ j).1) i.val.val.2
    exact exterior_pair_free k d _ _
  have : ∀ i, Module.Finite (S k d d) (V i) := fun i => by
    have := extendChain_finite P (fun j => (hP j).2) i.val.val.1
    have := extendChain_finite Q (fun j => (hQ j).2) i.val.val.2
    change Module.Finite (S k d d) (exteriorPair ((extendChain P).X i.val.val.1)
      ((extendChain Q).X i.val.val.2))
    exact ExteriorTensorProduct.finite
  let e : (exteriorTotal k d P Q).X n ≅ _ :=
    finiteCoproductEquiv U p hzero ≪≫ ModuleCat.coprodIsoDirectSum V
  have hfree : Module.Free (S k d d) (DirectSum (Subtype p) (fun i => V i)) := inferInstanceAs
    (Module.Free (S k d d) (Π₀ (i : Subtype p), V i))
  have hfinite : Module.Finite (S k d d) (DirectSum (Subtype p) (fun i => V i)) := inferInstanceAs
    (Module.Finite (S k d d) (Π₀ (i : Subtype p), V i))
  exact ⟨Module.Free.of_equiv e.toLinearEquiv.symm, Module.Finite.equiv e.toLinearEquiv.symm⟩

private theorem extendChain_isZero_above {A : Type u} [Ring A]
    (P : ChainComplex (ModuleCat.{u} A) ℕ) (h : ∀ n : ℕ, d < n → Subsingleton (P.X n))
    (i : ℤ) (hi : (d : ℤ) < i) : IsZero ((extendChain P).X i) := by
  have := h i.toNat (by omega)
  exact (ModuleCat.isZero_of_subsingleton (P.X i.toNat)).of_iso
    (P.extendXIso nonnegativeEmbedding (Int.toNat_of_nonneg (by omega)))

private theorem exterior_total_bounded (P Q : ChainComplex (ModuleCat.{u} (R k d)) ℕ)
    (hP : ∀ n : ℕ, d < n → Subsingleton (P.X n))
    (hQ : ∀ n : ℕ, d < n → Subsingleton (Q.X n))
    (n : ℤ) (hn : n < 0 ∨ (2 * d : ℤ) < n) :
    IsZero ((exteriorTotal k d P Q).X n) := by
  let F := exteriorBifunctor k d
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  change p + q = n at hpq
  have h : IsZero (((exteriorBicomplex k d (extendChain P) (extendChain Q)).X p).X q) := by
    rcases hn with hn | hn
    · exact pair_quadrant F P Q p q (by omega)
    · by_cases hp : (d : ℤ) < p
      · exact Functor.map_isZero (F.flip.obj ((extendChain Q).X q))
          (extendChain_isZero_above d P hP p hp)
      · exact Functor.map_isZero (F.obj ((extendChain P).X p))
          (extendChain_isZero_above d Q hQ q (by omega))
  exact h.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_total_augmented (M N : ModuleCat.{u} (R k d))
    [Module.Finite (R k d) M] [Module.Finite (R k d) N]
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hP : ∀ i, Module.Finite (R k d) (P.complex.X i))
    (hQ : ∀ i, Module.Finite (R k d) (Q.complex.X i)) :
    ∃ ε : exteriorTotal k d P.complex Q.complex ⟶
        (HomologicalComplex.single _ chainShape 0).obj (exteriorPair M N), QuasiIso ε := by
  let B := exteriorBifunctor k d
  have : IsNoetherianRing (R k d) := inferInstance
  obtain ⟨a, ha⟩ := total_column B P.complex Q.complex (extendAugmentation Q) (fun p => by
    have := extendChain_finite P.complex hP p
    exact map_quasiIso_of_finite (B.obj ((extendChain P.complex).X p))
      (fun U h₁ h₂ h₃ hU => exterior_right_exact k d _ U hU) (extendAugmentation Q)
      (extendChain_finite Q.complex hQ) (single_finite N))
  let G := B.flip.obj N
  have hG := map_quasiIso_of_finite G
    (fun U h₁ h₂ h₃ hU => exterior_left_exact k d N U hU) (extendAugmentation P)
    (extendChain_finite P.complex hP) (single_finite M)
  exact ⟨a ≫ (G.mapHomologicalComplex chainShape).map (extendAugmentation P) ≫
    (HomologicalComplex.singleMapHomologicalComplex G chainShape 0).hom.app M, inferInstance⟩

theorem finite_free_resolution : Spec.FiniteFreeResolution := by
  intro k _ d M N _ _
  obtain ⟨P, hP, hPd⟩ := exists_free_resolution k d M
  obtain ⟨Q, hQ, hQd⟩ := exists_free_resolution k d N
  obtain ⟨ε, hε⟩ := exterior_total_augmented k d M N P Q (fun i => (hP i).2)
    (fun i => (hQ i).2)
  exact ⟨P, Q, hP, hQ, fun i hi => ⟨hPd i hi, hQd i hi⟩, ε, hε,
    exterior_total_terms k d P.complex Q.complex hP hQ,
    exterior_total_bounded k d P.complex Q.complex hPd hQd,
    ⟨totalBaseChangeIso k d chainShape (extendChain P.complex) (extendChain Q.complex)⟩⟩

section Nonnegative

open HomologicalComplex

variable {A : Type u} [CommRing A]
variable (C : ChainComplex (ModuleCat.{u} A) ℤ)

/-- The obvious restriction followed by extension recovers a nonnegative complex. -/
private def reextend (hC : ∀ i : ℤ, i < 0 → IsZero (C.X i)) :
    C ≅ extendChain (C.restriction nonnegativeEmbedding) := by
  let e := nonnegativeEmbedding
  let f := e.liftExtend (𝟙 (C.restriction e)) (fun j hj i hi => by
    obtain ⟨n, hn⟩ := e.mem_prev hi
    exact (hj.notMem hi n hn).elim)
  have hf : ∀ i, IsIso (f.f i) := by
    intro i
    by_cases hi : 0 ≤ i
    · have he : e.f i.toNat = i := Int.toNat_of_nonneg hi
      rw [show f.f i = _ from e.liftExtend_f _ _ he]
      infer_instance
    · have h := hC i (by omega)
      exact h.isIso (extendChain_isZero (C.restriction e) i (by omega)) _
  have := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

private def nonnegativeHomologyIso (hC : ∀ i : ℤ, i < 0 → IsZero (C.X i)) (i : ℕ) :
    C.homology (i : ℤ) ≅ (C.restriction nonnegativeEmbedding).homology i :=
  (homologyFunctor _ _ (i : ℤ)).mapIso (reextend C hC) ≪≫
    (C.restriction nonnegativeEmbedding).extendHomologyIso nonnegativeEmbedding rfl

private def restrictExtendIso (P : ChainComplex (ModuleCat.{u} A) ℕ) :
    (extendChain P).restriction nonnegativeEmbedding ≅ P :=
  Hom.isoOfComponents (fun i => P.extendXIso nonnegativeEmbedding rfl) (by
    intro i j _
    change _ = (P.extend nonnegativeEmbedding).d (nonnegativeEmbedding.f i)
      (nonnegativeEmbedding.f j) ≫ _
    rw [P.extend_d_eq nonnegativeEmbedding (i := i) (j := j) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl)

private theorem reextend_f (hC : ∀ i : ℤ, i < 0 → IsZero (C.X i))
    {n : ℕ} {i : ℤ} (h : nonnegativeEmbedding.f n = i) :
    (reextend C hC).hom.f i =
      (C.restrictionXIso nonnegativeEmbedding h).inv ≫
        ((C.restriction nonnegativeEmbedding).extendXIso nonnegativeEmbedding h).inv := by
  unfold reextend
  simp only [asIso_hom]
  erw [nonnegativeEmbedding.liftExtend_f _ _ h]
  rw [id_f, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_quasiIso {C D : ChainComplex (ModuleCat.{u} A) ℤ}
    (f : C ⟶ D) [QuasiIso f]
    (hC : ∀ i : ℤ, i < 0 → IsZero (C.X i))
    (hD : ∀ i : ℤ, i < 0 → IsZero (D.X i)) :
    QuasiIso (restrictionMap f nonnegativeEmbedding) := by
  let e := nonnegativeEmbedding
  have h : (reextend C hC).hom ≫ extendMap (restrictionMap f e) e =
      f ≫ (reextend D hD).hom := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : 0 ≤ i
    · have he : e.f i.toNat = i := Int.toNat_of_nonneg hi
      rw [comp_f, comp_f]
      rw [reextend_f C hC he, reextend_f D hD he, extendMap_f _ _ he,
        restrictionMap_f' _ _ he]
      simp
      rfl
    · exact (hC i (by omega)).eq_of_src _ _
  apply (quasiIso_extendMap_iff _ e).mp
  apply (quasiIso_iff_comp_left (reextend C hC).hom _).mp
  rw [h]
  infer_instance

private def restrictResolution {M : ModuleCat.{u} A}
    (ε : C ⟶ (single _ chainShape 0).obj M) [QuasiIso ε]
    (hC : ∀ i : ℤ, i < 0 → IsZero (C.X i))
    (hf : ∀ i : ℕ, Module.Free A (C.X (i : ℤ))) : ProjectiveResolution M where
  complex := C.restriction nonnegativeEmbedding
  projective i := by
    change Projective (C.X (i : ℤ))
    have := hf i
    exact ModuleCat.projective_of_categoryTheory_projective (C.X (i : ℤ))
  π := restrictionMap
      (ε ≫ (extendSingleIso nonnegativeEmbedding M (i := 0) (i' := 0) rfl).inv)
      nonnegativeEmbedding ≫ (restrictExtendIso ((ChainComplex.single₀ _).obj M)).hom
  quasiIso := by
    have := restriction_quasiIso
      (ε ≫ (extendSingleIso nonnegativeEmbedding M (i := 0) (i' := 0) rfl).inv) hC
      (extendChain_isZero ((ChainComplex.single₀ _).obj M))
    infer_instance

open P103.Specs.Ch10.Comparison (LeftResolution) in
private def moduleResolution {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    LeftResolution A M where
  complex := P.complex
  ε := (P.π.f 0 ≫ (singleObjXSelf (ComplexShape.down ℕ) 0 M).hom).hom
  surjective := (ModuleCat.epi_iff_surjective _).mp (by infer_instance)
  exact_zero := by
    have h := P.exact₀.moduleCat_range_eq_ker
    rw [h]
    apply Eq.symm
    exact LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.mpr (singleObjXSelf (ComplexShape.down ℕ) 0 M).toLinearEquiv.injective)
  exact_succ i := (P.exact_succ i).moduleCat_range_eq_ker

end Nonnegative

section TorComparison

open HomologicalComplex
open scoped MonoidalCategory
open P103.Specs.Ch12.TorBaseChange (coefficientComplex coefficientTensorFunctor)
open private categoricalHomologyEquiv from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.Intersection.IsolatedTorSupport

private theorem ordinary_total_tor (M N : ModuleCat.{u} (R k d))
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
    (hP : ∀ i, Module.Free (R k d) (P.complex.X i)) (i : ℕ) :
    Nonempty (((ordinaryBicomplex k d (extendChain P.complex) (extendChain Q.complex)).total
      chainShape).homology (i : ℤ) ≃ₗ[R k d] Tor M N i) := by
  let B := MonoidalCategory.tensoringLeft (ModuleCat.{u} (R k d))
  let F := MonoidalCategory.tensorRight N
  let L := (F.mapHomologicalComplex chainShape).obj (extendChain P.complex)
  obtain ⟨e, he⟩ := total_column B P.complex Q.complex (extendAugmentation Q) (fun p => by
    have := extendChain_free P.complex hP p
    let G := MonoidalCategory.tensorLeft ((extendChain P.complex).X p)
    have hG : PreservesFiniteLimits G ∧ PreservesFiniteColimits G :=
      ⟨inferInstance, inferInstance⟩
    have : G.PreservesHomology := ((Functor.exact_tfae G).out 4 3).mp hG
    exact HomologicalComplex.quasiIso_map_of_preservesHomology (extendAugmentation Q) G)
  have hL (p : ℤ) (hp : p < 0) : IsZero (L.X p) :=
    F.map_isZero (extendChain_isZero P.complex p hp)
  let e₁ := isoOfQuasiIsoAt e (i : ℤ) ≪≫ nonnegativeHomologyIso L hL i
  let e₂ : L.restriction nonnegativeEmbedding ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex :=
    (F.mapHomologicalComplex _).mapIso (restrictExtendIso P.complex)
  let e₃ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex ≅
      coefficientComplex (S := R k d) P.complex N :=
    Hom.isoOfComponents (fun j => (TensorProduct.comm (R k d) (P.complex.X j) N).toModuleIso)
      (by
        intro j l _
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro a b
        rfl)
  let e₄ := (homologyFunctor _ _ i).mapIso (e₂ ≪≫ e₃)
  let e₅ := categoricalHomologyEquiv (coefficientComplex (S := R k d) P.complex N) i
  exact ⟨(e₁ ≪≫ e₄).toLinearEquiv.trans (e₅.trans
    (IsolatedTorSupport.torLeftEquiv M N (moduleResolution P)
      (fun j => ModuleCat.projective_of_module_projective (P.complex.X j)) i).symm)⟩

private abbrev DiagonalQuotient :=
  S k d d ⧸ AdvCommAlg.Koszul.listIdeal (diagonalList k d)

private def quotientToDiagonal :
    DiagonalQuotient k d ≃ₗ[S k d d] ↥((restrictDiagonal k d).obj (ModuleCat.of (R k d) (R k d))) := by
  let e : DiagonalQuotient k d ≃ₐ[k] R k d :=
    (Ideal.quotientEquivAlgOfEq k (ofList_difference k d)).trans (diagonalQuotientEquiv k d)
  refine { e.toRingEquiv.toAddEquiv with map_smul' := ?_ }
  intro s q
  change e (Ideal.Quotient.mk _ s * q) = identify k d s * e q
  rw [map_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def diagonalTensorIso (U : ModuleCat.{u} (S k d d)) :
    (coefficientTensorFunctor (S k d d) (S k d d) (DiagonalQuotient k d)).obj U ≅
      (restrictDiagonal k d).obj ((extendDiagonal k d).obj U) := by
  let V := (restrictDiagonal k d).obj ((extendDiagonal k d).obj U)
  let W := (coefficientTensorFunctor (S k d d) (S k d d) (DiagonalQuotient k d)).obj U
  let e : W ≃+ V :=
    (TensorProduct.congr (quotientToDiagonal k d) (LinearEquiv.refl (S k d d) U)).toAddEquiv
  have he (s : S k d d) (x : W) : e (s • x) = s • e x := by
    change (DiagonalQuotient k d ⊗[S k d d] U) at x
    refine TensorProduct.inductionOn (motive := fun z => e (s • (show W from z)) = s • e z) x ?_ ?_
    · intro q u
      change extendDiagonalTmul k d U (quotientToDiagonal k d (s • q)) u =
        extendDiagonalTmul k d U (identify k d s * (show R k d from quotientToDiagonal k d q)) u
      congr 1
      exact (quotientToDiagonal k d).map_smul s q
    · intro x y hx hy
      simpa only [smul_add, map_add] using congrArg₂ (· + ·) hx hy
  let e' : W ≃ₗ[S k d d] V := { e with map_smul' := he }
  exact e'.toModuleIso

private def diagonalComplexIso (C : ChainComplex (ModuleCat.{u} (S k d d)) ℕ) :
    coefficientComplex (S := S k d d) C (DiagonalQuotient k d) ≅
      ((restrictDiagonal k d).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((extendDiagonal k d).mapHomologicalComplex (ComplexShape.down ℕ)).obj C) :=
  Hom.isoOfComponents (fun j => diagonalTensorIso k d (C.X j)) (by
    intro j l _
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro a b
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem homology_tor : Spec.HomologyTor.{u} := by
  intro k _ d M N _ _ i
  obtain ⟨P, Q, hP, _, _, ε, hε, hfree, hbound, ⟨diagonalTotalIso⟩⟩ :=
    finite_free_resolution k d M N
  let A := R k d
  let B := S k d d
  let C := exteriorTotal k d P.complex Q.complex
  let F := extendDiagonal k d
  let G : ModuleCat.{u} A ⥤ ModuleCat.{u} B := restrictDiagonal k d
  let D := (F.mapHomologicalComplex chainShape).obj C
  let T := exteriorPair M N
  let Z := ModuleCat.of B (DiagonalQuotient k d)
  have hC (j : ℤ) (hj : j < 0) : IsZero (C.X j) := hbound j (Or.inl hj)
  have hD (j : ℤ) (hj : j < 0) : IsZero (D.X j) := F.map_isZero (hC j hj)
  let E := restrictResolution C ε hC (fun j => (hfree (j : ℤ)).1)
  let koszulIso := IsolatedTorSupport.koszulHomologyTorEquiv T (diagonalList k d)
    (diagonalRegular k d) i
  let resolutionIso := IsolatedTorSupport.torRightEquiv Z T (moduleResolution E)
    (fun j => ModuleCat.projective_of_module_projective (E.complex.X j)) i
  let E' := coefficientComplex (S := B) E.complex (DiagonalQuotient k d)
  let categoricalIso := (categoricalHomologyEquiv E' i).symm
  let coefficientIso := (homologyFunctor _ _ i).mapIso (diagonalComplexIso k d E.complex)
  have hG : G.PreservesHomology := ⟨fun f => inferInstance, fun f => inferInstance⟩
  let restrictionIso : _ ≅ G.obj ((D.restriction nonnegativeEmbedding).homology i) :=
    (ShortComplex.mapHomologyIso (D.restriction nonnegativeEmbedding |>.sc i) G)
  let totalHomologyIso := G.mapIso ((nonnegativeHomologyIso D hD i).symm ≪≫
    (homologyFunctor _ _ (i : ℤ)).mapIso diagonalTotalIso)
  obtain ⟨ordinaryTorIso⟩ := ordinary_total_tor k d M N P Q (fun j => (hP j).1) i
  let restrictedTorIso := (G.mapIso ordinaryTorIso.toModuleIso).toLinearEquiv
  let reducedTotalIso := (coefficientIso ≪≫ restrictionIso ≪≫ totalHomologyIso).toLinearEquiv
  let e := koszulIso.trans (resolutionIso.trans
    (categoricalIso.trans (reducedTotalIso.trans restrictedTorIso)))
  refine ⟨{ e.toAddEquiv with map_smul' := ?_ }⟩
  intro r x
  change e (includeX k d d r • x) = r • e x
  rw [e.map_smul]
  change identify k d (includeX k d d r) • (e x : Tor M N i) = r • e x
  rw [identify_includeX]

theorem length_comparison : Spec.LengthComparison := by
  intro k _ d M N _ _ i
  obtain ⟨e⟩ := homology_tor k d M N i
  exact (length_restrict_left k d M N i).trans e.length_eq

theorem tensor_quotient_length : Spec.TensorQuotientLength.{u} := by
  intro k _ d M N
  let V : ModuleCat.{u} (S k d d) :=
    (restrictDiagonal k d).obj (ModuleCat.of (R k d) (M ⊗[R k d] N))
  let e : diagonalReduction k d (exteriorPair M N) ≃ₗ[S k d d] V :=
    tensorQuotientEquiv k d M N
  have h : Module.length (S k d d) V = Module.length (R k d) (M ⊗[R k d] N) := by
    let : Module (S k d d) (M ⊗[R k d] N) := V.isModule
    let : IsScalarTower (S k d d) (R k d) (M ⊗[R k d] N) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    exact Module.length_eq_of_surjective (M := M ⊗[R k d] N) (identify_surjective k d)
  exact e.length_eq.trans h

theorem isolated_finite_length : Spec.IsolatedFiniteLength.{u} := by
  intro k _ d M N _ _ h
  refine ⟨Module.length_ne_top_iff.mp ?_, fun i => Module.length_ne_top_iff.mp ?_⟩
  · rw [tensor_quotient_length k d M N]
    exact Module.length_ne_top_iff.mpr h
  · rw [length_comparison k d M N i]
    exact Module.length_ne_top_iff.mpr (IsolatedTorSupport.tor_finite_length_of_tensor M N h i)

end TorComparison

end CommutativeAlgebraNotes.Intersection.FieldDiagonalTor
