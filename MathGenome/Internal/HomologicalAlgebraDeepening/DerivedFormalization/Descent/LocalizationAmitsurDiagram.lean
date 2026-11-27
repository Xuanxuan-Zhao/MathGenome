import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.AmitsurAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Descent.LocalizationCoverFaithfulness
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.LocalizationAmitsurDiagram
import Mathlib.RingTheory.TensorProduct.Pi

/-! The Amitsur diagram of the algebra associated to a finite principal-open cover. -/

open CategoryTheory
open scoped TensorProduct

namespace DerivedFormalization.Descent.LocalizationAmitsurDiagram

open LocalizationAmitsurDiagramSpec
open Algebra.TensorProduct (includeLeft includeRight productMap)

universe u v

variable {A : Type u} [CommRing A] {ι : Type v} (f : ι → A)

private theorem comparison_factor {n : ℕ} (i : Fin n) (b : coverAlgebra f)
    (t : Fin n → ι) :
    comparison f n (AmitsurAlgebras.factor A (coverAlgebra f) i b) t = factorComponent f t i b :=
  AmitsurAlgebras.liftFactors_factor (factorComponent f t) i b

theorem comparison_natural : comparisonNatural.{u, v} := by
  intro A _ ι f m n α
  change (comparison f n).comp (AmitsurAlgebras.map α) = (restrict f α).comp (comparison f m)
  apply AmitsurAlgebras.hom_ext
  intro i
  refine AlgHom.ext fun b ↦ funext fun t ↦ ?_
  change comparison f n (AmitsurAlgebras.map α (AmitsurAlgebras.factor A (coverAlgebra f) i b)) t =
    restrictComponent f α t (comparison f m (AmitsurAlgebras.factor A (coverAlgebra f) i b) (t ∘ α))
  rw [AmitsurAlgebras.map_factor, comparison_factor, comparison_factor]
  change localize (factor_isUnit f t (α i)) (b (t (α i))) =
    ((restrictComponent f α t).comp (localize (factor_isUnit f (t ∘ α) i))) (b (t (α i)))
  exact DFunLike.congr_fun (localization_hom_ext _ _) _

/-- The tensor product of two principal localizations inverts the product of their
denominators, with the comparison specified by the two canonical maps. -/
private noncomputable def tensorAwayEquiv (a b c : A) (hc : c = a * b) :
    Localization.Away a ⊗[A] Localization.Away b ≃ₐ[A] Localization.Away c := by
  let lhs : Localization.Away a →ₐ[A] Localization.Away c :=
    localize (IsLocalization.Away.isUnit_of_dvd c (hc ▸ dvd_mul_right a b))
  let rhs : Localization.Away b →ₐ[A] Localization.Away c :=
    localize (IsLocalization.Away.isUnit_of_dvd c (hc ▸ dvd_mul_left b a))
  let back : Localization.Away c →ₐ[A] Localization.Away a ⊗[A] Localization.Away b :=
    localize (by
      rw [hc, map_mul]
      have hl := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).map
        (includeLeft : Localization.Away a →ₐ[A] Localization.Away a ⊗[A] Localization.Away b)
      have hr := (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b).map
        (includeRight : Localization.Away b →ₐ[A] Localization.Away a ⊗[A] Localization.Away b)
      rw [AlgHom.commutes] at hl hr
      exact hl.mul hr)
  refine AlgEquiv.ofAlgHom (productMap lhs rhs) back (localization_hom_ext _ _) ?_
  apply Algebra.TensorProduct.ext
  · exact localization_hom_ext _ _
  · exact localization_hom_ext _ _

private theorem denominator_snoc {n : ℕ} (t : Fin n → ι) (j : ι) :
    denominator f (Fin.snoc t j) = denominator f t * f j := by
  simp only [denominator, Fin.prod_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc]

/-- Reindex the product over longer tuples by the last entry and the initial tuple. -/
private def snocProductEquiv (n : ℕ) :
    intersectionAlgebra f (n + 1) ≃ₐ[A] ∀ j : ι, ∀ t : Fin n → ι,
      intersection f (Fin.snoc t j) := by
  let e : (Σ _ : ι, Fin n → ι) ≃ (Fin (n + 1) → ι) :=
    (Equiv.sigmaEquivProd ι (Fin n → ι)).trans (Fin.snocEquiv fun _ ↦ ι)
  let e' := (AlgEquiv.piCongrLeft A (fun t : Fin (n + 1) → ι ↦ intersection f t) e).symm
  let curry : (∀ p : Σ _ : ι, Fin n → ι, intersection f (e p)) ≃ₐ[A]
      ∀ j : ι, ∀ t : Fin n → ι, intersection f (Fin.snoc t j) :=
    { Equiv.piCurry (fun j t ↦ intersection f (Fin.snoc t j)) with
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact e'.trans curry

private theorem snocProductEquiv_apply {n : ℕ} (z : intersectionAlgebra f (n + 1))
    (j : ι) (t : Fin n → ι) :
    snocProductEquiv f n z j t = z (Fin.snoc t j) := rfl

/-- Distribute the binary tensor product over both finite products, then localize
away from the product of the denominators in each component. -/
private noncomputable def tensorIntersections [Fintype ι] [DecidableEq ι] (n : ℕ) :
    intersectionAlgebra f n ⊗[A] coverAlgebra f ≃ₐ[A]
      ∀ j : ι, ∀ t : Fin n → ι, intersection f (Fin.snoc t j) :=
  (Algebra.TensorProduct.piRight A A (intersectionAlgebra f n)
    (fun j ↦ Localization.Away (f j))).trans (AlgEquiv.piCongrRight fun j ↦
      (Algebra.TensorProduct.comm A (intersectionAlgebra f n) (Localization.Away (f j))).trans
        ((Algebra.TensorProduct.piRight A A (Localization.Away (f j))
          (fun t : Fin n → ι ↦ intersection f t)).trans (AlgEquiv.piCongrRight fun t ↦
            (Algebra.TensorProduct.comm A (Localization.Away (f j)) (intersection f t)).trans
              (tensorAwayEquiv (denominator f t) (f j) _ (denominator_snoc f t j)))))

private theorem tensorIntersections_tmul [Fintype ι] [DecidableEq ι] {n : ℕ}
    (x : intersectionAlgebra f n) (y : coverAlgebra f) (j : ι) (t : Fin n → ι) :
    tensorIntersections f n (x ⊗ₜ[A] y) j t =
      tensorAwayEquiv (denominator f t) (f j) _ (denominator_snoc f t j)
        (x t ⊗ₜ[A] y j) := rfl


private theorem factorComponent_eq {n : ℕ} (t : Fin n → ι) (i : Fin n)
    (b : coverAlgebra f) {j : ι} (h : t i = j)
    (g : Localization.Away (f j) →ₐ[A] intersection f t) :
    factorComponent f t i b = g (b j) := by
  subst j
  exact DFunLike.congr_fun (localization_hom_ext (localize (factor_isUnit f t i)) g) (b (t i))

private noncomputable def appendLastEquiv (n : ℕ) :
    AmitsurAlgebras.TensorPower A (coverAlgebra f) n ⊗[A] coverAlgebra f ≃ₐ[A]
      AmitsurAlgebras.TensorPower A (coverAlgebra f) (n + 1) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (AmitsurAlgebras.oneEquiv A (coverAlgebra f)).symm).trans
    (AmitsurAlgebras.appendEquiv A (coverAlgebra f) n 1)

private theorem appendLastEquiv_left {n : ℕ} (i : Fin n) (b : coverAlgebra f) :
    appendLastEquiv f n (AmitsurAlgebras.factor A (coverAlgebra f) i b ⊗ₜ[A] 1) =
      AmitsurAlgebras.factor A (coverAlgebra f) i.castSucc b := by
  simp [appendLastEquiv, show Fin.castAdd 1 i = i.castSucc from rfl]

private theorem appendLastEquiv_right (n : ℕ) (b : coverAlgebra f) :
    appendLastEquiv f n (1 ⊗ₜ[A] b) =
      AmitsurAlgebras.factor A (coverAlgebra f) (Fin.last n) b := by
  simp [appendLastEquiv, show Fin.natAdd n (0 : Fin 1) = Fin.last n from rfl]

private theorem comparison_step [Fintype ι] [DecidableEq ι] (n : ℕ)
    (e : AmitsurAlgebras.TensorPower A (coverAlgebra f) n ≃ₐ[A] intersectionAlgebra f n)
    (he : e.toAlgHom = comparison f n) :
    ((snocProductEquiv f n).toAlgHom.comp (comparison f (n + 1))).comp
        (appendLastEquiv f n).toAlgHom =
      (tensorIntersections f n).toAlgHom.comp (Algebra.TensorProduct.congr e AlgEquiv.refl).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · apply AmitsurAlgebras.hom_ext
    intro i
    refine AlgHom.ext fun b ↦ funext fun j ↦ funext fun t ↦ ?_
    change snocProductEquiv f n (comparison f (n + 1)
        (appendLastEquiv f n (AmitsurAlgebras.factor A (coverAlgebra f) i b ⊗ₜ[A] 1))) j t =
      tensorIntersections f n ((Algebra.TensorProduct.congr e AlgEquiv.refl)
        (AmitsurAlgebras.factor A (coverAlgebra f) i b ⊗ₜ[A] 1)) j t
    rw [appendLastEquiv_left, snocProductEquiv_apply, comparison_factor]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.refl_toAlgHom, AlgHom.id_apply, tensorIntersections_tmul, Pi.one_apply]
    rw [he, comparison_factor]
    let join := tensorAwayEquiv (denominator f t) (f j)
      (denominator f (Fin.snoc t j)) (denominator_snoc f t j)
    let incl : intersection f t →ₐ[A] intersection f t ⊗[A] Localization.Away (f j) :=
      includeLeft
    let loc : Localization.Away (f (t i)) →ₐ[A] intersection f t :=
      localize (factor_isUnit f t i)
    let g : Localization.Away (f (t i)) →ₐ[A] intersection f (Fin.snoc t j) :=
      join.toAlgHom.comp (incl.comp loc)
    exact factorComponent_eq f (Fin.snoc t j) i.castSucc b (j := t i) (by simp) g
  · refine AlgHom.ext fun b ↦ funext fun j ↦ funext fun t ↦ ?_
    change snocProductEquiv f n (comparison f (n + 1) (appendLastEquiv f n (1 ⊗ₜ[A] b))) j t =
      tensorIntersections f n ((Algebra.TensorProduct.congr e AlgEquiv.refl) (1 ⊗ₜ[A] b)) j t
    rw [appendLastEquiv_right, snocProductEquiv_apply, comparison_factor]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.refl_toAlgHom, AlgHom.id_apply, map_one, tensorIntersections_tmul, Pi.one_apply]
    let join := tensorAwayEquiv (denominator f t) (f j)
      (denominator f (Fin.snoc t j)) (denominator_snoc f t j)
    let incl : Localization.Away (f j) →ₐ[A] intersection f t ⊗[A] Localization.Away (f j) :=
      includeRight
    let g : Localization.Away (f j) →ₐ[A] intersection f (Fin.snoc t j) :=
      join.toAlgHom.comp incl
    exact factorComponent_eq f (Fin.snoc t j) (Fin.last n) b (j := j) (by simp) g

private noncomputable def comparisonZeroEquiv :
    AmitsurAlgebras.TensorPower A (coverAlgebra f) 0 ≃ₐ[A] intersectionAlgebra f 0 :=
  (AmitsurAlgebras.emptyEquiv A (coverAlgebra f)).trans <|
    (AlgEquiv.funUnique A (Fin 0 → ι) A).symm.trans <|
      AlgEquiv.piCongrRight fun t ↦
        IsLocalization.atUnit A (intersection f t) (denominator f t)
          (by simp [denominator])

theorem comparison_bijective : comparisonBijective.{u, v} := by
  classical
  intro A _ ι _ f n
  let := Fintype.ofFinite ι
  induction n with
  | zero =>
    have h : (comparisonZeroEquiv f).toAlgHom = comparison f 0 :=
      AmitsurAlgebras.hom_ext fun i ↦ Fin.elim0 i
    rw [← h]
    exact (comparisonZeroEquiv f).bijective
  | succ n ih =>
    let e := AlgEquiv.ofBijective (comparison f n) ih
    let e' := ((Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      (tensorIntersections f n)).trans (snocProductEquiv f n).symm
    have h := comparison_step f n e rfl
    have h' : (comparison f (n + 1)).comp (appendLastEquiv f n).toAlgHom = e'.toAlgHom := by
      refine AlgHom.ext fun x ↦ (snocProductEquiv f n).injective ?_
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply,
        AlgEquiv.apply_symm_apply, e'] using DFunLike.congr_fun h x
    have h'' : comparison f (n + 1) =
        ((appendLastEquiv f n).symm.trans e').toAlgHom := by
      refine AlgHom.ext fun x ↦ ?_
      have hx := DFunLike.congr_fun h' ((appendLastEquiv f n).symm x)
      simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
        AlgEquiv.trans_apply] using hx
    rw [h'']
    exact ((appendLastEquiv f n).symm.trans e').bijective


theorem intersection_open : intersectionOpen.{u, v} := by
  classical
  intro A _ ι f n t
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iInf]
  ext p
  simp only [SetLike.mem_coe, Set.mem_iInter, PrimeSpectrum.mem_basicOpen, denominator,
    Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]

theorem coface_component : cofaceComponent.{u, v} := by
  intro A _ ι f p i t x
  exact congrFun (DFunLike.congr_fun (comparison_natural f i.succAbove) x) t

theorem intersection_spectrum : intersectionSpectrum.{u, v} := by
  intro A _ ι f n t
  refine ⟨PrimeSpectrum.localization_away_isOpenEmbedding _ (denominator f t), ?_⟩
  rw [PrimeSpectrum.localization_away_comap_range _ (denominator f t), intersection_open f t]

theorem codegeneracy_component : codegeneracyComponent.{u, v} := by
  intro A _ ι f p i t
  let α : Fin (p + 2) → Fin (p + 1) := i.predAbove
  have hs : Function.Surjective α := Fin.predAbove_surjective i
  let back : intersection f t →ₐ[A] intersection f (t ∘ α) :=
    localize (by
      change IsUnit (algebraMap A (intersection f (t ∘ α)) (∏ j, f (t j)))
      rw [map_prod]
      refine IsUnit.prod_iff.mpr fun j _ ↦ ?_
      obtain ⟨k, rfl⟩ := hs j
      exact factor_isUnit f (t ∘ α) k)
  refine ⟨AlgEquiv.ofAlgHom (restrictComponent f α t) back
    (localization_hom_ext _ _) (localization_hom_ext _ _), rfl, ?_, ?_, ?_, ?_⟩
  · rw [intersection_open f (t ∘ α), intersection_open f t]
    exact hs.iInf_comp (fun j ↦ PrimeSpectrum.basicOpen (f (t j)))
  · simp
  · simp
  · intro x
    exact congrFun (DFunLike.congr_fun (comparison_natural f α) x) t

private noncomputable def comparisonIso [Finite ι] :
    AmitsurAlgebras.augmentedDiagram A (coverAlgebra f) ≅ augmentedDiagram f := by
  let app : ∀ X : AugmentedSimplexCategory,
      (AmitsurAlgebras.augmentedDiagram A (coverAlgebra f)).obj X ≅
        (augmentedDiagram f).obj X
    | .star => Iso.refl _
    | .of p => CommAlgCat.isoMk
        (AlgEquiv.ofBijective (comparison f (p.len + 1)) (comparison_bijective f (p.len + 1)))
  refine NatIso.ofComponents app ?_
  intro X Y α
  cases X with
  | star =>
    cases Y with
    | star =>
      cases α
      rfl
    | of q =>
      apply CommAlgCat.hom_ext
      refine AlgHom.ext fun a ↦ ?_
      change comparison f (q.len + 1)
        (algebraMap A (AmitsurAlgebras.Degree A (coverAlgebra f) q.len) a.down) =
          algebraMap A (intersectionAlgebra f (q.len + 1)) a.down
      exact (comparison f (q.len + 1)).commutes a.down
  | of p =>
    cases Y with
    | star => exact (WithInitial.false_of_to_star α).elim
    | of q =>
      apply CommAlgCat.hom_ext
      exact comparison_natural f (WithInitial.down α).toOrderHom

theorem augmented_comparison : augmentedComparison.{u, v} := by
  intro A _ ι _ f hf
  exact ⟨localizationCover_faithfullyFlat A ι f hf, comparisonIso f, fun _ ↦ rfl, rfl⟩

end DerivedFormalization.Descent.LocalizationAmitsurDiagram
