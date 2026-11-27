import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.SequentialHomotopyLimits
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.Projective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.TowerCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

namespace DerivedFormalization.SequentialHomotopyLimits

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open HomologicalComplex
open CochainComplex (mappingCone mappingCocone)
open CochainComplex.HomComplex
open Specs.DerivedFormalization.Cochains (compValue cohomologyValue derivedValue qValue)
open Specs.DerivedFormalization.TowerExactSequence
open Specs.DerivedFormalization.SequentialHomotopyLimits

universe u v

noncomputable section

variable {R : Type u} [Ring R]

/-- The shifted cone of the identity minus the successor endomorphism. -/
abbrev holim : holimType.{u,v} := @holimValue

/-- The canonical map from the ordinary inverse limit to the shifted cone. -/
abbrev comparison : comparisonType.{u,v} := @comparisonValue

private lemma productComparison_natural {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) (q : ℤ) :
    homologyMap (productMap f) q ≫ productComparison Y q =
      productComparison X q ≫ moduleProductMap (cohomologyTowerMap f q) := by
  let H := cohomologyValue R q
  let a := fun n : ℕ ↦ X.obj (op n)
  let b := fun n : ℕ ↦ Y.obj (op n)
  let pH := Limits.Pi.map (f := fun n ↦ H.obj (a n))
    (g := fun n ↦ H.obj (b n)) (fun n ↦ H.map (f.app (op n)))
  apply Pi.hom_ext
  intro n
  change (H.map (productMap f) ≫ piComparison H b) ≫ Pi.π (fun n ↦ H.obj (b n)) n =
    (piComparison H a ≫ pH) ≫ Pi.π (fun n ↦ H.obj (b n)) n
  have hπ : pH ≫ Pi.π (fun n ↦ H.obj (b n)) n =
      Pi.π (fun n ↦ H.obj (a n)) n ≫ H.map (f.app (op n)) :=
    Limits.Pi.map_π (fun n ↦ H.map (f.app (op n))) n
  rw [Category.assoc, Category.assoc, piComparison_comp_π, hπ,
    piComparison_comp_π_assoc, ← H.map_comp, ← H.map_comp]
  exact congrArg H.map (Limits.Pi.map_π (fun n ↦ f.app (op n)) n)

private instance productComparison_isIso (X : Towers (compValue.{v} R)) (q : ℤ) :
    IsIso (productComparison X q) :=
  cohomology_preservesProduct R ℕ (fun n ↦ X.obj (op n)) q

private theorem productMap_quasiIso {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y)
    (hf : stagewiseQuasiIso f) : QuasiIso (productMap f) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := cohomologyValue R q
  have (n : ℕ) : IsIso (H.map (f.app (op n))) :=
    (quasiIsoAt_iff_isIso_homologyMap _ q).1 ((quasiIso_iff _).1 (hf n) q)
  let pH := Limits.Pi.map (f := fun n : ℕ ↦ H.obj (X.obj (op n)))
    (g := fun n : ℕ ↦ H.obj (Y.obj (op n))) (fun n ↦ H.map (f.app (op n)))
  have hComp : IsIso (homologyMap (productMap f) q ≫ productComparison Y q) := by
    rw [productComparison_natural]
    change IsIso (productComparison X q ≫ pH)
    infer_instance
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ (homologyMap (productMap f) q)
    (productComparison Y q) (productComparison_isIso Y q) hComp

set_option backward.isDefEq.respectTransparency false in
/-- A levelwise quasi-isomorphism induces one on the strict homotopy limit. -/
theorem holim_invariance : holimInvarianceType.{u,v} := by
  intro R _ X Y f hf
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  have hp := productMap_quasiIso f hf
  let p := productMap f
  let Q := DerivedCategory.Q (C := ModuleCat.{v} R)
  let a := mappingCone.triangleMap (differenceValue X) (differenceValue Y) p p
    (difference_natural f)
  have hX : Q.mapTriangle.obj (mappingCone.triangle (differenceValue X)) ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished _
  have hY : Q.mapTriangle.obj (mappingCone.triangle (differenceValue Y)) ∈ distTriang _ :=
    DerivedCategory.mappingCone_triangle_distinguished _
  have hp' : IsIso (Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) p).2 hp
  have ha := isIso₃_of_isIso₁₂ (Q.mapTriangle.map a) hX hY hp' hp'
  apply (CochainComplex.quasiIso_shift_iff _ (-1)).2
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) _).1 ha

section Cocone

variable {K L K' L' : compValue.{v} R} {g : K ⟶ L} {g' : K' ⟶ L'}

private abbrev coconeMap (a : K ⟶ K') (b : L ⟶ L') (w : g ≫ b = a ≫ g') :
    mappingCocone g ⟶ mappingCocone g' :=
  (mappingCone.map g g' a b w)⟦(-1 : ℤ)⟧'

set_option backward.isDefEq.respectTransparency false in
private lemma coconeMap_fst (a : K ⟶ K') (b : L ⟶ L') (w : g ≫ b = a ≫ g') (n : ℤ) :
    (coconeMap a b w).f n ≫ (mappingCocone.fst g').f n =
      (mappingCocone.fst g).f n ≫ a.f n := by
  have hn : (n + -1) + 1 = n := by omega
  simp [mappingCocone.fst, Cocycle.homOf, Cochain.leftShift_v _ (-1) 0
    (by omega) n n (add_zero n) (n + -1) hn, CochainComplex.shiftFunctorObjXIso,
    mappingCone.ext_from_iff g n (n + -1) hn, mappingCone.map]

set_option backward.isDefEq.respectTransparency false in
private lemma coconeMap_snd (a : K ⟶ K') (b : L ⟶ L') (w : g ≫ b = a ≫ g') (n : ℤ) :
    (coconeMap a b w).f n ≫ (mappingCocone.snd g').v n (n + -1) rfl =
      (mappingCocone.snd g).v n (n + -1) rfl ≫ b.f (n + -1) := by
  have hn : (n + -1) + 1 = n := by omega
  simp [mappingCocone.snd, Cochain.leftShift_v _ (-1) (-1)
    (by omega) n (n + -1) rfl (n + -1) (add_zero _), CochainComplex.shiftFunctorObjXIso,
    mappingCone.ext_from_iff g n (n + -1) hn, mappingCone.map,
    Int.negOnePow_even 2 ⟨1, rfl⟩]

private lemma cocone_degree_ext {V : ModuleCat.{v} R} (n : ℤ)
    {a b : V ⟶ (mappingCocone g).X n}
    (h₁ : a ≫ (mappingCocone.fst g).f n = b ≫ (mappingCocone.fst g).f n)
    (h₂ : a ≫ (mappingCocone.snd g).v n (n + -1) rfl =
      b ≫ (mappingCocone.snd g).v n (n + -1) rfl) : a = b := by
  let t := (mappingCocone.fst g).f n ≫ (mappingCocone.inl g).v n n (add_zero n) +
    (mappingCocone.snd g).v n (n + -1) rfl ≫ (mappingCocone.inr g).1.v (n + -1) n (by omega)
  have ht : t = 𝟙 _ := mappingCocone.id_X g n (n + -1) rfl
  calc
    a = a ≫ t := by rw [ht, Category.comp_id]
    _ = b ≫ t := by simp only [t, Preadditive.comp_add, reassoc_of% h₁, reassoc_of% h₂]
    _ = b := by rw [ht, Category.comp_id]

private lemma module_apply_eq {A B : ModuleCat.{v} R} {f g : A ⟶ B} (h : f = g) (x : A) :
    f x = g x := congrArg (fun f : A ⟶ B ↦ f x) h

private lemma cocone_degree_ext_elem (n : ℤ) {x y : (mappingCocone g).X n}
    (h₁ : (mappingCocone.fst g).f n x = (mappingCocone.fst g).f n y)
    (h₂ : (mappingCocone.snd g).v n (n + -1) rfl x =
      (mappingCocone.snd g).v n (n + -1) rfl y) : x = y := by
  have h (z : (mappingCocone g).X n) := module_apply_eq
    (mappingCocone.id_X g n (n + -1) rfl) z
  have hh (z : (mappingCocone g).X n) :
      (mappingCocone.inl g).v n n (add_zero n) ((mappingCocone.fst g).f n z) +
        (mappingCocone.inr g).1.v (n + -1) n (by omega)
          ((mappingCocone.snd g).v n (n + -1) rfl z) = z := h z
  rw [← hh x, h₁, h₂]
  exact hh y

end Cocone

set_option backward.isDefEq.respectTransparency false in
/-- The comparison with the shifted cone is natural on strict tower maps. -/
theorem comparison_naturality : comparisonNaturalityType.{u,v} := by
  intro R _ X Y f
  ext n : 1
  apply cocone_degree_ext (g := differenceValue Y) n
  · have h := (towerShortComplex_naturality R X Y f).1
    simpa only [comparisonValue, comp_f, Category.assoc, mappingCocone.lift_f_fst_f, mappingCocone.lift_f_fst_f_assoc,
      holimValue, coconeMap_fst] using congrArg (fun a ↦ a.f n) h
  · simp only [comparisonValue, holimValue, comp_f, Category.assoc, coconeMap_snd,
      mappingCocone.lift_f_snd_v, mappingCocone.lift_f_snd_v_assoc, Cochain.zero_v, zero_comp, comp_zero]

section Comparison

private def kernelToCocone (S : ShortComplex (compValue.{v} R)) : S.X₁ ⟶ mappingCocone S.g :=
  mappingCocone.lift S.g S.f 0 (by simp [S.zero])

private def coconeQuotient (S : ShortComplex (compValue.{v} R)) :
    mappingCocone S.g ⟶ mappingCocone (𝟙 S.X₃) :=
  coconeMap S.g (𝟙 S.X₃) (by simp)

set_option backward.isDefEq.respectTransparency false in
private lemma coconeQuotient_fst (S : ShortComplex (compValue.{v} R)) (n : ℤ) :
    (coconeQuotient S).f n ≫ (mappingCocone.fst (𝟙 S.X₃)).f n =
      (mappingCocone.fst S.g).f n ≫ S.g.f n :=
  coconeMap_fst _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma coconeQuotient_snd (S : ShortComplex (compValue.{v} R)) (n : ℤ) :
    (coconeQuotient S).f n ≫ (mappingCocone.snd (𝟙 S.X₃)).v n (n + -1) rfl =
      (mappingCocone.snd S.g).v n (n + -1) rfl := by
  simpa [coconeQuotient] using coconeMap_snd (g := S.g) (g' := 𝟙 S.X₃) S.g (𝟙 S.X₃) (by simp) n

set_option backward.isDefEq.respectTransparency false in
private def coconeSequence (S : ShortComplex (compValue.{v} R)) :
    ShortComplex (compValue.{v} R) :=
  ShortComplex.mk (kernelToCocone S) (coconeQuotient S) (by
    ext n : 1
    apply cocone_degree_ext n
    · simpa only [comp_f, zero_f, Category.assoc, coconeQuotient_fst, kernelToCocone,
        mappingCocone.lift_f_fst_f_assoc, zero_comp] using congrArg (fun a ↦ a.f n) S.zero
    · simp only [comp_f, zero_f, Category.assoc, coconeQuotient_snd, kernelToCocone,
        mappingCocone.lift_f_snd_v, Cochain.zero_v, zero_comp])

set_option backward.isDefEq.respectTransparency false in
private theorem coconeSequence_exact (S : ShortComplex (compValue.{v} R)) (hS : S.ShortExact) :
    (coconeSequence S).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  let E := eval (ModuleCat.{v} R) (ComplexShape.up ℤ) n
  have hex := (shortExact_iff_degreewise_shortExact S).1 hS n
  let f := (kernelToCocone S).f n
  let p := (coconeQuotient S).f n
  let a := (mappingCocone.fst S.g).f n
  let b := (mappingCocone.snd S.g).v n (n + -1) rfl
  let a' := (mappingCocone.fst (𝟙 S.X₃)).f n
  let b' := (mappingCocone.snd (𝟙 S.X₃)).v n (n + -1) rfl
  have hf₁ (x) : a (f x) = S.f.f n x :=
    module_apply_eq (mappingCocone.lift_f_fst_f ..) x
  have hf₂ (x) : b (f x) = 0 := by
    change ((kernelToCocone S).f n ≫ b) x = 0
    rw [kernelToCocone, show b = (mappingCocone.snd S.g).v n (n + -1) rfl from rfl,
      mappingCocone.lift_f_snd_v, Cochain.zero_v]
    rfl
  have hp₁ (x) : a' (p x) = S.g.f n (a x) :=
    module_apply_eq (coconeQuotient_fst S n) x
  have hp₂ (x) : b' (p x) = b x :=
    module_apply_eq (coconeQuotient_snd S n) x
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    intro x
    change p x = 0 ↔ ∃ x₀, f x₀ = x
    constructor
    · intro hx
      have h₁ : S.g.f n (a x) = 0 := by simpa [hx, a'] using (hp₁ x).symm
      have h₂ : b x = 0 := by simpa [hx, b'] using (hp₂ x).symm
      obtain ⟨x₀, hx₀⟩ := ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S.map E)).1 hex.exact (a x)).1 h₁
      exact ⟨x₀, cocone_degree_ext_elem n ((hf₁ x₀).trans hx₀) ((hf₂ x₀).trans h₂.symm)⟩
    · rintro ⟨x₀, rfl⟩
      exact module_apply_eq (congrArg (fun a ↦ a.f n) (coconeSequence S).zero) x₀
  · change Mono f
    apply (ModuleCat.mono_iff_injective _).2
    intro x y h
    exact (ModuleCat.mono_iff_injective _).1 hex.mono_f
      ((hf₁ x).symm.trans ((congrArg a h).trans (hf₁ y)))
  · change Epi p
    apply (ModuleCat.epi_iff_surjective _).2
    intro y
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective _).1 hex.epi_g (a' y)
    let i := (mappingCocone.inl S.g).v n n (add_zero n)
    let j := (mappingCocone.inr S.g).1.v (n + -1) n (by omega)
    refine ⟨i x + j (b' y), cocone_degree_ext_elem n ?_ ?_⟩
    · rw [hp₁]
      have h : a (i x + j (b' y)) = x := by
        change a.hom (i x + j (b' y)) = x
        rw [map_add]
        change (i ≫ a) x + (j ≫ a) (b' y) = x
        rw [show i ≫ a = 𝟙 _ from mappingCocone.inl_v_fst_f _ _,
          show j ≫ a = 0 from mappingCocone.inr_v_fst_f _ _ _ _, ModuleCat.id_apply]
        exact add_zero _
      exact (congrArg (fun z ↦ S.g.f n z) h).trans hx
    · rw [hp₂]
      change b.hom (i x + j (b' y)) = b' y
      rw [map_add]
      change (i ≫ b) x + (j ≫ b) (b' y) = b' y
      rw [show i ≫ b = 0 from mappingCocone.inl_v_snd_v _ _ _ _,
        show j ≫ b = 𝟙 _ from mappingCocone.inr_v_snd_v _ _ _ _, ModuleCat.id_apply]
      exact zero_add _

private lemma identityCocone_zero (L : compValue.{v} R) (n : ℤ) :
    IsZero ((mappingCocone (𝟙 L)).homology n) := by
  let K := mappingCone (𝟙 L)
  apply IsZero.of_iso _ ((cohomologyShiftIso (R := R) (-1) n).app K)
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (K.homology (n + -1)) = 0
  rw [← homologyMap_id, (mappingCone.homotopyToZeroOfId L).homologyMap_eq, homologyMap_zero]

/-- The canonical map is a quasi-isomorphism for a tower with surjective transitions. -/
theorem comparison_quasiIso : comparisonQuasiIsoType.{u,v} := by
  intro R _ X h
  let S := towerShortComplex X
  let e := coconeSequence_exact S (towerShortComplex_shortExact R X h)
  change QuasiIso (coconeSequence S).f
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have z₀ := identityCocone_zero S.X₃ (n - 1)
  have z₁ := identityCocone_zero S.X₃ n
  have h₁ := e.homology_exact₁ (n - 1) n (ComplexShape.up_mk _ _ (sub_add_cancel n 1))
  have h₂ := e.homology_exact₂ n
  have hmono := h₁.mono_g (z₀.eq_of_src _ _)
  have hepi := h₂.epi_f (z₁.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end Comparison

section Replacement

open MorphismProperty

private def degreewiseSurjections : MorphismProperty (compValue.{v} R) :=
  fun _ _ f ↦ ∀ n : ℤ, Function.Surjective (f.f n)

private abbrev ReplacementFactorization (R : Type u) [Ring R] :=
  FunctorialFactorizationData (quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))
    (degreewiseSurjections (R := R))

private abbrev Stage (R : Type u) [Ring R] := Towers (compValue.{v} R) ⥤ compValue.{v} R

private def ev (n : ℕ) : Stage.{u,v} R :=
  (evaluation _ _).obj (op n)

private def step (n : ℕ) : ev.{u,v} (R := R) (n + 1) ⟶ ev n :=
  (evaluation _ _).map (homOfLE (Nat.le_add_right n 1)).op

/-- Factor the next transition followed by the preceding stage inclusion. -/
private def replacementStage (F : ReplacementFactorization.{u,v} R) :
    (n : ℕ) → Σ Y : Stage.{u,v} R, ev n ⟶ Y
  | 0 => ⟨ev 0, 𝟙 _⟩
  | n + 1 =>
    let a := step n ≫ (replacementStage F n).2
    let fac := (F.functorCategory (Towers (compValue.{v} R))).factorizationData a
    ⟨fac.Z, fac.i⟩

private def replacementStep (F : ReplacementFactorization.{u,v} R) (n : ℕ) :
    (replacementStage F (n + 1)).1 ⟶ (replacementStage F n).1 :=
  ((F.functorCategory _).factorizationData (step n ≫ (replacementStage F n).2)).p

private theorem replacementStep_fac (F : ReplacementFactorization.{u,v} R) (n : ℕ) :
    (replacementStage F (n + 1)).2 ≫ replacementStep F n =
      step n ≫ (replacementStage F n).2 :=
  ((F.functorCategory _).factorizationData _).fac

set_option backward.isDefEq.respectTransparency false in
private def replacement (F : ReplacementFactorization.{u,v} R) :
    Towers (compValue.{v} R) ⥤ Towers (compValue.{v} R) where
  obj X := Functor.ofOpSequence (X := fun n ↦ (replacementStage F n).1.obj X)
    (fun n ↦ (replacementStep F n).app X)
  map f := NatTrans.ofOpSequence (fun n ↦ (replacementStage F n).1.map f) (by
    intro n
    simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
      ((replacementStep F n).naturality f).symm)
  map_id X := by
    apply NatTrans.ext
    funext n
    exact (replacementStage F n.unop).1.map_id X
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (replacementStage F n.unop).1.map_comp f g

set_option backward.isDefEq.respectTransparency false in
private def replacementUnit (F : ReplacementFactorization.{u,v} R) : 𝟭 _ ⟶ replacement F where
  app X := NatTrans.ofOpSequence (fun n ↦ (replacementStage F n).2.app X) (by
    intro n
    change transition X n ≫ (replacementStage F n).2.app X =
      (replacementStage F (n + 1)).2.app X ≫
        (Functor.ofOpSequence (X := fun k ↦ (replacementStage F k).1.obj X)
          (fun k ↦ (replacementStep F k).app X)).map (homOfLE (Nat.le_add_right n 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (NatTrans.congr_app (replacementStep_fac F n) X).symm)
  naturality X Y f := by
    apply NatTrans.ext
    funext n
    exact (replacementStage F n.unop).2.naturality f

private lemma replacement_transition (F : ReplacementFactorization.{u,v} R)
    (X : Towers (compValue.{v} R)) (n : ℕ) :
    transition ((replacement F).obj X) n =
      F.p.app (Arrow.mk (transition X n ≫ ((replacementUnit F).app X).app (op n))) :=
  Functor.ofOpSequence_map_homOfLE_succ
    (X := fun k ↦ (replacementStage F k).1.obj X) (fun k ↦ (replacementStep F k).app X) n

private theorem replacement_stagewise (F : ReplacementFactorization.{u,v} R)
    (X : Towers (compValue.{v} R)) :
    stagewiseQuasiIso ((replacementUnit F).app X) := by
  intro n
  cases n with
  | zero =>
    change QuasiIso (𝟙 (X.obj (op 0)))
    infer_instance
  | succ n =>
    exact (mem_quasiIso_iff _).1 (F.hi (Arrow.mk
      (transition X n ≫ (replacementStage F n).2.app X)))

private theorem replacement_surjective (F : ReplacementFactorization.{u,v} R)
    (X : Towers (compValue.{v} R)) :
    surjectiveTransitions ((replacement F).obj X) := by
  intro n i
  rw [replacement_transition]
  exact F.hp _ i

private theorem replacement_limitMap_quasiIso (F : ReplacementFactorization.{u,v} R)
    {X Z : Towers (compValue.{v} R)} (f : X ⟶ Z) (hf : stagewiseQuasiIso f) :
    QuasiIso (limMap ((replacement F).map f)) := by
  apply towerLimitMap_quasiIso R _ _ _ (replacement_surjective F X) (replacement_surjective F Z)
  intro n
  let a := (replacementUnit F).app X |>.app (op n)
  let b := ((replacement F).map f).app (op n)
  have ha : QuasiIso a := replacement_stagewise F X n
  have hcomp : QuasiIso (a ≫ b) := by
    have eq := NatTrans.congr_app ((replacementUnit F).naturality f) (op n)
    change f.app (op n) ≫ ((replacementUnit F).app Z).app (op n) = a ≫ b at eq
    rw [← eq]
    have := hf n
    have := replacement_stagewise F Z n
    exact quasiIso_comp _ _
  exact quasiIso_of_comp_left a b

private theorem replacement_derivedIso (F : ReplacementFactorization.{u,v} R) :
    ∃ e : (replacement F ⋙ lim) ⋙ qValue.{v} R ≅ holimValue ⋙ qValue.{v} R,
      ∀ X, e.hom.app X ≫ (qValue.{v} R).map (holimValue.map ((replacementUnit F).app X)) =
        (qValue.{v} R).map (comparisonValue ((replacement F).obj X)) := by
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  let Y := replacement F
  let j := replacementUnit F
  let Q := qValue.{v} R
  have hQ (K L : compValue.{v} R) (f : K ⟶ L) (hf : QuasiIso f) : IsIso (Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) f).2 hf
  have hC (X : Towers (compValue.{v} R)) : IsIso (Q.map (comparisonValue (Y.obj X))) :=
    hQ _ _ _ (comparison_quasiIso _ (replacement_surjective F X))
  have hJ (X : Towers (compValue.{v} R)) : IsIso (Q.map (holimValue.map (j.app X))) :=
    hQ _ _ _ (holim_invariance _ (replacement_stagewise F X))
  let e₁ : (Y ⋙ lim) ⋙ Q ≅ (Y ⋙ holimValue) ⋙ Q :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ _ (hC X)) (by
      intro X Z f
      change Q.map (limMap (Y.map f)) ≫ Q.map (comparisonValue (Y.obj Z)) =
        Q.map (comparisonValue (Y.obj X)) ≫ Q.map (holimValue.map (Y.map f))
      rw [← Q.map_comp, ← Q.map_comp]
      exact congrArg Q.map (comparison_naturality (Y.map f)))
  let e₂ : holimValue ⋙ Q ≅ (Y ⋙ holimValue) ⋙ Q :=
    NatIso.ofComponents (fun X ↦ @asIso _ _ _ _ _ (hJ X)) (by
      intro X Z f
      change Q.map (holimValue.map f) ≫ Q.map (holimValue.map (j.app Z)) =
        Q.map (holimValue.map (j.app X)) ≫ Q.map (holimValue.map (Y.map f))
      rw [← Q.map_comp, ← Q.map_comp, ← holimValue.map_comp, ← holimValue.map_comp]
      exact congrArg (fun a ↦ Q.map (holimValue.map a)) (j.naturality f))
  refine ⟨e₁ ≪≫ e₂.symm, fun X ↦ ?_⟩
  change (e₁.hom.app X ≫ e₂.inv.app X) ≫ e₂.hom.app X = e₁.hom.app X
  rw [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The factorization at each successor stage produces a functorial replacement.
Its ordinary limit computes the shifted cone model up to a natural zigzag. -/
theorem replacement_exists : replacementType.{u} := by
  intro R _ F
  let F' : ReplacementFactorization.{u,u} R := F.ofLE inf_le_right le_rfl
  let Y := replacement F'
  let j := replacementUnit F'
  have hC (X : Towers (compValue.{u} R)) : QuasiIso (comparisonValue (Y.obj X)) :=
    comparison_quasiIso _ (replacement_surjective F' X)
  have hJ (X : Towers (compValue.{u} R)) : QuasiIso (holimValue.map (j.app X)) :=
    holim_invariance _ (replacement_stagewise F' X)
  refine ⟨Y, j, fun X ↦ ⟨replacement_stagewise F' X, replacement_surjective F' X⟩,
    ?_, ?_, fun f hf ↦ replacement_limitMap_quasiIso F' f hf, fun X ↦ ⟨hC X, hJ X⟩, ?_⟩
  · intro X
    exact ⟨Iso.refl _, Category.id_comp _⟩
  · intro X n
    refine ⟨Iso.refl _, Category.comp_id _, ?_⟩
    exact (replacement_transition F' X n).trans (Category.id_comp _).symm
  · obtain ⟨e, _⟩ := replacement_derivedIso F'
    exact ⟨e⟩

/-- Q12 supplies the functorial factorization for the replacement. -/
theorem projective_replacement_exists : projectiveReplacementType.{u} := by
  intro R _
  have h : Nonempty (ProjectiveFactorization R) :=
    (Model.Complexes.projectiveFibrationFactorization R).nonempty_functorialFactorizationData
  obtain ⟨F⟩ := h
  exact ⟨F, replacement_exists R F⟩

private def negIdentityCocone : compValue.{v} R ⥤ compValue.{v} R where
  obj Z := mappingCocone (-𝟙 Z)
  map f := coconeMap f f (by simp)
  map_id Z := by
    change (shiftFunctor (compValue.{v} R) (-1 : ℤ)).map
      (mappingCone.map (-𝟙 Z) (-𝟙 Z) (𝟙 Z) (𝟙 Z) _) = 𝟙 _
    rw [mappingCone.map_id]
    exact (shiftFunctor (compValue.{v} R) (-1 : ℤ)).map_id _
  map_comp {X Y Z} f g := by
    let S := shiftFunctor (compValue.{v} R) (-1 : ℤ)
    have h := mappingCone.map_comp (-𝟙 X) (-𝟙 Y) (-𝟙 Z) f f (by simp) g g (by simp)
    exact (congrArg S.map h).trans (S.map_comp _ _)

private lemma negIdentityCocone_fst_natural {Z W : compValue.{v} R} (f : Z ⟶ W) :
    (negIdentityCocone (R := R)).map f ≫ mappingCocone.fst (-𝟙 W) =
      mappingCocone.fst (-𝟙 Z) ≫ f := by
  ext n : 1
  exact coconeMap_fst f f (by simp) n

private lemma negIdentityCocone_zero (Z : compValue.{v} R) (q : ℤ) :
    IsZero (((negIdentityCocone (R := R)).obj Z).homology q) := by
  let e : mappingCone (-𝟙 Z) ≅ mappingCone (𝟙 Z) :=
    { hom := mappingCone.map _ _ (𝟙 Z) (-𝟙 Z) (by simp)
      inv := mappingCone.map _ _ (𝟙 Z) (-𝟙 Z) (by simp)
      hom_inv_id := by
        rw [← mappingCone.map_comp]
        simpa using mappingCone.map_id (-𝟙 Z)
      inv_hom_id := by
        rw [← mappingCone.map_comp]
        simpa using mappingCone.map_id (𝟙 Z) }
  exact IsZero.of_iso (identityCocone_zero Z q)
    ((cohomologyValue R q).mapIso ((shiftFunctor (compValue.{v} R) (-1 : ℤ)).mapIso e))

private lemma contractible_inclusion_quasiIso (X Z : compValue.{v} R) :
    QuasiIso (biprod.inl : X ⟶ X ⊞ (negIdentityCocone (R := R)).obj Z) := by
  let C := (negIdentityCocone (R := R)).obj Z
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine ⟨⟨homologyMap (biprod.fst : X ⊞ C ⟶ X) q, ?_, ?_⟩⟩
  · rw [← homologyMap_comp, biprod.inl_fst, homologyMap_id]
  · have hz : homologyMap (biprod.snd : X ⊞ C ⟶ C) q = 0 :=
      (negIdentityCocone_zero Z q).eq_of_tgt _ _
    calc
      _ = homologyMap ((biprod.fst : X ⊞ C ⟶ X) ≫ biprod.inl) q :=
        (homologyMap_comp _ _ _).symm
      _ = homologyMap (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : X ⊞ C ⟶ X ⊞ C) q := by
        rw [homologyMap_add, homologyMap_comp biprod.snd biprod.inr, hz, zero_comp, add_zero]
      _ = 𝟙 _ := by rw [biprod.total, homologyMap_id]

set_option backward.isDefEq.respectTransparency false in
private def contractibleFactorization : ReplacementFactorization.{u,v} R where
  Z :=
    { obj a := a.left ⊞ (negIdentityCocone (R := R)).obj a.right
      map f := biprod.map f.left ((negIdentityCocone (R := R)).map f.right)
      map_id a := by apply biprod.hom_ext <;> simp
      map_comp f g := by apply biprod.hom_ext <;> simp }
  i :=
    { app _ := biprod.inl
      naturality _ _ _ := by simp }
  p :=
    { app a := biprod.desc a.hom (mappingCocone.fst (-𝟙 a.right))
      naturality _ _ f := by
        apply biprod.hom_ext'
        · simp
        · simp [negIdentityCocone_fst_natural] }
  fac := by
    apply NatTrans.ext
    funext a
    exact biprod.inl_desc _ _
  hi a := contractible_inclusion_quasiIso a.left a.right
  hp a n := by
    let C := (negIdentityCocone (R := R)).obj a.right
    let p : a.left ⊞ C ⟶ a.right := biprod.desc a.hom (mappingCocone.fst (-𝟙 a.right))
    let s := (mappingCocone.inl (-𝟙 a.right)).v n n (add_zero n) ≫
      (biprod.inr : C ⟶ a.left ⊞ C).f n
    have hs : s ≫ p.f n = 𝟙 _ := by
      dsimp only [s]
      rw [Category.assoc, ← comp_f, show biprod.inr ≫ p = mappingCocone.fst (-𝟙 a.right) by
        exact biprod.inr_desc _ _, mappingCocone.inl_v_fst_f]
    intro y
    exact ⟨s y, (module_apply_eq hs y).trans (ModuleCat.id_apply _ y)⟩

/-- Adjoining a contractible summand at each successor gives a surjective tower in the
original module universe. Its limit represents the shifted cone by the canonical zigzag. -/
theorem contractible_replacement_exists : contractibleReplacementType.{u,v} := by
  intro R _
  let F := contractibleFactorization.{u,v} (R := R)
  refine ⟨replacement F, replacementUnit F,
    fun X ↦ ⟨replacement_stagewise F X, replacement_surjective F X⟩, ?_, ?_,
    fun f hf ↦ replacement_limitMap_quasiIso F f hf, replacement_derivedIso F⟩
  · intro X
    exact ⟨Iso.refl _, Category.id_comp _⟩
  · intro X n
    refine ⟨Iso.refl _, Category.comp_id _, ?_⟩
    exact (replacement_transition F X n).trans (Category.id_comp _).symm

end Replacement

section DerivedLimit

open MorphismProperty

/-- The levelwise quasi-isomorphisms of sequential towers. -/
def towerQuasiIsomorphisms : MorphismProperty (Towers (compValue.{v} R)) :=
  fun _ _ f ↦ stagewiseQuasiIso f

private instance : (towerQuasiIsomorphisms.{u,v} (R := R)).IsMultiplicative where
  id_mem X n := inferInstanceAs (QuasiIso (𝟙 (X.obj (op n))))
  comp_mem f g hf hg n := by
    have := hf n
    have := hg n
    exact quasiIso_comp (f.app (op n)) (g.app (op n))

private instance : (towerQuasiIsomorphisms.{u,v} (R := R)).HasTwoOutOfThreeProperty where
  of_precomp f g hf hfg n := by
    have := hf n
    have : QuasiIso (f.app (op n) ≫ g.app (op n)) := hfg n
    exact quasiIso_of_comp_left (f.app (op n)) (g.app (op n))
  of_postcomp f g hg hfg n := by
    have := hg n
    have : QuasiIso (f.app (op n) ≫ g.app (op n)) := hfg n
    exact quasiIso_of_comp_right (f.app (op n)) (g.app (op n))

/-- The canonical natural map from the ordinary limit to the cone model. -/
def comparisonNat : (lim : Towers (compValue.{v} R) ⥤ _) ⟶ holimValue where
  app := comparisonValue
  naturality _ _ f := comparison_naturality f

/-- The localized cone model is the right derived functor of inverse limit,
with unit given by the canonical comparison. -/
theorem holim_isRightDerivedLimit (R : Type u) [Ring R] :
    let W := towerQuasiIsomorphisms.{u,v} (R := R)
    ∃ (G : W.Localization ⥤ derivedValue.{v} R)
      (e : W.Q ⋙ G ≅ holimValue ⋙ qValue.{v} R),
      G.IsRightDerivedFunctor (Functor.whiskerRight comparisonNat (qValue.{v} R) ≫ e.inv) W := by
  let := HasDerivedCategory.standard (ModuleCat.{v} R)
  let W := towerQuasiIsomorphisms.{u,v} (R := R)
  let S : ObjectProperty (Towers (compValue.{v} R)) := surjectiveTransitions
  let Φ : LocalizerMorphism (W.inverseImage S.ι) W := LocalizerMorphism.ofEq (F := S.ι) rfl
  obtain ⟨Y, j, hY, _, _, _, _⟩ := contractible_replacement_exists.{u,v} R
  let ρ := S.lift Y (fun X ↦ (hY X).2)
  let i : 𝟭 _ ⟶ ρ ⋙ Φ.functor := j
  have hi (X) : W (i.app X) := (hY X).1
  have : Φ.functor.Full := inferInstanceAs S.ι.Full
  have : Φ.functor.Faithful := inferInstanceAs S.ι.Faithful
  have : Φ.IsRightDerivabilityStructure :=
    Φ.isRightDerivabilityStructure_of_functorial_resolutions i hi rfl
  let Q := qValue.{v} R
  let H := holimValue ⋙ Q
  have hH : W.IsInvertedBy H := by
    intro X Y f hf
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) _).2 (holim_invariance f hf)
  let G := Localization.lift H hH W.Q
  let e := Localization.fac H hH W.Q
  have hlim : Φ.Derives (lim ⋙ Q) := by
    intro X Y f hf
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) _).2
      (towerLimitMap_quasiIso R X.obj Y.obj f.hom X.property Y.property hf)
  refine ⟨G, e, hlim.isRightDerivedFunctor_of_isIso
    (Functor.whiskerRight comparisonNat Q ≫ e.inv) (fun X ↦ ?_)⟩
  have : IsIso (Q.map (comparisonValue X.obj)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{v} R) _).2
      (comparison_quasiIso X.obj X.property)
  change IsIso (Q.map (comparisonValue X.obj) ≫ e.inv.app X.obj)
  infer_instance

end DerivedLimit

section Milnor

private lemma moduleDifference_π (M : Towers (ModuleCat.{v} R)) (n : ℕ) :
    moduleDifference M ≫ Pi.π (fun k ↦ M.obj (op k)) n =
      Pi.π (fun k ↦ M.obj (op k)) n -
        Pi.π (fun k ↦ M.obj (op k)) (n + 1) ≫ M.map (homOfLE (Nat.le_add_right n 1)).op := by
  simp [moduleDifference, Preadditive.sub_comp]

private lemma moduleInclusion_condition (M : Towers (ModuleCat.{v} R)) :
    moduleInclusion M ≫ moduleDifference M = 0 := by
  apply Pi.hom_ext
  intro n
  simp [moduleDifference_π, Preadditive.comp_sub, limit.w]

private instance moduleInclusion_mono (M : Towers (ModuleCat.{v} R)) :
    Mono (moduleInclusion M) := by
  constructor
  intro Z a b h
  apply limit.hom_ext
  intro n
  have h' := congrArg (fun c ↦ c ≫ Pi.π (fun k : ℕ ↦ M.obj (op k)) n.unop) h
  simpa only [Category.assoc, Pi.lift_comp_π] using h'

private def moduleLimitIsKernel (M : Towers (ModuleCat.{v} R)) :
    IsLimit (KernelFork.ofι (moduleInclusion M) (moduleInclusion_condition M)) := by
  apply KernelFork.IsLimit.ofι'
  intro Z p hp
  let Q := fun n : ℕ ↦ Pi.π (fun k ↦ M.obj (op k)) n
  let c : Cone M :=
    { pt := Z
      π := NatTrans.ofOpSequence (fun n ↦ p ≫ Q n) (by
        intro n
        have h : p ≫ moduleDifference M ≫ Q n = 0 := by rw [← Category.assoc, hp, zero_comp]
        rw [moduleDifference_π, Preadditive.comp_sub, sub_eq_zero] at h
        simpa [Q] using h) }
  refine ⟨limit.lift M c, ?_⟩
  apply Pi.hom_ext
  intro n
  rw [Category.assoc]
  change limit.lift M c ≫ (Pi.lift (fun k : ℕ ↦ limit.π M (op k))) ≫ Q n = _
  rw [Pi.lift_comp_π, limit.lift_π]
  rfl

private lemma moduleInclusion_natural {M N : Towers (ModuleCat.{v} R)} (a : M ⟶ N) :
    limMap a ≫ moduleInclusion N = moduleInclusion M ≫ moduleProductMap a := by
  apply Pi.hom_ext
  intro n
  simp [Category.assoc]

private lemma productComparison_difference (X : Towers (compValue.{v} R)) (q : ℤ) :
    homologyMap (differenceValue X) q ≫ productComparison X q =
      productComparison X q ≫ moduleDifference (cohomologyTower X q) := by
  let H := cohomologyValue R q
  let a := fun n : ℕ ↦ X.obj (op n)
  let b := fun n : ℕ ↦ H.obj (a n)
  apply Pi.hom_ext
  intro n
  change (H.map (differenceValue X) ≫ piComparison H a) ≫ Pi.π b n =
    (piComparison H a ≫ moduleDifference (cohomologyTower X q)) ≫ Pi.π b n
  have hn := moduleDifference_π (cohomologyTower X q) n
  change moduleDifference (cohomologyTower X q) ≫ Pi.π b n =
    Pi.π b n - Pi.π b (n + 1) ≫ H.map (transition X n) at hn
  rw [Category.assoc, piComparison_comp_π, Category.assoc, hn,
    Preadditive.comp_sub, piComparison_comp_π, piComparison_comp_π_assoc, ← H.map_comp]
  change H.map (differenceValue X ≫ Pi.π a n) =
    H.map (Pi.π a n) - H.map (Pi.π a (n + 1)) ≫ H.map (transition X n)
  have : H.Additive := show (HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
    (ComplexShape.up ℤ) q).Additive from inferInstance
  rw [towerDifference_π, H.map_sub, H.map_comp]

private abbrev quotientFunctor := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)

private abbrev homotopyCohomology (q : ℤ) :=
  HomotopyCategory.homologyFunctor (ModuleCat.{v} R) (ComplexShape.up ℤ) q

private abbrev factor (q : ℤ) :=
  HomotopyCategory.homologyFunctorFactors (ModuleCat.{v} R) (ComplexShape.up ℤ) q

@[reassoc]
private lemma factor_map {K L : compValue.{v} R} (f : K ⟶ L) (q : ℤ) :
    (homotopyCohomology q).map ((quotientFunctor (R := R)).map f) ≫ (factor q).hom.app L =
      (factor q).hom.app K ≫ homologyMap f q :=
  (factor q).hom.naturality f

private lemma factor_inv_map {K L : compValue.{v} R} (f : K ⟶ L) (q : ℤ) :
    homologyMap f q ≫ (factor q).inv.app L =
      (factor q).inv.app K ≫ (homotopyCohomology q).map ((quotientFunctor (R := R)).map f) :=
  (factor q).inv.naturality f

set_option backward.isDefEq.respectTransparency false in
private lemma holimTriangle_distinguished (X : Towers (compValue.{v} R)) :
    holimTriangle X ∈ distTriang _ := by
  let Q := quotientFunctor (R := R)
  let T := mappingCocone.triangle (differenceValue X)
  change Q.mapTriangle.obj T ∈ distTriang _
  apply (rotate_distinguished_triangle _).2
  apply (distinguished_iff_of_iso ((Q.mapTriangleRotateIso.app T) ≪≫
    Q.mapTriangle.mapIso (mappingCocone.rotateTriangleIso (differenceValue X)))).2
  exact HomotopyCategory.mappingCone_triangleh_distinguished _

set_option backward.isDefEq.respectTransparency false in
private def holimTriangleMap {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) :
    holimTriangle X ⟶ holimTriangle Y := by
  let a := productMap f
  let m := mappingCone.triangleMap (differenceValue X) (differenceValue Y) a a
      (difference_natural f)
  let Q := quotientFunctor (R := R)
  apply Q.mapTriangle.map
  refine ⟨holimValue.map f, a, a, ?_, difference_natural f, ?_⟩
  · ext n : 1
    exact (coconeMap_fst a a (difference_natural f) n).symm
  · let e := shiftFunctorCompIsoId (compValue.{v} R) (-1 : ℤ) 1 (by decide)
    change (mappingCone.inr (differenceValue X) ≫ e.inv.app (mappingCone (differenceValue X))) ≫
      (shiftFunctor _ (1 : ℤ)).map ((shiftFunctor _ (-1 : ℤ)).map m.hom₃) =
        a ≫ mappingCone.inr (differenceValue Y) ≫ e.inv.app (mappingCone (differenceValue Y))
    have h := e.inv.naturality m.hom₃
    change m.hom₃ ≫ e.inv.app (mappingCone (differenceValue Y)) =
      e.inv.app (mappingCone (differenceValue X)) ≫
      (shiftFunctor _ (1 : ℤ)).map ((shiftFunctor _ (-1 : ℤ)).map m.hom₃) at h
    have hh : mappingCone.inr (differenceValue X) ≫ m.hom₃ =
        a ≫ mappingCone.inr (differenceValue Y) := m.comm₂
    calc
      _ = mappingCone.inr (differenceValue X) ≫
          (m.hom₃ ≫ e.inv.app (mappingCone (differenceValue Y))) :=
        (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h.symm)
      _ = _ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hh).trans (Category.assoc _ _ _))

set_option backward.isDefEq.respectTransparency false in
private lemma coneConnecting_natural {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) (q : ℤ) :
    homologyMap (productMap f) (q - 1) ≫ coneConnecting Y q =
      coneConnecting X q ≫ homologyMap (holimValue.map f) q := by
  let H := homotopyCohomology (R := R) 0
  have h := H.homologySequenceδ_naturality (holimTriangleMap f) (q - 1) q (sub_add_cancel q 1)
  change (homotopyCohomology (q - 1)).map ((quotientFunctor (R := R)).map (productMap f)) ≫
      H.homologySequenceδ (holimTriangle Y) (q - 1) q (sub_add_cancel q 1) =
    H.homologySequenceδ (holimTriangle X) (q - 1) q (sub_add_cancel q 1) ≫
      (homotopyCohomology q).map ((quotientFunctor (R := R)).map (holimValue.map f)) at h
  simp only [coneConnecting, Category.assoc]
  rw [← Category.assoc (homologyMap (productMap f) (q - 1)), factor_inv_map,
    Category.assoc, reassoc_of% h]
  erw [factor_map (holimValue.map f) q]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma coneProjection_natural {X Y : Towers (compValue.{v} R)} (f : X ⟶ Y) (q : ℤ) :
    homologyMap (holimValue.map f) q ≫ coneProjection Y q =
      coneProjection X q ≫ homologyMap (productMap f) q := by
  unfold coneProjection
  rw [← homologyMap_comp, ← homologyMap_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  exact coconeMap_fst _ _ (difference_natural f) n

private abbrev connecting (X : Towers (compValue.{v} R)) (q : ℤ) :=
  inv (productComparison X (q - 1)) ≫ coneConnecting X q

private abbrev projection (X : Towers (compValue.{v} R)) (q : ℤ) :=
  coneProjection X q ≫ productComparison X q

private lemma exact_of_conjugate {A B C A' B' C' : ModuleCat.{v} R}
    {a : A ⟶ B} {b : B ⟶ C} {a' : A' ⟶ B'} {b' : B' ⟶ C'}
    {w : a ≫ b = 0} (h : (ShortComplex.mk a b w).Exact)
    (e₁ : A ≅ A') (e₂ : B ≅ B') (e₃ : C ≅ C')
    (h₁ : a ≫ e₂.hom = e₁.hom ≫ a') (h₂ : b ≫ e₃.hom = e₂.hom ≫ b') :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk a' b' w').Exact := by
  have hw : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, ← h₁, Category.assoc, ← h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  exact ⟨hw, ShortComplex.exact_of_iso (ShortComplex.isoMk e₁ e₂ e₃ h₁.symm h₂.symm) h⟩

set_option backward.isDefEq.respectTransparency false in
private theorem coneCohomologyExact (X : Towers (compValue.{v} R)) (q : ℤ) :
    (∃ h, (ShortComplex.mk (moduleDifference (cohomologyTower X (q - 1))) (connecting X q) h).Exact) ∧
    (∃ h, (ShortComplex.mk (connecting X q) (projection X q) h).Exact) ∧
    (∃ h, (ShortComplex.mk (projection X q) (moduleDifference (cohomologyTower X q)) h).Exact) := by
  let H := homotopyCohomology (R := R) 0
  let T := holimTriangle X
  let v := sub_add_cancel q 1
  let P (i : ℤ) := (factor i).app (towerProduct X) ≪≫ asIso (productComparison X i)
  let E := (factor q).app (holimValue.obj X)
  have hT := holimTriangle_distinguished X
  have hd (i : ℤ) : (H.shift i).map T.mor₂ ≫ (P i).hom =
      (P i).hom ≫ moduleDifference (cohomologyTower X i) := by
    change (homotopyCohomology i).map (quotientFunctor.map (differenceValue X)) ≫
        ((factor i).hom.app _ ≫ productComparison X i) =
      ((factor i).hom.app _ ≫ productComparison X i) ≫ moduleDifference (cohomologyTower X i)
    simp only [factor_map_assoc, Category.assoc, productComparison_difference]
  have hc : H.homologySequenceδ T (q - 1) q v ≫ E.hom = (P (q - 1)).hom ≫ connecting X q := by
    simp [P, E, coneConnecting, T, H, Category.assoc]
    rfl
  have hp : (H.shift q).map T.mor₁ ≫ (P q).hom = E.hom ≫ projection X q := by
    exact factor_map_assoc (mappingCocone.fst (differenceValue X)) q (productComparison X q)
  exact ⟨exact_of_conjugate (H.homologySequence_exact₃ T hT (q - 1) q v) _ _ _ (hd _) hc,
    exact_of_conjugate (H.homologySequence_exact₁ T hT (q - 1) q v) _ _ _ hc hp,
    exact_of_conjugate (H.homologySequence_exact₂ T hT q) _ _ _ hp (hd _)⟩

private structure MilnorData (X : Towers (compValue.{v} R)) (q : ℤ) where
  f : limOne (cohomologyTower X (q - 1)) ⟶ (holimValue.obj X).homology q
  g : (holimValue.obj X).homology q ⟶ limit (cohomologyTower X q)
  zero : f ≫ g = 0
  shortExact : (ShortComplex.mk f g zero).ShortExact
  left_fac : productComparison X (q - 1) ≫ cokernel.π _ ≫ f = coneConnecting X q
  right_fac : g ≫ moduleInclusion _ = projection X q

set_option backward.isDefEq.respectTransparency false in
private def milnorData (X : Towers (compValue.{v} R)) (q : ℤ) : MilnorData X q := by
  let M := cohomologyTower X q
  let dPrev := moduleDifference (cohomologyTower X (q - 1))
  let dNow := moduleDifference M
  let c := connecting X q
  let p := projection X q
  let h := coneCohomologyExact X q
  let w₁ : dPrev ≫ c = 0 := h.1.choose
  let w₂ : c ≫ p = 0 := h.2.1.choose
  let w₃ : p ≫ dNow = 0 := h.2.2.choose
  have ex₁ : (ShortComplex.mk dPrev c w₁).Exact := h.1.choose_spec
  have ex₂ : (ShortComplex.mk c p w₂).Exact := h.2.1.choose_spec
  have ex₃ : (ShortComplex.mk p dNow w₃).Exact := h.2.2.choose_spec
  let f := cokernel.desc dPrev c w₁
  let G := KernelFork.IsLimit.lift' (moduleLimitIsKernel M) p w₃
  let g := G.val
  have hf : cokernel.π dPrev ≫ f = c := cokernel.π_desc _ _ _
  have hg : g ≫ moduleInclusion M = p := G.property
  have hfp : f ≫ p = 0 := by
    rw [← cancel_epi (cokernel.π dPrev), comp_zero, ← Category.assoc, hf, w₂]
  have hfg : f ≫ g = 0 := by
    rw [← cancel_mono (moduleInclusion M), Category.assoc, hg, zero_comp, hfp]
  let S := ShortComplex.mk f p hfp
  let S' := ShortComplex.mk f g hfg
  let α : ShortComplex.mk c p w₂ ⟶ S :=
    ShortComplex.homMk (cokernel.π dPrev) (𝟙 _) (𝟙 _) (by simpa [S] using hf)
      (by simp [S])
  let β : S' ⟶ S :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) (moduleInclusion M) (by simp [S, S'])
      (by simpa [S, S'] using hg.symm)
  have ex : S.Exact := by
    have : Epi α.τ₁ := show Epi (cokernel.π dPrev) from inferInstance
    have : IsIso α.τ₂ := show IsIso (𝟙 _) from inferInstance
    have : Mono α.τ₃ := show Mono (𝟙 _) from inferInstance
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).1 ex₂
  have ex' : S'.Exact := by
    have : Epi β.τ₁ := show Epi (𝟙 _) from inferInstance
    have : IsIso β.τ₂ := show IsIso (𝟙 _) from inferInstance
    have : Mono β.τ₃ := moduleInclusion_mono M
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono β).2 ex
  have mono_f : Mono f := ex₁.mono_cokernelDesc
  let e := (moduleLimitIsKernel M).conePointUniqueUpToIso (kernelIsKernel dNow)
  have he : e.hom ≫ kernel.ι dNow = moduleInclusion M :=
    (moduleLimitIsKernel M).conePointUniqueUpToIso_hom_comp (kernelIsKernel dNow) WalkingParallelPair.zero
  have eg : g ≫ e.hom = kernel.lift dNow p w₃ := by
    apply (cancel_mono (kernel.ι dNow)).1
    rw [Category.assoc, he, hg, kernel.lift_ι]
  have epi_lift : Epi (kernel.lift dNow p w₃) := ex₃.epi_kernelLift
  have epi_g : Epi g := by
    have h : kernel.lift dNow p w₃ ≫ e.inv = g := by rw [← eg, Category.assoc, e.hom_inv_id, Category.comp_id]
    rw [← h]
    infer_instance
  refine ⟨f, g, hfg, ShortComplex.ShortExact.mk' ex' mono_f epi_g, ?_, hg⟩
  change productComparison X (q - 1) ≫ cokernel.π dPrev ≫ f = _
  rw [hf]
  exact IsIso.hom_inv_id_assoc _ _

set_option backward.isDefEq.respectTransparency false in
/-- The natural Milnor short exact sequence, with its maps induced by the cone sequence. -/
theorem milnor_sequence : milnorSequenceType.{u,v} := by
  intro R _ q
  refine ⟨fun X ↦ (milnorData X q).f, fun X ↦ (milnorData X q).g,
    fun X ↦ (milnorData X q).zero, ?_, ?_⟩
  · intro X
    let M := milnorData X q
    exact ⟨M.shortExact, M.left_fac, M.right_fac⟩
  · intro X Y a
    let A := milnorData X q
    let B := milnorData Y q
    let a₁ := limOneMap (cohomologyTowerMap a (q - 1))
    let a₂ := homologyMap (holimValue.map a) q
    let a₃ := limMap (cohomologyTowerMap a q)
    have h₁ : a₁ ≫ B.f = A.f ≫ a₂ := by
      apply (cancel_epi (productComparison X (q - 1) ≫ cokernel.π
        (moduleDifference (cohomologyTower X (q - 1))))).1
      have hc : cokernel.π (moduleDifference (cohomologyTower X (q - 1))) ≫ a₁ =
          moduleProductMap (cohomologyTowerMap a (q - 1)) ≫
            cokernel.π (moduleDifference (cohomologyTower Y (q - 1))) :=
        cokernel.π_desc _ _ _
      simp only [Category.assoc, reassoc_of% hc]
      rw [← reassoc_of% (productComparison_natural a (q - 1)),
        reassoc_of% A.left_fac, B.left_fac]
      exact coneConnecting_natural a q
    have h₂ : a₂ ≫ B.g = A.g ≫ a₃ := by
      apply (cancel_mono (moduleInclusion (cohomologyTower Y q))).1
      simp only [Category.assoc, B.right_fac]
      unfold a₃
      rw [moduleInclusion_natural, ← Category.assoc A.g, A.right_fac]
      unfold projection
      rw [← Category.assoc, coneProjection_natural, Category.assoc,
        productComparison_natural, Category.assoc]
    exact ⟨h₁, h₂⟩

end Milnor

end

end DerivedFormalization.SequentialHomotopyLimits
