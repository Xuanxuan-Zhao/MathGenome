import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.ChainHomotopy
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.BifibrantHom
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.Projective

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomotopicalAlgebra

universe u w

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexChainHomotopy

variable {A : Type u} [Ring A]

abbrev cochainPathComplex : pathComplexType.{u} := pathComplexValue
abbrev cochainPathFirst : evaluationType.{u} := firstEvaluationValue
abbrev cochainPathSecond : evaluationType.{u} := secondEvaluationValue
abbrev cochainPathSection : sectionType.{u} := diagonalSectionValue

private theorem degreeCast_rfl (Y : Cochains A) (n : ℤ) (x : Y.X n) :
    degreeCast Y rfl x = x := by simp [degreeCast]

private theorem degreeCast_degreeCast (Y : Cochains A) {i j k : ℤ}
    (h : i = j) (h' : j = k) (x : Y.X i) :
    degreeCast Y h' (degreeCast Y h x) = degreeCast Y (h.trans h') x := by
  subst j
  subst k
  simp [degreeCast]

private theorem degreeCast_sub (Y : Cochains A) {i j : ℤ} (h : i = j) (x y : Y.X i) :
    degreeCast Y h (x - y) = degreeCast Y h x - degreeCast Y h y :=
  map_sub (degreeCast Y h).hom x y

private theorem degreeCast_add (Y : Cochains A) {i j : ℤ} (h : i = j) (x y : Y.X i) :
    degreeCast Y h (x + y) = degreeCast Y h x + degreeCast Y h y :=
  map_add (degreeCast Y h).hom x y

private theorem componentComm {X Y : Cochains A} (f : X ⟶ Y) (i j : ℤ) (x : X.X i) :
    Y.d i j (f.f i x) = f.f j (X.d i j x) :=
  ConcreteCategory.congr_hom (f.comm i j) x

private def pathCoordinates {X Y : Cochains A} (f g : X ⟶ Y)
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)) (n : ℤ) : X.X n ⟶ PathTerm Y n :=
  ModuleCat.ofHom ((f.f n).hom.prod ((g.f n).hom.prod (h n).hom))

private theorem pathCoordinates_comm {X Y : Cochains A} (f g : X ⟶ Y)
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)) (n : ℤ) :
    pathCoordinates f g h n ≫ (cochainPathComplex Y).d n (n + 1) =
      X.d n (n + 1) ≫ pathCoordinates f g h (n + 1) ↔
    ∀ x : X.X n, g.f n x - f.f n x =
      Y.d (n - 1) n (h n x) +
        degreeCast Y (by omega : (n + 1) - 1 = n) (h (n + 1) (X.d n (n + 1) x)) := by
  rw [pathComplex_d]
  constructor
  · intro hc x
    have hh := ConcreteCategory.congr_hom hc x
    change pathStep Y n (f.f n x, g.f n x, h n x) =
      (f.f (n + 1) (X.d n (n + 1) x), g.f (n + 1) (X.d n (n + 1) x),
        h (n + 1) (X.d n (n + 1) x)) at hh
    rw [pathStep_apply Y n] at hh
    have hh' := congrArg (fun t : PathTerm Y (n + 1) =>
      degreeCast Y (by omega : (n + 1) - 1 = n) t.2.2) hh
    dsimp only at hh'
    rw [degreeCast_sub, degreeCast_degreeCast, degreeCast_rfl, degreeCast_d] at hh'
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hh'
  · intro hc
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change pathStep Y n (f.f n x, g.f n x, h n x) =
      (f.f (n + 1) (X.d n (n + 1) x), g.f (n + 1) (X.d n (n + 1) x),
        h (n + 1) (X.d n (n + 1) x))
    rw [pathStep_apply Y n, componentComm f, componentComm g]
    have hh := congrArg (fun t : Y.X n => degreeCast Y (by omega : n = (n + 1) - 1) t) (hc x)
    dsimp only at hh
    rw [degreeCast_add, degreeCast_d, degreeCast_degreeCast, degreeCast_rfl] at hh
    rw [hh, add_sub_cancel_left]

/-- A map with the prescribed three coordinates exists exactly when the cochain homotopy
equation holds. -/
theorem cochainPath_lift_iff : pathLiftType.{u} := by
  intro A _ X Y f g h
  constructor
  · intro hh
    exact ⟨CochainComplex.ofHom (pathCoordinates f g h)
      (fun n => (pathCoordinates_comm f g h n).mpr (hh n)), fun _ _ => rfl⟩
  · rintro ⟨K, hK⟩ n
    apply (pathCoordinates_comm f g h n).mp
    have hKn (i : ℤ) : K.f i = pathCoordinates f g h i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hK i
    simpa only [← hKn] using (K.comm n (n + 1))

private def extendHomotopy {X Y : Cochains A} (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1))
    (i j : ℤ) : X.X i ⟶ Y.X j :=
  if e : i - 1 = j then h i ≫ degreeCast Y e else 0

private theorem extendHomotopy_zero {X Y : Cochains A}
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)) (i j : ℤ)
    (hn : ¬ (ComplexShape.up ℤ).Rel j i) : extendHomotopy h i j = 0 := by
  simp only [ComplexShape.up_Rel] at hn
  rw [extendHomotopy, dite_eq_right (by omega)]

private theorem extendHomotopy_apply {X Y : Cochains A}
    (h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1)) {i j : ℤ}
    (e : i - 1 = j) (x : X.X i) :
    extendHomotopy h i j x = degreeCast Y e (h i x) := by
  rw [extendHomotopy, dite_eq_left e]
  rfl

private theorem cochainHomotopy_iff_equation {X Y : Cochains A} (f g : X ⟶ Y) :
    Nonempty (Homotopy f g) ↔
      ∃ h : ∀ n : ℤ, X.X n ⟶ Y.X (n - 1), HomotopyEquation f g h := by
  have hn (n : ℤ) : (ComplexShape.up ℤ).Rel n (n + 1) := rfl
  have hp (n : ℤ) : (ComplexShape.up ℤ).Rel (n - 1) n := by
    simp [ComplexShape.up_Rel]
  constructor
  · rintro ⟨H⟩
    let H' := H.symm
    refine ⟨fun n => H'.hom n (n - 1), fun n x => ?_⟩
    have hh := H'.comm n
    rw [dNext_eq _ (hn n), prevD_eq _ (hp n)] at hh
    have hh' := ConcreteCategory.congr_hom hh x
    change g.f n x = H'.hom (n + 1) n (X.d n (n + 1) x) +
      Y.d (n - 1) n (H'.hom n (n - 1) x) + f.f n x at hh'
    rw [sub_eq_iff_eq_add, hh', add_comm (H'.hom (n + 1) n (X.d n (n + 1) x))]
    have he : ∀ j (e : (n + 1) - 1 = j),
        degreeCast Y e (H'.hom (n + 1) ((n + 1) - 1) (X.d n (n + 1) x)) =
          H'.hom (n + 1) j (X.d n (n + 1) x) := by
      intro j e
      subst j
      apply degreeCast_rfl
    rw [he]
  · rintro ⟨h, hh⟩
    refine ⟨Homotopy.symm ({
      hom := extendHomotopy h
      zero := extendHomotopy_zero h
      comm := fun n => ?_ } : Homotopy g f)⟩
    rw [dNext_eq _ (hn n), prevD_eq _ (hp n)]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change g.f n x = extendHomotopy h (n + 1) n (X.d n (n + 1) x) +
      Y.d (n - 1) n (extendHomotopy h n (n - 1) x) + f.f n x
    rw [extendHomotopy_apply h (by omega : (n + 1) - 1 = n),
      extendHomotopy_apply h rfl, degreeCast_rfl, add_comm _ (Y.d (n - 1) n (h n x))]
    exact sub_eq_iff_eq_add.mp (hh n x)

/-- Ordinary cochain homotopies are exactly the pairs admitting a lift to the explicit path. -/
theorem cochainHomotopy_iff_path : pathHomotopyType.{u} := by
  intro A _ X Y f g
  rw [cochainHomotopy_iff_equation]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨K, hK⟩ := (cochainPath_lift_iff f g h).mp hh
    refine ⟨K, ?_, ?_⟩
    · apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun t : PathTerm Y n => t.1) (hK n x)
    · apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun t : PathTerm Y n => t.2.1) (hK n x)
  · rintro ⟨K, h₀, h₁⟩
    let h (n : ℤ) : X.X n ⟶ Y.X (n - 1) :=
      ModuleCat.ofHom ((LinearMap.snd _ _ _).comp ((LinearMap.snd _ _ _).comp (K.f n).hom))
    refine ⟨h, (cochainPath_lift_iff f g h).mpr ⟨K, fun n x => ?_⟩⟩
    have h₀n := ConcreteCategory.congr_hom (congrArg (fun k : X ⟶ Y => k.f n) h₀) x
    have h₁n := ConcreteCategory.congr_hom (congrArg (fun k : X ⟶ Y => k.f n) h₁) x
    exact Prod.ext h₀n (Prod.ext h₁n rfl)

private theorem pathSection_first (Y : Cochains A) :
    cochainPathSection Y ≫ cochainPathFirst Y = 𝟙 Y := rfl

private theorem pathSection_second (Y : Cochains A) :
    cochainPathSection Y ≫ cochainPathSecond Y = 𝟙 Y := rfl

private theorem pathD_apply (Y : Cochains A) {i j : ℤ} (r : i + 1 = j)
    (x : PathTerm Y i) :
    (cochainPathComplex Y).d i j x =
      ((Y.d i j x.1, Y.d i j x.2.1,
        degreeCast Y (by omega : i = j - 1) (x.2.1 - x.1) -
          Y.d (i - 1) (j - 1) x.2.2) : PathTerm Y j) := by
  subst j
  rw [pathComplex_d]
  exact pathStep_apply Y i x

private def pathContractionComponent (Y : Cochains A) (n : ℤ) :
    (cochainPathComplex Y).X n ⟶ (cochainPathComplex Y).X (n - 1) :=
  ModuleCat.ofHom ((0 : _ →ₗ[A] _).prod (((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)).prod 0))

private theorem pathContraction_apply (Y : Cochains A) {i j : ℤ} (e : i - 1 = j)
    (x : PathTerm Y i) :
    extendHomotopy (pathContractionComponent Y) i j x =
      ((0, degreeCast Y e x.2.2, 0) : PathTerm Y j) := by
  subst j
  rw [extendHomotopy_apply _ rfl, degreeCast_rfl, degreeCast_rfl]
  rfl

/-- The homotopy `(y₀,y₁,b) ↦ (0,b,0)` extends the contraction of the first kernel. -/
private def pathContraction (Y : Cochains A) :
    Homotopy (𝟙 (cochainPathComplex Y)) (cochainPathFirst Y ≫ cochainPathSection Y) where
  hom := extendHomotopy (pathContractionComponent Y)
  zero := extendHomotopy_zero _
  comm n := by
    have hn : (ComplexShape.up ℤ).Rel n (n + 1) := rfl
    have hp : (ComplexShape.up ℤ).Rel (n - 1) n := by simp [ComplexShape.up_Rel]
    rw [dNext_eq _ hn, prevD_eq _ hp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = extendHomotopy (pathContractionComponent Y) (n + 1) n
      ((cochainPathComplex Y).d n (n + 1) x) +
      (cochainPathComplex Y).d (n - 1) n
        (extendHomotopy (pathContractionComponent Y) n (n - 1) x) +
      ((x.1, x.1, 0) : PathTerm Y n)
    rw [pathD_apply Y rfl, pathContraction_apply Y (by omega : (n + 1) - 1 = n),
      pathContraction_apply Y rfl, pathD_apply Y (by omega : n - 1 + 1 = n)]
    rcases x with ⟨a, b, c⟩
    dsimp only
    simp only [degreeCast_rfl, degreeCast_sub, degreeCast_degreeCast, degreeCast_d,
      Prod.mk_add_mk, zero_add, sub_zero, add_zero, map_zero]
    rw [sub_add_cancel, sub_add_cancel]

/-- The first evaluation has contractible kernel. -/
theorem cochainPathFirst_contractibleKernel : contractibleKernelType.{u} := by
  intro A _ Y
  let e := cochainPathFirst Y
  let s := cochainPathSection Y
  let j := kernel.ι e
  have hk : (𝟙 (cochainPathComplex Y) - e ≫ s) ≫ e = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, pathSection_first,
      Category.comp_id, sub_self]
  let p := kernel.lift e (𝟙 (cochainPathComplex Y) - e ≫ s) hk
  have hjp : j ≫ p = 𝟙 (kernel e) := by
    rw [← cancel_mono (kernel.ι e), Category.assoc, kernel.lift_ι, Category.id_comp]
    simp [j, Preadditive.comp_sub]
  have h := ((pathContraction Y).compLeft j).compRight p
  have hj : j ≫ cochainPathFirst Y = 0 := kernel.condition e
  have hzero : (j ≫ (cochainPathFirst Y ≫ cochainPathSection Y)) ≫ p = 0 := by
    rw [← Category.assoc, hj, zero_comp, zero_comp]
  refine ⟨?_⟩
  simpa only [Category.comp_id, hjp, hzero] using h

private theorem pathSection_quasiIso (Y : Cochains A) : QuasiIso (cochainPathSection Y) := by
  let e : HomotopyEquiv Y (cochainPathComplex Y) :=
    { hom := cochainPathSection Y
      inv := cochainPathFirst Y
      homotopyHomInvId := Homotopy.ofEq (pathSection_first Y)
      homotopyInvHomId := (pathContraction Y).symm }
  exact e.quasiIso_hom

private theorem pathEvaluations_surjective (Y : Cochains A) (n : ℤ) :
    Function.Surjective ((prod.lift (cochainPathFirst Y) (cochainPathSecond Y)).f n) := by
  let F := eval (ModuleCat A) (ComplexShape.up ℤ) n
  let s : (Y ⨯ Y).X n ⟶ PathTerm Y n :=
    ModuleCat.ofHom (((prod.fst : Y ⨯ Y ⟶ Y).f n).hom.prod
      (((prod.snd : Y ⨯ Y ⟶ Y).f n).hom.prod 0))
  have hs : s ≫ (prod.lift (cochainPathFirst Y) (cochainPathSecond Y)).f n = 𝟙 _ := by
    apply (cancel_mono (prodComparison F Y Y)).mp
    apply prod.hom_ext
    · simp only [Category.assoc, prodComparison_fst, Category.id_comp]
      change s ≫ ((prod.lift (cochainPathFirst Y) (cochainPathSecond Y) ≫ prod.fst).f n) = _
      rw [prod.lift_fst]
      rfl
    · simp only [Category.assoc, prodComparison_snd, Category.id_comp]
      change s ≫ ((prod.lift (cochainPathFirst Y) (cochainPathSecond Y) ≫ prod.snd).f n) = _
      rw [prod.lift_snd]
      rfl
  intro z
  exact ⟨s z, ConcreteCategory.congr_hom hs z⟩

/-- The explicit section and evaluations form a path object in the projective model. -/
theorem cochainPath_projective : projectivePathType.{u} := by
  intro A _ M
  let model := M.model
  intro Y
  refine ⟨?_, ?_, ?_⟩
  · apply prod.hom_ext <;> simp [diag, pathSection_first, pathSection_second]
  · rw [M.weakEquivalences_eq, mem_quasiIso_iff]
    exact pathSection_quasiIso Y
  · rw [M.fibrations_eq]
    exact pathEvaluations_surjective Y

noncomputable abbrev cochainHomotopyToDerivedHom : comparisonType.{u, w} := comparisonValue

theorem cochainHomotopyToDerivedHom_map [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {X Y : Cochains A} (f : X ⟶ Y) :
    cochainHomotopyToDerivedHom ((cochainQuotient A).map f) = DerivedCategory.Q.map f := by
  change comparisonValue ((cochainQuotient A).map f) = _
  unfold comparisonValue
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

theorem cochainHomotopyToDerivedHom_natural : comparisonNaturalType.{u, w} := by
  intro A _ _ X' X Y Y' k l f
  obtain ⟨g, rfl⟩ := (cochainQuotient A).map_surjective f
  rw [← (cochainQuotient A).map_comp, ← (cochainQuotient A).map_comp]
  change cochainHomotopyToDerivedHom ((cochainQuotient A).map (k ≫ g ≫ l)) =
    DerivedCategory.Q.map k ≫ cochainHomotopyToDerivedHom ((cochainQuotient A).map g) ≫
      DerivedCategory.Q.map l
  rw [cochainHomotopyToDerivedHom_map, cochainHomotopyToDerivedHom_map]
  simp only [Functor.map_comp]

private theorem cochainHomotopy_iff_leftHomotopic (M : ProjectiveModel A) :
    letI := M.model
    ∀ {X Y : Cochains A} [IsCofibrant X] (f g : X ⟶ Y),
      Nonempty (Homotopy f g) ↔ Model.LeftHomotopic f g := by
  let model := M.model
  intro X Y _ f g
  have := projectiveAllFibrant A M Y
  obtain ⟨_, hw, hf⟩ := cochainPath_projective M Y
  let P : HomotopicalAlgebra.PathObject Y :=
    { P := cochainPathComplex Y
      p₀ := cochainPathFirst Y
      p₁ := cochainPathSecond Y
      ι := cochainPathSection Y
      ι_p₀ := pathSection_first Y
      ι_p₁ := pathSection_second Y
      weakEquivalence_ι := (weakEquivalence_iff _).mpr hw }
  have hP : P.IsGood := ⟨(fibration_iff _).mpr hf⟩
  exact (cochainHomotopy_iff_path f g).trans
    ((Model.rightHomotopic_iff_exists_into_pathObject ⟨P, hP⟩ f g).symm.trans
      (Model.leftHomotopic_iff_rightHomotopic f g).symm)

/-- For a projectively cofibrant source and any target, the canonical map from ordinary
cochain homotopy classes to the derived Hom set is a bijection. -/
theorem cochainHomotopyToDerivedHom_bijective : comparisonBijectiveType.{u, w} := by
  intro A _ M _
  let model := M.model
  intro X Y _
  have := projectiveAllFibrant A M Y
  have : (DerivedCategory.Q (C := ModuleCat A)).IsLocalization
      (weakEquivalences (Cochains A)) := by
    rw [M.weakEquivalences_eq]
    infer_instance
  let L := DerivedCategory.Q (C := ModuleCat A)
  have hb := Model.homotopyClassToLocalizationHom_bijective L X Y
  constructor
  · intro f g hfg
    obtain ⟨f', rfl⟩ := (cochainQuotient A).map_surjective f
    obtain ⟨g', rfl⟩ := (cochainQuotient A).map_surjective g
    have hq : L.map f' = L.map g' := by
      simpa only [cochainHomotopyToDerivedHom_map f', cochainHomotopyToDerivedHom_map g'] using hfg
    have hm : LeftHomotopyClass.mk f' = LeftHomotopyClass.mk g' :=
      hb.1 (by simpa only [Model.homotopyClassToLocalizationHom_mk] using hq)
    obtain ⟨H⟩ := (cochainHomotopy_iff_leftHomotopic M f' g').mpr
      ((Model.leftHomotopyClass_mk_eq_iff f' g').mp hm)
    exact HomotopyCategory.eq_of_homotopy f' g' H
  · intro q
    obtain ⟨f, hf⟩ := hb.2 q
    obtain ⟨f', rfl⟩ := f.mk_surjective
    exact ⟨(cochainQuotient A).map f', (cochainHomotopyToDerivedHom_map f').trans
      ((Model.homotopyClassToLocalizationHom_mk L f').symm.trans hf)⟩

end DerivedFormalization.Model.Complexes
