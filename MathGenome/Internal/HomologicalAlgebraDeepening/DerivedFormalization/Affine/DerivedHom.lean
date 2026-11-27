import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Affine.NonpositiveAlgebras
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedHom

open CategoryTheory CochainComplex.HomComplex

universe u v t

namespace DerivedFormalization.Affine

namespace DerivedHom

open _root_.Specs.DerivedFormalization.Affine.DerivedHom
open _root_.Specs.DerivedFormalization.DG.HomComplex (compose component ofStrict)
open RightDGModule (GradedHom homComplex differentialFormula compositionFormula)

variable {k : Type u} [Field k] [CharZero k] {A : CommDGAlgebra.{u,v} k}

abbrev internalHom : InternalHomType.{u,v} :=
  @_root_.Specs.DerivedFormalization.Affine.DerivedHom.internalHom

abbrev liftAlgebra : LiftAlgebraType.{u,v,t} :=
  @_root_.Specs.DerivedFormalization.Affine.DerivedHom.liftAlgebra

variable {L M N P : Mod A}

private theorem graded_ext {r : ℤ} {f g : GradedHom M N r}
    (h : ∀ i q (e : i+r = q) (x : (M.complex ()).X i),
      f.app () i q e x = g.app () i q e x) : f = g := by
  apply GradedHom.ext
  intro a i q e
  cases a
  exact ModuleCat.hom_ext (LinearMap.ext (h i q e))

theorem scalarFormula : ScalarFormula.{u,v} := by
  intro k _ _ A M N r j n e f z i q ir h er x
  change GradedHom.app (compose M M N r j n e f (scalarOperator M j z)) () i q h x = _
  rw [compositionFormula r j n e f (scalarOperator M j z) () i (i+j) q rfl (by omega)]
  rw [scalarOperator_apply, map_zsmul_unit]
  exact congrArg ((i*j).negOnePow • ·) (GradedHom.comm_act f i j (i+j) ir q rfl er (by omega) x z)

private theorem compose_apply {s r n : ℤ} (h : s+r = n) (g : GradedHom N P s)
    (f : GradedHom M N r) (i j q : ℤ) (e : i+r = j) (e' : j+s = q)
    (x : (M.complex ()).X i) :
    GradedHom.app (compose M N P s r n h g f) () i q (by omega) x =
      g.app () j q e' (f.app () i j e x) :=
  compositionFormula s r n h g f () i j q e e' x

private theorem graded_smul_apply {r : ℤ} (c : ℤˣ) (f : GradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (M.complex ()).X i) :
    GradedHom.app (c • f) () i q e x = c • f.app () i q e x := by
  change (c • f.val ()).v i q e x = _
  rw [Cochain.units_smul_v]
  rfl

/-- Postcompose with a homogeneous right-linear map. -/
def postGraded (M : Mod A) {s : ℤ} (g : GradedHom N P s) :
    GradedHom (internalHom M N) (internalHom M P) s :=
  GradedHom.mk (fun _ r q h =>
    ModuleCat.ofHom (compose M N P s r q (by omega) g)) (by
    intro a b r j n rs ns e er en f z
    cases a
    cases b
    change compose M N P s n ns _ g ((internalHom M N).act r j n e f z) =
      (internalHom M P).act rs j ns _ (compose M N P s r rs _ g f) z
    apply graded_ext
    intro i q h x
    rw [compose_apply _ g _ i (i+n) q rfl (by omega) x,
      scalarFormula M N r j n e f z i (i+n) (i+r) rfl rfl x, map_zsmul_unit,
      scalarFormula M P rs j ns _ _ z i q (i+rs) h rfl x,
      compose_apply _ g f i (i+r) (i+rs) rfl (by omega) x]
    exact congrArg ((i*j).negOnePow • ·) (g.comm_act (i+r) j (i+n) (i+rs) q
      (by omega) (by omega) (by omega) _ z))

/-- Precompose with a homogeneous right-linear map, using the Koszul sign. -/
def preGraded (N : Mod A) {s : ℤ} (g : GradedHom L M s) :
    GradedHom (internalHom M N) (internalHom L N) s :=
  GradedHom.mk (fun _ r q h =>
    ModuleCat.ofHom (((r*s).negOnePow •
      (compose L M N r s q (by omega)).flip g))) (by
    intro a b r j n rs ns e er en f z
    cases a
    cases b
    change (n*s).negOnePow • compose L M N n s ns _ ((internalHom M N).act r j n e f z) g =
      (internalHom L N).act rs j ns _ ((r*s).negOnePow • compose L M N r s rs _ f g) z
    apply graded_ext
    intro i q h x
    rw [graded_smul_apply,
      compose_apply _ _ g i (i+s) q rfl (by omega) x,
      scalarFormula M N r j n e f z (i+s) q (i+s+r) (by omega) rfl,
      scalarFormula L N rs j ns _ _ z i q (i+s+r) h (by omega) x,
      graded_smul_apply, compose_apply _ f g i (i+s) (i+s+r) rfl (by omega) x]
    rw [show N.act (i+s+r) j q (by omega)
        ((r*s).negOnePow • GradedHom.app f () (i+s) (i+s+r) rfl
          (g.app () i (i+s) rfl x)) z =
        (r*s).negOnePow • N.act (i+s+r) j q (by omega)
          (GradedHom.app f () (i+s) (i+s+r) rfl (g.app () i (i+s) rfl x)) z from
      map_zsmul_unit ((N.act (i+s+r) j q (by omega)).flip z) _ _]
    rw [smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add]
    have hs : n*s+(i+s)*j = i*j+r*s+2*(j*s) := by rw [← e]; ring
    rw [hs, Int.negOnePow_add, Int.negOnePow_two_mul, mul_one])

private theorem postGraded_apply (M : Mod A) {s : ℤ} (g : GradedHom N P s)
    (r q : ℤ) (e : r+s = q) (f : GradedHom M N r) :
    (postGraded M g).app () r q e f = compose M N P s r q (by omega) g f := rfl

private theorem preGraded_apply (N : Mod A) {s : ℤ} (g : GradedHom L M s)
    (r q : ℤ) (e : r+s = q) (f : GradedHom M N r) :
    (preGraded N g).app () r q e f =
      (r*s).negOnePow • compose L M N r s q (by omega) f g := rfl

private theorem compose_d {s r n q : ℤ} (h : s+r = n) (e : n+1 = q)
    (g : GradedHom N P s) (f : GradedHom M N r) :
    (homComplex M P).d n q (compose M N P s r n h g f) =
      compose M N P (s+1) r q (by omega) ((homComplex N P).d s (s+1) g) f +
      s.negOnePow • compose M N P s (r+1) q (by omega) g ((homComplex M N).d r (r+1) f) := by
  subst e
  exact (RightDGModule.dgCategory (algebraCategory A)).toData.leibniz s r n h g f

theorem postGraded_d (M : Mod A) {s : ℤ} (g : GradedHom N P s) :
    (homComplex (internalHom M N) (internalHom M P)).d s (s+1) (postGraded M g) =
      postGraded M ((homComplex N P).d s (s+1) g) := by
  apply graded_ext
  intro r q e f
  rw [differentialFormula, postGraded_apply, postGraded_apply, postGraded_apply]
  change (homComplex M P).d (r+s) q (compose M N P s r (r+s) _ g f) -
    s.negOnePow • compose M N P s (r+1) q _ g ((homComplex M N).d r (r+1) f) = _
  rw [compose_d (by omega) (by omega)]
  abel

theorem preGraded_d (N : Mod A) {s : ℤ} (g : GradedHom L M s) :
    (homComplex (internalHom M N) (internalHom L N)).d s (s+1) (preGraded N g) =
      preGraded N ((homComplex L M).d s (s+1) g) := by
  apply graded_ext
  intro r q e f
  rw [differentialFormula, preGraded_apply, preGraded_apply, preGraded_apply]
  change (homComplex L N).d (r+s) q ((r*s).negOnePow • compose L M N r s (r+s) _ f g) -
    s.negOnePow • (((r+1)*s).negOnePow •
      compose L M N (r+1) s q _ ((homComplex M N).d r (r+1) f) g) = _
  rw [map_zsmul_unit, compose_d (by omega) (by omega)]
  simp only [smul_add, smul_smul, mul_add, add_mul, one_mul, mul_one, Int.negOnePow_add]
  rw [show s.negOnePow * ((r*s).negOnePow * s.negOnePow) = (r*s).negOnePow by
    rw [mul_comm (r*s).negOnePow s.negOnePow, ← mul_assoc, Int.units_mul_self, one_mul]]
  abel

/-- Postcomposition with a strict map gives a strict map of internal Homs. -/
def post (M : Mod A) (g : N ⟶ P) : internalHom M N ⟶ internalHom M P :=
  RightDGModule.strictMap ⟨postGraded M (ofStrict g), by
    change (homComplex (internalHom M N) (internalHom M P)).d 0 1
      (postGraded M (ofStrict g)) = 0
    have hg : (homComplex N P).d 0 1 (ofStrict g) = 0 :=
      (RightDGModule.strictCycle g).property
    rw [postGraded_d, hg]
    apply graded_ext
    intro r q e f
    rw [postGraded_apply, map_zero, LinearMap.zero_apply]
    rfl⟩

/-- Precomposition with a strict map gives a strict map of internal Homs. -/
def pre (N : Mod A) (g : L ⟶ M) : internalHom M N ⟶ internalHom L N :=
  RightDGModule.strictMap ⟨preGraded N (ofStrict g), by
    change (homComplex (internalHom M N) (internalHom L N)).d 0 1
      (preGraded N (ofStrict g)) = 0
    have hg : (homComplex L M).d 0 1 (ofStrict g) = 0 :=
      (RightDGModule.strictCycle g).property
    rw [preGraded_d, hg]
    apply graded_ext
    intro r q e f
    rw [preGraded_apply, map_zero, smul_zero]
    rfl⟩

theorem post_apply (M : Mod A) (g : N ⟶ P) {r : ℤ} (f : GradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (M.complex ()).X i) :
    GradedHom.app (((post M g).app ()).f r f) () i q e x =
      (g.app ()).f q (f.app () i q e x) := by
  change GradedHom.app (compose M N P 0 r r (zero_add r) (ofStrict g) f) () i q e x = _
  rw [compose_apply _ (ofStrict g) f i q q e (add_zero q) x]
  exact CategoryTheory.congr_fun (Cochain.ofHom_v (g.app ()) q) (f.app () i q e x)

theorem pre_apply (N : Mod A) (g : L ⟶ M) {r : ℤ} (f : GradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (L.complex ()).X i) :
    GradedHom.app (((pre N g).app ()).f r f) () i q e x =
      f.app () i q e ((g.app ()).f i x) := by
  change GradedHom.app ((r*0).negOnePow • compose L M N r 0 r (add_zero r) f (ofStrict g)) ()
    i q e x = _
  rw [mul_zero, Int.negOnePow_zero, one_smul]
  rw [compose_apply _ f (ofStrict g) i i q (add_zero i) e x]
  change f.app () i q e ((Cochain.ofHom (g.app ())).v i i (add_zero i) x) = _
  rw [Cochain.ofHom_v]

private theorem strict_sub_apply (f g : M ⟶ N)
    (i : ℤ) (x : (M.complex ()).X i) :
    GradedHom.app (ofStrict f - ofStrict g) () i i (add_zero i) x =
      (f.app ()).f i x - (g.app ()).f i x := by
  change (Cochain.ofHom (f.app ()) - Cochain.ofHom (g.app ())).v i i (add_zero i) x = _
  simp only [Cochain.sub_v, Cochain.ofHom_v, ModuleCat.hom_sub, LinearMap.sub_apply]

private theorem boundary_eq_of_homotopy {f g : M ⟶ N} {h : GradedHom M N (-1)}
    (e : _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g h) :
    (homComplex M N).d (-1) 0 h = ofStrict f - ofStrict g := by
  apply graded_ext
  intro i q hq x
  have hi : i = q := by omega
  subst hi
  rw [RightDGModule.boundary_component, strict_sub_apply]
  exact (e () i x).symm

private theorem homotopy_of_boundary_eq {f g : M ⟶ N} {h : GradedHom M N (-1)}
    (e : (homComplex M N).d (-1) 0 h = ofStrict f - ofStrict g) :
    _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g h := by
  intro a i x
  cases a
  rw [← RightDGModule.boundary_component h () i x, e, strict_sub_apply]

private theorem postGraded_sub (M : Mod A) {s : ℤ} (f g : GradedHom N P s) :
    postGraded M (f-g) = postGraded M f - postGraded M g := by
  apply graded_ext
  intro r q e h
  change _ = ((postGraded M f).val () - (postGraded M g).val ()).v r q e h
  simp only [Cochain.sub_v, ModuleCat.hom_sub, LinearMap.sub_apply]
  exact LinearMap.congr_fun (map_sub (compose M N P s r q (by omega)) f g) h

private theorem preGraded_sub (N : Mod A) {s : ℤ} (f g : GradedHom L M s) :
    preGraded N (f-g) = preGraded N f - preGraded N g := by
  apply graded_ext
  intro r q e h
  change _ = ((preGraded N f).val () - (preGraded N g).val ()).v r q e h
  simp only [Cochain.sub_v, ModuleCat.hom_sub, LinearMap.sub_apply]
  change (r*s).negOnePow • compose L M N r s q _ h (f-g) =
    (r*s).negOnePow • compose L M N r s q _ h f -
      (r*s).negOnePow • compose L M N r s q _ h g
  rw [map_sub, smul_sub]

/-- A target homotopy induces postcomposition with its homogeneous degree minus one map. -/
theorem post_homotopy (M : Mod A) {f g : N ⟶ P} {h : GradedHom N P (-1)}
    (e : _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g h) :
    _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation
      (post M f) (post M g) (postGraded M h) := by
  apply homotopy_of_boundary_eq
  change (homComplex (internalHom M N) (internalHom M P)).d (-1) ((-1)+1)
    (postGraded M h) = _
  rw [postGraded_d]
  change postGraded M ((homComplex N P).d (-1) 0 h) = _
  rw [boundary_eq_of_homotopy e, postGraded_sub]
  change postGraded M (ofStrict f) - postGraded M (ofStrict g) =
    (RightDGModule.strictCycle (post M f)).val - (RightDGModule.strictCycle (post M g)).val
  simp only [post, RightDGModule.strictCycle_strictMap]

/-- A source homotopy induces signed precomposition with its degree minus one map. -/
theorem pre_homotopy (N : Mod A) {f g : L ⟶ M} {h : GradedHom L M (-1)}
    (e : _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g h) :
    _root_.Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation
      (pre N f) (pre N g) (preGraded N h) := by
  apply homotopy_of_boundary_eq
  change (homComplex (internalHom M N) (internalHom L N)).d (-1) ((-1)+1)
    (preGraded N h) = _
  rw [preGraded_d]
  change preGraded N ((homComplex L M).d (-1) 0 h) = _
  rw [boundary_eq_of_homotopy e, preGraded_sub]
  change preGraded N (ofStrict f) - preGraded N (ofStrict g) =
    (RightDGModule.strictCycle (pre N f)).val - (RightDGModule.strictCycle (pre N g)).val
  simp only [pre, RightDGModule.strictCycle_strictMap]

private theorem internalHom_map_ext {M' N' : Mod A}
    {f g : internalHom M N ⟶ internalHom M' N'}
    (e : ∀ (r i q : ℤ) (a : GradedHom M N r) (h : i+r = q) (x : (M'.complex ()).X i),
      GradedHom.app ((f.app ()).f r a) () i q h x =
        GradedHom.app ((g.app ()).f r a) () i q h x) : f = g := by
  apply RightDGModuleModel.hom_ext
  intro z
  cases z
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact graded_ext (fun i q h x => e r i q a h x)

private theorem post_id (M N : Mod A) : post M (𝟙 N) = 𝟙 (internalHom M N) := by
  apply internalHom_map_ext
  intro r i q f e x
  rw [post_apply]
  rfl

private theorem pre_id (M N : Mod A) : pre N (𝟙 M) = 𝟙 (internalHom M N) := by
  apply internalHom_map_ext
  intro r i q f e x
  rw [pre_apply]
  rfl

private theorem post_comp (M : Mod A) {N₁ N₂ N₃ : Mod A} (g : N₁ ⟶ N₂) (h : N₂ ⟶ N₃) :
    post M (g ≫ h) = post M g ≫ post M h := by
  apply internalHom_map_ext
  intro r i q f e x
  change GradedHom.app (((post M (g ≫ h)).app ()).f r f) () i q e x =
    GradedHom.app (((post M h).app ()).f r (((post M g).app ()).f r f)) () i q e x
  rw [post_apply, post_apply, post_apply]
  rfl

private theorem pre_comp (N : Mod A) {M₁ M₂ M₃ : Mod A} (g : M₁ ⟶ M₂) (h : M₂ ⟶ M₃) :
    pre N (g ≫ h) = pre N h ≫ pre N g := by
  apply internalHom_map_ext
  intro r i q f e x
  change GradedHom.app (((pre N (g ≫ h)).app ()).f r f) () i q e x =
    GradedHom.app (((pre N g).app ()).f r (((pre N h).app ()).f r f)) () i q e x
  rw [pre_apply, pre_apply, pre_apply]
  rfl

private theorem pre_post (f : L ⟶ M) (g : N ⟶ P) :
    pre N f ≫ post L g = post M g ≫ pre P f := by
  apply internalHom_map_ext
  intro r i q a e x
  change GradedHom.app (((post L g).app ()).f r (((pre N f).app ()).f r a)) () i q e x =
    GradedHom.app (((pre P f).app ()).f r (((post M g).app ()).f r a)) () i q e x
  rw [post_apply, pre_apply, pre_apply, post_apply]

/-- A pair of strict maps acts by precomposition and postcomposition. -/
def mapStrict (f : L ⟶ M) (g : N ⟶ P) : internalHom M N ⟶ internalHom L P :=
  pre N f ≫ post L g

theorem mapStrict_apply (f : L ⟶ M) (g : N ⟶ P) {r : ℤ} (h : GradedHom M N r)
    (i q : ℤ) (e : i+r = q) (x : (L.complex ()).X i) :
    GradedHom.app (((mapStrict f g).app ()).f r h) () i q e x =
      (g.app ()).f q (h.app () i q e ((f.app ()).f i x)) := by
  change GradedHom.app (((post L g).app ()).f r (((pre N f).app ()).f r h)) () i q e x = _
  rw [post_apply, pre_apply]

section HomotopyCategory

open Opposite
open RightDGModule (K homotopyClass toHomotopyCategory homotopyClass_surjective homotopyCriterion)

private abbrev Kₐ (A : CommDGAlgebra.{u,v} k) := K (algebraCategory A)

noncomputable section

private def representative {M N : Kₐ A} (f : M ⟶ N) : RightDGModuleHomModel M N :=
  Classical.choose (homotopyClass_surjective f)

private theorem representative_class {M N : Kₐ A} (f : M ⟶ N) :
    homotopyClass (representative f) = f :=
  Classical.choose_spec (homotopyClass_surjective f)

private theorem mapStrict_class_eq {f f' : L ⟶ M} {g g' : N ⟶ P}
    (e : homotopyClass f = homotopyClass f') (e' : homotopyClass g = homotopyClass g') :
    homotopyClass (mapStrict f g) = homotopyClass (mapStrict f' g') := by
  obtain ⟨h, hh⟩ := (homotopyCriterion f f').mp e
  obtain ⟨j, hj⟩ := (homotopyCriterion g g').mp e'
  have e₁ := (homotopyCriterion (pre N f) (pre N f')).mpr ⟨preGraded N h, pre_homotopy N hh⟩
  have e₂ := (homotopyCriterion (post L g) (post L g')).mpr ⟨postGraded L j, post_homotopy L hj⟩
  let F := toHomotopyCategory (algebraCategory A)
  change F.map (pre N f ≫ post L g) = F.map (pre N f' ≫ post L g')
  rw [Functor.map_comp, Functor.map_comp]
  exact congrArg₂ (fun (x : F.obj (internalHom M N) ⟶ F.obj (internalHom L N))
    (y : F.obj (internalHom L N) ⟶ F.obj (internalHom L P)) => x ≫ y) e₁ e₂

private theorem mapStrict_id (M N : Mod A) :
    mapStrict (𝟙 M) (𝟙 N) = 𝟙 (internalHom M N) := by
  simp only [mapStrict, pre_id, post_id, Category.id_comp]

private theorem mapStrict_comp {M₁ M₂ M₃ N₁ N₂ N₃ : Mod A}
    (f : M₂ ⟶ M₁) (f' : M₃ ⟶ M₂) (g : N₁ ⟶ N₂) (g' : N₂ ⟶ N₃) :
    mapStrict (f' ≫ f) (g ≫ g') = mapStrict f g ≫ mapStrict f' g' := by
  simp only [mapStrict, pre_comp, post_comp, Category.assoc]
  rw [← Category.assoc (post M₂ g), ← pre_post, Category.assoc]

/-- The internal Hom bifunctor on the shared homotopy category. -/
def homotopyHom (A : CommDGAlgebra.{u,v} k) : (Kₐ A)ᵒᵖ × Kₐ A ⥤ Kₐ A where
  obj X := internalHom X.1.unop X.2
  map f := homotopyClass (mapStrict (representative f.1.unop) (representative f.2))
  map_id X := by
    refine (mapStrict_class_eq (f' := 𝟙 _) (g' := 𝟙 _) ?_ ?_).trans ?_
    · exact representative_class _
    · exact representative_class _
    · rw [mapStrict_id]
      rfl
  map_comp f g := by
    refine (mapStrict_class_eq (f' := representative g.1.unop ≫ representative f.1.unop)
      (g' := representative f.2 ≫ representative g.2) ?_ ?_).trans ?_
    · change homotopyClass (representative (g.1.unop ≫ f.1.unop)) =
        (toHomotopyCategory _).map (representative g.1.unop ≫ representative f.1.unop)
      rw [Functor.map_comp]
      exact (representative_class _).trans
        (congrArg₂ (· ≫ ·) (representative_class _) (representative_class _)).symm
    · change homotopyClass (representative (f.2 ≫ g.2)) =
        (toHomotopyCategory _).map (representative f.2 ≫ representative g.2)
      rw [Functor.map_comp]
      exact (representative_class _).trans
        (congrArg₂ (· ≫ ·) (representative_class _) (representative_class _)).symm
    · rw [mapStrict_comp]
      exact (toHomotopyCategory _).map_comp _ _

theorem homotopyHom_map_strict (f : L ⟶ M) (g : N ⟶ P) :
    let F := toHomotopyCategory (algebraCategory A)
    (homotopyHom A).map (CategoryTheory.Prod.mkHom (F.map f).op (F.map g)) =
      F.map (mapStrict f g) := by
  exact mapStrict_class_eq (representative_class _) (representative_class _)

end

end HomotopyCategory

section DerivedCategory

open Opposite
open RightDGModule (K D Q homotopyClass toHomotopyCategory quasiIsomorphisms)
open _root_.Specs.DerivedFormalization.DG.DerivedKProjective
  (kProjectiveObjects restrictedLocalization replacementIso)
open _root_.Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)

noncomputable section

local instance (B : DGCategory.{u,v,0} k) :
    Category (_root_.Specs.DerivedFormalization.DG.HomComplex.homotopyCategory B) :=
  inferInstanceAs (Category (K B))

/-- The native derived category is already adequately sized for the one-object algebra. -/
abbrev nativeD (A : CommDGAlgebra.{u,v} k) := D (algebraCategory A) ⟨RightDGModule.instCategoryK _, rfl⟩

abbrev nativeQ (A : CommDGAlgebra.{u,v} k) : K (algebraCategory A) ⥤ nativeD A :=
  Q (algebraCategory A) ⟨RightDGModule.instCategoryK _, rfl⟩

private abbrev kProj (A : CommDGAlgebra.{u,v} k) := (kProjectiveObjects (algebraCategory A)).FullSubcategory

private abbrev includeKProj (A : CommDGAlgebra.{u,v} k) :
    kProj A ⥤ K (algebraCategory A) := (kProjectiveObjects (algebraCategory A)).ι

private abbrev localizeKProj (A : CommDGAlgebra.{u,v} k) : kProj A ⥤ nativeD A :=
  restrictedLocalization (algebraCategory A) ⟨RightDGModule.instCategoryK _, rfl⟩

/-- The product presentation of the derived input variables, resolving the first. -/
abbrev inputLocalization (A : CommDGAlgebra.{u,v} k) :
    (kProj A)ᵒᵖ × K (algebraCategory A) ⥤ (nativeD A)ᵒᵖ × nativeD A :=
  (localizeKProj A).op.prod (nativeQ A)

private abbrev modelHom (A : CommDGAlgebra.{u,v} k) :
    (kProj A)ᵒᵖ × K (algebraCategory A) ⥤ nativeD A :=
  (includeKProj A).op.prod (𝟭 _) ⋙ homotopyHom A ⋙ nativeQ A

private abbrev inputWeakEquivalences (A : CommDGAlgebra.{u,v} k) :
    MorphismProperty ((kProj A)ᵒᵖ × K (algebraCategory A)) :=
  (MorphismProperty.isomorphisms _).prod (quasiIsomorphisms (algebraCategory A))

private instance quasiIsomorphisms_containsIdentities :
    (quasiIsomorphisms (algebraCategory A)).ContainsIdentities :=
  ⟨fun M => ⟨𝟙 (show Mod A from M), rfl, fun a => by change QuasiIso (𝟙 ((show Mod A from M).complex a)); infer_instance⟩⟩

private instance (A : CommDGAlgebra.{u,v} k) : (localizeKProj A).IsEquivalence :=
  RightDGModule.kProjectiveLocalization_isEquivalence.{u,v,0}
    (algebraCategory A) ⟨RightDGModule.instCategoryK _, rfl⟩

private instance (A : CommDGAlgebra.{u,v} k) :
    (inputLocalization A).IsLocalization (inputWeakEquivalences A) := by
  let : (localizeKProj A).op.IsLocalization (MorphismProperty.isomorphisms _) :=
    Functor.IsLocalization.of_isEquivalence _ _ (le_refl _)
  exact Functor.IsLocalization.prod (L₁ := (localizeKProj A).op) (L₂ := nativeQ A)
    (MorphismProperty.isomorphisms _) (quasiIsomorphisms _)

private theorem post_quasiIso (M : Mod A) (hM : RightDGModule.IsKProjective M)
    (g : N ⟶ P) (hg : RightDGModule.IsQuasiIso g) : RightDGModule.IsQuasiIso (post M g) := by
  intro a
  cases a
  have ee : (post M g).app () = RightDGModule.homComplexMap M g := by
    apply HomologicalComplex.hom_ext
    intro r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    apply graded_ext
    intro i q e x
    rw [post_apply, RightDGModule.homComplexMap_app]
  rw [ee]
  exact hM.homComplexMap_quasiIso g hg

private theorem modelHom_inverts (A : CommDGAlgebra.{u,v} k) :
    (inputWeakEquivalences A).IsInvertedBy (modelHom A) := by
  intro X Y f hf
  let a : X ⟶ (Y.1, X.2) := CategoryTheory.Prod.mkHom f.1 (𝟙 X.2)
  let b : (Y.1, X.2) ⟶ Y := CategoryTheory.Prod.mkHom (𝟙 Y.1) f.2
  have hab : a ≫ b = f := CategoryTheory.Prod.hom_ext (by simp [a, b]) (by simp [a, b])
  let : IsIso f.1 := hf.1
  let : IsIso a := by
    let e : X ≅ (Y.1, X.2) := (CategoryTheory.prod.etaIso X).symm ≪≫
      (asIso f.1).prod (Iso.refl X.2)
    have he : e.hom = a := by
      apply CategoryTheory.Prod.hom_ext <;> simp [e, a, CategoryTheory.prod.etaIso]
    rw [← he]
    infer_instance
  have hb : IsIso ((modelHom A).map b) := by
    obtain ⟨g, hg, hq⟩ := hf.2
    let M := Y.1.unop.obj
    have he : ((modelHom A).map b) = (nativeQ A).map
        ((toHomotopyCategory (algebraCategory A)).map (post M g)) := by
      change (nativeQ A).map ((homotopyHom A).map (CategoryTheory.Prod.mkHom (𝟙 (op M)) f.2)) = _
      rw [show f.2 = (toHomotopyCategory (algebraCategory A)).map g from hg.symm]
      have hl := homotopyHom_map_strict (𝟙 (show Mod A from M)) g
      have hmap : mapStrict (𝟙 (show Mod A from M)) g = post M g := by
        simp only [mapStrict, pre_id, Category.id_comp]
      have hm := congrArg ((toHomotopyCategory (algebraCategory A)).map) hmap
      exact congrArg ((nativeQ A).map) (hl.trans hm)
    rw [he]
    exact Localization.inverts (nativeQ A) (quasiIsomorphisms (algebraCategory A)) _
      ⟨post M g, rfl, post_quasiIso M Y.1.unop.property g hq⟩
  rw [← hab, Functor.map_comp]
  infer_instance

noncomputable def deriveFromHomotopy : DeriveFromModelsFamilyType.{u,v} :=
  @_root_.Specs.DerivedFormalization.Affine.DerivedHom.deriveFromModels

/-- Internal derived Hom, resolving the source and localizing the target. -/
def rHom (A : CommDGAlgebra.{u,v} k) :
    (nativeD A)ᵒᵖ × nativeD A ⥤ nativeD A := by
  letI : Fact (HomotopyCategoryLaws (algebraCategory A)) := ⟨⟨RightDGModule.instCategoryK _, rfl⟩⟩
  letI : Category (_root_.Specs.DerivedFormalization.DG.Derived.derivedCategory (algebraCategory A)
      (Fact.out (p := HomotopyCategoryLaws (algebraCategory A)))) :=
    _root_.Specs.DerivedFormalization.DG.DerivedKProjective.derivedCategoryInstance (algebraCategory A) _
  letI : (derivedInputs A).IsLocalization (modelDenominators A) :=
    inferInstanceAs ((inputLocalization A).IsLocalization (inputWeakEquivalences A))
  exact deriveFromHomotopy A (homotopyHom A) (modelHom_inverts A)

/-- The factorization is natural in all homotopy classes between these models. -/
def rHomFactorization (A : CommDGAlgebra.{u,v} k) :
    inputLocalization A ⋙ rHom A ≅ modelHom A :=
  Localization.fac (modelHom A) (modelHom_inverts A) (inputLocalization A)

/-- Transport the localized Hom along an isomorphism to a pair of models. -/
def comparisonAlongIso {X : (nativeD A)ᵒᵖ × nativeD A}
    {Y : (kProj A)ᵒᵖ × K (algebraCategory A)}
    (e : X ≅ (inputLocalization A).obj Y) :
    (rHom A).obj X ≅ (modelHom A).obj Y :=
  (rHom A).mapIso e ≪≫ (rHomFactorization A).app Y

/-- The comparison commutes with any derived arrow and a compatible map
between the selected models. -/
theorem comparisonAlongIso_natural
    {X X' : (nativeD A)ᵒᵖ × nativeD A}
    {Y Y' : (kProj A)ᵒᵖ × K (algebraCategory A)}
    (e : X ≅ (inputLocalization A).obj Y)
    (e' : X' ≅ (inputLocalization A).obj Y')
    (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ (inputLocalization A).map g) :
    (rHom A).map f ≫ (comparisonAlongIso e').hom =
      (comparisonAlongIso e).hom ≫ (modelHom A).map g := by
  let R := rHom A
  let c := rHomFactorization A
  change R.map f ≫ (R.map e'.hom ≫ c.hom.app Y') =
    (R.map e.hom ≫ c.hom.app Y) ≫ (modelHom A).map g
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  have hn : R.map ((inputLocalization A).map g) ≫ c.hom.app Y' =
      c.hom.app Y ≫ (modelHom A).map g := c.hom.naturality g
  rw [hn, Category.assoc]

/-- Any K-projective model via a strict quasi-isomorphism computes the same derived Hom. -/
def modelComparison {P M : Mod A} (p : P ⟶ M) (hp : RightDGModule.IsQuasiIso p)
    (hP : RightDGModule.IsKProjective P) (N : Mod A) :
    (rHom A).obj (op ((nativeQ A).obj M), (nativeQ A).obj N) ≅
      (nativeQ A).obj (internalHom P N) := by
  let e : (nativeQ A).obj P ≅ (nativeQ A).obj M :=
    replacementIso ⟨RightDGModule.instCategoryK _, rfl⟩ p hp
  exact comparisonAlongIso (Y := (op ⟨P, hP⟩, N))
    (e.op.prod (Iso.refl ((nativeQ A).obj N)))

/-- The same bifunctor on the shared ambient localization, with the original
one-object algebra and the same base field. -/
abbrev ambientD (A : CommDGAlgebra.{u,v} k) :=
  DG.AmbientDerived.derivedCategory.{u,v,0,t} (algebraCategory A)

abbrev ambientRHom (A : CommDGAlgebra.{u,v} k) :
    (ambientD.{u,v,t} A)ᵒᵖ × ambientD.{u,v,t} A ⥤ ambientD.{u,v,t} A :=
  rHom (liftAlgebra.{u,v,t} A)

/-- The model comparison in the ambient category uses its actual localization. -/
def ambientModelComparison {P M : Mod (liftAlgebra.{u,v,t} A)}
    (p : P ⟶ M) (hp : RightDGModule.IsQuasiIso p)
    (hP : RightDGModule.IsKProjective P) (N : Mod (liftAlgebra.{u,v,t} A)) :
    let Q := DG.AmbientDerived.quotient.{u,v,0,t} (algebraCategory A)
    (ambientRHom.{u,v,t} A).obj (op (Q.obj M), Q.obj N) ≅ Q.obj (internalHom P N) :=
  modelComparison (A := liftAlgebra.{u,v,t} A) p hp hP N

end

end DerivedCategory

/-- Multiplication in the target is exactly the transported left action. -/
theorem leftScalarFormula : LeftScalarFormula.{u,v} := by
  intro k _ _ A M N r j n h f z i q ir e er x
  constructor
  · rw [scalarOperator_apply]
    change GradedHom.app ((r*j).negOnePow • (internalHom M N).act r j n h f z) () i q e x = _
    rw [graded_smul_apply, scalarFormula M N r j n h f z i q ir e er x,
      smul_smul, ← Int.negOnePow_add]
    rw [show r*j+i*j = ir*j by rw [← er]; ring]
  · rw [scalarOperator_apply, map_zsmul_unit,
      GradedHom.comm_act f i j (i+j) ir q rfl er (by omega) x z, scalarOperator_apply,
      smul_smul, ← Int.negOnePow_add]
    rw [show r*j+ir*j = i*j+2*(r*j) by rw [← er]; ring,
      Int.negOnePow_add, Int.negOnePow_two_mul, mul_one]

private def homActions (A : CommDGAlgebra.{u,v} k) : HomActions A where
  pre := pre
  post := post
  preGraded := preGraded
  postGraded := postGraded

private theorem homActionLaws (A : CommDGAlgebra.{u,v} k) : HomActionLaws A (homActions A) where
  pre f _ g i q e x := pre_apply _ f g i q e x
  post g _ f i q e x := post_apply _ g f i q e x
  preGraded r _s q e g f := preGraded_apply _ g r q e f
  postGraded r _s q e g f := postGraded_apply _ g r q e f
  preHomotopy h := pre_homotopy _ h
  postHomotopy h := post_homotopy _ h

theorem homActionsExist : HomActionsExist.{u,v} :=
  fun A => ⟨homActions A, homActionLaws A⟩

theorem derivedHomRealization : DerivedHomRealization.{u,v} := by
  intro k _ _ A h
  refine ⟨homActions A, homotopyHom A, rHom A, homActionLaws A, fun _ _ => rfl,
    ?_, rHomFactorization A, ?_, ?_⟩
  · intro L M N P f g
    exact heq_of_eq (homotopyHom_map_strict f g)
  · intro X X' Y Y' e e' f g he
    exact comparisonAlongIso_natural (A := A) e e' f g he
  · intro P M p hp hP N
    exact ⟨modelComparison p hp hP N⟩

section Coefficients

open DerivedFormalization.DG.AmbientDerived (strictInput)
open DerivedFormalization.DG.CoefficientLift
  (gradedEquiv gradedEquiv_apply_down gradedEquiv_comm_d gradedEquiv_comp gradedEquiv_strict
    homotopyClass_lift_iff isoOfComponents)

abbrev liftModule {A : CommDGAlgebra.{u,v} k} (M : Mod A) : Mod (liftAlgebra.{u,v,t} A) :=
  (strictInput.{u,v,0,t} (algebraCategory A)).obj M

private theorem gradedEquiv_act (M N : Mod A) (r j n : ℤ) (h : r+j = n)
    (f : GradedHom M N r) (z : A.complex.X j) :
    gradedEquiv.{u,v,0,t} M N n ((internalHom M N).act (a := ()) (b := ()) r j n h f z) =
      (internalHom (liftModule.{u,v,t} M) (liftModule.{u,v,t} N)).act (a := ()) (b := ()) r j n h
        (gradedEquiv.{u,v,0,t} M N r f) (ULift.up z) := by
  apply graded_ext (A := liftAlgebra.{u,v,t} A)
  intro i q e x
  apply ULift.ext
  rw [gradedEquiv_apply_down, scalarFormula M N r j n h f z i q (i+r) e rfl x.down]
  have he := scalarFormula (liftModule.{u,v,t} M) (liftModule.{u,v,t} N)
    r j n h (gradedEquiv.{u,v,0,t} M N r f) (ULift.up z) i q (i+r) e rfl x
  rw [he]
  rfl

/-- The strict comparison is given in each degree by conjugation with the
original up and down equivalences, using the actual scalar action. -/
def liftInternalHomIso (M N : Mod A) :
    liftModule.{u,v,t} (internalHom M N) ≅
      internalHom (liftModule.{u,v,t} M) (liftModule.{u,v,t} N) :=
  isoOfComponents
    (fun _ r => ULift.moduleEquiv.trans (gradedEquiv.{u,v,0,t} M N r))
    (fun _ r f => gradedEquiv_comm_d r (r+1) f.down)
    (by
      intro a b r j n h f z
      cases a
      cases b
      exact gradedEquiv_act M N r j n h f.down z.down)

theorem liftInternalHomIso_apply (M N : Mod A) (r : ℤ)
    (f : ((liftModule.{u,v,t} (internalHom M N)).complex ()).X r)
    (i q : ℤ) (e : i+r = q) (x : ((liftModule.{u,v,t} M).complex ()).X i) :
    (component (((liftInternalHomIso.{u,v,t} M N).hom.app ()).f r f) () i q e x).down =
      component f.down () i q e x.down := rfl

/-- Conjugation of the original homogeneous maps commutes with pre- and postcomposition. -/
theorem liftInternalHomIso_natural (f : L ⟶ M) (g : N ⟶ P) :
    let U := strictInput.{u,v,0,t} (algebraCategory A)
    U.map (mapStrict f g) ≫ (liftInternalHomIso.{u,v,t} L P).hom =
      (liftInternalHomIso.{u,v,t} M N).hom ≫ mapStrict (U.map f) (U.map g) := by
  dsimp only
  apply RightDGModuleModel.hom_ext
  intro a
  cases a
  apply HomologicalComplex.hom_ext
  intro r
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  apply graded_ext (A := liftAlgebra.{u,v,t} A)
  intro i q e x
  apply ULift.ext
  change (component (gradedEquiv.{u,v,0,t} L P r (((mapStrict f g).app ()).f r h.down))
      () i q e x).down =
    (component (((mapStrict (A := liftAlgebra.{u,v,t} A) (L := liftModule.{u,v,t} L)
      (M := liftModule.{u,v,t} M) (N := liftModule.{u,v,t} N) (P := liftModule.{u,v,t} P)
      ((strictInput.{u,v,0,t} (algebraCategory A)).map f)
      ((strictInput.{u,v,0,t} (algebraCategory A)).map g)).app ()).f r
        (gradedEquiv.{u,v,0,t} M N r h.down)) () i q e x).down
  rw [gradedEquiv_apply_down, mapStrict_apply]
  have hh := mapStrict_apply (A := liftAlgebra.{u,v,t} A) (L := liftModule.{u,v,t} L)
    (M := liftModule.{u,v,t} M) (N := liftModule.{u,v,t} N) (P := liftModule.{u,v,t} P)
    ((strictInput.{u,v,0,t} (algebraCategory A)).map f)
    ((strictInput.{u,v,0,t} (algebraCategory A)).map g)
    (gradedEquiv.{u,v,0,t} M N r h.down) i q e x
  exact (congrArg ULift.down hh).symm

theorem coefficientConjugation : CoefficientConjugation.{u,v,t} := by
  intro k _ _ A
  refine ⟨gradedEquiv.{u,v,0,t}, ?_⟩
  constructor
  · intros
    rfl
  · exact gradedEquiv_act
  · intro M N r q f
    exact gradedEquiv_comm_d.{u,v,0,t} r q f
  · intro M N P s r q h g f
    exact gradedEquiv_comp.{u,v,0,t} s r q h g f
  · intro M N f
    exact gradedEquiv_strict.{u,v,0,t} f
  · intro M N f g h
    constructor
    · intro H a i x
      exact congrArg ULift.down (H a i (ULift.up x))
    · intro H a i x
      exact ULift.ext (H a i x.down)
  · intro M N
    exact ⟨liftInternalHomIso.{u,v,t} M N, fun _ _ => rfl⟩

theorem ambientModels : AmbientModels.{u,v,t} := by
  intro k _ _ A h
  refine ⟨ambientRHom.{u,v,t} A, ?_, ?_⟩
  · intro P M p hp hP N
    exact ⟨ambientModelComparison (A := A) p hp hP N⟩
  · intro M N
    obtain ⟨P, p, hp, _, hP, _⟩ :=
      RightDGModule.originalInputDerivedHomComparison.{u,v,0,t} (algebraCategory A) h M
    exact ⟨P, p, hP, hp, ⟨ambientModelComparison (A := A) p hp hP (liftModule.{u,v,t} N)⟩⟩

end Coefficients

end DerivedHom

end DerivedFormalization.Affine
