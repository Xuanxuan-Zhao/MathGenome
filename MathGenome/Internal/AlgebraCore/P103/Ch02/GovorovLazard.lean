import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.GovorovLazard
import MathGenome.Internal.AlgebraCore.P103.Ch02.FlatnessTests

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
open P103.Specs.Ch02.GovorovLazard
open P103.Specs.Ch02.FlatnessTests

namespace P103.Ch02.GovorovLazard

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Finite relation factorization equalizes any parallel pair over M. -/
theorem equalize (h : FiniteRelations R M) {X Y : FreeTo R M} (f g : X ⟶ Y) :
    ∃ (Z : FreeTo R M) (q : Y ⟶ Z), f ≫ q = g ≫ q := by
  classical
  let b := Pi.basisFun R (Fin Y.rank)
  let c := Pi.basisFun R (Fin X.rank)
  let r : Fin X.rank → Fin Y.rank → R := fun j i => (f.linear - g.linear) (c j) i
  have hr (j : Fin X.rank) : ∑ i, r j i • Y.toM (b i) = 0 := by
    calc
      _ = Y.toM (∑ i, r j i • b i) := by simp
      _ = Y.toM ((f.linear - g.linear) (c j)) := by
        congr 1
        simpa [r, b, Pi.basisFun_repr] using b.sum_repr ((f.linear - g.linear) (c j))
      _ = 0 := by
        have hf := LinearMap.congr_fun f.over (c j)
        have hg := LinearMap.congr_fun g.over (c j)
        simpa only [LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero] using hf.trans hg.symm
  obtain ⟨l, y, s, hx, hs⟩ := h Y.rank X.rank (fun i => Y.toM (b i)) r hr
  let Z : FreeTo R M := ⟨l, (Pi.basisFun R (Fin l)).constr ℕ y⟩
  let q : (Fin Y.rank → R) →ₗ[R] (Fin l → R) :=
    b.constr ℕ (fun i => fun a => s i a)
  have hq (i) : q (b i) = fun a => s i a := b.constr_basis ℕ _ i
  have hZ (v : Fin l → R) : Z.toM v = ∑ a, v a • y a := by
    change (Pi.basisFun R (Fin l)).constr ℕ y v = _
    simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, Pi.basisFun_repr]
  have hqover : Z.toM.comp q = Y.toM := by
    apply b.ext
    intro i
    simpa only [LinearMap.comp_apply, hq, hZ] using (hx i).symm
  refine ⟨Z, ⟨q, hqover⟩, ?_⟩
  apply FreeTo.Hom.ext
  change q.comp f.linear = q.comp g.linear
  apply c.ext
  intro j
  apply sub_eq_zero.mp
  simp only [LinearMap.comp_apply]
  rw [← map_sub]
  change q ((f.linear - g.linear) (c j)) = 0
  rw [← b.sum_repr ((f.linear - g.linear) (c j))]
  ext a
  simpa only [map_sum, map_smul, hq, Finset.sum_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, b, Pi.basisFun_repr, r] using hs j a

/-- Direct sum gives a common successor of two finite-free maps. -/
theorem common_successor (X Y : FreeTo R M) :
    ∃ (Z : FreeTo R M) (_ : X ⟶ Z) (_ : Y ⟶ Z), True := by
  classical
  let b := Pi.basisFun R (Fin (X.rank + Y.rank))
  let x : Fin (X.rank + Y.rank) → M := Fin.addCases (fun i => X.toM (Pi.basisFun R (Fin X.rank) i))
    (fun i => Y.toM (Pi.basisFun R (Fin Y.rank) i))
  let Z : FreeTo R M := ⟨X.rank + Y.rank, b.constr ℕ x⟩
  let i : (Fin X.rank → R) →ₗ[R] (Fin (X.rank + Y.rank) → R) :=
    (Pi.basisFun R (Fin X.rank)).constr ℕ (fun j => b (j.castAdd Y.rank))
  let j : (Fin Y.rank → R) →ₗ[R] (Fin (X.rank + Y.rank) → R) :=
    (Pi.basisFun R (Fin Y.rank)).constr ℕ (fun j => b (j.natAdd X.rank))
  refine ⟨Z, ⟨i, ?_⟩, ⟨j, ?_⟩, trivial⟩
  · apply (Pi.basisFun R (Fin X.rank)).ext
    intro k
    simp [Z, i, x, b]
  · apply (Pi.basisFun R (Fin Y.rank)).ext
    intro k
    simp [Z, j, x, b]

/-- The source's category of finite-free maps is a small filtered category. -/
theorem canonical_filtered : canonical_filteredType.{u,v} := by
  intro R _ M _ _ h
  exact
    { cocone_objs := common_successor
      cocone_maps := fun {_ _} f g => equalize h f g
      nonempty := ⟨⟨0, 0⟩⟩ }

/-- The rank-one object with specified generator image. -/
abbrev point (m : M) : FreeTo R M :=
  ⟨1, (LinearMap.toSpanSingleton R M m).comp (LinearMap.proj 0)⟩

/-- A vector determines an arrow from its rank-one representative. -/
def pointArrow (X : FreeTo R M) (v : Fin X.rank → R) : point (X.toM v) ⟶ X :=
  ⟨(LinearMap.toSpanSingleton R _ v).comp (LinearMap.proj 0), by
    apply LinearMap.ext
    intro a
    simp [point, LinearMap.comp_apply]⟩

/-- A zero vector in M vanishes after a transition, by equalizing the
rank-one arrows sending the generator to that vector and to zero. -/
theorem eventually_zero [IsFiltered (FreeTo R M)] (X : FreeTo R M)
    (v : Fin X.rank → R) (hv : X.toM v = 0) :
    ∃ (Y : FreeTo R M) (f : X ⟶ Y), f.linear v = 0 := by
  let a : point (0 : M) ⟶ X :=
    ⟨(LinearMap.toSpanSingleton R _ v).comp (LinearMap.proj 0), by
      apply LinearMap.ext
      intro x
      simp [point, hv, LinearMap.comp_apply]⟩
  let b : point (0 : M) ⟶ X := ⟨0, by apply LinearMap.ext; intro x; simp [point]⟩
  obtain ⟨Y, f, hf⟩ := IsFilteredOrEmpty.cocone_maps a b
  refine ⟨Y, f, ?_⟩
  have he := congrArg (fun k : point (0 : M) ⟶ Y => k.linear (fun _ => 1)) hf
  change f.linear ((1 : R) • v) = f.linear 0 at he
  simpa using he

/-- The concrete filtered-colimit construction works with the ring and
module carriers in different universes. -/
instance forget_preserves_filtered_diagram
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) : PreservesColimit F (forget (ModuleCat R)) :=
  preservesColimit_of_preserves_colimit_cocone
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
    (Types.TypeMax.colimitCoconeIsColimit (F ⋙ forget (ModuleCat R)))

instance forget_reflects_filtered_diagram
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) : ReflectsColimit F (forget (ModuleCat R)) :=
  reflectsColimit_of_reflectsIsomorphisms _ _

/-- A filtered module colimit has the same universal property for targets
in larger universes. This avoids silently restricting tensor test modules. -/
def filteredDesc {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : ∀ j, F.obj j →ₗ[R] N)
    (hf : ∀ {i j} (a : i ⟶ j) x, f j (F.map a x) = f i x) : c.pt →ₗ[R] N := by
  have hc' := isColimitOfPreserves (forget (ModuleCat R)) hc
  choose j x hx using Types.jointly_surjective_of_isColimit hc'
  let g (m : c.pt) : N := f (j m) (x m)
  have hg (i : J) (a : F.obj i) : g (c.ι.app i a) = f i a := by
    obtain ⟨k, b, d, he⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc').mp (hx (c.ι.app i a))
    exact (hf b _).symm.trans ((congrArg (f k) he).trans (hf d _))
  exact
    { toFun := g
      map_add' := fun a b => by
        obtain ⟨i, a, b, rfl, rfl⟩ :=
          Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc' a b
        change g (c.ι.app i a + c.ι.app i b) = g (c.ι.app i a) + g (c.ι.app i b)
        rw [← map_add, hg, hg, hg, map_add]
      map_smul' := fun r a => by
        obtain ⟨i, a, rfl⟩ := Types.jointly_surjective_of_isColimit hc' a
        change g (r • c.ι.app i a) = r • g (c.ι.app i a)
        rw [← map_smul, hg, hg, map_smul] }

@[simp] theorem filteredDesc_ι {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : ∀ j, F.obj j →ₗ[R] N)
    (hf : ∀ {i j} (a : i ⟶ j) x, f j (F.map a x) = f i x)
    (i : J) (a : F.obj i) : filteredDesc hc f hf (c.ι.app i a) = f i a := by
  dsimp only [filteredDesc]
  obtain ⟨k, b, d, he⟩ := (Types.FilteredColimit.isColimit_eq_iff _
    (isColimitOfPreserves (forget (ModuleCat R)) hc)).mp
    (Classical.choose_spec (Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget (ModuleCat R)) hc) (c.ι.app i a))).choose_spec
  exact (hf b _).symm.trans ((congrArg (f k) he).trans (hf d _))

/-- The canonical comparison with M is an isomorphism, expressed by the
colimit universal property and an explicit linear equivalence of carriers. -/
theorem canonical_colimit : canonical_colimitType.{u,v} := by
  intro R _ M _ _ h
  letI := h
  let F := FreeTo.diagram (R := R) (M := M)
  apply Nonempty.intro
  apply isColimitOfReflects (forget (ModuleCat R))
  apply Types.FilteredColimit.isColimitOf' (F ⋙ forget (ModuleCat R))
  · intro m
    refine ⟨point m.down, ULift.up (fun _ => 1), ?_⟩
    apply ULift.ext
    change m.down = (1 : R) • m.down
    simp
  · intro X x y hxy
    have hv : X.toM (x.down - y.down) = 0 := by
      have he : X.toM x.down = X.toM y.down := congrArg ULift.down hxy
      simpa [map_sub] using sub_eq_zero.mpr he
    obtain ⟨Y, f, hf⟩ := eventually_zero X (x.down - y.down) hv
    refine ⟨Y, f, ?_⟩
    apply ULift.ext
    change f.linear x.down = f.linear y.down
    exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

/-- Flatness supplies the source's particular small filtered diagram. -/
theorem flat_filteredColimit : flat_filteredColimitType.{u,v,w} := by
  intro R _ M _ _ h
  have hrel := (FlatnessTests.flat_iff_finiteRelations R M).mp h
  letI := canonical_filtered R M hrel
  refine ⟨FreeTo R M, inferInstance, inferInstance, FreeTo.diagram,
    FreeTo.cocone, ⟨ULift.moduleEquiv⟩, ?_, canonical_colimit R M inferInstance⟩
  intro X
  exact ⟨X.rank, ⟨ULift.moduleEquiv.symm⟩⟩

/-- Filtered module colimits preserve objectwise injective maps. -/
theorem filtered_colimit_injective : filtered_colimit_injectiveType.{u,v} := by
  intro R _ J _ _ F G α c d hc hd f hα hf
  have hc' := isColimitOfPreserves (forget (ModuleCat R)) hc
  have hd' := isColimitOfPreserves (forget (ModuleCat R)) hd
  intro x y hxy
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc' x
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc' y
  have he : d.ι.app i (α.app i x) = d.ι.app j (α.app j y) := by
    have hi := congrArg (fun k : F.obj i ⟶ d.pt => k x) (hf i)
    have hj := congrArg (fun k : F.obj j ⟶ d.pt => k y) (hf j)
    exact hi.symm.trans (hxy.trans hj)
  obtain ⟨k, a, b, hab⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff _ hd').mp he
  apply (Types.FilteredColimit.isColimit_eq_iff _ hc').mpr
  refine ⟨k, a, b, hα k ?_⟩
  have ha := congrArg (fun q : F.obj i ⟶ G.obj k => q x) (α.naturality a)
  have hb := congrArg (fun q : F.obj j ⟶ G.obj k => q y) (α.naturality b)
  exact ha.trans (hab.trans hb.symm)

section TensorColimits
open P103.BalancedTensor

variable (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A]

/-- The balanced tensor functor with a fixed right module. -/
def tensorFunctor : ModuleCat.{v} R ⥤ AddCommGrpCat.{max v w} where
  obj B := AddCommGrpCat.of (Tensor R A B)
  map f := AddCommGrpCat.ofHom (map (LinearMap.id : A →ₗ[Rᵐᵒᵖ] A) f.hom)
  map_id B := by
    apply AddCommGrpCat.hom_ext
    exact map_id
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply hom_ext
    intros
    rfl

/-- A fixed right module acts by precomposition on additive maps. -/
@[instance_reducible] def additiveHomModule (N : Type*) [AddCommGroup N] :
    Module R (A →+ N) where
  smul r f :=
    { toFun a := f (MulOpposite.op r • a)
      map_zero' := by simp
      map_add' a b := by simp }
  one_smul f := by ext a; change f (MulOpposite.op (1 : R) • a) = f a; simp
  mul_smul r s f := by
    ext a
    change f (MulOpposite.op (r*s) • a) = f (MulOpposite.op s • (MulOpposite.op r • a))
    rw [← mul_smul, ← MulOpposite.op_mul]
  smul_zero r := by ext a; rfl
  smul_add r f g := by ext a; rfl
  add_smul r s f := by
    ext a
    change f (MulOpposite.op (r+s) • a) = f (MulOpposite.op r • a) + f (MulOpposite.op s • a)
    simp [add_smul]
  zero_smul f := by ext a; change f (MulOpposite.op (0 : R) • a) = 0; simp

variable {A}

/-- Curry a homomorphism from the balanced tensor. -/
def tensorCurry {B N : Type*} [AddCommGroup B] [Module R B] [AddCommGroup N]
    (f : Tensor R A B →+ N) :
    letI := additiveHomModule (R := R) A N
    B →ₗ[R] (A →+ N) := by
  letI := additiveHomModule (R := R) A N
  exact
    { toFun := fun b => f.comp (pairing.toBiadditive.flip b)
      map_add' := by intros; ext a; simp
      map_smul' := fun r b => by ext a; exact congrArg f (balance r a b).symm }

variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F}

/-- The tensor of a filtered-colimit cocone is a colimit cocone. -/
def tensorIsColimit (hc : IsColimit c) (A : Type w)
    [AddCommGroup A] [Module Rᵐᵒᵖ A] :
    IsColimit ((tensorFunctor (R := R) A).mapCocone c) := by
  let T := tensorFunctor (R := R) A
  let curried (d : Cocone (F ⋙ T)) (j : J) :
      letI := additiveHomModule (R := R) A d.pt
      F.obj j →ₗ[R] (A →+ d.pt) := tensorCurry (d.ι.app j).hom
  have compatible (d : Cocone (F ⋙ T)) {i j : J} (f : i ⟶ j) (x : F.obj i) :
      curried d j (F.map f x) = curried d i x := by
    ext a
    exact congrArg (fun q : T.obj (F.obj i) ⟶ d.pt => q (tmul R a x)) (d.w f)
  let descPair (d : Cocone (F ⋙ T)) : Pairing R (A := A) (B := c.pt) d.pt := by
    letI := additiveHomModule (R := R) A d.pt
    let g := filteredDesc hc (curried d) (compatible d)
    exact Pairing.ofFun (fun a b => g b a)
      (by intros; exact map_add _ _ _)
      (by intros; exact congrArg (fun f : A →+ d.pt => f _) (g.map_add _ _))
      (fun r a b => (congrArg (fun f : A →+ d.pt => f a) (g.map_smul r b)).symm)
  have hd (d : Cocone (F ⋙ T)) (j : J) (a : A) (m : F.obj j) :
      lift (descPair d) (tmul R a (c.ι.app j m)) = d.ι.app j (tmul R a m) := by
    letI := additiveHomModule (R := R) A d.pt
    change filteredDesc hc (curried d) (compatible d) (c.ι.app j m) a = _
    rw [filteredDesc_ι]
    rfl
  exact
    { desc := fun d => AddCommGrpCat.ofHom (lift (descPair d))
      fac := fun d j => by
        apply AddCommGrpCat.hom_ext
        apply hom_ext
        exact hd d j
      uniq := fun d f hf => by
        apply AddCommGrpCat.hom_ext
        apply hom_ext
        intro a m
        obtain ⟨j, m, rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitOfPreserves (forget (ModuleCat R)) hc) m
        exact (congrArg (fun q : T.obj (F.obj j) ⟶ d.pt => q (tmul R a m)) (hf j)).trans
          (hd d j a m).symm }

/-- The colimit comparisons retain the elementary tensor formulas. -/
theorem tensor_colimit : tensor_colimitType.{u,v,w} := by
  intro R _ J _ _ F c hc A _ _
  refine ⟨F ⋙ tensorFunctor A, (tensorFunctor A).mapCocone c,
    fun _ => AddEquiv.refl _, AddEquiv.refl _, ?_, ?_, ⟨tensorIsColimit hc A⟩⟩
  · intros; rfl
  · intros; rfl

end TensorColimits

section Converse
open P103.BalancedTensor

/-- Elementwise injectivity of filtered colimits of abelian groups. -/
theorem group_colimit_injective {J : Type v} [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ AddCommGrpCat.{max u v w}) (α : F ⟶ G)
    (c : Cocone F) (d : Cocone G) (hc : IsColimit c) (hd : IsColimit d)
    (f : c.pt ⟶ d.pt) (hα : ∀ j, Function.Injective (α.app j))
    (hf : ∀ j, c.ι.app j ≫ f = α.app j ≫ d.ι.app j) : Function.Injective f := by
  letI : PreservesFilteredColimitsOfSize.{v,v} (forget AddCommGrpCat.{max u v w}) :=
    preservesFilteredColimitsOfSize_shrink.{v,max u v w,v,max u v w} _
  have hc' := isColimitOfPreserves (forget AddCommGrpCat) hc
  have hd' := isColimitOfPreserves (forget AddCommGrpCat) hd
  intro x y hxy
  obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc' x
  obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit hc' y
  have he : d.ι.app i (α.app i x) = d.ι.app j (α.app j y) := by
    have hi := congrArg (fun k : F.obj i ⟶ d.pt => k x) (hf i)
    have hj := congrArg (fun k : F.obj j ⟶ d.pt => k y) (hf j)
    exact hi.symm.trans (hxy.trans hj)
  obtain ⟨k, a, b, hab⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hd').mp he
  apply (Types.FilteredColimit.isColimit_eq_iff _ hc').mpr
  refine ⟨k, a, b, hα k ?_⟩
  have ha := congrArg (fun q : F.obj i ⟶ G.obj k => q x) (α.naturality a)
  have hb := congrArg (fun q : F.obj j ⟶ G.obj k => q y) (α.naturality b)
  exact ha.trans (hab.trans hb.symm)

/-- Filtered colimits of flat modules are flat. The transition maps are
arbitrary, including maps with nonzero kernels. -/
theorem filtered_colimit_flat {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, Flat.{u,max u v,w} R (F.obj j)) : Flat.{u,max u v,w} R c.pt := by
  intro A B _ _ _ _ f hf H hH
  have hH' : H = map f LinearMap.id := hom_ext hH
  rw [hH']
  let TA := tensorFunctor (R := R) A
  let TB := tensorFunctor (R := R) B
  let α : F ⋙ TA ⟶ F ⋙ TB :=
    { app := fun j => AddCommGrpCat.ofHom (map f (LinearMap.id : F.obj j →ₗ[R] F.obj j))
      naturality := fun i j a => by
        apply AddCommGrpCat.hom_ext
        apply hom_ext
        intros
        rfl }
  exact group_colimit_injective.{u,v,w} (F ⋙ TA) (F ⋙ TB) α (TA.mapCocone c) (TB.mapCocone c)
    (tensorIsColimit hc A) (tensorIsColimit hc B)
    (AddCommGrpCat.ofHom (map f LinearMap.id))
    (fun j => hF j A B f hf _ (by intros; rfl))
    (fun j => by apply AddCommGrpCat.hom_ext; apply hom_ext; intros; rfl)

/-- A finite-free module at each vertex suffices for the preceding theorem. -/
theorem finiteFree_colimit_flat {J : Type v} [SmallCategory J] [IsFiltered J]
    {F : J ⥤ ModuleCat.{max u v} R} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, ∃ n : ℕ, Nonempty ((Fin n → R) ≃ₗ[R] F.obj j)) :
    Flat.{u,max u v,w} R c.pt := by
  apply filtered_colimit_flat hc
  intro j
  obtain ⟨n, ⟨e⟩⟩ := hF j
  have hp : Module.Projective R (F.obj j) := Module.Projective.of_equiv' e
  exact FlatnessTests.projective_flat R (F.obj j) hp

/-- Transfer flatness across a linear isomorphism, including a change of
carrier universe. -/
theorem flat_of_equiv {N : Type*} [AddCommGroup N] [Module R N]
    (e : N ≃ₗ[R] M) (hN : FiniteRelations R N) : Flat.{u,v,w} R M := by
  apply (FlatnessTests.flat_iff_finiteRelations R M).mpr
  intro n k x r hr
  have hr' (j) : ∑ i, r j i • e.symm (x i) = 0 := by
    simpa using congrArg e.symm (hr j)
  obtain ⟨l, y, s, hx, hs⟩ := hN n k (fun i => e.symm (x i)) r hr'
  refine ⟨l, fun a => e (y a), s, ?_, hs⟩
  intro i
  simpa using congrArg e (hx i)

/-- Govorov–Lazard over every unital ring, including the zero ring. -/
theorem flat_iff_filteredColimit : flat_iff_filteredColimitType.{u,v,w} := by
  intro R _ M _ _
  refine ⟨flat_filteredColimit R M, ?_⟩
  rintro ⟨J, hJ, hfilt, F, c, ⟨e⟩, hF, ⟨hc⟩⟩
  letI := hJ
  letI := hfilt
  have hflat := finiteFree_colimit_flat.{u,max u v,w} hc hF
  exact flat_of_equiv e ((FlatnessTests.flat_iff_finiteRelations R c.pt).mp hflat)

/-- The right-module version in the original orientation M⊗_R−. -/
theorem right_flat_iff_filteredColimit : right_flat_iff_filteredColimitType.{u,v,w} := by
  intro R _ M _ _
  exact (FlatnessTests.rightFlat_iff_opposite R M).trans (flat_iff_filteredColimit Rᵐᵒᵖ M)

/-- Combine the new colimit characterization with the accepted finite tests. -/
theorem characterizations : characterizationsType.{u,v,w} := by
  intro R _ M _ _
  exact ⟨FlatnessTests.flat_iff_exact R M, FlatnessTests.flat_iff_idealTest R M,
    FlatnessTests.flat_iff_finiteRelations R M, flat_iff_filteredColimit R M⟩

end Converse

end P103.Ch02.GovorovLazard
