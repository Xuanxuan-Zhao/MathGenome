import MathGenome.Internal.AlgebraCore.Specs.P103.Ch10.HorseshoeNaturality
import MathGenome.Internal.AlgebraCore.P103.Ch10.Comparison
import MathGenome.Internal.AlgebraCore.P103.Ch10.HomologySequence
import MathGenome.Internal.AlgebraCore.P103.Ch10.Horseshoe

noncomputable section
namespace P103.Ch10.HorseshoeNaturality
open CategoryTheory
open P103.Specs.Ch10 P103.Specs.Ch10.Complexes P103.Specs.Ch10.HomologySequence
open P103.Specs.Ch10.HorseshoeNaturality
universe u v w x y z t q

theorem split_map :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {ι : Type w} {c : ComplexShape ι} {A B C : HomologicalComplex D c}
    (F : D ⥤ E) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → DegreewiseSplit
      ((F.mapHomologicalComplex c).map i) ((F.mapHomologicalComplex c).map p) := by
  intro D _ _ E _ _ ι c A B C F _ i p hs n
  obtain ⟨h, ⟨s⟩⟩ := hs n
  refine ⟨?_, ⟨s.map F⟩⟩
  change F.map (i.f n) ≫ F.map (p.f n) = 0
  rw [← F.map_comp, h, F.map_zero]

theorem split_op :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι} {A B C : HomologicalComplex D c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseSplit i p →
    DegreewiseSplit ((HomologicalComplex.opFunctor D c).map p.op)
      ((HomologicalComplex.opFunctor D c).map i.op) := by
  intro D _ _ ι c A B C i p hs n
  obtain ⟨h, ⟨s⟩⟩ := hs n
  exact ⟨by change (p.f n).op ≫ (i.f n).op = 0; rw [← op_comp, h]; simp, ⟨s.op⟩⟩

theorem split_exact :
  ∀ {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseSplit i p → DegreewiseExact i p := by
  intro R _ ι c A B C i p hs n
  obtain ⟨h, ⟨s⟩⟩ := hs n
  exact ⟨(ModuleCat.mono_iff_injective _).mp s.mono_f,
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp s.exact,
    (ModuleCat.epi_iff_surjective _).mp s.epi_g⟩

/-- Product coordinates provide a compatible section and retraction; these
need not commute with the differentials. -/
theorem splitting_of_product {R : Type u} [Ring R] {U V W : ModuleCat.{v} R}
    (e : V ≃ₗ[R] U × W) (f : U ⟶ V) (g : V ⟶ W)
    (hf : ∀ x, e (f.hom x) = (x, 0)) (hg : ∀ x, g.hom x = (e x).2) :
    ∃ h : f ≫ g = 0, Nonempty (ShortComplex.mk f g h).Splitting := by
  have h : f ≫ g = 0 := by
    apply ModuleCat.hom_ext
    ext x
    change g.hom (f.hom x) = 0
    rw [hg, hf]
  refine ⟨h, ⟨{
    r := ModuleCat.ofHom ((LinearMap.fst R U W).comp e.toLinearMap)
    s := ModuleCat.ofHom (e.symm.toLinearMap.comp (LinearMap.inr R U W))
    f_r := ?_
    s_g := ?_
    id := ?_
  }⟩⟩
  · apply ModuleCat.hom_ext
    ext x
    change (e (f.hom x)).1 = x
    rw [hf]
  · apply ModuleCat.hom_ext
    ext x
    change g.hom (e.symm (0, x)) = x
    rw [hg, e.apply_symm_apply]
  · apply ModuleCat.hom_ext
    ext x
    change f.hom (e x).1 + e.symm (0, g.hom x) = x
    apply e.injective
    rw [map_add, hf, e.apply_symm_apply, hg]
    exact Prod.ext (add_zero _) (zero_add _)

theorem projective_split :
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (H : Horseshoe.ProjectiveData i p L N), DegreewiseSplit H.inclusion H.projection := by
  intro R _ A B C _ _ _ _ _ _ i p L N H n
  exact splitting_of_product (H.term n) _ _ (H.inclusion_apply n) (H.projection_apply n)

theorem injective_split :
  ∀ (R : Type u) [Ring R] (A B C : Type v)
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (H : Horseshoe.InjectiveData i p L N), DegreewiseSplit H.inclusion H.projection := by
  intro R _ A B C _ _ _ _ _ _ i p L N H n
  exact splitting_of_product (H.term n) _ _ (H.inclusion_apply n) (H.projection_apply n)

theorem applied_sequence :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.Rel n m →
    ∃! δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m,
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ ∧
      SequenceExact ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ := by
  intro D _ _ R _ ι c A B C F _ i p hs n m hnm
  exact P103.Ch10.HomologySequence.sequence _ _ (split_exact _ _ (split_map F i p hs)) n m hnm

theorem applied_naturality :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj C') n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A') m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (homologyMap ((F.mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap ((F.mapHomologicalComplex c).map γ) n) := by
  intro D _ _ R _ ι c A B C A' B' C' F _ i p i' p' α β γ hi hp hs hs' n m hnm δ ε hδ hε
  let G := F.mapHomologicalComplex c
  have hi' : G.map i ≫ G.map β = G.map α ≫ G.map i' := by
    simpa only [Functor.map_comp] using congrArg G.map hi
  have hp' : G.map p ≫ G.map γ = G.map β ≫ G.map p' := by
    simpa only [Functor.map_comp] using congrArg G.map hp
  exact (P103.Ch10.HomologySequence.naturality _ _ _ _ _ _ _ hi' hp'
    (split_exact _ _ (split_map F i p hs)) (split_exact _ _ (split_map F i' p' hs'))
    n m hnm δ ε hδ hε).2.2.1

theorem contravariant_sequence :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.symm.Rel n m →
    ∃! δ : Homology ((F.mapHomologicalComplex c.symm).obj A.op) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c.symm).obj C.op) m,
      Connecting
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ ∧
      SequenceExact
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ := by
  intro D _ _ R _ ι c A B C F _ i p hs n m hnm
  exact applied_sequence F _ _ (split_op i p hs) n m hnm

theorem coherent_connecting :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (F : E ⥤ ModuleCat.{q} R) [F.Additive], CoherentConnecting I K L F := by
  intro D _ _ E _ _ R _ ι c I K L F _
  intro n m hnm Cn Cm A B C A' B' C' PA PB PC QA QB QC i p i' p' a b cc α β γ ha _hb hc
    hi hp hs hs' δ ε hδ hε
  rw [Cm.map_eq PA QA a α ha, Cn.map_eq PC QC cc γ hc]
  exact applied_naturality F i p i' p' α β γ hi hp hs hs' n m hnm δ ε hδ hε

theorem coherent_transport :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
    (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
    (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
    (F : E ⥤ ModuleCat.{q} R) [F.Additive], CoherentTransport I K L F := by
  intro D _ _ E _ _ R _ ι c I K L F _
  intro n m hnm Cn Cm A B C PA QA PB QB PC QC i p i' p' α β γ ha hb hc
    hi hp hs hs' δ ε hδ hε
  rw [Cm.comparison_hom, Cn.comparison_hom]
  exact coherent_connecting I K L F n m hnm Cn Cm PA PB PC QA QB QC i p i' p'
    (𝟙 A) (𝟙 B) (𝟙 C) α β γ ha hb hc hi hp hs hs' δ ε hδ hε

section DiagramAlgebra
variable {R : Type u} [Ring R]

/-- Coordinates for one split row. No compatibility across degrees is imposed. -/
structure SplitRow (U V W : Type*) [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [Module R U] [Module R V] [Module R W] where
  e : V ≃ₗ[R] U × W
  i : U →ₗ[R] V
  p : V →ₗ[R] W
  hi : ∀ x, e (i x) = (x, 0)
  hp : ∀ x, p x = (e x).2

namespace SplitRow
variable {U V W U' V' W' : Type*}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W']
  [Module R U] [Module R V] [Module R W]
  [Module R U'] [Module R V'] [Module R W']
variable (S : SplitRow (R := R) U V W) (T : SplitRow (R := R) U' V' W')
def s : W →ₗ[R] V := S.e.symm.toLinearMap.comp (LinearMap.inr R U W)
def r : V →ₗ[R] U := (LinearMap.fst R U W).comp S.e.toLinearMap
@[simp] theorem r_i (x : U) : S.r (S.i x) = x := by simp [r, S.hi]
@[simp] theorem p_i (x : U) : S.p (S.i x) = 0 := by rw [S.hp, S.hi]
@[simp] theorem p_s (x : W) : S.p (S.s x) = x := by simp [s, S.hp]
theorem decompose (x : V) : S.i (S.r x) + S.s (S.p x) = x := by
  apply S.e.injective
  simp only [map_add, S.hi, s, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.inr_apply, LinearEquiv.apply_symm_apply, r, LinearMap.fst_apply, S.hp]
  exact Prod.ext (add_zero _) (zero_add _)
theorem injective : Function.Injective S.i := by
  intro x y h
  simpa using congrArg S.r h
theorem surjective : Function.Surjective S.p := fun x => ⟨S.s x, S.p_s x⟩
theorem exact : Function.Exact S.i S.p := by
  intro x
  constructor
  · intro hx
    refine ⟨S.r x, ?_⟩
    simpa [hx] using S.decompose x
  · rintro ⟨y, rfl⟩
    exact S.p_i y

def diagonal (a : U →ₗ[R] U') (c : W →ₗ[R] W') : V →ₗ[R] V' :=
  (T.i.comp (a.comp S.r)) + (T.s.comp (c.comp S.p))
@[simp] theorem diagonal_i (a : U →ₗ[R] U') (c : W →ₗ[R] W') (x : U) :
    S.diagonal T a c (S.i x) = T.i (a x) := by simp [diagonal]
@[simp] theorem p_diagonal (a : U →ₗ[R] U') (c : W →ₗ[R] W') (x : V) :
    T.p (S.diagonal T a c x) = c (S.p x) := by simp [diagonal]

/-- Complete a square with prescribed maps on both ends. Exactness of the
combined kernel is the sole condition on the preceding target row. -/
theorem lift_square [Module.Projective R W]
    {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module R E] [Module R F]
    (d : V' →ₗ[R] E) (f : U' →ₗ[R] E) (k : E →ₗ[R] F)
    (hf : Function.Exact f k)
    (a : U →ₗ[R] U') (c : W →ₗ[R] W') (b : V →ₗ[R] E)
    (hdi : d.comp T.i = f)
    (hbi : b.comp S.i = f.comp a)
    (hbc : k.comp b = (k.comp d).comp (S.diagonal T a c)) :
    ∃ t : V →ₗ[R] V', d.comp t = b ∧ t.comp S.i = T.i.comp a ∧
      T.p.comp t = c.comp S.p := by
  let D := S.diagonal T a c
  let z := (b - d.comp D).comp S.s
  have hz : k.comp z = 0 := by
    dsimp [z]
    rw [← LinearMap.comp_assoc, LinearMap.comp_sub]
    change (k.comp b - (k.comp d).comp D).comp S.s = 0
    rw [hbc, sub_self, LinearMap.zero_comp]
  obtain ⟨l, hl⟩ := P103.Ch10.Horseshoe.lift_exact f k hf z hz
  let t := D + T.i.comp (l.comp S.p)
  refine ⟨t, ?_, ?_, ?_⟩
  · ext x
    have he : (b - d.comp D) (S.i (S.r x)) = 0 := by
      change b (S.i (S.r x)) - d (D (S.i (S.r x))) = 0
      rw [show b (S.i (S.r x)) = f (a (S.r x)) from LinearMap.congr_fun hbi _,
        diagonal_i, show d (T.i (a (S.r x))) = f (a (S.r x)) from
          LinearMap.congr_fun hdi _, sub_self]
    have hz' : (b - d.comp D) x = z (S.p x) := by
      calc
        (b - d.comp D) x = (b - d.comp D) (S.i (S.r x) + S.s (S.p x)) :=
          congrArg (b - d.comp D) (S.decompose x).symm
        _ = z (S.p x) := by rw [map_add, he, zero_add]; rfl
    have hl' := LinearMap.congr_fun hl (S.p x)
    change f (l (S.p x)) = z (S.p x) at hl'
    change d (D x + T.i (l (S.p x))) = b x
    rw [map_add, show d (T.i (l (S.p x))) = f (l (S.p x)) from
      LinearMap.congr_fun hdi _, hl', ← hz']
    change d (D x) + (b x - d (D x)) = b x
    abel
  · ext x
    simp [t, D]
  · ext x
    simp [t, D]
end SplitRow

/-- A kernel inside a short exact row is the simultaneous kernel of its
projection and the preceding differential. -/
theorem exact_kernel_pair {U V W X Y Z : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R U] [Module R V] [Module R W]
    [Module R X] [Module R Y] [Module R Z]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) (i : V →ₗ[R] X) (p : X →ₗ[R] Y)
    (j : W →ₗ[R] Z) (d : X →ₗ[R] Z)
    (hf : Function.Exact f g) (hi : Function.Exact i p) (hj : Function.Injective j)
    (hd : d.comp i = j.comp g) : Function.Exact (i.comp f) (p.prod d) := by
  intro x
  constructor
  · intro hx
    have hp : p x = 0 := congrArg Prod.fst hx
    have hdx : d x = 0 := congrArg Prod.snd hx
    obtain ⟨v, rfl⟩ := (hi x).mp hp
    have hg : g v = 0 := by
      apply hj
      simpa only [LinearMap.comp_apply, map_zero] using
        (LinearMap.congr_fun hd v).symm.trans hdx
    obtain ⟨u, hu⟩ := (hf v).mp hg
    exact ⟨u, congrArg i hu⟩
  · rintro ⟨u, rfl⟩
    apply Prod.ext
    · exact hi.apply_apply_eq_zero _
    · change d (i (f u)) = 0
      rw [show d (i (f u)) = j (g (f u)) from LinearMap.congr_fun hd _,
        hf.apply_apply_eq_zero, map_zero]
end DiagramAlgebra

namespace SplitRow
variable {R : Type u} [Ring R]
variable {U V W V' W' : Type*} {U' : Type t}
  [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
  [AddCommGroup U'] [AddCommGroup V'] [AddCommGroup W']
  [Module R U] [Module R V] [Module R W]
  [Module R U'] [Module R V'] [Module R W']
variable (S : SplitRow (R := R) U V W) (T : SplitRow (R := R) U' V' W')

theorem extend_square [Module.Injective R U'] [Small.{t} R]
    {E Z : Type*} [AddCommGroup E] [AddCommGroup Z] [Module R E] [Module R Z]
    (d : E →ₗ[R] V) (f : Z →ₗ[R] E) (hf : Function.Exact f (S.p.comp d))
    (a : U →ₗ[R] U') (c : W →ₗ[R] W') (b : E →ₗ[R] V')
    (hbc : T.p.comp b = c.comp (S.p.comp d))
    (hr : (b - (S.diagonal T a c).comp d).comp f = 0) :
    ∃ t : V →ₗ[R] V', t.comp d = b ∧ t.comp S.i = T.i.comp a ∧
      T.p.comp t = c.comp S.p := by
  let D := S.diagonal T a c
  let z := b - D.comp d
  have hz : (T.r.comp z).comp f = 0 := by
    rw [LinearMap.comp_assoc, hr, LinearMap.comp_zero]
  obtain ⟨l, hl⟩ := P103.Ch10.Horseshoe.extend_exact f (S.p.comp d) hf (T.r.comp z) hz
  let t := D + T.i.comp (l.comp S.p)
  refine ⟨t, ?_, ?_, ?_⟩
  · ext x
    have hp : T.p (z x) = 0 := by
      dsimp [z]
      rw [map_sub, p_diagonal]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hbc x)
    have hz' : T.i (T.r (z x)) = z x := by
      simpa [hp] using T.decompose (z x)
    have hl' : l (S.p (d x)) = T.r (z x) := LinearMap.congr_fun hl x
    change D (d x) + T.i (l (S.p (d x))) = b x
    rw [hl', hz']
    change D (d x) + (b x - D (d x)) = b x
    abel
  · ext x
    simp [t, D]
  · ext x
    simp [t, D]
end SplitRow

/-- The dual simultaneous-kernel calculation, expressed as a sum of images. -/
theorem exact_image_sum {R : Type u} [Ring R] {U V W X Y Z : Type*}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [Module R U] [Module R V] [Module R W]
    [Module R X] [Module R Y] [Module R Z]
    (i : U →ₗ[R] V) (p : V →ₗ[R] W) (f : X →ₗ[R] V) (q : X →ₗ[R] Y)
    (g : Y →ₗ[R] W) (d : W →ₗ[R] Z)
    (hi : Function.Exact i p) (hg : Function.Exact g d) (hq : Function.Surjective q)
    (hf : p.comp f = g.comp q) : Function.Exact (i.coprod f) (d.comp p) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (hg (p x)).mp hx
    obtain ⟨z, hz⟩ := hq y
    have hp : p (x - f z) = 0 := by
      rw [map_sub, show p (f z) = g (q z) from LinearMap.congr_fun hf z, hz, hy, sub_self]
    obtain ⟨a, ha⟩ := (hi _).mp hp
    refine ⟨(a, z), ?_⟩
    change i a + f z = x
    rw [ha]
    abel
  · rintro ⟨⟨a, z⟩, rfl⟩
    change d (p (i a + f z)) = 0
    rw [map_add, hi.apply_apply_eq_zero, zero_add,
      show p (f z) = g (q z) from LinearMap.congr_fun hf z, hg.apply_apply_eq_zero]

namespace ProjectiveDiagram
open P103.Specs.Ch10.ProjectiveResolutions
open P103.Ch10.Horseshoe.Projective
variable {R : Type u} [Ring R]
variable {A B C A' B' C' : ModuleCat.{v} R}
variable {i : A ⟶ B} {p : B ⟶ C} {i' : A' ⟶ B'} {p' : B' ⟶ C'}
variable {L : Resolution R A} {N : Resolution R C}
  {L' : Resolution R A'} {N' : Resolution R C'}
variable (H : Horseshoe.ProjectiveData i.hom p.hom L N)
  (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')

def row (n : ℕ) : SplitRow (R := R) (L.complex.X n) (H.middle.complex.X n)
    (N.complex.X n) :=
  ⟨H.term n, (H.inclusion.f n).hom, (H.projection.f n).hom,
    H.inclusion_apply n, H.projection_apply n⟩

variable (α : L.complex ⟶ L'.complex) (γ : N.complex ⟶ N'.complex)

structure Entry (n : ℕ) where
  b : H.middle.complex.X n →ₗ[R] H'.middle.complex.X n
  left : b.comp (H.inclusion.f n).hom = (H'.inclusion.f n).hom.comp (α.f n).hom
  right : (H'.projection.f n).hom.comp b = (γ.f n).hom.comp (H.projection.f n).hom
  cycle : Cycle H'.middle n (b.comp (δ H.middle n))

/-- A single recursive step, parameterized by the preceding differential. -/
theorem extend (hN : N.IsProjective) (n : ℕ) (e : Entry H H' α γ n)
    {Z : Type*} [AddCommGroup Z] [Module R Z]
    (w : H'.middle.complex.X n →ₗ[R] Z)
    (he : Function.Exact
      ((H'.inclusion.f n).hom.comp (δ L' n)) ((H'.projection.f n).hom.prod w))
    (hw : w.comp (δ H'.middle n) = 0)
    (hr : w.comp (e.b.comp (δ H.middle n)) = 0) :
    ∃ t : H.middle.complex.X (n + 1) →ₗ[R] H'.middle.complex.X (n + 1),
      (δ H'.middle n).comp t = e.b.comp (δ H.middle n) ∧
      t.comp (H.inclusion.f (n + 1)).hom =
        (H'.inclusion.f (n + 1)).hom.comp (α.f (n + 1)).hom ∧
      (H'.projection.f (n + 1)).hom.comp t =
        (γ.f (n + 1)).hom.comp (H.projection.f (n + 1)).hom := by
  letI := hN (n + 1)
  apply (row H (n + 1)).lift_square (row H' (n + 1))
    (δ H'.middle n) ((H'.inclusion.f n).hom.comp (δ L' n))
    ((H'.projection.f n).hom.prod w) he
    (α.f (n + 1)).hom (γ.f (n + 1)).hom (e.b.comp (δ H.middle n))
  · exact congrArg ModuleCat.Hom.hom (H'.inclusion.comm (n + 1) n)
  · change (e.b.comp (δ H.middle n)).comp (H.inclusion.f (n + 1)).hom = _
    rw [LinearMap.comp_assoc,
      show (δ H.middle n).comp (H.inclusion.f (n + 1)).hom =
          (H.inclusion.f n).hom.comp (δ L n) from
        congrArg ModuleCat.Hom.hom (H.inclusion.comm (n + 1) n),
      ← LinearMap.comp_assoc, e.left, LinearMap.comp_assoc,
      ← show (δ L' n).comp (α.f (n + 1)).hom =
        (α.f n).hom.comp (δ L n) from congrArg ModuleCat.Hom.hom (α.comm (n + 1) n)]
    rfl
  · apply LinearMap.ext
    intro x
    apply Prod.ext
    · change (H'.projection.f n).hom (e.b ((δ H.middle n) x)) =
        (H'.projection.f n).hom ((δ H'.middle n)
          ((row H (n + 1)).diagonal (row H' (n + 1))
            (α.f (n + 1)).hom (γ.f (n + 1)).hom x))
      have h1 := LinearMap.congr_fun e.right ((δ H.middle n) x)
      have h2 := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H.projection.comm (n + 1) n)) x).symm
      have h3 := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (H'.projection.comm (n + 1) n))
        ((row H (n + 1)).diagonal (row H' (n + 1))
            (α.f (n + 1)).hom (γ.f (n + 1)).hom x)).symm
      have h4 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (γ.comm (n + 1) n))
        ((H.projection.f (n + 1)).hom x)
      change (H.projection.f n).hom ((δ H.middle n) x) =
        (δ N n) ((H.projection.f (n + 1)).hom x) at h2
      change (H'.projection.f n).hom ((δ H'.middle n) _) =
        (δ N' n) ((H'.projection.f (n + 1)).hom _) at h3
      simp only [LinearMap.comp_apply] at h1
      rw [h1, h2, h3]
      change (γ.f n).hom ((δ N n) _) = (δ N' n)
        ((row H' (n + 1)).p ((row H (n + 1)).diagonal (row H' (n + 1))
          (α.f (n + 1)).hom (γ.f (n + 1)).hom x))
      rw [SplitRow.p_diagonal]
      exact h4.symm
    · exact (LinearMap.congr_fun hr x).trans (LinearMap.congr_fun hw _).symm

theorem next_exists (hi' : Function.Injective i'.hom) (hN : N.IsProjective) (n : ℕ) (e : Entry H H' α γ n) :
    ∃ t : H.middle.complex.X (n + 1) →ₗ[R] H'.middle.complex.X (n + 1),
      (δ H'.middle n).comp t = e.b.comp (δ H.middle n) ∧
      t.comp (H.inclusion.f (n + 1)).hom =
        (H'.inclusion.f (n + 1)).hom.comp (α.f (n + 1)).hom ∧
      (H'.projection.f (n + 1)).hom.comp t =
        (γ.f (n + 1)).hom.comp (H.projection.f (n + 1)).hom := by
  cases n with
  | zero =>
    apply extend H H' α γ hN 0 e H'.middle.ε
    · exact exact_kernel_pair _ _ _ _ i'.hom _
        (LinearMap.exact_iff.mpr L'.exact_zero.symm) (row H' 0).exact
        hi' H'.augmentation_inclusion
    · exact δ_augmentation H'.middle
    · exact e.cycle
  | succ n =>
    apply extend H H' α γ hN (n + 1) e (δ H'.middle n)
    · exact exact_kernel_pair _ _ _ _ (H'.inclusion.f n).hom _
        (LinearMap.exact_iff.mpr (L'.exact_succ n).symm) (row H' (n + 1)).exact
        (row H' n).injective (congrArg ModuleCat.Hom.hom (H'.inclusion.comm (n + 1) n))
    · exact δ_square H'.middle n
    · exact e.cycle

variable {H H' α γ}

def next (hi' : Function.Injective i'.hom) (hN : N.IsProjective)
    (n : ℕ) (e : Entry H H' α γ n) : Entry H H' α γ (n + 1) := by
  let t := (next_exists H H' α γ hi' hN n e).choose
  have ht := (next_exists H H' α γ hi' hN n e).choose_spec
  refine ⟨t, ht.2.1, ht.2.2, ?_⟩
  change (δ H'.middle n).comp (t.comp (δ H.middle (n + 1))) = 0
  rw [← LinearMap.comp_assoc, ht.1, LinearMap.comp_assoc, δ_square, LinearMap.comp_zero]

theorem next_comm (hi' : Function.Injective i'.hom) (hN : N.IsProjective)
    (n : ℕ) (e : Entry H H' α γ n) :
    (δ H'.middle n).comp (next hi' hN n e).b = e.b.comp (δ H.middle n) := by
  unfold next
  exact (next_exists H H' α γ hi' hN n e).choose_spec.1

theorem initial (he' : Function.Exact i'.hom p'.hom) (hN : N.IsProjective)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hab : i ≫ b = a ≫ i') (hbc : p ≫ c = b ≫ p')
    (ha : Comparison.ChainLift L L' a.hom α) (hc : Comparison.ChainLift N N' c.hom γ) :
    ∃ e : Entry H H' α γ 0, H'.middle.ε.comp e.b = b.hom.comp H.middle.ε := by
  letI := hN 0
  obtain ⟨t, ht, hl, hr⟩ := (row H 0).lift_square (row H' 0)
    H'.middle.ε (i'.hom.comp L'.ε) p'.hom
    (L'.surjective.comp_exact_iff_exact.mpr he')
    (α.f 0).hom (γ.f 0).hom (b.hom.comp H.middle.ε)
    H'.augmentation_inclusion (by
      change (b.hom.comp H.middle.ε).comp (H.inclusion.f 0).hom = _
      rw [LinearMap.comp_assoc, H.augmentation_inclusion, ← LinearMap.comp_assoc,
        show b.hom.comp i.hom = i'.hom.comp a.hom from congrArg ModuleCat.Hom.hom hab,
        LinearMap.comp_assoc, ← ha]
      rfl) (by
      ext x
      have hs := LinearMap.congr_fun H.augmentation_projection x
      have ht := LinearMap.congr_fun H'.augmentation_projection
        ((row H 0).diagonal (row H' 0) (α.f 0).hom (γ.f 0).hom x)
      have hbc' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hbc) (H.middle.ε x)
      change c.hom (p.hom (H.middle.ε x)) = p'.hom (b.hom (H.middle.ε x)) at hbc'
      change N.ε ((H.projection.f 0).hom x) = p.hom (H.middle.ε x) at hs
      change N'.ε ((H'.projection.f 0).hom _) = p'.hom (H'.middle.ε _) at ht
      change p'.hom (b.hom (H.middle.ε x)) = p'.hom (H'.middle.ε _)
      rw [← hbc', ← hs, ← ht]
      change c.hom (N.ε ((H.projection.f 0).hom x)) =
        N'.ε ((row H' 0).p ((row H 0).diagonal (row H' 0)
          (α.f 0).hom (γ.f 0).hom x))
      rw [SplitRow.p_diagonal]
      exact (LinearMap.congr_fun hc _).symm)
  refine ⟨⟨t, hl, hr, ?_⟩, ht⟩
  change H'.middle.ε.comp (t.comp (δ H.middle 0)) = 0
  rw [← LinearMap.comp_assoc, ht, LinearMap.comp_assoc, δ_augmentation, LinearMap.comp_zero]

variable (hi' : Function.Injective i'.hom) (hN : N.IsProjective)
  (e : Entry H H' α γ 0)

def entries : ∀ n, Entry H H' α γ n
  | 0 => e
  | n + 1 => next hi' hN n (entries n)

def map : H.middle.complex ⟶ H'.middle.complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (entries hi' hN e n).b) (fun n => by
    apply ModuleCat.hom_ext
    exact next_comm hi' hN n (entries hi' hN e n))

theorem map_left : H.inclusion ≫ map hi' hN e = α ≫ H'.inclusion := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (entries hi' hN e n).left

theorem map_right : H.projection ≫ γ = map hi' hN e ≫ H'.projection := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (entries hi' hN e n).right.symm

end ProjectiveDiagram

namespace InjectiveDiagram
open P103.Specs.Ch10.InjectiveResolutions
open P103.Ch10.Horseshoe.Injective
variable {R : Type u} [Ring R]
variable {A B C A' B' C' : ModuleCat.{v} R}
variable {i : A ⟶ B} {p : B ⟶ C} {i' : A' ⟶ B'} {p' : B' ⟶ C'}
variable {L : Resolution R A} {N : Resolution R C}
  {L' : Resolution R A'} {N' : Resolution R C'}
variable (H : Horseshoe.InjectiveData i.hom p.hom L N)
  (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')

def row (n : ℕ) : SplitRow (R := R) (L.complex.X n) (H.middle.complex.X n)
    (N.complex.X n) :=
  ⟨H.term n, (H.inclusion.f n).hom, (H.projection.f n).hom,
    H.inclusion_apply n, H.projection_apply n⟩

variable (α : L.complex ⟶ L'.complex) (γ : N.complex ⟶ N'.complex)

structure Entry (n : ℕ) where
  b : H.middle.complex.X n →ₗ[R] H'.middle.complex.X n
  left : b.comp (H.inclusion.f n).hom = (H'.inclusion.f n).hom.comp (α.f n).hom
  right : (H'.projection.f n).hom.comp b = (γ.f n).hom.comp (H.projection.f n).hom
  cycle : Cocycle H.middle n ((δ H'.middle n).comp b)

theorem extend (n : ℕ) (e : Entry H H' α γ n)
    {Z : Type*} [AddCommGroup Z] [Module R Z]
    (w : Z →ₗ[R] H.middle.complex.X n)
    (he : Function.Exact ((H.inclusion.f n).hom.coprod w)
      ((H.projection.f (n + 1)).hom.comp (δ H.middle n)))
    (hw : (δ H.middle n).comp w = 0)
    (hr : ((δ H'.middle n).comp e.b).comp w = 0) :
    ∃ t : H.middle.complex.X (n + 1) →ₗ[R] H'.middle.complex.X (n + 1),
      t.comp (δ H.middle n) = (δ H'.middle n).comp e.b ∧
      t.comp (H.inclusion.f (n + 1)).hom =
        (H'.inclusion.f (n + 1)).hom.comp (α.f (n + 1)).hom ∧
      (H'.projection.f (n + 1)).hom.comp t =
        (γ.f (n + 1)).hom.comp (H.projection.f (n + 1)).hom := by
  letI := L'.injectiveTerm (n + 1)
  apply (row H (n + 1)).extend_square (row H' (n + 1))
    (δ H.middle n) ((H.inclusion.f n).hom.coprod w) he
    (α.f (n + 1)).hom (γ.f (n + 1)).hom ((δ H'.middle n).comp e.b)
  · ext x
    have h1 := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (H'.projection.comm n (n + 1))) (e.b x)).symm
    have h2 := LinearMap.congr_fun e.right x
    have h3 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (γ.comm n (n + 1))) ((H.projection.f n).hom x)
    have h4 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (H.projection.comm n (n + 1))) x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2 h3 h4 ⊢
    exact h1.trans ((congrArg (δ N' n) h2).trans
      (h3.trans (congrArg (γ.f (n + 1)).hom h4)))
  · let D := (row H (n + 1)).diagonal (row H' (n + 1))
      (α.f (n + 1)).hom (γ.f (n + 1)).hom
    let z := (δ H'.middle n).comp e.b - D.comp (δ H.middle n)
    have hzi : z.comp (H.inclusion.f n).hom = 0 := by
      ext x
      have h1 := LinearMap.congr_fun e.left x
      have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (H'.inclusion.comm n (n + 1))) ((α.f n).hom x)
      have h3 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (α.comm n (n + 1))) x
      have h4 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (H.inclusion.comm n (n + 1))) x
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2 h3 h4
      change (δ H'.middle n) (e.b ((H.inclusion.f n).hom x)) -
        D ((δ H.middle n) ((H.inclusion.f n).hom x)) = 0
      rw [h1, h2, h3, h4]
      change _ - (row H (n + 1)).diagonal (row H' (n + 1))
        (α.f (n + 1)).hom (γ.f (n + 1)).hom
        ((row H (n + 1)).i ((δ L n) x)) = 0
      rw [SplitRow.diagonal_i]
      exact sub_self _
    have hzw : z.comp w = 0 := by
      dsimp [z]
      rw [LinearMap.sub_comp, hr, LinearMap.comp_assoc, hw, LinearMap.comp_zero, sub_self]
    apply LinearMap.ext
    rintro ⟨x, y⟩
    change z ((H.inclusion.f n).hom x + w y) = 0
    rw [map_add, show z ((H.inclusion.f n).hom x) = 0 from LinearMap.congr_fun hzi x,
      show z (w y) = 0 from LinearMap.congr_fun hzw y, add_zero]

theorem next_exists (hp : Function.Surjective p.hom) (n : ℕ) (e : Entry H H' α γ n) :
    ∃ t : H.middle.complex.X (n + 1) →ₗ[R] H'.middle.complex.X (n + 1),
      t.comp (δ H.middle n) = (δ H'.middle n).comp e.b ∧
      t.comp (H.inclusion.f (n + 1)).hom =
        (H'.inclusion.f (n + 1)).hom.comp (α.f (n + 1)).hom ∧
      (H'.projection.f (n + 1)).hom.comp t =
        (γ.f (n + 1)).hom.comp (H.projection.f (n + 1)).hom := by
  cases n with
  | zero =>
    apply extend H H' α γ 0 e H.middle.η
    · rw [← show (δ N 0).comp (H.projection.f 0).hom =
          (H.projection.f 1).hom.comp (δ H.middle 0) from
        congrArg ModuleCat.Hom.hom (H.projection.comm 0 1)]
      exact exact_image_sum _ _ _ p.hom _ _ (row H 0).exact N.exact_zero hp
        H.augmentation_projection
    · exact δ_augmentation H.middle
    · exact e.cycle
  | succ n =>
    apply extend H H' α γ (n + 1) e (δ H.middle n)
    · rw [← show (δ N (n + 1)).comp (H.projection.f (n + 1)).hom =
          (H.projection.f (n + 2)).hom.comp (δ H.middle (n + 1)) from
        congrArg ModuleCat.Hom.hom (H.projection.comm (n + 1) (n + 2))]
      exact exact_image_sum _ _ _ (H.projection.f n).hom _ _ (row H (n + 1)).exact
        (N.exact_succ n) (row H n).surjective
        (congrArg ModuleCat.Hom.hom (H.projection.comm n (n + 1))).symm
    · exact δ_square H.middle n
    · exact e.cycle

variable {H H' α γ}
def next (hp : Function.Surjective p.hom) (n : ℕ) (e : Entry H H' α γ n) :
    Entry H H' α γ (n + 1) := by
  let t := (next_exists H H' α γ hp n e).choose
  have ht := (next_exists H H' α γ hp n e).choose_spec
  refine ⟨t, ht.2.1, ht.2.2, ?_⟩
  change ((δ H'.middle (n + 1)).comp t).comp (δ H.middle n) = 0
  rw [LinearMap.comp_assoc, ht.1, ← LinearMap.comp_assoc, δ_square, LinearMap.zero_comp]

theorem next_comm (hp : Function.Surjective p.hom) (n : ℕ) (e : Entry H H' α γ n) :
    (next hp n e).b.comp (δ H.middle n) = (δ H'.middle n).comp e.b :=
  (next_exists H H' α γ hp n e).choose_spec.1

theorem initial (he : Function.Exact i.hom p.hom)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (hab : i ≫ b = a ≫ i') (hbc : p ≫ c = b ≫ p')
    (ha : Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α)
    (hc : Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ) :
    ∃ e : Entry H H' α γ 0, e.b.comp H.middle.η = H'.middle.η.comp b.hom := by
  letI := L'.injectiveTerm 0
  have he' : Function.Exact i.hom ((row H 0).p.comp H.middle.η) := by
    change Function.Exact i.hom ((H.projection.f 0).hom.comp H.middle.η)
    rw [H.augmentation_projection]
    exact N.injective_η.comp_exact_iff_exact.mpr he
  obtain ⟨t, ht, hl, hr⟩ := (row H 0).extend_square (row H' 0) H.middle.η i.hom he'
    (α.f 0).hom (γ.f 0).hom (H'.middle.η.comp b.hom) (by
      ext x
      have h1 := LinearMap.congr_fun H'.augmentation_projection (b.hom x)
      have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hbc) x
      have h3 := LinearMap.congr_fun hc (p.hom x)
      have h4 := LinearMap.congr_fun H.augmentation_projection x
      simp only [LinearMap.comp_apply, ModuleCat.hom_comp] at h1 h2 h3 h4 ⊢
      exact h1.trans ((congrArg N'.η h2.symm).trans
        (h3.symm.trans (congrArg (γ.f 0).hom h4.symm)))) (by
      ext x
      have h1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hab) x
      have h2 := LinearMap.congr_fun H'.augmentation_inclusion (a.hom x)
      have h3 := LinearMap.congr_fun ha x
      have h4 := LinearMap.congr_fun H.augmentation_inclusion x
      simp only [LinearMap.comp_apply, ModuleCat.hom_comp] at h1 h2 h3 h4
      change H'.middle.η (b.hom (i.hom x)) -
        (row H 0).diagonal (row H' 0) (α.f 0).hom (γ.f 0).hom
          (H.middle.η (i.hom x)) = 0
      rw [h1, ← h2, ← h3, ← h4]
      change _ - (row H 0).diagonal (row H' 0) (α.f 0).hom (γ.f 0).hom
        ((row H 0).i (L.η x)) = 0
      rw [SplitRow.diagonal_i]
      exact sub_self _)
  refine ⟨⟨t, hl, hr, ?_⟩, ht⟩
  change ((δ H'.middle 0).comp t).comp H.middle.η = 0
  rw [LinearMap.comp_assoc, ht, ← LinearMap.comp_assoc, δ_augmentation, LinearMap.zero_comp]

variable (hp : Function.Surjective p.hom) (e : Entry H H' α γ 0)
def entries : ∀ n, Entry H H' α γ n
  | 0 => e
  | n + 1 => next hp n (entries n)

def map : H.middle.complex ⟶ H'.middle.complex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (entries hp e n).b) (fun n => by
    apply ModuleCat.hom_ext
    exact (next_comm hp n (entries hp e n)).symm)

theorem map_left : H.inclusion ≫ map hp e = α ≫ H'.inclusion := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (entries hp e n).left

theorem map_right : H.projection ≫ γ = map hp e ≫ H'.projection := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  exact (entries hp e n).right.symm

end InjectiveDiagram

theorem projective_diagram :
  ∀ (R : Type u) [Ring R] (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
      (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C'),
    L.IsProjective → N.IsProjective → L'.IsProjective → N'.IsProjective →
    ∀ (H : Horseshoe.ProjectiveData i.hom p.hom L N)
      (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
    ∃ (α : L.complex ⟶ L'.complex) (β : H.middle.complex ⟶ H'.middle.complex)
      (γ : N.complex ⟶ N'.complex),
      Comparison.ChainLift L L' a.hom α ∧ Comparison.ChainLift H.middle H'.middle b.hom β ∧
      Comparison.ChainLift N N' c.hom γ ∧
      H.inclusion ≫ β = α ≫ H'.inclusion ∧ H.projection ≫ γ = β ≫ H'.projection := by
  intro R _ A B C A' B' C' i p i' p' a b c _hi _he _hp hi' he' _hp' hab hbc
    L N L' N' hL hN _hL' _hN' H H'
  obtain ⟨α, ha⟩ := P103.Ch10.Comparison.chain_exists R A A' L L' hL a.hom
  obtain ⟨γ, hc⟩ := P103.Ch10.Comparison.chain_exists R C C' N N' hN c.hom
  obtain ⟨e, he⟩ := ProjectiveDiagram.initial (H := H) (H' := H') (α := α) (γ := γ) he' hN a b c hab hbc ha hc
  refine ⟨α, ProjectiveDiagram.map hi' hN e, γ, ha, ?_, hc,
    ProjectiveDiagram.map_left hi' hN e, ProjectiveDiagram.map_right hi' hN e⟩
  exact he

theorem injective_diagram :
  ∀ (R : Type u) [Ring R] (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
    Function.Injective i.hom → Function.Exact i.hom p.hom → Function.Surjective p.hom →
    Function.Injective i'.hom → Function.Exact i'.hom p'.hom → Function.Surjective p'.hom →
    i ≫ b = a ≫ i' → p ≫ c = b ≫ p' →
    ∀ (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
      (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
      (H : Horseshoe.InjectiveData i.hom p.hom L N)
      (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
    ∃ (α : L.complex ⟶ L'.complex) (β : H.middle.complex ⟶ H'.middle.complex)
      (γ : N.complex ⟶ N'.complex),
      Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α ∧
      Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β ∧
      Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ ∧
      H.inclusion ≫ β = α ≫ H'.inclusion ∧ H.projection ≫ γ = β ≫ H'.projection := by
  intro R _ A B C A' B' C' i p i' p' a b c _hi he hp _hi' _he' _hp' hab hbc
    L N L' N' H H'
  obtain ⟨α, ha⟩ := P103.Ch10.Comparison.cochain_exists R A A' (Comparison.ofInjective L) L' a.hom
  obtain ⟨γ, hc⟩ := P103.Ch10.Comparison.cochain_exists R C C' (Comparison.ofInjective N) N' c.hom
  obtain ⟨e, he⟩ := InjectiveDiagram.initial (H := H) (H' := H') (α := α) (γ := γ)
    he a b c hab hbc ha hc
  refine ⟨α, InjectiveDiagram.map hp e, γ, ha, ?_, hc,
    InjectiveDiagram.map_left hp e, InjectiveDiagram.map_right hp e⟩
  exact he

theorem abelian_sequence :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : D ⥤ AddCommGrpCat.{y}) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.Rel n m →
    ∃! δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A) m,
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ ∧
      SequenceExact (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ := by
  intro D _ _ ι c A B C F _ i p hs n m hnm
  exact applied_sequence (F ⋙ Comparison.abelianGroupsToModules) i p hs n m hnm

theorem abelian_naturality :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ AddCommGrpCat.{y}) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A) m)
      (ε : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj C') n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).obj A') m),
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i)
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p) n m δ →
      Connecting (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map i')
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map p') n m ε →
      (homologyMap (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c).map γ) n) := by
  intro D _ _ ι c A B C A' B' C' F _ i p i' p' α β γ hi hp hs hs' n m hnm δ ε hδ hε
  exact applied_naturality (F ⋙ Comparison.abelianGroupsToModules) i p i' p' α β γ
    hi hp hs hs' n m hnm δ ε hδ hε

theorem abelian_contravariant_sequence :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : Dᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n m, c.symm.Rel n m →
    ∃! δ : Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).obj A.op) n →ₗ[ℤ]
        Homology (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).obj C.op) m,
      Connecting
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ ∧
      SequenceExact
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
        (((F ⋙ Comparison.abelianGroupsToModules).mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ := by
  intro D _ _ ι c A B C F _ i p hs n m hnm
  exact contravariant_sequence (F ⋙ Comparison.abelianGroupsToModules) i p hs n m hnm

theorem injective_lifts_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map α₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map α₂ ∧
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map β₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map β₂ ∧
    (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map γ₁ =
      (Comparison.appliedHomology F (ComplexShape.up ℕ) n).map γ₂ := by
  intro R _ S _ F _ A B C A' B' C' i p i' p' a b c L N L' N' H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.cochain_homology_independent R S F A A' (Comparison.ofInjective L) L' a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.cochain_homology_independent R S F B B' (Comparison.ofInjective H.middle) H'.middle b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.cochain_homology_independent R S F C C' (Comparison.ofInjective N) N' c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem injective_contravariant_lifts_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₂ := by
  intro R _ S _ F _ A B C A' B' C' i p i' p' a b c L N L' N' H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.cochain_contravariant_independent R S F A A' (Comparison.ofInjective L) L' a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.cochain_contravariant_independent R S F B B' (Comparison.ofInjective H.middle) H'.middle b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.cochain_contravariant_independent R S F C C' (Comparison.ofInjective N) N' c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem injective_ab_lifts_independent :
  ∀ (R : Type u) [Ring R] 
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map α₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map α₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map β₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map β₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map γ₁ =
      (Comparison.appliedAbHomology F (ComplexShape.up ℕ) n).map γ₂ := by
  intro R _ F _ A B C A' B' C' i p i' p' a b c L N L' N' H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.cochain_ab_homology_independent R F A A' (Comparison.ofInjective L) L' a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.cochain_ab_homology_independent R F B B' (Comparison.ofInjective H.middle) H'.middle b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.cochain_ab_homology_independent R F C C' (Comparison.ofInjective N) N' c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem injective_ab_contravariant_lifts_independent :
  ∀ (R : Type u) [Ring R] 
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
    (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
    (H : Horseshoe.InjectiveData i.hom p.hom L N)
    (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₁ →
    Comparison.CochainLift (Comparison.ofInjective L) L' a.hom α₂ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₁ →
    Comparison.CochainLift (Comparison.ofInjective H.middle) H'.middle b.hom β₂ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₁ →
    Comparison.CochainLift (Comparison.ofInjective N) N' c.hom γ₂ →
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.up ℕ) n).rightOp.map γ₂ := by
  intro R _ F _ A B C A' B' C' i p i' p' a b c L N L' N' H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.cochain_ab_contravariant_independent R F A A' (Comparison.ofInjective L) L' a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.cochain_ab_contravariant_independent R F B B' (Comparison.ofInjective H.middle) H'.middle b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.cochain_ab_contravariant_independent R F C C' (Comparison.ofInjective N) N' c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem projective_lifts_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map α₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map α₂ ∧
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map β₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map β₂ ∧
    (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map γ₁ =
      (Comparison.appliedHomology F (ComplexShape.down ℕ) n).map γ₂ := by
  intro R _ S _ F _ A B C A' B' C' i p i' p' a b c L N L' N' hL hN H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.chain_homology_independent R S F A A' L L' hL a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.chain_homology_independent R S F B B' H.middle H'.middle H.projective b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.chain_homology_independent R S F C C' N N' hN c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem projective_contravariant_lifts_independent :
  ∀ (R : Type u) [Ring R] (S : Type w) [Ring S]
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₂ := by
  intro R _ S _ F _ A B C A' B' C' i p i' p' a b c L N L' N' hL hN H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.chain_contravariant_independent R S F A A' L L' hL a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.chain_contravariant_independent R S F B B' H.middle H'.middle H.projective b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.chain_contravariant_independent R S F C C' N N' hN c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem projective_ab_lifts_independent :
  ∀ (R : Type u) [Ring R] 
    (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map α₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map α₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map β₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map β₂ ∧
    (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map γ₁ =
      (Comparison.appliedAbHomology F (ComplexShape.down ℕ) n).map γ₂ := by
  intro R _ F _ A B C A' B' C' i p i' p' a b c L N L' N' hL hN H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.chain_ab_homology_independent R F A A' L L' hL a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.chain_ab_homology_independent R F B B' H.middle H'.middle H.projective b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.chain_ab_homology_independent R F C C' N N' hN c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem projective_ab_contravariant_lifts_independent :
  ∀ (R : Type u) [Ring R] 
    (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
    (A B C A' B' C' : ModuleCat.{v} R)
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
    (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
    (hL : L.IsProjective) (hN : N.IsProjective)
    (H : Horseshoe.ProjectiveData i.hom p.hom L N)
    (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N')
    (α₁ α₂ : L.complex ⟶ L'.complex)
    (β₁ β₂ : H.middle.complex ⟶ H'.middle.complex)
    (γ₁ γ₂ : N.complex ⟶ N'.complex) (n : ℕ),
    Comparison.ChainLift L L' a.hom α₁ →
    Comparison.ChainLift L L' a.hom α₂ →
    Comparison.ChainLift H.middle H'.middle b.hom β₁ →
    Comparison.ChainLift H.middle H'.middle b.hom β₂ →
    Comparison.ChainLift N N' c.hom γ₁ →
    Comparison.ChainLift N N' c.hom γ₂ →
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map α₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map β₂ ∧
    (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₁ =
      (Comparison.appliedAbContravariantHomology F (ComplexShape.down ℕ) n).rightOp.map γ₂ := by
  intro R _ F _ A B C A' B' C' i p i' p' a b c L N L' N' hL hN H H'
    α₁ α₂ β₁ β₂ γ₁ γ₂ n hα₁ hα₂ hβ₁ hβ₂ hγ₁ hγ₂
  exact ⟨P103.Ch10.Comparison.chain_ab_contravariant_independent R F A A' L L' hL a.hom α₁ α₂ n hα₁ hα₂,
    P103.Ch10.Comparison.chain_ab_contravariant_independent R F B B' H.middle H'.middle H.projective b.hom β₁ β₂ n hβ₁ hβ₂,
    P103.Ch10.Comparison.chain_ab_contravariant_independent R F C C' N N' hN c.hom γ₁ γ₂ n hγ₁ hγ₂⟩

theorem applied_full_naturality :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C A' B' C' : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive]
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C'),
    i ≫ β = α ≫ i' → p ≫ γ = β ≫ p' →
    DegreewiseSplit i p → DegreewiseSplit i' p' →
    ∀ n m, c.Rel n m →
    ∀ (δ : Homology ((F.mapHomologicalComplex c).obj C) n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A) m)
      (ε : Homology ((F.mapHomologicalComplex c).obj C') n →ₗ[R]
        Homology ((F.mapHomologicalComplex c).obj A') m),
      Connecting ((F.mapHomologicalComplex c).map i)
        ((F.mapHomologicalComplex c).map p) n m δ →
      Connecting ((F.mapHomologicalComplex c).map i')
        ((F.mapHomologicalComplex c).map p') n m ε →
      (homologyMap ((F.mapHomologicalComplex c).map β) n).comp
          (homologyMap ((F.mapHomologicalComplex c).map i) n) =
        (homologyMap ((F.mapHomologicalComplex c).map i') n).comp
          (homologyMap ((F.mapHomologicalComplex c).map α) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map γ) n).comp
          (homologyMap ((F.mapHomologicalComplex c).map p) n) =
        (homologyMap ((F.mapHomologicalComplex c).map p') n).comp
          (homologyMap ((F.mapHomologicalComplex c).map β) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map α) m).comp δ =
        ε.comp (homologyMap ((F.mapHomologicalComplex c).map γ) n) ∧
      (homologyMap ((F.mapHomologicalComplex c).map β) m).comp
          (homologyMap ((F.mapHomologicalComplex c).map i) m) =
        (homologyMap ((F.mapHomologicalComplex c).map i') m).comp
          (homologyMap ((F.mapHomologicalComplex c).map α) m) ∧
      (homologyMap ((F.mapHomologicalComplex c).map γ) m).comp
          (homologyMap ((F.mapHomologicalComplex c).map p) m) =
        (homologyMap ((F.mapHomologicalComplex c).map p') m).comp
          (homologyMap ((F.mapHomologicalComplex c).map β) m) := by
  intro D _ _ R _ ι c A B C A' B' C' F _ i p i' p' α β γ hi hp hs hs' n m hnm δ ε hδ hε
  let G := F.mapHomologicalComplex c
  have hi' : G.map i ≫ G.map β = G.map α ≫ G.map i' := by
    simpa only [Functor.map_comp] using congrArg G.map hi
  have hp' : G.map p ≫ G.map γ = G.map β ≫ G.map p' := by
    simpa only [Functor.map_comp] using congrArg G.map hp
  exact P103.Ch10.HomologySequence.naturality _ _ _ _ _ _ _ hi' hp'
    (split_exact _ _ (split_map F i p hs)) (split_exact _ _ (split_map F i' p' hs'))
    n m hnm δ ε hδ hε

lemma cochain_boundaries_zero {R : Type u} [Ring R]
    (C : CochainComplex (ModuleCat.{v} R) ℕ) : boundaries C 0 = ⊥ := by
  unfold boundaries
  rw [CochainComplex.prev_nat_zero, C.shape 0 0 (by decide)]
  simp

lemma cochain_homology_zero_injective {R : Type u} [Ring R]
    {A B : CochainComplex (ModuleCat.{v} R) ℕ} (i : A ⟶ B)
    (hi : Function.Injective (i.f 0).hom) : Function.Injective (homologyMap i 0) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  change homologyMap i 0 x = 0 at hx
  obtain ⟨z, rfl⟩ := (cycleBoundaries A 0).mkQ_surjective x
  have hz : homologyClass B 0 (cyclesMap i 0 z) = 0 := hx
  have hz' : (i.f 0).hom z.val = 0 := by
    have hh := (P103.Ch10.HomologySequence.class_zero_iff B 0 _).mp hz
    simpa [cochain_boundaries_zero] using hh
  have zz : z = 0 := Subtype.ext (hi (hz'.trans (map_zero _).symm))
  simp [zz]


theorem cochain_zero_exact :
  ∀ {R : Type u} [Ring R] {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (i : A ⟶ B) (p : B ⟶ C), DegreewiseExact i p →
    Function.Injective (homologyMap i 0) ∧
      Function.Exact (homologyMap i 0) (homologyMap p 0) := by
  intro R _ A B C i p hs
  obtain ⟨δ, hδ, _⟩ := P103.Ch10.HomologySequence.sequence i p hs 0 1 (by rfl)
  exact ⟨cochain_homology_zero_injective i (hs 0).1, hδ.2.1⟩

theorem applied_cochain_zero_exact :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : CochainComplex D ℕ}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Injective (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map i) 0) ∧
    Function.Exact (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map i) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map p) 0) := by
  intro D _ _ R _ A B C F _ i p hs
  exact cochain_zero_exact _ _ (split_exact _ _ (split_map F i p hs))

theorem applied_contravariant_chain_zero_exact :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : ChainComplex D ℕ}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Injective (homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map p.op)) 0) ∧
    Function.Exact (homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map p.op)) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((HomologicalComplex.opFunctor D (ComplexShape.down ℕ)).map i.op)) 0) := by
  intro D _ _ R _ A B C F _ i p hs
  exact applied_cochain_zero_exact F _ _ (split_op i p hs)



theorem contravariant_naturality
  {D : Type u} [Category.{v} D] [Preadditive D]
  {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
  {A B C A' B' C' : HomologicalComplex D c}
  (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive]
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
  (hi : i ≫ β = α ≫ i') (hp : p ≫ γ = β ≫ p')
  (hs : DegreewiseSplit i p) (hs' : DegreewiseSplit i' p')
  (n m : ι) (hnm : c.symm.Rel n m)
  (δ : Homology ((F.mapHomologicalComplex c.symm).obj A.op) n →ₗ[R]
      Homology ((F.mapHomologicalComplex c.symm).obj C.op) m)
  (ε : Homology ((F.mapHomologicalComplex c.symm).obj A'.op) n →ₗ[R]
      Homology ((F.mapHomologicalComplex c.symm).obj C'.op) m)
  (hδ : Connecting
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p.op))
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i.op)) n m δ)
  (hε : Connecting
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map p'.op))
    ((F.mapHomologicalComplex c.symm).map ((HomologicalComplex.opFunctor D c).map i'.op)) n m ε) :
  (homologyMap ((F.mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor D c).map γ.op)) m).comp ε =
  δ.comp (homologyMap ((F.mapHomologicalComplex c.symm).map
    ((HomologicalComplex.opFunctor D c).map α.op)) n) := by
  let G := HomologicalComplex.opFunctor D c
  have hiop : G.map p'.op ≫ G.map β.op = G.map γ.op ≫ G.map p.op := by
    simp only [← Functor.map_comp, ← op_comp]
    exact congrArg (fun k => G.map k.op) hp.symm
  have hpop : G.map i'.op ≫ G.map α.op = G.map β.op ≫ G.map i.op := by
    simp only [← Functor.map_comp, ← op_comp]
    exact congrArg (fun k => G.map k.op) hi.symm
  exact applied_naturality F _ _ _ _ _ _ _ hiop hpop
    (split_op i' p' hs') (split_op i p hs) n m hnm ε δ hε hδ


theorem coherent_contravariant_connecting
  {D : Type u} [Category.{v} D] [Preadditive D]
  {E : Type x} [Category.{y} E] [Preadditive E]
  {R : Type z} [Ring R] {ι : Type w} {c : ComplexShape ι}
  (I : D → Type t) (K : ∀ A, I A → HomologicalComplex E c)
  (L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop)
  (F : Eᵒᵖ ⥤ ModuleCat.{q} R) [F.Additive]
  (n m : ι) (hnm : c.symm.Rel n m)
  (Cn : Comparison.CoherentComparison I K L
    (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
      Comparison.quotientHomology c.symm n).rightOp)
  (Cm : Comparison.CoherentComparison I K L
    (HomologicalComplex.opFunctor E c ⋙ F.mapHomologicalComplex c.symm ⋙
      Comparison.quotientHomology c.symm m).rightOp)
  {A B C A' B' C' : D}
  (PA : I A) (PB : I B) (PC : I C) (QA : I A') (QB : I B') (QC : I C')
  (i : K A PA ⟶ K B PB) (p : K B PB ⟶ K C PC)
  (i' : K A' QA ⟶ K B' QB) (p' : K B' QB ⟶ K C' QC)
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (α : K A PA ⟶ K A' QA) (β : K B PB ⟶ K B' QB) (γ : K C PC ⟶ K C' QC)
  (ha : L PA QA a α) (_hb : L PB QB b β) (hc : L PC QC cc γ)
  (hi : i ≫ β = α ≫ i') (hp : p ≫ γ = β ≫ p')
  (hs : DegreewiseSplit i p) (hs' : DegreewiseSplit i' p') :
  ContravariantConnectingSquare I K L F n m Cn Cm PA PB PC QA QB QC i p i' p' a cc := by
  intro δ ε hδ hε
  rw [Cm.map_eq PC QC cc γ hc, Cn.map_eq PA QA a α ha]
  exact contravariant_naturality F i p i' p' α β γ hi hp hs hs' n m hnm δ ε hδ hε

theorem coherent_maps_transport
    {D : Type u} [Category.{v} D] [Preadditive D]
    {E : Type x} [Category.{y} E] [Preadditive E]
    {W : Type z} [Category.{q} W] [Preadditive W]
    {I : D → Type t} {K : ∀ A, I A → E}
    {L : ∀ {A B} (P : I A) (Q : I B), (A ⟶ B) → (K A P ⟶ K B Q) → Prop}
    {H : E ⥤ W} (C : Comparison.CoherentComparison I K L H)
    {A B : D} (P P' : I A) (Q Q' : I B) (a : A ⟶ B)
    (f : K A P ⟶ K B Q) (g : K A P' ⟶ K B Q')
    (hf : L P Q a f) (hg : L P' Q' a g) :
    H.map f ≫ (C.comparison Q Q').hom =
      (C.comparison P P').hom ≫ H.map g := by
  rw [← C.map_eq P Q a f hf, ← C.map_eq P' Q' a g hg]
  exact C.naturality P P' Q Q' a

theorem projective_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n))
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m))
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N') :
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨α, β, γ, ha, hb, hc, hl, hr⟩ := projective_diagram
    R A B C A' B' C' i p i' p' a b cc hi he hp hi' he' hp' hab hbc
    L N L' N' hL hN hL' hN' H H'
  exact coherent_connecting (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m hnm Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a b cc α β γ ha hb hc hl hr
    (projective_split R A B C i.hom p.hom L N H)
    (projective_split R A' B' C' i'.hom p'.hom L' N' H')

theorem projective_contravariant_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp)
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N') :
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨α, β, γ, ha, hb, hc, hl, hr⟩ := projective_diagram
    R A B C A' B' C' i p i' p' a b cc hi he hp hi' he' hp' hab hbc
    L N L' N' hL hN hL' hN' H H'
  exact coherent_contravariant_connecting (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m hnm Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a b cc α β γ ha hb hc hl hr
    (projective_split R A B C i.hom p.hom L N H)
    (projective_split R A' B' C' i'.hom p'.hom L' N' H')

theorem injective_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n))
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m))
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N') :
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨α, β, γ, ha, hb, hc, hl, hr⟩ := injective_diagram
    R A B C A' B' C' i p i' p' a b cc hi he hp hi' he' hp' hab hbc
    L N L' N' H H'
  exact coherent_connecting (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m hnm Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a b cc α β γ ha hb hc hl hr
    (injective_split R A B C i.hom p.hom L N H)
    (injective_split R A' B' C' i'.hom p'.hom L' N' H')

theorem injective_contravariant_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp)
  (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N') :
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨α, β, γ, ha, hb, hc, hl, hr⟩ := injective_diagram
    R A B C A' B' C' i p i' p' a b cc hi he hp hi' he' hp' hab hbc
    L N L' N' H H'
  exact coherent_contravariant_connecting (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m hnm Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a b cc α β γ ha hb hc hl hr
    (injective_split R A B C i.hom p.hom L N H)
    (injective_split R A' B' C' i'.hom p'.hom L' N' H')


theorem projective_canonical_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m) :
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨Cn⟩ := P103.Ch10.Comparison.chain_homology_functorial R S F n
  obtain ⟨Cm⟩ := P103.Ch10.Comparison.chain_homology_functorial R S F m
  exact ⟨Cn, Cm, projective_connecting R S F n m hnm Cn Cm⟩

theorem projective_contravariant_canonical_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m) :
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    F n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨Cn⟩ := P103.Ch10.Comparison.chain_contravariant_functorial R S F n
  obtain ⟨Cm⟩ := P103.Ch10.Comparison.chain_contravariant_functorial R S F m
  exact ⟨Cn, Cm, projective_contravariant_connecting R S F n m hnm Cn Cm⟩

theorem injective_canonical_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m) :
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨Cn⟩ := P103.Ch10.Comparison.cochain_homology_functorial R S F n
  obtain ⟨Cm⟩ := P103.Ch10.Comparison.cochain_homology_functorial R S F m
  exact ⟨Cn, Cm, injective_connecting R S F n m hnm Cn Cm⟩

theorem injective_contravariant_canonical_connecting
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m) :
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    F n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  obtain ⟨Cn⟩ := P103.Ch10.Comparison.cochain_contravariant_functorial R S F n
  obtain ⟨Cm⟩ := P103.Ch10.Comparison.cochain_contravariant_functorial R S F m
  exact ⟨Cn, Cm, injective_contravariant_connecting R S F n m hnm Cn Cm⟩

theorem projective_transport
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) n))
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology F (ComplexShape.down ℕ) m))
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A) (N' : ProjectiveResolutions.Resolution R C)
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj N.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L.complex) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj N'.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj L'.complex) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H.inclusion) ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H.projection) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H'.inclusion) ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map H'.projection) n m ε) :
  (Cm.comparison ⟨L, hL⟩ ⟨L', hL'⟩).hom.hom.comp δ =
      ε.comp (Cn.comparison ⟨N, hN⟩ ⟨N', hN'⟩).hom.hom := by
  rw [Cm.comparison_hom, Cn.comparison_hom]
  exact projective_connecting R S F n m hnm Cn Cm A B C A B C i p i p (𝟙 A) (𝟙 B) (𝟙 C)
    hi he hp hi he hp (by simp) (by simp) L N L' N' hL hN hL' hN' H H' δ ε hδ hε

theorem projective_contravariant_transport
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.down ℕ) m).rightOp)
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A) (N' : ProjectiveResolutions.Resolution R C)
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj L.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj N.complex.op) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj L'.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).obj N'.complex.op) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H.inclusion.op)) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H'.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.down ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.down ℕ)).map H'.inclusion.op)) n m ε) :
  (Cm.comparison ⟨N, hN⟩ ⟨N', hN'⟩).hom.unop.hom.comp ε =
      δ.comp (Cn.comparison ⟨L, hL⟩ ⟨L', hL'⟩).hom.unop.hom := by
  rw [Cm.comparison_hom, Cn.comparison_hom]
  exact projective_contravariant_connecting R S F n m hnm Cn Cm A B C A B C i p i p (𝟙 A) (𝟙 B) (𝟙 C)
    hi he hp hi he hp (by simp) (by simp) L N L' N' hL hN hL' hN' H H' δ ε hδ hε

theorem injective_transport
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : ModuleCat.{max u v} R ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) n))
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology F (ComplexShape.up ℕ) m))
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A) (N' : InjectiveResolutions.Resolution R C)
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L.complex) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj N'.complex) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj L'.complex) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.inclusion) ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H.projection) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H'.inclusion) ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map H'.projection) n m ε) :
  (Cm.comparison L L').hom.hom.comp δ =
      ε.comp (Cn.comparison N N').hom.hom := by
  rw [Cm.comparison_hom, Cn.comparison_hom]
  exact injective_connecting R S F n m hnm Cn Cm A B C A B C i p i p (𝟙 A) (𝟙 B) (𝟙 C)
    hi he hp hi he hp (by simp) (by simp) L N L' N' H H' δ ε hδ hε

theorem injective_contravariant_transport
  (R : Type u) [Ring R] (S : Type w) [Ring S]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ ModuleCat.{y} S) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m)
  (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) n).rightOp)
  (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology F (ComplexShape.up ℕ) m).rightOp)
  (A B C : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A) (N' : InjectiveResolutions.Resolution R C)
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i.hom p.hom L' N')
  (δ : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj L.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj N.complex.op) m)
  (ε : Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj L'.complex.op) n →ₗ[S] Homology ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).obj N'.complex.op) m)
  (hδ : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H.inclusion.op)) n m δ)
  (hε : Connecting ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H'.projection.op))
      ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map ((HomologicalComplex.opFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ)).map H'.inclusion.op)) n m ε) :
  (Cm.comparison N N').hom.unop.hom.comp ε =
      δ.comp (Cn.comparison L L').hom.unop.hom := by
  rw [Cm.comparison_hom, Cn.comparison_hom]
  exact injective_contravariant_connecting R S F n m hnm Cn Cm A B C A B C i p i p (𝟙 A) (𝟙 B) (𝟙 C)
    hi he hp hi he hp (by simp) (by simp) L N L' N' H H' δ ε hδ hε


theorem projective_ab_canonical_connecting :
  ∀   (R : Type u) [Ring R]
  (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  intro R _ F _ n m hnm
  exact projective_canonical_connecting R ℤ (F ⋙ Comparison.abelianGroupsToModules) n m hnm

theorem projective_contravariant_ab_canonical_connecting :
  ∀   (R : Type u) [Ring R]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.down ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.down ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : ProjectiveResolutions.Resolution R A) (N : ProjectiveResolutions.Resolution R C)
  (L' : ProjectiveResolutions.Resolution R A') (N' : ProjectiveResolutions.Resolution R C')
  (hL : L.IsProjective) (hN : N.IsProjective) (hL' : L'.IsProjective) (hN' : N'.IsProjective)
  (H : Horseshoe.ProjectiveData i.hom p.hom L N) (H' : Horseshoe.ProjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (Comparison.ProjectiveChoice R) (Comparison.projectiveComplex R) Comparison.projectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm ⟨L, hL⟩ ⟨H.middle, H.projective⟩ ⟨N, hN⟩ ⟨L', hL'⟩ ⟨H'.middle, H'.projective⟩ ⟨N', hN'⟩
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  intro R _ F _ n m hnm
  exact projective_contravariant_canonical_connecting R ℤ (F ⋙ Comparison.abelianGroupsToModules) n m hnm

theorem injective_ab_canonical_connecting :
  ∀   (R : Type u) [Ring R]
  (F : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) n)), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) m)),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  intro R _ F _ n m hnm
  exact injective_canonical_connecting R ℤ (F ⋙ Comparison.abelianGroupsToModules) n m hnm

theorem injective_contravariant_ab_canonical_connecting :
  ∀   (R : Type u) [Ring R]
  (F : (ModuleCat.{max u v} R)ᵒᵖ ⥤ AddCommGrpCat.{y}) [F.Additive]
  (n m : ℕ) (hnm : (ComplexShape.up ℕ).symm.Rel n m),
  ∃ (Cn : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) n).rightOp), ∃ (Cm : Comparison.CoherentComparison (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver (Comparison.appliedContravariantHomology (F ⋙ Comparison.abelianGroupsToModules) (ComplexShape.up ℕ) m).rightOp),
  ∀ (A B C A' B' C' : ModuleCat.{v} R)
  (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (cc : C ⟶ C')
  (hi : Function.Injective i.hom) (he : Function.Exact i.hom p.hom) (hp : Function.Surjective p.hom)
  (hi' : Function.Injective i'.hom) (he' : Function.Exact i'.hom p'.hom) (hp' : Function.Surjective p'.hom)
  (hab : i ≫ b = a ≫ i') (hbc : p ≫ cc = b ≫ p')
  (L : InjectiveResolutions.Resolution R A) (N : InjectiveResolutions.Resolution R C)
  (L' : InjectiveResolutions.Resolution R A') (N' : InjectiveResolutions.Resolution R C')
  (H : Horseshoe.InjectiveData i.hom p.hom L N) (H' : Horseshoe.InjectiveData i'.hom p'.hom L' N'),
  ContravariantConnectingSquare (fun A : ModuleCat.{v} R => InjectiveResolutions.Resolution R A) (Comparison.injectiveComplex R) Comparison.injectiveOver
    (F ⋙ Comparison.abelianGroupsToModules) n m Cn Cm L H.middle N L' H'.middle N'
    H.inclusion H.projection H'.inclusion H'.projection a cc := by
  intro R _ F _ n m hnm
  exact injective_contravariant_canonical_connecting R ℤ (F ⋙ Comparison.abelianGroupsToModules) n m hnm

section ChainBottom
variable {R : Type u} [Ring R]

private lemma terminal_cycle {ι : Type w} {c : ComplexShape ι}
    (D : HomologicalComplex (ModuleCat.{v} R) c) (n : ι)
    (hn : ∀ m, ¬ c.Rel n m) (x : D.X n) : x ∈ cycles D n := by
  change (D.d n (c.next n)).hom x = 0
  rw [D.shape _ _ (hn _)]
  rfl

/-- The last two assertions at the bottom of an ordinary chain long exact sequence. -/
theorem homology_terminal_exact {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex (ModuleCat.{v} R) c}
    (i : A ⟶ B) (p : B ⟶ C) (hs : DegreewiseExact i p)
    (n : ι) (hn : ∀ m, ¬ c.Rel n m) :
    Function.Exact (homologyMap i n) (homologyMap p n) ∧
      Function.Surjective (homologyMap p n) := by
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := (cycleBoundaries B n).mkQ_surjective h
    constructor
    · intro hz
      have hz' : (cyclesMap p n z).val ∈ boundaries C n :=
        (P103.Ch10.HomologySequence.class_zero_iff C n _).mp hz
      obtain ⟨x, hx⟩ := hz'
      obtain ⟨y, hy⟩ := (hs (c.prev n)).2.2 x
      have he : (p.f n).hom (z.val - (B.d (c.prev n) n).hom y) = 0 := by
        rw [map_sub, ← P103.Ch10.HomologySequence.comm_apply, hy, hx]
        exact sub_self _
      obtain ⟨a, ha⟩ := ((hs n).2.1 _).mp he
      refine ⟨homologyClass A n ⟨a, terminal_cycle A n hn a⟩, ?_⟩
      apply (P103.Ch10.Complexes.homologyClass_eq_iff B n _ _).mpr
      change ∃ b, (B.d (c.prev n) n).hom b = (i.f n).hom a - z.val
      refine ⟨-y, ?_⟩
      rw [ha, map_neg]
      abel
    · rintro ⟨h, hh⟩
      rw [← hh]
      obtain ⟨a, rfl⟩ := (cycleBoundaries A n).mkQ_surjective h
      apply (P103.Ch10.HomologySequence.class_zero_iff C n _).mpr
      change (p.f n).hom ((i.f n).hom a.val) ∈ boundaries C n
      rw [(hs n).2.1.apply_apply_eq_zero]
      exact Submodule.zero_mem _
  · intro h
    obtain ⟨z, rfl⟩ := (cycleBoundaries C n).mkQ_surjective h
    obtain ⟨b, hb⟩ := (hs n).2.2 z.val
    refine ⟨homologyClass B n ⟨b, terminal_cycle B n hn b⟩, ?_⟩
    apply congrArg (homologyClass C n)
    exact Subtype.ext hb


theorem chain_bottom_exact {A B C : ChainComplex (ModuleCat.{v} R) ℕ}
    (i : A ⟶ B) (p : B ⟶ C) (hs : DegreewiseExact i p) :
    Function.Exact (homologyMap i 0) (homologyMap p 0) ∧
      Function.Surjective (homologyMap p 0) :=
  homology_terminal_exact i p hs 0 (by simp)

theorem applied_terminal_exact :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {A B C : HomologicalComplex D c}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p → ∀ n, (∀ m, ¬ c.Rel n m) →
    Function.Exact (homologyMap ((F.mapHomologicalComplex c).map i) n)
      (homologyMap ((F.mapHomologicalComplex c).map p) n) ∧
    Function.Surjective (homologyMap ((F.mapHomologicalComplex c).map p) n) := by
  intro D _ _ R _ ι c A B C F _ i p hs n hn
  exact homology_terminal_exact _ _ (split_exact _ _ (split_map F i p hs)) n hn

theorem applied_chain_bottom :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : ChainComplex D ℕ}
    (F : D ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Exact (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map i) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) 0) ∧
    Function.Surjective (homologyMap ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map p) 0) := by
  intro D _ _ R _ A B C F _ i p hs
  exact applied_terminal_exact F i p hs 0 (by simp)


theorem applied_contravariant_cochain_bottom :
  ∀ {D : Type u} [Category.{v} D] [Preadditive D]
    {R : Type x} [Ring R] {A B C : CochainComplex D ℕ}
    (F : Dᵒᵖ ⥤ ModuleCat.{y} R) [F.Additive] (i : A ⟶ B) (p : B ⟶ C),
    DegreewiseSplit i p →
    Function.Exact
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map p.op)) 0)
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map i.op)) 0) ∧
    Function.Surjective
      (homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ).symm).map
        ((HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map i.op)) 0) := by
  intro D _ _ R _ A B C F _ i p hs
  exact applied_terminal_exact F _ _ (split_op i p hs) 0 (by simp)

end ChainBottom

end P103.Ch10.HorseshoeNaturality
