import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwists
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Order.Fin.Tuple

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open KaehlerDifferential

namespace DerivedFormalization.ProjectiveTopForms

open ProjectiveTwists

universe u

set_option linter.style.haveILetI false

section ExteriorMap

variable {A B M N P : Type*} [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  [AddCommGroup P] [Module B P]

/-- Precomposition by a semilinear map, using restriction of scalars on the codomain. -/
def semilinearAlternating (f : A →+* B) (g : M →ₛₗ[f] N) {p : ℕ}
    (a : AlternatingMap B N P (Fin p)) :
    letI := Module.compHom P f
    AlternatingMap A M P (Fin p) := by
  letI := Module.compHom P f
  classical
  refine
    { toFun := fun v ↦ a (g ∘ v)
      map_update_add' := ?_
      map_update_smul' := ?_
      map_eq_zero_of_eq' := fun v i j h hij ↦ a.map_eq_zero_of_eq _ (congrArg g h) hij }
  · intro _ v i x y
    simpa only [Function.comp_update, map_add] using a.map_update_add (g ∘ v) i (g x) (g y)
  · intro _ v i r x
    change _ = f r • a (g ∘ Function.update v i x)
    simpa only [Function.comp_update, map_smulₛₗ] using
      a.map_update_smul (g ∘ v) i (f r) (g x)

/-- Exterior powers on semilinear maps. -/
def exteriorMap (f : A →+* B) (g : M →ₛₗ[f] N) (p : ℕ) :
    (⋀[A]^p M) →ₛₗ[f] (⋀[B]^p N) := by
  letI := Module.compHom (⋀[B]^p N) f
  let L := exteriorPower.alternatingMapLinearEquiv (semilinearAlternating f g
    (exteriorPower.ιMulti B p))
  exact { toFun := L, map_add' := L.map_add, map_smul' := L.map_smul }

@[simp] theorem exteriorMap_ιMulti (f : A →+* B) (g : M →ₛₗ[f] N) (p : ℕ)
    (v : Fin p → M) :
    exteriorMap f g p (exteriorPower.ιMulti A p v) = exteriorPower.ιMulti B p (g ∘ v) := by
  letI := Module.compHom (⋀[B]^p N) f
  exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti
    (semilinearAlternating f g (exteriorPower.ιMulti B p)) v

end ExteriorMap

section DifferentialMap

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

/-- The canonical semilinear map on relative Kähler differentials. -/
def differentialMap (f : A →ₐ[K] B) : Ω[A⁄K] →ₛₗ[f.toRingHom] Ω[B⁄K] := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  let L := KaehlerDifferential.map K K A B
  exact { toFun := L, map_add' := L.map_add, map_smul' := L.map_smul }

@[simp] theorem differentialMap_D (f : A →ₐ[K] B) (a : A) :
    differentialMap f (D K A a) = D K B (f a) := by
  letI := f.toRingHom.toAlgebra
  letI := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map_D K K A B a

end DifferentialMap

variable (k : Type u) [Field k] (n : ℕ)

/-- The ground-field map to sections induced by the structure morphism of projective space. -/
def sectionConstants (U : OpensOfProj k n) : k →+* structureSections k n U :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (ProjectiveTwists.Expected.structureMapValue k n).appLE ⊤ U
      (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom

instance sectionAlgebra (U : OpensOfProj k n) : Algebra k (structureSections k n U) :=
  (sectionConstants k n U).toAlgebra

/-- Restriction of regular functions as an algebra homomorphism over the base field. -/
def restrictFunctions {U V : (OpensOfProj k n)ᵒᵖ} (f : U ⟶ V) :
    structureSections k n U.unop →ₐ[k] structureSections k n V.unop where
  __ := ((commStructurePresheaf k n).map f).hom
  commutes' a := by
    change ((((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (ProjectiveTwists.Expected.structureMapValue k n).appLE ⊤ U.unop _) ≫
        (commStructurePresheaf k n).map f).hom a) = _
    have h := Scheme.Hom.appLE_map (ProjectiveTwists.Expected.structureMapValue k n)
      (U := ⊤) (V := U.unop) (V' := V.unop)
      (by rw [Scheme.Hom.preimage_top]; exact le_top) f
    exact DFunLike.congr_fun (congrArg (fun g ↦
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g).hom) h) a

abbrev Differentials (U : OpensOfProj k n) := Ω[structureSections k n U⁄k]
abbrev Forms (p : ℕ) (U : OpensOfProj k n) := ⋀[structureSections k n U]^p (Differentials k n U)

/-- The usual restriction on the exterior powers of the Kähler modules of sections. -/
def restrictForms (p : ℕ) {U V : (OpensOfProj k n)ᵒᵖ} (f : U ⟶ V) :
    Forms k n p U.unop →ₛₗ[(restrictFunctions k n f).toRingHom] Forms k n p V.unop :=
  exteriorMap _ (differentialMap (restrictFunctions k n f)) p

private theorem linearMap_ext_differential {R K : Type*} [CommRing R] [CommRing K]
    [Algebra K R] {M : Type*} [AddCommGroup M] [Module R M]
    {f g : Ω[R⁄K] →ₗ[R] M} (h : ∀ x, f (D K R x) = g (D K R x)) : f = g := by
  apply LinearMap.ext_on (s := Set.range (D K R)) (KaehlerDifferential.span_range_derivation K R)
  rintro _ ⟨x, rfl⟩
  exact h x

theorem restrictForms_id (p : ℕ) (U : (OpensOfProj k n)ᵒᵖ) (v : Forms k n p U.unop) :
    restrictForms k n p (𝟙 U) v = v := by
  have h : ((structurePresheaf k n).map (𝟙 U)).hom = RingHom.id _ := by simp
  let d : Differentials k n U.unop →ₗ[structureSections k n U.unop] Differentials k n U.unop :=
    { toFun := differentialMap (restrictFunctions k n (𝟙 U))
      map_add' := map_add _
      map_smul' := fun r x ↦ (map_smulₛₗ _ r x).trans
        (by exact congrArg (· • _) (DFunLike.congr_fun h r)) }
  have hd : d = LinearMap.id := by
    apply linearMap_ext_differential
    intro a
    change differentialMap (restrictFunctions k n (𝟙 U)) (D _ _ a) = D _ _ a
    rw [differentialMap_D]
    exact congrArg (D k _) (DFunLike.congr_fun h a)
  let w : Forms k n p U.unop →ₗ[structureSections k n U.unop] Forms k n p U.unop :=
    { toFun := restrictForms k n p (𝟙 U)
      map_add' := map_add _
      map_smul' := fun r x ↦ (map_smulₛₗ _ r x).trans
        (by exact congrArg (· • _) (DFunLike.congr_fun h r)) }
  have hw : w = LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro a
    change restrictForms k n p (𝟙 U) (exteriorPower.ιMulti _ _ a) =
      exteriorPower.ιMulti _ _ a
    rw [restrictForms, exteriorMap_ιMulti]
    congr 1
    funext j
    exact DFunLike.congr_fun hd (a j)
  exact DFunLike.congr_fun hw v

theorem restrictForms_comp (p : ℕ) {U V W : (OpensOfProj k n)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) (v : Forms k n p U.unop) :
    restrictForms k n p (f ≫ g) v = restrictForms k n p g (restrictForms k n p f v) := by
  let a := restrictFunctions k n f
  let b := restrictFunctions k n g
  let c := restrictFunctions k n (f ≫ g)
  have h : b.toRingHom.comp a.toRingHom = c.toRingHom := by
    change (((structurePresheaf k n).map g).hom.comp ((structurePresheaf k n).map f).hom) = _
    exact (congrArg RingCat.Hom.hom ((structurePresheaf k n).map_comp f g)).symm
  letI := Module.compHom (Differentials k n W.unop) c.toRingHom
  letI := Module.compHom (Forms k n p W.unop) c.toRingHom
  let d := (differentialMap b).comp (differentialMap a) (σ₁₃ := b.toRingHom.comp a.toRingHom)
  let L₁ : Differentials k n U.unop →ₗ[structureSections k n U.unop]
      Differentials k n W.unop :=
    { toFun := differentialMap c, map_add' := map_add _, map_smul' := fun r x ↦ by
        change differentialMap c (r • x) = c r • differentialMap c x
        exact map_smulₛₗ (differentialMap c) r x }
  let L₂ : Differentials k n U.unop →ₗ[structureSections k n U.unop]
      Differentials k n W.unop :=
    { toFun := d, map_add' := map_add _, map_smul' := fun r x ↦ (map_smulₛₗ d r x).trans
        (by exact congrArg (· • d x) (DFunLike.congr_fun h r)) }
  have hd : L₁ = L₂ := by
    apply linearMap_ext_differential
    intro x
    change differentialMap c (D _ _ x) = differentialMap b (differentialMap a (D _ _ x))
    simp only [differentialMap_D]
    exact congrArg (D k _) (DFunLike.congr_fun h x).symm
  let e := (restrictForms k n p g).comp (restrictForms k n p f)
    (σ₁₃ := b.toRingHom.comp a.toRingHom)
  let E₁ : Forms k n p U.unop →ₗ[structureSections k n U.unop] Forms k n p W.unop :=
    { toFun := restrictForms k n p (f ≫ g), map_add' := map_add _, map_smul' := fun r x ↦ by
        change restrictForms k n p (f ≫ g) (r • x) = c r • restrictForms k n p (f ≫ g) x
        exact map_smulₛₗ (restrictForms k n p (f ≫ g)) r x }
  let E₂ : Forms k n p U.unop →ₗ[structureSections k n U.unop] Forms k n p W.unop :=
    { toFun := e, map_add' := map_add _, map_smul' := fun r x ↦ (map_smulₛₗ e r x).trans
        (by exact congrArg (· • e x) (DFunLike.congr_fun h r)) }
  have he : E₁ = E₂ := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro s
    change restrictForms k n p (f ≫ g) (exteriorPower.ιMulti _ _ s) =
      restrictForms k n p g (restrictForms k n p f (exteriorPower.ιMulti _ _ s))
    simp only [restrictForms, exteriorMap_ιMulti]
    congr 1
    funext j
    exact DFunLike.congr_fun hd (s j)
  exact DFunLike.congr_fun he v

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- Exterior powers of the sections' relative Kähler modules, before sheafification. -/
def formsPresheaf (p : ℕ) : PresheafOfModules (structurePresheaf k n) where
  obj U := ModuleCat.of (structureSections k n U.unop) (Forms k n p U.unop)
  map {U V} f := ModuleCat.semilinearMapAddEquiv ((structurePresheaf k n).map f).hom _ _
    (restrictForms k n p f)
  map_id U := by
    apply ModuleCat.Hom.ext
    apply DFunLike.ext
    exact restrictForms_id k n p U
  map_comp f g := by
    apply ModuleCat.Hom.ext
    apply DFunLike.ext
    exact restrictForms_comp k n p f g

/-- The sheaf of relative differential forms obtained by sheafification. -/
def formsSheaf (p : ℕ) : SheafOfModules (moduleRingSheaf k n) :=
  (twistSheafification k n).obj (formsPresheaf k n p)

def toFormsSheaf (p : ℕ) : formsPresheaf k n p ⟶ (formsSheaf k n p).val :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 (structurePresheaf k n))
    (𝟙 (formsSheaf k n p))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The signed exponent of the local frame of the canonical twist. -/
def canonicalDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

/-- The regular function x_j/x_i on the standard chart of x_i. -/
def chartCoordinate (i j : Index n) : structureSections k n (chart k n i) :=
  (Proj.awayToSection (grading k n) (variablePolynomial k n i)) (coordinateRatio k n i j)

/-- The indices of the affine coordinates, listed in increasing order. -/
abbrev orderedChartVariables (i : Index n) : Fin n ≃o ChartVariables n i :=
  finSuccAboveOrderIso i

/-- The signed wedge of the differentials of the chart coordinates, in increasing order. -/
def chartForm (i : Index n) : Forms k n n (chart k n i) :=
  (-1 : structureSections k n (chart k n i)) ^ i.val •
    exteriorPower.ιMulti _ _ (fun a ↦ D k _ (chartCoordinate k n i (i.succAbove a)))

/-- The signed wedge as a section of the sheaf of top forms. -/
def signedGenerator (i : Index n) : ProjectiveTwists.Expected.moduleOn k n (formsSheaf k n n) (chart k n i) :=
  (toFormsSheaf k n n).app (op (chart k n i)) (chartForm k n i)

namespace Expected

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- The sheafification agrees on the standard affine basis with the exterior power
of the actual relative Kähler module, through its canonical comparison. -/
def principalOpen : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    ∀ (i : Index n) (r : structureSections k n (chart k n i)),
      let U := (projectiveSpace k n).basicOpen r
      Function.Bijective (fun v : Forms k n n U ↦ (toFormsSheaf k n n).app (op U) v)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- The transition coefficient is the negative (n+1)-st power of the ratio of coordinates. -/
def transition : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n → ∀ (i j : Index n),
    let U := chart k n i ⊓ chart k n j
    let z := restrictFunctions k n (homOfLE (show U ≤ chart k n i from inf_le_left)).op
      (chartCoordinate k n i j)
    ∃ v : Units (structureSections k n U), (v : structureSections k n U) = z ∧
      (formsSheaf k n n).val.map (homOfLE (show U ≤ chart k n j from inf_le_right)).op
        (signedGenerator k n j) =
      ((v ^ canonicalDegree n : Units (structureSections k n U)) : structureSections k n U) •
        (formsSheaf k n n).val.map (homOfLE (show U ≤ chart k n i from inf_le_left)).op
          (signedGenerator k n i)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
set_option backward.isDefEq.respectTransparency false in
/-- The top forms identify with the twist in degree −n−1, as a module sheaf.
The underlying twist sections are the locally homogeneous rational functions from U21a. -/
def comparison : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    ∃ (M : SheafOfModules (moduleRingSheaf k n)) (α : formsSheaf k n n ≅ M)
      (e : ∀ U, ProjectiveTwists.Expected.moduleOn k n M U ≃ TwistSections k n (canonicalDegree n) U),
      (∀ U (s t : ProjectiveTwists.Expected.moduleOn k n M U) x,
        (e U (s + t)).val x = (e U s).val x + (e U t).val x) ∧
      (∀ U (r : structureSections k n U) (s : ProjectiveTwists.Expected.moduleOn k n M U) x,
        (e U (r • s)).val x = structureToFunctions k n U r x * (e U s).val x) ∧
      (∀ U V (h : V ≤ U) (s : ProjectiveTwists.Expected.moduleOn k n M U),
        e V (M.val.map (homOfLE h).op s) =
          restriction k n h (canonicalDegree n) (e U s)) ∧
      ∀ (i : Index n) (x : chart k n i),
        (e (chart k n i) (α.hom.val.app (op (chart k n i)) (signedGenerator k n i))).val x =
          frame k n i (canonicalDegree n)

end Expected

end DerivedFormalization.ProjectiveTopForms
