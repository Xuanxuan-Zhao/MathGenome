import MathGenome.Internal.AlgebraCore.Specs.P103.Ch12.ExtBaseChange
import MathGenome.Internal.AlgebraCore.P103.Ch04.HomFlatBaseChange
import MathGenome.Internal.AlgebraCore.P103.Ch11.ExtTorDefinitions

noncomputable section
universe u v w x
namespace P103.Ch12.ExtBaseChange
open CategoryTheory
open P103.Specs.Ch10.ProjectiveResolutions
open P103.Specs.Ch12.ExtBaseChange

section FiniteResolution
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A module together with the finite-generation evidence needed at each step. -/
structure FiniteStage (R : Type u) [CommRing R] where
  module : ModuleCat.{max u v} R
  finite : Module.Finite R module

attribute [instance] FiniteStage.finite

/-- Choice of a finite free cover, with a universe lift for resolution terms. -/
def coverRank (M : FiniteStage.{u,v} R) : ℕ :=
  (Module.Finite.exists_fin' R M.module).choose

def finiteCover (M : FiniteStage.{u,v} R) :
    ULift.{v} (Fin (coverRank M) → R) →ₗ[R] M.module :=
  (Module.Finite.exists_fin' R M.module).choose_spec.choose.comp
    (ULift.moduleEquiv : ULift.{v} (Fin (coverRank M) → R) ≃ₗ[R] _).toLinearMap

theorem finiteCover_surjective (M : FiniteStage.{u,v} R) :
    Function.Surjective (finiteCover M) :=
  (Module.Finite.exists_fin' R M.module).choose_spec.choose_spec.comp
    (ULift.moduleEquiv : ULift.{v} (Fin (coverRank M) → R) ≃ₗ[R] _).surjective

/-- Noetherianity makes the next kernel finite, without any bound on its rank. -/
def nextStage (M : FiniteStage.{u,v} R) : FiniteStage.{u,v} R where
  module := ModuleCat.of R (LinearMap.ker (finiteCover M))
  finite := inferInstance

variable (A : Type v) [AddCommGroup A] [Module R A] [Module.Finite R A]

def finiteSyzygy : ℕ → FiniteStage.{u,v} R
  | 0 => ⟨ModuleCat.of R (ULift.{u} A), inferInstance⟩
  | n + 1 => nextStage (finiteSyzygy n)

abbrev finiteTerm (n : ℕ) := ULift.{v} (Fin (coverRank (finiteSyzygy (R := R) A n)) → R)

/-- Cover the kernel and then include it in the preceding finite free term. -/
def finiteDifferential (n : ℕ) : finiteTerm (R := R) A (n + 1) →ₗ[R] finiteTerm (R := R) A n :=
  (LinearMap.ker (finiteCover (finiteSyzygy (R := R) A n))).subtype.comp
    (finiteCover (finiteSyzygy (R := R) A (n + 1)))

theorem finiteDifferential_square (n : ℕ) :
    (finiteDifferential (R := R) A n).comp (finiteDifferential A (n + 1)) = 0 := by
  apply LinearMap.ext
  intro z
  exact congrArg Subtype.val (finiteCover (finiteSyzygy (R := R) A (n + 2)) z).property

def finiteComplex : ChainComplex (ModuleCat.{max u v} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (finiteTerm (R := R) A n))
    (fun n => ModuleCat.ofHom (finiteDifferential A n)) (by
      intro n
      exact ModuleCat.hom_ext (finiteDifferential_square A n))

@[simp] theorem finiteComplex_d (n : ℕ) :
    ((finiteComplex (R := R) A).d (n + 1) n).hom = finiteDifferential A n := by
  simp only [finiteComplex, ChainComplex.of_d]
  rfl

/-- Surjectivity of the kernel cover gives exactness, rather than just square zero. -/
theorem finiteDifferential_range (n : ℕ) :
    LinearMap.range (finiteDifferential (R := R) A n) =
      LinearMap.ker (finiteCover (finiteSyzygy (R := R) A n)) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (finiteCover (finiteSyzygy (R := R) A (n + 1)) y).property
  · intro hz
    obtain ⟨y, hy⟩ := finiteCover_surjective (finiteSyzygy (R := R) A (n + 1)) ⟨z, hz⟩
    exact ⟨y, congrArg Subtype.val hy⟩

def finiteAugmentation : finiteTerm (R := R) A 0 →ₗ[R] A :=
  ULift.moduleEquiv.toLinearMap.comp (finiteCover (finiteSyzygy (R := R) A 0))

theorem finiteAugmentation_ker :
    LinearMap.ker (finiteAugmentation (R := R) A) =
      LinearMap.ker (finiteCover (finiteSyzygy (R := R) A 0)) := by
  ext z
  change (finiteCover (finiteSyzygy (R := R) A 0) z).down = 0 ↔ finiteCover (finiteSyzygy (R := R) A 0) z = 0
  exact ⟨fun h => ULift.ext h, fun h => congrArg ULift.down h⟩

theorem finiteDifferential_ker (n : ℕ) :
    LinearMap.ker (finiteDifferential (R := R) A n) =
      LinearMap.ker (finiteCover (finiteSyzygy (R := R) A (n + 1))) := by
  ext z
  change (finiteCover (finiteSyzygy (R := R) A (n + 1)) z).val = 0 ↔
    finiteCover (finiteSyzygy (R := R) A (n + 1)) z = 0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

/-- An ordinary, potentially infinite-length, degreewise finite free resolution. -/
def finiteFreeResolution : Resolution R A where
  complex := finiteComplex A
  ε := finiteAugmentation A
  surjective := (ULift.moduleEquiv : ULift.{u} A ≃ₗ[R] A).surjective.comp
    (finiteCover_surjective (finiteSyzygy (R := R) A 0))
  exact_zero := by
    change LinearMap.range ((finiteComplex A).d 1 0).hom = _
    rw [finiteComplex_d]
    exact (finiteDifferential_range A 0).trans (finiteAugmentation_ker A).symm
  exact_succ n := by
    simp only [finiteComplex_d]
    exact (finiteDifferential_range A (n + 1)).trans (finiteDifferential_ker A n).symm

theorem exists_finite_free_resolution : exists_finite_free_resolutionType.{u,v} := by
  intro R _ _ A _ _ _
  refine ⟨finiteFreeResolution (R := R) A, ?_, ?_⟩
  · intro n
    change Module.Free R (finiteTerm (R := R) A n)
    infer_instance
  · intro n
    change Module.Finite R (finiteTerm (R := R) A n)
    infer_instance

theorem finite_free_hom_bijective : finite_free_hom_bijectiveType.{u,v,w,x} := by
  intro R _ S _ _ _ P _ _ _ _ B _ _
  let : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  exact P103.Ch04.HomFlatBaseChange.bijective R S P B


end FiniteResolution

section HomComparison
variable {K : Type u} [CommRing K] (S : Type v) [CommRing S] [Algebra K S]
  (C : ChainComplex (ModuleCat.{w} K) ℕ)
  (B : Type x) [AddCommGroup B] [Module K B]

/-- Naturality of the canonical Hom comparison gives compatibility in all degrees. -/
def homComparison : baseChangeComplex S (linearHomComplex C B) ⟶
    linearHomComplex (baseChangeComplex S C) (TensorProduct K S B) where
  f n := ModuleCat.ofHom (P103.Specs.Ch04.HomFlatBaseChange.canonicalValue K S (C.X n) B)
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro t
    exact (P103.Ch04.HomFlatBaseChange.naturalitySource K S
      (C.X i) (C.X j) B (C.d j i).hom z t).symm

end HomComparison

theorem hom_cochain_comparison : hom_cochain_comparisonType.{u,v,w,x} := by
  intro R _ S _ _ C B _ _
  exact ⟨homComparison S C B, fun _ => rfl⟩


theorem hom_cochain_isomorphism : hom_cochain_isomorphismType.{u,v,w,x} := by
  intro R _ S _ _ _ C B _ _ hfree hfinite
  let (n : ℕ) : Module.Free R (C.X n) := hfree n
  let (n : ℕ) : Module.Finite R (C.X n) := hfinite n
  let e (n : ℕ) : (baseChangeComplex S (linearHomComplex C B)).X n ≅
      (linearHomComplex (baseChangeComplex S C) (TensorProduct R S B)).X n :=
    (LinearEquiv.ofBijective
      (P103.Specs.Ch04.HomFlatBaseChange.canonicalValue R S (C.X n) B)
      (finite_free_hom_bijective R S (C.X n) B)).toModuleIso
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, fun _ => rfl⟩
  intro i j _
  exact (homComparison S C B).comm i j


section FlatCohomology
open TensorProduct P103.Specs.Ch10.Complexes
variable {K : Type u} [CommRing K] (S : Type v) [CommRing S] [Algebra K S]
  [Module.Flat K S] {ι : Type*} {c : ComplexShape ι}
  (C : HomologicalComplex (ModuleCat.{w} K) c) (n : ι)

/-- The kernel isomorphism supplied by flatness, applied to the outgoing map. -/
def cyclesExtension : (S ⊗[K] cycles C n) ≃ₗ[S] cycles (baseChangeComplex S C) n :=
  LinearMap.tensorKerEquiv S S (C.d n (c.next n)).hom

@[simp] theorem cyclesExtension_tmul (s : S) (z : cycles C n) :
    cyclesExtension S C n (s ⊗ₜ[K] z) = baseChangeCycle S C n s z := rfl

/-- The incoming differential with its codomain restricted to cycles. -/
def incomingCycles : C.X (c.prev n) →ₗ[K] cycles C n :=
  (C.d (c.prev n) n).hom.codRestrict (cycles C n) (by
    intro x
    exact boundaryInclusion C n ⟨x, rfl⟩)

theorem incomingCycles_range : LinearMap.range (incomingCycles C n) = cycleBoundaries C n := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

theorem baseChange_range {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : M →ₗ[K] N) :
    LinearMap.range (f.baseChange S) = (LinearMap.range f).baseChange S := by
  ext z
  exact SetLike.ext_iff.mp (LinearMap.lTensor_range (Q := S) (g := f)) z

theorem cyclesExtension_incoming :
    (cyclesExtension S C n).toLinearMap.comp ((incomingCycles C n).baseChange S) =
      incomingCycles (baseChangeComplex S C) n := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s z => apply Subtype.ext; rfl
  | add x y hx hy =>
    simp only [map_add, hx, hy]
    exact (map_add (incomingCycles (baseChangeComplex S C) n) x y).symm

/-- Images as well as kernels match, so the isomorphism descends to their quotient. -/
theorem cyclesExtension_boundaries :
    ((cycleBoundaries C n).baseChange S).map (cyclesExtension S C n).toLinearMap =
      cycleBoundaries (baseChangeComplex S C) n := by
  rw [← incomingCycles_range C n, ← baseChange_range S, ← LinearMap.range_comp,
    cyclesExtension_incoming]
  exact incomingCycles_range (baseChangeComplex S C) n

def flatCohomology : (S ⊗[K] Homology C n) ≃ₗ[S]
    Homology (baseChangeComplex S C) n :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv S K S (cycleBoundaries C n)).trans
    (Submodule.Quotient.equiv _ _ (cyclesExtension S C n) (cyclesExtension_boundaries S C n))

@[simp] theorem flatCohomology_class (s : S) (z : cycles C n) :
    flatCohomology S C n (s ⊗ₜ[K] homologyClass C n z) =
      homologyClass _ n (baseChangeCycle S C n s z) := rfl

end FlatCohomology

open TensorProduct P103.Specs.Ch10.Complexes in
theorem flat_cohomology :
    ∀ (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
      [Module.Flat R S] {ι : Type x} {c : ComplexShape ι}
      (C : HomologicalComplex (ModuleCat.{w} R) c) (n : ι),
      ∃ e : (S ⊗[R] Homology C n) ≃ₗ[S] Homology (baseChangeComplex S C) n,
        ∀ s z, e (s ⊗ₜ[R] homologyClass C n z) =
          homologyClass _ n (baseChangeCycle S C n s z) := by
  intro R _ S _ _ _ ι c C n
  exact ⟨flatCohomology S C n, flatCohomology_class S C n⟩


section ExtScalars
open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions

/-- Refining the ordinary integer-valued Ext computation to its coefficient
scalar action. Both quotients have definitionally the same representatives. -/
def linearExtEquiv {K : Type u} [CommRing K] {n : ℕ}
    (E : ExtMaps.{u,v,w} K n) {A : ModuleCat.{v} K}
    (P : ProjectiveChoice K A) (B : ModuleCat.{w} K) :
    letI := extModule E P B
    Homology (linearHomComplex P.val.complex B) n ≃ₗ[K] ExtWith P.val B n := by
  letI := extModule E P B
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r x
  refine Quotient.inductionOn' x ?_
  intro z
  exact (P103.Ch11.ExtTorDefinitions.extModule_smul_class E P B r z).symm

end ExtScalars

section AssembleExt
open TensorProduct P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
variable {K : Type u} [CommRing K] (S : Type u) [CommRing S] [Algebra K S]
  [Module.Flat K S] {n : ℕ}
  (ER : ExtMaps.{u,v,w} K n) (ES : ExtMaps.{u,max u v,max u w} S n)
  {A : ModuleCat.{v} K} (P : FiniteFreeChoice K A) (B : ModuleCat.{w} K)

/-- Composition of the scalar refinement, flat cohomology, and termwise Hom isomorphism. -/
def finiteExtComparison : ExtComparison S ER ES P B := by
  letI : Module K (ExtWith P.val B n) := extModule ER P.projective B
  letI : Module S (ExtWith (extendResolution S P.val) (S ⊗[K] B) n) :=
    extModule ES (P.extend S).projective (ModuleCat.of S (S ⊗[K] B))
  let eR : Homology (linearHomComplex P.val.complex B) n ≃ₗ[K] ExtWith P.val B n :=
    linearExtEquiv ER P.projective B
  let eS : Homology (linearHomComplex (extendResolution S P.val).complex (S ⊗[K] B)) n ≃ₗ[S]
      ExtWith (extendResolution S P.val) (S ⊗[K] B) n :=
    linearExtEquiv ES (P.extend S).projective (ModuleCat.of S (S ⊗[K] B))
  let hc := hom_cochain_isomorphism K S P.val.complex B P.property.1 P.property.2
  let i := hc.choose
  have hi := hc.choose_spec
  let h := ((quotientHomology (ComplexShape.up ℕ) n).mapIso i).toLinearEquiv
  refine ⟨(eR.symm.baseChange K S _ _).trans
    ((flatCohomology S (linearHomComplex P.val.complex B) n).trans (h.trans eS)), ?_⟩
  intro s z
  change homologyClass _ n
    (cyclesMap i.hom n (baseChangeCycle S (linearHomComplex P.val.complex B) n s z)) = _
  apply congrArg (homologyClass
    (homComplex (baseChangeComplex S P.val.complex) (S ⊗[K] B)) n)
  apply Subtype.ext
  change (i.hom.f n).hom (s ⊗ₜ[K] z.val) = _
  rw [hi n]
  rfl

end AssembleExt

theorem ext_base_change : ext_base_changeType.{u,v,w} := by
  intro R _ _ S _ _ _ A _ B n ER ES
  obtain ⟨P, hP, hfin⟩ := exists_finite_free_resolution R A
  exact ⟨⟨P, hP, hfin⟩, ⟨finiteExtComparison S ER ES ⟨P, hP, hfin⟩ B⟩⟩


open P103.Specs.Ch10.Complexes P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open TensorProduct

/-- Naturality holds for every lift, so no choice of lifts or finite free
resolutions enters the final comparison. -/
theorem ext_naturality : ext_naturalityType.{u,v,w} := by
  intro R _ S _ _ _ n ER ES A A' P Q B B' f g l hl eP eQ
  letI : Module R (ExtWith P.val B n) := extModule ER P.projective B
  letI : Module R (ExtWith Q.val B' n) := extModule ER Q.projective B'
  intro s x
  let lS := ((scalarExtension R S).mapHomologicalComplex (ComplexShape.down ℕ)).map l
  have hlS : ChainLift (extendResolution S Q.val) (extendResolution S P.val)
      ((scalarExtension R S).map f).hom lS := by
    change (P.val.ε.baseChange S).comp ((l.f 0).hom.baseChange S) =
      (f.hom.baseChange S).comp (Q.val.ε.baseChange S)
    simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange S) hl
  rw [ER.formula P.projective Q.projective f g l hl,
    ES.formula (P.extend S).projective (Q.extend S).projective
      ((scalarExtension R S).map f) ((scalarExtension R S).map g) lS hlS]
  refine Quotient.inductionOn' x ?_
  intro z
  change eQ.equiv.toFun (s ⊗ₜ[R] homologyClass _ n
    (cyclesMap (homPreMap l B ≫ homPostMap Q.val.complex g.hom) n z)) =
    homologyMap (homPreMap lS (S ⊗[R] B) ≫
      homPostMap (extendResolution S Q.val).complex (g.hom.baseChange S)) n
      (eP.equiv.toFun (s ⊗ₜ[R] homologyClass _ n z))
  rw [eQ.formula, eP.formula, P103.Ch10.Complexes.homologyMap_apply]
  apply congrArg (homologyClass _ n)
  apply Subtype.ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro t p
  let h : P.val.complex.X n →ₗ[R] B := z.val
  change s • (t ⊗ₜ[R] g.hom (h ((l.f n).hom p))) =
    g.hom.baseChange S (s • (t ⊗ₜ[R] h ((l.f n).hom p)))
  rw [map_smul, LinearMap.baseChange_tmul]


section CanonicalExt
set_option maxHeartbeats 1600000
variable {K : Type u} [CommRing K]

/-- The coherent Ext maps give linear comparison isomorphisms between arbitrary
projective resolutions, including the globally chosen canonical resolutions. -/
def extResolutionEquiv {n : ℕ} (E : ExtMaps.{u,v,w} K n)
    {A : ModuleCat.{v} K} (P Q : ProjectiveChoice K A) (B : ModuleCat.{w} K) :
    letI := extModule E P B
    letI := extModule E Q B
    ExtWith P.val B n ≃ₗ[K] ExtWith Q.val B n := by
  letI := extModule E P B
  letI := extModule E Q B
  refine
    { toFun := E.map P Q (𝟙 A) (𝟙 B)
      invFun := E.map Q P (𝟙 A) (𝟙 B)
      left_inv := ?_
      right_inv := ?_
      map_add' := (E.map P Q (𝟙 A) (𝟙 B)).map_add
      map_smul' := P103.Ch11.ExtTorDefinitions.ext_linear K n E P Q (𝟙 A) (𝟙 B) }
  · intro x
    rw [← LinearMap.comp_apply, ← E.comp]
    simp only [Category.id_comp, E.id, LinearMap.id_apply]
  · intro x
    rw [← LinearMap.comp_apply, ← E.comp]
    simp only [Category.id_comp, E.id, LinearMap.id_apply]

theorem extMap_comp_apply {n : ℕ} (E : ExtMaps.{u,v,w} K n)
    {A A' A'' : ModuleCat.{v} K} (P : ProjectiveChoice K A)
    (Q : ProjectiveChoice K A') (T : ProjectiveChoice K A'')
    {B B' B'' : ModuleCat.{w} K} (f : A' ⟶ A) (f' : A'' ⟶ A')
    (g : B ⟶ B') (g' : B' ⟶ B'') (x : ExtWith P.val B n) :
    E.map Q T f' g' (E.map P Q f g x) = E.map P T (f' ≫ f) (g ≫ g') x := by
  rw [E.comp]
  rfl

variable (S : Type u) [CommRing S] [Algebra K S] [Module.Flat K S]
  (TR : CanonicalTheory.{u,v,w} K) (TS : CanonicalTheory.{u,max u v,max u w} S) (n : ℕ)

/-- Transport the computed comparison to the given canonical Ext theories. -/
def canonicalFromFinite {A : ModuleCat.{v} K} (P : FiniteFreeChoice K A) (B : ModuleCat.{w} K) :
    letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    letI : Module S (TS.Ext (ModuleCat.of S (S ⊗[K] A)) (ModuleCat.of S (S ⊗[K] B)) n) :=
      extModule (TS.extMaps n) (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A)))
        (ModuleCat.of S (S ⊗[K] B))
    (S ⊗[K] TR.Ext A B n) ≃ₗ[S]
      TS.Ext (ModuleCat.of S (S ⊗[K] A)) (ModuleCat.of S (S ⊗[K] B)) n := by
  letI := extModule (TR.extMaps n) (TR.leftResolutions A) B
  letI : Module K (ExtWith P.val B n) := extModule (TR.extMaps n) P.projective B
  letI : Module S (ExtWith (extendResolution S P.val) (S ⊗[K] B) n) :=
    extModule (TS.extMaps n) (P.extend S).projective (ModuleCat.of S (S ⊗[K] B))
  letI := extModule (TS.extMaps n) (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A)))
    (ModuleCat.of S (S ⊗[K] B))
  let r : TR.Ext A B n ≃ₗ[K] ExtWith P.val B n :=
    extResolutionEquiv (TR.extMaps n) (TR.leftResolutions A) P.projective B
  let t : ExtWith (extendResolution S P.val) (S ⊗[K] B) n ≃ₗ[S]
      TS.Ext (ModuleCat.of S (S ⊗[K] A)) (ModuleCat.of S (S ⊗[K] B)) n :=
    extResolutionEquiv (TS.extMaps n) (P.extend S).projective
      (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A))) (ModuleCat.of S (S ⊗[K] B))
  exact (r.baseChange K S _ _).trans ((finiteExtComparison S (TR.extMaps n) (TS.extMaps n) P B).equiv.trans t)


/-- The formula for the transport to canonical resolutions uses only the
coherent identity comparisons. -/
theorem canonicalFromFinite_tmul {A : ModuleCat.{v} K} (P : FiniteFreeChoice K A)
    (B : ModuleCat.{w} K) :
    letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    letI : Module K (ExtWith P.val B n) := extModule (TR.extMaps n) P.projective B
    ∀ (s : S) (x : TR.Ext A B n),
      (canonicalFromFinite S TR TS n P B).toFun (s ⊗ₜ[K] x) =
        (TS.extMaps n).map (P.extend S).projective
          (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A))) (𝟙 _) (𝟙 _)
          ((finiteExtComparison S (TR.extMaps n) (TS.extMaps n) P B).equiv.toFun
            (s ⊗ₜ[K] (TR.extMaps n).map (TR.leftResolutions A) P.projective (𝟙 _) (𝟙 _) x)) := by
  intros
  rfl

/-- The canonical comparison is natural even if the finite free resolution
used for each input module is chosen independently. -/
theorem canonicalFromFinite_natural {A A' : ModuleCat.{v} K}
    (P : FiniteFreeChoice K A) (Q : FiniteFreeChoice K A')
    {B B' : ModuleCat.{w} K} (f : A' ⟶ A) (g : B ⟶ B') :
    letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    letI : Module K (TR.Ext A' B' n) := extModule (TR.extMaps n) (TR.leftResolutions A') B'
    ∀ (s : S) (x : TR.Ext A B n),
      (canonicalFromFinite S TR TS n Q B').toFun (s ⊗ₜ[K] TR.extMap n f g x) =
        TS.extMap n ((scalarExtension K S).map f) ((scalarExtension K S).map g)
          ((canonicalFromFinite S TR TS n P B).toFun (s ⊗ₜ[K] x)) := by
  letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
  letI : Module K (TR.Ext A' B' n) := extModule (TR.extMaps n) (TR.leftResolutions A') B'
  letI : Module K (ExtWith P.val B n) := extModule (TR.extMaps n) P.projective B
  letI : Module K (ExtWith Q.val B' n) := extModule (TR.extMaps n) Q.projective B'
  intro s x
  let ER := TR.extMaps n
  let ES := TS.extMaps n
  let eP := finiteExtComparison S ER ES P B
  let eQ := finiteExtComparison S ER ES Q B'
  obtain ⟨l, hl⟩ := P103.Ch10.Comparison.chain_exists K A' A Q.val P.val Q.projective.property f.hom
  have h := ext_naturality K S n ER ES P Q f g l hl eP eQ s
    (ER.map (TR.leftResolutions A) P.projective (𝟙 _) (𝟙 _) x)
  have hsource : ER.map (TR.leftResolutions A') Q.projective (𝟙 _) (𝟙 _)
      (ER.map (TR.leftResolutions A) (TR.leftResolutions A') f g x) =
      ER.map P.projective Q.projective f g
        (ER.map (TR.leftResolutions A) P.projective (𝟙 _) (𝟙 _) x) := by
    rw [extMap_comp_apply, extMap_comp_apply]
    simp only [Category.id_comp, Category.comp_id]
  rw [canonicalFromFinite_tmul, canonicalFromFinite_tmul]
  change ES.map (Q.extend S).projective (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A')))
      (𝟙 _) (𝟙 _) (eQ.equiv.toFun (s ⊗ₜ[K] ER.map (TR.leftResolutions A') Q.projective
        (𝟙 _) (𝟙 _) (ER.map (TR.leftResolutions A) (TR.leftResolutions A') f g x))) =
    ES.map (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A)))
      (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A')))
      ((scalarExtension K S).map f) ((scalarExtension K S).map g)
      (ES.map (P.extend S).projective (TS.leftResolutions (ModuleCat.of S (S ⊗[K] A)))
        (𝟙 _) (𝟙 _) (eP.equiv.toFun (s ⊗ₜ[K]
          ER.map (TR.leftResolutions A) P.projective (𝟙 _) (𝟙 _) x)))
  rw [hsource, h]
  erw [extMap_comp_apply, extMap_comp_apply]
  erw [Category.id_comp, Category.comp_id]

/-- Once transported to fixed Ext objects, changing the finite free resolution
does not change the comparison isomorphism. -/
theorem canonicalFromFinite_independent {A : ModuleCat.{v} K}
    (P Q : FiniteFreeChoice K A) (B : ModuleCat.{w} K) :
    letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
    canonicalFromFinite S TR TS n P B = canonicalFromFinite S TR TS n Q B := by
  letI : Module K (TR.Ext A B n) := extModule (TR.extMaps n) (TR.leftResolutions A) B
  apply LinearEquiv.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    have h := canonicalFromFinite_natural S TR TS n P Q (𝟙 A) (𝟙 B) s x
    have hA : (scalarExtension K S).map (𝟙 A) = 𝟙 _ := (scalarExtension K S).map_id A
    have hB : (scalarExtension K S).map (𝟙 B) = 𝟙 _ := (scalarExtension K S).map_id B
    simp only [CanonicalTheory.extMap, hA, hB, (TR.extMaps n).id,
      (TS.extMaps n).id, LinearMap.id_apply] at h
    exact h.symm
  | add z z' hz hz' => simp only [map_add, hz, hz']

variable [IsNoetherianRing K]

/-- The Noetherian finite-generation construction supplies the required inputs. -/
def chosenFinite (A : ModuleCat.{v} K) [Module.Finite K A] : FiniteFreeChoice K A :=
  ⟨(exists_finite_free_resolution K A).choose,
    (exists_finite_free_resolution K A).choose_spec⟩

def canonicalComparison : CanonicalComparison S TR TS n where
  equiv A _ B := canonicalFromFinite S TR TS n (chosenFinite A) B
  naturality f g := canonicalFromFinite_natural S TR TS n (chosenFinite _) (chosenFinite _) f g

end CanonicalExt

theorem canonical_ext_base_change : canonical_ext_base_changeType.{u,v,w} := by
  intro R _ _ S _ _ _ TR TS n
  exact ⟨canonicalComparison S TR TS n⟩

end P103.Ch12.ExtBaseChange
