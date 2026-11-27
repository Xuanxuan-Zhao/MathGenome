import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KProjectiveFlatness
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeReplacement
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! K-projective cochain complexes are K-flat at their original module universe. -/

namespace DerivedFormalization.KProjectiveFlatness

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainTensor (tensor pure map)
open scoped TensorProduct

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]

private theorem tensorMap_apply {A B P Q : Comp.{v} R} (f : A ⟶ B) (g : P ⟶ Q)
    (i j n : ℤ) (h : i + j = n) (x : A.X i) (y : P.X j) :
    (map f g).f n (pure A P h x y) = pure B Q h (f.f i x) (g.f j y) :=
  CochainTensor.map_on_pure f g i j n h x y

private theorem tensorMap_id (A P : Comp.{v} R) :
    map (𝟙 A) (𝟙 P) = 𝟙 (tensor A P) := by
  apply CochainTensor.hom_ext
  intro i j n h x y
  simp only [tensorMap_apply, id_f, ModuleCat.id_apply]

private theorem tensorMap_comp {A B C P Q T : Comp.{v} R}
    (f : A ⟶ B) (g : B ⟶ C) (p : P ⟶ Q) (q : Q ⟶ T) :
    map f p ≫ map g q = map (f ≫ g) (p ≫ q) := by
  apply CochainTensor.hom_ext
  intro i j n h x y
  simp only [comp_f, ModuleCat.comp_apply, tensorMap_apply]

private def tensorIso {A B P Q : Comp.{v} R} (e : A ≅ B) (e' : P ≅ Q) :
    tensor A P ≅ tensor B Q where
  hom := map e.hom e'.hom
  inv := map e.inv e'.inv
  hom_inv_id := by rw [tensorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id, tensorMap_id]
  inv_hom_id := by rw [tensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id, tensorMap_id]

private theorem isKFlat_of_small {P : Comp.{v} R} [Small.{v} R] (hP : P.IsKProjective) :
    CochainTensor.IsKFlat P := by
  let := hP
  obtain ⟨F, p, hp, _, _, hF, hflat⟩ := SemifreeReplacement.nativeReplacement R P
  let := hF
  obtain ⟨e, _⟩ := (CochainComplex.IsKProjective.quasiIso_iff p).mp hp
  intro A hA
  let e' : HomotopyEquiv (tensor A F) (tensor A P) :=
    { hom := map (𝟙 A) e.hom
      inv := map (𝟙 A) e.inv
      homotopyHomInvId := by
        rw [tensorMap_comp, Category.id_comp, ← tensorMap_id A F]
        exact CochainTensor.mapHomotopy (Homotopy.refl _) e.homotopyHomInvId
      homotopyInvHomId := by
        rw [tensorMap_comp, Category.id_comp, ← tensorMap_id A P]
        exact CochainTensor.mapHomotopy (Homotopy.refl _) e.homotopyInvHomId }
  let : QuasiIso e'.hom := homotopyEquivalences_le_quasiIso _ _ _ e'.homotopyEquivalences_hom
  intro i
  rw [exactAt_iff_isZero_homology]
  exact ((hflat A hA i).isZero_homology).of_iso (asIso (homologyMap e'.hom i)).symm

variable {S : Type w} [CommRing S]

private abbrev restrict (f : R →+* S) : Comp.{v} S ⥤ Comp.{v} R :=
  (ModuleCat.restrictScalars.{v} f).mapHomologicalComplex (ComplexShape.up ℤ)

private theorem restrict_acyclic_iff (f : R →+* S) (X : Comp.{v} S) :
    ((restrict f).obj X).Acyclic ↔ X.Acyclic := by
  rw [HomologicalComplex.acyclic_iff, HomologicalComplex.acyclic_iff]
  apply forall_congr'
  intro i
  exact (X.sc i).exact_map_iff_of_faithful (ModuleCat.restrictScalars f)

private def restrictPreimage (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{v} S} (g : (ModuleCat.restrictScalars f).obj M ⟶
      (ModuleCat.restrictScalars f).obj N) : M ⟶ N :=
  ModuleCat.ofHom
    { toFun := fun x => g x
      map_add' := g.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := hf s
        exact g.hom.map_smul r x }

private theorem restrict_preimage (f : R →+* S) (hf : Function.Surjective f)
    {M N : ModuleCat.{v} S} (g : (ModuleCat.restrictScalars f).obj M ⟶
      (ModuleCat.restrictScalars f).obj N) :
    (ModuleCat.restrictScalars f).map (restrictPreimage f hf g) = g :=
  ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- Surjectivity makes the components of a restricted null homotopy linear over the target ring. -/
private theorem kProjective_of_restrict (f : R →+* S) (hf : Function.Surjective f)
    (P : Comp.{v} S) (hP : CochainComplex.IsKProjective ((restrict f).obj P)) : P.IsKProjective := by
  let := hP
  constructor
  intro A g hA
  let F := ModuleCat.restrictScalars.{v} f
  obtain ⟨h⟩ := CochainComplex.IsKProjective.nonempty_homotopy_zero ((restrict f).map g)
    ((restrict_acyclic_iff f A).2 hA)
  refine ⟨{ hom := fun i j => restrictPreimage f hf (h.hom i j), zero := ?_, comm := ?_ }⟩
  · intro i j hij
    apply F.map_injective
    rw [F.map_zero, restrict_preimage f hf]
    exact h.zero i j hij
  · intro i
    apply F.map_injective
    simpa only [F, Functor.map_add, Functor.map_comp, Functor.map_zero,
      restrict_preimage, dNext, prevD, AddMonoidHom.mk'_apply, zero_f_apply,
      Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_map_f] using h.comm i

/-- The simultaneous action on all terms of the two complexes. -/
private def scalarAction (A P : Comp.{v} R) :
    R →+* ((∀ i : ℤ, AddMonoid.End (A.X i)) × (∀ i : ℤ, AddMonoid.End (P.X i))) :=
  (RingHom.pi fun i => Module.toAddMonoidEnd R (A.X i)).prod
    (RingHom.pi fun i => Module.toAddMonoidEnd R (P.X i))

private abbrev ScalarImage (A P : Comp.{v} R) := (scalarAction A P).range

private instance (A P : Comp.{v} R) : CommRing (ScalarImage A P) :=
  Function.Surjective.commRing (scalarAction A P).rangeRestrict
    (scalarAction A P).rangeRestrict_surjective
    (map_zero _) (map_one _) (map_add _) (map_mul _) (map_neg _) (map_sub _)
    (map_nsmul _) (map_zsmul _) (map_pow _) (map_natCast _) (map_intCast _)

private abbrev descendTerm (M : ModuleCat.{v} R) (ρ : S →+* AddMonoid.End M) : ModuleCat.{v} S :=
  letI := Module.compHom M ρ
  ModuleCat.of S M

private abbrev descend (C : Comp.{v} R) (f : R →+* S) (hf : Function.Surjective f)
    (ρ : ∀ i, S →+* AddMonoid.End (C.X i))
    (hρ : ∀ i r (x : C.X i), ρ i (f r) x = r • x) : Comp.{v} S where
  X i := descendTerm (C.X i) (ρ i)
  d i j := ModuleCat.ofHom (X := descendTerm (C.X i) (ρ i))
    (Y := descendTerm (C.X j) (ρ j))
    { toFun := fun x => C.d i j x
      map_add' := (C.d i j).hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := hf s
        change C.d i j (ρ i (f r) x) = ρ j (f r) (C.d i j x)
        rw [hρ, hρ]
        exact (C.d i j).hom.map_smul r x }
  shape i j h := ModuleCat.hom_ext (LinearMap.ext fun x =>
    ConcreteCategory.congr_hom (C.shape i j h) x)
  d_comp_d' i j k _ _ := ModuleCat.hom_ext (LinearMap.ext fun x =>
    ConcreteCategory.congr_hom (C.d_comp_d i j k) x)

private def restrictDescendIso (C : Comp.{v} R) (f : R →+* S) (hf : Function.Surjective f)
    (ρ : ∀ i, S →+* AddMonoid.End (C.X i))
    (hρ : ∀ i r (x : C.X i), ρ i (f r) x = r • x) :
    (restrict f).obj (descend C f hf ρ hρ) ≅ C :=
  Hom.isoOfComponents (fun i =>
    (show ((restrict f).obj (descend C f hf ρ hρ)).X i ≃ₗ[R] C.X i from
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := hρ i }).toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

section TensorComparison

variable {T : Type v} [CommRing T] (f : R →+* T) (hf : Function.Surjective f)

local notation "res" => (ModuleCat.restrictScalars f)

/-- Changing the balancing ring along a surjection preserves the pure tensors. -/
private def tensorSummandEquiv (M N : ModuleCat.{v} T) :
    ((res).obj M ⊗[R] (res).obj N) ≃ₗ[R] (res).obj (ModuleCat.of T (M ⊗[T] N)) := by
  let M' := (res).obj M
  let N' := (res).obj N
  letI : SMulCommClass R T M' := ⟨fun r t x => by
    change f r • (t • x) = t • (f r • x)
    rw [← mul_smul, ← mul_smul, mul_comm (f r) t]⟩
  letI : SMulCommClass T R M' := SMulCommClass.symm _ _ _
  letI : TensorProduct.CompatibleSMul R T M' N' := ⟨fun t x y => by
    obtain ⟨r, rfl⟩ := hf t
    exact TensorProduct.smul_tmul r x y⟩
  letI : TensorProduct.CompatibleSMul T R M' N' :=
    ⟨fun r x y => TensorProduct.smul_tmul (f r) x y⟩
  let e := (TensorProduct.equivOfCompatibleSMul T R ℤ M' N').toAddEquiv
  refine { e with map_smul' := ?_ }
  intro r z
  show e (r • z) = (f r) • e z
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => rw [smul_add, e.map_add, hx, hy, e.map_add, smul_add]

open CochainTensor (ι tensorCofanIsColimit)

private def restrictedTensorCofan (X Y : Comp.{v} T) (n : ℤ) :=
  Cofan.mk (f := fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
    (res).obj (ModuleCat.of T (X.X p.1.1 ⊗[T] Y.X p.1.2)))
    ((res).obj ((tensor X Y).X n))
    (fun p => (res).map (ι X Y p.1.1 p.1.2 n p.2))

private def summandDiagramIso (X Y : Comp.{v} T) (n : ℤ) :
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      ModuleCat.of R ((res).obj (X.X p.1.1) ⊗[R] (res).obj (Y.X p.1.2))) ≅
    Discrete.functor (fun p : {p : ℤ × ℤ // p.1 + p.2 = n} =>
      (res).obj (ModuleCat.of T (X.X p.1.1 ⊗[T] Y.X p.1.2))) :=
  Discrete.natIso (fun ⟨p⟩ => (tensorSummandEquiv f hf (X.X p.1.1) (Y.X p.1.2)).toModuleIso)

/-- The target ring is in the module universe, so restriction preserves the coproduct. -/
private def restrictedTensorIsColimit (X Y : Comp.{v} T) (n : ℤ) :
    IsColimit ((Cocone.precompose (summandDiagramIso f hf X Y n).hom).obj
      (restrictedTensorCofan f X Y n)) :=
  (IsColimit.precomposeHomEquiv (summandDiagramIso f hf X Y n) _).symm
    (isColimitCofanMkObjOfIsColimit res _ _ (tensorCofanIsColimit X Y n))

private def tensorTermIso (X Y : Comp.{v} T) (n : ℤ) :
    (tensor ((restrict f).obj X) ((restrict f).obj Y)).X n ≅
      ((restrict f).obj (tensor X Y)).X n :=
  (tensorCofanIsColimit ((restrict f).obj X) ((restrict f).obj Y) n).coconePointUniqueUpToIso
    (restrictedTensorIsColimit f hf X Y n)

private theorem tensorTermIso_pure (X Y : Comp.{v} T) (i j n : ℤ) (h : i + j = n)
    (x : ((restrict f).obj X).X i) (y : ((restrict f).obj Y).X j) :
    (tensorTermIso f hf X Y n).hom (pure ((restrict f).obj X) ((restrict f).obj Y) h x y) =
      pure X Y h x y := by
  have eq := IsColimit.comp_coconePointUniqueUpToIso_hom
    (tensorCofanIsColimit ((restrict f).obj X) ((restrict f).obj Y) n)
    (restrictedTensorIsColimit f hf X Y n) ⟨⟨(i, j), h⟩⟩
  exact ConcreteCategory.congr_hom eq (x ⊗ₜ[R] y)

private theorem tensor_d_pure {A P : Comp.{v} R} (i j n : ℤ) (h : i + j = n)
    (x : A.X i) (y : P.X j) :
    (tensor A P).d n (n + 1) (pure A P h x y) =
      pure A P (by omega : (i + 1) + j = n + 1) (A.d i (i + 1) x) y +
        i.negOnePow • pure A P (by omega : i + (j + 1) = n + 1) x (P.d j (j + 1) y) :=
  CochainTensor.differential A P i j n h x y

/-- The comparison is a chain isomorphism for the actual signed differential. -/
private def restrictTensorIso (X Y : Comp.{v} T) :
    tensor ((restrict f).obj X) ((restrict f).obj Y) ≅ (restrict f).obj (tensor X Y) :=
  Hom.isoOfComponents (tensorTermIso f hf X Y) (by
    intro n n' hn
    obtain rfl : n + 1 = n' := hn
    apply CochainTensor.term_hom_ext
    intro i j h x y
    calc
      _ = (tensor X Y).d n (n + 1) (pure X Y h x y) := by
        rw [ModuleCat.comp_apply, tensorTermIso_pure]
        rfl
      _ = _ := by
        rw [tensor_d_pure (A := X) (P := Y) i j n h x y, ModuleCat.comp_apply,
          tensor_d_pure (A := (restrict f).obj X) (P := (restrict f).obj Y) i j n h x y]
        simp only [map_add, Units.smul_def, map_zsmul, tensorTermIso_pure]
        rfl)

end TensorComparison

/-- Every K-projective complex is K-flat, with both tests at the original module level. -/
theorem isKProjectiveIsKFlat :
    Specs.DerivedFormalization.KProjectiveFlatness.IsKProjectiveIsKFlat.{u,v} := by
  intro R _ P hP A hA
  let T : Type v := ScalarImage A P
  let f : R →+* T := (scalarAction A P).rangeRestrict
  have hf : Function.Surjective f := (scalarAction A P).rangeRestrict_surjective
  let ρA (i : ℤ) : T →+* AddMonoid.End (A.X i) :=
    (Pi.evalRingHom (fun j => AddMonoid.End (A.X j)) i).comp
      ((RingHom.fst _ _).comp (scalarAction A P).range.subtype)
  let ρP (i : ℤ) : T →+* AddMonoid.End (P.X i) :=
    (Pi.evalRingHom (fun j => AddMonoid.End (P.X j)) i).comp
      ((RingHom.snd _ _).comp (scalarAction A P).range.subtype)
  let A' := descend A f hf ρA (fun _ _ _ => rfl)
  let P' := descend P f hf ρP (fun _ _ _ => rfl)
  let eA : (restrict f).obj A' ≅ A := restrictDescendIso A f hf ρA (fun _ _ _ => rfl)
  let eP : (restrict f).obj P' ≅ P := restrictDescendIso P f hf ρP (fun _ _ _ => rfl)
  let := hP
  have hP' : CochainComplex.IsKProjective P' :=
    kProjective_of_restrict f hf P' (HomotopyEquiv.ofIso eP.symm).isKProjective
  have hA' : A'.Acyclic := (restrict_acyclic_iff f A').1 (fun i => (hA i).of_iso eA.symm)
  have hTensor := (restrict_acyclic_iff f (tensor A' P')).2 (isKFlat_of_small hP' A' hA')
  exact fun i => (hTensor i).of_iso ((restrictTensorIso f hf A' P').symm ≪≫ tensorIso eA eP)

end

end DerivedFormalization.KProjectiveFlatness
