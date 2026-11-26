import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalArtinAlgebras

/-! Fibre products and marked base change over local Artin algebras. -/

universe u v w z

namespace CommutativeAlgebraNotes

namespace LocalArtinAlgebra

variable {k : Type u} [Field k]

/-- Fibre product of any two local maps of Artin (k)-algebras into a common ring. -/
abbrev pullback {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :=
  pullbackModel f g

abbrev pullbackFst {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :=
  pullbackFstModel f g

abbrev pullbackSnd {A B C : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C) :=
  pullbackSndModel f g

open CategoryTheory CategoryTheory.Limits

variable {A B C W : LocalArtinAlgebra.{u,v} k} (f : Hom A C) (g : Hom B C)

theorem pullback_comm : f.comp (pullbackFst f g) = g.comp (pullbackSnd f g) :=
  Hom.ext fun x => x.property

/-- The map into a fibre product induced by a pair of compatible maps. -/
def pullbackLift (a : Hom W A) (b : Hom W B) (h : f.comp a = g.comp b) :
    Hom W (pullback f g) := by
  let p := (a : W →ₐ[k] A).prod (b : W →ₐ[k] B)
  let q : W →ₐ[k] pullback f g :=
    p.codRestrict (AlgHom.pullback (f : A →ₐ[k] C) (g : B →ₐ[k] C))
      (fun x => congrArg (fun e : Hom W C => e x) h)
  exact ⟨q, ⟨fun x hx =>
    IsUnit.of_map (a : W →ₐ[k] A) x (hx.map (pullbackFst f g : pullback f g →ₐ[k] A))⟩⟩

theorem pullback_hom_ext {l₁ l₂ : Hom W (pullback f g)}
    (h₁ : (pullbackFst f g).comp l₁ = (pullbackFst f g).comp l₂)
    (h₂ : (pullbackSnd f g).comp l₁ = (pullbackSnd f g).comp l₂) : l₁ = l₂ :=
  Hom.ext fun x => Subtype.ext <| Prod.ext
    (congrArg (fun e : Hom W A => e x) h₁) (congrArg (fun e : Hom W B => e x) h₂)

/-- The compatible-pair algebra satisfies the fibre-product universal property. -/
theorem isPullback : @CategoryTheory.IsPullback (LocalArtinAlgebra.{u,v} k) _
    (pullback f g) A B C (pullbackFst f g) (pullbackSnd f g) f g := by
  refine ⟨⟨pullback_comm f g⟩, ⟨PullbackCone.IsLimit.mk (pullback_comm f g) ?_ ?_ ?_ ?_⟩⟩
  · intro s
    exact pullbackLift f g s.fst s.snd s.condition
  · intro s
    exact Hom.ext (fun _ => rfl)
  · intro s
    exact Hom.ext (fun _ => rfl)
  · intro s m h₁ h₂
    exact pullback_hom_ext f g h₁ h₂

/-- Small extensions are surjections with a one-dimensional socle kernel. -/
def SmallExtension {A B : LocalArtinAlgebra.{u,v} k} (f : Hom A B) : Prop :=
  SmallExtensionModel f

/-- The base object (k). -/
abbrev field (k : Type u) [Field k] := fieldModel k

/-- The split square-zero object (koplus I). -/
abbrev split (k : Type u) [Field k] (I : Type v) [AddCommGroup I] [Module k I]
    [Module.Finite k I] := splitModel k I

/-- The dual numbers with their standard augmentation. -/
abbrev dualNumbers (k : Type u) [Field k] := dualModel k

/-- The augmentation induces the specified isomorphism on the residue field. -/
noncomputable def residueEquiv (A : LocalArtinAlgebra.{u,v} k) :
    IsLocalRing.ResidueField A ≃ₐ[k] k :=
  residueEquivModel A

@[simp]
theorem residueEquiv_residue (A : LocalArtinAlgebra.{u,v} k) (a : A) :
    A.residueEquiv (IsLocalRing.residue A a) = A.residue a := rfl

/-- The base field is terminal in the local Artin category. -/
theorem field_terminal (A : LocalArtinAlgebra.{u,u} k) :
    ∃! _ : Hom A (field k), True := by
  refine ⟨⟨A.residue, A.localResidue⟩, trivial, fun f _ => Hom.ext fun a => ?_⟩
  exact f.residue_apply a

/-- The base field is initial, with structural map to every object. -/
theorem field_initial (A : LocalArtinAlgebra.{u,u} k) :
    ∃! _ : Hom (field k) A, True := by
  let i := Algebra.ofId k A
  refine ⟨⟨i, ⟨fun a ha => ?_⟩⟩, trivial, fun f _ => Hom.ext fun a => ?_⟩
  · have h := ha.map A.residue
    change IsUnit (A.residue (algebraMap k A a)) at h
    exact (A.residue_algebraMap (a : k)) ▸ h
  · exact (f : field k →ₐ[k] A).commutes a

/-- The model of the dual numbers is the polynomial quotient by the square
of the variable, with the variable sent to the distinguished nilpotent. -/
theorem dualNumbers_presentation (k : Type u) [Field k] :
    ∃ e : AdjoinRoot ((Polynomial.X : Polynomial k) ^ 2) ≃ₐ[k] dualNumbers k,
      e (AdjoinRoot.root _) = (DualNumber.eps : DualNumber k) := by
  let p : Polynomial k := Polynomial.X ^ 2
  let i : AdjoinRoot p →ₐ[k] DualNumber k :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId k _) DualNumber.eps
      (by simp [p, pow_two, DualNumber.eps_mul_eps])
  have hroot : AdjoinRoot.root p * AdjoinRoot.root p = 0 := by
    have h := (AdjoinRoot.isRoot_root p).eq_zero
    simpa [p, pow_two] using h
  let j : DualNumber k →ₐ[k] AdjoinRoot p :=
    DualNumber.lift ⟨(Algebra.ofId k _, AdjoinRoot.root p), hroot, fun _ => Commute.all _ _⟩
  refine ⟨AlgEquiv.ofAlgHom i j ?_ ?_, ?_⟩
  · apply DualNumber.algHom_ext
    change i (j (DualNumber.eps : DualNumber k)) = DualNumber.eps
    simp only [i, j, DualNumber.lift_apply_eps, AdjoinRoot.liftAlgHom_root]
  · apply AdjoinRoot.algHom_ext
    change j (i (AdjoinRoot.root p)) = AdjoinRoot.root p
    simp only [i, j, DualNumber.lift_apply_eps, AdjoinRoot.liftAlgHom_root]
  · change i (AdjoinRoot.root p) = DualNumber.eps
    exact AdjoinRoot.liftAlgHom_root _ _ _ _

end LocalArtinAlgebra

namespace MarkedDeformation

open LocalArtinAlgebra

variable {k : Type u} [Field k] {A A' : LocalArtinAlgebra.{u,v} k}
variable {B : Type w} [CommRing B] [Algebra k B]

abbrev classOf (D : MarkedDeformation.{u,v,w,z} A B) : Classes.{u,v,w,z} A B := classModel D

/-- Two deformations define the same class exactly when they are marked-isomorphic. -/
theorem classOf_eq_iff {D E : MarkedDeformation.{u,v,w,z} A B} :
    classOf D = classOf E ↔
      ∃ e : D ≃ₐ[A] E, (specialFibreCongr e).trans E.marking = D.marking :=
  ⟨fun h => let ⟨⟨e, he⟩⟩ := Quotient.exact h; ⟨e, he⟩,
    fun ⟨e, he⟩ => Quotient.sound (show Isomorphic D E from ⟨⟨e, he⟩⟩)⟩

/-- Extension of scalars with the transported special-fibre marking. -/
abbrev baseChange (f : Hom A A') (D : MarkedDeformation.{u,v,w,z} A B) :=
  baseChangeModel f D

/-- Extension of scalars descends to marked isomorphism classes. -/
def baseChangeClasses (f : Hom A A') :
    Classes.{u,v,w,z} A B → Classes.{u,v,w,z} A' B :=
  baseChangeClassesModel f

@[simp]
theorem baseChangeClasses_classOf (f : Hom A A') (D : MarkedDeformation.{u,v,w,z} A B) :
    baseChangeClasses f (classOf D) = classOf (baseChange f D) :=
  rfl

open scoped TensorProduct

@[simp]
theorem baseChangeClasses_id (x : Classes.{u,v,w,z} A B) :
    baseChangeClasses (Hom.id A) x = x := by
  refine Quotient.inductionOn x fun D => ?_
  change classOf (baseChange (Hom.id A) D) = classOf D
  let e : (baseChange (Hom.id A) D) ≃ₐ[A] D := Algebra.TensorProduct.lid A D
  have hn : specialFibreCongr e = baseChangeSpecialFibre (Hom.id A) D := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro c x
    induction x using TensorProduct.inductionOn with
    | tmul a d =>
      change (c ⊗ₜ[A] (a • d)) = (a • c) ⊗ₜ[A] d
      exact TensorProduct.tmul_smul a c d
    | add x y ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
  exact classOf_eq_iff.mpr ⟨e, congrArg (fun a => a.trans D.marking) hn⟩

theorem baseChangeClasses_comp {A'' : LocalArtinAlgebra.{u,v} k}
    (f : Hom A A') (g : Hom A' A'') (x : Classes.{u,v,w,z} A B) :
    baseChangeClasses (g.comp f) x = baseChangeClasses g (baseChangeClasses f x) := by
  refine Quotient.inductionOn x fun D => ?_
  change classOf (baseChange (g.comp f) D) = classOf (baseChange g (baseChange f D))
  symm
  let : Algebra A A' := f.toAlgebra
  let : Algebra A' A'' := g.toAlgebra
  let : Algebra A A'' := (g.comp f).toAlgebra
  let : IsScalarTower A A' A'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := g.residueScalarTower
  let e : baseChange g (baseChange f D) ≃ₐ[A''] baseChange (g.comp f) D :=
    Algebra.TensorProduct.cancelBaseChange A A' A'' A'' D
  have hn :
      (specialFibreCongr e).trans (baseChangeSpecialFibre (g.comp f) D) =
        (baseChangeSpecialFibre g (baseChange f D)).trans (baseChangeSpecialFibre f D) := by
    apply AlgEquiv.coe_toAlgHom_injective
    apply Algebra.TensorProduct.ext'
    intro c y
    induction y using TensorProduct.inductionOn with
    | add x y ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
    | tmul b y =>
      induction y using TensorProduct.inductionOn with
      | add x y ihx ihy => simp only [TensorProduct.tmul_add, map_add, ihx, ihy]
      | tmul a d =>
        simp [e, specialFibreCongr, baseChangeSpecialFibre, smul_assoc]
  refine classOf_eq_iff.mpr ⟨e, AlgEquiv.ext fun x => ?_⟩
  simpa only [baseChange, baseChangeModel, AlgEquiv.trans_apply] using
    congrArg D.marking (DFunLike.congr_fun hn x)

end MarkedDeformation
end CommutativeAlgebraNotes
