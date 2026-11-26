import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct

open scoped TensorProduct
open TensorProduct

namespace CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct

universe u v w v' w'

variable (D : Type u) [CommRing D] (a b : ℕ)

@[simp] theorem jointEquiv_includeX (f : X D a) :
    jointEquiv D a b (includeX D a b f) =
      MvPowerSeries.rename (R := D) (Sum.inl : Fin a → Fin a ⊕ Fin b) f := by
  change MvPowerSeries.rename _ (MvPowerSeries.rename Sum.inl f) = _
  rw [MvPowerSeries.rename_rename]
  rfl

@[simp] theorem jointEquiv_includeY (f : X D b) :
    jointEquiv D a b (includeY D a b (xToY D b f)) =
      MvPowerSeries.rename (R := D) (Sum.inr : Fin b → Fin a ⊕ Fin b) f := by
  change MvPowerSeries.rename _ (MvPowerSeries.rename Sum.inr (MvPowerSeries.rename _ f)) = _
  rw [MvPowerSeries.rename_rename, MvPowerSeries.rename_rename]
  rfl

variable (M : Type v) (N : Type w) [AddCommGroup M] [Module (X D a) M] [AddCommGroup N]

/-- The exterior tensor product over the coefficient ring `D`, with its `S`-action
on the leftmost factor. -/
noncomputable abbrev Product [Module (Y D b) N] :=
  (S D a b ⊗[X D a] M) ⊗[Y D b] N

/-- The exterior tensor product of modules over a single power-series ring. -/
noncomputable abbrev diagonal [Module (X D a) N] :=
  Product D a a M (OnY N)

@[simp] theorem smul_tmul [Module (Y D b) N] (r s : S D a b) (m : M) (n : N) :
    r • ((s ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n : Product D a b M N) =
      ((r * s) ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n :=
  rfl

section Maps

variable {D a b M N} [Module (Y D b) N]
variable {M' : Type v'} {N' : Type w'}
variable [AddCommGroup M'] [Module (X D a) M'] [AddCommGroup N'] [Module (Y D b) N']

/-- Apply a linear map to each argument of the exterior tensor product. -/
noncomputable def map (f : M →ₗ[X D a] M') (g : N →ₗ[Y D b] N') :
    Product D a b M N →ₗ[S D a b] Product D a b M' N' :=
  AlgebraTensorModule.map (f.baseChange (S D a b)) g

@[simp] theorem map_tmul (f : M →ₗ[X D a] M') (g : N →ₗ[Y D b] N') (s : S D a b) (m : M) (n : N) :
    map f g ((s ⊗ₜ[X D a] m) ⊗ₜ[Y D b] n) =
      (s ⊗ₜ[X D a] f m) ⊗ₜ[Y D b] g n :=
  rfl

@[simp] theorem map_id :
    map (LinearMap.id : M →ₗ[X D a] M) (LinearMap.id : N →ₗ[Y D b] N) = LinearMap.id := by
  rw [map, LinearMap.baseChange_id, AlgebraTensorModule.map_id]

theorem map_comp {M'' N'' : Type*}
    [AddCommGroup M''] [Module (X D a) M''] [AddCommGroup N''] [Module (Y D b) N'']
    (f₁ : M →ₗ[X D a] M') (f₂ : M' →ₗ[X D a] M'')
    (g₁ : N →ₗ[Y D b] N') (g₂ : N' →ₗ[Y D b] N'') :
    map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) := by
  simp only [map, LinearMap.baseChange_comp, AlgebraTensorModule.map_comp]

theorem map_add_left (f₁ f₂ : M →ₗ[X D a] M') (g : N →ₗ[Y D b] N') :
    map (f₁ + f₂) g = map f₁ g + map f₂ g := by
  simp only [map, LinearMap.baseChange_add, AlgebraTensorModule.map_add_left]

theorem map_add_right (f : M →ₗ[X D a] M') (g₁ g₂ : N →ₗ[Y D b] N') :
    map f (g₁ + g₂) = map f g₁ + map f g₂ :=
  AlgebraTensorModule.map_add_right _ _ _

end Maps

section Finiteness

variable {D a b M N} [Module (Y D b) N]

/-- Pairs of generators in the original modules generate over the joint ring. -/
theorem span_pairs {ι κ : Type*} (m : ι → M) (n : κ → N)
    (hm : Submodule.span (X D a) (Set.range m) = ⊤)
    (hn : Submodule.span (Y D b) (Set.range n) = ⊤) :
    Submodule.span (S D a b)
      (Set.range (fun p : ι × κ => (((1 : S D a b) ⊗ₜ[X D a] m p.1) ⊗ₜ[Y D b] n p.2 :
        Product D a b M N))) = ⊤ := by
  let P := Submodule.span (S D a b)
    (Set.range (fun p : ι × κ => (((1 : S D a b) ⊗ₜ[X D a] m p.1) ⊗ₜ[Y D b] n p.2 :
      Product D a b M N)))
  change P = ⊤
  have hright (i : ι) (y : N) : ((1 : S D a b) ⊗ₜ[X D a] m i) ⊗ₜ[Y D b] y ∈ P := by
    have hy : y ∈ Submodule.span (Y D b) (Set.range n) := hn ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Submodule.subset_span ⟨(i, j), rfl⟩
    | zero => simpa only [tmul_zero] using P.zero_mem
    | add y z _ _ hy hz => simpa only [tmul_add] using P.add_mem hy hz
    | smul r y _ hy =>
      rw [tmul_smul]
      exact P.smul_mem (algebraMap (Y D b) (S D a b) r) hy
  have hleft (x : M) (y : N) : ((1 : S D a b) ⊗ₜ[X D a] x) ⊗ₜ[Y D b] y ∈ P := by
    have hx : x ∈ Submodule.span (X D a) (Set.range m) := hm ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hright i y
    | zero => simpa only [tmul_zero, zero_tmul] using P.zero_mem
    | add x z _ _ hx hz => simpa only [tmul_add, add_tmul] using P.add_mem hx hz
    | smul r x _ hx =>
      rw [tmul_smul]
      exact P.smul_mem (algebraMap (X D a) (S D a b) r) hx
  have hall (z : Product D a b M N) : z ∈ P := by
    induction z using TensorProduct.inductionOn with
    | add z t hz ht => exact P.add_mem hz ht
    | tmul x y =>
      induction x using TensorProduct.inductionOn with
      | add x t hx ht => simpa only [add_tmul] using P.add_mem hx ht
      | tmul s x =>
        rw [tmul_eq_smul_one_tmul s x, ← smul_tmul']
        exact P.smul_mem s (hleft x y)
  exact eq_top_iff.mpr fun z _ => hall z

scoped instance finite [Module.Finite (X D a) M] [Module.Finite (Y D b) N] :
    Module.Finite (S D a b) (Product D a b M N) := by
  obtain ⟨i, m, hm⟩ := Module.Finite.exists_fin (R := X D a) (M := M)
  obtain ⟨j, n, hn⟩ := Module.Finite.exists_fin (R := Y D b) (M := N)
  refine Module.Finite.of_fg_top ?_
  rw [← span_pairs m n hm hn]
  exact Submodule.fg_span (Set.finite_range _)

end Finiteness

section Diagonal

variable {D a} {P : Type*} [AddCommGroup P] [Module (X D a) P]

@[simp] theorem toY_smul (r : X D a) (p : P) :
    toY (r • p) = xToY D a r • toY p := by
  change r • p = (xToY D a).symm (xToY D a r) • p
  rw [(xToY D a).symm_apply_apply]

omit [AddCommGroup P] in
theorem toY_bijective : Function.Bijective (toY : P → OnY P) :=
  ⟨fun _ _ h => h, fun p => ⟨p, rfl⟩⟩

/-- The identity on elements, semilinear for the variable renaming. -/
noncomputable def toYSemilinear : P →ₛₗ[(xToY D a).toRingHom] OnY P where
  toFun := toY
  map_add' _ _ := rfl
  map_smul' := toY_smul

instance onYFinite [Module.Finite (X D a) P] : Module.Finite (Y D a) (OnY P) :=
  Module.Finite.of_surjective (toYSemilinear (D := D) (a := a) (P := P)) toY_bijective.surjective

variable {P' : Type*} [AddCommGroup P'] [Module (X D a) P']

/-- Regard a linear map as a map between the corresponding right-variable modules. -/
noncomputable def onYMap (f : P →ₗ[X D a] P') : OnY P →ₗ[Y D a] OnY P' where
  toFun p := f p
  map_add' := f.map_add
  map_smul' r := f.map_smul ((xToY D a).symm r)

@[simp] theorem onYMap_toY (f : P →ₗ[X D a] P') (p : P) :
    onYMap f (toY p) = toY (f p) :=
  rfl

end Diagonal

end CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
