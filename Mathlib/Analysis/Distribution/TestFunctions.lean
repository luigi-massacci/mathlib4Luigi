import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn



open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

-- Think `𝕜 = ℝ` or `𝕜 = ℂ`
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable {n : ℕ∞} {Ω : Opens E}


-- Note: does it make sense to parametrize by some Ω : Opens E?
-- As opposed to taking the subtype if needed. Seems like most of time we will take the whole space
-- anyway / extend by garbage
structure TestFunction (n : ℕ∞) (Ω : Opens E) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected compact_supp' : HasCompactSupport toFun
  protected supp_in' : tsupport toFun ⊆ Ω

scoped[Distributions] notation "𝓓^{"n"}_{"Ω"}(" E ", " F ")" =>
  TestFunction E F n Ω

open Distributions

class TestFunctionClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (Ω : outParam <| Opens E) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  compact_supp (f : B) : HasCompactSupport f
  supp_in (f : B) : tsupport f ⊆ Ω


open TestFunctionClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (Ω : outParam <| Opens E) [TestFunctionClass B E F n Ω ] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (Ω : outParam <| Opens E) [TestFunctionClass B E F n Ω] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    rcases (map_continuous f).bounded_above_of_compact_support (compact_supp f) with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)


namespace TestFunction

instance toTestFunctionClass :
    TestFunctionClass 𝓓^{n}_{Ω}(E, F) E F n Ω where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  compact_supp f := f.compact_supp'
  supp_in f := f.supp_in'

variable {E F}


protected theorem contDiff (f : 𝓓^{n}_{Ω}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem compact_supp (f : 𝓓^{n}_{Ω}(E, F)) : HasCompactSupport f := compact_supp f
protected theorem supp_in (f : 𝓓^{n}_{Ω}(E, F)) : tsupport f ⊆ Ω := supp_in f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}_{Ω}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}_{Ω}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections TestFunction (toFun → apply)

@[ext]
theorem ext {f g : 𝓓^{n}_{Ω}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}_{Ω}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}_{Ω}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  compact_supp' := h.symm ▸ f.compact_supp
  supp_in' := h.symm ▸ f.supp_in

@[simp]
theorem coe_copy (f : 𝓓^{n}_{Ω}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}_{Ω}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h


@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}_{Ω}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl


section AddCommGroup

lemma tsupport_zero_eq_empty : tsupport (0 : E → F) = ∅ := by
  exact tsupport_eq_empty_iff.mpr rfl

instance : Zero 𝓓^{n}_{Ω}(E, F) where
  zero := TestFunction.mk 0 contDiff_zero_fun HasCompactSupport.zero
          (le_of_eq_of_le tsupport_zero_eq_empty (empty_subset _ ))

@[simp]
lemma coe_zero : (0 : 𝓓^{n}_{Ω}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}_{Ω}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}_{Ω}(E, F) where
  add f g := TestFunction.mk (f + g) (f.contDiff.add g.contDiff) (f.compact_supp.add g.compact_supp)
             (le_trans tsupport_add (union_subset_iff.mpr ⟨f.supp_in, g.supp_in⟩))

@[simp]
lemma coe_add (f g : 𝓓^{n}_{Ω}(E, F)) : (f + g : 𝓓^{n}_{Ω}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}_{Ω}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

lemma tsupport_neg (f : E → F) : tsupport (-f) ⊆ tsupport f := by
    rw [show -f = (-1) • f by rw [neg_smul, one_smul]]
    convert tsupport_smul_subset_right (fun x ↦ -1) f

instance : Neg 𝓓^{n}_{Ω}(E, F) where
  neg f := TestFunction.mk (-f) (f.contDiff.neg) (f.compact_supp.neg')
           (le_trans (tsupport_neg f) f.supp_in)

-- TOOD: add sub to HasCompactSupport in general
instance instSub : Sub 𝓓^{n}_{Ω}(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.contDiff').sub (g.contDiff'),
    sub_eq_add_neg (f : E → F) g ▸ f.compact_supp.add g.compact_supp.neg',
    (by
      rw [sub_eq_add_neg]
      apply le_trans tsupport_add (union_subset_iff.mpr ⟨f.supp_in, ?_⟩)
      apply le_trans (tsupport_neg g) g.supp_in
    )
    ⟩
  ⟩

-- TOOD: add const_smul to HasCompactSupport (?)
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}_{Ω}(E, F) :=
  ⟨fun c f ↦
    TestFunction.mk (c • (f : E → F)) (f.contDiff.const_smul c) f.compact_supp.smul_left
    (le_trans (tsupport_smul_subset_right (fun _ ↦ c) f) f.supp_in)
  ⟩

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{Ω}(E, F)) : (c • f : 𝓓^{n}_{Ω}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}_{Ω}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl


instance instNSMul : SMul ℕ 𝓓^{n}_{Ω}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
      supp_in' := (le_trans (tsupport_smul_subset_right (fun _ ↦ c) f) f.supp_in)
    }
  ⟩

instance instZSMul : SMul ℤ 𝓓^{n}_{Ω}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
      supp_in' := (le_trans (tsupport_smul_subset_right (fun _ ↦ c) f) f.supp_in)
    }
  ⟩

instance : AddCommGroup 𝓓^{n}_{Ω}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F K n Ω)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}_{Ω}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n Ω: 𝓓^{n}_{Ω}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n Ω) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

-- Note: This should probably be used more! the ugly ext ... ext ... is in a lot of places.
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{Ω}(E, F) :=
  (coeHom_injective n Ω).module R (coeHom E F n Ω) fun _ _ => rfl

end Module

variable (n : ℕ∞) (E F)

def ContDiffMapSupportedIn.toTestFunction (K : Compacts E) : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}_{Ω}(E, F) where
  toFun f := TestFunction.mk f (f.contDiff) (f.hasCompactSupport) (sorry)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def topologicalSpace0 : TopologicalSpace 𝓓^{n}_{Ω}(E, F) :=
  ⨆ (K : Compacts E), coinduced (ContDiffMapSupportedIn.toTestFunction 𝕜 E F n K) (inferInstance)

noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{Ω}(E, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}_{Ω}(E, F)
       | topologicalSpace0 ℝ E F n ≤ t ∧ @LocallyConvexSpace ℝ 𝓓^{n}_{Ω}(E, F) _ _ _ _ t}

example (K : Compacts E): Continuous (ContDiffMapSupportedIn.toTestFunction 𝕜 E F n K) := by
  apply continuous_iff_coinduced_le.2
  have : topologicalSpace0 𝕜 E F n ≤ TestFunction.topologicalSpace E F n := by
    exact le_sInf (by aesop)
  exact le_trans (le_sSup (by aesop)) this

protected theorem continuous_iff {V : Type*} [AddCommMonoid V] [Module ℝ V]
  [t : TopologicalSpace V] [LocallyConvexSpace ℝ V] (f : 𝓓^{n}_{Ω}(E, F) →ₗ[ℝ] V) :
    Continuous f ↔
    ∀ K : Compacts E, Continuous (f ∘ ContDiffMapSupportedIn.toTestFunction 𝕜 E F n K) := by
    rw [continuous_iff_le_induced]
    have : TestFunction.topologicalSpace E F n ≤ induced f t
          ↔ topologicalSpace0 ℝ E F n ≤ induced f t := by
        constructor <;> refine fun h ↦ ?_
        · refine le_trans (le_sInf (fun _ _ ↦ ?_)) h
          simp_all only [LocallyConvexSpace.induced f, mem_setOf_eq]
        · refine sInf_le ?_
          simp only [mem_setOf_eq, LocallyConvexSpace.induced f, and_true, h]
    rw [this, topologicalSpace0, iSup_le_iff]
    simp_rw [← @coinduced_le_iff_le_induced _ _ f _ t, coinduced_compose]
    simp_rw [← continuous_iff_coinduced_le]
    rfl


end TestFunction
