import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn



open TopologicalSpace SeminormFamily Set Function Seminorm UniformSpace
open scoped BoundedContinuousFunction Topology NNReal

-- Think `𝕜 = ℝ` or `𝕜 = ℂ`
variable (𝕜 E F : Type*) [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable {n : ℕ∞}


-- Note: does it make sense to parametrize by some Ω : Opens E?
-- As opposed to taking the subtype if needed. Seems like most of time we will take the whole space
-- anyway / extend by garbage. This would also require to parammetrize D^n_K?
structure TestFunction (n : ℕ∞) : Type _ where
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected compact_supp' : HasCompactSupport toFun

scoped[Distributions] notation "𝓓^{" n "}(" E ", " F ")" =>
  TestFunction E F n

open Distributions

class TestFunctionClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  compact_supp (f : B) : HasCompactSupport f

open TestFunctionClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) [TestFunctionClass B E F n] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    rcases (map_continuous f).bounded_above_of_compact_support (compact_supp f) with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)


namespace TestFunction

instance toTestFunctionClass :
    TestFunctionClass 𝓓^{n}(E, F) E F n where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  compact_supp f := f.compact_supp'

variable {E F}

protected theorem contDiff (f : 𝓓^{n}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem compact_supp (f : 𝓓^{n}(E, F)) : HasCompactSupport f := compact_supp f

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.apply (f : 𝓓^{n}(E, F)) : E →F  := f

-- this must come after the coe_to_fun definition
initialize_simps_projections TestFunction (toFun → apply)

@[ext]
theorem ext {f g : 𝓓^{n}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `BoundedContDiffMap` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  compact_supp' := h.symm ▸ f.compact_supp

@[simp]
theorem coe_copy (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h


@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓓^{n}(E, F)) (x : E) :
   (f : BoundedContinuousFunction E F) x  = (f x) := rfl


section AddCommGroup

instance : Zero 𝓓^{n}(E, F) where
  zero := TestFunction.mk 0 contDiff_zero_fun HasCompactSupport.zero

@[simp]
lemma coe_zero : (0 : 𝓓^{n}(E, F)) = (0 : E → F) :=
  rfl

@[simp]
lemma zero_apply (x : E) : (0 : 𝓓^{n}(E, F)) x = 0 :=
  rfl

instance : Add 𝓓^{n}(E, F) where
  add f g := TestFunction.mk (f + g) (f.contDiff.add g.contDiff) (f.compact_supp.add g.compact_supp)

@[simp]
lemma coe_add (f g : 𝓓^{n}(E, F)) : (f + g : 𝓓^{n}(E, F)) = (f : E → F) + g :=
  rfl

@[simp]
lemma add_apply (f g : 𝓓^{n}(E, F)) (x : E) : (f + g) x = f x + g x :=
  rfl

instance : Neg 𝓓^{n}(E, F) where
  neg f := TestFunction.mk (-f) (f.contDiff.neg) (f.compact_supp.neg')

-- TOOD: add sub to HasCompactSupport in general
instance instSub : Sub 𝓓^{n}(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.contDiff').sub (g.contDiff'),
    sub_eq_add_neg (f : E → F) g ▸ f.compact_supp.add g.compact_supp.neg'
    ⟩
  ⟩

-- TOOD: add const_smul to HasCompactSupport (?)
instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
   SMul R 𝓓^{n}(E, F) :=
  ⟨fun c f ↦
    TestFunction.mk (c • (f : E → F)) (f.contDiff.const_smul c)  f.compact_supp.smul_left
  ⟩

@[simp]
lemma coe_smul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) : (c • f : 𝓓^{n}(E, F)) = c • (f : E → F) :=
  rfl

@[simp]
lemma smul_apply {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F]
    (c : R) (f : 𝓓^{n}(E, F)) (x : E) : (c • f) x = c • (f x) :=
  rfl


instance instNSMul : SMul ℕ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance instZSMul : SMul ℤ 𝓓^{n}(E, F) :=
 ⟨fun c f ↦
    {
      toFun := c • f
      contDiff' := (f.contDiff').const_smul c
      compact_supp' := f.compact_supp.smul_left
    }
  ⟩

instance : AddCommGroup 𝓓^{n}(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F K n)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓓^{n}(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F n : 𝓓^{n}(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F n) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

-- Note: This (and above) should probably be used more!
-- the ugy ext ... ext ... is in a lot of places.
instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}(E, F) :=
  (coeHom_injective n).module R (coeHom E F n) fun _ _ => rfl

end Module

variable (n : ℕ∞) (E F)

def ContDiffMapSupportedIn.toTestFunction (K : Compacts E) : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}(E, F) where
  toFun f := TestFunction.mk f (f.contDiff) (f.hasCompactSupport)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


open ContDiffMapSupportedIn

noncomputable def originalTop : TopologicalSpace 𝓓^{n}(E, F) :=
  ⨆ (K : Compacts E), coinduced (toTestFunction 𝕜 E F n K) (inferInstance)

noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}(E, F) :=
  sInf {t : TopologicalSpace 𝓓^{n}(E, F)
       | originalTop ℝ E F n ≤ t ∧ @LocallyConvexSpace ℝ 𝓓^{n}(E, F) _ _ _ _ t}

noncomputable instance : LocallyConvexSpace ℝ 𝓓^{n}(E, F) := by
  apply LocallyConvexSpace.sInf
  simp only [mem_setOf_eq, and_imp, imp_self, implies_true]

theorem continuous_toTestFunction (K : Compacts E):
    Continuous (toTestFunction 𝕜 E F n K) := by
  apply continuous_iff_coinduced_le.2
  have : originalTop 𝕜 E F n ≤ TestFunction.topologicalSpace E F n := by
    exact le_sInf (by aesop)
  exact le_trans (le_sSup (by aesop)) this

variable {n E F}

protected theorem continuous_iff {V : Type*} [AddCommMonoid V] [Module ℝ V] [Module 𝕜 V]
  [SMulCommClass ℝ 𝕜 V] [t : TopologicalSpace V] [LocallyConvexSpace ℝ V]
  (f : 𝓓^{n}(E, F) →ₗ[ℝ] V) :
    Continuous f ↔
    ∀ K : Compacts E, Continuous (f ∘ toTestFunction 𝕜 E F n K) := by
    rw [continuous_iff_le_induced]
    have : TestFunction.topologicalSpace E F n ≤ induced f t
          ↔ originalTop ℝ E F n ≤ induced f t := by
        constructor <;> refine fun h ↦ ?_
        · refine le_trans (le_sInf (fun _ _ ↦ ?_)) h
          simp_all only [LocallyConvexSpace.induced f, mem_setOf_eq]
        · refine sInf_le ?_
          simp only [mem_setOf_eq, LocallyConvexSpace.induced f, and_true, h]
    rw [this, originalTop, iSup_le_iff]
    simp_rw [← @coinduced_le_iff_le_induced _ _ f _ t, coinduced_compose]
    simp_rw [← continuous_iff_coinduced_le]
    rfl

variable (E F n)

@[simps]
noncomputable def to_bcfₗ : 𝓓^{n}(E, F) →ₗ[𝕜] E →ᵇ F  where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma to_bcf_comp_eq (K : Compacts E) :
  (to_bcfₗ 𝕜 E F n) ∘ (ContDiffMapSupportedIn.toTestFunction 𝕜 E F n K)  =
    ContDiffMapSupportedIn.to_bcfₗ 𝕜 := by
    congr

@[simps!]
noncomputable def to_bcfL : 𝓓^{n}(E, F) →L[𝕜] E →ᵇ F  :=
  { toLinearMap := to_bcfₗ 𝕜 E F n
    cont := show Continuous (to_bcfₗ ℝ E F n)
      by
        (
          rw [TestFunction.continuous_iff ℝ (to_bcfₗ ℝ E F n)]
          intro K
          rw [to_bcf_comp_eq _ _]
          exact (ContDiffMapSupportedIn.to_bcfL 𝕜).continuous
        )
  }

theorem injective_to_bcfL: Function.Injective (to_bcfL 𝕜 E F n) := by
  intro f g
  simp [to_bcfL, to_bcfₗ]

example : T25Space 𝓓^{n}(E, F) :=
  T25Space.of_injective_continuous (injective_to_bcfL ℝ E F n) (to_bcfL ℝ E F n).continuous

open ContDiffMapSupportedIn in
theorem continuous_of_commute_toTestFunction {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  (f : 𝓓^{n}(E, F) →ₗ[ℝ] 𝓓^{n}(E, G))
  (hKg : ∀ K : Compacts E, ∃ g : 𝓓^{n}_{K}(E, F) → 𝓓^{n}_{K}(E, G), Continuous g
        ∧ f ∘ toTestFunction ℝ E F n K = toTestFunction ℝ E G n K ∘ g) :
    Continuous f := by
  refine (TestFunction.continuous_iff ℝ f).mpr (fun K ↦ ?_)
  obtain ⟨g, hg, hfg⟩ := hKg K
  exact hfg ▸ (continuous_toTestFunction ℝ E G n K).comp hg


-- Sviluppare mkLM, mkCLM



section DiracDelta

variable {E}

noncomputable def delta (x : E) : 𝓓^{n}(E, F) →L[𝕜] F :=
  (BoundedContinuousFunction.evalCLM 𝕜 x).comp (to_bcfL 𝕜 E F n)

variable {F n}

@[simp]
theorem delta_apply (x₀ : E) (f : 𝓓^{n}(E, F)) : delta 𝕜 F n x₀ f = f x₀ :=
  rfl

end DiracDelta



end TestFunction
