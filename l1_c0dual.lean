import Mathlib

open Filter Finset Real

-- Prove that the set of bounded sequences converging to $0$ at infinity is closed in $ℓ^∞$
lemma c0_isClosed : IsClosed {x : (lp (fun _ : ℕ => ℝ) ⊤)| Tendsto x atTop (nhds 0)} := by
  rw [← closure_eq_iff_isClosed]; ext a
  rw [Set.mem_setOf, Metric.mem_closure_iff]
  simp only [Metric.tendsto_atTop, gt_iff_lt, Set.mem_setOf_eq, Subtype.exists, exists_and_left, ge_iff_le,
    dist_zero_right, Real.norm_eq_abs]
  constructor
  · intro h ε εpos; specialize h (ε / 2) (by positivity)
    rcases h with ⟨b, hb, hab⟩; specialize hb (ε / 2) (by positivity)
    rcases hb with ⟨N, hN⟩; rcases hab with ⟨bmem, hab⟩
    rw [dist_eq_norm] at hab
    have := lp.norm_apply_le_norm (show ⊤ ≠ 0 by simp) (a - ⟨b, bmem⟩)
    simp only [AddSubgroupClass.coe_sub, Pi.sub_apply, Real.norm_eq_abs] at this
    use N; intro n nge; specialize hN n nge; calc
      _ = |a n - b n + b n| := by simp
      _ ≤ _ := abs_add _ _
      _ < _ := by
        rw [show ε = ε / 2 + ε / 2 by ring]; gcongr
        · apply lt_of_le_of_lt _ hab; apply this
  intros; use a; simp only [Subtype.coe_eta, dist_self, SetLike.coe_mem, exists_const]
  constructor; all_goals assumption

-- Define $c0$ to be the closed subspace of $ℓ^∞$ consisting of bounded sequences converging to $0$ at infinity
noncomputable def c0 : ClosedSubmodule ℝ (lp (fun _ : ℕ => ℝ) ⊤) := {
  carrier := setOf fun x => Tendsto x.val atTop (nhds 0)
  add_mem' := by
    simp only [Subtype.forall, AddMemClass.mk_add_mk, Set.mem_setOf]
    intros; rw [show (0:ℝ) = 0+0 by simp]
    apply Tendsto.add; all_goals assumption
  smul_mem' := by
    simp only [Set.mem_setOf_eq, lp.coeFn_smul, Subtype.forall]
    intro c _ _ _; rw [show (0:ℝ) = c•0 by simp]
    apply Tendsto.const_smul; assumption
  isClosed' := c0_isClosed
  zero_mem' := by
    simp [Metric.tendsto_atTop, ← lp.coeFn_zero (fun i : ℕ => ℝ) ⊤]
    intros; use 1; intros; assumption
}

-- Prove that the $i$-th coordinate function belongs to $c0$ for all $i$
lemma single_mem_c0 : ∀ i, lp.single ⊤ i 1 ∈ c0 := by
  intro i; simp [c0, Metric.tendsto_atTop]
  intro ε εpos; use i + 1; intro n nge
  rw [Pi.single_eq_of_ne, abs_zero]
  exact εpos; omega

-- Prove an auxillary identity about the absolute value of a real number
lemma aux_abs_real : ∀ r : ℝ, |r| = r.sign * r := by
  intro r; rw [abs, sign]; split_ifs with h h'
  · rw [neg_one_mul]; apply max_eq_right
    linarith only [h]
  · rw [one_mul]; apply max_eq_left
    linarith only [h']
  · simp [show r = 0 by linarith]

-- Prove that the multiplication of an $ℓ¹$-sequence and an $ℓ^∞$-sequence is absolutely summable, and the sum is at most the product of the norms of the two sequences.
lemma summable_mul : ∀ (x : lp (fun _ : ℕ => ℝ) 1) (a : lp (fun _ : ℕ => ℝ) ⊤), Summable (fun i => |x i| * |a i|)
    ∧ ∑' i, |x i| * |a i| ≤ ‖x‖ * ‖a‖ := by
  intro x a; simp only
  have : ∀ (n : ℕ), ∑ i ∈ range n, |x i| * |a i| ≤ ‖x‖ * ‖a‖ := by
    intro n; calc
      _ ≤ ∑ i ∈ range n, |x i| * ‖a‖ := by
        apply sum_le_sum; intros; gcongr
        rw [← norm_eq_abs]; apply lp.norm_apply_le_norm
        · simp
      _ ≤ ‖x‖ * ‖a‖ := by
        rw [← sum_mul]; gcongr
        · simp only [ENNReal.toReal_one, zero_lt_one, lp.norm_eq_tsum_rpow, norm_eq_abs,
          rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
          apply Summable.sum_le_tsum
          · intros; positivity
          · have : (fun i => |x i|) = fun i => ‖x i‖ ^ (1 : ENNReal).toReal := by ext; simp
            rw [this]; apply (lp.memℓp x).summable; simp
  constructor
  · exact summable_of_sum_range_le (by intro; positivity) this
  apply Summable.tsum_le_of_sum_range_le
  · exact summable_of_sum_range_le (by intro; positivity) this
  exact this

-- Prove that any member of $c0$ has a standard summation identity with respect to the coordinate functions $lp.single ⊤ i 1$
lemma hasSum_single_c0 : ∀ a : c0.toSubmodule, HasSum (fun i => a.val i • ⟨lp.single ⊤ i 1, single_mem_c0 i⟩) a := by
  rintro ⟨a, amem⟩; rw [HasSum, Metric.tendsto_atTop]
  intro ε εpos; simp only [c0, Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_zero_right,
    norm_eq_abs, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq] at amem
  specialize amem (ε / 2) (by positivity); rcases amem with ⟨N, hN⟩
  simp only [ge_iff_le, le_eq_subset, SetLike.mk_smul_mk, Subtype.dist_eq,
    AddSubmonoidClass.coe_finset_sum]
  use range N; intro n sbst
  rw [dist_eq_norm, norm_sub_rev, lp.norm_eq_ciSup]; calc
    _ ≤ ε / 2 := by
      apply Real.iSup_le; intro i
      simp only [AddSubgroupClass.coe_sub, AddSubgroup.val_finset_sum, lp.coeFn_smul, Pi.sub_apply,
        sum_apply, Pi.smul_apply, lp.single_apply, smul_eq_mul, norm_eq_abs]
      by_cases h : i ∈ n
      · rw [sum_eq_single_of_mem _ h]
        simp only [Pi.single_eq_same, mul_one, sub_self, abs_zero]
        positivity
        · intros; rw [Pi.single_eq_of_ne]; simp
          omega
      rw [sum_eq_zero, sub_zero]; apply le_of_lt
      apply hN; revert h; contrapose!
      intro h; apply sbst; simp [h]
      · intro _ h'; rw [Pi.single_eq_of_ne]; simp
        intro heq; rw [heq] at h; contradiction
      · positivity
    _ < _ := by linarith only [εpos]

-- Construct the natural map from $ℓ¹$ to the dual space of $c0$
noncomputable def LI_ℓ1_c0dual_toFun : (lp (fun _ : ℕ => ℝ) 1) → (NormedSpace.Dual ℝ c0.toSubmodule) :=
  fun ⟨x, hx⟩ => {
    toFun := fun ⟨⟨a, ha⟩, amem⟩ => ∑' i, (x * a) i
    map_add' := by
      simp only [Subtype.forall, mul_add]; intro a ha amem b hb bmem
      have : ∀ i, (x * a + x * b) i = (x * a) i + (x * b) i := by intro; rfl
      rw [tsum_congr this, Summable.tsum_add]
      · rw [← summable_abs_iff]; replace this := (summable_mul ⟨x, hx⟩ ⟨a, ha⟩).left
        simp only [← abs_mul] at this; exact this
      · rw [← summable_abs_iff]; replace this := (summable_mul ⟨x, hx⟩ ⟨b, hb⟩).left
        simp only [← abs_mul] at this; exact this
    map_smul' := by
      simp only [RingHom.id_apply, smul_eq_mul, Subtype.forall]
      intro r a ha amem
      have : ∀ i, (x * r • a) i = r * (x * a) i := by
        intro; simp only [Algebra.mul_smul_comm]; rfl
      rw [tsum_congr this, Summable.tsum_mul_left]
      · rw [← summable_abs_iff]; replace this := (summable_mul ⟨x, hx⟩ ⟨a, ha⟩).left
        simp only [← abs_mul] at this; exact this
    cont := by
      simp only [Metric.continuous_iff, gt_iff_lt, Subtype.forall, dist_eq_norm]
      intro a ha amem ε εpos
      by_cases h : x = 0
      · simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub, h, zero_mul, sub_self,
        norm_zero]
        use 1; constructor; positivity
        intros; exact εpos
      replace h : 0 < ‖(⟨x, hx⟩ : lp (fun x => ℝ) 1)‖ := by simp [h]
      use ε / ‖(⟨x, hx⟩ : lp (fun x => ℝ) 1)‖; constructor; positivity
      intro b hb _ bnorm
      simp only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub] at bnorm
      have : ∀ i, ((x * b) i - (x * a) i) = x i * (b - a) i := by
        intro; rw [Pi.mul_apply, Pi.mul_apply, Pi.sub_apply, mul_sub]
      rw [← Summable.tsum_sub, tsum_congr this, norm_eq_abs]
      replace this := AddSubgroup.sub_mem (lp (fun x => ℝ) ⊤) hb ha
      calc
        _ ≤ ∑' (b_1 : ℕ), |x b_1| * |(b - a) b_1| := by
          have := (summable_mul ⟨x, hx⟩ ⟨b - a, this⟩).left
          simp only at this
          rw [abs_le, ← tsum_neg]; constructor
          all_goals apply Summable.tsum_le_tsum
          · intro; rw [← abs_mul]; apply neg_abs_le
          · apply Summable.neg; exact this
          any_goals rw [← summable_abs_iff]; simp only [abs_mul]; exact this
          · intro; rw [← abs_mul]; apply le_abs_self
          · exact this
        _ ≤ _ := (summable_mul ⟨x, hx⟩ ⟨b - a, this⟩).right
        _ < _ := by
          rw [lt_div_iff₀'] at bnorm; all_goals assumption
      · rw [← summable_abs_iff]; replace this := (summable_mul ⟨x, hx⟩ ⟨b, hb⟩).left
        simp only [← abs_mul] at this; exact this
      · rw [← summable_abs_iff]; replace this := (summable_mul ⟨x, hx⟩ ⟨a, ha⟩).left
        simp only [← abs_mul] at this; exact this
    }

-- Prove that $LI_ℓ1_c0dual_toFun$ preserves norms
lemma LI_ℓ1_c0dual_toFun_norm_eq : ∀ x, ‖LI_ℓ1_c0dual_toFun x‖ = ‖x‖ := by
  intro x; simp only [eq_iff_le_not_lt, not_lt]
  constructor
  · rw [ContinuousLinearMap.opNorm_le_iff (norm_nonneg _)]
    rintro ⟨a, amem⟩
    have := summable_mul x a; calc
      _ = |∑' i, x i * a i| := rfl
      _ ≤ ∑' i, |x i| * |a i| := by
        rw [abs_le, ← tsum_neg]; constructor
        all_goals apply Summable.tsum_le_tsum
        · intro; rw [← abs_mul]; apply neg_abs_le
        · apply Summable.neg; exact this.left
        any_goals rw [← summable_abs_iff]; simp only [abs_mul]; exact this.left
        · intro; rw [← abs_mul]; apply le_abs_self
        · exact this.left
      _ ≤ _ := by
        rw [← Submodule.norm_coe]; exact this.right
  rw [lp.norm_eq_tsum_rpow (by simp) x]
  simp only [norm_eq_abs, ENNReal.toReal_one, rpow_one, ne_eq, one_ne_zero, not_false_eq_true, div_self]
  have := (lp.memℓp x).summable
  simp only [ENNReal.toReal_one, zero_lt_one, norm_eq_abs, rpow_one, forall_const] at this
  apply this.tsum_le_of_sum_range_le
  · intro n; simp only [aux_abs_real]
    let xn := (∑ j ∈ range n, (x j).sign • (@Pi.single ℕ (fun _ => ℝ) _ _ j 1) : PreLp (fun _ : ℕ => ℝ))
    have hxn : ∀ i ∈ range n, xn i = (x i).sign := by
      intro i hi; dsimp [xn]
      rw [sum_apply, sum_eq_single_of_mem _ hi]; simp
      · intros; simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, Real.sign_eq_zero_iff]
        right; apply Pi.single_eq_of_ne; omega
    have hxn' : ∀ i ∉ range n, xn i = 0 := by
      intro _ h; dsimp [xn]; rw [sum_apply, sum_eq_zero]
      · intro _ h'; simp at h h'
        simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, Real.sign_eq_zero_iff]
        right; apply Pi.single_eq_of_ne; omega
    have xn_mem : xn ∈ lp (fun _ : ℕ => ℝ) ⊤ := by
      simp only [lp, AddSubgroup.mem_mk, Set.mem_setOf_eq]
      apply memℓp_infty; use 1; simp only [upperBounds, norm_eq_abs, Set.mem_range,
        forall_exists_index, forall_apply_eq_imp_iff, Set.mem_setOf_eq]
      intro i; by_cases hi : i ∈ range n
      · simp only [hxn _ hi, sign]
        split_ifs; all_goals norm_num
      simp [hxn' _ hi]
    have xn_c0 : ⟨xn, xn_mem⟩ ∈ c0 := by
      simp only [c0, ClosedSubmodule.mem_mk, Submodule.mem_mk, AddSubmonoid.mem_mk,
        AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
      simp only [Metric.tendsto_atTop, gt_iff_lt, ge_iff_le, dist_zero_right, norm_eq_abs]
      intros; use n; intro m mge
      rw [hxn', abs_zero]; assumption
      · simp only [mem_range, not_lt]; exact mge
    have xn_c0_norm : ‖(⟨⟨xn, xn_mem⟩, xn_c0⟩ : c0.toSubmodule)‖ ≤ 1 := by
      simp only [AddSubgroupClass.coe_norm, lp.norm_eq_ciSup, norm_eq_abs]
      apply Real.iSup_le
      · intro i; by_cases h : i ∈ range n
        · simp only [hxn _ h, sign]; split_ifs
          all_goals norm_num
        simp [hxn' _ h]
      simp
    calc
      _ = ∑ i ∈ range n, x i * xn i := by
        apply sum_congr rfl
        · intro i hi; rw [mul_comm]; congr
          symm; exact hxn _ hi
      _ = ‖LI_ℓ1_c0dual_toFun x ⟨⟨xn, xn_mem⟩, xn_c0⟩‖ := by
        simp only [LI_ℓ1_c0dual_toFun, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
          AddHom.coe_mk, norm_eq_abs]
        have : ∀ i ∉ range n, (x * xn) i = 0 := by
          intro i hi; rw [Pi.mul_apply, hxn' _ hi]
          simp
        rw [tsum_eq_sum this, abs_eq_self.mpr]; rfl
        · apply sum_nonneg; intro _ h
          dsimp [xn]; rw [Pi.mul_apply, sum_apply, sum_eq_single_of_mem _ h]
          simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
          rw [mul_comm]; apply sign_mul_nonneg
          · intros; simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero, Real.sign_eq_zero_iff]
            right; apply Pi.single_eq_of_ne; omega
      _ ≤ _ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by
        nth_rw 2 [← mul_one ‖LI_ℓ1_c0dual_toFun x‖]
        apply mul_le_mul_of_nonneg_left
        · exact xn_c0_norm
        positivity

-- Construct the linear isometry from $ℓ¹$ to the dual space of $c0$ using `LI_ℓ1_c0dual_toFun` and `LI_ℓ1_c0dual_toFun_norm_eq`
noncomputable def LI_ℓ1_c0dual : LinearIsometry (RingHom.id ℝ) (lp (fun _ : ℕ => ℝ) 1) (NormedSpace.Dual ℝ c0.toSubmodule) := {
  toFun := LI_ℓ1_c0dual_toFun
  map_add' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩; ext ⟨⟨a, ha⟩, _⟩; simp only [LI_ℓ1_c0dual_toFun, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.add_apply]
    rw [← Summable.tsum_add]; apply tsum_congr
    · intro; repeat rw [Pi.mul_apply]
      rw [Pi.add_apply, add_mul]
    · rw [← summable_abs_iff]; have := (summable_mul ⟨x, hx⟩ ⟨a, ha⟩).left
      simp only [← abs_mul] at this; exact this
    · rw [← summable_abs_iff]; have := (summable_mul ⟨y, hy⟩ ⟨a, ha⟩).left
      simp only [← abs_mul] at this; exact this
  map_smul' := by
    rintro r ⟨x, hx⟩; ext ⟨⟨a, ha⟩, _⟩; simp only [LI_ℓ1_c0dual_toFun, ContinuousLinearMap.coe_mk',
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, ContinuousLinearMap.coe_smul',
      Pi.smul_apply, smul_eq_mul]
    rw [← Summable.tsum_mul_left]; apply tsum_congr
    · intro; rw [Pi.mul_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
    · rw [← summable_abs_iff]; have := (summable_mul ⟨x, hx⟩ ⟨a, ha⟩).left
      simp only [← abs_mul] at this; exact this
  norm_map' := LI_ℓ1_c0dual_toFun_norm_eq
}

-- Prove that for any $f$ in the dual space of $c0$, the evaluations of $f$ at coordinate functions form an $ℓ¹$-sequence
lemma dual_apply_single_mem_ℓ1 : ∀ (f : NormedSpace.Dual ℝ c0.toSubmodule), (fun i => f ⟨lp.single ⊤ i 1, single_mem_c0 i⟩)
    ∈ lp (fun _ : ℕ => ℝ) 1 := by
  intro f; simp only [Membership.mem, Set.Mem, lp, setOf, AddSubgroup.coe_set_mk,
    ClosedSubmodule.coe_toSubmodule]
  apply memℓp_gen; simp only [Real.norm_eq_abs, ENNReal.toReal_one, Real.rpow_one]
  apply summable_of_sum_range_le
  · intro; positivity
  · intro n; calc
      _ = f (∑ i ∈ range n, sign (f ⟨lp.single ⊤ i 1, single_mem_c0 i⟩) • ⟨lp.single ⊤ i 1, single_mem_c0 i⟩) := by
        rw [map_sum]; apply sum_congr rfl
        · intros; rw [map_smul]; apply aux_abs_real
      _ ≤ _ := le_abs_self _
      _ = _ := symm (Real.norm_eq_abs _)
      _ ≤ _ := f.le_opNorm _
      _ ≤ ‖f‖ := by
        nth_rw 2 [← mul_one ‖f‖]; gcongr
        simp only [SetLike.mk_smul_mk, AddSubgroupClass.coe_norm, AddSubmonoidClass.coe_finset_sum]
        simp only [lp.norm_eq_ciSup, AddSubgroup.val_finset_sum, lp.coeFn_smul, sum_apply,
          Pi.smul_apply, lp.single_apply, smul_eq_mul, norm_eq_abs]
        apply Real.iSup_le
        · intro a; by_cases h : n ≤ a
          · rw [sum_eq_zero]; simp
            intro _ h'; rw [Pi.single_eq_of_ne]; simp
            rw [mem_range] at h'; omega
          push_neg at h; rw [← mem_range] at h
          rw [sum_eq_single_of_mem _ h, Pi.single_eq_same, mul_one, sign]
          split_ifs; all_goals norm_num
          · intros; right; apply Pi.single_eq_of_ne
            omega
        simp

-- Prove $LI_ℓ1_c0dual$ is surjective by applying `dual_apply_single_mem_ℓ1`
lemma surjective_LI_ℓ1_c0dual : (⇑LI_ℓ1_c0dual).Surjective := by
  intro f; let x : lp (fun _ : ℕ => ℝ) 1 := ⟨fun i => f ⟨lp.single ⊤ i 1, single_mem_c0 i⟩, dual_apply_single_mem_ℓ1 f⟩
  use x; ext ⟨a, amem⟩; simp only [LI_ℓ1_c0dual, LinearIsometry.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, LI_ℓ1_c0dual_toFun, ContinuousLinearMap.coe_mk']
  have : T2Space c0.toSubmodule := TopologicalSpace.t2Space_of_metrizableSpace
  have := hasSum_single_c0 ⟨a, amem⟩
  simp only [SetLike.mk_smul_mk] at this
  rw [← this.tsum_eq, f.map_tsum this.summable]; apply tsum_congr
  · intro n; rw [Pi.mul_apply]; dsimp [x]
    rw [mul_comm, ← smul_eq_mul, ← f.map_smul]; rfl
