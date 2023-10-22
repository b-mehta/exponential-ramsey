/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import basic
import prereq.constructive

/-!
# Section 4
-/

lemma convex_on.mul {f g : ℝ → ℝ} {s : set ℝ} (hf : convex_on ℝ s f) (hg : convex_on ℝ s g)
  (hf' : monotone_on f s) (hg' : monotone_on g s)
  (hf'' : ∀ x ∈ s, 0 ≤ f x) (hg'' : ∀ x ∈ s, 0 ≤ g x) : convex_on ℝ s (λ x, f x * g x) :=
begin
  refine linear_order.convex_on_of_lt hf.1 _,
  intros x hx y hy hxy a b ha hb hab,
  replace hg := hg.2 hx hy ha.le hb.le hab,
  refine (mul_le_mul (hf.2 hx hy ha.le hb.le hab) hg (hg'' _ (hf.1 hx hy ha.le hb.le hab))
    (add_nonneg (smul_nonneg ha.le (hf'' _ hx)) (smul_nonneg hb.le (hf'' _ hy)))).trans _,
  have : b = 1 - a, { rwa eq_sub_iff_add_eq' },
  subst this,
  simp only [smul_eq_mul],
  suffices : 0 ≤ a * (1 - a) * (g y - g x) * (f y - f x),
  { nlinarith only [this] },
  exact mul_nonneg (mul_nonneg (by positivity) (sub_nonneg_of_le (hg' hx hy hxy.le)))
    (sub_nonneg_of_le (hf' hx hy hxy.le)),
end

lemma monotone_on.mul {s : set ℝ} {f g : ℝ → ℝ} (hf : monotone_on f s) (hg : monotone_on g s)
  (hf' : ∀ x ∈ s, 0 ≤ f x) (hg' : ∀ x ∈ s, 0 ≤ g x) :
  monotone_on (λ x, f x * g x) s :=
λ x hx y hy hxy, mul_le_mul (hf hx hy hxy) (hg hx hy hxy) (hg' _ hx) (hf' _ hy)

lemma convex_on_sub_const {s : set ℝ} {c : ℝ} (hs : convex ℝ s) : convex_on ℝ s (λ x, x - c) :=
(convex_on_id hs).sub (concave_on_const _ hs)

lemma convex.union {s t : set ℝ} (hs : convex ℝ s) (ht : convex ℝ t)
  (hst : ¬ disjoint s t) : convex ℝ (s ∪ t) :=
begin
  rw set.not_disjoint_iff at hst,
  obtain ⟨a, has, hat⟩ := hst,
  rw [convex_iff_ord_connected, set.ord_connected_iff_uIcc_subset],
  rintro x (hx | hx) y (hy | hy),
  { exact (hs.ord_connected.uIcc_subset hx hy).trans (set.subset_union_left _ _) },
  { exact set.uIcc_subset_uIcc_union_uIcc.trans (set.union_subset_union
      (hs.ord_connected.uIcc_subset hx has) (ht.ord_connected.uIcc_subset hat hy)) },
  { rw set.union_comm,
    exact set.uIcc_subset_uIcc_union_uIcc.trans (set.union_subset_union
      (ht.ord_connected.uIcc_subset hx hat) (hs.ord_connected.uIcc_subset has hy)) },
  { exact (ht.ord_connected.uIcc_subset hx hy).trans (set.subset_union_right _ _) },
end

lemma convex_on_univ_max {k : ℝ} : convex_on ℝ set.univ (max k) :=
begin
  refine linear_order.convex_on_of_lt convex_univ _,
  rintro x - y - hxy a b ha hb hab,
  simp only [smul_eq_mul],
  refine max_le _ _,
  { refine (add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hb.le)).trans_eq' _,
    rw [←add_mul, hab, one_mul] },
  { exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha.le)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hb.le) },
end

lemma convex_on.congr' {s : set ℝ} {f g : ℝ → ℝ} (hf : convex_on ℝ s f) (h : s.eq_on f g) :
  convex_on ℝ s g :=
begin
  refine ⟨hf.1, _⟩,
  intros x hx y hy a b ha hb hab,
  rw [←h (hf.1 hx hy ha hb hab), ←h hx, ←h hy],
  exact hf.2 hx hy ha hb hab,
end

/-- the descending factorial but with a more general setting -/
def desc_factorial {α : Type*} [has_one α] [has_mul α] [has_sub α] [has_nat_cast α] (x : α) : ℕ → α
| 0 := 1
| (k + 1) := (x - k) * desc_factorial k

lemma desc_factorial_nonneg {x : ℝ} : ∀ {k : ℕ}, (k : ℝ) - 1 ≤ x → 0 ≤ desc_factorial x k
| 0 h := zero_le_one
| (k + 1) h := mul_nonneg (by rwa [nat.cast_add_one, add_sub_cancel, ←sub_nonneg] at h)
  (desc_factorial_nonneg (h.trans' (by simp)))

lemma desc_factorial_nat (n : ℕ) : ∀ (k : ℕ), desc_factorial n k = n.desc_factorial k
| 0 := rfl
| (k + 1) := congr_arg _ (desc_factorial_nat k)

lemma desc_factorial_cast_nat (n : ℕ) : ∀ (k : ℕ), desc_factorial (n : ℝ) k = n.desc_factorial k
| 0 := by rw [desc_factorial, nat.desc_factorial_zero, nat.cast_one]
| (k + 1) :=
  begin
    rw [desc_factorial, nat.desc_factorial_succ, desc_factorial_cast_nat, nat.cast_mul],
    cases lt_or_le n k,
    { rw [nat.desc_factorial_of_lt h, nat.cast_zero, mul_zero, mul_zero] },
    { rw nat.cast_sub h },
  end

lemma desc_factorial_monotone_on : ∀ k, monotone_on (λ x : ℝ, desc_factorial x k) (set.Ici (k - 1))
| 0 :=
  begin
    simp only [desc_factorial],
    exact monotone_on_const,
  end
| (k + 1) :=
  begin
    rw [nat.cast_add_one, add_sub_cancel],
    refine monotone_on.mul _ ((desc_factorial_monotone_on k).mono _) _ _,
    { intros x hx y hy hxy,
      simpa using hxy },
    { rw set.Ici_subset_Ici,
      simp },
    { rintro x hx,
      exact sub_nonneg_of_le hx },
    rintro x (hx : _ ≤ _),
    refine desc_factorial_nonneg (hx.trans' _),
    simp
  end

lemma desc_factorial_convex : ∀ k : ℕ, convex_on ℝ (set.Ici ((k : ℝ) - 1)) (λ x, desc_factorial x k)
| 0 := convex_on_const 1 (convex_Ici _)
| (k + 1) :=
  begin
    rw [nat.cast_add_one, add_sub_cancel],
    change convex_on _ _ (λ x : ℝ, (x - k) * desc_factorial x k),
    refine convex_on.mul _ _ _ _ _ _,
    { exact convex_on_sub_const (convex_Ici _) },
    { refine (desc_factorial_convex k).subset _ (convex_Ici _),
      rw set.Ici_subset_Ici,
      simp },
    { intros x hx y hy hxy,
      simpa using hxy },
    { refine (desc_factorial_monotone_on _).mono _,
      rw set.Ici_subset_Ici,
      simp },
    { rintro x hx,
      exact sub_nonneg_of_le hx },
    rintro x (hx : _ ≤ _),
    refine desc_factorial_nonneg (hx.trans' _),
    simp
  end


lemma my_convex {k : ℝ} {f : ℝ → ℝ} (hf : convex_on ℝ (set.Ici k) f)
  (hf' : monotone_on f (set.Ici k)) (hk : ∀ x < k, f x = f k) : convex_on ℝ set.univ f :=
begin
  have : f = f ∘ max k,
  { ext x,
    rw function.comp_apply,
    cases lt_or_le x k,
    { rw [max_eq_left h.le, hk _ h] },
    { rw max_eq_right h } },
  rw this,
  have : set.range (max k) = set.Ici k,
  { ext x,
    rw [set.mem_range, set.mem_Ici],
    split,
    { rintro ⟨x, rfl⟩,
      exact le_max_left _ _ },
    intro h,
    refine ⟨x, _⟩,
    rw max_eq_right h },
  refine convex_on.comp _ _ _,
  { rwa [set.image_univ, this] },
  { exact convex_on_univ_max },
  rwa [set.image_univ, this],
end

-- is equal to desc_factorial for all naturals x, and for all x ≥ k - 1
/-- a variant of the descending factorial which truncates at k-1 -/
noncomputable def my_desc_factorial (x : ℝ) (k : ℕ) : ℝ :=
if x < k - 1 then 0 else desc_factorial x k

lemma my_desc_factorial_eq_on {k : ℕ} :
  (set.Ici ((k : ℝ) - 1)).eq_on (λ x, my_desc_factorial x k) (λ x, desc_factorial x k) :=
begin
  intros x hx,
  dsimp,
  rw [my_desc_factorial, if_neg],
  rwa not_lt
end

lemma my_desc_factorial_eq_nat_desc_factorial {n k : ℕ} :
  my_desc_factorial n k = n.desc_factorial k :=
begin
  rw [my_desc_factorial, desc_factorial_cast_nat, ite_eq_right_iff, eq_comm, nat.cast_eq_zero,
    nat.desc_factorial_eq_zero_iff_lt],
  intro h,
  rw ←@nat.cast_lt ℝ,
  linarith
end

lemma my_desc_factorial_convex_on_Ici (k : ℕ) :
  convex_on ℝ (set.Ici ((k : ℝ) - 1)) (λ x, my_desc_factorial x k) :=
(desc_factorial_convex _).congr' my_desc_factorial_eq_on.symm

lemma my_desc_factorial_convex {k : ℕ} (hk : k ≠ 0):
  convex_on ℝ set.univ (λ x, my_desc_factorial x k) :=
begin
  refine my_convex ((desc_factorial_convex _).congr' my_desc_factorial_eq_on.symm)
    ((desc_factorial_monotone_on _).congr my_desc_factorial_eq_on.symm) _,
  intros x hx,
  rw [my_desc_factorial, if_pos hx, my_desc_factorial, if_neg (lt_irrefl _)],
  have h : (k : ℝ) - 1 = (k - 1 : ℕ),
  { rw [nat.cast_sub, nat.cast_one],
    rwa [nat.succ_le_iff, pos_iff_ne_zero] },
  rw [h, desc_factorial_cast_nat, eq_comm, nat.cast_eq_zero, nat.desc_factorial_eq_zero_iff_lt],
  exact nat.pred_lt hk,
end

/-- a definition of the generalized binomial coefficient -/
noncomputable def my_generalized_binomial (x : ℝ) (k : ℕ) : ℝ :=
(k.factorial : ℝ)⁻¹ • my_desc_factorial x k

lemma my_generalized_binomial_nat (n k : ℕ) :
  my_generalized_binomial n k = n.choose k :=
begin
  rw [my_generalized_binomial, my_desc_factorial_eq_nat_desc_factorial, smul_eq_mul,
    nat.desc_factorial_eq_factorial_mul_choose, nat.cast_mul, inv_mul_cancel_left₀],
  positivity
end

lemma my_generalized_binomial_convex {k : ℕ} (hk : k ≠ 0) :
  convex_on ℝ set.univ (λ x, my_generalized_binomial x k) :=
(my_desc_factorial_convex hk).smul (by positivity)

open_locale big_operators exponential_ramsey

lemma my_thing {α : Type*} {s : finset α} (f : α → ℕ) (b : ℕ) (hb : b ≠ 0) :
  my_generalized_binomial ((∑ i in s, f i) / s.card) b * s.card ≤ (∑ i in s, (f i).choose b) :=
begin
  simp only [div_eq_inv_mul, finset.mul_sum],
  cases eq_or_ne s.card 0 with hs hs,
  { simp only [hs, nat.cast_zero, mul_zero, ←nat.cast_sum],
    exact nat.cast_nonneg _ },
  rw [←le_div_iff, div_eq_mul_inv, mul_comm, finset.mul_sum],
  swap, { positivity },
  simp only [←my_generalized_binomial_nat],
  have h₁ : ∑ i in s, (s.card : ℝ)⁻¹ = 1,
  { rw [finset.sum_const, nsmul_eq_mul, mul_inv_cancel],
    positivity },
  have h₂ : ∀ i ∈ s, (f i : ℝ) ∈ (set.univ : set ℝ),
  { intros i hi, simp },
  have h₃ : ∀ i ∈ s, (0 : ℝ) ≤ (s.card)⁻¹,
  { intros i hi,
    positivity },
  exact (my_generalized_binomial_convex hb).map_sum_le h₃ h₁ h₂,
end

open real

lemma b_le_sigma_mul_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 ≤ σ) :
  (b : ℝ) ≤ σ * m := hb.trans (half_le_self (by positivity))

lemma cast_b_le_cast_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2)
  (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) : (b : ℝ) ≤ m :=
(b_le_sigma_mul_m hb hσ₀).trans (mul_le_of_le_one_left (nat.cast_nonneg _) hσ₁)

lemma b_le_m {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2)
  (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) : b ≤ m :=
nat.cast_le.1 (cast_b_le_cast_m hb hσ₀ hσ₁)

lemma four_two_aux_aux {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ : 0 < σ) :
  (my_generalized_binomial (σ * m) b) * (m.choose b)⁻¹ =
    desc_factorial (σ * m) b / desc_factorial m b :=
begin
  rw [my_generalized_binomial, smul_eq_mul, nat.choose_eq_desc_factorial_div_factorial,
    nat.cast_div, inv_div, ←div_eq_inv_mul, div_mul_div_cancel, ←desc_factorial_cast_nat],
  { congr' 1,
    refine my_desc_factorial_eq_on _,
    rw set.mem_Ici,
    have : (b : ℝ) - 1 ≤ b, { linarith },
    refine this.trans (hb.trans _),
    apply half_le_self _,
    positivity },
  { positivity },
  { exact nat.factorial_dvd_desc_factorial _ _ },
  { positivity },
end

lemma four_two_aux {m b : ℕ} {σ : ℝ} :
  desc_factorial (σ * m) b / desc_factorial m b = ∏ i in finset.range b, (σ * m - i) / (m - i) :=
begin
  induction b with b ih,
  { rw [desc_factorial, desc_factorial, finset.prod_range_zero, div_one] },
  rw [desc_factorial, desc_factorial, finset.prod_range_succ, ←ih, div_mul_div_comm, mul_comm,
    mul_comm (_ - _)],
end

lemma four_two_aux' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
  ∏ i in finset.range b, (σ * m - i) / (m - i) =
    σ ^ b * ∏ i in finset.range b, (1 - ((1 - σ) * i) / (σ * (m - i))) :=
begin
  rw [finset.pow_eq_prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl _,
  intros i hi,
  rw [mul_one_sub, mul_div_assoc', mul_div_mul_left _ _ hσ₀.ne', sub_div'],
  { ring_nf },
  rw finset.mem_range at hi,
  have hb' : 0 < b := pos_of_gt hi,
  have : (i : ℝ) < b, { rwa nat.cast_lt },
  suffices : (i : ℝ) < m, { linarith only [this] },
  refine (this.trans_le hb).trans_le ((half_le_self (by positivity)).trans _),
  exact mul_le_of_le_one_left (nat.cast_nonneg _) hσ₁,
end.

lemma four_two_aux'' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
  (hi : i ∈ finset.range b) :
  (1 : ℝ) - i / (σ * m) ≤ 1 - ((1 - σ) * i) / (σ * (m - i)) :=
begin
  rw finset.mem_range at hi,
  have : (i : ℝ) < m,
  { rw nat.cast_lt,
    refine hi.trans_le (b_le_m hb hσ₀ hσ₁) },
  rw [sub_le_sub_iff_left, mul_comm σ, ←div_mul_div_comm, ←div_div, div_eq_mul_one_div (i / σ : ℝ),
    mul_comm],
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  rw [div_le_div_iff, one_mul, one_sub_mul, sub_le_sub_iff_left],
  { refine (hb.trans (half_le_self (by positivity))).trans' (le_of_lt _),
    rwa nat.cast_lt },
  { rwa sub_pos },
  exact this.trans_le' (nat.cast_nonneg _),
end

lemma exp_thing {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1 / 2) :
  real.exp (-2 * x) ≤ 1 - x :=
begin
  let a := 2 * x,
  have ha : 0 ≤ a := mul_nonneg (by norm_num1) hx₀,
  have ha' : 0 ≤ 1 - a,
  { simp only [a],
    linarith only [hx₁] },
  have := convex_on_exp.2 (set.mem_univ (-1)) (set.mem_univ 0) ha ha' (by simp),
  simp only [smul_eq_mul, mul_neg, ←neg_mul, mul_one, mul_zero, add_zero, real.exp_zero, a] at this,
  refine this.trans _,
  rw [add_comm, sub_add, sub_le_sub_iff_left, ←mul_one_sub, mul_right_comm],
  refine le_mul_of_one_le_left hx₀ _,
  rw [←div_le_iff', le_sub_comm, real.exp_neg, inv_le],
  { exact exp_one_gt_d9.le.trans' (by norm_num) },
  { exact exp_pos _ },
  { norm_num1 },
  { norm_num1 },
end

lemma four_two_aux''' {m b i : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ)
  (hi : i ∈ finset.range b) :
  real.exp ((- 2 / (σ * m)) * i) ≤ (1 : ℝ) - i / (σ * m) :=
begin
  rw [div_mul_comm, mul_comm],
  refine exp_thing (by positivity) _,
  refine div_le_of_nonneg_of_le_mul (by positivity) (by norm_num) _,
  rw [mul_comm, mul_one_div],
  refine hb.trans' _,
  rw nat.cast_le,
  rw finset.mem_range at hi,
  exact hi.le
end

lemma four_two_aux'''' {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
  real.exp ((- 2 / (σ * m)) * ∑ i in finset.range b, i) ≤
    ∏ i in finset.range b, (1 - ((1 - σ) * i) / (σ * (m - i))) :=
begin
  rw [finset.mul_sum, real.exp_sum],
  refine finset.prod_le_prod _ _,
  { intros i hi,
    positivity },
  intros i hi,
  exact (four_two_aux''' hb hσ₀ hi).trans (four_two_aux'' hb hσ₀ hσ₁ hi),
end

-- Fact 4.2
lemma four_two_left {m b : ℕ} {σ : ℝ} (hb : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) :
  σ ^ b * m.choose b * exp (- b ^ 2 / (σ * m)) ≤ my_generalized_binomial (σ * m) b :=
begin
  have : 0 < (m.choose b : ℝ),
  { rw nat.cast_pos,
    exact nat.choose_pos (b_le_m hb hσ₀.le hσ₁) },
  rw [mul_right_comm, ←le_div_iff this, div_eq_mul_inv (my_generalized_binomial _ _),
    four_two_aux_aux hb hσ₀, four_two_aux, four_two_aux' hb hσ₀ hσ₁],
  refine mul_le_mul_of_nonneg_left ((four_two_aux'''' hb hσ₀.le hσ₁).trans' _) (by positivity),
  rw [exp_le_exp, ←nat.cast_sum, finset.sum_range_id, ←nat.choose_two_right, div_mul_eq_mul_div],
  refine div_le_div_of_le (by positivity) _,
  rw [neg_mul, neg_le_neg_iff, ←le_div_iff'],
  swap, { norm_num1 },
  refine (nat.choose_le_pow 2 b).trans _,
  simp,
end

open filter finset real

namespace simple_graph
variables {V : Type*} [decidable_eq V] {χ : top_edge_labelling V (fin 2)}

lemma four_one_part_one [fintype V] (μ : ℝ) (l k : ℕ) (C : book_config χ)
  (hC : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ)
  (hR : ¬ (∃ m : finset V, χ.monochromatic_of m 0 ∧ k ≤ m.card)) :
  ∃ U : finset V, χ.monochromatic_of U 1 ∧ U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ ∧
    U ⊆ C.X ∧ ∀ x ∈ U, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card :=
begin
  let W := (C.X.filter (λ x, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card)),
  have : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ W.card := hC,
  rw [←fintype.card_coe W, ramsey_number_le_iff, is_ramsey_valid_iff_eq] at this,
  obtain ⟨U, hU⟩ := this (χ.pullback (function.embedding.subtype _)),
  rw [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons] at hU,
  replace hU := hU.resolve_left _,
  { refine ⟨U.map (function.embedding.subtype _), hU.1.map, _, _⟩,
    { rw [card_map, hU.2] },
    simp only [finset.subset_iff, finset.mem_map, mem_filter, function.embedding.coe_subtype,
      forall_exists_index, exists_prop, finset.exists_coe, subtype.coe_mk, exists_and_distrib_right,
      exists_eq_right],
    split,
    { rintro x ⟨hx₁, hx₂⟩ hx,
      exact hx₁ },
    { rintro x ⟨hx₁, hx₂⟩ hx,
      exact hx₂ } },
  rintro ⟨hU', hU''⟩,
  refine hR ⟨U.map (function.embedding.subtype _), _, _⟩,
  { exact hU'.map },
  rw [card_map, hU''],
end

lemma col_density_mul [fintype V] {k : fin 2} {A B : finset V} :
  col_density χ k A B * A.card = (∑ x in B, (col_neighbors χ k x ∩ A).card) / B.card :=
begin
  rcases A.eq_empty_or_nonempty with rfl | hA,
  { rw [col_density_empty_left],
    simp only [inter_empty, card_empty, nat.cast_zero, sum_const_zero, zero_div, mul_zero] },
  rw [col_density_comm, col_density_eq_sum, div_mul_eq_mul_div, mul_div_mul_right],
  rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
end

lemma col_density_mul_mul [fintype V] {k : fin 2} {A B : finset V} :
  col_density χ k A B * (A.card * B.card) = ∑ x in B, (col_neighbors χ k x ∩ A).card :=
begin
  rcases B.eq_empty_or_nonempty with rfl | hA,
  { rw [col_density_empty_right, sum_empty, zero_mul] },
  rw [←mul_assoc, col_density_mul, div_mul_cancel],
  rwa [nat.cast_ne_zero, ←pos_iff_ne_zero, card_pos],
end


-- (10)
lemma four_one_part_two [fintype V] (μ : ℝ) {l : ℕ} {C : book_config χ} {U : finset V}
  (hl : l ≠ 0)
  (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊)
  (hU' : U ⊆ C.X) (hU'' : ∀ x ∈ U, μ * C.X.card ≤ (blue_neighbors χ x ∩ C.X).card) :
  (μ * C.X.card - U.card) / (C.X.card - U.card) ≤ blue_density χ U (C.X \ U) :=
begin
  rw [col_density_eq_sum, card_sdiff hU', ←nat.cast_sub (card_le_of_subset hU'), ←div_div],
  refine div_le_div_of_le (nat.cast_nonneg _) _,
  rw [le_div_iff],
  have : U.card • (μ * C.X.card - U.card) ≤ ∑ x in U, (blue_neighbors χ x ∩ (C.X \ U)).card,
  { rw ←finset.sum_const,
    refine sum_le_sum _,
    intros x hx,
    rw [inter_sdiff, sub_le_iff_le_add, ←nat.cast_add],
    refine (hU'' _ hx).trans _,
    rw nat.cast_le,
    exact card_le_card_sdiff_add_card },
  refine this.trans_eq' _,
  { rw [nsmul_eq_mul, mul_comm] },
  rw hU,
  positivity
end

-- (10)
lemma four_one_part_three (μ : ℝ) {k l : ℕ} {C : book_config χ} {U : finset V}
  (hμ : 0 ≤ μ) (hk₆ : 6 ≤ k) (hl : 3 ≤ l)
  (hU : U.card = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊)
  (hX : ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.X.card) :
  μ - 2 / k ≤ (μ * C.X.card - U.card) / (C.X.card - U.card) :=
begin
  set m : ℕ := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊,
  have hm₃ : 3 ≤ m,
  { rw [nat.add_one_le_ceil_iff, nat.cast_two, div_eq_mul_inv, rpow_mul (nat.cast_nonneg _),
      ←rpow_lt_rpow_iff, ←rpow_mul, inv_mul_cancel, rpow_one],
    { norm_cast,
      rw ←nat.succ_le_iff,
      exact (pow_le_pow_of_le_left (by norm_num1) hl 2).trans_eq' (by norm_num1) },
    { norm_num1 },
    { exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
    { norm_num1 },
    { exact rpow_nonneg_of_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) _ },
    { norm_num1 } },
  have hm₂ : 2 ≤ m := hm₃.trans' (by norm_num1),
  have hk₀ : 0 < (k : ℝ),
  { rw nat.cast_pos,
    exact (hk₆.trans_lt' (by norm_num1)) },
  have hk₃ : 3 ≤ k := hk₆.trans' (by norm_num1),
  have := (right_lt_ramsey_number hk₃ hm₂).trans_le hX,
  have : (0 : ℝ) < C.X.card - U.card,
  { rwa [hU, sub_pos, nat.cast_lt] },
  rw [sub_div' _ _ _ hk₀.ne', div_le_div_iff hk₀ this, sub_mul, sub_mul, mul_sub, mul_sub, hU,
    sub_sub, mul_right_comm, sub_le_sub_iff_left],
  suffices : (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ C.X.card,
  { linarith },
  have : (m : ℝ) * (k / 2 * (1 - μ) + 1) ≤ (m : ℝ) * (k / 2 + 1),
  { refine mul_le_mul_of_nonneg_left (add_le_add_right _ _) (nat.cast_nonneg _),
    refine mul_le_of_le_one_right (half_pos hk₀).le _,
    rwa sub_le_self_iff },
  refine this.trans _,
  rw ramsey_number_pair_swap at hX,
  replace hX := (mul_sub_two_le_ramsey_number hm₃).trans hX,
  rw ←@nat.cast_le ℝ at hX,
  refine hX.trans' _,
  rw [nat.cast_mul, nat.cast_sub, nat.cast_two],
  swap,
  { exact hk₃.trans' (by norm_num1) },
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  rw [←@nat.cast_le ℝ, nat.cast_bit0, nat.cast_bit1, nat.cast_one] at hk₆,
  linarith only [hk₆],
end

variables [fintype V] {k l : ℕ} {C : book_config χ} {U : finset V} {μ₀ : ℝ}

lemma ceil_lt_two_mul {x : ℝ} (hx : 1 / 2 < x) : (⌈x⌉₊ : ℝ) < 2 * x :=
begin
  cases lt_or_le x 1,
  { have : ⌈x⌉₊ = 1,
    { rw nat.ceil_eq_iff,
      { rw [nat.sub_self, nat.cast_zero, nat.cast_one],
        split;
        linarith },
      norm_num },
    rw [this, nat.cast_one],
    linarith },
  refine (nat.ceil_lt_add_one _).trans_le _,
  { linarith },
  { linarith },
end

lemma ceil_le_two_mul {x : ℝ} (hx : 1 / 2 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x :=
begin
  rcases eq_or_lt_of_le hx with rfl | hx',
  { norm_num },
  exact (ceil_lt_two_mul hx').le
end

-- l ≥ 4 / μ₀
lemma mu_div_two_le_sigma (hμ₀ : 0 < μ₀) : ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ (μ : ℝ), μ₀ ≤ μ → ∀ (σ : ℝ), μ - 2 / k ≤ σ → μ / 2 ≤ σ :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [t.eventually_ge_at_top (4 / μ₀)] with l hl k hlk μ hμ σ hσ,
  have hk : 4 / μ ≤ k,
  { refine (div_le_div_of_le_left (by norm_num1) hμ₀ hμ).trans (hl.trans _),
    rwa nat.cast_le },
  refine hσ.trans' _,
  rw [le_sub_comm, sub_half],
  refine (div_le_div_of_le_left (by norm_num1) _ hk).trans _,
  { exact div_pos (by norm_num1) (hμ₀.trans_le hμ) },
  rw [div_div_eq_mul_div, bit0_eq_two_mul (2 : ℝ), mul_div_mul_left],
  norm_num1,
end

-- l ≥ 4 / μ₀
-- l ≥ 1 / 16
-- l ≥ (8 / μ₀) ^ 2.4
lemma four_one_part_four (hμ₀ : 0 < μ₀) :
  ∀ᶠ (l : ℕ) in at_top, ∀ (k : ℕ), l ≤ k →
    ∀ (μ : ℝ), μ₀ ≤ μ →
    ∀ (σ : ℝ), μ - 2 / k ≤ σ →
    (⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊ : ℝ) ≤ σ * ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h3 : (0 : ℝ) < 2 / 3 - 1 / 4, { norm_num1 },
  have h4 : (0 : ℝ) < 1 / 4, { norm_num1 },
  filter_upwards
    [((tendsto_rpow_at_top h4).comp t).eventually_ge_at_top (1 / 2),
    ((tendsto_rpow_at_top h3).comp t).eventually_ge_at_top (4 * 2 / μ₀),
    mu_div_two_le_sigma hμ₀,
    eventually_gt_at_top 0]
    with l hl hl'' hl' hl₀ k hlk μ hμ σ hσ,
  specialize hl' k hlk μ hμ σ hσ,
  dsimp at hl hl'',
  rw [mul_div_assoc],
  refine (mul_le_mul_of_nonneg_right hl' (by positivity)).trans' _,
  rw [div_mul_div_comm, ←bit0_eq_two_mul],
  refine (ceil_le_two_mul hl).trans _,
  rw [le_div_iff', ←mul_assoc, ←div_le_iff'],
  rotate,
  { exact hμ₀.trans_le hμ },
  { norm_num1 },
  refine (nat.le_ceil _).trans' _,
  rw [mul_div_assoc, mul_div_left_comm, ←le_div_iff', ←rpow_sub],
  { exact hl''.trans' (div_le_div_of_le_left (by norm_num1) hμ₀ hμ), },
  { rwa nat.cast_pos },
  refine rpow_pos_of_pos _ _,
  rwa nat.cast_pos,
end

/-- the set of vertices which are connected to S by only blue edges -/
def common_blues (χ : top_edge_labelling V (fin 2)) (S : finset V) :
  finset V := univ.filter (λ i, ∀ j ∈ S, i ∈ blue_neighbors χ j)

lemma monochromatic_between_common_blues {S : finset V} :
  χ.monochromatic_between S (common_blues χ S) 1 :=
begin
  intros x hx y hy h,
  simp only [common_blues, mem_filter, mem_univ, true_and, exists_prop] at hy,
  have := hy x hx,
  rw [mem_col_neighbors] at this,
  obtain ⟨h, z⟩ := this,
  exact z
end

lemma four_one_part_five (χ : top_edge_labelling V (fin 2)) {b : ℕ} {X U : finset V} :
  ∑ S in powerset_len b U, ((common_blues χ S ∩ (X \ U)).card : ℝ) =
    ∑ v in X \ U, (blue_neighbors χ v ∩ U).card.choose b :=
begin
  have : ∀ S, ((common_blues χ S ∩ (X \ U)).card : ℝ) =
    ∑ v in X \ U, if v ∈ common_blues χ S then 1 else 0,
  { intro S,
    rw [sum_boole, filter_mem_eq_inter, inter_comm] },
  simp_rw this,
  rw sum_comm,
  refine sum_congr rfl _,
  intros v hv,
  rw [sum_boole, ←card_powerset_len],
  congr' 2,
  ext S,
  simp only [mem_powerset_len, mem_filter, common_blues, mem_univ, true_and, subset_inter_iff,
    and_assoc],
  rw ←and_rotate,
  refine and_congr_left' _,
  rw subset_iff,
  refine ball_congr _,
  intros x hx,
  rw [mem_col_neighbors_comm],
end

lemma four_one_part_six (χ : top_edge_labelling V (fin 2)) {m b : ℕ} {X U : finset V} (σ : ℝ)
  (hU : U.card = m) (hb : b ≠ 0) (hσ' : σ = blue_density χ U (X \ U)):
  my_generalized_binomial (σ * ↑m) b * ((X \ U).card) ≤
    ∑ v in X \ U, (blue_neighbors χ v ∩ U).card.choose b :=
begin
  refine (my_thing _ _ hb).trans' _,
  rw [←col_density_mul, ←hσ', hU],
end

lemma four_one_part_seven {V : Type*} [decidable_eq V] {m b : ℕ} {X U : finset V} {μ σ : ℝ}
  (hσ : (b : ℝ) ≤ σ * m / 2) (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 1) (hμ₀ : 0 < μ)
  (hσ' : μ - 2 / k ≤ σ) (hk : 6 ≤ k) (hm : 3 ≤ m) (hkμ : 4 / μ ≤ k) (hUX : U ⊆ X)
  (hU : U.card = m) (hX : ramsey_number ![k, m] ≤ X.card) :
  (μ ^ b * X.card * (m.choose b)) * (3 / 4) * exp (- 4 * b / (μ * k) - b ^ 2 / (σ * m)) ≤
    my_generalized_binomial (σ * ↑m) b * ((X \ U).card) :=
begin
  refine (mul_le_mul_of_nonneg_right (four_two_left hσ hσ₀ hσ₁) (nat.cast_nonneg _)).trans' _,
  have : 4 * m ≤ X.card,
  { refine hX.trans' _,
    refine (ramsey_number.mono_two hk le_rfl).trans' _,
    rw ramsey_number_pair_swap,
    refine (mul_sub_two_le_ramsey_number hm).trans_eq' _,
    rw mul_comm,
    norm_num1 },
  have h₁ : 3 / 4 * (X.card : ℝ) ≤ (X \ U).card,
  { rw [←@nat.cast_le ℝ, nat.cast_mul, nat.cast_bit0, nat.cast_two] at this,
    rw [cast_card_sdiff hUX, hU],
    linarith only [this] },
  have : μ * (1 - 2 / (μ * k)) ≤ σ,
  { rwa [mul_one_sub, mul_div_assoc', mul_div_mul_left _ _ hμ₀.ne'] },
  have h₂ : μ * exp (- 4 / (μ * k)) ≤ σ,
  { refine this.trans' (mul_le_mul_of_nonneg_left _ hμ₀.le),
    refine (exp_thing (by positivity) _).trans_eq' _,
    { rwa [←div_div, div_le_div_iff, one_mul, div_mul_eq_mul_div, ←bit0_eq_two_mul],
      { rw nat.cast_pos,
        exact hk.trans_lt' (by norm_num1), },
      norm_num1 },
    rw [mul_div_assoc', neg_mul, ←bit0_eq_two_mul] },
  rw [sub_eq_add_neg, neg_div, real.exp_add, mul_right_comm _ (real.exp _), ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (exp_pos _).le,
  rw [mul_right_comm _ (m.choose b : ℝ), mul_right_comm, mul_right_comm _ (m.choose b : ℝ)],
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  rw [mul_comm (μ ^ b), mul_right_comm _ (μ ^ b), mul_assoc, mul_comm (σ ^ b),
    mul_comm (X.card : ℝ)],
  refine mul_le_mul h₁ _ (by positivity) (nat.cast_nonneg _),
  refine (pow_le_pow_of_le_left (by positivity) h₂ _).trans' _,
  rw [mul_pow, ←rpow_nat_cast (exp _), ←exp_mul, div_mul_eq_mul_div],
end

lemma four_one_part_eight {μ : ℝ} {m b : ℕ} {U X : finset V} (hU : U.card = m) (hbm : b ≤ m)
  (h : μ ^ b * X.card / 2 * m.choose b ≤
    ∑ S in powerset_len b U, ((common_blues χ S ∩ (X \ U)).card : ℝ)) :
  ∃ S ⊆ U, S.card = b ∧ μ ^ b * X.card / 2 ≤ (common_blues χ S ∩ (X \ U)).card :=
begin
  have : (powerset_len b U).nonempty,
  { apply powerset_len_nonempty,
    rwa hU },
  have h' : ∑ (i : finset V) in powerset_len b U, μ ^ b * X.card / 2 ≤
    μ ^ b * X.card / 2 * m.choose b,
  { rw [sum_const, card_powerset_len, hU, nsmul_eq_mul, mul_comm] },
  obtain ⟨S, hS, hS'⟩ := exists_le_of_sum_le this (h.trans' h'),
  rw mem_powerset_len at hS,
  exact ⟨S, hS.1, hS.2, hS'⟩,
end

lemma four_one_part_nine_aux :
  tendsto
    (λ l : ℝ, l ^ -(2 / 3 - 1 / 4 * 2 : ℝ) + l ^ -(1 - 1 / 4 : ℝ))
    at_top (nhds (0 + 0)) :=
begin
  refine tendsto.add _ _,
  { refine tendsto_rpow_neg_at_top _,
    norm_num },
  { refine tendsto_rpow_neg_at_top _,
    norm_num }
end

-- l ≥ 4 / μ₀
-- l > 0
-- l ^ (- 1 / 6) + l ^ (- 3 / 4) ≤ μ₀ * log (3 / 2) / 8
lemma four_one_part_nine (hμ₀ : 0 < μ₀) :
  ∀ᶠ (l : ℕ) in at_top,
  ∀ k, l ≤ k →
    ∀ (μ σ : ℝ) (b m : ℕ),
      μ₀ ≤ μ →
      μ - 2 / k ≤ σ →
      (b : ℝ) ≤ σ * m / 2 →
      b = ⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊ →
      m = ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊ →
    (1 / 2 : ℝ) ≤ 3 / 4 * exp (- 4 * b / (μ * k) - b ^ 2 / (σ * m)) :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have ineq : 0 + 0 < log (3 / 2) * μ₀ / (4 * 2),
  { rw [add_zero],
    refine div_pos (mul_pos _ hμ₀) (by norm_num1),
    refine log_pos _,
    norm_num },
  have := eventually_le_of_tendsto_lt ineq four_one_part_nine_aux,
  have h4 : (0 : ℝ) < 1 / 4, { norm_num1 },
  filter_upwards
    [((tendsto_rpow_at_top h4).comp t).eventually_ge_at_top (1 / 2),
      mu_div_two_le_sigma hμ₀,
      t.eventually_gt_at_top 0,
      eventually_gt_at_top 0,
      t.eventually this
    ] with l hl hl' hl'' hl''' hl'''' --
    k hlk μ σ b m hμ hσ hσ' hb hm,
  suffices : (2 / 3 : ℝ) ≤ exp (- 4 * b / (μ * k) - b ^ 2 / (σ * m)),
  { linarith only [this] },
  have : μ / 2 ≤ σ := hl' k hlk μ hμ σ hσ,
  rw ←log_le_iff_le_exp,
  swap,
  { norm_num1 },
  have : 0 < m,
  { rw [hm, nat.ceil_pos],
    positivity },
  rw [neg_mul, neg_div, neg_sub_left, le_neg, ←log_inv, inv_div],
  have hμ' : 0 < μ := hμ₀.trans_le hμ,
  have : (b : ℝ) ^ 2 / (σ * m) ≤ (b ^ 2) / m * (2 / μ),
  { rw [mul_comm, ←div_div, div_eq_mul_inv _ σ],
    refine mul_le_mul_of_nonneg_left _ (by positivity),
    refine inv_le_of_inv_le (by positivity) _,
    rwa inv_div },
  refine (add_le_add_right this _).trans _,
  have h' := ceil_le_two_mul hl,
  dsimp at h',
  have : (b ^ 2 : ℝ) / m ≤ 4 * l ^ (- ((2 / 3) - (1 / 4 : ℝ) * 2)),
  { rw [neg_sub, rpow_sub hl'', rpow_mul (nat.cast_nonneg _), rpow_two, mul_div_assoc'],
    refine div_le_div (by positivity) _ (rpow_pos_of_pos hl'' _) _,
    { rw hb,
      refine (pow_le_pow_of_le_left (by positivity) h' 2).trans_eq _,
      rw [mul_pow],
      congr' 1,
      norm_num1 },
      rw hm,
      exact nat.le_ceil _ },
  refine (add_le_add_right (mul_le_mul_of_nonneg_right this (by positivity)) _).trans _,
  have : (4 : ℝ) * b / (μ * k) ≤ l ^ (-(1 - (1 / 4 : ℝ))) * ((4 * 2) / μ),
  { rw [neg_sub, rpow_sub hl'', rpow_one, div_mul_div_comm, mul_comm _ (_ * _ : ℝ), mul_assoc,
      mul_comm μ, hb],
    refine div_le_div (by positivity) (mul_le_mul_of_nonneg_left h' (by positivity))
      (by positivity) (mul_le_mul_of_nonneg_right _ hμ'.le),
    rwa nat.cast_le },
  refine (add_le_add_left this _).trans _,
  rw [mul_comm (4 : ℝ), mul_assoc, mul_div_assoc', ←add_mul, ←le_div_iff, div_div_eq_mul_div],
  swap,
  { exact div_pos (by norm_num1) hμ' },
  exact hl''''.trans (div_le_div_of_le (by norm_num1) (mul_le_mul_of_nonneg_left hμ
    (log_pos (by norm_num1)).le)),
end

-- lemma 4.1
-- (9)
lemma four_one (hμ₀ : 0 < μ₀) :
  ∀ᶠ (l : ℕ) in at_top, ∀ k, l ≤ k → ∀ (μ : ℝ), μ₀ ≤ μ →
    ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2), ∀ C : book_config χ,
  ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ →
  ¬ (∃ m : finset (fin n), χ.monochromatic_of m 0 ∧ k ≤ m.card) →
  ∃ s t : finset (fin n),
    s ⊆ C.X ∧
    t ⊆ C.X ∧
    disjoint s t ∧
    χ.monochromatic_of s 1 ∧
    χ.monochromatic_between s t 1 ∧
    (l : ℝ) ^ (1 / 4 : ℝ) ≤ s.card ∧
    μ ^ s.card * C.X.card / 2 ≤ t.card :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h23 : (0 : ℝ) < 2 / 3 := by norm_num,
  filter_upwards [eventually_ge_at_top 6,
    four_one_part_four hμ₀,
    four_one_part_nine hμ₀,
    mu_div_two_le_sigma hμ₀,
    t.eventually_ge_at_top (4 / μ₀),
    ((tendsto_rpow_at_top h23).comp t).eventually_gt_at_top 2]
      with l hl hl' hl₃ hl₄ hl₅ hl₆ --
    k hlk μ hμ n χ C hC hR,
  obtain ⟨U, Ublue, Usize, UX, Uneigh⟩ := four_one_part_one μ l k C hC hR,
  set m := ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊,
  have hm : 3 ≤ m,
  { rw [nat.add_one_le_ceil_iff, nat.cast_two],
    exact hl₆ },
  have hC' : ramsey_number ![k, m] ≤ C.X.card := hC.trans (card_le_of_subset (filter_subset _ _)),
  let σ := blue_density χ U (C.X \ U),
  have hμ' : 0 < μ := hμ₀.trans_le hμ,
  have h11 : μ - 2 / k ≤ σ,
  { exact (four_one_part_three μ hμ'.le (hl.trans hlk) (hl.trans' (by norm_num1)) Usize hC').trans
      (four_one_part_two μ (hl.trans_lt' (by norm_num1)).ne' Usize UX Uneigh) },
  -- simp only [←nat.ceil_le],
  specialize hl' k hlk μ hμ σ h11,
  set b := ⌈(l : ℝ) ^ (1 / 4 : ℝ)⌉₊,
  have hb : b ≠ 0,
  { rw [ne.def, nat.ceil_eq_zero, not_le],
    refine rpow_pos_of_pos _ _,
    rw nat.cast_pos,
    linarith only [hl] },
  specialize hl₃ k hlk μ σ b m hμ h11 hl' rfl rfl,
  have : μ / 2 ≤ σ := hl₄ k hlk μ hμ σ h11,
  have hk : 4 / μ ≤ k,
  { refine ((div_le_div_of_le_left (by norm_num1) hμ₀ hμ).trans hl₅).trans _,
    rwa nat.cast_le },
  have hσ₀ : 0 < σ := this.trans_lt' (by positivity),
  have hσ₁ : σ ≤ 1,
  { change (simple_graph.edge_density _ _ _ : ℝ) ≤ 1,
    rw [←rat.cast_one, rat.cast_le],
    exact edge_density_le_one _ _ _ },
  have h₁ : μ ^ b * C.X.card / 2 * m.choose b ≤
    ∑ S in powerset_len b U, ((common_blues χ S ∩ (C.X \ U)).card : ℝ),
  { rw four_one_part_five χ,
    refine (four_one_part_six χ σ Usize hb rfl).trans' _,
    refine (four_one_part_seven hl' hσ₀ hσ₁ hμ' h11 (hl.trans hlk) hm hk UX Usize hC').trans' _,
    rw [div_mul_eq_mul_div, div_eq_mul_one_div],
    refine (mul_le_mul_of_nonneg_left hl₃ (by positivity)).trans_eq _,
    simp only [mul_assoc] },
  have hbm : b ≤ m := b_le_m hl' hσ₀.le hσ₁,
  obtain ⟨S, hSU, hScard, hT⟩ := four_one_part_eight Usize hbm h₁,
  refine ⟨S, common_blues χ S ∩ (C.X \ U), _, _, _, _, _, _, _⟩,
  { exact hSU.trans UX },
  { exact (inter_subset_right _ _).trans (sdiff_subset _ _) },
  { refine disjoint.inf_right' _ _,
    refine disjoint.mono_left hSU _,
    exact disjoint_sdiff },
  { refine Ublue.subset _,
    exact hSU },
  { refine monochromatic_between_common_blues.subset_right _,
    exact inter_subset_left _ _ },
  { rw [hScard],
    exact nat.le_ceil _ },
  rwa hScard
end

lemma four_one' (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ, μ₀ ≤ μ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ C : book_config χ,
    ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ →
    ¬ (∃ m : finset (fin n), χ.monochromatic_of m 0 ∧ k ≤ m.card) →
  ∃ s t : finset (fin n),
    (l : ℝ) ^ (1 / 4 : ℝ) ≤ s.card ∧
    (s, t) ∈ book_config.useful_blue_books χ μ C.X :=
begin
  filter_upwards [four_one hμ₀] with l hl k hlk μ hμ n χ C h₁ h₂,
  obtain ⟨s, t, hs, ht, hst, hs', hst', hscard, htcard⟩ := hl k hlk μ hμ n χ C h₁ h₂,
  refine ⟨s, t, hscard, _⟩,
  rw book_config.mem_useful_blue_books',
  exact ⟨hs, ht, hst, hs', hst', htcard⟩,
end

lemma four_three_aux (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ, μ₀ ≤ μ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ m : finset (fin n), χ.monochromatic_of m 0 ∧ k ≤ m.card) →
  ∀ C : book_config χ,
    ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤ C.num_big_blues μ →
    (l : ℝ) ^ (1 / 4 : ℝ) ≤ (book_config.get_book χ μ C.X).1.card :=
begin
  filter_upwards [four_one' hμ₀] with l hl k hlk μ hμ n χ hχ C hC,
  obtain ⟨s, t, hs, hst⟩ := hl k hlk μ hμ n χ C hC hχ,
  refine hs.trans _,
  rw nat.cast_le,
  exact book_config.get_book_max s t hst,
end

lemma four_three_aux' (hμ₀ : 0 < μ₀) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ, μ₀ ≤ μ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ m : finset (fin n), χ.monochromatic_of m 0 ∧ k ≤ m.card) →
  ∀ init : book_config χ,
  ∀ i : ℕ,
    i ≤ final_step μ k l init →
    (l : ℝ) ^ (1 / 4 : ℝ) * (big_blue_steps μ k l init ∩ range i).card ≤
      (algorithm μ k l init i).B.card :=
begin
  filter_upwards [eventually_gt_at_top 0, four_three_aux hμ₀] with
    l hl₀ hl k hlk μ hμ n χ hχ init i hi,
  induction i with i ih,
  { rw [range_zero, inter_empty, card_empty, nat.cast_zero, mul_zero],
    exact nat.cast_nonneg _ },
  rw [range_succ],
  rw nat.succ_le_iff at hi,
  specialize ih hi.le,
  by_cases i ∈ big_blue_steps μ k l init,
  swap,
  { rw inter_insert_of_not_mem h,
    refine ih.trans _,
    rw nat.cast_le,
    exact (card_le_of_subset (B_subset hi)) },
  rw [inter_insert_of_mem h, card_insert_of_not_mem],
  swap,
  { simp },
  rw [big_blue_applied h, book_config.big_blue_step_B,
    nat.cast_add_one, mul_add_one, card_disjoint_union, nat.cast_add],
  { refine add_le_add ih _,
    rw [big_blue_steps, mem_filter] at h,
    exact hl k hlk μ hμ n χ hχ _ h.2.2 },
  refine disjoint.mono_right book_config.get_book_fst_subset _,
  exact (algorithm μ k l init i).hXB.symm,
end

lemma four_three (hμ₀ : 0 < μ₀)  :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ, μ₀ ≤ μ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
    ¬ (∃ (m : finset (fin n)) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card) →
  ∀ init : book_config χ,
    ((big_blue_steps μ k l init).card : ℝ) ≤ (l : ℝ) ^ (3 / 4 : ℝ) :=
begin
  filter_upwards [four_three_aux' hμ₀, eventually_gt_at_top 0] with l hl hl₀ k hlk μ hμ n χ hχ init,
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    exists_or_distrib, not_or_distrib] at hχ,
  obtain ⟨hχr, hχb⟩ := hχ,
  specialize hl k hlk μ hμ n χ hχr init (final_step μ k l init) le_rfl,
  have : big_blue_steps μ k l init ∩ range (final_step μ k l init) = big_blue_steps μ k l init,
  { rw [inter_eq_left_iff_subset, big_blue_steps],
    exact filter_subset _ _ },
  rw this at hl,
  push_neg at hχb,
  by_contra',
  refine ((mul_le_mul_of_nonneg_left this.le (by positivity)).trans hl).not_lt _,
  rw [←rpow_add, div_add_div_same, add_comm, bit1, add_assoc, ←bit0, ←bit0, div_self, rpow_one,
    nat.cast_lt],
  { exact hχb (end_state μ k l init).B (end_state μ k l init).blue_B },
  { norm_num1 },
  rwa nat.cast_pos
end

lemma four_four_red_aux {μ : ℝ} {k l : ℕ}
  (ini : book_config χ) (i : ℕ) (hi : i ≤ final_step μ k l ini) :
  (red_steps μ k l ini ∩ range i).card ≤ (algorithm μ k l ini i).A.card :=
begin
  induction i with i ih,
  { rw [range_zero, inter_empty, card_empty],
    simp },
  rw [range_succ],
  rw nat.succ_le_iff at hi,
  specialize ih hi.le,
  by_cases i ∈ red_steps μ k l ini,
  swap,
  { rw [inter_insert_of_not_mem h],
    refine ih.trans _,
    exact card_le_of_subset (A_subset hi) },
  rw [inter_insert_of_mem h, card_insert_of_not_mem],
  swap,
  { simp },
  rwa [red_applied h, book_config.red_step_basic_A, card_insert_of_not_mem, add_le_add_iff_right],
  refine finset.disjoint_left.1 (algorithm μ k l ini i).hXA _,
  exact book_config.get_central_vertex_mem_X _ _ _,
end

lemma four_four_blue_density_aux {μ : ℝ} {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0)
  (ini : book_config χ) (i : ℕ) (hi : i ≤ final_step μ k l ini) :
  ((big_blue_steps μ k l ini ∪ density_steps μ k l ini) ∩ range i).card ≤
    (algorithm μ k l ini i).B.card :=
begin
  induction i with i ih,
  { rw [range_zero, inter_empty, card_empty],
    simp },
  rw [range_succ],
  rw nat.succ_le_iff at hi,
  specialize ih hi.le,
  by_cases i ∈ big_blue_steps μ k l ini ∪ density_steps μ k l ini,
  swap,
  { rw [inter_insert_of_not_mem h],
    exact ih.trans (card_le_of_subset (B_subset hi)) },
  rw [inter_insert_of_mem h, card_insert_of_not_mem],
  swap,
  { simp },
  refine (add_le_add_right ih 1).trans _,
  rw mem_union at h,
  cases h,
  { rw [big_blue_applied h, book_config.big_blue_step_B, card_disjoint_union, add_le_add_iff_left],
    swap,
    { refine disjoint.mono_right book_config.get_book_fst_subset _,
      exact (algorithm μ k l ini i).hXB.symm },
    rw [big_blue_steps, mem_filter] at h,
    exact book_config.one_le_card_get_book_fst (book_config.get_book_condition hk hl h.2.2) },
  rw [density_applied h, book_config.density_boost_step_basic_B, card_insert_of_not_mem],
  refine finset.disjoint_left.1 (algorithm μ k l ini i).hXB _,
  exact book_config.get_central_vertex_mem_X _ _ _,
end

lemma t_le_A_card (μ : ℝ) (k l : ℕ) (ini : book_config χ) :
  (red_steps μ k l ini).card ≤ (end_state μ k l ini).A.card :=
begin
  have hl := four_four_red_aux ini (final_step μ k l ini) le_rfl,
  have : red_steps μ k l ini ∩ range (final_step μ k l ini) = red_steps μ k l ini,
  { rw [inter_eq_left_iff_subset],
    exact red_steps_subset_red_or_density_steps.trans (filter_subset _ _) },
  rwa [this] at hl,
end

-- observation 4.4
lemma four_four_red (μ : ℝ) {k l : ℕ}
  (h : ¬ (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card))
  (ini : book_config χ) :
  (red_steps μ k l ini).card ≤ k :=
begin
  have hl := t_le_A_card μ k l ini,
  simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    exists_or_distrib, not_or_distrib, not_exists, not_and, not_le] at h,
  exact hl.trans (h.1 _ (end_state μ k l ini).red_A).le,
end

-- observation 4.4
lemma four_four_blue_density (μ : ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0)
  (h : ¬ (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card))
  (ini : book_config χ) :
  (big_blue_steps μ k l ini).card + (density_steps μ k l ini).card ≤ l :=
begin
  have hl := four_four_blue_density_aux hk hl ini (final_step μ k l ini) le_rfl,
  have : (big_blue_steps μ k l ini ∪ density_steps μ k l ini) ∩ range (final_step μ k l ini) =
    big_blue_steps μ k l ini ∪ density_steps μ k l ini,
  { rw [inter_eq_left_iff_subset, union_subset_iff],
    exact ⟨filter_subset _ _,
      density_steps_subset_red_or_density_steps.trans (filter_subset _ _)⟩ },
  rw [←card_disjoint_union, ←this],
  { simp only [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
      exists_or_distrib, not_or_distrib, not_exists, not_and, not_le] at h,
    exact hl.trans (h.2 _ (end_state μ k l ini).blue_B).le },
  refine big_blue_steps_disjoint_red_or_density_steps.mono_right _,
  exact density_steps_subset_red_or_density_steps
end

-- observation 4.4
lemma four_four_degree (μ : ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0)
  (h : ¬ (∃ (m : finset V) (c : fin 2), χ.monochromatic_of m c ∧ ![k, l] c ≤ m.card))
  (ini : book_config χ) :
  (degree_steps μ k l ini).card ≤ k + l + 1 :=
begin
  refine (num_degree_steps_le_add).trans _,
  rw [add_le_add_iff_right, add_assoc],
  exact add_le_add (four_four_red μ h _) (four_four_blue_density μ hk hl h _),
end

end simple_graph
