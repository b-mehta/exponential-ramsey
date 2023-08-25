import algebra.order.chebyshev

import prereq.graph_probability
import section4

open real

lemma mul_log_two_le_log_one_add {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε ≤ 1) : ε * log 2 ≤ log (1 + ε) :=
begin
  rw le_log_iff_exp_le,
  swap,
  { linarith },
  have : 0 ≤ 1 - ε, { rwa sub_nonneg },
  have := convex_on_exp.2 (set.mem_univ 0) (set.mem_univ (log 2)) this hε (by simp),
  simp only [smul_eq_mul, mul_zero, zero_add, real.exp_zero, mul_one, exp_log two_pos] at this,
  refine this.trans_eq _,
  ring_nf
end

namespace simple_graph

open_locale exponential_ramsey

open filter finset nat

lemma top_adjuster {α : Type*} [semilattice_sup α] [nonempty α] {p : α → Prop}
  (h : ∀ᶠ k : α in at_top, p k) :
  ∀ᶠ l : α in at_top, ∀ k : α, l ≤ k → p k :=
begin
  rw eventually_at_top at h ⊢,
  obtain ⟨n, hn⟩ := h,
  refine ⟨n, _⟩,
  rintro i (hi : n ≤ i) j hj,
  exact hn j (hi.trans hj),
end

lemma eventually_le_floor (c : ℝ) (hc : c < 1) :
  ∀ᶠ k : ℝ in at_top, c * k ≤ ⌊k⌋₊ :=
begin
  cases le_or_lt c 0,
  { filter_upwards [eventually_ge_at_top (0 : ℝ)] with x hx,
    exact (nat.cast_nonneg _).trans' (mul_nonpos_of_nonpos_of_nonneg h hx) },
  filter_upwards [eventually_ge_at_top (1 - c)⁻¹] with x hx,
  refine (nat.sub_one_lt_floor x).le.trans' _,
  rwa [le_sub_comm, ←one_sub_mul, ←div_le_iff', one_div],
  rwa sub_pos,
end

lemma ceil_eventually_le (c : ℝ) (hc : 1 < c) :
  ∀ᶠ k : ℝ in at_top, (⌈k⌉₊ : ℝ) ≤ c * k :=
begin
  filter_upwards [(tendsto_id.const_mul_at_top (sub_pos_of_lt hc)).eventually_ge_at_top 1,
    eventually_ge_at_top (0 : ℝ)] with x hx hx',
  refine (nat.ceil_lt_add_one hx').le.trans _,
  rwa [id.def, sub_one_mul, le_sub_iff_add_le'] at hx,
end

lemma is_o_rpow_rpow {r s : ℝ} (hrs : r < s) :
  (λ (x : ℝ), x ^ r) =o[at_top] (λ x, x ^ s) :=
begin
  rw asymptotics.is_o_iff,
  intros ε hε,
  have : 0 < s - r := sub_pos_of_lt hrs,
  filter_upwards [eventually_gt_at_top (0 : ℝ),
    (tendsto_rpow_at_top this).eventually_ge_at_top (1 / ε)] with x hx hx',
  rwa [norm_rpow_of_nonneg hx.le, norm_rpow_of_nonneg hx.le, norm_of_nonneg hx.le, ←div_le_iff' hε,
    div_eq_mul_one_div, ←le_div_iff' (rpow_pos_of_pos hx _), ←rpow_sub hx],
end

lemma is_o_id_rpow {s : ℝ} (hrs : 1 < s) : (λ x : ℝ, x) =o[at_top] (λ x, x ^ s) :=
by simpa only [rpow_one] using is_o_rpow_rpow hrs

lemma is_o_one_rpow {s : ℝ} (hrs : 0 < s) : (λ (x : ℝ), (1 : ℝ)) =o[at_top] (λ x, x ^ s) :=
by simpa only [rpow_zero] using is_o_rpow_rpow hrs

lemma one_lt_q_function_aux : ∀ᶠ k : ℕ in at_top,
  0.8 * (2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k) ≤ ⌊2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k⌋₊ :=
begin
  have : tendsto (λ x : ℝ, 2 * x ^ (1 / 4 : ℝ) * log x) at_top at_top,
  { refine tendsto.at_top_mul_at_top _ tendsto_log_at_top,
    exact (tendsto_rpow_at_top (by norm_num)).const_mul_at_top two_pos },
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have := (this.comp t).eventually (eventually_le_floor 0.8 (by norm_num)),
  filter_upwards [this] with k hk,
  rw [neg_div, rpow_neg (nat.cast_nonneg _), div_inv_eq_mul],
  exact hk,
end

lemma ε_lt_one : ∀ᶠ k : ℕ in at_top, (k : ℝ) ^ (-1 / 4 : ℝ) < 1 :=
begin
  filter_upwards [eventually_gt_at_top 1] with k hk,
  refine rpow_lt_one_of_one_lt_of_neg (nat.one_lt_cast.2 hk) (by norm_num),
end

lemma root_ε_lt_one : ∀ᶠ k : ℕ in at_top, (k : ℝ) ^ (-1 / 8 : ℝ) < 1 :=
begin
  filter_upwards [eventually_gt_at_top 1] with k hk,
  refine rpow_lt_one_of_one_lt_of_neg (nat.one_lt_cast.2 hk) (by norm_num),
end

lemma one_lt_q_function : ∀ᶠ k : ℕ in at_top,
  ∀ p₀ : ℝ, 0 ≤ p₀ →
  1 ≤ q_function k p₀ ⌊2 / ((k : ℝ) ^ (-1 / 4 : ℝ)) * log k⌋₊ :=
begin
  have hc : 1 < log 2 * (4 / 5 * 2),
  { rw [←div_lt_iff],
    { exact log_two_gt_d9.trans_le' (by norm_num) },
    norm_num },
  have := ((is_o_id_rpow hc).add (is_o_one_rpow (zero_lt_one.trans hc))).def zero_lt_one,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [eventually_ge_at_top 1, one_lt_q_function_aux, t.eventually_ge_at_top 1,
    t.eventually this,
    ε_lt_one]
    with k hk hk' hk₁ hk₂ hε' --
    p₀ hp₀,
  have hk₀' : (0 : ℝ) < k := nat.cast_pos.2 hk,
  rw q_function,
  set ε : ℝ := (k : ℝ) ^ (-1 / 4 : ℝ),
  have hε : 0 < ε := rpow_pos_of_pos hk₀' _,
  have hε₁ : ε ≤ 1 := hε'.le,
  refine le_add_of_nonneg_of_le hp₀ _,
  rw [one_le_div hk₀', le_sub_iff_add_le, ←rpow_nat_cast],
  refine (rpow_le_rpow_of_exponent_le _ hk').trans' _,
  { rw [le_add_iff_nonneg_right],
    exact hε.le },
  rw [rpow_def_of_pos, ←mul_assoc, ←mul_assoc, mul_comm, ←rpow_def_of_pos hk₀'],
  swap,
  { positivity },
  have : log 2 * (4 / 5 * 2) ≤ log (1 + ε) * (4 / 5) * (2 / ε),
  { rw [mul_div_assoc' _ _ ε, le_div_iff' hε, ←mul_assoc, mul_assoc (log _)],
    refine mul_le_mul_of_nonneg_right (mul_log_two_le_log_one_add hε.le hε₁) _,
    norm_num1 },
  refine (rpow_le_rpow_of_exponent_le hk₁ this).trans' _,
  rwa [norm_of_nonneg, one_mul, norm_of_nonneg] at hk₂,
  { exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _ },
  positivity
end

lemma height_upper_bound : ∀ᶠ k : ℕ in at_top,
  ∀ p₀ : ℝ, 0 ≤ p₀ →
  ∀ p : ℝ, p ≤ 1 →
  (height k p₀ p : ℝ) ≤ 2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k :=
begin
  have : tendsto (λ k : ℝ, ⌊2 / (k : ℝ) ^ (-1 / 4 : ℝ) * log k⌋₊) at_top at_top,
  { refine tendsto_nat_floor_at_top.comp _,
    rw neg_div,
    refine tendsto.at_top_mul_at_top _ tendsto_log_at_top,
    have : ∀ᶠ k : ℝ in at_top, 2 * k ^ (1 / 4 : ℝ) = 2 / k ^ (-(1 / 4) : ℝ),
    { filter_upwards [eventually_ge_at_top (0 : ℝ)] with k hk,
      rw [rpow_neg hk, div_inv_eq_mul] },
    refine tendsto.congr' this _,
    exact (tendsto_rpow_at_top (by norm_num)).const_mul_at_top two_pos },
  have := this.comp tendsto_coe_nat_at_top_at_top,
  filter_upwards [eventually_ne_at_top 0, this.eventually_ge_at_top 1,
    one_lt_q_function] with k hk hk' hk'' --
    p₀ hp₀ p hp,
  rw [←nat.le_floor_iff', height, dif_pos],
  rotate,
  { exact hk },
  { rw ←pos_iff_ne_zero,
    exact one_le_height },
  refine nat.find_min' _ _,
  exact ⟨hk', hp.trans (hk'' p₀ hp₀)⟩,
end

open_locale big_operators

-- #check weight

variables {V : Type*} [decidable_eq V] [fintype V] {χ : top_edge_labelling V (fin 2)}

lemma five_five_aux_part_one {X Y : finset V} :
  ∑ x y in X, red_density χ X Y * ((red_neighbors χ x ∩ Y).card) =
    (red_density χ X Y) ^ 2 * X.card ^ 2 * Y.card :=
begin
  simp_rw [sum_const, nsmul_eq_mul, ←mul_sum],
  suffices : red_density χ X Y * X.card * Y.card = ∑ (x : V) in X, (red_neighbors χ x ∩ Y).card,
  { rw [←this, sq, sq],
    linarith only },
  rw [mul_right_comm, mul_assoc, col_density_comm, col_density_mul_mul],
end

lemma five_five_aux_part_two {X Y : finset V} :
  ∑ x y in X, (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card =
    ∑ z in Y, (red_neighbors χ z ∩ X).card ^ 2 :=
begin
  simp_rw [inter_comm, card_eq_sum_ones, ←@filter_mem_eq_inter _ _ Y, ←@filter_mem_eq_inter _ _ X,
    sum_filter, sq, sum_mul, mul_sum, boole_mul, ←ite_and, mem_inter, @sum_comm _ _ _ _ Y],
  refine sum_congr rfl (λ x hx, _),
  refine sum_congr rfl (λ x' hx', _),
  refine sum_congr rfl (λ y hy, _),
  refine if_congr _ rfl rfl,
  rw @mem_col_neighbors_comm _ _ _ _ _ _ y,
  rw @mem_col_neighbors_comm _ _ _ _ _ _ y,
end

-- this proof might be possible without the empty casing from the col_density_sum variants
lemma five_five_aux {X Y : finset V} :
  ∑ x y in X, red_density χ X Y * (red_neighbors χ x ∩ Y).card ≤
    ∑ x y in X, (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card :=
begin
  simp only [←nat.cast_sum],
  rw [five_five_aux_part_one, five_five_aux_part_two, nat.cast_sum],
  have : (∑ z in Y, (red_neighbors χ z ∩ X).card : ℝ) ^ 2 ≤
    (Y.card : ℝ) * ∑ z in Y, ((red_neighbors χ z ∩ X).card : ℝ) ^ 2 := sq_sum_le_card_mul_sum_sq,
  rcases X.eq_empty_or_nonempty with rfl | hX,
  { simp },
  rcases Y.eq_empty_or_nonempty with rfl | hY,
  { simp },
  have hY : 0 < (Y.card : ℝ) := by positivity,
  rw [←div_le_iff' hY] at this,
  simp only [nat.cast_pow],
  refine this.trans_eq' _,
  rw [col_density_comm],
  rw [col_density_eq_sum, div_pow, div_mul_eq_mul_div, mul_pow, mul_div_mul_right,
    div_mul_eq_mul_div, sq (Y.card : ℝ), mul_div_mul_right _ _ hY.ne'],
  positivity
end

-- (13) observation 5.5
lemma five_five (χ : top_edge_labelling V (fin 2)) (X Y : finset V) :
  0 ≤ ∑ x y in X, pair_weight χ X Y x y :=
begin
  simp_rw [pair_weight, ←mul_sum, sum_sub_distrib],
  refine mul_nonneg (by positivity) (sub_nonneg_of_le _),
  exact five_five_aux
end

lemma tendsto_nat_ceil_at_top {α : Type*} [linear_ordered_semiring α] [floor_semiring α] :
  tendsto (λ (x : α), ⌈x⌉₊) at_top at_top :=
nat.ceil_mono.tendsto_at_top_at_top (λ n, ⟨n, (nat.ceil_nat_cast _).ge⟩)

lemma log_le_log_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
  log x ≤ log y :=
(log_le_log hx (hx.trans_le hxy)).2 hxy

lemma log_n_large (c : ℝ) : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  c ≤ 1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have := ((tendsto_rpow_at_top h34).at_top_mul_at_top tendsto_log_at_top).const_mul_at_top
    (show (0 : ℝ) < 1 / 128, by norm_num),
  filter_upwards [(this.comp t).eventually_ge_at_top c, t.eventually_gt_at_top (0 : ℝ)] with
    l hl hl' k hlk,
  refine hl.trans _,
  dsimp,
  rw ←mul_assoc,
  exact mul_le_mul_of_nonneg_left (log_le_log_of_le hl' (nat.cast_le.2 hlk)) (by positivity),
end

lemma five_six_aux_left_term : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ *
    ((k : ℝ) ^ (-1/8 : ℝ)) ^ ((⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 / 4) < 1 / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h12 : (0 : ℝ) < 1 / 2, { norm_num },
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have h32 : (0 : ℝ) < 3 / 2, { norm_num },
  have := ((tendsto_rpow_at_top h34).comp t).eventually (ceil_eventually_le 2 one_lt_two),
  filter_upwards [this, log_n_large 1, t.eventually_gt_at_top (1 : ℝ),
    (((tendsto_rpow_at_top h32).at_top_mul_at_top tendsto_log_at_top).comp t).eventually_gt_at_top
      (64 * log 2)] with l h₁ h₂ h₃ h₄
    k hlk,
  dsimp at h₁,
  specialize h₂ k hlk,
  have h₃' : (1 : ℝ) < k := h₃.trans_le (nat.cast_le.2 hlk),
  have h₃'1 : (0 : ℝ) < k := zero_lt_one.trans h₃',
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊,
  { rw [nat.cast_pos, nat.floor_pos],
    exact one_le_exp (h₂.trans' zero_le_one) },
  rw [←rpow_mul (nat.cast_nonneg k), ←log_lt_log_iff],
  rotate,
  { exact mul_pos (pow_pos h'₁ _) (rpow_pos_of_pos h₃'1 _) },
  { norm_num1 },
  rw [log_mul, log_pow, log_rpow h₃'1, mul_comm],
  rotate,
  { exact (pow_pos h'₁ _).ne' },
  { exact (rpow_pos_of_pos h₃'1 _).ne' },
  refine (add_le_add_right (mul_le_mul (log_le_log_of_le h'₁ (nat.floor_le (exp_pos _).le)) h₁
    (nat.cast_nonneg _) _) _).trans_lt _,
  { rw log_exp,
    exact h₂.trans' zero_le_one },
  rw [log_exp, neg_div, neg_mul, div_mul_div_comm, one_mul, mul_right_comm, ←add_mul,
    mul_mul_mul_comm, ←rpow_add (zero_lt_one.trans h₃), mul_comm (1 / 128 : ℝ), ←div_eq_mul_one_div,
    div_eq_mul_one_div (_ ^ 2 : ℝ)],
  have : (l : ℝ) ^ (2 * (3 / 4) : ℝ) ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2,
  { calc _ = (l : ℝ) ^ ((3 / 4) * 2 : ℝ) : by rw [mul_comm]
      ... = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℝ) : rpow_mul (nat.cast_nonneg _) _ _
      ... = ((l : ℝ) ^ (3 / 4 : ℝ)) ^ (2 : ℕ) : rpow_two _
      ... ≤ (⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊ : ℝ) ^ 2 :
        pow_le_pow_of_le_left (by positivity) (nat.le_ceil _) _ },
  refine (mul_le_mul_of_nonneg_right (add_le_add_left (neg_le_neg (mul_le_mul_of_nonneg_right
    this (by norm_num))) _) (log_nonneg h₃'.le)).trans_lt _,
  rw [←two_mul, mul_comm (_ / _), ←sub_eq_add_neg, ←mul_sub, mul_right_comm],
  norm_num1,
  rw [one_div (2 : ℝ), mul_neg, log_inv, neg_lt_neg_iff, ←div_eq_mul_one_div, lt_div_iff'],
  swap,
  { norm_num },
  exact (mul_le_mul_of_nonneg_left (log_le_log_of_le (zero_lt_one.trans h₃) (nat.cast_le.2 hlk))
    (by positivity)).trans_lt' h₄,
end

lemma five_six_aux_right_term_aux : ∀ᶠ k : ℝ in at_top,
  1 ≤ 32 * k ^ (1 / 8 : ℝ) - log k :=
begin
  have h8 : (0 : ℝ) < 1 / 8, { norm_num },
  filter_upwards [(is_o_log_rpow_at_top h8).def zero_lt_one,
    (tendsto_rpow_at_top h8).eventually_ge_at_top 1,
    tendsto_log_at_top.eventually_ge_at_top (0 : ℝ),
    eventually_ge_at_top (0 : ℝ)] with x hx hx' hxl hx₀,
  rw [norm_of_nonneg hxl, norm_of_nonneg (rpow_nonneg_of_nonneg hx₀ _), one_mul] at hx,
  linarith only [hx, hx']
end

lemma five_six_aux_right_term : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  (⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊ : ℝ) ^ k *
    exp (- k ^ (-1 / 8 : ℝ) * k ^ 2 / 4)
    < 1 / 2 :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h : (0 : ℝ) < 3 / 4 + 1, { norm_num1 },
  filter_upwards [eventually_gt_at_top 1, log_n_large 1,
    top_adjuster (((tendsto_rpow_at_top h).comp t).eventually_gt_at_top (128 * log 2)),
    top_adjuster (t.eventually five_six_aux_right_term_aux)] with
    l h₁ h₂ h₃ h₄ --
    k hlk,
  specialize h₂ k hlk,
  have h'₁ : (0 : ℝ) < ⌊exp (1 / 128 * (l : ℝ) ^ (3 / 4 : ℝ) * log k)⌋₊,
  { rw [nat.cast_pos, nat.floor_pos],
    exact one_le_exp (h₂.trans' zero_le_one) },
  rw [neg_mul, ←rpow_two, ←rpow_add, ←log_lt_log_iff (mul_pos (pow_pos h'₁ _) (exp_pos _)),
    log_mul (pow_ne_zero _ h'₁.ne') (exp_pos _).ne', log_exp, log_pow],
  rotate,
  { norm_num1 },
  { rwa nat.cast_pos,
    exact zero_lt_one.trans (h₁.trans_le hlk) },
  refine (add_le_add_right (mul_le_mul_of_nonneg_left (log_le_log_of_le h'₁ (nat.floor_le
    (exp_pos _).le)) (nat.cast_nonneg _)) _).trans_lt _,
  rw [log_exp, mul_right_comm, ←mul_assoc],
  refine (add_le_add_right (mul_le_mul_of_nonneg_left (rpow_le_rpow (nat.cast_nonneg _)
    (nat.cast_le.2 hlk) _) (mul_nonneg (nat.cast_nonneg _) (mul_nonneg _ _))) _).trans_lt _,
  { norm_num1 },
  { norm_num1 },
  { exact log_nonneg (nat.one_le_cast.2 (h₁.le.trans hlk)) },
  rw [mul_comm, ←mul_assoc, ←rpow_add_one, neg_div, ←sub_eq_add_neg, ←mul_assoc],
  swap,
  { rw [nat.cast_ne_zero],
    linarith only [h₁.le.trans hlk] },
  have h : (k : ℝ) ^ ((-1) / 8 + 2 : ℝ) / 4 =
    k ^ (3 / 4 + 1 : ℝ) * (1 / 128) * (32 * k ^ (1 / 8 : ℝ)),
  { rw [←div_eq_mul_one_div, div_eq_mul_one_div _ (4 : ℝ), div_mul_eq_mul_div, mul_left_comm,
      ←rpow_add, ←div_mul_eq_mul_div, mul_comm],
    { norm_num1, refl },
    rwa nat.cast_pos,
    exact zero_lt_one.trans (h₁.trans_le hlk) },
  rw [h, ←mul_sub, one_div (2 : ℝ), log_inv, lt_neg, ←mul_neg, neg_sub, mul_one_div,
    div_mul_eq_mul_div, lt_div_iff'],
  swap, { norm_num1 },
  refine (h₃ _ hlk).trans_le _,
  exact le_mul_of_one_le_right (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (h₄ _ hlk),
end

lemma five_six_aux_part_one : ∃ c : ℝ, 0 < c ∧ ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  exp (c * l ^ (3 / 4 : ℝ) * log k) ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  refine ⟨1 / 128, by norm_num, _⟩,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_at_top h34)).comp t,
  filter_upwards [top_adjuster (t.eventually_gt_at_top 0), eventually_ge_at_top 2,
    this.eventually_ge_at_top 2, five_six_aux_left_term, five_six_aux_right_term,
    top_adjuster root_ε_lt_one]
    with l hl₁ℕ hl₂ℕ hl₃ hf' hf'' hε k hlk,
  refine le_of_lt _,
  rw ←nat.floor_lt (exp_pos _).le,
  specialize hf' k hlk,
  specialize hf'' k hlk,
  set p : ℝ := k ^ (-1/8 : ℝ),
  have hp₀ : 0 < p,
  { refine rpow_pos_of_pos _ _,
    exact hl₁ℕ k hlk },
  have hp₁ : p < 1 := hε k hlk,
  rw ramsey_number_pair_swap,
  refine basic_off_diagonal_ramsey_bound hp₀ hp₁ hl₃ (hl₂ℕ.trans hlk) _,
  exact (add_lt_add hf' hf'').trans_eq (by norm_num),
end

lemma five_six : ∀ᶠ l : ℕ in at_top, ∀ k : ℕ, l ≤ k →
  k ^ 6 * ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] ≤
    ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  obtain ⟨c, hc, hf⟩ := five_six_aux_part_one,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h23 : (0 : ℝ) < 2 / 3, { norm_num },
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  have h2334 : (2 / 3 : ℝ) < (3 / 4), { norm_num },
  have hc6 : 0 < c / 6, { positivity },
  have := ((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6,
  filter_upwards [hf, top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster ((tendsto_log_at_top.comp t).eventually_ge_at_top 0),
    ((tendsto_rpow_at_top h23).comp t).eventually (ceil_eventually_le 6 (by norm_num)),
    t.eventually (((is_o_one_rpow h34).add (is_o_rpow_rpow h2334)).def hc6)] with
    l hl hl₀ hll₀ hl' hl₁
    k hlk,
  specialize hl k hlk,
  rw ramsey_number_pair_swap,
  refine (nat.mul_le_mul_left _ ramsey_number_le_right_pow_left').trans _,
  rw [←@nat.cast_le ℝ, ←pow_add, nat.cast_pow],
  refine hl.trans' _,
  rw [←log_le_iff_le_exp (pow_pos (hl₀ _ hlk) _), log_pow, nat.cast_add, nat.cast_bit0,
    nat.cast_bit1, nat.cast_one],
  refine mul_le_mul_of_nonneg_right _ (hll₀ _ hlk),
  refine (add_le_add_left hl' _).trans _,
  rw [←mul_one_add, ←le_div_iff', ←div_mul_eq_mul_div],
  swap,
  { norm_num1 },
  refine ((le_norm_self _).trans hl₁).trans_eq _,
  rw [norm_of_nonneg],
  exact rpow_nonneg_of_nonneg (nat.cast_nonneg _) _,
end

lemma abs_pair_weight_le_one {X Y : finset V} {x y : V} : |pair_weight χ X Y x y| ≤ 1 :=
begin
  rw [pair_weight, abs_mul, abs_inv],
  cases nat.eq_zero_or_pos Y.card,
  { rw [h, nat.cast_zero, abs_zero, inv_zero, zero_mul],
    exact zero_le_one },
  rw [nat.abs_cast, inv_mul_le_iff, mul_one],
  swap,
  { rwa nat.cast_pos },
  have hr₀ : 0 ≤ red_density χ X Y := col_density_nonneg,
  have hr₁ : red_density χ X Y ≤ 1 := col_density_le_one,
  have : set.uIcc (red_density χ X Y * (red_neighbors χ x ∩ Y).card)
    (red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card ⊆
    set.uIcc 0 Y.card,
  { rw [set.uIcc_subset_uIcc_iff_mem, set.uIcc_of_le, set.mem_Icc, set.mem_Icc, and_assoc],
    swap,
    { exact nat.cast_nonneg _ },
    exact ⟨by positivity, mul_le_of_le_one_of_le' hr₁ (nat.cast_le.2 (card_le_of_subset
      (inter_subset_right _ _))) hr₀ (nat.cast_nonneg _), nat.cast_nonneg _, nat.cast_le.2
      (card_le_of_subset (inter_subset_right _ _))⟩ },
  refine (set.abs_sub_le_of_uIcc_subset_uIcc this).trans _,
  simp
end

lemma sum_pair_weight_eq {X Y : finset V} (y : V) (hy : y ∈ X) :
  ∑ x in X, pair_weight χ X Y y x = weight χ X Y y + pair_weight χ X Y y y :=
by rw [weight, sum_erase_add _ _ hy]

lemma double_sum_pair_weight_eq {X Y : finset V} :
  ∑ x y in X, pair_weight χ X Y x y = ∑ y in X, (weight χ X Y y + pair_weight χ X Y y y) :=
sum_congr rfl sum_pair_weight_eq

lemma sum_pair_weight_le {X Y : finset V} (y : V) (hy : y ∈ X) :
  weight χ X Y y + pair_weight χ X Y y y ≤ X.card :=
begin
  rw [←sum_pair_weight_eq _ hy],
  refine le_of_abs_le ((abs_sum_le_sum_abs _ _).trans _),
  refine (sum_le_card_nsmul _ _ 1 _).trans_eq (nat.smul_one_eq_coe _),
  intros x hx,
  exact abs_pair_weight_le_one,
end

lemma five_four_aux (μ : ℝ) (k l : ℕ) (ini : book_config χ) (i : ℕ)
  (hi : i ∈ red_or_density_steps μ k l ini) :
  (0 : ℝ) ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊] * (algorithm μ k l ini i).X.card +
    ((algorithm μ k l ini i).X.card - ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊]) *
    (weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).Y (get_x hi) + 1) :=
begin
  set C := algorithm μ k l ini i,
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊],
  have hi' := hi,
  simp only [red_or_density_steps, mem_filter, mem_range] at hi',
  change (0 : ℝ) ≤ m * C.X.card +
    (C.X.card - m) * (weight χ C.X C.Y (get_x hi) + 1),
  refine (five_five χ C.X C.Y).trans _,
  rw [double_sum_pair_weight_eq],
  rw book_config.num_big_blues at hi',
  have : C.X.card - m ≤ (book_config.central_vertices μ C).card,
  { rw [tsub_le_iff_right, book_config.central_vertices],
    refine (add_le_add_left hi'.2.2.le _).trans' ((card_union_le _ _).trans' (card_le_of_subset _)),
    rw ←filter_or,
    simp only [finset.subset_iff, mem_filter, true_and] {contextual := tt},
    intros x hx,
    exact le_total _ _ },
  obtain ⟨nei, Bnei, neicard⟩ := exists_smaller_set _ _ this,
  have : ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] < C.X.card :=
    ramsey_number_lt_of_lt_final_step hi'.1,
  have hm : m ≤ C.X.card,
  { refine this.le.trans' _,
    refine ramsey_number.mono_two le_rfl _,
    refine nat.ceil_mono _,
    rcases nat.eq_zero_or_pos l with rfl | hl,
    { rw [nat.cast_zero, zero_rpow, zero_rpow]; norm_num1 },
    refine rpow_le_rpow_of_exponent_le _ (by norm_num1),
    rwa [nat.one_le_cast, nat.succ_le_iff] },
  have : book_config.central_vertices μ C ⊆ C.X := filter_subset _ _,
  have h : (C.X \ nei).card = m,
  { rw [card_sdiff (Bnei.trans this), neicard, nat.sub_sub_self hm] },
  rw [←sum_sdiff (Bnei.trans this), ←nsmul_eq_mul, ←nat.cast_sub hm, ←neicard, ←h, ←nsmul_eq_mul],
  refine add_le_add (sum_le_card_nsmul _ _ _ _) (sum_le_card_nsmul _ _ _ _),
  { intros x hx,
    exact sum_pair_weight_le x (sdiff_subset _ _ hx)},
  intros x hx,
  refine add_le_add _ (le_of_abs_le abs_pair_weight_le_one),
  refine book_config.get_central_vertex_max _ _ _ _ _,
  exact Bnei hx,
end

lemma five_four_end : ∀ᶠ k : ℝ in at_top, 1 / (k ^ 6 - 1) + 1 / k ^ 6 ≤ 1 / k ^ 5 :=
begin
  filter_upwards [eventually_ge_at_top (3 : ℝ)] with k hk₁,
  rw [←add_halves' (1 / k ^ 5), div_div],
  have h1 : 0 < k ^ 5 * 2,
  { positivity },
  suffices h2 : k ^ 5 * 2 ≤ k ^ 6 - 1,
  { refine add_le_add (one_div_le_one_div_of_le h1 h2) (one_div_le_one_div_of_le h1 (h2.trans _)),
    simp },
  rw [pow_succ' _ 5, le_sub_comm, ←mul_sub],
  exact one_le_mul_of_one_le_of_one_le (one_le_pow_of_one_le (hk₁.trans' (by norm_num)) _)
    (by linarith only [hk₁]),
end

lemma five_four :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ : ℝ,
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
  ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  - ((algorithm μ k l ini i).X.card : ℝ) / k ^ 5 ≤
    weight χ (algorithm μ k l ini i).X (algorithm μ k l ini i).Y (get_x hi) :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h23 : (0 : ℝ) < 2 / 3, { norm_num },
  have := (tendsto_nat_ceil_at_top.comp (tendsto_rpow_at_top h23)).comp t,
  filter_upwards [five_six, this.eventually_ge_at_top 1,
    top_adjuster (eventually_gt_at_top 1),
    top_adjuster (t.eventually five_four_end)] with l hl hl' hl₂ hl₃
    k hlk μ n χ ini i hi,
  specialize hl₂ k hlk,
  specialize hl₃ k hlk,
  have hi' := hi,
  rw [red_or_density_steps, mem_filter, mem_range] at hi',
  set C := algorithm μ k l ini i,
  change - (C.X.card : ℝ) / k ^ 5 ≤ weight χ C.X C.Y (get_x hi),
  let m := ramsey_number ![k, ⌈(l : ℝ) ^ (2 / 3 : ℝ)⌉₊],
  have h₅₄ : (0 : ℝ) ≤ m * C.X.card + (C.X.card - m) * (weight χ C.X C.Y _ + 1) :=
    five_four_aux μ k l ini i hi,
  have hm : 1 ≤ m,
  { refine ramsey_number_ge_min _ _,
    simp only [fin.forall_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
      hl₂.le, true_and, hl'] },
  have hX : k ^ 6 * m ≤ C.X.card := (hl k hlk).trans (ramsey_number_lt_of_lt_final_step hi'.1).le,
  have h : (k ^ 6 - 1 : ℝ) * m ≤ (C.X.card : ℝ) - m,
  { rw [sub_one_mul, sub_le_sub_iff_right],
    exact_mod_cast hX },
  have c : (k ^ 6 : ℝ) ≤ C.X.card,
  { rw [←nat.cast_pow, nat.cast_le],
    exact hX.trans' (nat.le_mul_of_pos_right hm) },
  have b' : (m : ℝ) < C.X.card,
  { rw [nat.cast_lt],
    refine hX.trans_lt' _,
    refine lt_mul_left hm _,
    exact one_lt_pow hl₂ (by norm_num) },
  have b : (0 : ℝ) < C.X.card - m,
  { rwa [sub_pos] },
  have : (0 : ℝ) < C.X.card,
  { refine b.trans_le _,
    simp only [sub_le_self_iff, nat.cast_nonneg] },
  rw [neg_div, div_eq_mul_one_div, ←mul_neg, ←le_div_iff' this],
  have : - (m / (C.X.card - m) + 1 / C.X.card : ℝ) ≤ weight χ C.X C.Y (get_x hi) / C.X.card,
  { rw [neg_le_iff_add_nonneg', add_assoc, div_add_div_same, add_comm (1 : ℝ),
      div_add_div _ _ b.ne' this.ne'],
    exact div_nonneg h₅₄ (mul_nonneg b.le (nat.cast_nonneg _)) },
  refine this.trans' _,
  rw [neg_le_neg_iff],
  refine (add_le_add (div_le_div_of_le_left _ _ h)
    (div_le_div_of_le_left zero_le_one _ c)).trans _,
  { exact nat.cast_nonneg _ },
  { refine mul_pos (sub_pos_of_lt (one_lt_pow (nat.one_lt_cast.2 hl₂) (by norm_num1))) _,
    rwa nat.cast_pos },
  { refine pow_pos _ _,
    rwa nat.cast_pos,
    exact hl₂.le },
  rw [mul_comm, ←div_div, div_self],
  swap,
  { rw [nat.cast_ne_zero, ←pos_iff_ne_zero],
    exact hm },
  exact hl₃
end

lemma five_seven_aux {k : ℕ} {p₀ p : ℝ} :
  α_function k (height k p₀ p) =
    (k : ℝ) ^ (- 1 / 4 : ℝ) * (q_function k p₀ (height k p₀ p - 1) - q_function k p₀ 0 + 1 / k) :=
by rw [α_function, q_function, q_function, pow_zero, sub_self, zero_div, add_zero, add_sub_cancel',
    ←add_div, sub_add_cancel, mul_div_assoc]

lemma height_spec {k : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) :
  p ≤ q_function k p₀ (height k p₀ p) :=
begin
  rw [height, dif_pos hk],
  exact (nat.find_spec (q_function_above _ _ hk)).2,
end

lemma height_min {k h : ℕ} {p₀ p : ℝ} (hk : k ≠ 0) (hh : h ≠ 0) :
  p ≤ q_function k p₀ h → height k p₀ p ≤ h :=
begin
  intro h',
  rw [height, dif_pos hk],
  refine nat.find_min' (q_function_above _ _ hk) ⟨hh.bot_lt, h'⟩,
end

lemma five_seven_left {k : ℕ} {p₀ p : ℝ} :
  (k : ℝ) ^ (- 1 / 4 : ℝ) / k ≤ α_function k (height k p₀ p) :=
begin
  rw [five_seven_aux, div_eq_mul_one_div],
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  rw [le_add_iff_nonneg_left, sub_nonneg],
  refine q_increasing _,
  exact nat.zero_le _
end

lemma α_one {k : ℕ} : α_function k 1 = (k : ℝ) ^ (- 1 / 4 : ℝ) / k :=
by rw [α_function, nat.sub_self, pow_zero, mul_one]

lemma q_height_lt_p {k : ℕ} {p₀ p : ℝ} (h : 1 < height k p₀ p) :
  q_function k p₀ (height k p₀ p - 1) < p :=
begin
  have : k ≠ 0,
  { replace h := h.ne',
    rw [height] at h,
    simp only [ne.def, dite_eq_right_iff, not_forall] at h,
    obtain ⟨hh, -⟩ := h,
    exact hh },
  by_contra' z,
  have := height_min this _ z,
  { rw ←not_lt at this,
    exact this (nat.sub_lt one_le_height zero_lt_one) },
  simpa using h,
end

lemma five_seven_right {k : ℕ} {p₀ p : ℝ} (h : q_function k p₀ 0 ≤ p) :
  α_function k (height k p₀ p) ≤ (k : ℝ) ^ (- 1 / 4 : ℝ) * (p - q_function k p₀ 0 + 1 / k) :=
begin
  rw [five_seven_aux],
  refine mul_le_mul_of_nonneg_left _ (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _),
  simp only [add_le_add_iff_right, sub_le_sub_iff_right],
  cases lt_or_eq_of_le (@one_le_height k p₀ p) with h₁ h₁,
  { exact (q_height_lt_p h₁).le },
  rwa [h₁, nat.sub_self],
end

lemma five_seven_extra {k : ℕ} {p₀ p : ℝ} (h' : p ≤ q_function k p₀ 1) :
  height k p₀ p = 1 :=
begin
  rw [height],
  split_ifs,
  { rw nat.find_eq_iff,
    simp [h'] },
  refl
end

-- WARNING: the hypothesis 1 / k ≤ ini.p should be seen as setting an absolute lower bound on p₀,
-- and k and ini both depend on it, with 1 / k ≤ it ≤ ini.p
lemma five_eight {μ : ℝ} {k l : ℕ} {ini : book_config χ} (h : 1 / (k : ℝ) ≤ ini.p)
  {i : ℕ} (hi : i ∈ degree_steps μ k l ini)
  (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
  (1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * (algorithm μ k l ini i).p * (algorithm μ k l ini (i + 1)).Y.card ≤
    (red_neighbors χ x ∩ (algorithm μ k l ini (i + 1)).Y).card :=
begin
  set C := algorithm μ k l ini i,
  set ε := (k : ℝ) ^ (- 1 / 4 : ℝ),
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_Y],
  rw [degree_regularisation_applied hi, book_config.degree_regularisation_step_X, mem_filter] at hx,
  rw [degree_steps, mem_filter, mem_range] at hi,
  change (1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * C.p * C.Y.card ≤ (red_neighbors χ x ∩ C.Y).card,
  change x ∈ C.X ∧ (C.p - _ * α_function k (C.height k ini.p)) * (C.Y.card : ℝ) ≤
    (red_neighbors χ x ∩ C.Y).card at hx,
  have : 1 / (k : ℝ) < C.p := one_div_k_lt_p_of_lt_final_step hi.1,
  refine hx.2.trans' (mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)),
  rw [one_sub_mul, sub_le_sub_iff_left],
  cases le_total C.p (q_function k ini.p 0) with h' h',
  { rw [book_config.height, five_seven_extra, α_one, mul_div_assoc', ←rpow_add' (nat.cast_nonneg _),
      div_eq_mul_one_div],
    { refine (mul_le_mul_of_nonneg_left this.le (rpow_nonneg_of_nonneg (nat.cast_nonneg _)
        _)).trans_eq _,
      norm_num },
    { norm_num },
    exact h'.trans (q_increasing zero_le_one) },
  refine (mul_le_mul_of_nonneg_left (five_seven_right h') (rpow_nonneg_of_nonneg
    (nat.cast_nonneg _) _)).trans _,
  rw [←mul_assoc, ←rpow_add' (nat.cast_nonneg _)],
  swap,
  { norm_num1 },
  refine mul_le_mul _ _ _ _,
  { refine le_of_eq _,
    norm_num },
  { rw [q_function_zero, sub_add, sub_le_self_iff, sub_nonneg],
    exact h },
  { refine add_nonneg _ _,
    { rwa sub_nonneg },
    { positivity } },
  { positivity }
end

lemma five_eight_weak {μ : ℝ} {k l : ℕ} {ini : book_config χ} (h : 1 / (k : ℝ) ≤ ini.p)
  {i : ℕ} (hi : i ∈ degree_steps μ k l ini)
  (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
  (1 - (k : ℝ) ^ (- 1 / 8 : ℝ)) * (1 / k) * (algorithm μ k l ini (i + 1)).Y.card ≤
    (red_neighbors χ x ∩ (algorithm μ k l ini (i + 1)).Y).card :=
begin
  rcases eq_or_ne k 0 with rfl | hk,
  { simp },
  refine (five_eight h hi x hx).trans' _,
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  refine mul_le_mul_of_nonneg_left _ _,
  { rw [degree_steps, mem_filter, mem_range] at hi,
    exact (one_div_k_lt_p_of_lt_final_step hi.1).le },
  rw sub_nonneg,
  refine rpow_le_one_of_one_le_of_nonpos _ (by norm_num),
  rwa [nat.one_le_cast, nat.succ_le_iff, pos_iff_ne_zero],
end

lemma five_eight_weaker (p₀l : ℝ) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ,
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  ∀ x : fin n,
  i ∈ degree_steps μ k l ini →
  x ∈ (algorithm μ k l ini (i + 1)).X →
  ((1 : ℝ) / (2 * k)) * (algorithm μ k l ini (i + 1)).Y.card ≤
    (red_neighbors χ x ∩ (algorithm μ k l ini (i + 1)).Y).card :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have := tendsto_rpow_neg_at_top (show (0 : ℝ) < 1 / 8, by norm_num),
  have := eventually_le_of_tendsto_lt (show (0 : ℝ) < 1 - 2⁻¹, by norm_num) this,
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually this)] with
    l hl hl₂
    k hlk μ n χ ini hini i x hi hx,
  specialize hl k hlk,
  specialize hl₂ k hlk,
  refine (five_eight_weak _ hi x hx).trans' _,
  { refine hini.trans' _,
    rw [one_div],
    exact inv_le_of_inv_le hp₀l hl },
  refine mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _),
  rw [one_div, mul_inv, one_div],
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  rw [le_sub_comm, neg_div],
  exact hl₂
end

lemma five_eight_weaker' (p₀l : ℝ) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ,
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  ∀ x : fin n,
  i ∈ red_or_density_steps μ k l ini →
  x ∈ (algorithm μ k l ini i).X →
  ((1 : ℝ) / (2 * k)) * (algorithm μ k l ini i).Y.card ≤
    (red_neighbors χ x ∩ (algorithm μ k l ini i).Y).card :=
begin
  filter_upwards [five_eight_weaker p₀l hp₀l] with
    l hl k hlk μ n χ ini hini i x hi hx,
  rw [red_or_density_steps, mem_filter, ←nat.odd_iff_not_even, mem_range] at hi,
  rcases hi.2.1 with ⟨j, rfl⟩,
  refine hl k hlk μ n χ ini hini (2 * j) x _ hx,
  rw [degree_steps, mem_filter, mem_range],
  exact ⟨hi.1.trans_le' (nat.le_succ _), by simp⟩,
end

lemma q_height_le_two {k : ℕ} {p₀ p : ℝ} (hp₀₁ : p₀ ≤ 1) (hp₂ : p ≤ 2) :
  q_function k p₀ (height k p₀ p - 1) ≤ 2 :=
begin
  cases eq_or_lt_of_le (@one_le_height k p₀ p) with h₁ h₁,
  { rw [←h₁, nat.sub_self, q_function_zero],
    exact hp₀₁.trans one_le_two },
  exact (q_height_lt_p h₁).le.trans hp₂,
end

lemma α_le_one {k : ℕ} {p₀ p : ℝ} (hp₀₁ : p₀ ≤ 1) (h : 1 / (k : ℝ) ≤ p₀) (hk : 2 ^ 4 ≤ k)
  (hp : p ≤ 2) :
  α_function k (height k p₀ p) ≤ 1 :=
begin
  rcases eq_or_ne k 0 with rfl | hk₀,
  { rw [α_function],
    simp only [char_p.cast_eq_zero, div_zero, zero_le_one] },
  rw [five_seven_aux, q_function_zero, mul_comm, ←le_div_iff, neg_div, rpow_neg (nat.cast_nonneg _),
    one_div _⁻¹, inv_inv],
  swap,
  { positivity },
  rw sub_add,
  refine (sub_le_sub_right (q_height_le_two hp₀₁ hp) _).trans _,
  refine (sub_le_self _ (sub_nonneg_of_le h)).trans _,
  refine (rpow_le_rpow (by norm_num1) (nat.cast_le.2 hk) (by norm_num)).trans' _,
  rw [nat.cast_pow, ←rpow_nat_cast, ←rpow_mul];
  norm_num,
end

variables {k l : ℕ} {ini : book_config χ} {i : ℕ}

lemma p_pos {μ : ℝ} (hi : i < final_step μ k l ini) : 0 < (algorithm μ k l ini i).p :=
begin
  refine (one_div_k_lt_p_of_lt_final_step hi).trans_le' _,
  positivity
end

lemma X_nonempty {μ : ℝ} (hi : i < final_step μ k l ini) : (algorithm μ k l ini i).X.nonempty :=
begin
  refine nonempty_of_ne_empty _,
  intro h,
  refine (p_pos hi).ne' _,
  rw [book_config.p, h, col_density_empty_left],
end

lemma Y_nonempty {μ : ℝ} (hi : i < final_step μ k l ini) : (algorithm μ k l ini i).Y.nonempty :=
begin
  refine nonempty_of_ne_empty _,
  intro h,
  refine (p_pos hi).ne' _,
  rw [book_config.p, h, col_density_empty_right],
end

-- WARNING: the hypothesis 1 / k ≤ ini.p should be seen as setting an absolute lower bound on p₀,
-- and k and ini both depend on it, with 1 / k ≤ it ≤ ini.p
lemma red_neighbors_Y_nonempty {μ : ℝ} (h : 1 / (k : ℝ) ≤ ini.p) (hk : 1 < k)
  (hi : i ∈ degree_steps μ k l ini)
  (x : V) (hx : x ∈ (algorithm μ k l ini (i + 1)).X) :
  (red_neighbors χ x ∩ (algorithm μ k l ini (i + 1)).Y).nonempty :=
begin
  rw [←card_pos, ←@nat.cast_pos ℝ],
  have : i < final_step μ k l ini,
  { rw [degree_steps, mem_filter, mem_range] at hi,
    exact hi.1 },
  refine (five_eight h hi x hx).trans_lt' _,
  refine mul_pos (mul_pos _ (p_pos this)) _,
  { rw [sub_pos],
    refine rpow_lt_one_of_one_lt_of_neg _ _,
    { rwa nat.one_lt_cast },
    norm_num1 },
  rw [nat.cast_pos, card_pos, degree_regularisation_applied hi,
    book_config.degree_regularisation_step_Y],
  exact Y_nonempty this,
end

lemma red_neighbors_Y_nonempty' {μ : ℝ} (h : 1 / (k : ℝ) ≤ ini.p) (hk : 1 < k)
  (hi : i ∈ red_or_density_steps μ k l ini)
  (x : V) (hx : x ∈ (algorithm μ k l ini i).X) :
  (red_neighbors χ x ∩ (algorithm μ k l ini i).Y).nonempty :=
begin
  rw [red_or_density_steps, mem_filter, ←nat.odd_iff_not_even, mem_range] at hi,
  rcases hi.2.1 with ⟨j, rfl⟩,
  refine red_neighbors_Y_nonempty h hk _ x hx,
  rw [degree_steps, mem_filter, mem_range],
  exact ⟨hi.1.trans_le' (nat.le_succ _), by simp⟩,
end

lemma red_neighbors_eq_blue_compl {x : V} : red_neighbors χ x = (insert x (blue_neighbors χ x))ᶜ :=
begin
  ext y,
  rw [mem_compl, mem_insert, mem_col_neighbors, mem_col_neighbors, not_or_distrib],
  simp only [fin.fin_two_eq_zero_iff_ne_one, not_exists],
  split,
  { rintro ⟨p, q⟩,
    exact ⟨p.symm, λ h, q⟩ },
  rintro ⟨p, q⟩,
  exact ⟨ne.symm p, q _⟩,
end

lemma red_neighbors_inter_eq {x : V} {X : finset V} (hx : x ∈ X) :
  red_neighbors χ x ∩ X = X \ (insert x (blue_neighbors χ x ∩ X)) :=
by rw [red_neighbors_eq_blue_compl, sdiff_eq_inter_compl, inter_comm, ←insert_inter_of_mem hx,
    compl_inter, ←inf_eq_inter, ←sup_eq_union, inf_sup_left, inf_compl_self, sup_bot_eq]

lemma card_red_neighbors_inter {μ : ℝ} (hi : i ∈ red_or_density_steps μ k l ini) :
  ((red_neighbors χ (get_x hi) ∩ (algorithm μ k l ini i).X).card : ℝ) =
    (1 - blue_X_ratio μ k l ini i) * (algorithm μ k l ini i).X.card - 1 :=
begin
  rw [red_neighbors_inter_eq, cast_card_sdiff, card_insert_of_not_mem, one_sub_mul,
    nat.cast_add_one, ←sub_sub, blue_X_ratio_prop],
  { simp [not_mem_col_neighbors] },
  { rw [insert_subset],
    exact ⟨book_config.get_central_vertex_mem_X _ _ _, inter_subset_right _ _⟩ },
  { exact book_config.get_central_vertex_mem_X _ _ _ },
end

lemma blue_neighbors_eq_red_compl {x : V} : blue_neighbors χ x = (insert x (red_neighbors χ x))ᶜ :=
begin
  ext y,
  rw [mem_compl, mem_insert, mem_col_neighbors, mem_col_neighbors, not_or_distrib],
  simp only [fin.fin_two_eq_zero_iff_ne_one, not_exists, not_not],
  split,
  { rintro ⟨p, q⟩,
    exact ⟨p.symm, λ h, q⟩ },
  rintro ⟨p, q⟩,
  exact ⟨_, q (ne.symm p)⟩,
end

lemma red_neighbors_X_nonempty {μ₁ μ : ℝ} (hμ₁ : μ₁ < 1) (hμu : μ ≤ μ₁) (hk : (1 - μ₁)⁻¹ ≤ k)
  (hl : 1 < l)
  (hi : i ∈ red_or_density_steps μ k l ini) :
  (red_neighbors χ (get_x hi) ∩ (algorithm μ k l ini i).X).nonempty :=
begin
  set X := (algorithm μ k l ini i).X with ←hx,
  have hi' := hi,
  rw [red_or_density_steps, mem_filter, mem_range] at hi',
  rw [←card_pos, ←@nat.cast_pos ℝ, card_red_neighbors_inter, sub_pos],
  suffices : 1 < (1 - μ) * X.card,
  { refine this.trans_le (mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)),
    rw sub_le_sub_iff_left,
    exact blue_X_ratio_le_mu hi },
  have : (k : ℝ) < X.card,
  { rw nat.cast_lt,
    refine (ramsey_number_lt_of_lt_final_step hi'.1).trans_le' _,
    refine (ramsey_number.mono_two le_rfl _).trans_eq' ramsey_number_two_right.symm,
    rw [nat.add_one_le_ceil_iff, nat.cast_one],
    exact one_lt_rpow (nat.one_lt_cast.2 hl) (by norm_num) },
  rw [←div_lt_iff' (sub_pos_of_lt (hμ₁.trans_le' hμu)), one_div],
  refine this.trans_le' (hk.trans' _),
  exact inv_le_inv_of_le (sub_pos_of_lt hμ₁) (sub_le_sub_left hμu _),
end

lemma five_one_case_a {α : ℝ} (X Y : finset V) {x : V}
  (hxX : (red_neighbors χ x ∩ X).nonempty) (hxY : (red_neighbors χ x ∩ Y).nonempty) :
    - α * ((red_neighbors χ x ∩ X).card * (red_neighbors χ x ∩ Y).card) / Y.card ≤
      ∑ y in red_neighbors χ x ∩ X, pair_weight χ X Y x y →
    red_density χ X Y - α ≤ red_density χ (red_neighbors χ x ∩ X) (red_neighbors χ x ∩ Y) :=
begin
  intro h,
  conv_rhs { rw col_density_eq_sum },
  simp only [pair_weight, ←mul_sum] at h,
  rw [inv_mul_eq_div, div_le_div_right, sum_sub_distrib, sum_const, nsmul_eq_mul,
    le_sub_iff_add_le', mul_left_comm, ←add_mul, ←sub_eq_add_neg, ←le_div_iff] at h,
  { refine h.trans_eq _,
    congr' with i : 2,
    rw [inter_left_comm, inter_assoc] },
  { positivity },
  rw [nat.cast_pos, card_pos],
  exact hxY.mono (inter_subset_right _ _),
end

local notation `NB` := blue_neighbors χ
local notation `NR` := red_neighbors χ

lemma five_one_case_b_aux {α : ℝ} (X Y : finset V) {x : V} (hx : x ∈ X)
  (hy : Y.nonempty)
  (h : ∑ y in NR x ∩ X, pair_weight χ X Y x y <
    - α * ((NR x ∩ X).card * (NR x ∩ Y).card) / Y.card) :
  red_density χ X Y * ((NB x ∩ X).card * (NR x ∩ Y).card) +
    α * ((NR x ∩ X).card * (NR x ∩ Y).card) + weight χ X Y x * Y.card ≤
    ∑ y in NB x ∩ X, (NR y ∩ (NR x ∩ Y)).card :=
begin
  have : weight χ X Y x + α * ((NR x ∩ X).card * (NR x ∩ Y).card) / Y.card
    ≤ ∑ y in NB x ∩ X, pair_weight χ X Y x y,
  { rw [←le_sub_iff_add_le, sub_eq_add_neg, ←sub_le_iff_le_add', ←neg_div, ←neg_mul],
    refine h.le.trans_eq' _,
    rw [red_neighbors_inter_eq hx, sub_eq_iff_eq_add, insert_eq, sdiff_union_distrib,
      sdiff_singleton_eq_erase, inter_sdiff, (inter_eq_left_iff_subset _ _).2 (erase_subset _ _),
      ←sum_union, sdiff_union_of_subset, weight],
    { rw subset_erase,
      exact ⟨inter_subset_right _ _, by simp [not_mem_col_neighbors]⟩ },
    exact disjoint_sdiff_self_left },
  simp only [pair_weight, ←mul_sum] at this,
  rw [inv_mul_eq_div, le_div_iff, sum_sub_distrib, sum_const, add_mul, div_mul_cancel,
    nsmul_eq_mul, le_sub_iff_add_le', mul_left_comm _ (col_density χ 0 X Y), ←add_assoc,
    add_right_comm] at this,
  { refine this.trans_eq (sum_congr rfl _),
    intros y hy,
    rw [inter_left_comm, inter_assoc] },
  positivity,
  positivity,
end

lemma five_one_case_b_end (m : ℕ) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → k ^ m ≤ ramsey_number ![k, ⌈(l : ℝ) ^ (3 / 4 : ℝ)⌉₊] :=
begin
  obtain ⟨c, hc, hf⟩ := five_six_aux_part_one,
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h34 : (0 : ℝ) < 3 / 4, { norm_num },
  filter_upwards [hf, top_adjuster (t.eventually_ge_at_top 1),
      ((tendsto_rpow_at_top h34).comp t).eventually_ge_at_top (m / c)]
      with l hl hk₀ hl₁ k hlk,
  specialize hk₀ k hlk,
  rw div_le_iff' hc at hl₁,
  rw [←@nat.cast_le ℝ, nat.cast_pow, ←rpow_nat_cast],
  refine (hl k hlk).trans' _,
  rw [rpow_def_of_pos, exp_le_exp, mul_comm],
  { exact mul_le_mul_of_nonneg_right hl₁ (log_nonneg hk₀) },
  linarith only [hk₀]
end

lemma five_one_case_b (p₀l : ℝ) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k →
  ∀ μ : ℝ,
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  let C := algorithm μ k l ini i in
  ∑ y in red_neighbors χ (get_x hi) ∩ C.X,
    pair_weight χ C.X C.Y (get_x hi) y <
    - α_function k (height k ini.p C.p) *
      ((red_neighbors χ (get_x hi) ∩ C.X).card *
       (red_neighbors χ (get_x hi) ∩ C.Y).card) / C.Y.card →
  C.p * (blue_X_ratio μ k l ini i) * (C.X.card * (red_neighbors χ (get_x hi) ∩ C.Y).card) +
    α_function k (height k ini.p C.p) * (1 - blue_X_ratio μ k l ini i) *
      (C.X.card * (red_neighbors χ (get_x hi) ∩ C.Y).card) -
      3 / k ^ 4 * (C.X.card * (red_neighbors χ (get_x hi) ∩ C.Y).card)  ≤
    ∑ y in blue_neighbors χ (get_x hi) ∩ C.X,
      (red_neighbors χ y ∩ (red_neighbors χ (get_x hi) ∩ C.Y)).card :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually_gt_at_top (0 : ℝ)),
    five_eight_weaker' p₀l hp₀l,
    five_four,
    five_one_case_b_end 4,
    eventually_ge_at_top (2 ^ 4)] with l hl hk₀ h₅₈ h₅₄ hk₄ hl₄
    k hlk μ n χ ini hini i hi h,
  specialize hl k hlk,
  let C := algorithm μ k l ini i,
  let x := get_x hi,
  let β := blue_X_ratio μ k l ini i,
  let α := α_function k (height k ini.p C.p),
  have hx : x ∈ C.X := book_config.get_central_vertex_mem_X _ _ _,
  specialize h₅₈ k hlk μ n χ ini hini i x hi hx,
  have hi' := hi,
  rw [red_or_density_steps, mem_filter, mem_range] at hi',
  have hβ := blue_X_ratio_prop hi,
  have hβ' := card_red_neighbors_inter hi,
  refine (five_one_case_b_aux C.X C.Y hx (Y_nonempty hi'.1) h).trans' _,
  change _ ≤ C.p * ((blue_neighbors χ x ∩ C.X).card * (red_neighbors χ x ∩ C.Y).card) +
    α * ((red_neighbors χ x ∩ C.X).card * (red_neighbors χ x ∩ C.Y).card) +
      weight χ C.X C.Y x * C.Y.card,
  rw [←hβ, hβ', mul_assoc, mul_assoc, sub_one_mul, mul_sub, sub_eq_add_neg (_ * _),
    sub_eq_add_neg _ (_ / _ * _)],
  simp only [←mul_assoc, add_assoc],
  rw [add_le_add_iff_left, add_le_add_iff_left],
  have hp₀ : (1 : ℝ) / k ≤ ini.p,
  { refine hini.trans' _,
    rw [one_div],
    exact inv_le_of_inv_le hp₀l hl },
  have : (C.Y.card : ℝ) ≤ k * (2 * ((red_neighbors χ x ∩ C.Y).card)),
  { rw [mul_left_comm, ←mul_assoc, ←div_le_iff', div_eq_mul_one_div, mul_comm],
    { exact h₅₈ },
    refine mul_pos _ (hk₀ k hlk),
    exact two_pos },
  have : - ((2 : ℝ) / k ^ 4) * (C.X.card * (red_neighbors χ x ∩ C.Y).card) ≤
    weight χ C.X C.Y x * C.Y.card,
  { refine (mul_le_mul_of_nonneg_right (h₅₄ k hlk μ n χ ini i hi) (nat.cast_nonneg _)).trans' _,
    rw [neg_mul, neg_div, neg_mul, neg_le_neg_iff],
    refine (mul_le_mul_of_nonneg_left this (div_nonneg (nat.cast_nonneg _)
      (pow_nonneg (nat.cast_nonneg _) _))).trans_eq _,
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_left_comm, pow_succ,
      mul_div_mul_left _ _ (hk₀ k hlk).ne', mul_left_comm] },
  refine (add_le_add_left this _).trans' _,
  rw [neg_mul, ←neg_add, neg_le_neg_iff, ←mul_assoc, ←add_mul],
  refine (mul_le_mul_of_nonneg_right _ (nat.cast_nonneg _)),
  rw [←le_sub_iff_add_le, ←sub_mul, div_sub_div_same, bit1, add_sub_cancel'],
  refine (α_le_one col_density_le_one hp₀ (hl₄.trans hlk) (col_density_le_one.trans
    one_le_two)).trans _,
  rw [mul_comm, mul_one_div, one_le_div],
  swap,
  { exact pow_pos (hk₀ k hlk) _ },
  rw [←nat.cast_pow, nat.cast_le],
  exact (hk₄ k hlk).trans (ramsey_number_lt_of_lt_final_step hi'.1).le,
end

lemma blue_X_ratio_le_one {μ : ℝ} : blue_X_ratio μ k l ini i ≤ 1 :=
begin
  rw [blue_X_ratio],
  split_ifs,
  swap,
  { exact zero_le_one },
  refine div_le_one_of_le _ (nat.cast_nonneg _),
  exact nat.cast_le.2 (card_le_of_subset (inter_subset_right _ _)),
end

lemma five_one_case_b_later (μ₁ : ℝ) (p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ, ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ, p₀l ≤ ini.p → ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  let C := algorithm μ k l ini i in
  ∑ y in red_neighbors χ (get_x hi) ∩ C.X,
    pair_weight χ C.X C.Y (get_x hi) y <
    - α_function k (height k ini.p C.p) *
      ((red_neighbors χ (get_x hi) ∩ C.X).card *
       (red_neighbors χ (get_x hi) ∩ C.Y).card) / C.Y.card →
  C.p * blue_X_ratio μ k l ini i * (C.X.card * (red_neighbors χ (get_x hi) ∩ C.Y).card) +
    α_function k (height k ini.p C.p) * (1 - blue_X_ratio μ k l ini i) * (1 - k ^ (- 1 / 4 : ℝ)) *
      (C.X.card * (red_neighbors χ (get_x hi) ∩ C.Y).card) ≤
    ∑ y in blue_neighbors χ (get_x hi) ∩ C.X,
      (red_neighbors χ y ∩ (red_neighbors χ (get_x hi) ∩ C.Y)).card :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h4 : (0 : ℝ) < ((-1) / 4 + ((-1) / 4 - 1) + 4), { norm_num },
  have := ((tendsto_rpow_at_top h4).comp t).eventually_ge_at_top (3 / (1 - μ₁)),
  filter_upwards [five_one_case_b p₀l hp₀l,
    top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster this] with l hl hk₀ hl'
    k hlk μ hμu n χ ini hini i hi h,
  refine (hl k hlk μ n χ ini hini i hi h).trans' _,
  clear hl,
  specialize hk₀ k hlk,
  rw [add_sub_assoc, add_le_add_iff_left, ←sub_mul],
  refine mul_le_mul_of_nonneg_right _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  rw [mul_one_sub, sub_le_sub_iff_left, mul_assoc],
  refine (mul_le_mul_of_nonneg_right five_seven_left _).trans' _,
  { exact mul_nonneg (sub_nonneg_of_le blue_X_ratio_le_one)
      (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) },
  rw [←rpow_sub_one hk₀.ne', mul_comm, mul_assoc, ←rpow_add hk₀, ←rpow_nat_cast, nat.cast_bit0,
    nat.cast_bit0, nat.cast_one, div_le_iff (rpow_pos_of_pos hk₀ _), mul_assoc, ←rpow_add hk₀],
  have : 1 - μ ≤ 1 - blue_X_ratio μ k l ini i,
  { exact sub_le_sub_left (blue_X_ratio_le_mu hi) _ },
  refine (mul_le_mul_of_nonneg_right this (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)).trans' _,
  rw ←div_le_iff' (sub_pos_of_lt (hμ₁.trans_le' hμu)),
  exact (hl' k hlk).trans' (div_le_div_of_le_left (by norm_num1) (sub_pos_of_lt hμ₁)
    (sub_le_sub_left hμu _)),
end

lemma α_pos (k h : ℕ) (hk : 0 < k) : 0 < α_function k h :=
begin
  have hk' : (0 : ℝ) < k := nat.cast_pos.2 hk,
  refine div_pos (mul_pos (rpow_pos_of_pos hk' _) _) hk',
  exact pow_pos (add_pos_of_nonneg_of_pos zero_le_one (rpow_pos_of_pos hk' _)) _,
end

lemma α_nonneg (k h : ℕ) : 0 ≤ α_function k h :=
div_nonneg (mul_nonneg (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _) (pow_nonneg (add_nonneg
  zero_le_one (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _)) _)) (nat.cast_nonneg _)

lemma five_one_case_b_condition (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ → ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2), ∀ ini : book_config χ, p₀l ≤ ini.p → ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  let C := algorithm μ k l ini i in
  ∑ y in red_neighbors χ (get_x hi) ∩ C.X,
    pair_weight χ C.X C.Y (get_x hi) y <
    - α_function k (height k ini.p C.p) *
      ((red_neighbors χ (get_x hi) ∩ C.X).card *
       (red_neighbors χ (get_x hi) ∩ C.Y).card) / C.Y.card →
  (blue_neighbors χ (get_x hi) ∩ C.X).nonempty :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [five_one_case_b_later μ₁ p₀l hμ₁ hp₀l,
    top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    eventually_gt_at_top 1,
    top_adjuster (t.eventually_gt_at_top (1 : ℝ)),
    top_adjuster ε_lt_one] with l hl hl' hl₁ hk₁ hε
    k hlk μ hμu n χ ini hini i hi h,
  specialize hl k hlk μ hμu n χ ini hini i hi h,
  specialize hk₁ k hlk,
  refine nonempty_of_ne_empty _,
  intro hXB,
  have hβ : blue_X_ratio μ k l ini i = 0,
  { rw [blue_X_ratio_eq hi, hXB, card_empty, nat.cast_zero, zero_div] },
  rw [hXB, hβ, sum_empty, mul_zero, zero_mul, zero_add, sub_zero, mul_one] at hl,
  have hp₀ : (1 : ℝ) / k ≤ ini.p,
  { refine hini.trans' _,
    rw [one_div],
    exact inv_le_of_inv_le hp₀l (hl' k hlk) },
  refine hl.not_lt _,
  refine mul_pos _ _,
  swap,
  { rw [←nat.cast_mul, nat.cast_pos, pos_iff_ne_zero, mul_ne_zero_iff, ←pos_iff_ne_zero,
      ←pos_iff_ne_zero, card_pos, card_pos],
    refine ⟨X_nonempty _, _⟩,
    { rw [red_or_density_steps, mem_filter, mem_range] at hi,
      exact hi.1 },
    exact red_neighbors_Y_nonempty' hp₀ (hl₁.trans_le hlk) hi _
      (book_config.get_central_vertex_mem_X _ _ _) },
  have hk₀ : (0 : ℝ) < k,
  { exact hk₁.trans_le' zero_le_one },
  refine mul_pos _ _,
  { exact α_pos _ _ (nat.cast_pos.1 hk₀) },
  refine sub_pos_of_lt _,
  exact hε k hlk,
end

lemma five_one (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  ∀ hi : i ∈ red_or_density_steps μ k l ini,
  let C := algorithm μ k l ini i in
    C.p - α_function k (height k ini.p C.p) ≤
      red_density χ (red_neighbors χ (get_x hi) ∩ C.X)
                    (red_neighbors χ (get_x hi) ∩ C.Y) ∨
    (0 < blue_X_ratio μ k l ini i ∧ (algorithm μ k l ini i).p +
      (1 - k ^ (- 1 / 4 : ℝ)) *
        ((1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i) *
          α_function k (height k ini.p C.p) ≤
      red_density χ (blue_neighbors χ (get_x hi) ∩ C.X)
                    (red_neighbors χ (get_x hi) ∩ C.Y)) :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  filter_upwards [top_adjuster (t.eventually_ge_at_top p₀l⁻¹),
    top_adjuster (t.eventually_ge_at_top (1 - μ₁)⁻¹),
    eventually_gt_at_top 1,
    five_one_case_b_later μ₁ p₀l hμ₁ hp₀l,
    five_one_case_b_condition μ₁ p₀l hμ₁ hp₀l] with l hkp hkμ hl₁ h₁ h₂
    k hlk μ hμu n χ ini hini i hi,
  let C := algorithm μ k l ini i,
  let α := α_function k (height k ini.p C.p),
  let x := get_x hi,
  let β := blue_X_ratio μ k l ini i,
  let ε : ℝ := k ^ (- 1 / 4 : ℝ),
  let Yr := red_neighbors χ x ∩ C.Y,
  change C.p - α ≤ red_density χ (red_neighbors χ x ∩ C.X) Yr ∨
         (0 < β ∧ C.p + (1 - ε) * ((1 - β) / β) * α ≤
          red_density χ (blue_neighbors χ x ∩ C.X) Yr),
  have hp₀ : (1 : ℝ) / k ≤ ini.p,
  { refine hini.trans' _,
    rw [one_div],
    exact inv_le_of_inv_le hp₀l (hkp k hlk) },
  have hYr : Yr.nonempty := red_neighbors_Y_nonempty' hp₀ (hl₁.trans_le hlk) hi _
    (book_config.get_central_vertex_mem_X _ _ _),
  have hX : C.X.nonempty,
  { refine X_nonempty _,
    rw [red_or_density_steps, mem_filter, mem_range] at hi,
    exact hi.1 },
  cases le_or_lt (-α * ((red_neighbors χ x ∩ C.X).card * Yr.card) / C.Y.card)
    (∑ y in red_neighbors χ x ∩ C.X, pair_weight χ C.X C.Y x y) with hα hα,
  { exact or.inl (five_one_case_a _ _ (red_neighbors_X_nonempty hμ₁ hμu (hkμ k hlk) hl₁ hi)
      hYr hα) },
  replace h₁ : C.p * β * (C.X.card * Yr.card) + α * (1 - β) * (1 - ε) * (C.X.card * Yr.card) ≤
    ∑ y in blue_neighbors χ x ∩ C.X, (red_neighbors χ y ∩ Yr).card :=
    h₁ k hlk μ hμu n χ ini hini i hi hα,
  replace h₂ : (blue_neighbors χ x ∩ C.X).nonempty := h₂ k hlk μ hμu n χ ini hini i hi hα,
  right,
  have hβ : 0 < β,
  { change 0 < blue_X_ratio _ _ _ _ _,
    rw [blue_X_ratio_eq hi],
    exact div_pos (nat.cast_pos.2 (card_pos.2 h₂)) (nat.cast_pos.2 (card_pos.2 hX)), },
  refine ⟨hβ, _⟩,
  rw [col_density_eq_sum, le_div_iff, ←blue_X_ratio_prop hi, add_mul],
  swap,
  { rw [←nat.cast_mul, ←card_product, nat.cast_pos, card_pos, nonempty_product],
    exact ⟨h₂, hYr⟩ },
  refine h₁.trans' _,
  rw [mul_assoc, ←mul_assoc, add_le_add_iff_left, ←mul_assoc],
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  rw [mul_div_assoc', div_mul_eq_mul_div, div_mul_cancel _ hβ.ne'],
  refine le_of_eq _,
  rw [mul_right_comm, mul_rotate],
end

lemma five_two (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  i ∈ density_steps μ k l ini →
  0 < blue_X_ratio μ k l ini i ∧
  (1 - (k : ℝ) ^ (- 1 / 4 : ℝ)) * ((1 - blue_X_ratio μ k l ini i) / blue_X_ratio μ k l ini i) *
    α_function k (height k ini.p (algorithm μ k l ini i).p) ≤
      (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p :=
begin
  filter_upwards [five_one μ₁ p₀l hμ₁ hp₀l] with l hl
    k hlk μ hμu n χ ini hini i hi,
  have hi' := hi,
  simp only [density_steps, mem_image, subtype.coe_mk, mem_filter, mem_attach, true_and,
    exists_prop, subtype.exists, exists_and_distrib_right, exists_eq_right] at hi',
  obtain ⟨hi'', hhi''⟩ := hi',
  obtain ⟨hβ', h⟩ := (hl k hlk μ hμu n χ ini hini i hi'').resolve_left hhi''.not_le,
  refine ⟨hβ', _⟩,
  rw [le_sub_iff_add_le'],
  refine h.trans _,
  rw [density_applied hi],
  refl,
end

lemma blue_X_ratio_pos (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
  i ∈ density_steps μ k l ini → 0 < blue_X_ratio μ k l ini i :=
begin
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l] with l hl k hlk μ hμu n χ ini hini i hi,
  exact (hl k hlk μ hμu n χ ini hini i hi).1,
end

lemma five_three_left (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
    i ∈ density_steps μ k l ini →
  (algorithm μ k l ini i).p ≤ (algorithm μ k l ini (i + 1)).p :=
begin
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l,
    top_adjuster ε_lt_one] with l hl hε
    k hlk μ hμu n χ ini hini i hi,
  rw ←sub_nonneg,
  refine (hl _ hlk _ hμu _ _ _ hini _ hi).2.trans' _,
  refine mul_nonneg (mul_nonneg (sub_pos_of_lt (hε k hlk)).le (div_nonneg (sub_nonneg_of_le _)
    blue_X_ratio_nonneg)) (α_nonneg _ _),
  exact blue_X_ratio_le_one,
end

lemma five_three_right (μ₁ p₀l : ℝ) (hμ₁ : μ₁ < 1) (hp₀l : 0 < p₀l) :
  ∀ᶠ l : ℕ in at_top,
  ∀ k, l ≤ k → ∀ μ, μ ≤ μ₁ →
  ∀ n : ℕ,
  ∀ χ : top_edge_labelling (fin n) (fin 2),
  ∀ ini : book_config χ,
    p₀l ≤ ini.p →
  ∀ i : ℕ,
    i ∈ density_steps μ k l ini →
  (1 : ℝ) / k ^ 2 ≤ blue_X_ratio μ k l ini i :=
begin
  have t : tendsto (coe : ℕ → ℝ) at_top at_top := tendsto_coe_nat_at_top_at_top,
  have h54 := tendsto_rpow_at_top (show (0 : ℝ) < 5 / 4, by norm_num),
  have h34 := tendsto_rpow_at_top (show (0 : ℝ) < 3 / 4, by norm_num),
  have h := (tendsto_at_top_add_const_right _ (-2) h34).at_top_mul_at_top h54,
  have := tendsto_rpow_neg_at_top (show (0 : ℝ) < 1 / 4, by norm_num),
  have := eventually_le_of_tendsto_lt (show (0 : ℝ) < 1 - 2⁻¹, by norm_num) this,
  filter_upwards [five_two μ₁ p₀l hμ₁ hp₀l,
    top_adjuster (t.eventually this),
    top_adjuster (t.eventually_gt_at_top 0),
    top_adjuster ((h.comp t).eventually_ge_at_top 1)] with l hl hl' hk₀ hk'
    k hlk μ hμu n χ ini hini i hi,
  specialize hk₀ k hlk,
  obtain ⟨hβ, h⟩ := hl k hlk μ hμu n χ ini hini i hi,
  have : (algorithm μ k l ini (i + 1)).p - (algorithm μ k l ini i).p ≤ 1,
  { exact (sub_le_self _ (col_density_nonneg)).trans col_density_le_one },
  replace h := h.trans this,
  rw mul_right_comm at h,
  have : (1 : ℝ) / 2 ≤ 1 - k ^ (- 1 / 4 : ℝ),
  { rw [le_sub_comm, one_div, neg_div],
    exact hl' k hlk },
  have : (1 : ℝ) / (2 * k ^ (5 / 4 : ℝ)) ≤
    (1 - k ^ (- 1 / 4 : ℝ)) * α_function k (height k ini.p (algorithm μ k l ini i).p),
  { rw [one_div, mul_inv, ←one_div],
    refine mul_le_mul this _ (inv_nonneg.2 (rpow_nonneg_of_nonneg (nat.cast_nonneg _) _))
      (this.trans' (by norm_num1)),
    rw [←rpow_neg (nat.cast_nonneg k)],
    refine five_seven_left.trans_eq' _,
    rw ←rpow_sub_one,
    { norm_num },
    exact hk₀.ne' },
  replace h := (mul_le_mul_of_nonneg_right this _).trans h,
  swap,
  { refine div_nonneg (sub_nonneg_of_le _) blue_X_ratio_nonneg,
    exact blue_X_ratio_le_one },
  rw [mul_comm, mul_one_div, sub_div, div_self hβ.ne', div_le_iff, one_mul, sub_le_iff_le_add] at h,
  swap,
  { exact mul_pos two_pos (rpow_pos_of_pos hk₀ _) },
  rw one_div,
  refine inv_le_of_inv_le hβ _,
  rw ←one_div,
  refine h.trans _,
  rw [←le_sub_iff_add_le'],
  refine (hk' k hlk).trans_eq _,
  dsimp,
  rw [←sub_eq_add_neg, sub_mul, sub_left_inj, ←rpow_nat_cast, ←rpow_add'],
  { norm_num1,
    refl },
  { exact nat.cast_nonneg _},
  norm_num1
end

end simple_graph
