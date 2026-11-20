import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Archimedes–Richardson Exhaustion-Extrapolation Method (AREEM-8) Formalization

本模組針對阿基米德–理查森窮竭外推法（AREEM）進行形式化驗證，包含：
1. 內接與外切正 $N$ 邊形逼近 $\pi_{in}(N), \pi_{out}(N)$ 及各階外推格式 $S, R^{(1)}, R^{(2)}$ 之定義。
2. 嚴格夾擠不等式 $\pi_{in}(N) < \pi < \pi_{out}(N)$ 之證明。
3. 四階組合 $S(N)$ 權重 $w = 2/3$ 之唯一性與主誤差係數推導。
4. 偶次冪級數 Richardson 外推消去引理及六階、八階主誤差係數驗證。
5. $R^{(2)}(N)$ 對三角節點 $\{N, 2N, 4N\}$ 之依賴性定理（特別針對 $N = 192$）。
6. 正向誤差比 $r_X(N)$ 與反向衰減比 $\rho_X(N)$ 之漸近極限（$4, 16, 64, 256$ 與其倒數）及定量誤差界限。
7. 避免相消誤差（catastrophic cancellation）之正六邊形半角遞迴啟動演算法與等價性證明。
-/

namespace AREEM

open Real Filter Topology

noncomputable section

/-! ## 1. 基本定義（對應論文第 2 節） -/

/-- 單位圓內接正 $N$ 邊形半周長逼近：$\pi_{in}(N) = N \sin(\pi / N)$ -/
def piIn (N : ℝ) : ℝ := N * Real.sin (Real.pi / N)

/-- 單位圓外切正 $N$ 邊形半周長逼近：$\pi_{out}(N) = N \tan(\pi / N)$ -/
def piOut (N : ℝ) : ℝ := N * Real.tan (Real.pi / N)

/-- 古典算術平均格式：$\pi_E(N) = \frac{\pi_{in}(N) + \pi_{out}(N)}{2}$ -/
def piE (N : ℝ) : ℝ := (piIn N + piOut N) / 2

/-- 四階線性組合格式（Snellius–Huygens 組合）：$S(N) = \frac{2\pi_{in}(N) + \pi_{out}(N)}{3}$ -/
def S (N : ℝ) : ℝ := (2 * piIn N + piOut N) / 3

/-- 六階一次 Richardson 外推格式：$R^{(1)}(N) = \frac{16 S(2N) - S(N)}{15}$ -/
def R1 (N : ℝ) : ℝ := (16 * S (2 * N) - S N) / 15

/-- 八階二次 Richardson 外推格式：$R^{(2)}(N) = \frac{64 R^{(1)}(2N) - R^{(1)}(N)}{63}$ -/
def R2 (N : ℝ) : ℝ := (64 * R1 (2 * N) - R1 N) / 63


/-! ## 2. 嚴格夾擠定理（對應論文第 2 節與第 3 節） -/

/-- 對任意 $N \ge 6$，內接逼近嚴格小於 $\pi$：$\pi_{in}(N) < \pi$ -/
theorem piIn_lt_pi {N : ℝ} (hN : 6 ≤ N) : piIn N < Real.pi := by
  have hN_pos : 0 < N := by linarith
  have hx_pos : 0 < Real.pi / N := div_pos Real.pi_pos hN_pos
  have hsin : Real.sin (Real.pi / N) < Real.pi / N := Real.sin_lt hx_pos
  unfold piIn
  calc
    N * Real.sin (Real.pi / N) < N * (Real.pi / N) := mul_lt_mul_of_pos_left hsin hN_pos
    _ = Real.pi := by field_simp

/-- 對任意 $N \ge 6$，外切逼近嚴格大於 $\pi$：$\pi < \pi_{out}(N)$ -/
theorem pi_lt_piOut {N : ℝ} (hN : 6 ≤ N) : Real.pi < piOut N := by
  have hN_pos : 0 < N := by linarith
  have hx_pos : 0 < Real.pi / N := div_pos Real.pi_pos hN_pos
  have hx_lt_half_pi : Real.pi / N < Real.pi / 2 := by
    apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
  have htan : Real.pi / N < Real.tan (Real.pi / N) := Real.lt_tan hx_pos hx_lt_half_pi
  unfold piOut
  calc
    Real.pi = N * (Real.pi / N) := by field_simp
    _ < N * Real.tan (Real.pi / N) := mul_lt_mul_of_pos_left htan hN_pos

/-- 嚴格雙邊夾擠定理：$\pi_{in}(N) < \pi < \pi_{out}(N)$ -/
theorem strict_enclosure {N : ℝ} (hN : 6 ≤ N) : piIn N < Real.pi ∧ Real.pi < piOut N :=
  ⟨piIn_lt_pi hN, pi_lt_piOut hN⟩


/-! ## 3. 四階組合權重唯一性與係數推導（對應論文第 4 節） -/

/-- 一般仿射線性組合 $T_w(N) = w \pi_{in}(N) + (1 - w) \pi_{out}(N)$ -/
def affineComb (w : ℝ) (inVal outVal : ℝ) : ℝ := w * inVal + (1 - w) * outVal

/-- $S(N)$ 為權重 $w = 2/3$ 之仿射組合 -/
theorem S_eq_affineComb (N : ℝ) : S N = affineComb (2 / 3) (piIn N) (piOut N) := by
  unfold S affineComb
  ring

/-- 權重唯一性定理：消去 $N^{-2}$ 主誤差項 $\pi^3 \left(\frac{1}{3} - \frac{w}{2}\right) = 0$ 當且僅當 $w = \frac{2}{3}$ -/
theorem unique_fourth_order_weight (w : ℝ) :
    w * (-Real.pi ^ 3 / 6) + (1 - w) * (Real.pi ^ 3 / 3) = 0 ↔ w = 2 / 3 := by
  have hpi3 : Real.pi ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt Real.pi_pos)
  have hfactor :
      w * (-Real.pi ^ 3 / 6) + (1 - w) * (Real.pi ^ 3 / 3) = Real.pi ^ 3 * (1 / 3 - w / 2) := by
    ring
  rw [hfactor, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hpi3
    · linarith
  · intro hw
    right
    linarith

/-- 驗證 $S(N)$ 展開式中 $N^{-4}, N^{-6}, N^{-8}$ 之有理係數分別為 $1/20, 1/56, 7/960$ -/
theorem S_expansion_rational_coeffs :
    (2 * (1 / 120 : ℝ) + 1 * (2 / 15)) / 3 = 1 / 20 ∧
    (2 * (-1 / 5040 : ℝ) + 1 * (17 / 315)) / 3 = 1 / 56 ∧
    (2 * (1 / 362880 : ℝ) + 1 * (62 / 2835)) / 3 = 7 / 960 := by
  norm_num


/-! ## 4. 偶次冪 Richardson 外推引理與高階係數（對應論文第 5 節） -/

/-- 一般階數 $p$ 之 Richardson 外推算子：$T^{(1)}(N) = \frac{2^p T(2N) - T(N)}{2^p - 1}$ -/
def richardsonStep (p : ℕ) (T : ℝ → ℝ) (N : ℝ) : ℝ :=
  ((2 : ℝ) ^ p * T (2 * N) - T N) / ((2 : ℝ) ^ p - 1)

theorem R1_eq_richardsonStep (N : ℝ) : R1 N = richardsonStep 4 S N := by
  unfold R1 richardsonStep
  norm_num

theorem R2_eq_richardsonStep (N : ℝ) : R2 N = richardsonStep 6 R1 N := by
  unfold R2 richardsonStep
  norm_num

/-- **Richardson 外推消去引理（論文第 5 節）**：
    若 $T(N) = \pi + \frac{C_p}{N^p} + \frac{C_{p+2}}{N^{p+2}} + E(N)$ 且 $p \ge 1$，
    則一步 Richardson 外推完全消去 $N^{-p}$ 項，並將 $N^{-(p+2)}$ 係數轉化為
    $C_{p+2} \cdot \frac{2^{-2} - 1}{2^p - 1}$。 -/
theorem richardson_even_cancellation
    {p : ℕ} (hp : 1 ≤ p) {T E : ℝ → ℝ} {C_p C_p2 N : ℝ} (hN : N ≠ 0)
    (hT_N : T N = Real.pi + C_p / N ^ p + C_p2 / N ^ (p + 2) + E N)
    (hT_2N : T (2 * N) =
      Real.pi + C_p / (2 * N) ^ p + C_p2 / (2 * N) ^ (p + 2) + E (2 * N)) :
    richardsonStep p T N =
      Real.pi + (C_p2 * (((2 : ℝ) ^ (-2 : ℤ) - 1) / ((2 : ℝ) ^ p - 1))) / N ^ (p + 2) +
        ((2 : ℝ) ^ p * E (2 * N) - E N) / ((2 : ℝ) ^ p - 1) := by
  have h2p_gt_one : (1 : ℝ) < (2 : ℝ) ^ p := one_lt_pow₀ (by norm_num) (by omega)
  have hdenom : (2 : ℝ) ^ p - 1 ≠ 0 := by linarith
  have hNp : N ^ p ≠ 0 := pow_ne_zero p hN
  have hNp2 : N ^ (p + 2) ≠ 0 := pow_ne_zero (p + 2) hN
  unfold richardsonStep
  rw [hT_N, hT_2N]
  have hpow1 : (2 * N) ^ p = (2 : ℝ) ^ p * N ^ p := mul_pow 2 N p
  have hpow2 : (2 * N) ^ (p + 2) = (2 : ℝ) ^ p * 4 * N ^ (p + 2) := by
    calc
      (2 * N) ^ (p + 2) = (2 : ℝ) ^ (p + 2) * N ^ (p + 2) := mul_pow 2 N (p + 2)
      _ = ((2 : ℝ) ^ p * (2 : ℝ) ^ 2) * N ^ (p + 2) := by rw [pow_add]
      _ = (2 : ℝ) ^ p * 4 * N ^ (p + 2) := by norm_num
  rw [hpow1, hpow2]
  have h2neg2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
  rw [h2neg2]
  field_simp [hdenom, hNp, hNp2]
  ring

/-- 驗證六階格式 $R^{(1)}(N)$ 與八階格式 $R^{(2)}(N)$ 之主誤差有理係數：
    $-1/1120$ 與 $+1/184320$ -/
theorem high_order_leading_coeffs :
    (1 / 56 : ℝ) * (((2 : ℝ) ^ (-2 : ℤ) - 1) / ((2 : ℝ) ^ 4 - 1)) = -1 / 1120 ∧
    (-7 / 15360 : ℝ) * (((2 : ℝ) ^ (-2 : ℤ) - 1) / ((2 : ℝ) ^ 6 - 1)) = 1 / 184320 := by
  norm_num


/-! ## 5. 節點域必要性定理（對應論文第 2 節與第 12.2 節） -/

/-- **節點域展開定理**：$R^{(2)}(N)$ 等價於 $\{S(N), S(2N), S(4N)\}$ 之精確線性組合 -/
theorem R2_node_expansion (N : ℝ) :
    R2 N = (1024 * S (4 * N) - 80 * S (2 * N) + S N) / 945 := by
  unfold R2 R1
  have h2 : 2 * (2 * N) = 4 * N := by ring
  rw [h2]
  ring

/-- 推論：$R^{(2)}(192)$ 依賴於節點 $\{192, 384, 768\}$ -/
theorem R2_192_nodes :
    R2 192 = (1024 * S 768 - 80 * S 384 + S 192) / 945 := by
  have h := R2_node_expansion 192
  norm_num at h
  exact h


/-! ## 6. 誤差比值漸近極限與定量誤差界限（對應論文第 6 節） -/

/-- 正向誤差比：$r_X(N) = \frac{|X(N) - \pi|}{|X(2N) - \pi|}$ -/
def forwardRatio (X : ℝ → ℝ) (N : ℝ) : ℝ :=
  |X N - Real.pi| / |X (2 * N) - Real.pi|

/-- 反向衰減比：$\rho_X(N) = \frac{|X(2N) - \pi|}{|X(N) - \pi|}$ -/
def reverseRatio (X : ℝ → ℝ) (N : ℝ) : ℝ :=
  |X (2 * N) - Real.pi| / |X N - Real.pi|

theorem reverseRatio_eq_inv_forwardRatio (X : ℝ → ℝ) (N : ℝ) :
    reverseRatio X N = (forwardRatio X N)⁻¹ := by
  unfold reverseRatio forwardRatio
  rw [inv_div]

/-- **誤差比值極限定理（論文第 6 節）**：
    若 $X(N) - \pi = \frac{C}{N^p} + r(N)$，其中 $C \ne 0$ 且 $r(N) \cdot N^p \to 0$（當 $N \to \infty$），
    則正向誤差比 $\lim_{N \to \infty} r_X(N) = 2^p$（對應階數 $2, 4, 6, 8$ 分別為 $4, 16, 64, 256$），
    且反向衰減比 $\lim_{N \to \infty} \rho_X(N) = 2^{-p}$。 -/
theorem error_ratio_limits
    {p : ℕ} {X r : ℝ → ℝ} {C : ℝ} (hC : C ≠ 0)
    (hexp : ∀ N : ℝ, X N - Real.pi = C / N ^ p + r N)
    (hr : Tendsto (fun N : ℝ => r N * N ^ p) atTop (𝓝 0)) :
    Tendsto (forwardRatio X) atTop (𝓝 ((2 : ℝ) ^ p)) ∧
    Tendsto (reverseRatio X) atTop (𝓝 (((2 : ℝ) ^ p)⁻¹)) := by
  have hscaled : Tendsto (fun N : ℝ => (X N - Real.pi) * N ^ p) atTop (𝓝 C) := by
    have h1 : Tendsto (fun N : ℝ => C + r N * N ^ p) atTop (𝓝 (C + 0)) :=
      tendsto_const_nhds.add hr
    rw [add_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hNp : N ^ p ≠ 0 := pow_ne_zero p (ne_of_gt hN)
    rw [hexp N]
    field_simp [hNp]
  have h2N : Tendsto (fun N : ℝ => (2 : ℝ) * N) atTop atTop :=
    (tendsto_id : Tendsto (fun N : ℝ => N) atTop atTop).const_mul_atTop (by norm_num)
  have hscaled_2N : Tendsto (fun N : ℝ => (X (2 * N) - Real.pi) * (2 * N) ^ p) atTop (𝓝 C) :=
    hscaled.comp h2N
  have h2p_ne : (2 : ℝ) ^ p ≠ 0 := pow_ne_zero p (by norm_num)
  have hscaled_2N_div :
      Tendsto (fun N : ℝ => (X (2 * N) - Real.pi) * N ^ p) atTop (𝓝 (C / (2 : ℝ) ^ p)) := by
    have hdiv := hscaled_2N.div_const ((2 : ℝ) ^ p)
    refine hdiv.congr' ?_
    filter_upwards with N
    rw [mul_pow]
    field_simp [h2p_ne]
  have hnorm_num : Tendsto (fun N : ℝ => |(X N - Real.pi) * N ^ p|) atTop (𝓝 |C|) :=
    hscaled.abs
  have hnorm_den :
      Tendsto (fun N : ℝ => |(X (2 * N) - Real.pi) * N ^ p|) atTop (𝓝 |C / (2 : ℝ) ^ p|) :=
    hscaled_2N_div.abs
  have hden_ne : |C / (2 : ℝ) ^ p| ≠ 0 := abs_ne_zero.mpr (div_ne_zero hC h2p_ne)
  have hlim_val : |C| / |C / (2 : ℝ) ^ p| = (2 : ℝ) ^ p := by
    rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) p)]
    field_simp [abs_ne_zero.mpr hC]
  have hfwd : Tendsto (forwardRatio X) atTop (𝓝 ((2 : ℝ) ^ p)) := by
    rw [← hlim_val]
    have hquot := hnorm_num.div hnorm_den hden_ne
    refine hquot.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with N hN
    have hNp_pos : 0 < N ^ p := pow_pos hN p
    dsimp only [Pi.div_apply, forwardRatio]
    rw [abs_mul, abs_mul, abs_of_pos hNp_pos]
    exact mul_div_mul_right _ _ (ne_of_gt hNp_pos)
  have hrev : Tendsto (reverseRatio X) atTop (𝓝 (((2 : ℝ) ^ p)⁻¹)) := by
    have hinv := hfwd.inv₀ h2p_ne
    refine hinv.congr' ?_
    filter_upwards with N
    exact (reverseRatio_eq_inv_forwardRatio X N).symm
  exact ⟨hfwd, hrev⟩

/-- **定量誤差界限結構（論文第 6 節）**：
    當 $N \ge 12$ 且餘項受主項 $0.1$ 倍幾何比例控制時，建立確定性上界：
    $|R^{(2)}(N) - \pi| \le \frac{1.1 \pi^9}{184320 N^8}$。 -/
theorem R2_quantitative_bound {N : ℝ} (hN : 12 ≤ N)
    (hrem : |R2 N - Real.pi - Real.pi ^ 9 / (184320 * N ^ 8)| ≤
      0.1 * (Real.pi ^ 9 / (184320 * N ^ 8))) :
    |R2 N - Real.pi| ≤ 1.1 * Real.pi ^ 9 / (184320 * N ^ 8) := by
  have hN_pos : 0 < N := by linarith
  have hlead_nonneg : 0 ≤ Real.pi ^ 9 / (184320 * N ^ 8) := by positivity
  have htri :
      |R2 N - Real.pi| ≤
        |R2 N - Real.pi - Real.pi ^ 9 / (184320 * N ^ 8)| +
          |Real.pi ^ 9 / (184320 * N ^ 8)| := by
    have heq :
        R2 N - Real.pi =
          (R2 N - Real.pi - Real.pi ^ 9 / (184320 * N ^ 8)) +
            Real.pi ^ 9 / (184320 * N ^ 8) := by ring
    conv_lhs => rw [heq]
    exact abs_add_le _ _
  rw [abs_of_nonneg hlead_nonneg] at htri
  have hgoal_eq :
      1.1 * Real.pi ^ 9 / (184320 * N ^ 8) =
        0.1 * (Real.pi ^ 9 / (184320 * N ^ 8)) + Real.pi ^ 9 / (184320 * N ^ 8) := by ring
  rw [hgoal_eq]
  linarith


/-! ## 7. 半角遞迴與 AREEM-8 演算法（對應論文第 7 節與第 9 節） -/

/-- 數值穩定之半角遞迴算子：
    $c_{2N} = \sqrt{\frac{1 + c_N}{2}}, \quad s_{2N} = \frac{s_N}{\sqrt{2(1 + c_N)}}$ -/
def halfAngleStep (sc : ℝ × ℝ) : ℝ × ℝ :=
  (sc.1 / Real.sqrt (2 * (1 + sc.2)), Real.sqrt ((1 + sc.2) / 2))

/-- 從正六邊形精確值 $(s_6, c_6) = (1/2, \sqrt{3}/2)$ 出發之倍增序列（對應 $N = 6 \cdot 2^k$） -/
def hexagonSeq : ℕ → ℝ × ℝ
  | 0 => (1 / 2, Real.sqrt 3 / 2)
  | k + 1 => halfAngleStep (hexagonSeq k)

/-- **半角遞迴精確性定理（歸納法證明）**：
    對所有 $k \in \mathbb{N}$，`hexagonSeq k` 精確等於 $(\sin(\pi / (6 \cdot 2^k)), \cos(\pi / (6 \cdot 2^k)))$。 -/
theorem hexagonSeq_correct (k : ℕ) :
    hexagonSeq k =
      (Real.sin (Real.pi / (6 * (2 : ℝ) ^ k)), Real.cos (Real.pi / (6 * (2 : ℝ) ^ k))) := by
  induction k with
  | zero =>
    simp only [hexagonSeq, pow_zero, mul_one]
    exact Prod.ext Real.sin_pi_div_six.symm Real.cos_pi_div_six.symm
  | succ k ih =>
    simp only [hexagonSeq, ih, halfAngleStep]
    set θ : ℝ := Real.pi / (6 * (2 : ℝ) ^ (k + 1))
    have hpow_pos : (0 : ℝ) < 6 * (2 : ℝ) ^ (k + 1) := by positivity
    have hθ_pos : 0 < θ := div_pos Real.pi_pos hpow_pos
    have hθ_lt_half_pi : θ < Real.pi / 2 := by
      have hge6 : (6 : ℝ) ≤ 6 * (2 : ℝ) ^ (k + 1) := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        linarith
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
    have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθ_lt_half_pi⟩
    have htwoθ : Real.pi / (6 * (2 : ℝ) ^ k) = 2 * θ := by
      dsimp [θ]
      rw [pow_succ]
      ring
    rw [htwoθ, Real.sin_two_mul, Real.cos_two_mul]
    have h1 : (1 + (2 * Real.cos θ ^ 2 - 1)) / 2 = Real.cos θ ^ 2 := by ring
    have h2 : 2 * (1 + (2 * Real.cos θ ^ 2 - 1)) = (2 * Real.cos θ) ^ 2 := by ring
    rw [h1, h2, Real.sqrt_sq (le_of_lt hcos_pos), Real.sqrt_sq (by linarith)]
    ext
    · field_simp [ne_of_gt hcos_pos]
    · rfl

/-- 基於半角遞迴之第 $k$ 層四階近似 $S_{rec}(k)$（無需於角度中預先代入 $\pi$） -/
def S_rec (k : ℕ) : ℝ :=
  let N : ℝ := 6 * (2 : ℝ) ^ k
  let sc := hexagonSeq k
  let p_in := N * sc.1
  let p_out := N * (sc.1 / sc.2)
  (2 * p_in + p_out) / 3

/-- 完整 AREEM-8 演算法輸出（給定基準層 $k$，使用節點 $k, k+1, k+2$；當 $k = 5$ 時即為 $R^{(2)}(192)$） -/
def areem8 (k : ℕ) : ℝ :=
  let s0 := S_rec k
  let s1 := S_rec (k + 1)
  let s2 := S_rec (k + 2)
  let r1_0 := (16 * s1 - s0) / 15
  let r1_1 := (16 * s2 - s1) / 15
  (64 * r1_1 - r1_0) / 63

/-- **演算法等價性主定理**：
    透過正六邊形半角遞迴計算之 `areem8 k` 在實數域 $\mathbb{R}$ 上嚴格等於理論外推值 $R^{(2)}(6 \cdot 2^k)$。 -/
theorem areem8_eq_R2 (k : ℕ) : areem8 k = R2 (6 * (2 : ℝ) ^ k) := by
  have hS_rec : ∀ m : ℕ, S_rec m = S (6 * (2 : ℝ) ^ m) := by
    intro m
    unfold S_rec S piIn piOut
    rw [hexagonSeq_correct m, Real.tan_eq_sin_div_cos]
  unfold areem8 R2 R1
  rw [hS_rec k, hS_rec (k + 1), hS_rec (k + 2)]
  have hn1 : 2 * (6 * (2 : ℝ) ^ k) = 6 * (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
  have hn2 : 2 * (2 * (6 * (2 : ℝ) ^ k)) = 6 * (2 : ℝ) ^ (k + 2) := by
    rw [pow_succ, pow_succ]; ring
  rw [hn2, hn1]

/-- $k = 5$ 時，$6 \cdot 2^5 = 192$，`areem8 5` 精確給出 $R^{(2)}(192)$ -/
theorem areem8_5_eq_R2_192 : areem8 5 = R2 192 := by
  have h := areem8_eq_R2 5
  norm_num at h
  exact h

end

end AREEM
