namespace DiscreteAlgebra

private theorem mul_left_cancel_pos {k a b : Nat} (hk : 0 < k) (h : k * a = k * b) :
    a = b := by
  have hstep : ∀ x y : Nat, x < y → k * x < k * y := by
    intro x y hxy
    have hsub : y = x + (y - x - 1 + 1) := by omega
    rw [hsub, Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    have hlt' := hstep a b hlt
    omega
  | inr hge =>
    cases Nat.lt_or_ge b a with
    | inl hgt =>
      have hgt' := hstep b a hgt
      omega
    | inr hle => omega

private theorem dvd_antisymm {a b : Nat} (hab : a ∣ b) (hba : b ∣ a) : a = b := by
  cases hab with
  | intro x hx =>
    cases hba with
    | intro y hy =>
      cases Nat.lt_or_ge x 2 with
      | inl hxlt =>
        have hx01 : x = 0 ∨ x = 1 := by omega
        cases hx01 with
        | inl hx0 =>
          rw [hx0, Nat.mul_zero] at hx
          rw [hx, Nat.zero_mul] at hy
          omega
        | inr hx1 =>
          rw [hx1, Nat.mul_one] at hx
          omega
      | inr hxge =>
        cases Nat.eq_zero_or_pos y with
        | inl hy0 =>
          rw [hy0, Nat.mul_zero] at hy
          rw [hy, Nat.zero_mul] at hx
          omega
        | inr hypos =>
          have hx2 : x = (x - 2) + 2 := by omega
          have hy1 : y = (y - 1) + 1 := by omega
          have h1 : 2 * a ≤ b := by
            rw [hx, hx2, Nat.mul_add]
            omega
          have h2 : b ≤ a := by
            rw [hy, hy1, Nat.mul_add, Nat.mul_one]
            omega
          have ha0 : a = 0 := by omega
          rw [ha0, Nat.zero_mul] at hx
          omega

/-- Divisibility is preserved under natural-number linear combinations. -/
theorem dvd_linear_comb {d a b : Nat} (x y : Nat) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ x * a + y * b := by
  cases ha with
  | intro u hu =>
    cases hb with
    | intro v hv =>
      refine ⟨x * u + y * v, ?_⟩
      rw [hu, hv, Nat.mul_add, Nat.mul_left_comm d x u, Nat.mul_left_comm d y v]

/-- If `d` divides both `a` and `b` with `b ≤ a`, then `d` divides `a - b`. -/
theorem dvd_sub_of_dvd {d a b : Nat} (hle : b ≤ a) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ a - b := by
  cases ha with
  | intro u hu =>
    cases hb with
    | intro v hv =>
      cases Nat.eq_zero_or_pos d with
      | inl hd0 =>
        subst hd0
        simp only [Nat.zero_mul] at hu hv
        refine ⟨0, ?_⟩
        omega
      | inr hdpos =>
        have hvu : v ≤ u := by
          cases Nat.lt_or_ge u v with
          | inr h => exact h
          | inl hlt =>
            have hsub : v = u + (v - u - 1 + 1) := by omega
            have hgt : d * u < d * v := by
              rw [hsub, Nat.mul_add, Nat.mul_add, Nat.mul_one]
              omega
            omega
        refine ⟨u - v, ?_⟩
        have hmul : d * ((u - v) + v) = d * (u - v) + d * v := Nat.mul_add d (u - v) v
        have hsum : (u - v) + v = u := by omega
        rw [hsum] at hmul
        omega

/-- Divisibility invariance under Euclidean remainder: if `d ∣ b`, then `d ∣ a ↔ d ∣ a % b`. -/
theorem dvd_iff_dvd_mod {d a b : Nat} (hb : d ∣ b) : d ∣ a ↔ d ∣ a % b := by
  have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hqb : d ∣ b * (a / b) := by
    cases hb with
    | intro k hk =>
      refine ⟨k * (a / b), ?_⟩
      rw [hk, Nat.mul_assoc]
  constructor
  · intro ha
    have hle : b * (a / b) ≤ a := by omega
    have hsub : a % b = a - b * (a / b) := by omega
    rw [hsub]
    exact dvd_sub_of_dvd hle ha hqb
  · intro hmod
    have hsum : d ∣ 1 * (b * (a / b)) + 1 * (a % b) := dvd_linear_comb 1 1 hqb hmod
    have heq : 1 * (b * (a / b)) + 1 * (a % b) = a := by omega
    rw [heq] at hsum
    exact hsum

/-- Euclidean algorithm reduction invariance: `gcd a b = gcd b (a % b)`. -/
theorem gcd_step (a b : Nat) : Nat.gcd a b = Nat.gcd b (a % b) := by
  apply dvd_antisymm
  · apply Nat.dvd_gcd
    · exact Nat.gcd_dvd_right a b
    · exact (dvd_iff_dvd_mod (Nat.gcd_dvd_right a b)).mp (Nat.gcd_dvd_left a b)
  · apply Nat.dvd_gcd
    · exact (dvd_iff_dvd_mod (Nat.gcd_dvd_left b (a % b))).mpr (Nat.gcd_dvd_right b (a % b))
    · exact Nat.gcd_dvd_left b (a % b)

/-- Homogeneity of GCD under positive and zero scaling: `gcd (k * a) (k * b) = k * gcd a b`. -/
theorem gcd_mul_left (k a b : Nat) : Nat.gcd (k * a) (k * b) = k * Nat.gcd a b := by
  cases Nat.eq_zero_or_pos k with
  | inl hk0 =>
    subst hk0
    simp
  | inr hk =>
    apply dvd_antisymm
    · have hdvd_k : k ∣ Nat.gcd (k * a) (k * b) := by
        apply Nat.dvd_gcd
        · exact ⟨a, rfl⟩
        · exact ⟨b, rfl⟩
      cases hdvd_k with
      | intro q hq =>
        have hqa : q ∣ a := by
          have h1 : k * q ∣ k * a := by
            rw [← hq]
            exact Nat.gcd_dvd_left (k * a) (k * b)
          cases h1 with
          | intro u hu =>
            refine ⟨u, ?_⟩
            apply mul_left_cancel_pos hk
            rw [hu, Nat.mul_assoc]
        have hqb : q ∣ b := by
          have h2 : k * q ∣ k * b := by
            rw [← hq]
            exact Nat.gcd_dvd_right (k * a) (k * b)
          cases h2 with
          | intro v hv =>
            refine ⟨v, ?_⟩
            apply mul_left_cancel_pos hk
            rw [hv, Nat.mul_assoc]
        have hqg : q ∣ Nat.gcd a b := Nat.dvd_gcd hqa hqb
        cases hqg with
        | intro w hw =>
          refine ⟨w, ?_⟩
          rw [hq, hw, Nat.mul_assoc]
    · apply Nat.dvd_gcd
      · cases Nat.gcd_dvd_left a b with
        | intro u hu =>
          refine ⟨u, ?_⟩
          rw [Nat.mul_assoc, ← hu]
      · cases Nat.gcd_dvd_right a b with
        | intro v hv =>
          refine ⟨v, ?_⟩
          rw [Nat.mul_assoc, ← hv]

end DiscreteAlgebra
