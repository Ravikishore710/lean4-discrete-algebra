import DiscreteAlgebra.ModularArithmetic
import DiscreteAlgebra.BezoutAndPrimes

namespace DiscreteAlgebra

/-- Setoid induced by modular congruence modulo `m`. -/
def modSetoid (m : Nat) : Setoid Nat where
  r := ModEq m
  iseqv := ModEq.equivalence m

/-- Residue class algebra `ℤ/mℤ` constructed as the quotient of `Nat` by `ModEq m`. -/
def ZMod (m : Nat) : Type := Quotient (modSetoid m)

/-- Canonical projection from `Nat` into `ZMod m`. -/
def ZMod.mk (m : Nat) (a : Nat) : ZMod m := Quotient.mk (modSetoid m) a

/-- Well-defined addition on `ZMod m`. -/
def ZMod.add {m : Nat} : ZMod m → ZMod m → ZMod m :=
  Quotient.lift₂ (fun a b => ZMod.mk m (a + b)) fun _ _ _ _ h1 h2 =>
    Quotient.sound (ModEq.add h1 h2)

/-- Well-defined multiplication on `ZMod m`. -/
def ZMod.mul {m : Nat} : ZMod m → ZMod m → ZMod m :=
  Quotient.lift₂ (fun a b => ZMod.mk m (a * b)) fun _ _ _ _ h1 h2 =>
    Quotient.sound (ModEq.mul h1 h2)

/-- Helper counting natural numbers `k < bound` coprime to `n`. -/
def countCoprime (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => countCoprime n k + if Nat.gcd n k = 1 then 1 else 0

/-- Euler's totient function `φ(n)`: count of integers `0 ≤ k < n` with `gcd n k = 1`. -/
def totient (n : Nat) : Nat := countCoprime n n

/-- Exact bridge between quotient equality in `ZMod m` and modular congruence `ModEq m`. -/
theorem ZMod.mk_eq_iff {m a b : Nat} :
    ZMod.mk m a = ZMod.mk m b ↔ a ≡ b [MOD m] :=
  ⟨Quotient.exact, Quotient.sound⟩

/-- Left distributivity of multiplication over addition in the quotient algebra `ZMod m`. -/
theorem ZMod.mul_add {m : Nat} (x y z : ZMod m) :
    ZMod.mul x (ZMod.add y z) = ZMod.add (ZMod.mul x y) (ZMod.mul x z) := by
  refine Quotient.ind (fun a => ?_) x
  refine Quotient.ind (fun b => ?_) y
  refine Quotient.ind (fun c => ?_) z
  exact Quotient.sound (by rw [Nat.mul_add]; exact rfl)

private theorem mul_sub_nat {c a b : Nat} (hle : b ≤ a) : c * a - c * b = c * (a - b) := by
  have hmul : c * ((a - b) + b) = c * (a - b) + c * b := Nat.mul_add c (a - b) b
  have hsum : (a - b) + b = a := by omega
  rw [hsum] at hmul
  omega

private theorem mul_dvd_of_coprime {m n x : Nat}
    (hcop : Nat.gcd m n = 1) (hm : m ∣ x) (hn : n ∣ x) : m * n ∣ x := by
  cases hm with
  | intro k hk =>
    rw [hk] at hn
    have hcop' : Nat.gcd n m = 1 := by rw [Nat.gcd_comm]; exact hcop
    cases coprime_dvd_of_dvd_mul hcop' hn with
    | intro q hq =>
      refine ⟨q, ?_⟩
      rw [hk, hq, Nat.mul_assoc]

/-- Left cancellation in modular arithmetic for factors coprime to the modulus. -/
theorem ModEq.mul_left_cancel_of_coprime {m c a b : Nat}
    (hcop : Nat.gcd c m = 1) (h : c * a ≡ c * b [MOD m]) : a ≡ b [MOD m] := by
  have hcop' : Nat.gcd m c = 1 := by rw [Nat.gcd_comm]; exact hcop
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    have hle : a ≤ b := by omega
    have hle_mul : c * a ≤ c * b := Nat.mul_le_mul_left c hle
    have hdvd : m ∣ c * b - c * a := (ModEq.iff_dvd_sub hle_mul).mp h.symm
    rw [mul_sub_nat hle] at hdvd
    have hdvd' : m ∣ b - a := coprime_dvd_of_dvd_mul hcop' hdvd
    exact ((ModEq.iff_dvd_sub hle).mpr hdvd').symm
  | inr hge =>
    have hle_mul : c * b ≤ c * a := Nat.mul_le_mul_left c hge
    have hdvd : m ∣ c * a - c * b := (ModEq.iff_dvd_sub hle_mul).mp h
    rw [mul_sub_nat hge] at hdvd
    have hdvd' : m ∣ a - b := coprime_dvd_of_dvd_mul hcop' hdvd
    exact (ModEq.iff_dvd_sub hge).mpr hdvd'

/-- Combining congruences modulo coprime moduli `m` and `n` yields congruence modulo `m * n`. -/
theorem ModEq.of_coprime_mul {m n a b : Nat}
    (hcop : Nat.gcd m n = 1) (hm : a ≡ b [MOD m]) (hn : a ≡ b [MOD n]) :
    a ≡ b [MOD m * n] := by
  cases Nat.lt_or_ge a b with
  | inl hlt =>
    have hle : a ≤ b := by omega
    have hdm : m ∣ b - a := (ModEq.iff_dvd_sub hle).mp hm.symm
    have hdn : n ∣ b - a := (ModEq.iff_dvd_sub hle).mp hn.symm
    have hdmn : m * n ∣ b - a := mul_dvd_of_coprime hcop hdm hdn
    exact ((ModEq.iff_dvd_sub hle).mpr hdmn).symm
  | inr hge =>
    have hdm : m ∣ a - b := (ModEq.iff_dvd_sub hge).mp hm
    have hdn : n ∣ a - b := (ModEq.iff_dvd_sub hge).mp hn
    have hdmn : m * n ∣ a - b := mul_dvd_of_coprime hcop hdm hdn
    exact (ModEq.iff_dvd_sub hge).mpr hdmn

/-- Constructive modular inverse: if `gcd m n = 1`, there exists `k : Nat` with `k * m ≡ 1 [MOD n]`. -/
theorem exists_mod_inv {m n : Nat} (hcop : Nat.gcd m n = 1) :
    ∃ k : Nat, k * m ≡ 1 [MOD n] := by
  cases Nat.lt_or_ge n 2 with
  | inl hn2 =>
    have hn01 : n = 0 ∨ n = 1 := by omega
    cases hn01 with
    | inl hn0 =>
      subst hn0
      simp only [Nat.gcd_zero_right] at hcop
      refine ⟨1, ?_⟩
      rw [hcop]
      rfl
    | inr hn1 =>
      subst hn1
      refine ⟨0, ?_⟩
      rfl
  | inr hn2 =>
    have hmpos : 1 ≤ m := by
      cases Nat.eq_zero_or_pos m with
      | inl hm0 =>
        subst hm0
        simp only [Nat.gcd_zero_left] at hcop
        omega
      | inr h => omega
    have hbez : Int.ofNat 1 = (extGcd m n).1 * Int.ofNat m + (extGcd m n).2 * Int.ofNat n := by
      have h := bezout_identity m n
      rw [hcop] at h
      exact h
    cases hu : (extGcd m n).1 with
    | ofNat k =>
      rw [hu] at hbez
      cases hv : (extGcd m n).2 with
      | ofNat j =>
        rw [hv, ← Int.ofNat_mul, ← Int.ofNat_mul, ← Int.ofNat_add] at hbez
        have hnat : 1 = k * m + j * n := Int.ofNat.inj hbez
        cases Nat.eq_zero_or_pos j with
        | inl hj0 =>
          rw [hj0, Nat.zero_mul, Nat.add_zero] at hnat
          refine ⟨k, ?_⟩
          rw [← hnat]
          rfl
        | inr hjpos =>
          have hj1 : j = (j - 1) + 1 := by omega
          rw [hj1, Nat.add_mul, Nat.one_mul] at hnat
          omega
      | negSucc j =>
        rw [hv] at hbez
        have hneg : Int.negSucc j = - Int.ofNat (j + 1) := by omega
        rw [hneg, Int.neg_mul, ← Int.ofNat_mul, ← Int.ofNat_mul] at hbez
        have hnat : k * m = 1 + (j + 1) * n := by omega
        refine ⟨k, ?_⟩
        rw [hnat]
        exact (ModEq.iff_dvd_sub (by omega)).mpr ⟨j + 1, by rw [Nat.mul_comm]; omega⟩
    | negSucc t =>
      rw [hu] at hbez
      have hnegt : Int.negSucc t = - Int.ofNat (t + 1) := by omega
      rw [hnegt, Int.neg_mul, ← Int.ofNat_mul] at hbez
      cases hv : (extGcd m n).2 with
      | negSucc j =>
        rw [hv] at hbez
        have hnegj : Int.negSucc j = - Int.ofNat (j + 1) := by omega
        rw [hnegj, Int.neg_mul, ← Int.ofNat_mul] at hbez
        omega
      | ofNat j =>
        rw [hv, ← Int.ofNat_mul] at hbez
        have hjn : j * n = 1 + (t + 1) * m := by omega
        have htm_pos : 1 ≤ (t + 1) * m := by
          have hm1 : m = (m - 1) + 1 := by omega
          rw [hm1, Nat.mul_add, Nat.mul_one]
          omega
        have h2j : 2 * j ≤ j * n := by
          have hn' : n = (n - 2) + 2 := by omega
          rw [hn', Nat.mul_add]
          omega
        have hjle : j ≤ (t + 1) * m := by omega
        refine ⟨(t + 1) * (n - 1), ?_⟩
        have hq : (t + 1) * (n - 1) * m = 1 + ((t + 1) * m - j) * n := by
          have h1 : ((t + 1) * m - j) * n + j * n = (t + 1) * m * n := by
            rw [← Nat.add_mul]
            have hsum : (t + 1) * m - j + j = (t + 1) * m := by omega
            rw [hsum]
          have h2 : (t + 1) * (n - 1) * m + (t + 1) * m = (t + 1) * m * n := by
            calc (t + 1) * (n - 1) * m + (t + 1) * m
                = ((t + 1) * (n - 1) + (t + 1)) * m := by rw [Nat.add_mul]
              _ = (t + 1) * ((n - 1) + 1) * m := by rw [Nat.mul_add, Nat.mul_one]
              _ = (t + 1) * n * m := by
                    have hn1 : (n - 1) + 1 = n := by omega
                    rw [hn1]
              _ = (t + 1) * m * n := by
                    rw [Nat.mul_assoc, Nat.mul_comm n m, ← Nat.mul_assoc]
          omega
        rw [hq]
        exact (ModEq.iff_dvd_sub (by omega)).mpr
          ⟨(t + 1) * m - j, by rw [Nat.mul_comm]; omega⟩

/-- Chinese Remainder Theorem (existence): for coprime moduli `m, n`, every simultaneous
system `x ≡ a [MOD m]`, `x ≡ b [MOD n]` admits a solution in `Nat`. -/
theorem chinese_remainder_exists {m n : Nat} (hcop : Nat.gcd m n = 1) (a b : Nat) :
    ∃ x : Nat, x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  cases exists_mod_inv hcop with
  | intro u hu =>
    have hcop' : Nat.gcd n m = 1 := by rw [Nat.gcd_comm]; exact hcop
    cases exists_mod_inv hcop' with
    | intro v hv =>
      refine ⟨a * (v * n) + b * (u * m), ?_, ?_⟩
      · have h1 : a * (v * n) ≡ a * 1 [MOD m] := ModEq.mul rfl hv
        have h2 : b * (u * m) ≡ 0 [MOD m] := by
          unfold ModEq
          rw [← Nat.mul_assoc, Nat.mul_comm (b * u) m, Nat.mul_mod, Nat.mod_self, Nat.zero_mul]
        have hsum : a * (v * n) + b * (u * m) ≡ a * 1 + 0 [MOD m] := ModEq.add h1 h2
        rw [Nat.mul_one, Nat.add_zero] at hsum
        exact hsum
      · have h1 : a * (v * n) ≡ 0 [MOD n] := by
          unfold ModEq
          rw [← Nat.mul_assoc, Nat.mul_comm (a * v) n, Nat.mul_mod, Nat.mod_self, Nat.zero_mul]
        have h2 : b * (u * m) ≡ b * 1 [MOD n] := ModEq.mul rfl hu
        have hsum : a * (v * n) + b * (u * m) ≡ 0 + b * 1 [MOD n] := ModEq.add h1 h2
        rw [Nat.zero_add, Nat.mul_one] at hsum
        exact hsum

/-- Chinese Remainder Theorem (uniqueness): any two solutions of a coprime simultaneous
congruence system are congruent modulo `m * n`. -/
theorem chinese_remainder_unique {m n a b x y : Nat}
    (hcop : Nat.gcd m n = 1)
    (hx1 : x ≡ a [MOD m]) (hx2 : x ≡ b [MOD n])
    (hy1 : y ≡ a [MOD m]) (hy2 : y ≡ b [MOD n]) :
    x ≡ y [MOD m * n] :=
  ModEq.of_coprime_mul hcop (hx1.trans hy1.symm) (hx2.trans hy2.symm)

private theorem countCoprime_prime {p : Nat} (hp : IsPrime p) :
    ∀ k : Nat, 1 ≤ k → k ≤ p → countCoprime p k = k - 1 := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ j ih =>
    intro h1 hle
    cases Nat.eq_zero_or_pos j with
    | inl hj0 =>
      subst hj0
      have hp2 := hp.1
      simp only [countCoprime, Nat.gcd_zero_right]
      split <;> omega
    | inr hjpos =>
      have hih : countCoprime p j = j - 1 := ih (by omega) (by omega)
      have hcop : Nat.gcd p j = 1 := by
        cases hp.2 (Nat.gcd p j) (Nat.gcd_dvd_left p j) with
        | inl h1 => exact h1
        | inr hp_eq =>
          have hpj : p ∣ j := by
            rw [← hp_eq]
            exact Nat.gcd_dvd_right p j
          cases hpj with
          | intro q hq =>
            cases Nat.eq_zero_or_pos q with
            | inl hq0 => rw [hq0, Nat.mul_zero] at hq; omega
            | inr hqpos =>
              have hq1 : q = (q - 1) + 1 := by omega
              rw [hq1, Nat.mul_add, Nat.mul_one] at hq
              omega
      simp only [countCoprime, hcop]
      split <;> omega

/-- Euler's totient theorem for primes: `φ(p) = p - 1` for every prime `p`. -/
theorem totient_prime {p : Nat} (hp : IsPrime p) : totient p = p - 1 :=
  countCoprime_prime hp p (by have := hp.1; omega) (Nat.le_refl p)

end DiscreteAlgebra
