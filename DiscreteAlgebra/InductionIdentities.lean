namespace DiscreteAlgebra

/-- Sum of the first `n` natural numbers: `0 + 1 + ⋯ + n`. -/
def sumFirst : Nat → Nat
  | 0 => 0
  | n + 1 => sumFirst n + (n + 1)

/-- Sum of the first `n` odd natural numbers: `1 + 3 + ⋯ + (2n - 1)`. -/
def sumOdd : Nat → Nat
  | 0 => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- Sum of squares of the first `n` natural numbers: `0² + 1² + ⋯ + n²`. -/
def sumSquares : Nat → Nat
  | 0 => 0
  | n + 1 => sumSquares n + (n + 1) * (n + 1)

/-- Sum of cubes of the first `n` natural numbers: `0³ + 1³ + ⋯ + n³`. -/
def sumCubes : Nat → Nat
  | 0 => 0
  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)

/-- Geometric sum of powers of two: `2⁰ + 2¹ + ⋯ + 2ⁿ`. -/
def sumPowTwo : Nat → Nat
  | 0 => 1
  | n + 1 => sumPowTwo n + 2 ^ (n + 1)

/-- Gauss's triangular number identity: `2 * (0 + 1 + ⋯ + n) = n * (n + 1)`. -/
theorem two_mul_sumFirst (n : Nat) : 2 * sumFirst n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc 2 * sumFirst (k + 1)
        = 2 * (sumFirst k + (k + 1)) := rfl
      _ = 2 * sumFirst k + 2 * (k + 1) := by rw [Nat.mul_add]
      _ = k * (k + 1) + 2 * (k + 1) := by rw [ih]
      _ = (k + 2) * (k + 1) := by rw [← Nat.add_mul]
      _ = (k + 1) * (k + 2) := by rw [Nat.mul_comm]

/-- Sum of the first `n` odd natural numbers equals `n²`. -/
theorem sumOdd_eq_sq (n : Nat) : sumOdd n = n * n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc sumOdd (k + 1)
        = sumOdd k + (2 * k + 1) := rfl
      _ = k * k + (2 * k + 1) := by rw [ih]
      _ = k * k + k + k + 1 := by omega
      _ = k * (k + 1) + (k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      _ = (k + 1) * (k + 1) := by rw [Nat.add_mul, Nat.one_mul]

/-- Sum-of-squares identity: `6 * (0² + 1² + ⋯ + n²) = n * (n + 1) * (2n + 1)`. -/
theorem six_mul_sumSquares (n : Nat) :
    6 * sumSquares n = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hlin : k * (2 * k + 1) + 6 * (k + 1) = (k + 2) * (2 * (k + 1) + 1) := by
      have h1 : k * (2 * k + 1) = 2 * (k * k) + k := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm k 2 k]
      have h2 : (k + 2) * (2 * (k + 1) + 1) = 2 * (k * k) + 7 * k + 6 := by
        have h2a : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
        rw [h2a, Nat.add_mul, Nat.mul_add, Nat.mul_left_comm k 2 k]
        omega
      rw [h1, h2]
      omega
    calc 6 * sumSquares (k + 1)
        = 6 * (sumSquares k + (k + 1) * (k + 1)) := rfl
      _ = 6 * sumSquares k + 6 * ((k + 1) * (k + 1)) := by rw [Nat.mul_add]
      _ = k * (k + 1) * (2 * k + 1) + 6 * ((k + 1) * (k + 1)) := by rw [ih]
      _ = (k + 1) * (k * (2 * k + 1)) + (k + 1) * (6 * (k + 1)) := by
            rw [Nat.mul_comm k (k + 1), Nat.mul_assoc (k + 1) k (2 * k + 1),
                Nat.mul_left_comm 6 (k + 1) (k + 1)]
      _ = (k + 1) * (k * (2 * k + 1) + 6 * (k + 1)) := by rw [← Nat.mul_add]
      _ = (k + 1) * ((k + 2) * (2 * (k + 1) + 1)) := by rw [hlin]
      _ = (k + 1) * (k + 2) * (2 * (k + 1) + 1) := by rw [← Nat.mul_assoc]

/-- Nicomachus's theorem: `0³ + 1³ + ⋯ + n³ = (0 + 1 + ⋯ + n)²`. -/
theorem sumCubes_eq_sumFirst_sq (n : Nat) :
    sumCubes n = sumFirst n * sumFirst n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have htri : 2 * sumFirst k = k * (k + 1) := two_mul_sumFirst k
    have hsq : (sumFirst k + (k + 1)) * (sumFirst k + (k + 1)) =
        sumFirst k * sumFirst k + 2 * sumFirst k * (k + 1) + (k + 1) * (k + 1) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have hcomm : (k + 1) * sumFirst k = sumFirst k * (k + 1) := Nat.mul_comm _ _
      have h2a : 2 * sumFirst k = sumFirst k + sumFirst k := by omega
      have h2 : 2 * sumFirst k * (k + 1) =
          sumFirst k * (k + 1) + sumFirst k * (k + 1) := by
        rw [h2a, Nat.add_mul]
      rw [hcomm, h2]
      omega
    have hcube : (k + 1) * (k + 1) * (k + 1) =
        k * (k + 1) * (k + 1) + (k + 1) * (k + 1) := by
      rw [Nat.add_mul k 1 (k + 1), Nat.one_mul, Nat.add_mul]
    calc sumCubes (k + 1)
        = sumCubes k + (k + 1) * (k + 1) * (k + 1) := rfl
      _ = sumFirst k * sumFirst k + (k + 1) * (k + 1) * (k + 1) := by rw [ih]
      _ = sumFirst k * sumFirst k + k * (k + 1) * (k + 1) + (k + 1) * (k + 1) := by
            rw [hcube, ← Nat.add_assoc]
      _ = sumFirst k * sumFirst k + 2 * sumFirst k * (k + 1) + (k + 1) * (k + 1) := by
            rw [← htri]
      _ = (sumFirst k + (k + 1)) * (sumFirst k + (k + 1)) := by rw [← hsq]
      _ = sumFirst (k + 1) * sumFirst (k + 1) := rfl

/-- Geometric series identity for base 2: `(2⁰ + 2¹ + ⋯ + 2ⁿ) + 1 = 2^(n + 1)`. -/
theorem sumPowTwo_add_one (n : Nat) : sumPowTwo n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc sumPowTwo (k + 1) + 1
        = sumPowTwo k + 2 ^ (k + 1) + 1 := rfl
      _ = (sumPowTwo k + 1) + 2 ^ (k + 1) := by omega
      _ = 2 ^ (k + 1) + 2 ^ (k + 1) := by rw [ih]
      _ = 2 ^ (k + 1) * 2 := by omega
      _ = 2 ^ (k + 1 + 1) := by rw [Nat.pow_succ]

end DiscreteAlgebra
