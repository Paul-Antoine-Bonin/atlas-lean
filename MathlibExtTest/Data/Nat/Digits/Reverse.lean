import MathlibExt.Data.Nat.Digits.Reverse

example : Nat.reverseDigits 10 123 = 321 := by decide

example : Nat.reverseDigits 2 6 = 3 := by decide

example (n : ℕ) : Nat.reverseDigits 0 n = n := by simp

example (n : ℕ) : Nat.reverseDigits 1 n = n := by simp
