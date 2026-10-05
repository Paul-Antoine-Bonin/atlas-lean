module

public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues111

@[expose] public section

namespace MetaMathlibExt

example : tribonacciWithInitialValues111 0 = 1 := rfl
example : tribonacciWithInitialValues111 1 = 1 := rfl
example : tribonacciWithInitialValues111 2 = 1 := rfl
example : tribonacciWithInitialValues111 3 = 3 := rfl
example : tribonacciWithInitialValues111 4 = 5 := rfl
example : tribonacciWithInitialValues111 5 = 9 := rfl

example (n : ℕ) :
    tribonacciWithInitialValues111 (n + 3) =
      tribonacciWithInitialValues111 (n + 2) +
        tribonacciWithInitialValues111 (n + 1) + tribonacciWithInitialValues111 n := rfl

#print axioms MetaMathlibExt.tribonacciWithInitialValues111

end MetaMathlibExt

end
