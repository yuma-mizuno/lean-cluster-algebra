import ring_theory.localization
import category_theory.yoneda
import algebra.category.CommRing.basic

open category_theory

universe u
section
variables {A : Type u} [comm_ring A] (M : submonoid (CommRing.of A)) 

section
variables (x y : ℕ)

def foo := x + y

#check (foo : ℕ → ℕ → ℕ)
end

section
parameters (x y : ℕ)

def bar := x + y

#check (bar : ℕ)
#check (bar + 7 : ℕ)


end

end