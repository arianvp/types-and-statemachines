\begin{code}

data Σ (A : Set) (P : A → Set) : Set where
  _,_ : (a : A) →  (b : P a) → Σ A P


Famₒ : (I X : Set) → Set
Famₒ I X = Σ I (λ x → X)

Famₐ : {I X Y : Set} → (f : X → Y) → (Famₒ I X → Famₒ I Y)
Famₐ f (I , p) = I , f p

Powₒ : (X : Set) → Set₁
Powₒ X = X → Set

Powₐ : { X Y : Set} → (f : X → Y) → (Powₒ Y → Powₒ X)
Powₐ f  = λ P → λ z → P (f z)
\end{code}


Given the set ℕ we can define a recursor on this set as follows
\begin{code}
data ℕ : Set where
  z : ℕ
  s_ : ℕ → ℕ

0' : ℕ
0' = z

1' : ℕ
1' = s z


module A where
    R : (A : Powₒ ℕ) → (a : A z) → (b : ({n : ℕ} → A n → A (s n))) → (n : ℕ) → A n
    R A a b z = a
    R A a b (s n) = b (R A a b n)


\end{code}
