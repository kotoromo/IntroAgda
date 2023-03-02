Type = Set

data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

Nat-elim : {φ : ℕ → Type}
           → φ 0
           → ((k : ℕ) → φ k → φ (suc k))
           --------------------------------
           → (n : ℕ) → φ n


Nat-elim {φ} φ₀ f zero = φ₀
Nat-elim {φ} φ₀ f (suc x) = f x (Nat-elim φ₀ f x)

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + suc n = suc n
suc m + zero = suc m
suc m + suc n = suc (suc (m + n))

data _≡_ {T : Type} : T → T → Type where
  refl : (x : T) → x ≡ x


≡-sym : ∀ {T : Type} {n m : T}
        → n ≡ m
        -----------
        → m ≡ n

≡-sym (refl n) = refl n

≡-trans : ∀ {A : Type} {x y z : A}
          → x ≡ y
          → y ≡ z
          -------------------------
          → x ≡ z

≡-trans (refl x) (refl y) = refl x

--{ Lema }--
--  * ∀ A B : Type . ∀ f : A → B . ∀ x y : T . x ≡ y ⇒ f x ≡ f y 
--  * ∀ n ∈ ℕ . n + 0 = n
--  * ∀ n ∈ ℕ . 0 + n = n
--  * ∀ n, m ∈ ℕ . n + suc m = suc (m + n)

cong : ∀ {A B : Type} (f : A → B) {x y : A}
       → x ≡ y
       --------
       → f x ≡ f y
cong f (refl x) = refl (f x)

zero+n-=-n : ∀ (n : ℕ) → (zero + n) ≡ n
zero+n-=-n zero = refl zero
zero+n-=-n (suc n) = refl (suc n)

n+zero-=-n : ∀ (n : ℕ) → (n + zero) ≡ n
n+zero-=-n zero = refl zero
n+zero-=-n (suc n) = refl (suc n)

+-suc : ∀ (n m : ℕ) → (suc m + n) ≡ suc (m + n)

+-suc zero m = cong suc (≡-sym (n+zero-=-n m))
+-suc (suc n) zero = cong suc (cong suc (zero+n-=-n n))
+-suc (suc n) (suc m) = cong suc (cong suc HI)
  where
    HI : (suc m + n) ≡ suc (m + n)
    HI = +-suc n m
              
--{ La suma en ℕ es conmutativa. }--
+-conm : ∀ (x y : ℕ) → (x + y) ≡ (y + x)

+-conm zero y = ≡-sym AF4
  where
    AF1 : (zero + y) ≡ y
    AF1 = zero+n-=-n y
    AF2 : (y + zero) ≡ y
    AF2 = n+zero-=-n y
    AF3 : y ≡ (zero + y)
    AF3 = ≡-sym AF1
    AF4 : (y + zero) ≡ (zero + y)
    AF4 = ≡-trans AF2 AF3
+-conm (suc x) zero = refl (suc x)
+-conm (suc x) (suc y) = cong suc (cong suc HI)
  where
    HI : (x + y) ≡ (y + x) 
    HI = +-conm x y