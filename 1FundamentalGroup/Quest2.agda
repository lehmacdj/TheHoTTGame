-- ignore
module 1FundamentalGroup.Quest2 where
open import 1FundamentalGroup.Preambles.P2

isSet→LoopSpace≡⊤ : {A : Type} (x : A) → isSet A → (x ≡ x) ≡ ⊤
isSet→LoopSpace≡⊤ = {!!}

data _⊔_ (A B : Type) : Type where

     inl : A → A ⊔ B
     inr : B → A ⊔ B

ℤ≡ℕ⊔ℕ : ℤ ≡ ℕ ⊔ ℕ
ℤ≡ℕ⊔ℕ = isoToPath i where
  toNats : ℤ → ℕ ⊔ ℕ
  toNats (pos n) = inr n
  toNats (negsuc n) = inl n

  fromNats : ℕ ⊔ ℕ → ℤ
  fromNats (inl n) = negsuc n
  fromNats (inr n) = pos n

  i : ℤ ≅ (ℕ ⊔ ℕ)
  i = iso toNats fromNats s r where
    s : section toNats fromNats
    s (inl x) = refl
    s (inr x) = refl

    r : retract toNats fromNats
    r (pos n) = refl
    r (negsuc n) = refl

⊔NoConfusion : {A B : Type} → A ⊔ B → A ⊔ B → Type
⊔NoConfusion (inl x) (inl y) = x ≡ y
⊔NoConfusion (inl x) (inr y) = ⊥
⊔NoConfusion (inr x) (inl y) = ⊥
⊔NoConfusion (inr x) (inr y) = x ≡ y

Path≡⊔NoConfusion : {A B : Type} -> (x y : A ⊔ B) -> (x ≡ y) ≡ ⊔NoConfusion x y
Path≡⊔NoConfusion {A} {B} x y = isoToPath i where
  ⊔NoConfusionRefl : (x : A ⊔ B) -> ⊔NoConfusion x x
  ⊔NoConfusionRefl (inl x) = refl
  ⊔NoConfusionRefl (inr x) = refl

  to : (x y : A ⊔ B) -> x ≡ y -> ⊔NoConfusion x y
  to x y = J (λ y' p -> ⊔NoConfusion x y') (⊔NoConfusionRefl x)

  from : (x y : A ⊔ B) -> ⊔NoConfusion x y -> x ≡ y
  from (inl x) (inl y) nc = cong inl nc
  from (inr x) (inr y) nc = cong inr nc

  i : (x ≡ y) ≅ (⊔NoConfusion x y)
  i = iso (to x y) (from x y) (s x y) (r x y) where
    s : (x y : A ⊔ B) -> section (to x y) (from x y)
    s (inl x) (inl y) = J (λ y' p -> to (inl x) (inl y') (from (inl x) (inl y') p) ≡ p) (JRefl {!λ y' p -> ⊔NoConfusion x y'!} {!!})
    s (inr x) (inr y) = {!!}

    r : (x y : A ⊔ B) -> retract (to x y) (from x y)
    r x y = {!!}

isSet⊔NoConfusion : {A B : Type} -> isSet A -> isSet B -> (x y : A ⊔ B) -> isProp (⊔NoConfusion x y)
isSet⊔NoConfusion = {!!}

isSet⊔ : {A B : Type} → isSet A -> isSet B -> isSet (A ⊔ B)
isSet⊔ {A} {B} isSetA isSetB x y =
  pathToFun (cong isProp (sym (Path≡⊔NoConfusion x y))) (isSet⊔NoConfusion isSetA isSetB x y)

isSetℤ : isSet ℤ
isSetℤ = pathToFun (cong isSet (sym ℤ≡ℕ⊔ℕ)) (isSet⊔ isSetℕ isSetℕ)
