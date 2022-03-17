-- ignore
module 1FundamentalGroup.Quest0 where
open import 1FundamentalGroup.Preambles.P0

Refl : base ≡ base
Refl = λ i → base

Flip : Bool → Bool
Flip false = true
Flip true = false

flipIso : Bool ≅ Bool
flipIso = iso Flip Flip eq eq where
  eq : section Flip Flip
  eq false = λ i → false
  eq true = λ i → true

flipPath : Bool ≡ Bool
flipPath = isoToPath flipIso

doubleCover : S¹ → Type
doubleCover base = Bool
doubleCover (loop i) = flipPath i

endPtOfTrue : base ≡ base → doubleCover base
endPtOfTrue p = endPt doubleCover p true

Refl≢loop : Refl ≡ loop → ⊥
Refl≢loop p = true≢false (cong endPtOfTrue p)

------------------- Side Quest - Empty -------------------------

-- This is a comment box,
-- remove the {- and -} to do the side quests

toEmpty : (A : Type) → Type
toEmpty A = A → ⊥

pathEmpty : (A : Type) → Type₁
pathEmpty A = A ≡ ⊥

isoEmpty : (A : Type) → Type
isoEmpty A = A ≅ ⊥

outOf⊥ : (A : Type) → ⊥ → A
outOf⊥ A ()

toEmpty→isoEmpty : (A : Type) → toEmpty A → isoEmpty A
toEmpty→isoEmpty A imp = iso imp (outOf⊥ A) s r where
  s : section imp (outOf⊥ A)
  s = λ ()

  r : retract imp (outOf⊥ A)
  r = λ a → outOf⊥ (outOf⊥ A (imp a) ≡ a) (imp a)

isoEmpty→pathEmpty : (A : Type) → isoEmpty A → pathEmpty A
isoEmpty→pathEmpty A = λ x → isoToPath x

pathEmpty→toEmpty : (A : Type) → pathEmpty A → toEmpty A
pathEmpty→toEmpty A = λ x → pathToFun x 

------------------- Side Quests - true≢false --------------------

-- This is a comment box,
-- remove the {- and -} to do the side quests

true≢false' : true ≡ false → ⊥
true≢false' p = pathToFun (cong T p) tt where
  T : Bool → Type
  T true = ⊤
  T false = ⊥
