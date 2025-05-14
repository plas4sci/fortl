module Units where

open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality
open import Data.Product

record AbelianGroup : Set₁ where
  field
    X : Set
    unit : X
    _⊗_  : X -> X -> X
    _⁻1  : X -> X

    unitL : {x : X} -> unit ⊗ x ≡ x
    unitR : {x : X} -> x ⊗ unit ≡ x
    assoc : {x y z : X} -> x ⊗ (y ⊗ z) ≡ (x ⊗ y) ⊗ z
    inv   : {x : X} -> (x ⁻1) ⊗ x ≡ unit
    comm  : {x y : X} -> x ⊗ y ≡ y ⊗ x

open AbelianGroup {{...}}

prod : AbelianGroup -> AbelianGroup -> AbelianGroup
prod (record { X = Xa ; unit = unita ; _⊗_ = _⊗a_ ; _⁻1 = _⁻1a ; unitL = unitLa ; unitR = unitRa ; assoc = assoca ; inv = inva ; comm = comma })
     (record { X = Xb ; unit = unitb ; _⊗_ = _⊗b_ ; _⁻1 = _⁻1b ; unitL = unitLb ; unitR = unitRb ; assoc = assocb ; inv = invb ; comm = commb })
     = record
         { X = Xa × Xb
         ; unit = unita , unitb
         ; _⊗_ = \(xa , xb) -> \(ya , yb) -> (xa ⊗a ya , xb ⊗b yb)
         ; _⁻1 = {!!}
         ; unitL = {!!}
         ; unitR = {!!}
         ; assoc = {!!}
         ; inv = {!!}
         ; comm = {!!}
         }

record AbelianGroupGradedField {{G : AbelianGroup}} : Set₁ where
  field
    L    : X -> Set
    _·_  : {i j : X} -> L i -> L j -> L (i ⊗ j)
    _+_  : {i : X} -> L i -> L i -> L i
    _⁻1  : {i : X} -> L i -> L (i ⁻1)
    -_   : {i : X} -> L i -> L i
    one  : L unit
    zero : {i : X} -> L i

    unit·L : {i : X} {x : L i} -> x · one ≅ x
    unit·R : {i : X} {x : L i} -> one · x ≅ x
    assoc· : {i j k : X} {x : L i} {y : L j} {z : L k}
          -> x · (y · z) ≅ (x · y) · z
    comm· : {i j : X} {x : L i} {y : L j}
          -> x · y ≅ y · x
    inv1· : {i : X} {x : L i} -> x · (x ⁻1) ≅ one
    inv2· : {i : X} {x : L i} -> (x ⁻1) · x ≅ one

    unit+L : {i : X} {x : L i} -> x + zero ≡ x
    unit+R : {i : X} {x : L i} -> zero + x ≡ x
    assoc+ : {i : X} {x y z : L i}
          -> x + (y + z) ≡ (x + y) + z
    comm+ : {i : X} {x y : L i}
          -> x + y ≡ y + x
    inv1+ : {i : X} {x : L i} -> x + (- x) ≡ zero
    inv2+ : {i : X} {x : L i} -> (- x) + x ≡ zero

    distrib : {i j : X} {x : L i} {y z : L j}
            -> x · (y + z) ≡ (x · y) + (x · z)

open AbelianGroupGradedField {{...}}
