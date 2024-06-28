{-# LANGUAGE DataKinds #-}

module Lang.Primitives where

import Lang.Syntax

type0 :: Type 1
type0 = TyCon "Type"

natTy :: Type 0
natTy = TyCon "Nat"

floatTy :: Type 0
floatTy = TyCon "Float"

agroup :: Type 1
agroup = TyCon "AbelianGroup"

typeConstructors :: [(String, Type 1)]
typeConstructors = [
    ("Float", type0)
  , ("Nat"  , type0)
  , ("Unit" , FunTy agroup type0)
  , ("1", agroup)
 ]