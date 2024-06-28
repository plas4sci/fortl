module Lang.Options where

import Control.Monad.Trans.Reader

------------------------------
-- Language options accepts in files

data Option = Typed | Poly | HindleyMilner
  deriving (Eq, Show)

-- Some helpers
isTyped :: [Option] -> Bool
isTyped options = elem Typed options

isPoly :: [Option] -> Bool
isPoly options = elem Poly options

-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts = return $ opt : opts