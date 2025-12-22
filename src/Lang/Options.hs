module Lang.Options where

import Control.Monad.Trans.Reader

------------------------------
-- Language options accepted in files

data Option = Default
  deriving (Eq, Show)

-- Builds up a the language option list and checks for conflicting options
addOption :: Option -> [Option] -> ReaderT String (Either String) [Option]
addOption opt opts = return $ opt : opts