module Env () where

import           Data.Bifunctor (Bifunctor (second))
import           Lang           (Name (..))
import           Prelude        hiding (lookup)

newtype Env val = Env [(Name, val)]
    deriving (Show, Eq)

emptyEnv :: Env v
emptyEnv = Env []

instance Functor Env where
  fmap f (Env xs) = Env (map (second f) xs)

newtype Msg = Msg String
    deriving (Show)

type Res v = Either Msg v

failure :: String -> Res v
failure =  Left . Msg

lookup :: Env v -> Name -> Res v
lookup (Env []) (Name n) = failure ("Not found identifier " ++ n)
lookup (Env ((x, v) : xs)) n
    | x == n = Right v
    | otherwise = lookup (Env xs) n

extend :: Env v -> Name -> v -> Env v
extend (Env xs) n val = Env ((n, val) : xs)

-- Given a list of used names and a proposed name,
-- return a non-conflicting name
-- The proposed name will be returned if it is non-conflicting
freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used  = freshen used (nextName x)
    | otherwise = x
    where
        nextName :: Name -> Name
        nextName (Name s) = Name (s ++ "'")
