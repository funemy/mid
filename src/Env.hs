module Env (
    Res,
    emptyEnv,
    extend,
    freshen,
    lookup,
    names,
) where

import Err (ErrMsg (..))
import Lang (Env (..), Name (..))
import Prelude hiding (lookup)

emptyEnv :: Env v
emptyEnv = Env []

type Res v = Either ErrMsg v

failure :: String -> Res v
failure = Left . ErrMsg

lookup :: Env v -> Name -> Res v
lookup (Env []) (Name n) = failure ("Not found identifier: " ++ n)
lookup (Env ((x, v) : xs)) n
    | x == n = Right v
    | otherwise = lookup (Env xs) n

extend :: Env v -> Name -> v -> Env v
extend (Env xs) n val = Env ((n, val) : xs)

names :: Env v -> [Name]
names (Env env) = map fst env

-- Given a list of used names and a proposed name,
-- return a non-conflicting name
-- The proposed name will be returned if it is non-conflicting
freshen :: [Name] -> Name -> Name
freshen used x
    | x `elem` used = freshen used (nextName x)
    | otherwise = x
  where
    nextName :: Name -> Name
    nextName (Name s) = Name (s ++ "'")
