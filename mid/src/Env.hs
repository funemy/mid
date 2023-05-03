module Env (
    Result,
    emptyEnv,
    extend,
    freshen,
    lookup,
    names,
) where

import Lang (Env (..), ErrMsg (..), Name (..), Result)
import Prelude hiding (lookup)

emptyEnv :: Env v
emptyEnv = Env []

failure :: String -> Result v
failure = Left . ErrMsg

lookup :: Env v -> Name -> Result v
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
