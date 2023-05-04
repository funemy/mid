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

lookup :: Name -> Env v -> Result v
lookup (Name n) (Env []) = failure ("Not found identifier: " ++ n)
lookup n (Env ((x, v) : xs))
    | x == n = Right v
    | otherwise = lookup n (Env xs)

extend :: Name -> v -> Env v -> Env v
extend n val (Env xs) = Env ((n, val) : xs)

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
