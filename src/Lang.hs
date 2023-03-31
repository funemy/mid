module Lang (Name (..), Term (..)) where

import Text.Printf (printf)

newtype Name = Name String
    deriving (Eq)

instance Show Name where
    show (Name s) = s

-- TODO: add List and Vec
-- TODO: add Either
-- FIXME: missing sym/cong/trans for equality
data Term
    = Var Name
    | Pi Name Term Term
    | Lam Name Term
    | App Term Term
    | Sigma Name Term Term
    | -- Pair constructor
      MkPair Term Term
    | Fst Term
    | Snd Term
    | Nat
    | Zero
    | Succ Term
    | -- indNat has the same signature as ATAPL
      -- 1st term: the Property (Nat -> U)
      -- 2nd term: the base case (p 0)
      -- 3rd term: the inductive case
      -- 4th term: the number
      IndNat Term Term Term Term
    | -- Equality type
      -- The 1st argument is the type of the 2nd and 3rd
      -- TODO: we should be able to infer the 1st argument
      Equal Term Term Term
    | -- Ctor for Equality types (i.e., refl)
      -- I'm curious about this, isn't `refl` in Agda takes implicit arguments?
      Refl
    | -- Substitution on equal terms
      -- Given a property p of some type A, a proof that p holds on an element x : A,
      -- and a proof of x = y (y, of course, should also be of type A),
      -- returns a proof that p also holds on y
      -- 1st term: property p
      -- 2nd term: proof of the first property on x, i.e., (p x)
      -- 3rd term: equality proof of x=y
      Subst Term Term Term
    | UnitTy
    | Unit
    | Absurd
    | -- Induction principle for Absurd
      -- Given a proposition we want to prove, and a proof of absurdity,
      -- returns a proof of the target proposition
      -- 1st term: the proposition p we want to prove, p : U
      -- 2nd term: a proof of absurdity
      IndAbsurd Term Term
    | -- Atom type as in "The Litte Typer"
      Atom
    | -- Ctor for Atom values
      Quote String
    | Universe
    | -- Type annotation (ascription)
      -- 1st term: term,
      -- 2nd term: type
      As Term Term

toInt :: Term -> Int
toInt Zero = 0
toInt (Succ x) = 1 + toInt x
toInt _ = error "Cannot print ill-formed natural numbers."

instance Show Term where
    show (Var s) = show s
    show (Pi n ty ty') = printf "Π%s:%s.%s" (show n) (show ty) (show ty')
    show (Lam n b) = printf "λ%s.%s" (show n) (show b)
    show (App f a) = printf "%s %s" (show f) (show a)
    show (Sigma n ty ty') = printf "Σ%s:%s.%s" (show n) (show ty) (show ty')
    show (MkPair l r) = printf "(%s, %s)" (show l) (show r)
    show (Fst p) = printf "%s.1" (show p)
    show (Snd p) = printf "%s.2" (show p)
    show Nat = "Nat"
    show Zero = "0"
    show n@(Succ _) = show $ toInt n
    show (IndNat ty t1 t2 t3) = printf "(ind-nat %s %s %s %s)" (show ty) (show t1) (show t2) (show t3)
    show (Equal ty t1 t2) = printf "%s:%s≡%s" (show t1) (show ty) (show t2)
    show Refl = "refl"
    show (Subst t1 t2 t3) = printf "(subst %s %s %s)" (show t1) (show t2) (show t3)
    show UnitTy = "Unit"
    show Unit = "()"
    show Absurd = "⊥"
    show (IndAbsurd e ty) = printf "(ind-absurd %s %s)" (show e) (show ty)
    show Atom = "Atom"
    show (Quote s) = printf "'%s" s
    show Universe = "U"
    show (As e ty) = printf "(as %s %s)" (show e) (show ty)
