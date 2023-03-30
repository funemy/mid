module Lang (Name(..), Term(..)) where
import           Text.Printf (printf)

newtype Name = Name String
  deriving (Eq)

instance Show Name where
  show (Name s) = s

-- TODO: add List and Vec
-- TODO: add Either
data Term
  = Var Name
  | Pi Name Term Term
  | Lam Name Term
  | App Term Term
  | Sigma Name Term Term
  -- Pair constructor
  | MkPair Term Term
  | Fst Term
  | Snd Term
  | Nat
  | Zero
  | Succ Term
  | IndNat Term Term Term Term
  -- Equality type
  | Equal Term Term
  -- Ctor for Equality types (i.e., refl)
  | Refl
  -- Substitution on equal terms
  -- FIXME: missing sym/cong/trans
  | Subst Term Term Term
  | UnitTy
  | Unit
  | Absurd
  | IndAbsrud Term Term
  -- Atom type as in "The Litte Typer"
  | Atom
  -- Ctor for Atom
  | Quote String
  | Universe
  | Isa Term Term

toInt :: Term -> Int
toInt Zero     = 0
toInt (Succ x) = 1 + toInt x
toInt _        = error "Cannot print ill-formed natural numbers."

instance Show Term where
  show (Var s)                 = show s
  show (Pi n ty ty')           = printf "Π%s:%s.%s" (show n) (show ty) (show ty')
  show (Lam n b)               = printf "λ%s.%s" (show n) (show b)
  show (App f a)               = printf "%s %s" (show f) (show a)
  show (Sigma n ty ty')        = printf "Σ%s:%s.%s" (show n) (show ty) (show ty')
  show (MkPair l r)            = printf "(%s, %s)" (show l) (show r)
  show (Fst p)                 = printf "%s.1" (show p)
  show (Snd p)                 = printf "%s.2" (show p)
  show Nat                     = "Nat"
  show Zero                    = "0"
  show n@(Succ _)              = show $ toInt n
  show (IndNat ty t1 t2 t3)    = printf "(ind-nat %s %s %s %s)" (show ty) (show t1) (show t2) (show t3)
  show (Equal ty ty')          = printf "%s≡%s" (show ty) (show ty')
  show Refl                    = "refl"
  show (Subst t1 t2 t3)        = printf "(subst %s %s %s)" (show t1) (show t2) (show t3)
  show UnitTy                  = "Unit"
  show Unit                    = "()"
  show Absurd                  = "⊥"
  show (IndAbsrud e ty)        = printf "(ind-absurd %s %s)" (show e) (show ty)
  show Atom                    = "Atom"
  show (Quote s)               = printf "'%s" s
  show Universe                = "U"
  show (Isa e ty)              = printf "(isa %s %s)" (show e) (show ty)
