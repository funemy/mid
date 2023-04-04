module TyCheck (
    ) where

import Env
import Err (errMsgTyCk)
import Lang (
    Closure,
    Env (..),
    Name,
    Neutral (..),
    Term (..),
    Ty,
    TyCtx,
    TyCtxEntry (..),
    Val (..),
 )
import Norm (eval, evalCls, reify')
import Prelude hiding (lookup)

type Depth = Int

-- used for alpha-equivalence checking
type NameSpace = Env Depth

-- the auxliary function for alpha equivalence checking
alphaEquiv' :: Int -> NameSpace -> Term -> NameSpace -> Term -> Bool
-- simple cases
alphaEquiv' _ _ Nat _ Nat = True
alphaEquiv' _ _ Zero _ Zero = True
alphaEquiv' _ _ UnitTy _ UnitTy = True
alphaEquiv' _ _ Unit _ Unit = True
alphaEquiv' _ _ Absurd _ Absurd = True
alphaEquiv' _ _ Atom _ Atom = True
alphaEquiv' _ _ Universe _ Universe = True
alphaEquiv' _ _ Refl _ Refl = True
alphaEquiv' _ _ (Quote s1) _ (Quote s2) = s1 == s2
alphaEquiv' _ ns1 (Var n1) ns2 (Var n2) = lookup ns1 n1 == lookup ns2 n2
-- inductive cases
alphaEquiv' d ns1 (App t11 t12) ns2 (App t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (MkPair t11 t12) ns2 (MkPair t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Fst t1) ns2 (Fst t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Snd t1) ns2 (Snd t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Succ t1) ns2 (Succ t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (IndAbsurd t11 t12) ns2 (IndAbsurd t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
-- Special case:
-- If two terms can be type cheked to be Absurd, then they are alpha equivalent no matter what
-- When encountering an absurd term, we just annotate them with type Absurd
-- so the terms are alpha-equivalent no matter what.
-- Otherwise, we don't have a way of type-checking them, because Absurd
-- has no inhabitant.
alphaEquiv' _ _ (As _ Absurd) _ (As _ Absurd) = True
alphaEquiv' d ns1 (As t11 t12) ns2 (As t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Equal t11 t12 t13) ns2 (Equal t21 t22 t23) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
     in equiv1 && equiv2 && equiv3
alphaEquiv' d ns1 (Subst t11 t12 t13) ns2 (Subst t21 t22 t23) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
     in equiv1 && equiv2 && equiv3
alphaEquiv' d ns1 (IndNat t11 t12 t13 t14) ns2 (IndNat t21 t22 t23 t24) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
        equiv4 = alphaEquiv' d ns1 t14 ns2 t24
     in equiv1 && equiv2 && equiv3 && equiv4
-- interesting cases
alphaEquiv' d ns1 (Pi n1 t11 t12) ns2 (Pi n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
alphaEquiv' d ns1 (Lam n1 t1) ns2 (Lam n2 t2) =
    let ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
     in alphaEquiv' (d + 1) ns1' t1 ns2' t2
alphaEquiv' d ns1 (Sigma n1 t11 t12) ns2 (Sigma n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
-- fallback case
alphaEquiv' _ _ _ _ _ = False

alphaEquiv :: Term -> Term -> Bool
alphaEquiv t1 = alphaEquiv' 0 emptyEnv t1 emptyEnv

lookupTy :: TyCtx -> Name -> Res Ty
lookupTy ctx n = do
    entry <- lookup ctx n
    case entry of
        Decl ty -> return ty
        Def ty _ -> return ty

-- Convert a typing context into an Env of Val.
-- Used when calling `eval` in `infer`
toEnv :: TyCtx -> Env Val
toEnv (Env []) = Env []
toEnv (Env ((n, e) : xs)) = extend rest n v
  where
    rest = toEnv (Env xs)
    v = case e of
        Decl ty -> VNeutral ty (NVar n)
        Def _ val -> val

-- isXXXs below are a set of helper functions used in type checking
-- The functions in the tutorial requires TyCtx mostly for debugging.
-- We will keep the functions simple for the moment.
isPi :: Ty -> Res (Ty, Closure)
isPi (VPi tyA cls) = Right (tyA, cls)
isPi ty = Left $ errMsgTyCk "Expect a Pi type, but got" ty

isNat :: Ty -> Res ()
isNat VNat = Right ()
isNat ty = Left $ errMsgTyCk "Expect a Nat type, but got" ty

infer :: TyCtx -> Term -> Res Ty
infer ctx (Var n) = lookupTy ctx n
infer ctx (Pi n tyA tyB) = do
    check ctx tyA VUniverse
    tyA' <- eval (toEnv ctx) tyA
    check (extend ctx n (Decl tyA')) tyB VUniverse
    Right VUniverse
infer ctx (App f a) = do
    fTy <- infer ctx f
    (tyA, cls) <- isPi fTy
    check ctx a tyA
    aVal <- eval (toEnv ctx) a
    tyB <- evalCls cls aVal
    Right tyB
infer ctx (Sigma na te te') = _wH
infer ctx (MkPair te te') = _wI
infer ctx (Fst te) = _wJ
infer ctx (Snd te) = _wK
infer _ Nat = Right VUniverse
infer _ Zero = Right VNat
infer ctx (Succ n) = do
    ty <- infer ctx n
    isNat ty
    Right VNat
infer ctx (IndNat te te' te2 te3) = _wO
infer ctx (Equal te te' te2) = _wP
infer ctx (Subst te te' te2) = _wR
infer _ UnitTy = Right VUniverse
infer _ Unit = Right VUnitTy
infer _ Absurd = Right VUniverse
infer ctx (IndAbsurd te te') = _wV
infer _ Atom = Right VUniverse
infer _ (Quote s) = Right VAtom
infer _ Universe = Right VUniverse
infer ctx (As te te') = _wZ
infer _ t = Left $ errMsgTyCk "No inference rule for" t

check :: TyCtx -> Term -> Ty -> Res ()
check ctx (Lam na te) ty = _w12
check ctx (App te te') ty = _w13
check ctx (Sigma na te te') ty = _w14
check ctx (MkPair te te') ty = _w15
check ctx (Fst te) ty = _w16
check ctx (Snd te) ty = _w17
check ctx (IndNat te te' te2 te3) ty = _w1b
check ctx (Equal te te' te2) ty = _w1c
check ctx Refl ty = _w1d
check ctx (Subst te te' te2) ty = _w1e
check ctx (IndAbsurd te te') ty = _w1i
check ctx (As te te') ty = _w1m
-- subsumption
check ctx t ty1 = do
    ty2 <- infer ctx t
    ty1' <- reify' ctx VUniverse ty1
    ty2' <- reify' ctx VUniverse ty2
    if alphaEquiv ty1' ty2'
        then Right ()
        else Left $ errMsgTyCk "cannot show equivalence between inferred and checked type on term" (t, ty1, ty2)
