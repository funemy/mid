module TyCheck () where

import Lang (Name, Term (..))

type Depth = Int

newtype NameSpace = NameSpace [(Name, Depth)]

emptyNS :: NameSpace
emptyNS = NameSpace []

lookupNS :: Name -> NameSpace -> Maybe Int
lookupNS n (NameSpace []) = Nothing
lookupNS n (NameSpace ((n', d) : xs))
    | n == n' = Just d
    | otherwise = lookupNS n (NameSpace xs)

extendNS :: Name -> Depth -> NameSpace -> NameSpace
extendNS n d (NameSpace xs) = NameSpace ((n, d) : xs)

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
alphaEquiv' _ ns1 (Var n1) ns2 (Var n2) = lookupNS n1 ns1 == lookupNS n2 ns2
-- inductive cases
alphaEquiv' d ns1 (App t11 t12) ns2 (App t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (MkPair t11 t12) ns2 (MkPair t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Fst t1) ns2 (Fst t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Snd t1) ns2 (Snd t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Succ t1) ns2 (Succ t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (IndAbsrud t11 t12) ns2 (IndAbsrud t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
-- Special case:
-- If two terms can be type cheked to be Absurd, then they are alpha equivalent no matter what
alphaEquiv' _ _ (As _ Absurd) _ (As _ Absurd) = True
alphaEquiv' d ns1 (As t11 t12) ns2 (As t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Equal t11 t12) ns2 (Equal t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
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
        ns1' = extendNS n1 d ns1
        ns2' = extendNS n2 d ns2
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
alphaEquiv' d ns1 (Lam n1 t1) ns2 (Lam n2 t2) =
    let ns1' = extendNS n1 d ns1
        ns2' = extendNS n2 d ns2
     in alphaEquiv' (d + 1) ns1' t1 ns2' t2
alphaEquiv' d ns1 (Sigma n1 t11 t12) ns2 (Sigma n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extendNS n1 d ns1
        ns2' = extendNS n2 d ns2
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
-- fallback case
alphaEquiv' _ _ _ _ _ = False

alphaEquiv :: Term -> Term -> Bool
alphaEquiv t1 t2 = alphaEquiv' 0 emptyNS t1 emptyNS t2
