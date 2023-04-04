module Err (ErrMsg (..), errMsg, errMsgNorm, errMsgTyCk) where

newtype ErrMsg = ErrMsg String
    deriving (Show, Eq)

errMsg :: Show t => String -> String -> t -> ErrMsg
errMsg stage msg t = ErrMsg (stage ++ " " ++ msg ++ ": " ++ show t)

errMsgNorm :: Show t => String -> t -> ErrMsg
errMsgNorm = errMsg "[Norm]"

errMsgTyCk :: Show t => String -> t -> ErrMsg
errMsgTyCk = errMsg "[TyCk]"