module Err (
    errMsg,
    errMsgNorm,
    errMsgTyCk,
    errMsgTop,
) where

import Lang (ErrMsg (..))

errMsg :: Show t => String -> String -> t -> ErrMsg
errMsg stage msg t = ErrMsg (stage ++ " " ++ msg ++ ": " ++ show t)

errMsgNorm :: Show t => String -> t -> ErrMsg
errMsgNorm = errMsg "[Norm]"

errMsgTyCk :: Show t => String -> t -> ErrMsg
errMsgTyCk = errMsg "[TyCk]"

errMsgTop :: Show t => String -> t -> ErrMsg
errMsgTop = errMsg "[Toplevel]"