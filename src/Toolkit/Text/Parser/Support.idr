module Toolkit.Text.Parser.Support

import Text.Lexer
import Text.Parser

%default total

public export
Rule : Type -> Type -> Type
Rule tok ty = Grammar (TokenData tok) True ty


public export
RuleEmpty : Type -> Type -> Type
RuleEmpty tok ty = Grammar (TokenData tok) False ty

export
eoi : (f : a -> Bool) -> RuleEmpty a ()
eoi f = do
    nextIs "Not End of Input" (f . tok)
    pure ()
