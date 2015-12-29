-----------------------------------------------------------------------------
--
-- Module      :  Language.PureScript.Parser.Kinds
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- A parser for kinds
--
-----------------------------------------------------------------------------

module Language.PureScript.Parser.Kinds (
    parseKind
) where

import Prelude ()
import Prelude.Compat

import Language.PureScript.Kinds
import Language.PureScript.Parser.Common
import Language.PureScript.Parser.Lexer
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P

parseStar :: TokenParser Kind
parseStar = const Star <$> (symbol' "*" P.<|> uname' "Type")

parseBang :: TokenParser Kind
parseBang = const Bang <$> (symbol' "!" P.<|> uname' "Effect")

parseConstraint :: TokenParser Kind
parseConstraint = const ConstraintKind <$> (symbol' "?" P.<|> uname' "Constraint")

parseKindVar :: TokenParser Kind
parseKindVar = KindVar <$> lname

parseTypeAtom :: TokenParser Kind
parseTypeAtom = indented *> P.choice
            [ parseStar
            , parseBang
            , parseConstraint
            , parseKindVar
            , parens parseKind
            ]
-- |
-- Parse a kind
--
parseKind :: TokenParser Kind
parseKind = P.buildExpressionParser operators parseTypeAtom P.<?> "kind"
  where
  operators = [ [ P.Prefix ((symbol' "#" P.<|> uname' "Row") >> return Row) ]
              , [ P.Infix (rarrow >> return FunKind) P.AssocRight ] ]
