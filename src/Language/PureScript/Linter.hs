-- |
-- This module implements a simple linting pass on the PureScript AST.
--
module Language.PureScript.Linter (lint, module L) where

import Debug.Trace (traceShow)

import Prelude.Compat
import Protolude (ordNub)

import Control.Monad.Writer.Class

import Data.List ((\\))
import Data.Maybe (mapMaybe)
import Data.Monoid
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T

import Language.PureScript.AST
import Language.PureScript.Crash
import Language.PureScript.Errors
import Language.PureScript.Linter.Exhaustive as L
import Language.PureScript.Linter.Imports as L
import Language.PureScript.Names
import Language.PureScript.Types

{-
  data Expr =
      Var Name
    | App Expr Expr
    | Let Name Expr

  data Scope = Scope { freeVars :: Set Name, unusedVars :: Set (SrcPosInfo, Name) }
  -- or: scope :: Expr -> Scope
  freeVars :: Expr -> Set Name
  freeVars expr =
    case expr of
      Var n -> S.singleton n
      App f x -> S.union (freeVars f) (freeVars x)
      Let n x inY -> S.union (fv x) (S.delete n (fv inY))

  unusedVars :: Expr -> Set Name
  unusedVars expr =
    case expr of
      Let n x y ->
        if S.member n (fv y)
          then -- ... used
          else -- ... not-used
-}


-- | Lint the PureScript AST.
-- |
-- | Right now, this pass only performs a shadowing check.
lint :: forall m. (MonadWriter MultipleErrors m) => Module -> m ()
lint (Module _ _ mn ds _) = censor (addHint (ErrorInModule mn)) $ mapM_ lintDeclaration ds
  where
  moduleNames :: S.Set Ident
  moduleNames = S.fromList (ordNub (mapMaybe getDeclIdent ds))

  getDeclIdent :: Declaration -> Maybe Ident
  getDeclIdent (PositionedDeclaration _ _ d) = getDeclIdent d
  getDeclIdent (ValueDeclaration ident _ _ _) = Just ident
  getDeclIdent (ExternDeclaration ident _) = Just ident
  getDeclIdent (TypeInstanceDeclaration ident _ _ _ _) = Just ident
  getDeclIdent (BindingGroupDeclaration _) = internalError "lint: binding groups should not be desugared yet."
  getDeclIdent _ = Nothing

  lintDeclaration :: Declaration -> m ()
  lintDeclaration = tell . f
    where
    (warningsInDecl, _, _, _, _) =
      everythingWithScope
        (\_ _ -> mempty)
        (\i e -> checkShadowedInE i e <> checkUnusedInE e)
        stepB
        (\_ _ -> mempty)
        stepDo

    f :: Declaration -> MultipleErrors
    f (PositionedDeclaration pos _ dec) = addHint (PositionedError pos) (f dec)
    f (TypeClassDeclaration name args _ _ decs) = addHint (ErrorInTypeClassDeclaration name) (foldMap (f' (S.fromList $ fst <$> args)) decs)
    f dec = f' S.empty dec

    f' :: S.Set Text -> Declaration -> MultipleErrors
    f' s (PositionedDeclaration pos _ dec) = addHint (PositionedError pos) (f' s dec)
    f' s dec@(ValueDeclaration name _ _ _) = addHint (ErrorInValueDeclaration name) (warningsInDecl moduleNames dec <> checkTypeVarsInDecl s dec)
    f' s (TypeDeclaration name ty) = addHint (ErrorInTypeDeclaration name) (checkTypeVars s ty)
    f' s dec = warningsInDecl moduleNames dec <> checkTypeVarsInDecl s dec

    checkUnusedInE :: Expr -> MultipleErrors -- Pos would be nice.
    checkUnusedInE expr =
      if S.null unused
        then mempty
        else
          singleError . ErrorMessage [] . UnusedVar .
            T.intercalate ", " . map showIdent . S.toList $
              unused
      where
        unused = S.difference introduced consumed
        (introduced, consumed) = go mempty mempty expr
        go :: S.Set Ident -> S.Set Ident -> Expr -> (S.Set Ident, S.Set Ident)
        go intrd consd te = case te of
          Literal (ArrayLiteral es) -> stop -- TODO: Fold on sub-expressions w/ <>.
          Literal (ObjectLiteral eMap) -> stop
          Literal _ -> stop
          UnaryMinus e -> same e
          BinaryNoParens e1 e2 e3 -> stop
          Parens e -> same e
          Accessor _ e -> same e
          ObjectUpdate e eMap -> stop
          Abs (Left i) e -> stop
          Abs (Right b) e -> stop
          App e1 e2 -> stop
          Var (Qualified mm i) -> stop
          Op _ -> stop -- No operator declarations inside an expression
          IfThenElse ep e1 e2 -> stop
          Constructor _ -> stop -- WTF is this. It's not using a constructor to create a value; that would need Expr somewhere.
          Case es cases -> stop -- [CaseAlternative] needs exploring as well.
          TypedValue _ e _ -> stop
          Let decs e -> stop
          {-
            case decs of
              ValueDeclaration i _ bs ee -> stop
              PositionedDeclaration _ _ (ValueDeclaration i _ bs ee) -> stop
              _ -> stop
          -}
          Do dos -> stop -- Value, Bind, Let and PositionedElement(?) fun.
          TypeClassDictionaryConstructorApp _ e -> same e
          TypeClassDictionary _ _ _ -> stop -- TODO: I _don't_ think the Ident in here is for us.
          TypeClassDictionaryAccessor _ i -> stop -- TODO: ...?
          DeferredDictionary _ _ -> stop
          AnonymousArgument -> stop
          Hole _ -> stop
          PositionedValue _ _ e -> traceShow e $ same e -- TODO: Use the pos info.
          where
            stop = (mempty, mempty)
            same = go intrd consd

    checkShadowedInE :: S.Set Ident -> Expr -> MultipleErrors
    checkShadowedInE s (Abs (Left name) _) | name `S.member` s = errorMessage (ShadowedName name)
    checkShadowedInE s (Let ds' _) = foldMap go ds'
      where
      go d | Just i <- getDeclIdent d
           , i `S.member` s = errorMessage (ShadowedName i)
           | otherwise = mempty
    checkShadowedInE _ _ = mempty

    stepB :: S.Set Ident -> Binder -> MultipleErrors
    stepB s (VarBinder name) | name `S.member` s = errorMessage (ShadowedName name)
    stepB s (NamedBinder name _) | name `S.member` s = errorMessage (ShadowedName name)
    stepB _ _ = mempty

    stepDo :: S.Set Ident -> DoNotationElement -> MultipleErrors
    stepDo s (DoNotationLet ds') = foldMap go ds'
      where
      go d | Just i <- getDeclIdent d
           , i `S.member` s = errorMessage (ShadowedName i)
           | otherwise = mempty
    stepDo _ _ = mempty

  checkTypeVarsInDecl :: S.Set Text -> Declaration -> MultipleErrors
  checkTypeVarsInDecl s d = let (f, _, _, _, _) = accumTypes (checkTypeVars s) in f d

  checkTypeVars :: S.Set Text -> Type -> MultipleErrors
  checkTypeVars set ty = everythingWithContextOnTypes set mempty mappend step ty <> findUnused ty
    where
    step :: S.Set Text -> Type -> (S.Set Text, MultipleErrors)
    step s (ForAll tv _ _) = bindVar s tv
    step s _ = (s, mempty)
    bindVar :: S.Set Text -> Text -> (S.Set Text, MultipleErrors)
    bindVar = bind ShadowedTypeVar
    findUnused :: Type -> MultipleErrors
    findUnused ty' =
      let used = usedTypeVariables ty'
          declared = everythingOnTypes (++) go ty'
          unused = ordNub declared \\ ordNub used
      in foldl (<>) mempty $ map (errorMessage . UnusedTypeVar) unused
      where
      go :: Type -> [Text]
      go (ForAll tv _ _) = [tv]
      go _ = []

  bind :: (Ord a) => (a -> SimpleErrorMessage) -> S.Set a -> a -> (S.Set a, MultipleErrors)
  bind mkError s name | name `S.member` s = (s, errorMessage (mkError name))
                      | otherwise = (S.insert name s, mempty)
