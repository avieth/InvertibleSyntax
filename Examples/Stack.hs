{-|
Module      : Examples.Stack
Description : Stack DSL example with invertible syntax.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Examples.Stack where

import Data.Functor.Identity
import Data.Profunctor
import Control.Freedom.Construction
import InvertibleSyntax.InvertibleSyntax
import InvertibleSyntax.Freedom

type FStack = (Sequence (Push Pure + Pop + Add) Rec) + None
type Stack = Fix FStack

data Push f h s t where
    Push :: f h () Integer -> Push f h () ()

data Pop h s t where
    Pop :: Pop h () ()

data Add h s t where
    Add :: Add h () ()

invsynNumber :: InvertibleSyntax String Identity (Pure h () Integer) (Pure h () Integer)
invsynNumber = dimap deconstruct reconstruct unsignedDecimal
  where
    deconstruct :: Pure h () Integer -> Integer
    deconstruct term = case term of
        Pure f -> f ()
    reconstruct :: Integer -> Pure h () Integer
    reconstruct = Pure . const

invsynPush
    :: InvertibleSyntax String Identity (f h () Integer) (f h () Integer)
    -> InvertibleSyntax String Identity (Push f h () ()) (Push f h () ())
invsynPush invsyn = do
    string "push "
    optional (many (char ' '))
    dimap deconstruct reconstruct invsyn
  where
    deconstruct :: Push f h s () -> f h s Integer
    deconstruct term = case term of
        Push subTerm -> subTerm
    reconstruct :: f h () Integer -> Push f h () ()
    reconstruct = Push

invsynPop :: InvertibleSyntax String Identity (Pop h () ()) (Pop h () ())
invsynPop = do 
    string "pop"
    return Pop

invsynAdd :: InvertibleSyntax String Identity (Add h () ()) (Add h () ())
invsynAdd = do
    string "add"
    return Add

invsynSequenceSemicolon
    :: InvertibleSyntax String Identity (left h s ()) (left h s ())
    -> InvertibleSyntax String Identity (right h s t) (right h s t)
    -> InvertibleSyntax String Identity (Sequence left right h s t) (Sequence left right h s t)
invsynSequenceSemicolon left right = do
    l <- lmap getLeft left
    optional (many1 (char ' '))
    char ';'
    optional (many1 (char ' '))
    pretty (char '\n')
    r <- lmap getRight right
    return (Sequence l r)
  where
    getLeft :: Sequence left right h s t -> left h s ()
    getLeft term = case term of
        Sequence left _ -> left
    getRight :: Sequence left right h s t -> right h s t
    getRight term = case term of
        Sequence _ right -> right

invsynNone :: InvertibleSyntax String Identity (None h s t) (None h s t)
invsynNone = return None

-- The construction of this parser mirrors the definition of FStack; they
-- have precisely the same form.
invsynFStack :: InvertibleSyntax String Identity (FStack (Fix FStack) () ()) (FStack (Fix FStack) () ())
invsynFStack =
        ( invsynSequenceSemicolon
              ((invsynPush invsynNumber) \+\ invsynPop \+\ invsynAdd)
              (invsynRec (invsynFix invsynFStack)))
    \+\ invsynNone
