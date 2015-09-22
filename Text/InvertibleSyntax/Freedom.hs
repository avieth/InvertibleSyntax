{-|
Module      : InvertibleSyntax.Freedom
Description : Generic InvertibleSyntax terms for Freedom-style datatypes.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}

module Text.InvertibleSyntax.Freedom (

      invsynSum
    , (\+\)

    , invsynRec
    , invsynFix

    ) where

import Prelude hiding ((+))
import Data.Profunctor
import Data.Functor.Identity
import Text.InvertibleSyntax
import Control.Freedom.Construction
import qualified Text.Parsec as P

invsynSum
    :: ( Functor m )
    => InvertibleSyntax stream m (f h s t) (f h s t)
    -> InvertibleSyntax stream m (g h s t) (g h s t)
    -> InvertibleSyntax stream m ((f + g) h s t) ((f + g) h s t)
invsynSum invsF invsG = dimap deconstruct reconstruct (choice invsF invsG)
  where
    deconstruct :: ((f + g) h s t) -> Either (f h s t) (g h s t)
    deconstruct term = case term of
        FSumL f -> Left f
        FSumR g -> Right g
    reconstruct :: Either (f h s t) (g h s t) -> ((f + g) h s t)
    reconstruct term = case term of
        Left f -> FSumL f
        Right g -> FSumR g

infixr 8 \+\
(\+\)
    :: ( Functor m )
    => InvertibleSyntax stream m (f h s t) (f h s t)
    -> InvertibleSyntax stream m (g h s t) (g h s t)
    -> InvertibleSyntax stream m ((f + g) h s t) ((f + g) h s t)
(\+\) = invsynSum

invsynRec
    :: InvertibleSyntax stream m (h s t) (h s t)
    -> InvertibleSyntax stream m (Rec h s t) (Rec h s t)
invsynRec invs = dimap deconstruct reconstruct invs
  where
    deconstruct :: Rec h s t -> h s t
    deconstruct term = case term of
        Rec x -> x
    reconstruct :: h s t -> Rec h s t
    reconstruct = Rec

invsynFix
    :: InvertibleSyntax stream m (f (Fix f) s t) (f (Fix f) s t)
    -> InvertibleSyntax stream m (Fix f s t) (Fix f s t)
invsynFix invs = dimap deconstruct reconstruct invs
  where
    deconstruct :: Fix f s t -> f (Fix f) s t
    deconstruct = runFix
    reconstruct :: f (Fix f) s t -> Fix f s t
    reconstruct = Fix

{-
exPure :: InvertibleSyntax String Identity (Pure h () String) (Pure h () String)
exPure = do string "Pure ("
            str <- lmap (\(Pure f) -> f ()) anyString
            string ")"
            return (Pure (const str))

exNone :: InvertibleSyntax String Identity (None h s t) (None h s t)
exNone = do string "None"
            return None


type Ex1 = Pure + None

exSum :: InvertibleSyntax String Identity (Fix Ex1 () String) (Fix Ex1 () String)
exSum = invsynFix (exPure + exNone)

term1 :: Fix Ex1 () String
term1 = inj (Pure (const "foo"))

term2 :: Fix Ex1 () String
term2 = inj None

data Sequence' left right h s t where
    Sequence' :: left h () () -> right h () () -> Sequence' left right h () ()

-- Consists of sequences of 0 or more Pure () () terms.
type Ex2 = Sequence' Pure Rec + None

-- A generic Sequence' parser with statements delimeted by a mandatory
-- semicolon.
exSequence'
    :: ( )
    => InvertibleSyntax String Identity (left h () ()) (left h () ())
    -> InvertibleSyntax String Identity (right h () ()) (right h () ())
    -> InvertibleSyntax String Identity (Sequence' left right h () ()) (Sequence' left right h () ())
exSequence' left right = do l <- lmap ldeconstruct left
                            optional (many (char ' '))
                            string ";"
                            optional (many (char ' '))
                            pretty (char '\n')
                            optional (many (char ' '))
                            r <- lmap rdeconstruct right
                            optional (many (char ' '))
                            string ";"
                            optional (many (char ' '))
                            pretty (char '\n')
                            optional (many (char ' '))
                            return (Sequence' l r)
  where
    ldeconstruct :: Sequence' left right h () () -> left h () ()
    ldeconstruct term = case term of
        Sequence' x _ -> x
    rdeconstruct :: Sequence' left right h () () -> right h () ()
    rdeconstruct term = case term of
        Sequence' _ x -> x

-- A generic Sequence' parser with statements delimeted by either a semicolon
-- or a newline or both.
--
-- Notice how we demand at least one of the semicolon and newline. It's an
-- invertible syntax which always prints ';\n'. 
exSequenceOptionalSemicolon'
    :: ( )
    => InvertibleSyntax String Identity (left h () ()) (left h () ())
    -> InvertibleSyntax String Identity (right h () ()) (right h () ())
    -> InvertibleSyntax String Identity (Sequence' left right h () ()) (Sequence' left right h () ())
exSequenceOptionalSemicolon' left right = do l <- lmap ldeconstruct left
                                             delimeter
                                             optional (many (char ' '))
                                             r <- lmap rdeconstruct right
                                             delimeter
                                             optional (many (char ' '))
                                             return (Sequence' l r)
  where
    delimeter = tryTwo (optional (many (char ' ')) >> pretty (char ';'))
                       (optional (many (char ' ')) >> pretty (char '\n'))
    ldeconstruct :: Sequence' left right h () () -> left h () ()
    ldeconstruct term = case term of
        Sequence' x _ -> x
    rdeconstruct :: Sequence' left right h () () -> right h () ()
    rdeconstruct term = case term of
        Sequence' _ x -> x



term3 :: Fix Ex2 () ()
term3 = inj (Sequence' (Pure (const ())) (Rec (inj (Sequence' (Pure (const ())) (Rec (inj None))))))

exPureUnit :: InvertibleSyntax String Identity (Pure h () ()) (Pure h () ())
exPureUnit = do string "Pure"
                return (Pure (const ()))

ex2 :: InvertibleSyntax String Identity (Fix Ex2 () ()) (Fix Ex2 () ())
ex2 = invsynFix (exSequence' exPureUnit (exRec ex2) + exNone)

ex3 :: InvertibleSyntax String Identity (Fix Ex2 () ()) (Fix Ex2 () ())
ex3 = invsynFix (exSequenceOptionalSemicolon' exPureUnit (exRec ex3) + exNone)
-}
