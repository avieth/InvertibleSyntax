{-|
Module      : InvertibleSyntax
Description : Parsers and printers defined simultaneously.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module InvertibleSyntax.InvertibleSyntax where

import Prelude hiding (id, (.))
import Control.Category
import Control.Applicative hiding (many)
import Control.Arrow
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Writer.Lazy
import Data.Monoid hiding (Sum(..), Product(..))
import Data.Functor.Identity
import Data.Functor.Contravariant
import Data.Bifunctor
import Data.Profunctor
import qualified Text.Parsec as P

-- | @InvertibleSyntax stream m s t@ means that we have, essentially:
--
--     @
--       print :: s -> Maybe stream
--       parse :: stream -> Maybe t
--       thru :: s -> t
--     @
--
--   and if we've done anything right, it should be the case that:
--
--     @
--       parse <=< print = Just . thru
--     @
--
--   That's to say, you have a compatible printer and parser, as well as
--   a function @s -> t@ which factors through that parser and printer.
--
--     @
--       input ---> symbolic ----> parsed ---> output
--                      |            ^
--                      |           /
--                      |          /
--                      |         /
--                      |        /
--                      |       /
--                      |      /
--                      |     /
--                      v    /
--                     stream
--     @
--
--
--   In the special case that @s ~ t@, we must have:
--
--     @
--       thru = id
--       parse <=< print = Just
--     @
--
--   This case inspires the name @InvertibleSyntax@, as it gives a parser and
--   printer for the same datatype, like a DSL for example.
--
--   Note that the printer is partial: not every input type will actually print!
--   That's because there are some cases in which a parser for some type @t@
--   cannot parse every member of @t@! Take an alphanumeric string for example.
--   If we need the left-inverse property of parse to print, then we just
--   cannot print the string "#" because this will never parse.
--
--   The form of this type isn't exactly like what was described above:
--   there is in general no @thru@ function, for if there were, we could not
--   implement @empty@ from @Alternative@. Instead, we have the printer
--   produce a @stream@ and a @parsed@ simultaneously, or nothing at all.
data InvertibleSyntax stream m input output where
    InvertibleSyntax
        :: (input -> symbolic)
        -> (symbolic -> Maybe (stream, parsed))  -- The printer.
        -> (P.ParsecT stream () m parsed)        -- The parser.
        -> (parsed -> output)
        -> InvertibleSyntax stream m input output

printer :: InvertibleSyntax stream m input output -> (input -> Maybe stream)
printer term = case term of
    InvertibleSyntax inp printer _ _ -> (fmap . fmap) fst (getOp (contramap inp (Op printer)))

parser :: InvertibleSyntax stream m input output -> P.ParsecT stream () m output
parser term = case term of
    InvertibleSyntax _ _ parser out -> fmap out parser

instance Profunctor (InvertibleSyntax stream m) where
    dimap l r term = case term of
        InvertibleSyntax inp printer parser out -> InvertibleSyntax
            (inp . l)
            (printer)
            (parser)
            (r . out)

instance Functor (InvertibleSyntax stream m s) where
    fmap = rmap

-- TODO formal proof that
--   1. pure x has left-inverse property
--   2. if x and y have left-inverse property, then so does x <*> y.
instance Monoid stream => Applicative (InvertibleSyntax stream m s) where
    -- Makes sense: u ~ t and we print nothing, consume no input.
    pure x = InvertibleSyntax (const x) (\x -> Just (mempty, x)) (pure x) (const x)
    -- What will the hidden @u@ become here? We have @s@ and @t@ fixed.
    -- Aha, yes; we must pair up both peculiar @u@s, which may be different
    -- for mf and mx, and do the application in the out function.
    mf <*> mx = case (mf, mx) of
        (InvertibleSyntax inpf printf parsef outf, InvertibleSyntax inpx printx parsex outx) ->
            InvertibleSyntax (\s -> (inpf s, inpx s)) (print) (parse) (\(f, x) -> (outf f) (outx x))
          where
            -- The next printer just sequences the two printers. Unlike the parser,
            -- it is *not* concerned with the function @f@ nor the point @x@; the
            -- point @u@ determines everything.
            print = \(uf, ux) -> bundle <$> printf uf <*> printx ux
              where
                bundle = \(mleft, xleft) (mright, xright) -> (mleft <> mright, (xleft, xright))
            -- For the parser... well that's easy, since Parsec has already
            -- defined the applicative.
            -- It's compatible with the above: consume what mf would print, then
            -- consume what mx would print.
            -- We throw them into a tuple so that our output function (rmap
            -- part of the formal profunctor) can handle the application.
            parse = (,) <$> parsef <*> parsex

instance Monoid stream => Alternative (InvertibleSyntax stream m s) where
    empty = InvertibleSyntax id (const Nothing) empty id
    left <|> right = case (left, right) of
        ( InvertibleSyntax inpLeft printLeft parseLeft outLeft
          , InvertibleSyntax inpRight printRight parseRight outRight 
          ) -> InvertibleSyntax inp print parse out
            where
              inp = \i -> (inpLeft i, inpRight i)
              print = \(symLeft, symRight) ->
                              (fmap . fmap) Left (printLeft symLeft)
                          <|> (fmap . fmap) Right (printRight symRight)
              parse = (Left <$> P.try parseLeft) P.<|> (Right <$> P.try parseRight)
              out = either outLeft outRight

-- We shall need this in our implementation of (>>=).
-- For bind, the internal type @u@ cannot become, like for applicative, a pair
-- of the two output types, because we don't know what the second one
-- will be until we evaluate the function @k@. To workaround this, we hide
-- the internal @u@ of the result of @k@ inside @IntermediateBind@, caching
-- as well the function necessary to bring us back to some known type @t@.
data IntermediateBind stream t where
    IntermediateBind :: u -> (u -> t) -> IntermediateBind stream t

-- TODO formal proof that
--   1. return x has left-inverse property (see Applicative instance).
--   2. if x has left-inverse property, and for all y, k y has left-inverse
--      property, then so does x >>= k.
instance Monoid stream => Monad (InvertibleSyntax stream m input) where
    return = pure
    x >>= k = case x of
        InvertibleSyntax inpx printx parsex outx ->
            InvertibleSyntax inp print parse out
          where
            -- We must preserve the input so that we can feed it to k.
            -- This is just @first@ in the (->) arrow.
            inp = \i -> (inpx i, i)

            print = \(symx, input) -> do (printedx, parsedx) <- printx symx
                                         case k (outx parsedx) of
                                             InvertibleSyntax inpk printk parsek outk -> do
                                                 (printedk, parsedk) <- printk (inpk input)
                                                 return (printedx <> printedk, IntermediateBind parsedk outk)

            parse = do ex <- parsex
                       case k (outx ex) of
                           InvertibleSyntax inpk printk parsek outk -> do
                               ek <- parsek
                               return (IntermediateBind ek outk)

            out = \intermediateBind -> case intermediateBind of
                IntermediateBind x f -> f x

class Dump stream t where
    dump :: t -> stream

instance Dump [Char] Char where
    dump = pure

instance Dump [Char] [Char] where
    dump = id

many
    :: ( Monad m
       , Monoid stream
       )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m [s] [t]
many invs = case invs of
    InvertibleSyntax oldInp oldPrint oldParse oldOut ->
        InvertibleSyntax inp print parse out
      where
        -- The internal terms are simply wrapped up in lists.
        --   symbolic -> [symbolic]
        --   parsed -> [parsed]
        inp = fmap oldInp
        out = fmap oldOut
        print = \xs -> concatFsts . unzip <$> traverse oldPrint xs
          where
            concatFsts = \(xs, ys) -> (mconcat xs, ys)
        parse = P.many oldParse

many1
    :: ( Monad m
       , Monoid stream
       )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m (s, [s]) (t, [t])
many1 invs = (,) <$> (lmap fst invs) <*> (lmap snd (many invs))

-- Note how the separator must have the same input type as the separated!
-- I suspect this will not be a problem, since the separator is typically a
-- fixed thing which doesn't depend on input: you can print it without giving
-- any data.
sepBy1
    :: ( Monad m
       , Monoid stream
       )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m s sept
    -> InvertibleSyntax stream m (s, [s]) (t, [t])
sepBy1 invsP invsSep = do x <- lmap fst invsP
                          xs <- lmap snd (many (invsSep >> invsP))
                          return (x, xs)

{-
sepBy
    :: ( Monad m
       , Monoid stream
       )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m s sept
    -> InvertibleSyntax stream m [s] [t]
sepBy invsP invsSep = bundle (sepBy1 invsP invsSep) <|> pure []
  where
    bundle = dimap (\(x, xs) -> x : xs) (\xs -> (take 1 xs, drop 1 xs))
-}

-- Choose the printer according to the input binary sum.
-- Parser tries the left first and then the right in case it doesn't pass,
-- and indicates which one passed.
choice
    :: ( Functor m
       )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m s' t'
    -> InvertibleSyntax stream m (Either s s') (Either t t')
choice left right = case (left, right) of
    ( InvertibleSyntax inpLeft printLeft parseLeft outLeft
      , InvertibleSyntax inpRight printRight parseRight outRight
      ) ->
        InvertibleSyntax inp print parse out
      where
        -- Observe the similarity to the definition of many: there we fmap,
        -- here we bimap. What else can we achieve just by swapping this
        -- function?
        inp = bimap inpLeft inpRight
        out = bimap outLeft outRight
        -- fmap . fmap so that we go through the maybe and into the second
        -- component of the tuple, where the internal @parsed@ type lives.
        print = either ((fmap . fmap) Left) ((fmap . fmap) Right) . bimap printLeft printRight
        parse = (P.try (fmap Left parseLeft)) P.<|> (P.try (fmap Right parseRight))

satisfy
    :: ( P.Stream stream m Char
       , Dump stream Char
       )
    => (Char -> Bool)
    -> InvertibleSyntax stream m Char Char
satisfy p = InvertibleSyntax id print parse id
  where
    print = \c -> if p c then Just (dump c, c) else Nothing
    parse = P.satisfy p

oneOf
    :: ( P.Stream stream m Char
       , Dump stream Char
       )
    => [Char]
    -> InvertibleSyntax stream m Char Char
oneOf cs = satisfy (\c -> elem c cs)

noneOf
    :: ( P.Stream stream m Char
       , Dump stream Char
       )
    => [Char]
    -> InvertibleSyntax stream m Char Char
noneOf cs = satisfy (\c -> not (elem c cs))

-- symbolic type is Char; parsed type is Char.
char :: (P.Stream stream m Char, Dump stream Char) => Char -> InvertibleSyntax stream m s Char
char c = InvertibleSyntax (const c) (\c -> Just (dump c, c)) (P.char c) id

-- symbolic type is Char; parsed type is Char.
anyChar :: (P.Stream stream m Char, Dump stream Char) => InvertibleSyntax stream m Char Char
anyChar = InvertibleSyntax id (\c -> Just (dump c, c)) P.anyChar id

-- symbolic type is String; parsed type is String.
string
    :: ( P.Stream stream m Char
       , Dump stream String
       )
    => String
    -> InvertibleSyntax stream m s String
string str = InvertibleSyntax (const str) (\str -> Just (dump str, str)) (P.string str) id

-- symbolic type is String; parsed type is String.
anyString
    :: ( P.Stream stream m Char
       , Dump stream Char
       , Monoid stream
       , Monad m
       )
    => InvertibleSyntax stream m String String
anyString = many anyChar

anyQuotedString
    :: ( P.Stream stream m Char
       , Dump stream [Char]
       , Monoid stream
       , Monad m
       )
    => InvertibleSyntax stream m String String
anyQuotedString = InvertibleSyntax id printer parser id
  where
    printer str = Just (dump (concat ["\"", escaped, "\""]), str)
      where escaped = do x <- str
                         if x == '\"'
                         then "\\\""
                         else return x
    parser = do P.char '\"'
                s <- middle
                P.char '\"'
                return s
    middle = P.many ((P.try escaped) P.<|> (P.try notEscaped))
    escaped = do c <- P.char '\\'
                 P.char '\"'
    notEscaped = do c <- P.anyChar
                    if c == '\"'
                    then mzero
                    else return c

-- Indicate that this printer should be used for printing, but its parser is
-- optional. Example use case: optional semicolon at the end of a line, which
-- should be placed when printed but is not necessary when parsed.
-- 
-- Contrast with option, which makes it optional for parsing but does not
-- print it.
--
-- This demonstrates the utility of the @symbolic@ and @parsed@ skolem type
-- variables. The input to symbolic function and the printer can remain
-- unchanged, because the input and symbolic *types* have not changed.
-- The parsed type, on the other hand, *has* changed: it has a Maybe out in
-- front. The liaison is easily updated by fmapping Just.
pretty
    :: ( Monoid stream, P.Stream stream m tok )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m s (Maybe t)
pretty invs = case invs of
    InvertibleSyntax oldInp oldPrinter oldParser oldOut ->
        InvertibleSyntax oldInp newPrinter newParser (fmap oldOut)
          where
            newPrinter = \symb -> do (printed, parsed) <- oldPrinter symb
                                     return (printed, Just parsed)
            newParser = P.optionMaybe oldParser

optional
    :: ( Monoid stream, P.Stream stream m tok )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m r (Maybe t)
optional invs = case invs of
    InvertibleSyntax oldInp oldPrinter oldParser oldOut ->
        InvertibleSyntax newInp newPrinter newParser (fmap oldOut)
          where
            newInp = const ()
            newPrinter = const (Just (mempty, Nothing))
            newParser = P.optionMaybe oldParser

-- Print: print both in order.
-- Parse: take at least one or both, but fail if neither.
-- Study the output type: it's either both or one of them.
tryTwo
    :: ( _ )
    => InvertibleSyntax stream m s t
    -> InvertibleSyntax stream m s u
    -> InvertibleSyntax stream m s (Either (t, u) (Either t u))
tryTwo left right = case (left, right) of
    (   InvertibleSyntax inpLeft printLeft parseLeft outLeft
      , InvertibleSyntax inpRight printRight parseRight outRight
      ) -> InvertibleSyntax inp print parse out
      where
        inp = \s -> (inpLeft s, inpRight s)
        print = \(left, right) -> do (printedLeft, parsedLeft) <- printLeft left
                                     (printedRight, parsedRight) <- printRight right
                                     return (printedLeft <> printedRight, Left (parsedLeft, parsedRight))
        parse = do l <- P.optionMaybe parseLeft
                   r <- P.optionMaybe parseRight
                   case (l, r) of
                       (Nothing, Nothing) -> mzero
                       (Just x, Just y) -> return $ Left (x, y)
                       (Just x, Nothing) -> return $ Right (Left x)
                       (Nothing, Just y) -> return $ Right (Right y)
        out = \term -> case term of
                           Left (l, r) -> Left (outLeft l, outRight r)
                           Right (Left l) -> Right (Left (outLeft l))
                           Right (Right r) -> Right (Right (outRight r))
