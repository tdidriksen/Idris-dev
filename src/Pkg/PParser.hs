{-# LANGUAGE CPP #-}
#if !(MIN_VERSION_base(4,8,0))
{-# LANGUAGE OverlappingInstances #-}
#endif
module Pkg.PParser where

import Text.Trifecta hiding (span, charLiteral, natural, symbol, char, string, whiteSpace)

import Idris.Core.TT
import Idris.REPL
import Idris.AbsSyntaxTree
import Idris.ParseHelpers hiding (stringLiteral)
import Idris.CmdOptions

import Control.Monad.State.Strict
import Control.Applicative

import Util.System

type PParser = StateT PkgDesc IdrisInnerParser

data PkgDesc = PkgDesc {
    pkgname     :: String
  , libdeps     :: [String]
  , objs        :: [String]
  , makefile    :: Maybe String
  , idris_opts  :: [Opt]
  , sourcedir   :: String
  , modules     :: [Name]
  , idris_main  :: Name
  , execout     :: Maybe String
  , idris_tests :: [Name]
  } deriving (Show)

instance HasLastTokenSpan PParser where
  getLastTokenSpan = return Nothing

#if MIN_VERSION_base(4,8,0)
instance {-# OVERLAPPING #-} TokenParsing PParser where
#else
instance TokenParsing PParser where
#endif
  someSpace = many (simpleWhiteSpace <|> singleLineComment <|> multiLineComment) *> pure ()

defaultPkg :: PkgDesc
defaultPkg = PkgDesc "" [] [] Nothing [] "" [] (sUN "") Nothing []

parseDesc :: FilePath -> IO PkgDesc
parseDesc fp = do
    p <- readFile fp
    case runparser pPkg defaultPkg fp p of
      Failure err -> fail (show err)
      Success x -> return x

pPkg :: PParser PkgDesc
pPkg = do
    reserved "package"; p <- fst <$> identifier
    st <- get
    put (st { pkgname = p })
    some pClause
    st <- get
    eof
    return st

pClause :: PParser ()
pClause = do reserved "executable"; lchar '=';
             exec <- fst <$> iName []
             st <- get
             put (st { execout = Just (show exec) })
      <|> do reserved "main"; lchar '=';
             main <- fst <$> iName []
             st <- get
             put (st { idris_main = main })
      <|> do reserved "sourcedir"; lchar '=';
             src <- fst <$> identifier
             st <- get
             put (st { sourcedir = src })
      <|> do reserved "opts"; lchar '=';
             opts <- stringLiteral
             st <- get
             let args = pureArgParser (words opts)
             put (st { idris_opts = args ++ idris_opts st })
      <|> do reserved "pkgs"; lchar '=';
             ps <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             let pkgs = pureArgParser $ concatMap (\x -> ["-p", x]) ps
             put (st {idris_opts = pkgs ++ idris_opts st})
      <|> do reserved "modules"; lchar '=';
             ms <- sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put (st { modules = modules st ++ ms })
      <|> do reserved "libs"; lchar '=';
             ls <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { libdeps = libdeps st ++ ls })
      <|> do reserved "objs"; lchar '=';
             ls <- sepBy1 (fst <$> identifier) (lchar ',')
             st <- get
             put (st { objs = libdeps st ++ ls })
      <|> do reserved "makefile"; lchar '=';
             mk <- fst <$> iName []
             st <- get
             put (st { makefile = Just (show mk) })
      <|> do reserved "tests"; lchar '=';
             ts <- sepBy1 (fst <$> iName []) (lchar ',')
             st <- get
             put st { idris_tests = idris_tests st ++ ts }
