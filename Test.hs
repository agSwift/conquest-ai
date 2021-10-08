{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Test where

import Control.DeepSeq
import Control.Exception
import System.Environment
import System.IO
import System.Timeout (timeout)
import Control.Monad
import Unsafe.Coerce
import Data.List (intercalate)
import System.Directory
import System.FilePath
import Control.Monad.Trans.Writer
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class (lift)

data Test input result = input :=> result
  deriving (Show, Read)

apply :: (i -> r) -> Test i r -> Test i r
apply f (i :=> r) = i :=> f i

type Result = (String, Int, Int)

data LogLevel = Verbose | Silent
  deriving Eq

type TestM a = WriterT [Result] (ReaderT LogLevel IO) a

runTests :: TestM a -> IO a
runTests thing_inside = do
  args <- getArgs
  let lvl = case args of
              ("-v" : _) -> Verbose
              _ -> Silent
  (r, results) <- runReaderT (runWriterT thing_inside) lvl
  printResults lvl results
  return r

forceTest :: NFData b => Test a b -> IO (Test a (Either SomeException b))
forceTest t@(a :=> b) = timeout' (1 * 10^6) (let !_ = force b in return (a :=> Right b))  -- wait a second
  `catch` (\(e :: SomeException) -> return (a :=> Left e))
  where timeout' :: Int -> IO a -> IO a
        timeout' n thing_inside =
          timeout n thing_inside >>= \case
            Nothing -> error "timeout"
            Just a -> pure a

single :: String -> Int -> Int -> TestM ()
single name score possible
  = tell [(name, score, possible)]

test
  :: (Show i, Show r, NFData r)
  => String
  -> (i -> r)
  -> (r -> r -> Bool)
  -> [Test i r]
  -> TestM ()
test name f cmp fp = do
  lvl <- lift ask
  result <- lift $ lift $ doTest lvl name f cmp fp
  tell [result]

testFromFile
  :: (Read i, Show i, Show r, Read r, NFData r)
  => String
  -> (i -> r)
  -> (r -> r -> Bool)
  -> FilePath
  -> TestM ()
testFromFile name f cmp fp = do
  lvl <- lift ask
  result <- lift $ lift $ doTestFromFile lvl name f cmp fp
  tell [result]

doTestFromFile
  :: (Read i, Show i, Show r, Read r, NFData r)
  => LogLevel
  -> String
  -> (i -> r)
  -> (r -> r -> Bool)
  -> FilePath
  -> IO Result
doTestFromFile lvl name f cmp fp = do
  tests <- map read . lines <$> readFile fp
  outputs <- mapM forceTest (map (apply f) tests)
  result <- doTest lvl name f cmp tests
  when (lvl == Verbose) $ do
    let write_log = do
        tmp <- getTemporaryDirectory
        createDirectoryIfMissing True (tmp ++ takeDirectory fp)
        let res_file = tmp ++ fp
        writeFile res_file (unlines $ map show outputs)
        hPutStrLn stderr ("Output written to: " ++ res_file)
    write_log
      `catch` (\(_ :: SomeException) -> return ())
  return result

doTest
  :: (Show i, Show r, NFData r)
  => LogLevel
  -> String
  -> (i -> r)
  -> (r -> r -> Bool)
  -> [Test i r]
  -> IO Result
doTest lvl name f cmp tests = do
  outputs <- mapM forceTest (map (apply f) tests)
  let check _ (_ :=> Left _) = False
      check (_ :=> exp) (_ :=> Right act) = cmp exp act
      results = zipWith check tests outputs
      score = length (filter id results)
      possible = length tests
  when (lvl == Verbose) $
    forM_ (zip tests outputs) $ \(test, output) ->
      unless (check test output) $ do
        hPutStrLn stderr (replicate 80 '-')
        hPutStrLn stderr (grey ++ "Error in " ++ reset ++ name ++ grey ++ " for test case: " ++ show (input test) ++ reset)
        hPutStrLn stderr (grey ++ "Expected: " ++ green ++ show (result test) ++ grey ++ " Got: " ++ red ++ show (result output) ++ reset)
  return (name, score, possible)

printResults :: LogLevel -> [Result] -> IO ()
printResults lvl results = do
  when (lvl == Verbose) $ do
    hPutStrLn stderr (replicate 80 '-')
    hPutStrLn stderr "Test summary:\n "
    hPutStrLn stderr (prettyTestResult results)
  putStrLn (jsonTestResult results)

result :: Test i r -> r
result (_ :=> r) = r

input :: Test i r -> i
input (i :=> _) = i

prettyTestResult :: [Result] -> String
prettyTestResult results = unlines (map showResult results)
  where
    tag_len (tag, _, _) = length tag
    max_tag_len = maximum (map tag_len results)
    width = max_tag_len + 20
    showResult (name, score, possible)
      = let colour = if score == possible then green else red
        in  concat [ name, replicate (width - length name) ' ', colour, show score, "/", show possible, reset]

red,green,grey,reset :: String
red = "\x1b[31m"
green = "\x1b[32m"
grey = "\x1b[37m"
reset = "\x1b[0m"

jsonTestResult :: [Result] -> String
jsonTestResult results = "[" ++ intercalate ", " (map showResult results) ++ "]"
  where
    showKV k v = show k ++ ": " ++ show v
    showResult (name, score, possible)
      = concat [ "{"
               , intercalate ", " [ showKV "name" name
                                  , showKV "score" score
                                  , showKV "possible" possible
                                  ]
               , "}"
               ]
