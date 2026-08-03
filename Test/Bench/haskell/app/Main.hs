{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Prelude hiding (id)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Data.Bits (shiftR, xor)
import qualified Data.ByteString as BS
import Data.Int (Int32)
import Data.List (foldl')
import Data.ProtoLens (decodeMessage, defMessage, encodeMessage)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Word (Word8, Word32, Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Lens.Family2 ((&), (.~), (^.))
import Proto.Perf (Batch, Item, Meta)
import Proto.Perf_Fields
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)
import qualified Data.Vector as Vector

protoLensVersion :: String
protoLensVersion = "0.7.1.7"

protoLensRuntimeVersion :: String
protoLensRuntimeVersion = "0.7.0.8"

ghcVersion :: String
ghcVersion = "8.8.4"

fnvOffset :: Word64
fnvOffset = 14695981039346656037

fnvPrime :: Word64
fnvPrime = 1099511628211

hashByte :: Word64 -> Word8 -> Word64
hashByte hash value = (hash `xor` fromIntegral value) * fnvPrime

hashWord64 :: Word64 -> Word64 -> Word64
hashWord64 initial value = go 8 initial value
  where
    go :: Int -> Word64 -> Word64 -> Word64
    go 0 !hash _ = hash
    go count !hash !remaining =
      go (count - 1) (hashByte hash (fromIntegral remaining)) (remaining `shiftR` 8)

hashBytesWithLength :: Word64 -> BS.ByteString -> Word64
hashBytesWithLength hash bytes =
  BS.foldl' hashByte (hashWord64 hash (fromIntegral (BS.length bytes))) bytes

hashText :: Word64 -> Text.Text -> Word64
hashText hash = hashBytesWithLength hash . Text.encodeUtf8

hashBytes :: BS.ByteString -> Word64
hashBytes = BS.foldl' hashByte fnvOffset

metaFor :: Word64 -> Meta
metaFor i =
  (defMessage :: Meta)
    & source .~ Text.pack ("source-" ++ show (i `mod` 11))
    & createdAt .~ (1700000000 + i * 17)
    & active .~ (i `mod` 2 == 0)

itemFor :: Word64 -> Item
itemFor i =
  (defMessage :: Item)
    & id .~ fromIntegral i
    & name .~ Text.pack ("item-" ++ show i)
    & scores .~ [fromIntegral ((i + 1) * j - 19) :: Int32 | j <- [3 .. 10]]
    & payload .~ BS.pack
        [ fromIntegral ((i * 31 + j * 17 + 13) `mod` 251)
        | j <- [0 .. 47 + i `mod` 16]
        ]
    & meta .~ metaFor i
    & tags .~
        [ Text.pack ("tag-" ++ show (i `mod` 5))
        , Text.pack ("group-" ++ show (i `mod` 9))
        , Text.pack ("bucket-" ++ show (i `mod` 13))
        , Text.pack ("region-" ++ show (i `mod` 7))
        ]
    & note .~ Text.pack ("note-" ++ show (i `mod` 17) ++ "-" ++ show (i * 3))

batchFor :: Int -> Batch
batchFor count =
  (defMessage :: Batch)
    & items .~ map (itemFor . fromIntegral) [0 .. count - 1]
    & label .~ Text.pack ("batch-" ++ show count)

batchContentHash :: Batch -> Word64
batchContentHash batch =
  foldl' hashItem initial (batch ^. items)
  where
    initial =
      hashWord64
        (hashText fnvOffset (batch ^. label))
        (fromIntegral (length (batch ^. items)))

    hashItem :: Word64 -> Item -> Word64
    hashItem hash item =
      let hash1 = hashWord64 hash (fromIntegral (item ^. id))
          hash2 = hashText hash1 (item ^. name)
          itemScores = item ^. scores
          hash3 = hashWord64 hash2 (fromIntegral (length itemScores))
          hash4 = foldl'
            (\current score -> hashWord64 current (fromIntegral (fromIntegral score :: Word32)))
            hash3
            itemScores
          hash5 = hashBytesWithLength hash4 (item ^. payload)
          hash6 = case item ^. maybe'meta of
            Nothing -> hashByte hash5 0
            Just metadata ->
              let present = hashByte hash5 1
                  withSource = hashText present (metadata ^. source)
                  withCreatedAt = hashWord64 withSource (metadata ^. createdAt)
               in hashByte withCreatedAt (if metadata ^. active then 1 else 0)
          itemTags = item ^. tags
          hash7 = hashWord64 hash6 (fromIntegral (length itemTags))
          hash8 = foldl' hashText hash7 itemTags
       in hashText hash8 (item ^. note)

encodeNF :: Batch -> IO BS.ByteString
encodeNF batch = evaluate (force (encodeMessage batch))
{-# NOINLINE encodeNF #-}

decodeNF :: BS.ByteString -> IO Batch
decodeNF bytes = case decodeMessage bytes of
  Left errorText -> die errorText
  Right value -> evaluate (force value)
{-# NOINLINE decodeNF #-}

consumeBytes :: BS.ByteString -> Word64
consumeBytes bytes
  | BS.null bytes = 0
  | otherwise =
      fromIntegral (BS.length bytes)
        + fromIntegral (BS.head bytes)
        + fromIntegral (BS.last bytes)

consumeBatch :: Batch -> Word64
consumeBatch batch
  | Vector.null values = fromIntegral (Text.length (batch ^. label))
  | otherwise =
      fromIntegral (Vector.length values)
        + fromIntegral (Vector.head values ^. id)
        + fromIntegral (Vector.last values ^. id)
        + fromIntegral (Text.length (batch ^. label))
  where
    values = batch ^. vec'items

data Result = Result
  { dataSetupNs :: !Word64
  , inputSetupNs :: !Word64
  , firstNs :: !Word64
  , steadyNs :: !Word64
  , outputBytes :: !Word64
  , contentHash :: !Word64
  , outputHash :: !Word64
  , checksum :: !Word64
  }

runEncode :: Int -> Word64 -> Bool -> IO Result
runEncode itemCount iterations validate = do
  setupStart <- getMonotonicTimeNSec
  batch <- evaluate (force (batchFor itemCount))
  setupStop <- getMonotonicTimeNSec
  let expectedHash = batchContentHash batch

  firstStart <- getMonotonicTimeNSec
  first <- encodeNF batch
  firstStop <- getMonotonicTimeNSec

  steadyStart <- getMonotonicTimeNSec
  (!total, !lastValue) <- encodeLoop iterations (consumeBytes first) first batch
  steadyStop <- getMonotonicTimeNSec

  if validate
    then do
      decoded <- decodeNF lastValue
      if batchContentHash decoded == expectedHash
        then pure ()
        else die "haskell-binary encode content mismatch"
    else pure ()

  pure Result
    { dataSetupNs = setupStop - setupStart
    , inputSetupNs = 0
    , firstNs = firstStop - firstStart
    , steadyNs = steadyStop - steadyStart
    , outputBytes = fromIntegral (BS.length lastValue)
    , contentHash = expectedHash
    , outputHash = hashBytes lastValue
    , checksum = total
    }
  where
    encodeLoop 0 !total !lastValue _ = pure (total, lastValue)
    encodeLoop remaining !total _ batch = do
      bytes <- encodeNF batch
      encodeLoop (remaining - 1) (total + consumeBytes bytes) bytes batch

runDecode :: Int -> Word64 -> Bool -> IO Result
runDecode itemCount iterations validate = do
  setupStart <- getMonotonicTimeNSec
  batch <- evaluate (force (batchFor itemCount))
  setupStop <- getMonotonicTimeNSec
  let expectedHash = batchContentHash batch

  inputStart <- getMonotonicTimeNSec
  input <- encodeNF batch
  inputStop <- getMonotonicTimeNSec

  firstStart <- getMonotonicTimeNSec
  first <- decodeNF input
  firstStop <- getMonotonicTimeNSec

  steadyStart <- getMonotonicTimeNSec
  (!total, !lastValue) <- decodeLoop iterations (consumeBatch first) first input
  steadyStop <- getMonotonicTimeNSec

  if validate && batchContentHash lastValue /= expectedHash
    then die "haskell-binary decode content mismatch"
    else pure ()

  pure Result
    { dataSetupNs = setupStop - setupStart
    , inputSetupNs = inputStop - inputStart
    , firstNs = firstStop - firstStart
    , steadyNs = steadyStop - steadyStart
    , outputBytes = fromIntegral (BS.length input)
    , contentHash = expectedHash
    , outputHash = hashBytes input
    , checksum = total
    }
  where
    decodeLoop 0 !total !lastValue _ = pure (total, lastValue)
    decodeLoop remaining !total _ input = do
      value <- decodeNF input
      decodeLoop (remaining - 1) (total + consumeBatch value) value input

printResult :: String -> Int -> Word64 -> Bool -> Result -> IO ()
printResult operation itemCount iterations validate result =
  putStrLn $
    "BENCH_RESULT implementation=haskell-binary"
      ++ " operation=" ++ operation
      ++ " items=" ++ show itemCount
      ++ " iterations=" ++ show iterations
      ++ " data_setup_ns=" ++ show (dataSetupNs result)
      ++ " input_setup_ns=" ++ show (inputSetupNs result)
      ++ " first_ns=" ++ show (firstNs result)
      ++ " steady_ns=" ++ show (steadyNs result)
      ++ " steady_ns_per_op=" ++ show perOperation
      ++ " output_bytes=" ++ show (outputBytes result)
      ++ " content_hash=" ++ show (contentHash result)
      ++ " output_hash=" ++ show (outputHash result)
      ++ " checksum=" ++ show (checksum result)
      ++ " validation=" ++ (if validate then "1" else "0")
      ++ " runtime_version=ghc-" ++ ghcVersion
      ++ " protobuf_version=proto-lens-" ++ protoLensVersion
      ++ " protobuf_runtime_version=proto-lens-runtime-" ++ protoLensRuntimeVersion
  where
    perOperation = if iterations == 0 then 0 else steadyNs result `div` iterations

printStartup :: IO ()
printStartup = putStrLn $
  "BENCH_RESULT implementation=haskell-runtime operation=startup"
    ++ " items=0 iterations=0 data_setup_ns=0 input_setup_ns=0 first_ns=0"
    ++ " steady_ns=0 steady_ns_per_op=0 output_bytes=0 content_hash=0"
    ++ " output_hash=0 checksum=0 validation=0"
    ++ " runtime_version=ghc-" ++ ghcVersion
    ++ " protobuf_version=proto-lens-" ++ protoLensVersion
    ++ " protobuf_runtime_version=proto-lens-runtime-" ++ protoLensRuntimeVersion

parseWord64 :: String -> String -> IO Word64
parseWord64 field value = case readMaybe value of
  Just parsed -> pure parsed
  Nothing -> die ("invalid " ++ field ++ ": " ++ value)

main :: IO ()
main = do
  arguments <- getArgs
  case arguments of
    ["startup"] -> printStartup
    ["version"] -> putStrLn $
      "proto-lens-" ++ protoLensVersion
        ++ " proto-lens-runtime-" ++ protoLensRuntimeVersion
        ++ " ghc-" ++ ghcVersion
    [operation, itemText, iterationText, validateText] -> do
      itemCount64 <- parseWord64 "item count" itemText
      iterations <- parseWord64 "iteration count" iterationText
      if itemCount64 > fromIntegral (maxBound :: Int)
        then die "item count is too large for the Haskell runtime"
        else pure ()
      validate <- case validateText of
        "0" -> pure False
        "1" -> pure True
        _ -> die "validate must be 0 or 1"
      result <- case operation of
        "encode" -> runEncode (fromIntegral itemCount64) iterations validate
        "decode" -> runDecode (fromIntegral itemCount64) iterations validate
        _ -> die "operation must be encode or decode"
      printResult operation (fromIntegral itemCount64) iterations validate result
    _ -> die "usage: <encode|decode> <items> <steady-iterations> <validate:0|1>"
