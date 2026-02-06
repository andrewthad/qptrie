{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DataKinds #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language NumDecimals #-}
{-# language NumericUnderscores #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TypeApplications #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

import Data.Bits (unsafeShiftR)
import Data.Bytes.Types (BytesN(..))
import Data.Word (Word64,Word8,Word16)
import Data.Foldable (foldl')
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.HUnit ((@=?))
import Text.Printf (printf)

import qualified Arithmetic.Nat as Nat
import qualified Data.List as List
import qualified Data.Trie.Quad as Trie
import qualified Data.Trie.Quad.Prefix as Prefix
import qualified Data.Trie.Quad.Bytes as BytesTrie
import qualified GHC.Exts as Exts
import qualified Test.Tasty.HUnit as THU
import qualified Test.Tasty.QuickCheck as QC

import qualified Data.Trie.Quad.Prefix.Word32.Word64 as P32

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "trie"
  [ testGroup "word64"
    [ THU.testCase "A" $
        Trie.lookup 0x0AFF
          (Trie.insert
            0x0BFF
            "there"
            (Trie.singleton 0x0AFF "hello")
          )
        @=?
        Just "hello"
    , THU.testCase "B" $
        (Trie.insert
          0x0BFF
          "there"
          (Trie.singleton 0x0AFF "hello")
        )
        @=?
        (Trie.insert
          0x0AFF
          "hello"
          (Trie.singleton 0x0BFF "there")
        )
    , THU.testCase "C" $
        ( Trie.insert 0x0BFF "there"
        $ Trie.insert 0x0CFF "people"
        $ Trie.singleton 0x0AFF "hello"
        )
        @=?
        ( Trie.insert 0x0CFF "people"
        $ Trie.insert 0x0AFF "hello"
        $ Trie.singleton 0x0BFF "there"
        )
    , THU.testCase "D" $
        ( Trie.insert 0x0BFF "there"
        $ Trie.insert 0x00FF "people"
        $ Trie.singleton 0x0AFF "hello"
        )
        @=?
        ( Trie.insert 0x00FF "people"
        $ Trie.insert 0x0AFF "hello"
        $ Trie.singleton 0x0BFF "there"
        )
    , THU.testCase "E" $
        ( Trie.insert 0x0B1F "there"
        $ Trie.insert 0x0B0F "people"
        $ Trie.singleton 0x0AFF "hello"
        )
        @=?
        ( Trie.insert 0x0B0F "people"
        $ Trie.insert 0x0AFF "hello"
        $ Trie.singleton 0x0B1F "there"
        )
    , THU.testCase "F" $ case Trie.valid alphaTrie of
        True -> pure ()
        False -> THU.assertFailure (show alphaTrie)
    , THU.testCase "G" $
        Trie.Branch 60 0b0000000000000011 (Exts.fromListN 2 [Trie.Leaf 0 "bar",Trie.Leaf 1 "foo"])
        @=?
        Trie.insert 1 "foo" (Trie.singleton 0 "bar")
    , THU.testCase "H" $
        Trie.Branch 60 0b0000000000000011 (Exts.fromListN 2 [Trie.Leaf 0 "baz",Trie.Leaf 1 "foo"])
        @=?
        Trie.insert 0 "baz" (Trie.insert 1 "foo" (Trie.singleton 0 "bar"))
    , QC.testProperty "lookup-all" $ \(xs :: [Word64]) ->
        let t = foldl' (\acc w -> Trie.insert w w acc) (Trie.singleton 0 0) xs
         in QC.counterexample (show t) (List.all (\x -> Trie.lookup x t == Just x) xs)
    , QC.testProperty "validity" $ \(xs :: [Word64]) ->
        let t = foldl' (\acc w -> Trie.insert w w acc) (Trie.singleton 0 0) xs
         in QC.counterexample (show t) (Trie.valid t)
    ]
  , testGroup "bytes"
    [ THU.testCase "A" $
        let theTrie = BytesTrie.insert
              Nat.two
              (w16b 0x0BFF )
              "there"
              (BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello")
         in case BytesTrie.valid theTrie of
              True -> case BytesTrie.lookup Nat.two (w16b 0x0AFF) theTrie of
                Just "hello" -> pure ()
                _ -> THU.assertFailure ("expected just hello, trie was: " ++ show theTrie)
              False -> THU.assertFailure ("invalid trie: " ++ show theTrie)
    , THU.testCase "B" $
        (BytesTrie.insert
          Nat.two
          (w16b 0x0BFF )
          "there"
          (BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello")
        )
        @=?
        (BytesTrie.insert
          Nat.two
          (w16b 0x0AFF )
          "hello"
          (BytesTrie.singleton Nat.two (w16b 0x0BFF) "there")
        )
    , THU.testCase "C" $
        ( BytesTrie.insert Nat.two (w16b 0x0BFF) "there"
        $ BytesTrie.insert Nat.two (w16b 0x0CFF) "people"
        $ BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello"
        )
        @=?
        ( BytesTrie.insert Nat.two (w16b 0x0CFF) "people"
        $ BytesTrie.insert Nat.two (w16b 0x0AFF) "hello"
        $ BytesTrie.singleton Nat.two (w16b 0x0BFF) "there"
        )
    , THU.testCase "D" $
        ( BytesTrie.insert Nat.two (w16b 0x0BFF) "there"
        $ BytesTrie.insert Nat.two (w16b 0x00FF) "people"
        $ BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello"
        )
        @=?
        ( BytesTrie.insert Nat.two (w16b 0x00FF) "people"
        $ BytesTrie.insert Nat.two (w16b 0x0AFF) "hello"
        $ BytesTrie.singleton Nat.two (w16b 0x0BFF) "there"
        )
    , THU.testCase "E" $
        ( BytesTrie.insert Nat.two (w16b 0x0B1F) "there"
        $ BytesTrie.insert Nat.two (w16b 0x0B0F) "people"
        $ BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello"
        )
        @=?
        ( BytesTrie.insert Nat.two (w16b 0x0B0F) "people"
        $ BytesTrie.insert Nat.two (w16b 0x0AFF) "hello"
        $ BytesTrie.singleton Nat.two (w16b 0x0B1F) "there"
        )
    , THU.testCase "F" $ case BytesTrie.valid alphaBytesTrie of
        True -> pure ()
        False -> THU.assertFailure (show alphaBytesTrie)
    , THU.testCase "G" $
        ( BytesTrie.upsert Nat.two (w16b 0x0CFF) (maybe "people" (<> " Kenobi"))
        $ BytesTrie.insert Nat.two (w16b 0x0BFF) "there"
        $ BytesTrie.insert Nat.two (w16b 0x0CFF) "General"
        $ BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello"
        )
        @=?
        ( BytesTrie.insert Nat.two (w16b 0x0CFF) "General Kenobi"
        $ BytesTrie.insert Nat.two (w16b 0x0AFF) "hello"
        $ BytesTrie.singleton Nat.two (w16b 0x0BFF) "there"
        )
    , THU.testCase "H" $
        ( BytesTrie.upsert Nat.two (w16b 0x0CFF) (maybe "people" (<> " Kenobi"))
        $ BytesTrie.insert Nat.two (w16b 0x0BFF) "there"
        $ BytesTrie.singleton Nat.two (w16b 0x0AFF) "hello"
        )
        @=?
        ( BytesTrie.insert Nat.two (w16b 0x0CFF) "people"
        $ BytesTrie.insert Nat.two (w16b 0x0AFF) "hello"
        $ BytesTrie.singleton Nat.two (w16b 0x0BFF) "there"
        )
    ]
  , testGroup "prefix"
    [ THU.testCase "A" $
        Prefix.lookup 0x0AF1
          (Prefix.insert 60 0x0AF2 "there" (Prefix.singleton 60 0x0AE0 "hello"))
        @=?
        Just "there"
    , THU.testCase "B" $
        THU.assertEqual (show bigPrefixTrie) (Just "baz") (Prefix.lookup 0x0AF1 bigPrefixTrie)
    , THU.testCase "C" $ Prefix.lookup 0x0AF0 bigPrefixTrie @=? Just "baz"
    , THU.testCase "D" $ Prefix.lookup 0x0AFF bigPrefixTrie @=? Just "baz"
    , THU.testCase "E" $ Prefix.lookup 0x0AD5 bigPrefixTrie @=? Just "bar"
    , THU.testCase "F" $ Prefix.lookup 0x0400 bigPrefixTrie @=? Just "burr"
    , THU.testCase "G" $ THU.assertEqual
        ("While looking up 0x04FF in\n" ++ show bigPrefixTrie)
        (Just "burr")
        (Prefix.lookup 0x04FF bigPrefixTrie)
    , THU.testCase "H" $ THU.assertEqual
        ("While looking up 0x05FF in\n" ++ show bigPrefixTrie)
        (Just "burr")
        (Prefix.lookup 0x05FF bigPrefixTrie)
    , THU.testCase "I" $ THU.assertEqual
        ("While looking up 0x07FF in\n" ++ show bigPrefixTrie)
        (Just "burr")
        (Prefix.lookup 0x07FF bigPrefixTrie)
    , THU.testCase "J" $ Prefix.lookup 0x0800 bigPrefixTrie @=? Just "bla"
    , THU.testCase "K" $ Prefix.lookup 0x08FF bigPrefixTrie @=? Just "bla"
    , THU.testCase "L" $ Prefix.lookup 0x0900 bigPrefixTrie @=? Just "foo"
    , THU.testCase "M" $ case Prefix.valid bigPrefixTrie of
        True -> pure ()
        False -> THU.assertFailure (show bigPrefixTrie)
    ]
  , testGroup "minimize"
    [ THU.testCase "A" $ let r = P32.minimize ipTrie1 in case P32.valid r of
        True -> pure ()
        False -> THU.assertFailure (show r)
    , THU.testCase "B" $ let r = P32.minimize ipTrie2 in case P32.valid r of
        True -> pure ()
        False -> case P32.nodeCount r of
          1 -> pure ()
          n -> THU.assertFailure ("Expected node count of 1 but got " ++ show n)
    , THU.testCase "C" $ let r = P32.minimize ipTrie3 in case P32.valid r of
        True -> case P32.nodeCount r of
          3 -> pure ()
          n -> THU.assertFailure ("Expected node count of 3 but got " ++ show n ++ "\nStructure:\n" ++ show r)
        False -> THU.assertFailure (show r)
    , THU.testCase "D" $ let r = P32.minimize ipTrie4 in case P32.valid r of
        True -> case P32.nodeCount r of
          3 -> pure ()
          n -> THU.assertFailure ("Expected node count of 3 but got " ++ show n ++ "\nStructure:\n" ++ show r)
        False -> THU.assertFailure (show r)
    , THU.testCase "E" $ let r = P32.minimize ipTrie5 in case P32.valid r of
        True -> case P32.nodeCount r of
          1 -> pure ()
          n -> THU.assertFailure ("Expected node count of 1 but got " ++ show n ++ "\nStructure:\n" ++ show r)
        False -> THU.assertFailure (show r)
    , THU.testCase "F" $ let r = P32.minimize ipTrie6 in case P32.valid r of
        True -> case P32.nodeCount r of
          1 -> pure ()
          n -> THU.assertFailure ("Expected node count of 1 but got " ++ show n ++ "\nStructure:\n" ++ show r)
        False -> THU.assertFailure (show r)
    , THU.testCase "G" $ let r = P32.minimize ipTrie7 in case P32.valid r of
        True -> case P32.nodeCount r of
          5 -> pure ()
          n -> THU.assertFailure ("Expected node count of 1 but got " ++ show n ++ "\nStructure:\n" ++ show r)
        False -> THU.assertFailure (show r)
    ]
  ]

ipTrie1 :: P32.Trie
ipTrie1 = id
  $ P32.insert    28 0xAAAA_BBB0 100
  $ P32.singleton 28 0xAAAA_CCC0 101

ipTrie2 :: P32.Trie
ipTrie2 = id
  $ P32.insert    28 0xAAAA_DD00 100
  $ P32.singleton 28 0xAAAA_DD10 100

ipTrie3 :: P32.Trie
ipTrie3 = id
  $ P32.insert    28 0xAAAA_DD00 100
  $ P32.insert    28 0xAAAA_DD10 100
  $ P32.insert    28 0xAAAA_DD20 100
  $ P32.insert    28 0xAAAA_DD30 100
  $ P32.singleton 32 0xAAAA_AA3F 200

ipTrie4 :: P32.Trie
ipTrie4 = id
  $ P32.insert    28 0xAAAA_DD80 100
  $ P32.insert    28 0xAAAA_DD90 100
  $ P32.insert    28 0xAAAA_DDA0 100
  $ P32.insert    28 0xAAAA_DDB0 100
  $ P32.insert    28 0xAAAA_DDC0 100
  $ P32.insert    28 0xAAAA_DDD0 100
  $ P32.insert    28 0xAAAA_DDE0 100
  $ P32.insert    28 0xAAAA_DDF0 100
  $ P32.singleton 32 0xAAAA_AA3F 200

ipTrie5 :: P32.Trie
ipTrie5 = id
  $ P32.insert    28 0xAAAA_DD80 100
  $ P32.insert    28 0xAAAA_DD90 100
  $ P32.insert    28 0xAAAA_DDA0 100
  $ P32.insert    28 0xAAAA_DDB0 100
  $ P32.insert    28 0xAAAA_DDC0 100
  $ P32.insert    28 0xAAAA_DDD0 100
  $ P32.insert    28 0xAAAA_DDE0 100
  $ P32.insert    28 0xAAAA_DDF0 100
  $ P32.singleton 25 0xAAAA_DD00 100

ipTrie6 :: P32.Trie
ipTrie6 = id
  $ P32.insert    27 0xAAAA_D100 100
  $ P32.singleton 27 0xAAAA_D120 100

ipTrie7 :: P32.Trie
ipTrie7 = id
  $ P32.insert    27 0xAAAA_D100 100
  $ P32.insert    27 0xAAAA_D120 200
  $ P32.insert    27 0xAAAA_D140 100
  $ P32.insert    27 0xAAAA_D160 100
  $ P32.singleton 27 0xAAAA_D180 100

bigPrefixTrie :: Prefix.Trie String
bigPrefixTrie = id
  $ Prefix.insert    54 0x0400 "burr"
  $ Prefix.insert    56 0x0800 "bla"
  $ Prefix.insert    56 0x0900 "foo"
  $ Prefix.insert    60 0x0A90 "buzz"
  $ Prefix.insert    60 0x0AC0 "bang"
  $ Prefix.insert    60 0x0AD0 "bar"
  $ Prefix.insert    60 0x0AF0 "baz"
  $ Prefix.singleton 60 0x0AE0 "hello"

alphaTrie :: Trie.Trie String
alphaTrie = id
  $ Trie.insert    0x0400 "burr"
  $ Trie.insert    0x0800 "bla"
  $ Trie.insert    0x0900 "foo"
  $ Trie.insert    0x0A90 "buzz"
  $ Trie.insert    0x0AC0 "bang"
  $ Trie.insert    0x0AD0 "bar"
  $ Trie.insert    0x0AF0 "baz"
  $ Trie.singleton 0x0AE0 "hello"

alphaBytesTrie :: BytesTrie.Trie 2 String
alphaBytesTrie = id
  $ BytesTrie.insert    Nat.two (w16b 0x0400) "burr"
  $ BytesTrie.insert    Nat.two (w16b 0x0800) "bla"
  $ BytesTrie.insert    Nat.two (w16b 0x0900) "foo"
  $ BytesTrie.insert    Nat.two (w16b 0x0A90) "buzz"
  $ BytesTrie.insert    Nat.two (w16b 0x0AC0) "bang"
  $ BytesTrie.insert    Nat.two (w16b 0x0AD0) "bar"
  $ BytesTrie.insert    Nat.two (w16b 0x0AF0) "baz"
  $ BytesTrie.singleton Nat.two (w16b 0x0AE0) "hello"

instance Show a => Show (Prefix.Trie a) where
  showsPrec !d (Prefix.Leaf klen k v) = showParen (d > 10) $
    showString "Leaf " .
    shows klen .
    showChar ' ' .
    (\s -> printf "0x%016x" k ++ s) .
    showChar ' ' .
    showsPrec 11 v
  showsPrec !d (Prefix.Branch pos bitset children) = showParen (d > 10) $
    showString "Branch " .
    showsPrec 11 pos .
    showChar ' ' .
    (\s -> printf "0b%016b" bitset ++ s) .
    showChar ' ' .
    showsPrec 11 children

deriving newtype instance Show a => Show (BytesTrie.Trie n a)

-- TODO: only kind of works correctly
instance Show a => Show (BytesTrie.Node a) where
  showsPrec !d (BytesTrie.Leaf k v) = showParen (d > 10) $
    showString "Leaf " .
    (\s -> shows k s) .
    showChar ' ' .
    showsPrec 11 v
  showsPrec !d (BytesTrie.Branch pos bitset children) = showParen (d > 10) $
    showString "Branch " .
    showsPrec 11 pos .
    showChar ' ' .
    (\s -> printf "0b%016b" bitset ++ s) .
    showChar ' ' .
    showsPrec 11 children

w16b :: Word16 -> BytesN 2
w16b w = BytesN
  { array=Exts.fromList
      [ (0xEF :: Word8)
      , (fromIntegral @Word16 @Word8 (unsafeShiftR w 8))
      , (fromIntegral @Word16 @Word8 (unsafeShiftR w 0))
      ]
  , offset=1
  }
