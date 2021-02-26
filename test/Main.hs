{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language NumDecimals #-}

import Control.Monad (when,replicateM)
import Data.Bool (bool)
import Data.Char (ord)
import Data.Primitive (ByteArray)
import Data.Word (Word64)
import Data.Foldable (foldl')
import Test.Tasty (defaultMain,testGroup,TestTree)
import Test.Tasty.HUnit ((@=?),assertFailure)
import Test.Tasty.QuickCheck (testProperty,(===))
import Text.Printf (printf)

import qualified Data.List as List
import qualified Data.Trie.Quad as Trie
import qualified Data.Trie.Quad.Prefix as Prefix
import qualified Data.Bits as Bits
import qualified Data.Primitive as PM
import qualified GHC.Exts as Exts
import qualified Test.Tasty.HUnit as THU
import qualified Test.Tasty.QuickCheck as QC

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
  ]

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

instance Show a => Show (Trie.Trie a) where
  showsPrec !d (Trie.Leaf k v) = showParen (d > 10) $
    showString "Leaf " .
    (\s -> printf "0x%016x" k ++ s) .
    showChar ' ' .
    showsPrec 11 v
  showsPrec !d (Trie.Branch pos bitset children) = showParen (d > 10) $
    showString "Branch " .
    showsPrec 11 pos .
    showChar ' ' .
    (\s -> printf "0b%016b" bitset ++ s) .
    showChar ' ' .
    showsPrec 11 children
    
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
