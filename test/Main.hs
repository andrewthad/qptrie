{-# language BangPatterns #-}
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
    , QC.testProperty "lookup-all" $ \(xs :: [Word64]) ->
        let t = foldl' (\acc w -> Trie.insert w w acc) (Trie.singleton 0 0) xs
         in List.all (\x -> Trie.lookup x t == Just x) xs
    ]
  ]

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
    (\s -> printf "0b%032b" bitset ++ s) .
    showChar ' ' .
    shows children
    

