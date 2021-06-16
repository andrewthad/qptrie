{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

import Gauge.Main (defaultMain,bgroup,bench,whnf)
import RandomNumbers (randomW64_500)
import Data.Word (Word64)

import qualified Data.Primitive.Ptr as PM
import qualified Data.Trie.Quad as Quad
import qualified Data.IntMap.Strict as IntMap

main :: IO ()
main = do
  defaultMain
    [ bgroup "qptrie"
      [ bgroup "insert"
        [ bench "500" $ whnf qptrieInsertRandom500 (Quad.singleton 0 ())
        ]
      ]
    , bgroup "intmap"
      [ bgroup "insert"
        [ bench "500" $ whnf intmapInsertRandom500 (IntMap.singleton 0 ())
        ]
      ]
    ]

qptrieInsertRandom500 :: Quad.Trie () -> Quad.Trie ()
{-# noinline qptrieInsertRandom500 #-}
qptrieInsertRandom500 t0 =
  let go !ix !acc = if ix < 500
        then go (ix + 1) (Quad.insert (PM.indexOffPtr randomW64_500 ix) () acc)
        else acc
   in go 0 t0

intmapInsertRandom500 :: IntMap.IntMap () -> IntMap.IntMap ()
{-# noinline intmapInsertRandom500 #-}
intmapInsertRandom500 t0 =
  let go !ix !acc = if ix < 500
        then go (ix + 1) (IntMap.insert (fromIntegral @Word64 @Int (PM.indexOffPtr randomW64_500 ix)) () acc)
        else acc
   in go 0 t0


