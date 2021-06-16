{-# language BangPatterns #-}
{-# language MagicHash #-}
{-# language ScopedTypeVariables #-}

module Data.Trie.Internal
  ( insertSmallArray
  , replaceSmallArray
  ) where

import Control.Monad.ST.Run (runSmallArrayST)
import Data.Primitive (SmallArray)
import qualified Data.Primitive as PM

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insertSmallArray :: SmallArray a -> Int -> a -> SmallArray a
insertSmallArray !ary !idx b = runSmallArrayST $ do
  mary <- PM.newSmallArray (count+1) b
  PM.copySmallArray mary 0 ary 0 idx
  PM.copySmallArray mary (idx+1) ary idx (count-idx)
  PM.unsafeFreezeSmallArray mary
  where !count = PM.sizeofSmallArray ary

-- | /O(n)/ Replace the element at the given index.
replaceSmallArray :: SmallArray a -> Int -> a -> SmallArray a
replaceSmallArray !ary !idx b = runSmallArrayST $ do
  mary <- PM.thawSmallArray ary 0 count
  PM.writeSmallArray mary idx b
  PM.unsafeFreezeSmallArray mary
  where !count = PM.sizeofSmallArray ary

