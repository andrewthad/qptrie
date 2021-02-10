{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

module Data.Trie.Quad
  ( Trie(..)
  , singleton
  , insert
  , lookup
  , lookup#
  ) where

import Prelude hiding (lookup)

import Data.Bits (countLeadingZeros,xor,popCount,(.&.),(.|.),unsafeShiftR,unsafeShiftL)
import Data.Primitive (SmallArray)
import Data.Word (Word32,Word64)
import Control.Monad.ST.Run (runSmallArrayST)
import qualified Data.Primitive as PM

-- This explanation of how popcount is used in this module is copied
-- from https://github.com/fanf2/qp/blob/HEAD/qp.h:
--
-- You can use popcount() to implement a sparse array of length N
-- containing M < N members using bitmap of length N and a packed
-- vector of M elements. A member i is present in the array if bit
-- i is set, so M == popcount(bitmap). The index of member i in
-- the packed vector is the popcount of the bits preceding i.
--   mask = 1 << i;
--   if(bitmap & mask)
--     member = vector[popcount(bitmap & mask-1)]

-- | Non-empty qp tries. These have the following properties:
--
-- * Keys are considered processed in 4-bit chunks. This means that the
--   maximum height of a trie is 16.
-- * Nodes are compressed in the traditional sense of trie
--   compression. Single-child nodes do not appear except in the degenerate
--   case of a singleton trie. Like in a crit-bit tree, every node identifies
--   the position of the critical nybble.
-- * Nodes are compressed in the sense that qp tries and hash-array mapped
--   tries are compressed. A bitset is used to eliminate empty elements of
--   arrays.
data Trie a
  = Branch
      !Int -- position, >=0 and <=60, must divide 4 evenly 
      !Word -- bitset
      !(SmallArray (Trie a)) -- invariant: max length is 16
  | Leaf !Word64 !a
  deriving stock (Eq)

singleton :: Word64 -> a -> Trie a
singleton !k !v = Leaf k v

lookup :: Word64 -> Trie a -> Maybe a
{-# inline lookup #-}
lookup !k t = case lookup# k t of
  (# (# #) | #) -> Nothing
  (# | v #) -> Just v

lookup# :: Word64 -> Trie a -> (# (# #) | a #)
{-# noinline lookup# #-}
lookup# !k t0 = go t0 where
  go (Leaf x v) = if x == k
    then (# | v #)
    else (# (# #) | #)
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (60 - pos)
        mask :: Word
        mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
     in case bitset .&. mask of
          0 -> (# (# #) | #)
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

insert :: Word64 -> a -> Trie a -> Trie a
insert !k v t0 = go t0 where
  go (Leaf x xv) = if x == k
    then (Leaf x v)
    else
      let pos = deltaNybbleStartIx k x
          k' = unsafeShiftR k (60 - pos) .&. 0x0F
          x' = unsafeShiftR x (60 - pos) .&. 0x0F
          kleaf = Leaf k v
          xleaf = Leaf x xv
          arr = runSmallArrayST $ do 
            dst <- PM.newSmallArray 2 kleaf
            let !ix = if k' < x' then 1 else 0
            PM.writeSmallArray dst ix xleaf
            PM.unsafeFreezeSmallArray dst
       in Branch pos
            (unsafeShiftL 1 (fromIntegral @Word64 @Int k')
             .|.
             unsafeShiftL 1 (fromIntegral @Word64 @Int x')
            )
            arr
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (60 - pos)
        mask :: Word
        mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
        trueIx = popCount (bitset .&. (mask - 1))
     in case bitset .&. mask of
          0 ->
            let newNode = Leaf k v
             in Branch pos (bitset .|. mask) (insertSmallArray children trueIx newNode)
          _ -> case PM.indexSmallArray## children trueIx of
            (# child #) ->
              let child' = go child
               in Branch pos bitset (replaceSmallArray children trueIx child') 

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

deltaNybbleStartIx :: Word64 -> Word64 -> Int
deltaNybbleStartIx a b = countLeadingZeros (xor a b) .&. 0b11111100
