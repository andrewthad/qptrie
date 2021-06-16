{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

module Data.Trie.Quad
  ( Trie(..)
  , singleton
  , insert
  , lookup
  , lookup#
  , valid
  ) where

import Prelude hiding (lookup)

import Data.Trie.Internal (insertSmallArray,replaceSmallArray)
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
      !(SmallArray (Trie a))
      -- invariant: max length of children is 16
      -- invariant: position in any child branches is greater than position of parent
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

-- This function is a bit of a misnomer. It's not actually the nearest key
-- in the trie. It's any key where the maximum number of leading nybbles
-- match the needle.
nearestKey :: Word64 -> Trie a -> Word64
nearestKey !k t0 = go t0 where
  go (Leaf x _) = x
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (60 - pos)
        mask :: Word
        mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
     in case bitset .&. mask of
          0 -> case PM.indexSmallArray## children 0 of
            (# child #) -> leftmostChildKey child
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

-- Precondition: branch nodes must not be empty
leftmostChildKey :: Trie a -> Word64
leftmostChildKey t0 = go t0 where
  go (Leaf k _) = k
  go (Branch _ _ children) = go (PM.indexSmallArray children 0)

compressIndex ::
     Word64 -- ^ 4-bit number (0 to 15 inclusive)
  -> Word -- bitset (only lower 16 bits should ever be set)
  -> (Int,Bool)
{-# inline compressIndex #-}
compressIndex !i !bitset = 
  let mask :: Word
      mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
   in (popCount (bitset .&. (mask - 1)), (bitset .&. mask) /= 0)

insert :: Word64 -> a -> Trie a -> Trie a
{-# noinline insert #-}
insert !k v t0 =
  let !j = nearestKey k t0
      !critPos = deltaNybbleStartIx j k
      go lf@(Leaf k' _) = if k /= k'
        then makeDoubleton critPos k j v lf
        else Leaf k v
      go br@(Branch pos bitset children) =
        case compare pos critPos of
          LT -> let !kslice = 0x0F .&. unsafeShiftR k (60 - pos) in
            case compressIndex kslice bitset of
              (ix,True) -> case PM.indexSmallArray## children ix of
                (# child #) ->
                  let !child' = go child
                   in Branch pos bitset (replaceSmallArray children ix child')
              (_,False) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake b"
          GT -> makeDoubleton critPos k j v br
          EQ -> let !kslice = 0x0F .&. unsafeShiftR k (60 - pos) in
            case compressIndex kslice bitset of
              (_,True) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake d"
              (ix,False) -> Branch pos
                (bitset .|. unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int kslice))
                (insertSmallArray children ix (Leaf k v))
   in go t0

-- critPos must not be 64
-- the given node contains the j key already
makeDoubleton :: Int -> Word64 -> Word64 -> a -> Trie a -> Trie a
makeDoubleton !critPos !k !j v !node =
  let kslice = 0x0F .&. unsafeShiftR k (60 - critPos)
      jslice = 0x0F .&. unsafeShiftR j (60 - critPos)
      kleaf = Leaf k v
      arr = runSmallArrayST $ do 
        dst <- PM.newSmallArray 2 kleaf
        let !ix = if kslice < jslice then 1 else 0
        PM.writeSmallArray dst ix node
        PM.unsafeFreezeSmallArray dst
   in Branch critPos
     (unsafeShiftL 1 (fromIntegral @Word64 @Int kslice)
      .|.
      unsafeShiftL 1 (fromIntegral @Word64 @Int jslice)
     ) arr

-- Returns number between 0 and 64. Number always divides 4 evenly.
deltaNybbleStartIx :: Word64 -> Word64 -> Int
deltaNybbleStartIx a b = countLeadingZeros (xor a b) .&. 0b11111100

valid :: Trie a -> Bool
{-# noinline valid #-}
valid = go (-1) where
  go !_ Leaf{} = True
  go !i (Branch pos bitset children) =
    PM.sizeofSmallArray children > 1
    &&
    popCount bitset == PM.sizeofSmallArray children
    &&
    pos > i
    &&
    mod pos 4 == 0
    &&
    all (go pos) children
