{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language NumericUnderscores #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

-- | Specialization of @Data.Trie.Quad.Prefix@ where the keys are 32 bits
-- (instead of 64 bits) and the values are 64-bit words (instead of having
-- the data structure be polymorphic in its value).
--
-- This is helpful in the case where the key is an IPv4 address and the
-- value is a number.
module Data.Trie.Quad.Prefix.Word32.Word64
  ( Trie(..)
  , singleton
  , insert
  , lookup
  , lookup#
  , valid
  ) where

import Prelude hiding (lookup)

import Control.Monad.ST.Run (runSmallArrayST)
import Data.Bits (countLeadingZeros,xor,popCount,(.&.),(.|.),unsafeShiftR,unsafeShiftL)
import Data.Bits (shiftR,shiftL)
import Data.Primitive (SmallArray)
import Data.Word (Word32)
import Numeric (showHex)
import GHC.Exts (Word64#)
import GHC.Word (Word64(W64#))

import qualified Data.Primitive as PM

-- | Non-empty qp tries. These have all of the properties that the tries in
--   @Data.Trie.Quad@ have. Additionally:
--
-- * Every key is accompanied by a prefix. The prefix dictates how many of the
--   most significant bits are used. All insignificant bits are set
--   to zero. This is very much like a CIDR mask for IP addresses. A prefix
--   of zero implies a singleton map that matches everything. Prefixes must not
--   be greater than 64.
-- * Interpreted as ranges, the set of keys must not overlap. Overlapping key
--   ranges result in an exception.
-- * The same key must not be inserted more than once. This results in an
--   exception.
data Trie
  = Branch
      !Word32 -- position, >=0 and <=60, must divide 4 evenly 
      !Word32 -- bitset (only the low 16 bits are used, high 16 bits must be zero)
      !(SmallArray Trie) -- invariant: max length is 16
  | Leaf
      !Word32 -- effective key length, between 0 and 64
      !Word32 -- key, normalized
      !Word64
  deriving stock (Eq)

normalizeKey ::
     Word32 -- number of most significant bits that are used, N.
  -> Word32 -- the key
  -> Word32 -- key with lower bits zeroed out. Number of zeroed lower bits = 64 - N.
normalizeKey b w = shiftL 0xFFFF_FFFF (32 - fromIntegral @Word32 @Int b) .&. w

inclusiveUpperBound ::
     Word32 -- number of most significant bits that are used, N.
  -> Word32 -- the key
  -> Word32 -- key with lower bits all set to 1
inclusiveUpperBound b w = shiftR 0xFFFF_FFFF (fromIntegral @Word32 @Int b) .|. w

singleton ::
     Int -- ^ Number of bits to consider, @[0-32]@
  -> Word32 -- ^ Key, for bit count less than 32, low bits are masked out 
  -> Word64 -- ^ Value
  -> Trie
singleton !b !k !v
  | b < 0 = errorWithoutStackTrace "Data.Trie.Quad.Prefix: key size less than zero"
  | b > 32 = errorWithoutStackTrace "Data.Trie.Quad.Prefix: key size greater than 32"
  | otherwise = let !b32 = fromIntegral b :: Word32 in Leaf b32 (normalizeKey b32 k) v

lookup ::
     Word32 -- ^ Key
  -> Trie -- ^ Trie
  -> Maybe Word64
{-# inline lookup #-}
lookup !k t = case lookup# k t of
  (# (# #) | #) -> Nothing
  (# | v #) -> Just (W64# v)

lookup# :: Word32 -> Trie -> (# (# #) | Word64# #)
{-# noinline lookup# #-}
lookup# !k t0 = go t0 where
  go (Leaf xbits x (W64# v)) = if x == normalizeKey xbits k
    then (# | v #)
    else (# (# #) | #)
  go (Branch pos bitset children) =
    let i :: Word32 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (28 - fromIntegral @Word32 @Int pos)
        (ix,wasFound) = compressIndex i bitset
     in case wasFound of
          -- False -> error
          --   ("not found but i is: " ++ show i ++ ",ix is: " ++ show ix ++
          --    ", bitset was " ++ printf "0b%016b" bitset)
          False -> let ix' = ix - 1 in case ix' of
            (-1) -> (# (# #) | #)
            _ ->
              let !(# child #) = PM.indexSmallArray## children ix'
               in go child
          True ->
            let !(# child #) = PM.indexSmallArray## children ix
             in go child

-- This function is a bit of a misnomer. It's not actually the nearest key
-- in the trie. It's any key where the maximum number of leading nybbles
-- match the needle.
--
-- TODO: I believe it is possible to make this function error in the case
-- of overlapping keys.
nearestKey :: Word32 -> Trie -> Word32
nearestKey !k t0 = go t0 where
  go (Leaf _ x _) = x
  go (Branch pos bitset children) =
    let i :: Word32 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (28 - fromIntegral @Word32 @Int pos)
        mask :: Word32
        mask = unsafeShiftL (1 :: Word32) (fromIntegral @Word32 @Int i)
     in case bitset .&. mask of
          0 -> case PM.indexSmallArray## children 0 of
            (# child #) -> leftmostChildKey child
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

-- Precondition: branch nodes must not be empty
leftmostChildKey :: Trie -> Word32
leftmostChildKey t0 = go t0 where
  go (Leaf _ k _) = k
  go (Branch _ _ children) = go (PM.indexSmallArray children 0)

-- | Behavior is undefined when the number of bits to consider is
-- outside of the acceptable range.
insert ::
     Int -- ^ Number of bits to consider, @[0-32]@
  -> Word32 -- ^ Key, for bit count less than 32, low bits are masked out 
  -> Word64 -- ^ Value
  -> Trie
  -> Trie
{-# noinline insert #-}
insert !b !k0 !v t0 =
  let !b32 = fromIntegral @Int @Word32 b
      !k = normalizeKey b32 k0
      !j = nearestKey k t0
      !critPos = deltaNybbleStartIx j k
      go lf@(Leaf b' k' _) = if k == k'
        then errorWithoutStackTrace ("Data.Trie.Quad.Prefix.Word32.Word64: overlapping keys " ++ showHex k0 ('[' : shows b ("] and " ++ showHex k' ('[' : shows b' "]"))))
        else makeDoubleton critPos b32 k j v lf
      go br@(Branch pos bitset children) =
        case compare pos critPos of
          LT -> let !kslice = 0x0F .&. unsafeShiftR k (28 - fromIntegral @Word32 @Int pos) in
            case compressIndex kslice bitset of
              (ix,True) -> case PM.indexSmallArray## children ix of
                (# child #) ->
                  let !child' = go child
                   in Branch pos bitset (replaceSmallArray children ix child')
              (_,False) -> errorWithoutStackTrace "Data.Trie.Quad.Prefix.Word32.Word64.insert: mistake b"
          GT -> makeDoubleton critPos b32 k j v br
          EQ -> let !kslice = 0x0F .&. unsafeShiftR k (28 - fromIntegral @Word32 @Int pos) in
            case compressIndex kslice bitset of
              (_,True) -> errorWithoutStackTrace "Data.Trie.Quad.Prefix.Word32.Word64.insert: mistake d"
              (ix,False) -> Branch pos
                (bitset .|. unsafeShiftL (1 :: Word32) (fromIntegral @Word32 @Int kslice))
                (insertSmallArray children ix (Leaf b32 k v))
   in go t0

-- critPos must not be 64
-- the given node contains the j key already
makeDoubleton :: Word32 -> Word32 -> Word32 -> Word32 -> Word64 -> Trie -> Trie
makeDoubleton !critPos !klen !k !j v !node =
  let kslice = 0x0F .&. unsafeShiftR k (28 - fromIntegral @Word32 @Int critPos)
      jslice = 0x0F .&. unsafeShiftR j (28 - fromIntegral @Word32 @Int critPos)
      kleaf = Leaf klen k v
      arr = runSmallArrayST $ do 
        dst <- PM.newSmallArray 2 kleaf
        let !ix = if kslice < jslice then 1 else 0
        PM.writeSmallArray dst ix node
        PM.unsafeFreezeSmallArray dst
   in Branch critPos
     (unsafeShiftL 1 (fromIntegral @Word32 @Int kslice)
      .|.
      unsafeShiftL 1 (fromIntegral @Word32 @Int jslice)
     ) arr

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

-- Returns number between 0 and 32. Number always divides 4 evenly.
deltaNybbleStartIx :: Word32 -> Word32 -> Word32
{-# inline deltaNybbleStartIx #-}
deltaNybbleStartIx a b =
  fromIntegral @Int @Word32 (countLeadingZeros (xor a b)) .&. 0b11111100

compressIndex ::
     Word32 -- ^ 4-bit number (0 to 15 inclusive)
  -> Word32 -- bitset (only lower 16 bits should ever be set)
  -> (Int,Bool)
{-# inline compressIndex #-}
compressIndex !i !bitset = 
  let mask :: Word32
      mask = unsafeShiftL (1 :: Word32) (fromIntegral @Word32 @Int i)
   in (popCount (bitset .&. (mask - 1)), (bitset .&. mask) /= 0)

data MaybeWord32
  = JustWord32 {-# UNPACK #-} !Word32
  | NothingWord32

valid :: Trie -> Bool
{-# noinline valid #-}
valid t0 = case go 0 (0 :: Word32) t0 of
  JustWord32 _ -> True
  NothingWord32 -> False
  where
  go !prevMax !_ (Leaf k x _) = if prevMax == 0
    -- Checking that prevMax is 0 is a hack that makes the validity check
    -- accept some tries that it should not. The correct thing is to either
    -- augment Word32 with a "bottom" value or track whether or not we are
    -- on the far left-hand side of a trie. I'm willing to live with the
    -- incorrectness since this function is just for testing.
    then JustWord32 (inclusiveUpperBound k x)
    else if prevMax < x
      then JustWord32 (inclusiveUpperBound k x)
      else NothingWord32
  go !prevMax0 !i (Branch pos bitset children)
    | PM.sizeofSmallArray children <= 1 = NothingWord32
    | popCount bitset /= PM.sizeofSmallArray children = NothingWord32
    | pos < i = NothingWord32 -- note: should actually be lte, but word32 has no negatives to use as an initial value
    | mod pos 4 /= 0 = NothingWord32
    | otherwise = foldl
        (\acc node -> case acc of
          NothingWord32 -> NothingWord32
          JustWord32 prevMax -> go prevMax pos node
        ) (JustWord32 prevMax0) children

