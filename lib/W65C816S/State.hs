{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecursiveDo #-}

module W65C816S.State where

import Control.Monad.IO.Class
import Control.Monad.Trans.Class (lift)
import Data.Bits (Bits (shiftL), shiftR)
import Data.Word
import Optics
import Optics.State.Operators
import W65C816S.Memory.Class
import Data.Binary
import qualified Data.ByteString.Lazy as BL
import Foreign.Storable (sizeOf)

data W65C816S mem = W65C816S
  { w65C816SA,
    w65C816SB,
    w65C816SDbr :: Word8,
    w65C816SD,
    w65C816SX,
    w65C816SY ::
      Word16,
    w65C816SP,
    w65C816SPbr ::
      Word8,
    w65C816SPc,
    w65C816SS ::
      Word16,
    w65C816SE :: Bool,
    w65C816SMem :: mem
  }

makeFieldLabels ''W65C816S

instance LabelOptic "c" A_Lens (W65C816S mem) (W65C816S mem) Word16 Word16 where
  labelOptic =
    lens
      ( \W65C816S {w65C816SA = (fromIntegral -> a), w65C816SB = (fromIntegral -> b)} ->
        shiftL b 8
      )
      ( \prev c ->
        prev {w65C816SA = fromIntegral c, w65C816SB = fromIntegral $ shiftR c 8}
      )

class Accumulator num where
  acc :: Optic A_Lens NoIx (W65C816S mem) (W65C816S mem) num num

instance Accumulator Word8 where
  acc = #a

instance Accumulator Word16 where
  acc = #c

instance LabelOptic "xl" A_Lens (W65C816S mem) (W65C816S mem) Word16 Word16 where
  labelOptic =
    lens
      w65C816SX
      ( \prev x ->
        prev {w65C816SX = mod x 0x100}
      )

instance LabelOptic "yl" A_Lens (W65C816S mem) (W65C816S mem) Word16 Word16 where
  labelOptic =
    lens
      w65C816SY
      ( \prev y ->
        prev {w65C816SY = mod y 0x100}
      )

instance LabelOptic "sp" A_Lens (W65C816S mem) (W65C816S mem) Word16 Word16 where
  labelOptic =
    lens
      w65C816SS
      ( \prev@(W65C816S {w65C816SE}) s ->
          if w65C816SE
            then prev {w65C816SS = mod s 0x100 + 0x100}
            else prev {w65C816SS = s}
      )

readMem (fromIntegral -> bank) (fromIntegral -> off) = do
  mem <- use #mem
  lift $ fmap le $ readByteOff mem $ off + shiftL bank 16

writeMem (fromIntegral -> bank) (fromIntegral -> off) value = do
  mem <- use #mem
  mem <- lift $ writeByteOff mem (off + shiftL bank 16) $ LE value
  #mem .= mem

currInstr = do
  pc <- use #pc
  pbr <- use #pbr
  res <-readMem pbr pc
  #pc %= (fromIntegral (sizeOf res) +)
  pure res

push value = do
  sp <- #sp <%= subtract (fromIntegral (sizeOf value) + 1)
  writeMem 0 sp value
  #sp %= subtract 1

pushLens lens = do
  push =<< use lens

pop = do
  sp <- #sp <%= (1 +)
  res <- readMem 0 sp
  #sp %= (+ fromIntegral (sizeOf res - 1))
  pure res

popLens lens = do
  assign lens =<< pop