%
% Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
%
% SPDX-License-Identifier: GPL-2.0-only
%

> -- Foundational Word definitions and their consequences
>
> module Data.WordLib where
>
> import Data.Word
> import Data.Bits
>
> -- Convenience functions dealing with properties of the machine word:
> -- * Number of bits in a word (architecture specific)
> -- * Radix $n$ such that $2^n$ is the number of bits in the word
> -- * Bytes required to store a word
> -- * Selecting one of two alternatives depending on the size of the machine word
> --      (32 or 64 bits)
>
> wordBits :: Int
> wordBits = finiteBitSize (undefined::Word)
>
> wordSize :: Int
> wordSize = wordBits `div` 8
>
> wordSizeCase :: a -> a -> a
> wordSizeCase a b = case wordBits of
>         32 -> a
>         64 -> b
>         _ -> error "Unknown word size"
>
> wordRadix :: Int
> wordRadix = wordSizeCase 5 6

