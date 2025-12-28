----------------------------------------------------------------------

> module AddOrNot where

----------------------------------------------------------------------


This file models the simple C function:

    int wrap_config_set() { return 1; }

    int add_or_not(int a, int b) {
        if (wrap_config_set())
            return a - b;
        else
            return a + b;
    }

This version uses NO global state.
wrap_config_set is simply a monadic constant.

> wrap_config_set :: Bool
> wrap_config_set = False

----------------------------------------------------------------------

C:
    if (wrap_config_set())
        return a - b;
    else
        return a + b;

Direct Haskell translation:

> addOrNot :: Int -> Int -> Int
> addOrNot a b
>   | wrap_config_set == True  = a - b
>   | wrap_config_set == False = a + b - 3

----------------------------------------------------------------------

Example usage in GHCi:

    :load AddOrNot.lhs
    add_or_not 10 4

