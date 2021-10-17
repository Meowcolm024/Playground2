#include "wrap.hpp"
#include <HsFFI.h>
#ifdef __GLASGOW_HASKELL__
#include "HsLib_stub.h"
#endif

// ghc --make -no-hs-main -optc-O wrap.cpp HsLib -c

extern "C" {
    int32_t fibonacci(int32_t n) {
        hs_init(0, 0);
        int32_t result = fibonacci_hs(n);
        hs_exit();
        return result;
    }
}
