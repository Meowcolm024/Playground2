#include <HsFFI.h>
#ifdef __GLASGOW_HASKELL__
#include "HsLib_stub.h"
#endif
#include <iostream>

// ghc --make -lstdc++ -no-hs-main -optc-O test.cpp HsLib -o test

int main(int argc, char *argv[])
{
    using namespace std;
    int i;
    hs_init(&argc, &argv);

    i = fibonacci_hs(42);
    cout << "Fibonacci: " << i << endl;

    hs_exit();
    return 0;
}