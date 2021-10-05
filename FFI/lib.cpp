#include <iostream>
#include "lib.hpp"

// clang++ -fPIC -shared -o libTest.so lib.cpp

void cpphello(int n)
{
    for (int i = 0; i < n; i++)
        std::cout << "Hello World" << std::endl;
}

extern "C"
{
    void hello(int n) {
        cpphello(n);
    }
}
