#include <iostream>
#include "lib.hpp"

// clang++ -fPIC -shared -o libTest.so lib.cpp

void cpphello(int n)
{
    for (int i = 0; i < n; i++)
        std::cout << "Hello World" << std::endl;
}

void cppArr(const int* arr, int n) {
    for (int i = n-1; i >= 0; i--)
        std::cout << arr[i] << " ";
    std::cout << std::endl;
}

extern "C"
{
    void hello(int n) {
        cpphello(n);
    }

    void printArr(const int* arr, int n) {
        cppArr(arr, n);
    };

    int resetArray(int* arr, int n) {
        int acc = 0;
        for (int i = 0; i < n; i++) {
            acc += arr[i];
            arr[i] = 0;
        }
        return acc;
    }
}
