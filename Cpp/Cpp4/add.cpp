#include <iostream>
using namespace std;

int main() {
    int arr[5];             // int arr[5]

    auto p1 = arr;          // int *p1
    auto p2 = &arr[0];      // int *p2
    auto p3 = &arr;         // int (*p3)[5]

    return 0;
}