#include <iostream>

int main() {
    const int * const p = new int const(10);
    auto* arr = new int[3];
    std::cout << arr << "\n" << &arr << "\n" << &arr[0] << "\n";
    const int& c = 10;
    int cc = c;
    return 0;
}