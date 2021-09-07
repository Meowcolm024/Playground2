#include <iostream>

constexpr int x = 233;

void f() {
    constexpr auto z = 666;
    constexpr int y = x + 1 + z;
    std::cout << y << std::endl;
}

int main()
{
    f();

    int p = 23;
    int xs [10] = {1,2,3,4,5,6,7,8,9,0};
    int y = xs[p - 12];

   std:: cout << y << std::endl;

    return 0;
}