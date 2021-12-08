#include <iostream>

auto fun = [](auto i)
{
    return new int(i);
};

enum class T {
    A, B = -3 , C = 0
};

int main()
{
    int y = 233;
    auto z = fun(2);
    delete z;
    auto x = new int;
    std::cout << z << " " << x << "\n";
    delete x;

    std::cout << int(T::A) << " " << int(T::B) << " " << int(T::C) << " \n";

    return 0;
}