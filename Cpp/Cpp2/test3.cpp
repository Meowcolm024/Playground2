#include <iostream>
#include <variant>

using namespace std;

auto safeDiv(int a, int b) -> decltype(auto)
{
    return b == 0 ? variant<int, string>{"Error: Divide by Zero!"} : variant<int, string>{a / b};
}

int main()
{
    const int x = 1;
    int y = 2;

    const auto px = &x;
    auto py = &y;

    auto ppx = &px;
    auto const ppy = &py;

    auto a = safeDiv(6,2);
    auto b = safeDiv(1,0);

    return 0;
}