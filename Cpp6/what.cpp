#include <iostream>
using namespace std;

auto f(const int *h) -> void
{
    int *t;
    // *t = *h;
    cout << t << endl;
}

int main()
{
    auto a = 1;
    int *h = &a;
    f(h);
}