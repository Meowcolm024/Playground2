#include <iostream>

// -O3 for tail recursion optimization
int64_t sumfrom(int64_t x, int64_t acc)
{
    return x == 0 ? acc : sumfrom(x - 1, acc + x);
}

// not tailrec
int64_t exp(int64_t e, int64_t x)
{
    if (x == 0)
        return 1;
    else if (x % 2 == 0)
    {
        auto y = exp(e, x / 2);
        return y * y;
    }
    else
    {
        auto y = exp(e, (x - 1) / 2);
        return e * y * y;
    }
}

int main()
{
    using namespace std;

    auto x = sumfrom(2333333, 0);
    cout << x << endl;

    // auto y = exp(2, 10);
    // cout << y << endl;

    return 0;
}